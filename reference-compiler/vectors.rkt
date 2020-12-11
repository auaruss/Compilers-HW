#lang racket
(require graph)
(require "conditionals.rkt"
         "interp.rkt"
         "interp-R3.rkt"
         "utilities.rkt"
         "runtime-config.rkt"
         "type-check-R3.rkt")

(provide compile-R3 vectors-passes)

(define compile-R3
  (class compile-R2
    (super-new)
    
    (inherit variable-size print-x86-block print-x86-instr 
             first-offset add-node generic-explicate-pred partial-eval)

    (define/public (vector-primitives)
      (set 'vector 'vector-ref 'vector-set! 'vector-length))
    
    (define/override (primitives)
      (set-union (super primitives) (vector-primitives)))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; shrink

    (define/override (shrink-exp e)
      (match e
        [(Void)
         (Void)]
        ;; Annoying to have to re-do the following code to insert
        ;; the has-type's. -Jeremy
        [(Prim 'and (list e1 e2))
         #;(let ([tmp (gensym 'tmp)])
           (Let tmp (shrink-exp e1)
                (HasType (If (Var tmp) (shrink-exp e2) (Var tmp)) 'Boolean)))
         
         ;; The following is better for explicate-pred -Jeremy
         (If (shrink-exp e1) (shrink-exp e2) (Bool #f))]
        [(Prim 'or (list e1 e2))
         #;(let ([tmp (gensym 'tmp)])
           (Let tmp (shrink-exp e1)
                (HasType (If (Var tmp) (Var tmp) (shrink-exp e2)) 'Boolean)))
         
         ;; The following is better for explicate-pred -Jeremy
         (If (shrink-exp e1) (Bool #t) (shrink-exp e2))]
        [(Prim '<= (list e1 e2))
         (Prim 'not (list (Prim '< (list (shrink-exp e2) (shrink-exp e1)))))]
        [(Prim '>= (list e1 e2))
         (Prim 'not (list (Prim '< (list (shrink-exp e1) (shrink-exp e2)))))]
        [(Prim '- (list e1 e2))
         (Prim '+ (list (shrink-exp e1)
                        (Prim '- (list (shrink-exp e2)))))]
        [(HasType e t)
         (HasType (shrink-exp e) t)]
        [else
         (super shrink-exp e)]
        ))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; partial-eval : R3 -> R3

    (define/override (pe-exp env)
      (lambda (e)
        (debug "R2/pe-exp: " e)
        (match e
          [(Void)
           (Void)]
          [(HasType e ty)
           (define e^ ((pe-exp env) e))
           (HasType e^ ty)]
          [(Prim op es)
           #:when (member op '(vector vector-ref vector-set! vector-length))
           ;; TODO
           (define es^ (for/list ([e es]) ((pe-exp env) e)))
           (Prim op es^)]
          [else  ((super pe-exp env) e)]
          )))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uniquify : R3 -> C1-expr x (C1-stmt list)

    (define/override (uniquify-exp env)
      (lambda (e)
	(match e
          [(Void) (Void)]
          [(HasType e t)
           (HasType ((uniquify-exp env) e) t)]
          [else ((super uniquify-exp env) e)]
          )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; expose-allocation


    (define/public (expose-alloc-vector es vec-type alloc-exp)
         (define e* (for/list ([e es]) (expose-alloc-exp e)))
         ;; 1. evaluate the e* and let-bind them to x*
         ;; 2. allocate the vector
         ;; 3. initialize the vector
         ;; Step 1 comes before step 2 because the e* may trigger GC!
         (define len  (length e*))
         (define size (* (+ len 1) 8))
         (define vec (gensym 'alloc))
         
         ;; step 1
         (define-values (bndss inits)
           (for/lists (l1 l2) ([e e*])
             (cond [(atm? e) (values '() e)]
                   [else
                    (define tmp (gensym 'vecinit))
                    (values (list (cons tmp e)) (Var tmp))])))
         (define bnds (append* bndss))

         ;; step 3
         (define init-vec (foldr
                           (lambda (init n rest)
                             (let ([v (gensym '_)])
                               (Let v
                                    (Prim 'vector-set!
                                          (list (Var vec) (Int n) init))
                                    rest)))
                           (Var vec)
                           inits
                           (range len)))

         ;; step 2 (and include step 3)
         (define voidy (gensym '_))
         (define alloc-init-vec
            (Let voidy
                  (If (Prim '< (list (Prim '+ (list (GlobalValue 'free_ptr)
                                                    (Int size)))
                                     (GlobalValue 'fromspace_end)))
                      (Void)
                      (Collect size))
                  (Let vec alloc-exp init-vec)))
         
         ;; combine 1 and 2-3
         (make-lets bnds alloc-init-vec)
      )
    
    (define/public (expose-alloc-exp e)
      (verbose "expose-alloc-exp" e)
      (match e
        [(HasType (Prim 'vector es) vec-type)
         (define len  (length es))
         (expose-alloc-vector es vec-type (Allocate len vec-type))]
        [(Prim 'vector es)
         (error 'expose-alloc-exp "expected has-type around vector ~a" e)]
        #;[(HasType e t)
         (HasType (expose-alloc-exp e) t)]
        [(Var x) (Var x)]
        [(Int n) (Int n)]
        [(Bool b) (Bool b)]
        [(Void) (Void)]
        [(If cnd thn els)
         (If (expose-alloc-exp cnd)
             (expose-alloc-exp thn) (expose-alloc-exp els))]
        [(Prim op es) 
         (define new-es (map (lambda (e) (expose-alloc-exp e)) es))
         (Prim op new-es)]
        [(Let x rhs body)
         (Let x (expose-alloc-exp rhs)
              (expose-alloc-exp body))]
        ))

    (define/public (expose-allocation e)
      (verbose "expose-allocation" e)
      (match e
        [(Program info body)
         (Program info (expose-alloc-exp body))]
        [else
         (error "in expose-allocation, unmatched" e)]))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; remove-complex-opera*

    (define/override (rco-atom e)
      (verbose "R3/rco-atom" e)
      (match e
        [(Void)
         (values (Void) '())]
        [(Collect size)
         (define tmp (gensym 'tmp))
         (values (Void) `((,tmp . ,(Collect size))))]
        [(Allocate len type)
         (define tmp (gensym 'alloc))
         (values (Var tmp) `((,tmp . ,(Allocate len type))))]
        [(GlobalValue name)
         (define tmp (gensym 'tmp))
         (values (Var tmp) `((,tmp . ,(GlobalValue name))))]
        [else
         (verbose "R3/rco-atom super case" e)
         (super rco-atom e)]
        ))
    
    (define/override (rco-exp e)
      (verbose "R3/rco-exp" e)
      (match e
        [(Void)
         (Void)]
        [(Collect size)
         (Collect size)]
        [(Allocate len type)
         (Allocate len type)]
        [(GlobalValue name)
         (GlobalValue name)]
        #;[(Prim op es)
         (define-values (new-es sss)
           (for/lists (l1 l2) ([e es]) (rco-atom e)))
         (make-lets (append* sss) (Prim op new-es))]
        #;[(HasType e t)
         (verbose "R3/rco-exp has-type case" e)
         (HasType (rco-exp e) t)]
        [else
         (verbose "R3/rco-exp super case" e)
         (super rco-exp e)]
        ))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; explicate-control

    ;; explicate-tail : exp -> tail
    (define/override (explicate-tail e)
      (match e
        [(Void) (delay (Return (Void)))]
        [else (super explicate-tail e)]
        ))

    (define/override (basic-exp? e)
      (match e
        [(Allocate len type) #t]
        [(GlobalValue name) #t]
        [(Void) #t]
        [else (super basic-exp? e)]
        ))

    ;; explicate-assign : exp * var * tail -> tail
    (define/override (explicate-assign e x cont-block)
      (match e
        [(Collect size) (delay (Seq (Collect size) (force cont-block)))]
        [else (super explicate-assign e x cont-block)]
        ))

    (define/override (explicate-pred cnd thn-block els-block)
      (match cnd
        [(Prim op es)
         #:when (set-member? (vector-primitives) op)
         (define tmp (gensym 'tmp))
         (define cnd-block
           (generic-explicate-pred (Var tmp) thn-block els-block))
         (delay (Seq (Assign (Var tmp) cnd) cnd-block))]
        [else (super explicate-pred cnd thn-block els-block)]
        ))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; select-instructions : C2 -> psuedo-x86

    (define/public (root-type? t)
      (match t
        [`(Vector ,T ...)
         #t]
        [else #f]))
    
    (define/override (select-instr-arg e)
      (match e
        [(Void) (Imm 0)]
        [else (super select-instr-arg e)]
        ))

    (field [tmp-vec-reg 'r11])
    
    (define/override (select-instr-stmt e)
      (verbose "R3/select-instr-stmt" e)
      (match e
        [(Assign lhs (Void))
         (list (Instr 'movq (list (Imm 0) (select-instr-arg lhs))))]
        [(Assign lhs (GlobalValue name))
         (list (Instr 'movq (list (Global name) (select-instr-arg lhs))))]
        [(Assign lhs (Allocate len `(Vector ,ts ...)))
         (define lhs^ (select-instr-arg lhs))
         ;; Add one quad word for the meta info tag
         (define size (* (add1 len) 8))
         ;;highest 7 bits are unused
         ;;lowest 1 bit is 1 saying this is not a forwarding pointer
         (define is-not-forward-tag 1)
         ;;next 6 lowest bits are the length
         (define length-tag (arithmetic-shift len 1))
         ;;bits [6,56] are a bitmask indicating if [0,50] are pointers
         (define ptr-tag
           (for/fold ([tag 0]) ([t (in-list ts)] [i (in-naturals 7)])
             (bitwise-ior tag (arithmetic-shift (b2i (root-type? t)) i))))
         ;; Combine the tags into a single quad word
         (define tag (bitwise-ior ptr-tag length-tag is-not-forward-tag))
         (list (Instr 'movq (list (Global 'free_ptr) (Reg tmp-vec-reg)))
               (Instr 'addq (list (Imm size) (Global 'free_ptr)))
               (Instr 'movq (list (Imm tag) (Deref tmp-vec-reg 0)))
               (Instr 'movq (list (Reg tmp-vec-reg) lhs^))
               )
         ]
        [(Collect size)
         (list (Instr 'movq (list (Reg rootstack-reg) (Reg 'rdi)))
               (Instr 'movq (list (select-instr-arg (Int size)) (Reg 'rsi)))
               (Callq 'collect 2))]
        [(Assign lhs (Prim 'vector-ref (list e-vec i)))
         ;; We should try to do this in patch instructions
         (define lhs^ (select-instr-arg lhs))
         (define e-vec^ (select-instr-arg e-vec))
         (define new-i (match (select-instr-arg i) [(Imm i) i]))
         (list (Instr 'movq (list e-vec^ (Reg tmp-vec-reg)))
               (Instr 'movq (list (Deref tmp-vec-reg (* (add1 new-i) 8)) lhs^)))]
        [(Assign lhs (Prim 'vector-length (list e-vec)))
         (define lhs^ (select-instr-arg lhs))
         (define e-vec^ (select-instr-arg e-vec))
         (list (Instr 'movq (list e-vec^ (Reg tmp-vec-reg)))
               (Instr 'movq (list (Deref tmp-vec-reg 0) (Reg tmp-vec-reg)))
               (Instr 'andq (list (Imm 126) (Reg tmp-vec-reg)))
               (Instr 'sarq (list (Imm 1) (Reg tmp-vec-reg)))
               (Instr 'movq (list (Reg tmp-vec-reg) lhs^))
               )]
        [(Assign lhs (Prim 'vector-set! (list e-vec i e-arg)))
         (define new-lhs (select-instr-arg lhs))
         (define new-e-vec (select-instr-arg e-vec))
         (define new-i (match (select-instr-arg i) [(Imm i) i]))
         (define new-e-arg (select-instr-arg e-arg))
         (list (Instr 'movq (list new-e-vec (Reg tmp-vec-reg)))
               (Instr 'movq (list new-e-arg
                                  (Deref tmp-vec-reg (* (add1 new-i) 8))))
               (Instr 'movq (list (Imm 0) new-lhs)))]
        [else (super select-instr-stmt e)]
        ))
        
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uncover-live

    (define/override (free-vars a)
      (match a
        [(Global l) (set)]
        [else (super free-vars a)]
        ))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (define/override (build-interference-instr live-after G loc-types)
      (lambda (ast)
	(match ast
          [(Callq f _)
           (cond [(eq? f 'collect)
                  (for ([v live-after])
                    (cond [(and (not (set-member? registers v))
                                (root-type? (dict-ref loc-types v)))
                           (for ([u (callee-save-for-alloc)])
                             (add-edge! G u v))]))]
                 [else (void)])
           ((super build-interference-instr live-after G) ast)]
          [else
           ((super build-interference-instr live-after G) ast)]
          )))

    (define/override (build-interference-block G loc-types)
      (lambda (block)
        (match block
          [(Block info ss)
           (define lives (dict-ref info 'lives))
           ;; pull off the live-before of the first instruction.
           (define live-afters (cdr lives))
           (define new-ss 
             (for/list ([inst ss] [live-after live-afters])
               ((build-interference-instr live-after G loc-types) inst)))
           (define new-info (dict-remove info 'lives))
           (Block new-info new-ss)]
          [else (error "R3/build-interference-block unhandled" block)]
          )))

    (define/override (build-interference ast)
      (match ast
        [(Program info (CFG cfg))
         (define loc-types (lookup 'locals-types info))
         (define locals (map car loc-types))
         (define IG (undirected-graph '()))
         (for ([v locals])
           (add-vertex! IG v))
         (define new-CFG
           (for/list ([b cfg])
             (cons (car b) ((build-interference-block IG loc-types) (cdr b)))))
         (print-dot IG "./interfere.dot")
         (define new-info
           (dict-set-all info `((locals . ,locals)
                                (locals-types . ,loc-types)
                                (conflicts . ,IG))))
         (Program new-info (CFG new-CFG))]
        ))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; allocate-registers

    (define/override (valid-color c v unavail-colors info)
      (define loc-types (dict-ref info 'locals-types))
      (and (not (set-member? unavail-colors c))
           (or (< c (num-registers-for-alloc))
               (and (root-type? (dict-ref loc-types v)) 
                    (even? c))
               (and (not (root-type? (dict-ref loc-types v)))
                    (odd? c)))))

    (define/override (init-num-spills)
      (cons 0 0))

    (define/override (update-num-spills spills c)
      (match spills
        [`(,stack-spills . ,root-spills)
         (cond [(>= c (num-registers-for-alloc))
                (if (odd? c)
                    (cons (add1 stack-spills) root-spills)
                    (cons stack-spills (add1 root-spills)))]
               [else
                spills]
               )]))

    (define/override (record-num-spills info num-spills)
      (dict-set (dict-set info 'num-spills (car num-spills))
                'num-root-spills (cdr num-spills)))
    
    (define/override (assign-homes-imm homes)
      (lambda (e)
        (match e
          [(Global l) e]
          [else
	   ((super assign-homes-imm homes) e)])))
    
    (define/override (assign-homes-instr homes)
      (lambda (e)
        (match e
          [(Instr 'set (list 'l e))
           (define new-e ((assign-homes-imm homes) e))
           (Instr 'set (list 'l new-e))]
          [else
           ((super assign-homes-instr homes) e)]
          )))

    (define/override (identify-home num-used-callee c)
      (define n (num-registers-for-alloc))
      (cond
        [(< c n)
         (Reg (color->register c))]
        [(even? c) ;; root stack
         (define new-c (floor (/ (- c n) 2)))
         (define offset (- (* (add1 new-c) (variable-size))))
         (Deref rootstack-reg offset)]
        [(odd? c) ;; regular stack
         (define new-c (floor (/ (- c n) 2)))
         (define offset (- (+ (first-offset num-used-callee)
                              (* new-c (variable-size)))))
         (Deref 'rbp offset)]
        ))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; patch-instructions : psuedo-x86 -> x86

    (define/override (in-memory? a)
      (match a
        [(Global l) #t]
        [else (super in-memory? a)]))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; print-x86 : x86 -> string

    (define/override (print-x86-imm e)
      (match e
        [(Global label)
         (format "~a(%rip)" (label-name label))]
        [else (super print-x86-imm e)]
        ))

    (define/override (print-x86 e)
      (match e
        [(Program info (CFG cfg))
         (define spills (dict-ref info 'num-spills))
         (define root-spills (dict-ref info 'num-root-spills))
         (define stack-space (* (variable-size) spills))
         (define root-space (* (variable-size) root-spills))

         (define used-callee (set->list (dict-ref info 'used-callee)))
         (define save-callee-reg
           (for/list ([r used-callee])
             (format "\tpushq\t%~a\n" r)))
         (define restore-callee-reg
           (for/list ([r (reverse used-callee)])
             (format "\tpopq\t%~a\n" r)))
         (define callee-space (* (length used-callee) (variable-size)))
         
         (define stack-adj (- (align (+ callee-space stack-space) 16)
                              callee-space))
         (define initialize-heaps
           (string-append
            (format "\tmovq\t$~a, %rdi\n" (rootstack-size))
            (format "\tmovq\t$~a, %rsi\n" (heap-size))
            (format "\tcallq\t~a\n" (label-name "initialize"))
            (format "\tmovq\t~a, %~a\n" 
                    (print-x86-imm (Global 'rootstack_begin))
                    rootstack-reg)))
         (define initialize-roots
           (for/list ([i (range root-spills)])
             (string-append 
              (format "\tmovq $0, (%~a)\n" rootstack-reg)
              (format "\taddq $~a, %~a\n" 
                      (variable-size) rootstack-reg))))
         (string-append
          (string-append*
           (for/list ([(label block) (in-dict cfg)])
             (string-append (format "~a:\n" (label-name label)) 
                            (print-x86-block block))))
          "\n"
          (format "\t.globl ~a\n" (label-name "main"))
          (format "~a:\n" (label-name "main"))
          (format "\tpushq\t%rbp\n")
          (format "\tmovq\t%rsp, %rbp\n")
          (string-append* save-callee-reg)
          (format "\tsubq\t$~a, %rsp\n" stack-adj)
          initialize-heaps
          (string-append* initialize-roots)
          (format "\tjmp\t\t~a\n" (label-name 'start))
          (format "~a:\n" (label-name 'conclusion))
          (format "\tsubq\t$~a, %~a\n" root-space rootstack-reg)
          (format "\taddq\t$~a, %rsp\n" stack-adj)
          (string-append* restore-callee-reg)
          (format "\tpopq\t%rbp\n")
          (format "\tretq\n"))]
        ))

    ));; new-compile-R3

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Passes

(define vectors-passes
  (let ([compiler (new compile-R3)])
    `(("shrink"
       ,(lambda (p) (send compiler shrink p))
       ,interp-R3
       ,type-check-R3)
      ("uniquify"
       ,(lambda (p) (send compiler uniquify p))
       ,interp-R3
       ,type-check-R3)
      ("partial-eval"
       ,(lambda (p) (send compiler partial-eval p))
       ,interp-R3)
      ("expose allocation"
       ,(lambda (p) (send compiler expose-allocation p))
       ,interp-R3-prime
       ,type-check-R3)
      ("remove-complex-opera*"
       ,(lambda (p) (send compiler remove-complex-opera* p))
       ,interp-R3-prime
       ,type-check-R3)
      ("explicate-control"
       ,(lambda (p) (send compiler explicate-control p))
       ,interp-C2
       ,type-check-C2)
      ("select-instructions"
       ,(lambda (p) (send compiler select-instructions p))
       ,interp-pseudo-x86-2)
      ("uncover-live"
       ,(lambda (p) (send compiler uncover-live p))
       ,interp-pseudo-x86-2)
      ("build-interference"
       ,(lambda (p) (send compiler build-interference p))
       ,interp-pseudo-x86-2)
      ("build-move-graph"
       ,(lambda (p) (send compiler build-move-graph p))
       ,interp-pseudo-x86-2)
      ("allocate-registers"
       ,(lambda (p) (send compiler allocate-registers p))
       ,interp-x86-2)
      ("remove-jumps"
       ,(lambda (p) (send compiler remove-jumps p))
       ,interp-x86-2)
      ("patch-instructions"
       ,(lambda (p) (send compiler patch-instructions p))
       ,interp-x86-2)
      ("print-x86"
       ,(lambda (p) (send compiler print-x86 p))
       #f)
      )))
