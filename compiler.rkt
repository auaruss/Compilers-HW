#lang racket
(require racket/set racket/stream)
(require graph)
(require racket/fixnum)
(require "interp-R0.rkt")
(require "interp-R1.rkt")
(require "interp.rkt")
(require "utilities.rkt")
(provide (all-defined-out))
(require racket/dict)
(require racket/set)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; R0 examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (Prim '- (list (flip-exp e1)))]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (flip-exp e2) (flip-exp e1)))]
    ))

(define (flip-R0 e)
  (match e
    [(Program info e) (Program info (flip-exp e))]
    ))


;; Next we have the partial evaluation pass described in the bzook.
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]
    ))

(define (pe-R0 p)
  (match p
    [(Program info e) (Program info (pe-exp e))]
    ))

(define (test-pe p)
  (assert "testing pe-R0"
     (equal? (interp-R0 p) (interp-R0 (pe-R0 p)))))

(test-pe (parse-program `(program () (+ 10 (- (+ 5 3))))))
(test-pe (parse-program `(program () (+ 1 (+ 3 1)))))
(test-pe (parse-program `(program () (- (+ 3 (- 5))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uniquify-exp
  (λ (symtab)
    (λ (exp)
      (match exp
        [(Var x)
         (Var (symbol-table-lookup symtab x))]
        [(Int n) (Int n)]
        [(Let x e body)
         (let ([new-x (gensym x)]) 
           (Let new-x
                ((uniquify-exp symtab) e)
                ((uniquify-exp (extend-symbol-table symtab x new-x)) body)))]
        [(Prim op es)
         (Prim op (for/list ([e es]) ((uniquify-exp symtab) e)))]))))


(define init-symbol-table
  (λ ()
    (let ([init (make-immutable-hash)]) init)))

(define symbol-table-lookup
  (λ (symtab x)
    (if (empty? (hash-ref symtab x)) (error "variable not in scope") (car (hash-ref symtab x)))))

(define extend-symbol-table
  (λ (symtab x new-x)
    (hash-set symtab
              x
              (let [(not-found (λ () '()))]
                (cons new-x (hash-ref symtab x not-found))))))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e)
     (Program info ((uniquify-exp (init-symbol-table)) e))]
    ))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
    (match p
      [(Program info e)
       (Program info (rco-exp e))]))

(define map-values
    (λ (f ls)
      (cond
        [(empty? ls)
         (values '() '())]
        [(cons? ls) (define-values (v1 v2) (f (car ls)))
                    (define-values (ls1 ls2) (map-values f (cdr ls)))
                    (values (cons v1 ls1) (cons v2 ls2))])))

(define rco-atom
  (λ (e)
    (match e
      [(Var x) (values e '())]
      [(Int n) (values e '())]
      [(Let x e body)
       (let ([v (gensym 'tmp)])
                 (values
                  (Var v)
                  (list (cons v (Let x (rco-exp e) (rco-exp body))))))] ;; rco-atom on body, no gensym
      [(Prim op es)
       (define-values (exps syms)
         (map-values
          (λ (e)
            (cond [(or (Var? e) (Int? e))
                   (rco-atom e)]
                  [else (let ([v (gensym 'tmp)])
                          (define-values (_1 _2) (rco-atom e))
                          (values (Var v)
                                  (cons (cons v _1) _2)))]))
          es))
       (let ([v (gensym 'tmp)])
         (values (Var v)
                 (cons (cons v (Prim op exps)) (append* syms))))])))
(define rco-exp
  (λ (e)
    (match e
      [(Var x) (Var x)]
      [(Int n) (Int n)]
      [(Let x e body) (Let x (rco-exp e) (rco-exp body))]
      [(Prim op es)
       (define-values (exps symbols) (map-values rco-atom es))
       (foldl
        (λ (elem acc)
          (if (empty? elem) acc (Let (car elem) (cdr elem) acc)))
        (Prim op exps)
        (append* (reverse symbols)))])))

(define rp (Program '() (Prim '+ (list (Prim '- (list (Prim 'read '()))) (Prim 'read '())))))

;; Sam

; explicate-tail : R1 -> C0Tail x [Var]
; takes in R1 expression and produces C0 Tail and list of let-bound variables
(define (explicate-tail r1exp)
  (match r1exp
    [(Int n)
     (values (Return (Int n)) '())]
    [(Prim 'read '())
     (values (Return (Prim 'read '())) '())]
    [(Prim '- (list e))
     (values (Return (Prim '- (list e))) '())]
    [(Prim '+ (list e1 e2))
     (values (Return (Prim '+ (list e1 e2))) '())] 
    [(Var x)
     (values (Return (Var x)) '())]
    [(Let x e body) 
     (define-values (c0tail let-binds) (explicate-tail body))
     (define-values (c0tail^ let-binds^) (explicate-assign e (Var x) c0tail)) ;; why var here
     (values c0tail^ (cons x (append let-binds let-binds^)))]))


; explicate-assign : R1 Var C0Tail -> C0Tail x [Var]
; takes in R1 expression, the variable where it will be assigned, and a C0Tail that comes
; after the assignment. Returns a C0Tail and list of variables

;; simplify

(define (explicate-assign r1exp v c)
  (match r1exp
    [(Int n)
     (values (Seq (Assign v (Int n)) c) '())]
    [(Prim 'read '())
     (values (Seq (Assign v (Prim 'read '())) c) '())]
    [(Prim '- (list e))
     (values (Seq (Assign v (Prim '- (list e))) c)
             '())] 
    [(Prim '+ (list e1 e2))
     (values (Seq (Assign v (Prim '+ (list e1 e2))) c)
             '())] 
    [(Var x)
     (values (Seq (Assign v (Var x)) c) '())]
    [(Let x e body) 
     (define-values (c0tail let-binds) (explicate-assign body v c))
     (define-values (c0tail^ let-binds^) (explicate-assign e (Var x) c0tail))
     (values c0tail^ (cons x (append let-binds let-binds^)))]))

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (match p
    [(Program info e)
     (define-values (c0t let-binds) (explicate-tail e))
     (Program (cons (cons 'locals let-binds) info) (CFG (list (cons 'start c0t))))]))

(define given-let (Let 'x (Let 'y (Prim '- (list (Int 42))) (Var 'y)) (Prim '- (list (Var 'x)))))
(define r1program-let (Program '() given-let))

(define new-let (Let 'x (Prim 'read '()) (Let 'y (Prim 'read '())
                                              (Prim '+ (list (Var 'x) (Prim '- (list (Var 'y))))))))

(define newprog (Program '() new-let))

(define asdf (Program '() (Let 'x (Prim '+ (list (Prim 'read '()) (Prim 'read '()))) (Var 'x))))

;; todo: more testing!

;; note: explicate-control passes all tests in run-tests.rkt

; atm? : c0exp -> bool

(define (atm? c0exp)
    (match c0exp
      [(Int n) true]
      [(Var x) true]
      [_ false]))

; sel-ins-atm : C0atm -> pseudo-x86
; takes in a c0 atom and converts to pseudo-x86

(define (sel-ins-atm c0a)
  (match c0a
    [(Int n) (Imm n)]
    [(Var x) (Var x)]))

; sel-ins-stmt : C0stmt -> pseudo-x86
; takes in a c0 statement and converts to pseudo-x86

(define (sel-ins-stmt c0stmt)
  (match c0stmt
    [(Assign v e)
     (if (atm? e)
         (list (Instr 'movq (list (sel-ins-atm e) v)))
         (match e
           [(Prim 'read '())
            (list (Callq 'read_int)
                  (Instr 'movq (list (Reg 'rax) v)))]
           [(Prim '- (list atm))
            (define x86atm (sel-ins-atm atm))
            (if (equal? x86atm v)
                (list (Instr 'negq (list v)))
                (list (Instr 'movq (list x86atm v))
                      (Instr 'negq (list v))))]
           [(Prim '+ (list atm1 atm2))
            (define x86atm1 (sel-ins-atm atm1))
            (define x86atm2 (sel-ins-atm atm2))
            (cond [(equal? x86atm1 v) (list (Instr 'addq (list x86atm2 v)))]
                  [(equal? x86atm2 v) (list (Instr 'addq (list x86atm1 v)))]
                  [else (list (Instr 'movq (list x86atm1 v))
                              (Instr 'addq (list x86atm2 v)))])]))]))

; sel-ins-tail : C0tail -> pseudo-x86
; takes in a c0 tail and converts it ot pseudo-x86

(define (sel-ins-tail c0t)
  (match c0t
    [(Return e)
     (append (sel-ins-stmt (Assign (Reg 'rax) e))
             (list (Jmp 'conclusion)))]
    [(Seq stmt tail)
     (define x86stmt (sel-ins-stmt stmt))
     (define x86tail (sel-ins-tail tail))
     (append x86stmt x86tail)]))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (match p
    [(Program info (CFG es))
     (Program info (CFG (for/list ([ls es]) (cons (car ls) (Block '() (sel-ins-tail (cdr ls)))))))]))

;; I think this is right...
;; todo: check/test !

;; note: select-instructions passes all tests in run-tests.rkt

;; /Sam


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;  Assignment 2 Work (Replaces assign-homes)    ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; uncover-live

(define (instr-arg-varset arg)
  (match arg 
	 [(Var v) (set (Var v))]
	 [_ (list->set '())]))

(define (instr-read-varset instr) 
  (match instr
	 [(Instr 'movq (list e1 e2))
	  (instr-arg-varset e1)]
	 [(Instr op (list e1 e2))
	  (set-union (instr-arg-varset e1) (instr-arg-varset e2))]
	 [(Instr 'negq (list e1))
	  (instr-arg-varset e1)]
	 [_ (list->set '())]))

(define (instr-written-varset instr)
  (match instr
	 [(Instr op (list e1 e2))
	  (instr-arg-varset e2)]
	 [(Instr 'negq (list e1))
	  (instr-arg-varset e1)]
	 [_ (list->set '())]))

(define (uncover-live-helper instr-ls live-after-set)
  (cond
    [(null? instr-ls) (list (list->set '()))]
    [else (let ([new-live-after-set (set-union (set-subtract live-after-set (instr-written-varset (car instr-ls))) (instr-read-varset (car instr-ls)))]) 
	  (append (uncover-live-helper (cdr instr-ls) new-live-after-set) (list live-after-set)))]
    ))


(define (uncover-live p)
  (match p
    [(Program info (CFG es)) 
     (Program info (CFG (for/list ([ls es]) (cons (car ls) (match (cdr ls)
							     [(Block b-info instr-ls) 
							      (Block (uncover-live-helper (reverse instr-ls) (list->set '())) instr-ls)])))))]
    ))

;;Test from book chapter 3
(define ch3example (Let 'v (Int 1) (Let 'w (Int 46) (Let 'x (Prim '+ (list (Var 'v) (Int 7))) (Let 'y (Prim '+ (list (Int 4) (Var 'x))) (Let 'z (Prim '+ (list (Var 'x) (Var 'w))) (Prim  '+ (list (Var 'z) (Prim '- (list (Var 'y)))))))))))
(define ch3program (Program '() ch3example))
;;match case used to print the block's info
#;(uncover-live (select-instructions (explicate-control (remove-complex-opera* (uniquify ch3program)))))
#;(match (uncover-live (select-instructions (explicate-control (remove-complex-opera* (uniquify ch3program)))))
       [(Program info (CFG es))
	(match (cdr (car es)) 
	       [(Block b-info instr-ls) b-info])])

;; build-interference
(define CALLER-SAVED-REGISTERS
  '(rax rdx rcx rsi rdi r8 r9 r10 r11))

(define (build-interference p)
  (match p
    [(Program info (CFG es))
     (let ([l-after-k-and-instrs (match (cdr (car es)) 
                                   [(Block b-info instr-ls) (zip b-info instr-ls)])])
       (Program
        (cons (list 'conflicts
                    (foldr (λ (pr g) (bi-helper (car pr) (cdr pr) g)) (undirected-graph '()) l-after-k-and-instrs)))
        (CFG es)))]))

(define (bi-helper s instr g)
  (let ([ls (set->list s)])
    (if (empty? ls)
        g
        (match instr
          [(or (Instr 'addq (list s d))
               (Instr 'subq (list s d))) 
           (for/list ([v ls]) (if (eq? v d) 0 ; This 0 is just some dummy value so we don't do the mutation.
                                  (add-edge! g d v)))]
          [(Instr 'callq label)
           (for/list ([v ls]) (for/list ([r CALLER-SAVED-REGISTERS]) (add-edge! g r v)))]
          [(Instr 'movq (list s d))
           (for/list ([v ls]) (if (or (eq? v d) (eq? v s)) 0 ; This 0 is just some dummy value so we don't do the mutation.
                                  (add-edge! g d v)))]
          [whatever g]))
    g))

(define (zip l1 l2)
  (if (or (empty? l1) (empty? l2))
      '()
      (cons (cons (car l1) (car l2)) (zip (cdr l1) (cdr l2)))))

(build-interference (uncover-live (select-instructions (explicate-control (remove-complex-opera* ch3program)))))
(get-edges (build-interference (uncover-live (select-instructions (explicate-control (remove-complex-opera* ch3program))))))

;; allocate-registers

;; get-longest : [List] -> List
;; gets longest list in list of lists

(define (get-longest ls)
  (if (empty? ls)
      '()
      (if (>= (length (first ls))
              (length (get-longest (rest ls))))
          (first ls)
          (get-longest (rest ls)))))

;; get-longest-val : [Hash Any List] -> List
;; get the longest value in hash

(define (get-longest-val hash)
  (let ([vals (hash-values hash)])
    (get-longest vals)))

;; choose-least : [Nat] Nat -> Nat
;; returns the smallest Nat not in the given set

(define (choose-least satset cand)
  (if (empty? satset)
      cand
      (let ([m (apply min satset)])
        (if (< cand m)
            cand
            (choose-least (remove m satset) (add1 cand))))))

;; hash-key : [Hash Key Val] Val -> Key
;; returns the (a) key that maps to given val

(define (hash-key hash val)
  (local
    [(define (first-cdr ls v)
        (if (empty? ls)
            (error "val not found")
            (if (equal? (cdr (car ls)) v)
                (car (car ls))
                (first-cdr (cdr ls) v))))]
    (first-cdr (hash->list hash) val)))

;; A SatSet is a set of nats (colors)

;; color-graph : InterferenceGraph -> [Hash Var SatSet] -> [(Var . Nat)]
;; takes an unweighted/undirected intereference graph and a mutable hashtable of vars to saturation sets
;; in program, returns mapping from var to color (Nat)

;; interference graph from book example
(define ig1 (unweighted-graph/undirected '((t z) (z y) (z w) (y w) (x w) (w v))))
(define h1 (make-hash '((t . ()) (z . ()) (y . ()) (w . ()) (x . ()) (v . ()))))
(define testhash (hash 't '(a e w) 'z '() 'y '(w q f f d) 'w '() 'x '(z a) 'v '(e)))

(define (color-graph ig hash)
  (if (hash-empty? hash)
      empty
      (let* ([maxsat (get-longest-val hash)]
             [maxsat-vert (hash-key hash maxsat)]
             [adj-verts (get-neighbors ig maxsat-vert)]
             [col (choose-least maxsat 0)])
        (for-each (λ (vert) (if (hash-has-key? hash vert)
                                (hash-set! hash vert
                                           (cons col (hash-ref hash vert)))
                                hash))
                      adj-verts)
        (hash-remove! hash maxsat-vert)
        (cons `(,maxsat-vert . ,col) (color-graph ig hash)))))

;; allocate-registers-exp : pseudo-x86 InterferenceGraph [Var] -> pseudo-x86
;; takes in pseudo-x86 exp, intereference graph, and list of vars, returns
;; a pseudo-x86 exp with allocated registers according to color-graph

(define (allocate-registers-exp e ig vars)
  (let* ([hash (make-hash (map (λ (var) `(,var . ())) vars))]
         [coloring (color-graph ig hash)])
    coloring))

;; assign-homes : pseudo-x86 -> pseudo-x86

(define (calc-stack-space ls)
  (cond
    [(null? ls) 0]
    [else (+ 8 (calc-stack-space (cdr ls)))]
    ))

(define (find-index v ls)
  (cond
    ;;[(eq? v (Var-name (car ls))) 1]
    [(eq? v (car ls)) 1]
    [else (add1 (find-index v (cdr ls)))]
    ))

;; simplify
;; todo: FIX PUSHQ/POPQ

(define (assign-homes-exp e ls)
  (match e
    [(Reg reg) (Reg reg)]
    [(Imm int) (Imm int)]
    [(Var v) (Deref 'rbp (* -8 (find-index v (cdr ls))))]
    [(Instr 'addq (list e1 e2)) (Instr 'addq (list (assign-homes-exp e1 ls) (assign-homes-exp e2 ls)))]
    [(Instr 'subq (list e1 e2)) (Instr 'subq (list (assign-homes-exp e1 ls) (assign-homes-exp e2 ls)))]
    [(Instr 'movq (list e1 e2)) (Instr 'movq (list (assign-homes-exp e1 ls) (assign-homes-exp e2 ls)))]
    [(Instr 'negq (list e1)) (Instr 'negq (list (assign-homes-exp e1 ls)))]
    [(Callq l) (Callq l)]
    [(Retq) (Retq)]
    [(Instr 'pushq (list e1)) (Instr 'pushq (list (assign-homes e1 ls)))]
    [(Instr 'popq (list e1)) (Instr 'popq (list (assign-homes e1 ls)))]
    [(Jmp e1) (Jmp e1)]
    [(Block info es) (Block info (for/list ([e es]) (assign-homes-exp e ls)))]
    ))

(define (assign-homes p)
  (match p
    [(Program info (CFG es)) (Program (list (cons 'stack-space (calc-stack-space (cdr (car info))))) (CFG (for/list ([ls es]) (cons (car ls) (assign-homes-exp (cdr ls) (car info))))))]
    ))

;; note: assign-homes passes all tests in run-tests.rkt

;;TEST
;;(assign-homes (Program (list (cons 'locals (list (Var 'x) (Var 'y)))) (CFG (list (cons 'start (Block '() (list (Instr 'movq (list (Imm 42) (Var 'y))) (Instr 'negq (list (Var 'y))) (Instr 'movq (list (Var 'y) (Var 'x))) (Instr 'movq (list (Var 'x) (Reg 'rax))) (Instr 'negq (list (Reg 'rax))) (Jmp 'conclusion))))))))
;;(assign-homes (select-instructions (explicate-control r1program-let)))
;;(let ([x (+ (read) (read))]) x)
;(remove-complex-opera* (uniquify (Program '() (Let 'x (Prim '+ (list (Prim 'read '()) (Prim 'read '()))) (Var 'x)))))


;; Grant

;; patch-instructions : psuedo-x86 -> x86

(define (patch-instructions-instr px86instr)
  (match px86instr
    [(Instr op (list e1 e2)) 
     (match (list e1 e2)
       [(list (Deref a b) (Deref c d)) (list (Instr 'movq (list e1 (Reg 'rax))) (Instr op (list (Reg 'rax) e2)))]
       [(list x y) (list (Instr op (list e1 e2)))]
       )]
    [(Instr op (list e1)) (list (Instr op (list e1)))]
    [i (list i)]
    ))

(define (patch-instructions-block px86block)
  (match px86block
    [(Block info es) (Block info (append* (for/list ([i es]) (patch-instructions-instr i))))]
    ))

(define (patch-instructions p)
  (match p
    [(Program info (CFG es)) (Program info (CFG (for/list ([ls es]) (cons (car ls) (patch-instructions-block (cdr ls))))))]
    ))

;;TEST
;;(patch-instructions (assign-homes (select-instructions (explicate-control r1program-let))))

;;  (error "TODO: code goes here (patch-instructions)"))

;; Grant/Sam

(define x86prog (patch-instructions (assign-homes (select-instructions (explicate-control r1program-let)))))
;x86prog

(define (main-str stacksize)
  (format "\t.globl ~a\n~a:\n\tpushq\t%rbp\n\tmovq\t%rsp, %rbp\n\tsubq\t$~a, %rsp\n\tjmp ~a\n"
          (label-name "main") (label-name "main") (align stacksize 16) (label-name "start"))) ;; 16 is stack-space

(define (concl-str stacksize)
  (format "~a:\n\taddq\t$~a, %rsp\n\tpopq\t%rbp\n\tretq"
          (label-name "conclusion") (align stacksize 16))) ;; stack-space

(define (stringify-arg arg)
  (match arg
    [(Imm n) (format "$~a" n)]
    [(Reg r) (format "%~a" r)]
    [(Deref r n) (format "~a(%~a)" n r)]))

(define (stringify-in instr)
  (match instr
    [(Instr 'addq (list a1 a2))
     (define st1 (stringify-arg a1))
     (define st2 (stringify-arg a2))
     (format "addq\t~a, ~a" st1 st2)]
    [(Instr 'subq (list a1 a2))
     (define st1 (stringify-arg a1))
     (define st2 (stringify-arg a2))
     (format "subq\t~a, ~a" st1 st2)]
    [(Instr 'movq (list a1 a2))
     (define st1 (stringify-arg a1))
     (define st2 (stringify-arg a2))
     (format "movq\t~a, ~a" st1 st2)]
    [(Instr 'negq (list a))
     (define st (stringify-arg a))
     (format "negq\t~a" st)]
    [(Callq lbl)
     (format "callq\t~a" (label-name lbl))]
    [(Retq) "retq"]
    [(Instr 'pushq arg)
     (define st (stringify-arg arg))
     (format "pushq\t~a" st)]
    [(Instr 'popq arg)
     (define st (stringify-arg arg))
     (format "popq\t~a" st)]
    [(Jmp lbl)
     (format "jmp\t~a" (label-name lbl))]))

;; format-x86 : [instr] -> string
(define (format-x86 ins)
  (foldr (λ (f r) (string-append "\t" f "\n" r)) "" (map stringify-in ins)))
     
     ;(format "~a:\n\t" label)

;; print-x86 : x86 -> string
(define (print-x86 p)
  (match p
    [(Program info (CFG es)) (format "~a:\n~a~a~a"
                                     (label-name "start")
                                     (format-x86 (Block-instr* (cdr (car es))))
                                     (main-str (cdr (car info)))
                                     (concl-str (cdr (car info))))]))

;;Grant/Sam
