#lang racket
(require racket/set)
(require "utilities.rkt")
(require "functions.rkt")
(require "interp.rkt")
(require "interp-R5.rkt")
(require "type-check-R5.rkt")
(provide compile-R5 lambda-passes)

;(define typed-vars (make-parameter #f))

(define compile-R5
  (class compile-R4
    (super-new)

    (inherit select-instr-arg root-type? fun-def-name reveal-functions-def
             expose-alloc-vector)
    
    (define/override (primitives)
      (set-union (super primitives) 
		 (set 'procedure-arity 'closure)))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; shrink

    (define/override (shrink-exp e)
      (match e
        [(Lambda params rT body)
         (Lambda params rT (shrink-exp body))]
        [else
         (super shrink-exp e)]
        ))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; partial-eval : R5 -> R5

    (define/override (pe-exp env)
      (lambda (e)
	(copious "R5/pe-exp" e)
	(define recur (pe-exp env))
	(match e
          [(Prim 'procedure-arity (list e1))
           (Prim 'procedure-arity (list (recur e1)))]
          [(Lambda params rT body)
           (Lambda params rT (recur body))]
	  [else ((super pe-exp env) e)]
	  )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uniquify : env -> R5 -> R5

    (define/override (uniquify-exp env)
      (lambda (e)
	(match e
	  [(Lambda (list `[,xs : ,Ts] ...) rT body)
	   (define new-xs (for/list ([x xs]) (gensym (racket-id->c-id x))))
	   (define new-env (append (map cons xs new-xs) env))
	   (define (annotate x t) `[,x : ,t])
	   (Lambda (map annotate new-xs Ts) rT 
                   ((uniquify-exp new-env) body))]
	  [else ((super uniquify-exp env) e)])))


    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; optimize-direct-calls

    (define/public (optimize-direct-calls-exp e)
      (let ([recur (lambda (e) (optimize-direct-calls-exp e))])
      (match e
        [(Int n) (Int n)]
        [(Var x) (Var x)]
        [(Void) (Void)]
        [(Bool b) (Bool b)]
        [(HasType e t) (HasType (recur e) t)]
        [(Let x e body)
         (Let x (recur e) (recur body))]
        [(If cnd thn els)
         (If (recur cnd) (recur thn) (recur els))]
        [(Prim op es)
         (Prim op (map recur es))]
        [(Apply e es)
         (define e^ (recur e))
         (define es^ (map recur es))
         (define (optimize-apply rator rands)
           (match rator
             [(Lambda (list `[,xs : ,Ts] ...) rT body)
              (make-lets (map cons xs rands) body)]
             [(Let x rhs body)
              (Let x rhs (optimize-apply body rands))]
             [else (Apply rator rands)]))
         (optimize-apply e^ es^)]
        [(Lambda ps rT body)
         (Lambda ps rT (recur body))]
        [else (error "R5/optimize-direct-calls-exp unmatched" e)]
        )))
      
    (define/public (optimize-direct-calls-def d)
      (match d
        [(Def f ps rt info body)
         (define new-body (optimize-direct-calls-exp body))
         (Def f ps rt info new-body)]))
      
    (define/public (optimize-direct-calls p)
      (match p
        [(ProgramDefs info ds)
         (ProgramDefs info (for/list ([d ds]) (optimize-direct-calls-def d)))]
        [else
         (error "R5/optimize-direct-calls unmatched" p)]
        ))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; reveal-functions
    
    (define/override (reveal-functions-exp funs)
      (lambda (e)
	(match e
          [(Var x)
           (cond
             [(lookup x funs #f) (FunRefArity x (lookup x funs))]
             [else e])]
	  [(Lambda params rT body)
	   (Lambda params rT ((reveal-functions-exp funs) body))]
          [else ((super reveal-functions-exp funs) e)])))

    (define/public (fun-def-arity d)
      (match d
        [(Def f xs rt info body)
         (length xs)]
        [else (error 'fun-def-arity "ill-formed function definition in ~a" d)]))
    
    (define/override (reveal-functions e)
      (match e
        [(ProgramDefs info ds)
         (define funs 
           (for/list ([d ds]) 
             (cons (fun-def-name d) (fun-def-arity d))))
         (ProgramDefs info (map (reveal-functions-def funs) ds))]
        [else
         (error "R5/reveal-functions unmatched" e)]
        ))
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    ;; The following handles global functions, but what about lambda's?
    ;; How to identify lambda's? Label them?
    ;;   Wait until after closure conversion and put the labels on the Closure
    ;;   form?
    ;; Perform abstract interpretation? flow analysis?
    ;;
    ;; categorize an application as
    ;;
    ;;    * direct if only one function flow into it, and that
    ;;      function has no free variables
    ;;
    ;;    * direct/closure if only one function flow into it, and that
    ;;      function has free variables
    ;;
    ;;    * indirect if more than one function flows in and all
    ;;      functions flowing into it have no free variables
    ;;
    ;;    * indirect/closure if more than one function flows in and
    ;;      some functions flowing into it have free variables
    ;;
    ;; Idea: generate two versions of functions with no free variables,
    ;; one with the closure parameter, and one without. But then
    ;; there's the problem of figuring out which one to send where.
    
    (define/public (detect-escapees-exp e)
        (define (recur e) (detect-escapees-exp e))
        (match e
          [(Var x)    (set)]
          [(Int n)    (set)]
          [(Bool b)   (set)]
          [(Void)     (set)]
          [(FunRefArity f n) (set f)]
          [(Let x e body)
           (set-union (recur e) (recur body))]
          [(If cnd thn els)
           (set-union (recur cnd) (recur thn) (recur els))]
          [(Lambda (list `[,xs : ,Ts] ...) rT body)
           (recur body)]
          [(Apply (FunRefArity f n) es)
           (apply set-union (cons (set) (map recur es)))]
          [(Apply e es)
           (set-union (recur e) (apply set-union (cons (set) (map recur es))))]
          [(Prim op es)
           (apply set-union (cons (set) (map recur es)))]
          [(HasType e t)
           (recur e)]
          [else (error 'detect-escapees-exp "unmatched ~a" e)]
          ))
  
    (define/public (detect-escapees-def d)
      (match d
        [(Def f params rt info body)
         (detect-escapees-exp body)]
        ))
    
    (define/public (optimize-closures-exp escapees e)
      (verbose "R5/optimize-closures-exp ~a" e)
      (define (recur e) (optimize-closures-exp escapees e))
      (match e
        [(FunRefArity f n)
         #:when (set-member? escapees f)
         (values (Closure n (list (FunRef f))) '())]
        [(FunRefArity f n)
         #:when (not (set-member? escapees f))
         (values (FunRef f) '())]
        [(Apply e es)
         (define-values (new-e e-fs) (recur e))
         (define-values (new-es es-fss) (for/lists (l1 l2) ([e es])
                                          (recur e)))
         (match new-e
           [(FunRef f) ;; regular function application
            (values (Apply (FunRef f) new-es)
                    (append e-fs (apply append es-fss)))]
           [else ;; closure application
            (define-values (bnds new-e^)
              (match new-e
                [(HasType (Var c) ty)
                 (values '() (HasType (Var c) ty))]
                [else
                 (define tmp (gensym 'clos))
                 (values (list (cons tmp new-e)) (Var tmp))]))
            (define new-apply
              (make-lets bnds
                         (Apply (Prim 'vector-ref (list new-e^ (Int 0)))
                                (cons new-e^ new-es))))
            (values new-apply (append e-fs (apply append es-fss)))
            ])]

        [(Lambda (list `[,xs : ,Ts] ...) rT body)
         (define-values (new-body body-fs) (recur body))
         (define new-rT (closure-convert-type rT))
         (let* ([fun-name (gensym 'lambda)]
                [params (for/list ([x xs] [T Ts])
                          `[,x : ,(closure-convert-type T)])]
                [rm (lambda (x h) (hash-remove h x))]
                [fvs-table (hash->list (foldl rm (free-variables body) xs))]
                [fvs-expr  (map cdr fvs-table)]
                [fvT (for/list ([e fvs-expr])
                       (match e [(HasType _ t) (closure-convert-type t)]))]
                [fvs-tmp   (gensym 'fvs)])
           (define clos-type `(Vector _ ,@fvT))
           (values
            (Closure (length xs) (cons (FunRef fun-name) fvs-expr))
            (cons (Def fun-name (cons `[,fvs-tmp : ,clos-type] params) new-rT
                    '() (convert-fun-body fvs-tmp fvs-expr new-body))
                  body-fs)))]
        
        [(HasType e t)
         (let-values ([(e b*) (recur e)])
           (values (HasType e (closure-convert-type t)) b*))]
        [(or (Var _) (Int _) (Bool _))
         (values e '())]
        [(Void)
         (values (Void) '())]
        [(Let x e body)
         (define-values (new-e e-fs) (recur e))
         (define-values (new-body body-fs) (recur body))
         (values (Let x new-e new-body)
                 (append e-fs body-fs))]
        [(If cnd thn els)
         (define-values (new-cnd cnd-fs) (recur cnd))
         (define-values (new-thn thn-fs) (recur thn))
         (define-values (new-els els-fs) (recur els))
         (values (If new-cnd new-thn new-els)
                 (append cnd-fs thn-fs els-fs))]

        [(Prim op es)
         (define-values (new-es es-fss) (for/lists (ls1 ls2) ([e es])
                                          (recur e)))
         (values (Prim op new-es) (append* es-fss))]
        [else
         (error "R5/optimize-closures-exp unmatched" e)]
        ))
    
    (define/public (optimize-closures-def escapees d)
      (match d
        [(Def f params rt info body)
         (define-values (new-body body-fs)(optimize-closures-exp escapees body))
         (define new-params (for/list ([p params])
                              (match p [`[,x : ,T]
                                        `[,x : ,(closure-convert-type T)]])))
         (define new-rt (closure-convert-type rt))
         (cond [(not (set-member? escapees f))
                ;; no need for closure parameter
                (cons (Def f new-params new-rt info new-body) body-fs)]
               [else
                (define fvs-tmp (gensym 'fvs))
                (cons
                 (Def f (cons `[,fvs-tmp : _] new-params) new-rt info
                   (convert-fun-body fvs-tmp '() new-body))
                 body-fs)
                ])]
        ))
    
    ;; This replaces convert-to-closures
    (define/public (optimize-closures p)
      (match p
        [(ProgramDefs info ds)
         (define escapees
           (apply set-union (for/list ([d ds]) (detect-escapees-def d))))
         (ProgramDefs
          info
          (append* (for/list ([d ds])
                     (optimize-closures-def escapees d))))]
        ))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; convert-to-closures : env -> R5 -> R4

    (define/public (closure-convert-type t)
      (match t
        [`(Vector ,ts ...)
         (define ts^ (for/list ([t ts])
                       (closure-convert-type t)))
         `(Vector ,@ts^)]
        [`(,ts ... -> ,rt)
         (define ts^ (for/list ([t ts])
                       (closure-convert-type t)))
         (define rt^ (closure-convert-type rt))
         ;; The following isn't totally accurate but it captures how
         ;; closures are used in the code generated for application. -Jeremy
         `(Vector ((Vector _) ,@ts^ -> ,rt^))]
        [else t]
        ))
    
    ;; The returned hash table maps variable x to (HasType x t). -Jeremy
    
    ;; free-variables : expr -> (immutable-hash id expr)
    (define/public (free-variables e)
      (define (recur e) (free-variables e))
      (match e
        [(HasType (Var x) t)
         (hash x e)]
        [(HasType e t)
         (recur e)]
        [(Int n) (hash)]
        [(Bool b) (hash)]
        [(FunRef f) (hash)]
        [(Let x e body)
	 (hash-union (recur e) (hash-remove (recur body) x))]
        [(If cnd thn els)
         (hash-union (recur cnd) (recur thn) (recur els))]
	[(Lambda (list `[,xs : ,Ts] ...) rT body)
         (define (rm x h) (hash-remove h x))
         (foldl rm (recur body) xs)]
	[(Apply e es)
	 (apply hash-union (cons (recur e) (map recur es)))]
	[(Prim op es)
	 (apply hash-union (map recur es))]
        [else (error 'free-variables "unmatched ~a" e)]))

    (define/public (convert-fun-body fvs-id free-vars body)
      (let loop ([xs free-vars] [i 1])
        (match xs
          ['() body]
          [(cons (HasType (Var x) t) xs^)
           (Let x (Prim 'vector-ref (list (Var fvs-id) (Int i)))
                (loop xs^ (add1 i)))]
          [else (error 'convert-fun-body "unmatched ~a" xs)])))
      
    (define/public (convert-to-closures-exp e)
      (verbose "R5/convert-to-closures-exp ~a" e)
      (define (recur e) (convert-to-closures-exp e))
      (match e
        [(Apply e es)
         (define-values (new-e e-fs) (recur e))
         (define-values (new-es es-fss) (for/lists (l1 l2) ([e es])
                                          (recur e)))
         (define-values (bnds new-e^)
           (match new-e
             [(HasType (Var c) ty)
              (values '() (HasType (Var c) ty))]
             [else
              (define tmp (gensym 'clos))
              (values (list (cons tmp new-e)) (Var tmp))]))
         (define new-apply
           (make-lets bnds
                      (Apply (Prim 'vector-ref (list new-e^ (Int 0)))
                             (cons new-e^ new-es))))
         (values new-apply (append e-fs (apply append es-fss)))]

        [(Lambda (list `[,xs : ,Ts] ...) rT body)
         (define-values (new-body body-fs) (recur body))
         (define new-rT (closure-convert-type rT))
         (let* ([fun-name (gensym 'lambda)]
                [params (for/list ([x xs] [T Ts])
                          `[,x : ,(closure-convert-type T)])]
                [rm (lambda (x h) (hash-remove h x))]
                [fvs-table (hash->list (foldl rm (free-variables body) xs))]
                [fvs-expr  (map cdr fvs-table)]
                [fvT (for/list ([e fvs-expr])
                       (match e [(HasType _ t) (closure-convert-type t)]))]
                [fvs-tmp   (gensym 'fvs)])
           (define clos-type `(Vector _ ,@fvT))
           (values
            (Closure (length xs) (cons (FunRef fun-name) fvs-expr))
            (cons (Def fun-name (cons `[,fvs-tmp : ,clos-type] params) new-rT
                    '() (convert-fun-body fvs-tmp fvs-expr new-body))
                  body-fs)))]
        
        [(FunRefArity f n)
         (values (Closure n (list (FunRef f))) '())]
        [(HasType e t)
         (let-values ([(e b*) (recur e)])
           (values (HasType e (closure-convert-type t)) b*))]
        [(or (Var _) (Int _) (Bool _))
         (values e '())]
        [(Void)
         (values (Void) '())]
        [(Let x e body)
         (define-values (new-e e-fs) (recur e))
         (define-values (new-body body-fs) (recur body))
         (values (Let x new-e new-body)
                 (append e-fs body-fs))]
        [(If cnd thn els)
         (define-values (new-cnd cnd-fs) (recur cnd))
         (define-values (new-thn thn-fs) (recur thn))
         (define-values (new-els els-fs) (recur els))
         (values (If new-cnd new-thn new-els)
                 (append cnd-fs thn-fs els-fs))]

        [(Prim op es)
         (define-values (new-es es-fss) (for/lists (ls1 ls2) ([e es])
                                          (recur e)))
         (values (Prim op new-es) (append* es-fss))]
        [else
         (error "R5/convert-to-closures-exp unmatched" e)]
        ))

    (define/public (convert-to-closures-def e)
      (match e
        [(Def f params rt info body)
         (define-values (new-body body-fs) (convert-to-closures-exp body))
         (define new-params (for/list ([p params])
                              (match p [`[,x : ,T]
                                        `[,x : ,(closure-convert-type T)]])))
         (define new-rt (closure-convert-type rt))
         (cond [(eq? f 'main)
                (cons (Def f new-params new-rt info new-body)
                      body-fs)]
               [else
                ;; fvs-tmp is not used, because there are no free variables
                ;; so it's type doesn't matter. -Jeremy
                (define fvs-tmp (gensym 'fvs))
                (cons
                 (Def f (cons `[,fvs-tmp : _] new-params) new-rt info
                   (convert-fun-body fvs-tmp '() new-body))
                 body-fs)])]
        [else
         (error "R5/convert-to-clsoures-def" e)]
        ))
    
    (define/public (convert-to-closures e)
      (match e
        [(ProgramDefs info ds)
         (ProgramDefs info (append* (for/list ([d ds])
                                      (convert-to-closures-def d))))]
        ))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; optimize-known-calls

    (define/public (optimize-known-calls-exp closures)
      (lambda (e)
        (let ([recur (optimize-known-calls-exp closures)])
          (match e
            [(Int n) (Int n)]
            [(Var x) (Var x)]
            [(Void) (Void)]
            [(Bool b) (Bool b)]
            [(Prim 'vector-ref (list (Var c) (Int 0)))
             #:when (dict-has-key? closures c)
             (debug "closure vector-ref" c (dict-ref closures c))
             (FunRef (dict-ref closures c))]
            [(HasType e t) (HasType (recur e) t)]
            [(Let x (HasType (Closure arity (list (FunRef f) fvs ...)) clos-ty)
                  body)
             (debug "closure" x f)
             (define closures^ (cons (cons x f) closures))
             (define body^ ((optimize-known-calls-exp closures^) body))
             (Let x (HasType (Closure arity (cons (FunRef f) fvs)) clos-ty)
                  body^)]
            [(Let x e body)
             (Let x (recur e) (recur body))]
            [(If cnd thn els)
             (If (recur cnd) (recur thn) (recur els))]
            [(Prim op es)
             (Prim op (map recur es))]
            [(Apply e es)
             (define e^ (recur e))
             (define es^ (map recur es))
             (match e^
               [(Lambda (list `[,xs : ,Ts] ...) rT body)
                (make-lets (map cons xs es^) body)]
               [else (Apply e^ es^)])]
            [(Closure arity es)
             (define es^ (for/list ([e es]) (recur e)))
             (Closure arity es^)]
            [(FunRef f)
             (FunRef f)]
            [else (error "R5/optimize-known-calls-exp unmatched" e)]
            ))))
    
    (define/public (optimize-known-calls-def d)
      (match d
        [(Def f ps rt info body)
         (define new-body ((optimize-known-calls-exp '()) body))
         (Def f ps rt info new-body)]))
      
    (define/public (optimize-known-calls p)
      (match p
        [(ProgramDefs info ds)
         (ProgramDefs info (for/list ([d ds]) (optimize-known-calls-def d)))]
        [else
         (error "R5/optimize-known-calls unmatched" p)]
        ))
    

    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; limit-functions

    (define/override (limit-functions-exp args)
      (lambda (e)
	(copious "R5/limit-functions-exp" e)
	(let ([recur (limit-functions-exp args)])
          (match e
            [(Closure arity fvs)
             (Closure arity (map recur fvs))]
            [else
             ((super limit-functions-exp  args) e)]
            ))))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; expose-allocation

    (define/override (expose-alloc-exp e)
      (verbose "R5/expose-alloc-exp" e)
      (match e
        [(HasType (Closure arity es) vec-type)
         (define len  (length es))
         (expose-alloc-vector es vec-type (AllocateClosure len vec-type arity))]
        [else
         (super expose-alloc-exp e)]
        ))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; remove-complex-opera*

    (define/override (rco-atom e)
      (verbose "R5/rco-atom" e)
      (match e
        [(AllocateClosure len type arity)
         (define tmp (gensym 'alloc))
         (values (Var tmp) `((,tmp . ,(AllocateClosure len type arity))))]
        [else
         (super rco-atom e)]
        ))

    (define/override (rco-exp e)
      (verbose "R5/rco-exp" e)
      (match e
        [(AllocateClosure len type arity)
         (AllocateClosure len type arity)]
        [else
         (super rco-exp e)]
        ))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; explicate-control

    (define/override (basic-exp? e)
      (match e
        [(AllocateClosure len type arity) #t]
        [else
         (super basic-exp? e)]
        ))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; select-instructions

    (define/override (select-instr-stmt e)
      (verbose "R6/select-instr-stmt" e)
      (match e
        [(Assign lhs (AllocateClosure
                      len `(Vector (,clos-type ,ts ... -> ,rt) ,fvts ...)
                      arity))
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
         ;;bits [57,63] store the arity of the function
         (define arity-tag (arithmetic-shift arity 57))
         ;; Combine the tags into a single quad word
         (define tag (bitwise-ior arity-tag ptr-tag length-tag
                                  is-not-forward-tag))
         (define tmp-reg 'r11)         
         (list (Instr 'movq (list (Global 'free_ptr) (Reg tmp-reg)))
               (Instr 'addq (list (Imm size) (Global 'free_ptr)))
               (Instr 'movq (list (Imm tag) (Deref tmp-reg 0)))
               (Instr 'movq (list (Reg tmp-reg) lhs^))
               )]
        [(Assign lhs (Prim 'procedure-arity (list e)))
         (define new-lhs (select-instr-arg lhs))
         (define new-e (select-instr-arg e))
         (define tmp-reg 'r11)
         (list (Instr 'movq (list new-e (Reg tmp-reg)))
               (Instr 'movq (list (Deref tmp-reg 0) (Reg tmp-reg)))
               (Instr 'sarq (list (Imm 57) (Reg tmp-reg)))
               (Instr 'movq (list (Reg tmp-reg) new-lhs)))]
        [else
         (super select-instr-stmt e)]
        ))


    )) ;; new-compile-R5


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Passes

(define lambda-passes
  (let ([compiler (new compile-R5)])
    `(("shrink"
       ,(lambda (p) (send compiler shrink p))
       ,interp-R5
       ,type-check-R5)
      ("uniquify" 
       ,(lambda (p) (send compiler uniquify p))
       ,interp-R5
       ,type-check-R5)
      ("partial-eval"
       ,(lambda (p) (send compiler partial-eval p))
       ,interp-R5
       ,type-check-R5)
      ("optimize-direct-calls" 
       ,(lambda (p) (send compiler optimize-direct-calls p))
       ,interp-R5
       ,type-check-R5)
      ("reveal-functions"
       ,(lambda (p) (send compiler reveal-functions p))
       ,interp-F2
       ,(lambda (p)
          (begin
            (typed-vars #t)
            (define t (type-check-R5 p))
            (typed-vars #f)
            t)))
      #;("convert-to-closures"
       ,(lambda (p) (send compiler convert-to-closures p))
       ,interp-F2
       ,type-check-R5)
      ("optimize-closures"
       ,(lambda (p) (send compiler optimize-closures p))
       ,interp-F2
       ,type-check-R5)
      ("optimize-known-calls" 
       ,(lambda (p) (send compiler optimize-known-calls p))
       ,interp-F2
       ,type-check-R5)
      ("limit-functions"
       ,(lambda (p) (send compiler limit-functions p))
       ,interp-F2
       ,type-check-R5)
      ("expose allocation"
       ,(lambda (p) (send compiler expose-allocation p))
       ,interp-F2
       ,type-check-R5)
      ("remove-complex-opera*"
       ,(lambda (p) (send compiler remove-complex-opera* p))
       ,interp-F2
       ,type-check-R5)
      ("explicate-control"
       ,(lambda (p) (send compiler explicate-control p))
       ,interp-C4
       ,type-check-C4)
      ("select-instructions"
       ,(lambda (p) (send compiler select-instructions p))
       ,interp-pseudo-x86-3)
      ("uncover-live"
       ,(lambda (p) (send compiler uncover-live p))
       ,interp-pseudo-x86-3)
      ("build-interference"
       ,(lambda (p) (send compiler build-interference p))
       ,interp-pseudo-x86-3)
      ("build-move-graph"
       ,(lambda (p) (send compiler build-move-graph p))
       ,interp-pseudo-x86-3)
      ("allocate-registers"
       ,(lambda (p) (send compiler allocate-registers p))
       ,interp-x86-3)
      ("remove-jumps"
       ,(lambda (p) (send compiler remove-jumps p))
       ,interp-x86-3)
      ("patch-instructions"
       ,(lambda (p) (send compiler patch-instructions p))
       ,interp-x86-3)
      ("print x86"
       ,(lambda (p) (send compiler print-x86 p))
       #f)
      )))

    
    
    
