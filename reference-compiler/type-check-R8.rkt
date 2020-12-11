#lang racket
(require graph)
(require "multigraph.rkt")
(require "utilities.rkt")
(require (only-in "any.rkt" compile-R6))
(require (only-in "type-check-R5.rkt" typed-vars))
(require (only-in "type-check-R6.rkt" type-check-R6-class shrink-vectorof))
(provide type-check-R8 type-check-R8-vectorof type-check-R8-class type-check-C7)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; type-check-R8

(define type-check-R8-class
  (class type-check-R6-class
    (super-new)
    (inherit type-equal?)

    (define/override (type-check-exp env)
      (lambda (e)
        (define recur (type-check-exp env))
        (match e
          [(SetBang x rhs)
           (define-values (rhs^ rhsT) (recur rhs))
           (define varT (dict-ref env x))
           (unless (type-equal? rhsT varT)
             (error 'type-check-exp
                    "variable and RHS of set! have different type, ~a != ~a"
                    varT rhsT))
           (values (SetBang x rhs^) 'Void)]
          [(WhileLoop cnd body)
           (define-values (cnd^ Tc) (recur cnd))
           (unless (type-equal? Tc 'Boolean)
             (error 'type-check-exp
                    "expected condition of if to have type Boolean, not ~a" Tc))
           (define-values (body^ Tbody) ((type-check-exp env) body))
           (values (WhileLoop cnd^ body^) 'Void)]
          [(ForLoop x e body)
           (define-values (e^ Te) (recur e))
           (match Te
             [`(Vectorof ,t)
              (define new-env (cons `(,x . ,t) env))
              (define-values (body^ Tbody) ((type-check-exp new-env) body))
              (values (ForLoop x e^ body^) 'Void)]
             [else (error 'type-check-exp
                          "expected a Vectorof in for loop, not ~a" Te)])]
          [(Begin es body)
           (define-values (es^ ts)
             (for/lists (l1 l2) ([e es]) (recur e)))
           (define-values (body^ Tbody) (recur body))
           (debug "type check begin" body^ es^)
           (values (Begin es^ body^) Tbody)]
          [else ((super type-check-exp env) e)]
          )))

    ))

(define (type-check-R8 p)
  (send (new type-check-R8-class) type-check-program p))

(define (type-check-R8-vectorof p)
  (shrink-vectorof #t)
  (define res (send (new type-check-R8-class) type-check-program p))
  (shrink-vectorof #f)
  res)

(define (type-check-exp env)
  (send (new type-check-R8-class) type-check-exp env))

(define (ty-equal? t1 t2)
  (send (new type-check-R8-class) type-equal? t1 t2))

(define (type-check-apply env e es)
  (send (new type-check-R8-class) type-check-apply env e es))

(define (fun-def-type d)
  (send (new type-check-R8-class) fun-def-type d))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; type-check-C7

;; Dataflow analysis

(define FV-R8
  (class compile-R6
    (super-new)
    
    (define/override (free-variables e)
      (define (recur e) (send this free-variables e))
      (match e
        [(Var x)
         (hash x (HasType (Var x) '_))]
        [(ForLoop x e body)
	 (hash-union (recur e) (hash-remove (recur body) x))]
        ;; C-level expressions
        [(Void)
         (hash)]
        [(Allocate size ty)
         (hash)]
        [(AllocateClosure len ty arity)
         (hash)]
        [(GlobalValue name)
         (hash)]
        [(Call f arg*)
         (hash-union (recur f) (apply hash-union (map recur arg*)))]
	[else (super free-variables e)]
	))
    ))
(define FV-R8-inst (new FV-R8))

(define (free-vars-exp e)
  (define fvs-hash (send FV-R8-inst free-variables e))
  (list->set (hash-keys fvs-hash)))

(define type-changed #t)

(define (exp-ready? exp env)
  (for/and ([x (free-vars-exp exp)])
    (dict-has-key? env x)))

(define (meet-type t1 t2)
  (match (list t1 t2)
    [(list '_ t2) t2]
    [(list t1 '_) t1]
    [(list `(Vector ,ts1 ...)
           `(Vector ,ts2 ...))
     `(Vector ,@(for/list ([t1 ts1] [t2 ts2])
                  (meet-type t1 t2)))]
    [(list `(,ts1 ... -> ,rt1)
           `(,ts2 ... -> ,rt2))
     `(,@(for/list ([t1 ts1] [t2 ts2])
           (meet-type t1 t2))
       -> ,(meet-type rt1 rt2))]
    [else
     (cond [(equal? t1 t2)
            t1]
           [else
            (error "expected equal types" t1 t2)])]))

(define (update-type x t env)
  (cond [(dict-has-key? env x)
         (define old-t (dict-ref env x))
         (unless (ty-equal? t old-t)
           (error 'update-type "old type ~a and new type ~ are inconsistent"
                  old-t t))
         (define new-t (meet-type old-t t))
         (cond [(not (equal? new-t old-t))
                (dict-set! env x new-t)
                (set! type-changed #t)])]
        [(eq? t '_)
         (void)]
        [else
         (set! type-changed #t)
         (dict-set! env x t)]))

(define (type-check-stmt env)
  (lambda (s)
    (verbose 'type-check-stmt s)
    (match s
      [(Assign (Var x) e)
       #:when (exp-ready? e env)
       (define-values (e^ t) ((type-check-exp env) e))
       (update-type x t env)]
      [(Assign (Var x) e)
       (void)]
      [(Collect size)
       (void)]
      [(Exit)
       (void)]
      [(Prim 'vector-set! (list vec index rhs))
       #:when (and (exp-ready? vec env) (exp-ready? index env)
                   (exp-ready? rhs env))
       ((type-check-exp env) s)]
      [(Prim 'read '())
       (void)]
      [(Call e es)
       (define-values (e^ es^ rt) (type-check-apply env e es))
       (void)]
      )))

(define (type-check-tail env block-env G)
  (lambda (t)
    (verbose 'type-check-tail t)
    (match t
      [(Return e)
       #:when (exp-ready? e env)
       (define-values (e^ t) ((type-check-exp env) e))
       t]
      [(Return e) '_]      
      [(Seq s t)
       ((type-check-stmt env) s)
       ((type-check-tail env block-env G) t)]
      [(Goto label)
       (cond [(dict-has-key? block-env label)
              (dict-ref block-env label)]
             [else '_])]
      [(IfStmt cnd tail1 tail2)
       (cond [(exp-ready? cnd env)
              (define-values (c Tc) ((type-check-exp env) cnd))
              (unless (ty-equal? Tc 'Boolean)
                (error "type error: condition of if should be Boolean, not" Tc))
              ])
       (define T1 ((type-check-tail env block-env G) tail1))
       (define T2 ((type-check-tail env block-env G) tail2))
       (unless (ty-equal? T1 T2)
         (error "type error: branches of if should have same type, not"
                T1 T2))
       (meet-type T1 T2)]
      [(TailCall f arg*)
       #:when (and (exp-ready? f env)
                   (for/and ([arg arg*]) (exp-ready? arg env)))
       (define-values (f^ arg*^ rt) (type-check-apply env f arg*))
       rt]
      [(TailCall f arg*) '_]
      [(Exit) '_]
      )))

(define (adjacent-tail t)
  (match t
    [(Goto label)
     (set label)]
    [(IfStmt cnd t1 t2)
     (set-union (adjacent-tail t1) (adjacent-tail t2))]
    [(Seq s t)
     (adjacent-tail t)]
    [else
     (set)]))

(define (C-CFG->graph cfg)
  (define G (make-multigraph '()))
  (for ([label (in-dict-keys cfg)])
    (add-vertex! G label))
  (for ([(src b) (in-dict cfg)])
    (for ([tgt (adjacent-tail b)])
      (add-directed-edge! G src tgt)))
  G)

(define (type-check-C-def global-env)
  (lambda (d)
    (match d
      [(Def f (and p:t* (list `[,xs : ,ps] ...)) rt info CFG)
       (verbose "type-check-C-def" f)
       (define env (make-hash (append (map cons xs ps) global-env)))
       (define block-env (make-hash))
       (set! type-changed #t)
       (define (iterate)
         (cond [type-changed
                (set! type-changed #f)
                (for ([(label tail) (in-dict CFG)])
                  (define t ((type-check-tail env block-env CFG) tail))
                  (update-type label t block-env)
                  )
                (verbose "type-check-C-def" env block-env)
                (iterate)]
               [else (void)]))
       (iterate)
       (define start (symbol-append f 'start))
       (unless (dict-has-key? block-env start)
         (error 'type-check-C-def "failed to infer type for ~a" start))
       (define t (dict-ref block-env start))
       (unless (ty-equal? t rt)
         (error "mismatching return type" t rt))
       (define locals-types
         (for/list ([(x t) (in-dict env)]
                    #:when (not (dict-has-key? global-env x)))
           (cons x t)))
       (define new-info (dict-set info 'locals-types locals-types))
       (Def f p:t* rt new-info CFG)]
      )))

(define (type-check-C7 p)
  (match p
    [(ProgramDefs info ds)
     (define new-env (for/list ([d ds]) 
                       (cons (Def-name d) (fun-def-type d))))
     (define ds^ (for/list ([d ds])
                   ((type-check-C-def new-env) d)))
     (ProgramDefs info ds^)]))

