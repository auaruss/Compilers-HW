#lang racket
(require "utilities.rkt")
(require (only-in "type-check-R4.rkt" type-check-R4-class))
(provide type-check-R5 type-check-R5-class type-check-C4 typed-vars)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Lambda                                                                    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; type-check-R5

(define typed-vars (make-parameter #f))

(define type-check-R5-class
  (class type-check-R4-class
    (super-new)

    ;; lenient type checking for '_
    (define/override (type-equal? t1 t2)
      (debug 'type-equal? "lenient" t1 t2)
      (match (list t1 t2)
        [(list '_ t2) #t]
        [(list t1 '_) #t]
        [(list `(Vector ,ts1 ...)
               `(Vector ,ts2 ...))
         (for/and ([t1 ts1] [t2 ts2])
           (type-equal? t1 t2))]
        [(list `(,ts1 ... -> ,rt1)
               `(,ts2 ... -> ,rt2))
         (and (for/and ([t1 ts1] [t2 ts2])
                (type-equal? t1 t2))
              (type-equal? rt1 rt2))]
        [else
         (equal? t1 t2)]))

    (define/override (type-check-exp env)
      (lambda (e)
        (debug 'type-check-exp "R5" e)
        (define recur (type-check-exp env))
        (match e
          [(HasType (Var x) t)
           ((type-check-exp env) (Var x))]
          [(Var x)
           (define t (dict-ref env x))
           (define var (cond [(typed-vars) (HasType (Var x) t)]
                             [else (Var x)]))
           (values var t)]
          [(Closure arity es)
           (define-values (e* t*) (for/lists (e* t*) ([e es])
                                    (recur e)))
           (let ([t `(Vector ,@t*)])
             (values (HasType (Closure arity e*) t) t))]
          [(Prim 'procedure-arity (list e))
           (define-values (e^ t) (recur e))
           (match t
             ;; before closure conversion
             [`(,ts ... -> ,rt)
              (values (Prim 'procedure-arity (list e^)) 'Integer)]
             ;; after closure conversion
             [`(Vector (,clos ,ts ... -> ,rt))
              (values (Prim 'procedure-arity (list e^)) 'Integer)]
             [else (error 'type-check-exp
                          "expected a function in procedure-arity, not ~a" t)])]
          [(HasType (Closure arity es) t)
           ((type-check-exp env) (Closure arity es))]
          [(AllocateClosure size t arity)
           (values (AllocateClosure size t arity) t)]
          [(FunRefArity f n)
           (let ([t (dict-ref env f)])
             (values (FunRefArity f n) t))]
          [(Lambda (and params `([,xs : ,Ts] ...)) rT body)
           (define-values (new-body bodyT) 
             ((type-check-exp (append (map cons xs Ts) env)) body))
           (define ty `(,@Ts -> ,rT))
           (cond
             [(type-equal? rT bodyT)
              (values (Lambda params rT new-body) ty)]
             [else
              (error "function body's type does not match return type" bodyT rT)
              ])]
          [else ((super type-check-exp env) e)]
          )))

    ))

(define (type-check-R5 p)
  (send (new type-check-R5-class) type-check-program p))

(define (type-check-exp env)
  (send (new type-check-R5-class) type-check-exp env))

(define (ty-equal? t1 t2)
  (send (new type-check-R5-class) type-equal? t1 t2))

(define (type-check-apply env e es)
  (send (new type-check-R5-class) type-check-apply env e es))

(define (fun-def-type d)
  (send (new type-check-R5-class) fun-def-type d))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; type-check-C4

(define (type-check-stmt env)
  (lambda (s)
    (match s
      [(Assign (Var x) e)
       (define-values (e^ t) ((type-check-exp env) e))
       (cond [(dict-has-key? env x)
              (unless (ty-equal? t (dict-ref env x))
                (error 'type-check-stmt
                       "type error: variable and RHS have different types"
                       t (dict-ref env x)))]
             [else
              (dict-set! env x t)])]
      [(Collect size)
       (void)]
      )))

(define (type-check-tail env block-env G)
  (lambda (t)
    (match t
      [(Return e)
       (define-values (e^ t) ((type-check-exp env) e))
       t]
      [(Seq s t)
       ((type-check-stmt env) s)
       ((type-check-tail env block-env G) t)]
      [(Goto label)
       ;; Memoization because G is a DAG -Jeremy
       (cond [(dict-has-key? block-env label)
              (dict-ref block-env label)]
             [else
              (define t ((type-check-tail env block-env G)
                         (dict-ref G label)))
              (dict-set! block-env label t)
              t])]
      [(IfStmt cnd tail1 tail2)
       (define-values (c Tc) ((type-check-exp env) cnd))
       (unless (ty-equal? Tc 'Boolean)
         (error "type error: condition of if should be Boolean, not" Tc))
       (define T1 ((type-check-tail env block-env G) tail1))
       (define T2 ((type-check-tail env block-env G) tail2))
       (unless (ty-equal? T1 T2)
         (error "type error: branches of if should have same type, not"
                T1 T2))
       T1]
      [(TailCall f arg*)
       (define-values (f^ arg*^ rt) (type-check-apply env f arg*))
       rt]
      )))

(define (type-check-C-def global-env)
  (lambda (d)
    (match d
      [(Def f (and p:t* (list `[,xs : ,ps] ...)) rt info CFG)
       (define new-env (append (map cons xs ps) global-env))
       (define env (make-hash new-env))
       (define block-env (make-hash))
       (define t ((type-check-tail env block-env CFG)
                  (dict-ref CFG (symbol-append f 'start))))
       (unless (ty-equal? t rt)
         (error "mismatching return type" t rt))
       (define locals-types
         (for/list ([(x t) (in-dict env)]
                    #:when (not (dict-has-key? global-env x)))
           (cons x t)))
       (define new-info (dict-set info 'locals-types locals-types))
       (Def f p:t* rt new-info CFG)]
      )))

(define (type-check-C4 p)
  (match p
    [(ProgramDefs info ds)
     (define new-env (for/list ([d ds]) 
                       (cons (Def-name d) (fun-def-type d))))
     (define ds^ (for/list ([d ds])
                   ((type-check-C-def new-env) d)))
     (ProgramDefs info ds^)]))

