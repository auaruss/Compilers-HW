#lang racket
(require "utilities.rkt")
(require (only-in "type-check-R3.rkt" type-check-R3-class))
(provide type-check-R4 type-check-R4-class type-check-C3)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Functions                                                                 ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; type-check-R4

(define type-check-R4-class
  (class type-check-R3-class
    (super-new)
    (inherit check-type-equal?)

    (define/public (type-check-apply env e es)
      (define-values (e^ ty) ((type-check-exp env) e))
      (define-values (e* ty*) (for/lists (e* ty*) ([e (in-list es)])
                                ((type-check-exp env) e)))
      (match ty
        [`(,ty^* ... -> ,rt)
         (for ([arg-ty ty*] [param-ty ty^*])
           (check-type-equal? arg-ty param-ty (Apply e es)))
         (values e^ e* rt)]
        [else (error 'type-check-apply "expected a function, not" ty)]))

    (define/override (type-check-exp env)
      (lambda (e)
        (match e
          [(FunRef f)
           (values (FunRef f)  (dict-ref env f))]
          [(Apply e es)
           (define-values (e^ es^ rt) (type-check-apply env e es))
           (values (Apply e^ es^) rt)]
          [(Call e es)
           (define-values (e^ es^ rt) (type-check-apply env e es))
           (values (Call e^ es^) rt)]
          [else ((super type-check-exp env) e)]
          )))

    (define/public (type-check-def env)
      (lambda (e)
        (match e
          [(Def f (and p:t* (list `[,xs : ,ps] ...)) rt info body)
           (define new-env (append (map cons xs ps) env))
           (define-values (body^ ty^) ((type-check-exp new-env) body))
           (check-type-equal? ty^ rt body)
           (Def f p:t* rt info body^)]
          [else (error 'type-check-def "ill-formed function definition ~a" e)]
          )))	 

    (define/public (fun-def-type d)
      (match d [(Def f (list `[,xs : ,ps] ...) rt info body)  `(,@ps -> ,rt)]
        [else (error 'fun-def-type "ill-formed function definition in ~a" d)]))

    (define/override (type-check-program e)
      (match e
        [(ProgramDefsExp info ds body)
         (define new-env (for/list ([d ds])
                           (cons (Def-name d) (fun-def-type d))))
         (define ds^ (for/list ([d ds]) ((type-check-def new-env) d)))
         (define-values (body^ ty) ((type-check-exp new-env) body))
         (check-type-equal? ty 'Integer body)
         (ProgramDefsExp info ds^ body^)]
        [(ProgramDefs info ds)
         (define new-env (for/list ([d ds]) 
                           (cons (Def-name d) (fun-def-type d))))
         (define ds^ (for/list ([d ds]) ((type-check-def new-env) d)))
         ;; TODO: check that main has Integer return type.
         (ProgramDefs info ds^)]
        [(Program info body)
         (define-values (body^ ty) ((type-check-exp '()) body))
         (check-type-equal? ty 'Integer body)
         (ProgramDefsExp info '() body^)]
        [else (error 'type-check "unrecognized ~a" e)]))
    ))

(define (type-check-R4 p)
  (send (new type-check-R4-class) type-check-program p))

(define (type-check-exp env)
  (send (new type-check-R4-class) type-check-exp env))

(define (ty-equal? t1 t2)
  (send (new type-check-R4-class) type-equal? t1 t2))

(define (type-check-apply env e es)
  (send (new type-check-R4-class) type-check-apply env e es))

(define (fun-def-type d)
  (send (new type-check-R4-class) fun-def-type d))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; type-check-C3

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

(define (type-check-C3 p)
  (match p
    [(ProgramDefs info ds)
     (define new-env (for/list ([d ds]) 
                       (cons (Def-name d) (fun-def-type d))))
     (define ds^ (for/list ([d ds])
                   ((type-check-C-def new-env) d)))
     (ProgramDefs info ds^)]))
