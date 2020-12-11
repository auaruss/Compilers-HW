#lang racket
(require "utilities.rkt")
(require (only-in "type-check-R5.rkt" type-check-R5-class))
(provide type-check-R6 type-check-R6-class type-check-C5 type-check-R6-vectorof shrink-vectorof)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Any, inject, project                                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; type-check-R6

(define shrink-vectorof (make-parameter #f))

(define type-check-R6-class
  (class type-check-R5-class
    (super-new)
    (inherit type-equal?)

    (define/override (operator-types)
      (append
       '((integer? . ((Any) . Boolean))
         (vector? . ((Any) . Boolean))
         (procedure? . ((Any) . Boolean))
         (void? . ((Any) . Boolean))
         (tag-of-any . ((Any) . Integer))
         (make-any . ((_ Integer) . Any))
         )
       (super operator-types)))

    (define/public (type-predicates)
      (set 'boolean? 'integer? 'vector? 'procedure? 'void?))

    (define/public (combine-types t1 t2)
      (match (list t1 t2)
        [(list '_ t2) t2]
        [(list t1 '_) t1]
        [(list `(Vector ,ts1 ...)
               `(Vector ,ts2 ...))
         `(Vector ,@(for/list ([t1 ts1] [t2 ts2])
                      (combine-types t1 t2)))]
        [(list `(,ts1 ... -> ,rt1)
               `(,ts2 ... -> ,rt2))
         `(,@(for/list ([t1 ts1] [t2 ts2])
               (combine-types t1 t2))
           -> ,(combine-types rt1 rt2))]
        [else
         t1]))

    (define/public (flat-ty? ty)
      (match ty
        [(or `Integer `Boolean '_ `Void)
         #t]
        ;; The following is a special case to handle programs
        ;; after closure conversion. -Jeremy
        [`(Vector ((Vector _) ,ts ... -> Any))
         (for/and ([t ts]) (eq? t 'Any))]
        [`(Vector ,ts ...)
         (for/and ([t ts]) (eq? t 'Any))]
        [`(Vectorof Any)
         #t]
        [`(,ts ... -> ,rt)
         (and (eq? rt 'Any) (for/and ([t ts]) (eq? t 'Any)))]
        [else
         #f]
        ))

    (define/override (type-check-exp env)
      (lambda (e)
        (define recur (type-check-exp env))
        (match e
          ;; Change If to use combine-types
          [(If cnd thn els)
           (define-values (c Tc) (recur cnd))
           (define-values (t Tt) (recur thn))
           (define-values (e Te) (recur els))
           (unless (type-equal? Tc 'Boolean)
             (error 'type-check-exp
                    "expected condition of if to have type Boolean, not ~a" Tc))
           (unless (type-equal? Tt Te)
             (error 'type-check-exp
                    "branches of if must have the same type, but ~a != ~a"
                    Tt Te))
           (values (If c t e) (combine-types Tt Te))]
          [(Prim 'vector-length (list e))
           (define-values (e^ t) (recur e))
           (match t
             [(or `(Vector ,_ ...) `(Vectorof ,_))
              (values (Prim 'vector-length (list e^))  'Integer)]
             [else (error 'type-check-exp
                          "expected a vector in vector-length, not ~a" t)])]
          [(Prim 'vector-ref (list e ei))
           (define-values (e^ t) (recur e))
           (define-values (i it) (recur ei))
           (unless (type-equal? it 'Integer)
             (error 'type-check-exp "vector-ref: index not Integer: ~a" it))
           (match (list t i)
             [(list `(Vector ,ts ...) (Int i^))
              (unless (and (exact-nonnegative-integer? i^)
                           (i^ . < . (length ts)))
                (error 'type-check-exp "invalid index ~a in ~a" i^ e))
              (let ([t (list-ref ts i^)])
                (values (Prim 'vector-ref (list e^ (Int i^))) t))]
             [(list `(Vectorof ,t) i)
              (cond [(shrink-vectorof)
                     (define v (gensym 'tmp))
                     (define tmp-i (gensym 'tmp))
                     (values
                      (Let v e^
                           (Let tmp-i i
                                (If (Prim 'and (list
                                                (Prim '<= (list (Int 0) (Var tmp-i)))
                                                (Prim '< (list (Var tmp-i)
                                                               (Prim 'vector-length (list (Var v)))))))
                                    (Prim 'vector-ref (list (Var v) (Var tmp-i)))
                                    (Exit))))
                      t)]
                    [else
                     (values (Prim 'vector-ref (list e^ i))  t)])]
             [else (error "expected a vector in vector-ref, not" t)])]
          [(Prim 'vector-set! (list e-vec e-i e-arg))
           (define-values (e-vec^ t-vec) (recur e-vec))
           (define-values (i it) (recur e-i))
           (define-values (e-arg^ t-arg) (recur e-arg))
           (unless (type-equal? it 'Integer)
             (error 'type-check-exp "vector-set!: index not Integer: ~a" it))
           (match (list t-vec i)
             [(list `(Vector ,ts ...) (Int i^))
              (unless (and (exact-nonnegative-integer? i^)
                           (i^ . < . (length ts)))
                (error 'type-check-exp "invalid index ~a in ~a" i^ e))
              (unless (type-equal? (list-ref ts i^) t-arg)
                (error 'type-check-exp "type mismatch in vector-set! ~a ~a" 
                       (list-ref ts i^) t-arg))
              (values (Prim 'vector-set! (list e-vec^ (Int i^) e-arg^))  'Void)]
             [(list `(Vectorof ,t) i)
              (unless (type-equal? t t-arg)
                (error 'type-check-exp "type mismatch in vector-set! ~a ~a" 
                       t t-arg))
              (cond [(shrink-vectorof)
                     (define v (gensym 'tmp))
                     (define tmp-i (gensym 'tmp))
                     (values
                      (Let v e-vec^
                           (Let tmp-i i
                                (If (Prim 'and (list
                                                (Prim '<= (list (Int 0) (Var tmp-i)))
                                                (Prim '< (list (Var tmp-i)
                                                               (Prim 'vector-length (list (Var v)))))))
                                    (Prim 'vector-set! (list (Var v) (Var tmp-i) e-arg^))
                                    (Exit))))
                      'Void)]
                    [else
                     (values (Prim 'vector-set! (list e-vec^ i e-arg^))  'Void)])]
             [else
              (error 'type-check-exp "expected a vector in vector-set!, not ~a"
                     t-vec)])]
          [(Inject e ty)
           (unless (flat-ty? ty)
             (error 'type-check-exp
                    "may only inject a value of flat type, not ~a" ty))
           (define-values (new-e e-ty) (recur e))
           (cond
             [(type-equal? e-ty ty)
              (values (Inject new-e ty) 'Any)]
             [else
              (error 'type-check-exp
                     "injected expression does not have expected type" 
                     e e-ty ty)])]
          [(ValueOf e ty)
           (define-values (new-e e-ty) (recur e))
           (values (ValueOf new-e ty) ty)]
          [(Project e ty)
           (unless (flat-ty? ty)
             (error 'type-check-exp
                    "may only project to a flat type, not ~a" ty))
           (define-values (new-e e-ty) (recur e))
           (cond
             [(type-equal? e-ty 'Any)
              (values (Project new-e ty) ty)]
             [else
              (error 'type-check-exp
                     "project expression does not have type Any" e)])]
          [(Prim pred (list e))
           #:when (set-member? (type-predicates) pred)
           (define-values (new-e e-ty) (recur e))
           (cond
             [(type-equal? e-ty 'Any)
              (values (Prim pred (list new-e)) 'Boolean)]
             [else
              (error 'type-check-exp
                     "type predicate expected argument of type Any, not ~a" e-ty)])]
          [(Exit)
           (values (Exit) '_)]
          [(Prim 'eq? (list arg1 arg2))
           (define-values (e1 t1) (recur arg1))
           (define-values (e2 t2) (recur arg2))
           (match* (t1 t2)
             ;; allow comparison of vectors of different element types
             [(`(Vector ,ts1 ...) `(Vector ,ts2 ...))   (void)]
             [(`(Vectorof ,t1) `(Vectorof ,t2))         (void)]
             [(other wise)
              (unless (type-equal? t1 t2)
                (error 'type-check-exp
                       "type error: different argument types of eq?: ~a != ~a"
                       t1 t2))])
           (values (Prim 'eq? (list e1 e2)) 'Boolean)]
          [else ((super type-check-exp env) e)]
          )))

    ))

(define (type-check-R6 p)
  (send (new type-check-R6-class) type-check-program p))

(define (type-check-R6-vectorof p)
  (shrink-vectorof #t)
  (define res (send (new type-check-R6-class) type-check-program p))
  (shrink-vectorof #f)
  res)

(define (type-check-exp env)
  (send (new type-check-R6-class) type-check-exp env))

(define (ty-equal? t1 t2)
  (send (new type-check-R6-class) type-equal? t1 t2))

(define (combine-ty t1 t2)
  (send (new type-check-R6-class) combine-types t1 t2))

(define (type-check-apply env e es)
  (send (new type-check-R6-class) type-check-apply env e es))

(define (fun-def-type d)
  (send (new type-check-R6-class) fun-def-type d))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; type-check-C5

;; everything copied and pasted from type-check-C4 to pick up new type-check-exp

(define (type-check-stmt env)
  (lambda (s)
    (match s
      [(Assign (Var x) e)
       (define-values (e^ t) ((type-check-exp env) e))
       (cond [(dict-has-key? env x)
              (unless (ty-equal? t (dict-ref env x))
                (error 'type-check-stmt
                       "type error: variable's type ~a and RHS type ~a are different"
                       (dict-ref env x) t))]
             [else
              (dict-set! env x t)])]
      [(Collect size)
       (void)]
      [(Exit)
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
              (debug 'type-check-tail "type checking block ~a" label)
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
       (combine-ty T1 T2)]
      [(TailCall f arg*)
       (define-values (f^ arg*^ rt) (type-check-apply env f arg*))
       rt]
      [(Exit) '_]
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

(define (type-check-C5 p)
  (match p
    [(ProgramDefs info ds)
     (define new-env (for/list ([d ds]) 
                       (cons (Def-name d) (fun-def-type d))))
     (define ds^ (for/list ([d ds])
                   ((type-check-C-def new-env) d)))
     (ProgramDefs info ds^)]))

