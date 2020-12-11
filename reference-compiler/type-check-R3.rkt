#lang racket
(require "utilities.rkt")
(require (only-in "type-check-R2.rkt" type-check-R2-class))
(provide type-check-R3 type-check-R3-class type-check-C2)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Tuples (aka Vectors)                                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; type-check-R3

(define type-check-R3-class
  (class type-check-R2-class
    (super-new)
    (inherit check-type-equal?)

    (define/override (type-check-exp env)
      (lambda (e)
        (define recur (type-check-exp env))
        (match e
          [(Void) (values (Void) 'Void)]
          [(Prim 'vector es)
           (define-values (e* t*) (for/lists (e* t*) ([e es]) (recur e)))
           (define t `(Vector ,@t*))
           (values (HasType (Prim 'vector e*) t)  t)]
          [(Prim 'vector-ref (list e1 (Int i)))
           (define-values (e1^ t) (recur e1))
           (match t
             [`(Vector ,ts ...)
              (unless (and (0 . <= . i) (i . < . (length ts)))
                (error 'type-check "index ~a out of bounds\nin ~v" i e))
              (values (Prim 'vector-ref (list e1^ (Int i)))  (list-ref ts i))]
             [else (error 'type-check "expect Vector, not ~a\nin ~v" t e)])]
          [(Prim 'vector-set! (list e1 (Int i) arg) )
           (define-values (e-vec t-vec) (recur e1))
           (define-values (e-arg^ t-arg) (recur arg))
           (match t-vec
             [`(Vector ,ts ...)
              (unless (and (0 . <= . i) (i . < . (length ts)))
                (error 'type-check "index ~a out of bounds\nin ~v" i e))
              (check-type-equal? (list-ref ts i) t-arg e)
              (values (Prim 'vector-set! (list e-vec (Int i) e-arg^))  'Void)]
             [else (error 'type-check "expect Vector, not ~a\nin ~v" t-vec e)])]
          [(Prim 'vector-length (list e))
           (define-values (e^ t) (recur e))
           (match t
             [`(Vector ,ts ...)
              (values (Prim 'vector-length (list e^))  'Integer)]
             [else (error 'type-check "expect Vector, not ~a\nin ~v" t e)])]
          [(Prim 'eq? (list arg1 arg2))
           (define-values (e1 t1) (recur arg1))
           (define-values (e2 t2) (recur arg2))
           (match* (t1 t2)
             [(`(Vector ,ts1 ...)  `(Vector ,ts2 ...))  (void)]
             [(other wise)  (check-type-equal? t1 t2 e)])
           (values (Prim 'eq? (list e1 e2)) 'Boolean)]
          [(HasType (Prim 'vector es) t)
           ((type-check-exp env) (Prim 'vector es))]
          [(HasType e1 t)
           (define-values (e1^ t^) (recur e1))
           (check-type-equal? t t^ e)
           (values (HasType e1^ t) t)]
          [(GlobalValue name)
           (values (GlobalValue name) 'Integer)]
          [(Allocate size t)
           (values (Allocate size t) t)]
          [(Collect size)
           (values (Collect size) 'Void)]
          [else ((super type-check-exp env) e)]
          )))
    ))

(define (type-check-R3 p)
  (send (new type-check-R3-class) type-check-program p))

(define (type-check-exp env)
  (send (new type-check-R3-class) type-check-exp env))

(define (type-equal? t1 t2)
  (send (new type-check-R3-class) type-equal? t1 t2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; type-check-C2

(define (type-check-stmt env)
  (lambda (s)
    (match s
      [(Assign (Var x) e)
       (define-values (e^ t) ((type-check-exp env) e))
       (cond [(dict-has-key? env x)
              (unless (type-equal? t (dict-ref env x))
                (error 'type-check-stmt
                       "type error: variable and RHS have different types, ~a != ~a"
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
       (unless (type-equal? Tc 'Boolean)
         (error 'type-check-tail
                "type error: condition must be Boolean, not ~a" Tc))
       (define T1 ((type-check-tail env block-env G) tail1))
       (define T2 ((type-check-tail env block-env G) tail2))
       (unless (type-equal? T1 T2)
         (error 'type-check-tail
                "type error: branches of if should have same type, but ~a != ~a"
                T1 T2))
       T1]
      )))

(define (type-check-C2 p)
  (match p
    [(Program info (CFG G))
     ;; Top-down traversal so we see variable definitions before uses.
     ;; -Jeremy
     (define env (make-hash))
     (define block-env (make-hash))
     (define t ((type-check-tail env block-env G)
                (dict-ref G 'start)))
     (unless (type-equal? t 'Integer)
       (error 'type-check-C2
              "return type of program must be Integer, not ~a" t))
     (define locals-types (for/list ([(x t) (in-dict env)])
                            (cons x t)))
     (define new-info (dict-set info 'locals-types locals-types))
     (Program new-info (CFG G))]))
