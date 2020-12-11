#lang racket
(require "utilities.rkt")
(require "type-check-R1.rkt")
(provide type-check-R2 type-check-R2-class type-check-C1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Booleans and Control Flow                                                 ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; type-check-R2

(define type-check-R2-class
  (class type-check-R1-class
    (super-new)
    (inherit check-type-equal?)
    
    (define/override (operator-types)
      (append '((- . ((Integer Integer) . Integer))
                (and . ((Boolean Boolean) . Boolean))
                (or . ((Boolean Boolean) . Boolean))
                (< . ((Integer Integer) . Boolean))
                (<= . ((Integer Integer) . Boolean))
                (> . ((Integer Integer) . Boolean))
                (>= . ((Integer Integer) . Boolean))
                (not . ((Boolean) . Boolean))
                )
              (super operator-types)))

    (define/override (type-check-exp env)
      (lambda (e)
        (match e
          [(Bool b) (values (Bool b) 'Boolean)]
          [(If cnd thn els)
           (define-values (cnd^ Tc) ((type-check-exp env) cnd))
           (define-values (thn^ Tt) ((type-check-exp env) thn))
           (define-values (els^ Te) ((type-check-exp env) els))
           (check-type-equal? Tc 'Boolean e)
           (check-type-equal? Tt Te e)
           (values (If cnd^ thn^ els^) Te)]
          [(Prim 'eq? (list e1 e2))
           (define-values (e1^ T1) ((type-check-exp env) e1))
           (define-values (e2^ T2) ((type-check-exp env) e2))
           (check-type-equal? T1 T2 e)
           (values (Prim 'eq? (list e1^ e2^)) 'Boolean)]
          [else ((super type-check-exp env) e)])))
    ))

(define (type-check-R2 p)
  (send (new type-check-R2-class) type-check-program p))

(define (type-check-exp env)
  (send (new type-check-R2-class) type-check-exp env))

(define (type-equal? t1 t2)
  (send (new type-check-R2-class) type-equal? t1 t2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; type-check-C1

(define (type-check-stmt env)
  (lambda (s)
    (match s
      [(Assign (Var x) e)
       (define-values (e^ t) ((type-check-exp env) e))
       (cond [(dict-has-key? env x)
              (unless (type-equal? t (dict-ref env x))
                (error 'type-check-stmt
                       "variable and RHS have different types, ~a != ~a"
                       t (dict-ref env x)))]
             [else
              (dict-set! env x t)])]
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
         (error "type error: condition of if should be Boolean, not" Tc))
       (define T1 ((type-check-tail env block-env G) tail1))
       (define T2 ((type-check-tail env block-env G) tail2))
       (unless (type-equal? T1 T2)
         (error "type error: branches of if should have same type, not"
                T1 T2))
       T1]
      )))

(define (type-check-C1 p)
  (match p
    [(Program info (CFG G))
     ;; Top-down traversal so we see variable definitions before uses.
     ;; -Jeremy
     (define env (make-hash))
     (define block-env (make-hash))
     (define t ((type-check-tail env block-env G)
                (dict-ref G 'start)))
     (unless (type-equal? t 'Integer)
       (error "return type of program must be Integer, not" t))
     (define locals-types (for/list ([(x t) (in-dict env)])
                            (cons x t)))
     (define new-info (dict-set info 'locals-types locals-types))
     (Program new-info (CFG G))]))
