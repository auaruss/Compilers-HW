#lang racket
(require racket/fixnum)
(require "utilities.rkt")
(require "interp-R1.rkt")
(provide interp-R2 interp-exp interp-R2-class)

;; Note to maintainers of this code:
;;   A copy of this interpreter is in the book and should be
;;   kept in sync with this code.

(define interp-R2-class
  (class interp-R1-class
    (super-new)

    (define/public (interp-op op)
      (match op
        ['+ fx+]
        ['- fx-]
        ['read read-fixnum]
        ['not (lambda (v) (match v [#t #f] [#f #t]))]
        ['or (lambda (v1 v2)
               (cond [(and (boolean? v1) (boolean? v2))
                      (or v1 v2)]))]
        ['eq? (lambda (v1 v2)
                (cond [(or (and (fixnum? v1) (fixnum? v2))
                           (and (boolean? v1) (boolean? v2))
                           (and (vector? v1) (vector? v2)))
                       (eq? v1 v2)]))]
        ['< (lambda (v1 v2)
              (cond [(and (fixnum? v1) (fixnum? v2))
                     (< v1 v2)]))]
        ['<= (lambda (v1 v2)
               (cond [(and (fixnum? v1) (fixnum? v2))
                      (<= v1 v2)]))]
        ['> (lambda (v1 v2)
              (cond [(and (fixnum? v1) (fixnum? v2))
                     (> v1 v2)]))]
        ['>= (lambda (v1 v2)
               (cond [(and (fixnum? v1) (fixnum? v2))
                      (>= v1 v2)]))]
        [else (error 'interp-op "unknown operator")]
        ))

    (define/override ((interp-exp env) e)
      (define recur (interp-exp env))
      (match e
        [(Bool b) b]
        [(If cnd thn els)
         (define b (recur cnd))
         (match b
           [#t (recur thn)]
           [#f (recur els)])]
        [(Prim 'and (list e1 e2))
         (define v1 (recur e1))
         (match v1
           [#t (match (recur e2) [#t #t] [#f #f])]
           [#f #f])]
        [(Prim op args)
         (apply (interp-op op) (for/list ([e args]) (recur e)))]
        [else ((super interp-exp env) e)]
        ))
    ))

(define (interp-R2 p)
  (send (new interp-R2-class) interp-program p))

(define (interp-exp env)
  (send (new interp-R2-class) interp-exp env))
