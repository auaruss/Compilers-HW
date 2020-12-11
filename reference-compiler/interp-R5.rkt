#lang racket
(require racket/fixnum)
(require "utilities.rkt")
(require "interp-R4.rkt")
(provide interp-R5 interp-R5-class)

;; Note to maintainers of this code:
;;   A copy of this interpreter is in the book and should be
;;   kept in sync with this code.

(define interp-R5-class
  (class interp-R4-class
    (super-new)

    (define/override (interp-op op)
      (match op
        ['procedure-arity
         (lambda (v)
           (match v
             [`(function (,xs ...) ,body ,lam-env)  (length xs)]
             [else (error 'interp-op "expected a function, not ~a" v)]))]
        [else (super interp-op op)]))

    (define/override ((interp-exp env) e)
      (define recur (interp-exp env))
      (verbose "R5/interp-exp" e)
      (match e
        [(Lambda (list `[,xs : ,Ts] ...) rT body)
         `(function ,xs ,body ,env)]
        [else ((super interp-exp env) e)]))
    ))

(define (interp-R5 p)
  (send (new interp-R5-class) interp-program p))
 
