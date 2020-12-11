#lang racket
(require racket/fixnum)
(require "utilities.rkt")
(require "casts.rkt")
(require "interp-R6.rkt")
(provide interp-R8 interp-R8-class)

;; Note to maintainers of this code:
;;   A copy of this interpreter is in the book and should be
;;   kept in sync with this code.

(define interp-R8-class
  (class interp-R6-class
    (super-new)

    (define/override ((interp-exp env) e)
      (verbose "R8/interp-exp" e)
      (define recur (interp-exp env))
      (match e
        [(SetBang x rhs)
         (set-box! (lookup x env) (recur rhs))]
        [(WhileLoop cnd body)
         (define (loop)
           (cond [(recur cnd)  (recur body) (loop)]
                 [else         (void)]))
         (loop)]
        [(ForLoop x seq body)
         (define vec (recur seq))
         (for ([i vec])
           (define new-env (cons (cons x (box i)) env))
           ((interp-exp new-env) body))
         (void)]
        [(Begin es body)
         (for ([e es]) (recur e))
         (recur body)]
        [else ((super interp-exp env) e)]))
    ))

(define (interp-R8 p)
  (send (new interp-R8-class) interp-program p))

