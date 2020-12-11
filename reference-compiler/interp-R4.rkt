#lang racket
(require racket/fixnum)
(require "utilities.rkt")
(require "interp-R3.rkt")
(provide interp-R4 interp-R4-class)

;; Note to maintainers of this code:
;;   A copy of this interpreter is in the book and should be
;;   kept in sync with this code.

(define interp-R4-class
  (class interp-R3-class
    (super-new)

    (define/override ((interp-exp env) e)
      (define recur (interp-exp env))
      (verbose "R4/interp-exp" e)
      (match e
        [(Var x) (unbox (dict-ref env x))]
        [(Let x e body)
         (define new-env (dict-set env x (box (recur e))))
         ((interp-exp new-env) body)]
        [(Apply fun args)
         (define fun-val (recur fun))
         (define arg-vals (for/list ([e args]) (recur e)))
         (match fun-val
           [`(function (,xs ...) ,body ,fun-env)
            (define params-args (for/list ([x xs] [arg arg-vals])
                                  (cons x (box arg))))
            (define new-env (append params-args fun-env))
            ((interp-exp new-env) body)]
           [else (error 'interp-exp "expected function, not ~a" fun-val)])]
        [else ((super interp-exp env) e)]
        ))

    (define/public (interp-def d)
      (match d
        [(Def f (list `[,xs : ,ps] ...) rt _ body)
         (cons f (box `(function ,xs ,body ())))]
        ))

    (define/override (interp-program p)
      (verbose "interp-R4" p)
      (match p
        [(ProgramDefsExp info ds body)
         (let ([top-level (for/list ([d ds]) (interp-def d))])
           (for/list ([f (in-dict-values top-level)])
             (set-box! f (match (unbox f)
                           [`(function ,xs ,body ())
                            `(function ,xs ,body ,top-level)])))
           ((interp-exp top-level) body))]
        
        ;; For after the shrink pass.
        [(ProgramDefs info ds)
         (let ([top-level (for/list ([d ds]) (interp-def d))])
           (for ([f (in-dict-values top-level)])
             (set-box! f (match (unbox f)
                            [`(function ,xs ,body ())
                             `(function ,xs ,body ,top-level)])))
           ;; call the main function
           ((interp-exp top-level) (Apply (Var 'main) '())))]
        ))
    ))

(define (interp-R4 p)
  (send (new interp-R4-class) interp-program p))
