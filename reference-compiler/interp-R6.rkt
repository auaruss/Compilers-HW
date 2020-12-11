#lang racket
(require racket/fixnum)
(require "utilities.rkt")
(require "casts.rkt")
(require "interp-R5.rkt")
(provide interp-R6 interp-R6-class)

;; Note to maintainers of this code:
;;   A copy of this interpreter is in the book and should be
;;   kept in sync with this code.

(define interp-R6-class
  (class interp-R5-class
    (super-new)

    (define (vector-ish? v)
      (match v
        [`(vector-proxy ,vec ,rs ,ws)
         (vector-ish? vec)]
        [else
         (vector? v)]))

    (define/override (interp-op op)
      (match op
        ;; The following should be moved to a new interpreter -Jeremy
        ['vector-proxy (lambda (vec rs ws) `(vector-proxy ,vec ,rs ,ws))]
        ['boolean? (match-lambda
                     [`(tagged ,v1 ,tg) (equal? tg (any-tag 'Boolean))]
                     [else #f])]
        ['integer? (match-lambda
                     [`(tagged ,v1 ,tg) (equal? tg (any-tag 'Integer))]
                     [else #f])]
        ['vector? (match-lambda
                    [`(tagged ,v1 ,tg) (equal? tg (any-tag `(Vector Any)))]
                    [else #f])]
        ['procedure? (match-lambda
                       [`(tagged ,v1 ,tg) (equal? tg (any-tag `(Any -> Any)))]
                       [else #f])]
        ['eq? (match-lambda*
                [`((tagged ,v1^ ,tg1) (tagged ,v2^ ,tg2))
                 (and (eq? v1^ v2^) (equal? tg1 tg2))]
                [ls (apply (super interp-op op) ls)])]
        ['make-any (lambda (v tg) `(tagged ,v ,tg))]
        ['tag-of-any
         (match-lambda
           [`(tagged ,v^ ,tg)  tg]
           [v  (error 'interp-op "expected tagged value, not ~a" v)])]
        [else (super interp-op op)]))

    (define/override ((interp-exp env) e)
      (define recur (interp-exp env))
      (verbose "R6/interp-exp" e)
      (match e
        [(Inject e ty) `(tagged ,(recur e) ,(any-tag ty))]
        [(Project e ty2)  (apply-project (recur e) ty2)]
        [(ValueOf e ty)
         (match (recur e)
           [`(tagged ,v^ ,tg)  v^]
           [v (error 'interp-op "expected tagged value, not ~a" v)])]
        [(Exit) (error 'interp-exp "exiting")]
        [else ((super interp-exp env) e)]))
    ))

(define (interp-R6 p)
  (send (new interp-R6-class) interp-program p))
