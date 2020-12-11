#lang racket
(require racket/fixnum)
(require "utilities.rkt" (prefix-in runtime-config: "runtime-config.rkt"))
(provide interp-R7 interp-R7-prog)

;; Note to maintainers of this code:
;;   A copy of this interpreter is in the book and should be
;;   kept in sync with this code.

(define (tag-of-any e)
  (match e
    [`(tagged ,v ,ty) ty]
    [else (error 'tag-of-any "expected a tagged value, not ~a" e)]
    ))

(define (value-of-any e)
  (match e
    [`(tagged ,v ,ty) v]
    [else (error 'value-of-any "expected a tagged value, not ~a" e)]))

(define primitives (set '+ '- 'read
			'< '<= '> '>= 'not
			'vector 'vector-ref 'vector-set!
			'boolean? 'integer? 'vector? 'procedure?))

(define (interp-op op)
  (match op
    ['+ fx+]
    ['- fx-]
    ['read read-fixnum]
    ['not (lambda (v) (match v [#t #f] [#f #t]))]
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
    ['vector vector]
    ['vector-ref vector-ref]
    ['vector-set! vector-set!]
    ['boolean? (lambda (v)
		 (match v
		   [`(tagged ,v1 Boolean) #t]
		   [else #f]))]
    ['integer? (lambda (v)
		 (match v
		   [`(tagged ,v1 Integer) #t]
		   [else #f]))]
    ['vector? (lambda (v)
		(match v
		  [`(tagged ,v1 (Vector ,ts ...)) #t]
		  [else #f]))]
    ['procedure? (lambda (v)
		   (match v
		     [`(tagged ,v1 (,ts ... -> ,rt)) #t]
		     [else #f]))]
    [else (error 'interp-op "unknown operator")]
    ))

(define (tag-value v)
  (cond [(boolean? v) `(tagged ,v Boolean)]
        [(fixnum? v) `(tagged ,v Integer)]
        [(procedure? v)
         (define n (procedure-arity v))
         `(tagged ,v (,@(for/list ([_ (range 0 n)]) 'Any) -> Any))]
        [(vector? v) `(tagged ,v (Vectorof Any))]
        [(void? v) `(tagged ,v Void)]
        [else
         (error 'tag-value "unidentified value ~a" v)]
        ))

(define (interp-R7-exp env)
  (lambda (ast)
    (define recur (interp-R7-exp env))
    (match ast
      [(Var x) (lookup x env)]
      [(FunRef f) (lookup f env)]
      ;; The following deals with the detail of our translation.
      ;; It keeps the arity of functions in the funref.
      [(FunRefArity f n) (lookup f env)]
      [(Int n) `(tagged ,n Integer)]
      [(Bool b) `(tagged ,b Boolean)]
      [(Prim 'read '()) `(tagged ,(read-fixnum) Integer)]
      [(Lambda xs rt body)
       `(tagged (function ,xs ,body ,env)
                (,@(for/list ([x xs]) 'Any) -> Any))]
      [(Prim 'vector es)
       `(tagged ,(apply vector (for/list ([e es]) (recur e)))
                (Vector ,@(for/list ([e es]) 'Any)))]
      [(Prim 'vector-set! (list e1 n e2))
       (define vec (value-of-any (recur e1)))
       (define i (value-of-any (recur n)))
       (vector-set! vec i (recur e2))
       `(tagged ,(void) Void)]
      [(Prim 'vector-ref (list e1 n))
       (define vec (value-of-any (recur e1)))
       (define i (value-of-any (recur n)))
       (vector-ref vec i)]
      [(Let x e body)
       (let ([v (recur e)])
         ((interp-R7-exp (cons (cons x v) env)) body))]
      [(Prim 'and (list e1 e2))
       (recur (If e1 e2 (Bool #f)))]
      [(Prim 'or (list e1 e2))
       (define v1 (recur e1))
       (match (value-of-any v1)
         [#f (recur e2)]
         [else v1])]
      [(Prim 'eq? (list l r))
       `(tagged ,(equal? (recur l) (recur r)) Boolean)]
      [(If q t f)
       (match (value-of-any (recur q))
         [#f (recur f)]
         [else (recur t)])]
      [(Prim op es)
       (tag-value
        (apply (interp-op op) (for/list ([e es]) (value-of-any (recur e)))))]
      [(Apply f es)
       (define new-args (map recur es))
       (let ([f-val (value-of-any (recur f))])
         (match f-val 
           [`(function (,xs ...) ,body ,lam-env)
            (define new-env (append (map cons xs new-args) lam-env))
            ((interp-R7-exp new-env) body)]
           [else (error "interp-R7-exp, expected function, not" f-val)]))]
      [(HasType e t)
       (recur e)]
      )))

(define (interp-R7-def ast)
  (match ast
    [(Def f xs rt info body)
     (mcons f `(function ,xs ,body ()))]
    [else
     (error "interp-R7-def unmatched" ast)]
    ))

;; This version is for source code in R7.
(define (interp-R7 ast)
  (match ast
    [(ProgramDefsExp info ds body)
     (let ([top-level (map (lambda (d) (interp-R7-def d)) ds)])
         ;; Use set-cdr! on define lambda's for mutual recursion
       (for/list ([b top-level])
         (set-mcdr! b (match (mcdr b)
                        [`(function ,xs ,body ())
                         `(tagged (function ,xs ,body ,top-level) 
                                  (,@(for/list ([x xs]) 'Any) -> Any))])))
       (match ((interp-R7-exp top-level) body)
         [`(tagged ,n Integer)
          n]
         [v
          (error 'interp-R7 "expected an integer result from the program, not "
                 v)]))]
    [(Program info body)
     (let ([top-level '()])
       (match ((interp-R7-exp top-level) body)
         [`(tagged ,n Integer)
          n]
         [v
          (error 'interp-R7 "expected an integer result from the program, not "
                 v)]))]
    [else
     (error "interp-R7 unmatched" ast)]
    ))

;; This version is for after uniquify.
(define (interp-R7-prog ast)
  (match ast
    [(ProgramDefs info ds)
     (let ([top-level (map (lambda (d) (interp-R7-def d)) ds)])
       ;; Use set-cdr! on define lambda's for mutual recursion
       (for/list ([b top-level])
         (set-mcdr! b (match (mcdr b)
                        [`(function ,xs ,body ())
                         `(tagged (function ,xs ,body ,top-level) 
                                  (,@(for/list ([x xs]) 'Any) -> Any))])))
       (match ((interp-R7-exp top-level) (Apply (Var 'main) '()))
         [`(tagged ,n Integer)
          n]
         [v
          (error 'interp-R7 "expected an integer result from the program, not "
                 v)]))]
    [else
     (error "interp-R7-prog unmatched" ast)]
    ))
