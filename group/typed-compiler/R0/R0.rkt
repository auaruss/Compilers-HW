#lang typed/racket


(struct Int [(value : Integer)])
(struct Prim [(op : Op) (args* : (Listof Exp))])
(struct Program [(body : Exp)]) ; info missing but not needed for R0 I think?

(define-type Op (U 'read '+ '-))
(define-type Exp (U Int Prim))
(define-type R0 Program)

(: list-max (→ (Listof Integer) Integer))
(define list-max
  (λ (ls)
    (foldl max 0 ls)))

(: height (→ Exp Integer))
(define height
  (λ (exp)
    (match exp
      [(Int n) 1]
      [(Prim op args*)
       (add1 (list-max (map height args*)))])))