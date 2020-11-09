(define (id [x : Integer]) : Integer x)

(define (f [v : (Vector (Integer -> Integer))]) : (Integer -> Integer)
  (vector-ref v 0))

((f (vector id)) 42)
