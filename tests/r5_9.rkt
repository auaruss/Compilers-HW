(define (g [f : (Integer Integer Integer Integer Integer Integer -> Integer)] [x : Integer])
  : Integer
  (f x x x x x x))

(g (lambda: ([x  : Integer] [y : Integer] [z : Integer]
               [u : Integer] [v : Integer] [w : Integer]) : Integer x)
     42)
