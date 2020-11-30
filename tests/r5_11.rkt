(define (f [x : Integer]) : (Integer -> Integer)
  (lambda: ([y : Integer]) : Integer
    (- x y)))

((f (read)) (read))
