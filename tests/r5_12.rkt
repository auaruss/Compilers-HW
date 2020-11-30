(let ([curry-add (lambda: ([x : Integer]) : (Integer -> Integer)
                          (lambda: ([y : Integer]) : Integer (+ x y)))])
  ((curry-add 20) 22))
