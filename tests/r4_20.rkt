(define (foo [x1 : Integer] [x2 : Integer] [x3 : Integer]
             [x4 : Integer] [x5 : Integer] [x6 : Integer]
             [x7 : Integer] [x8 : Integer] [x9 : Integer]) : Integer
  (if (eq? 0 x1) x9
      (foo (+ x1 (- 1)) x2 x3 x4 x5 x6 x7 x8 (+ x9 (- 1)))))
(foo 100 2 3 4 5 6 7 8 142)
