(define (h [a : Integer] [b : Integer] [c : Integer] [d : Integer]
           [e : Integer] [f : Integer] [g : Integer]) : Integer
  (+ a (+ b (+ c (+ d (+ e (+ f g)))))))
(h 1 2 3 4 5 6 7)
