(define (add8  [a : Integer] [b : Integer] [c : Integer] [d : Integer] [e : Integer] [f : Integer] [g : Integer] [h : Integer]) : Integer
   (+ a (+ b (+ c (+ d (+ e (+ f (+ g h))))))))
(add8 1 2 3 4 5 6 7 8)
