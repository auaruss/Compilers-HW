(define (tail-sum [n : Integer] [r : Integer]) : Integer
  (if (eq? n 0) r
      (tail-sum (- n 1) (+ n r))))

(+ (tail-sum 5 0) 27)
