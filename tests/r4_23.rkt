(define (f [x : Integer]) : Integer
  (if (eq? x 0) 0
      (if (eq? x 1) 1
          (+ (f (- x 1)) (f (- x 2))))))

(define (g [x : Integer] [y : Integer] [z : Integer]) : Integer
  (if (eq? x 0) y
      (if (eq? x 1) z
          (g (- x 1) z (+ y z)))))

(+ (f 8) (g 8 0 1))
