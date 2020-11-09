(define (big [x : Integer] [y : Integer] [z : Integer]) : Integer
  (+ (+ (+ (+ x y) (+ x z))
        (+ (+ z x) (+ z y)))
     (+ (+ (+ y y) (+ y x))
        (+ (+ z x) (+ z z)))))

(+ 42 (big (read) (read) (read)))
