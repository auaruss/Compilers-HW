(define (f [x : Integer]) : (Integer -> Integer)
   (let ([y 4])
      (lambda: ([z : Integer]) : Integer
	 (+ x (+ y z)))))

(let ([g (if (eq? 0 0)
             (f 5)
             (lambda: ([x : Integer]) : Integer x))])
  (let ([h (if (< 0 1)
               (f 3)
               (if #t
                   (f 0)
                   (f 1)))])
    (- (+ (let ([k g])
            (- (k 11)))
          (let ([j h])
            (- (j 15)))))))
