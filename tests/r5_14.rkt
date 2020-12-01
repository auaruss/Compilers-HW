(define (f) : (Integer -> (Vector Integer))
  (let ([v (vector 0)])
    (lambda: ([x : Integer]) : (Vector Integer)
             (let ([y (vector-set! v 0 x)])
               v))))
(let ([g (f)])
  (let ([h (f)])
    (let ([a (g 1)])
      (let ([b (h 2)])
        (let ([c (g 20)])
          (let ([d (h 22)])
            (+ (vector-ref c 0)
               (vector-ref d 0))))))))

