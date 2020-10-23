(let ([v1 (vector 0)])
  (let ([g1 (vector 1 2 3 4 5)])
    (let ([dummy
           (if (eq? (read) 0)
               (vector-set! v1 0 42)
               (vector-set! g1 0 42))])
      (vector-ref v1 0))))
    
