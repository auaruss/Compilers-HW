;; a function that triggers collect
(define (g [x : Integer]) : Integer
  (let ([v (vector 1)])
    (if (eq? x 0)
        0
        (g (- x (vector-ref v 0))))))

(let ([v1 (vector 1)])
(let ([v2 (vector 1)])
(let ([v3 (vector 1)])
(let ([v4 (vector 1)])
(let ([v5 (vector 1)])
(let ([v6 (vector 1)])
(let ([v7 (vector 1)])
(let ([v8 (vector 1)])
(let ([v9 (vector 1)])
(let ([v10 (vector 1)])
(let ([y (g 1000)])    ;; a function call with live vector-typed variables.
    (+ (+ 32 y)
       (+ (vector-ref v1 0)
       (+ (vector-ref v2 0)
          (+ (vector-ref v3 0)
             (+ (vector-ref v4 0)
                (+ (vector-ref v5 0)
                   (+ (vector-ref v6 0)
                      (+ (vector-ref v7 0)
                         (+ (vector-ref v8 0)
                            (+ (vector-ref v9 0)
                               (vector-ref v10 0))))))))))))))))))))))





