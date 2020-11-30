(define (add1 [x : Integer]) : Integer
  (+ x 1))

(let ([y (read)])
  (let ([f (if (eq? (read) 0)
               add1
               (lambda: ([x : Integer]) : Integer (- x y)))])
    (f 41)))
