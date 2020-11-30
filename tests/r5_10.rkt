(let ([y (read)])
  (let ([f (lambda: ([x : Integer]) : Integer
                    (+ x y))])
    (f 21)))
