(let ([f (lambda: ([y : Integer]) : Integer y)])
  (let ([g (lambda: ([x : Integer]) : Integer (f x))])
    (g 42)))
