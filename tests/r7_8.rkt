(define (vector-foo vec)
  (let ([_ (vector-set! vec 0 42)])
    vec))
(define (vector-foo-too vec)
  (let ([_ (vector-set! vec 1 42)])
    vec))
(define (vector-foo-three vec)
  (let ([_ (vector-set! vec 2 42)])
    (vector-ref vec 2)))
(let ([x (vector-foo-three (vector-foo-too (vector-foo (vector 0 0 0))))])
  x)