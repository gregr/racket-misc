#lang racket/base
(provide
  min-and-max
  )

(module+ test
  (require rackunit))

(define (min-and-max v min-v max-v) (max (min v max-v) min-v))

(module+ test
  (check-equal?
    (min-and-max 4 3 10)
    4)
  (check-equal?
    (min-and-max 1 3 10)
    3)
  (check-equal?
    (min-and-max 15 3 10)
    10))
