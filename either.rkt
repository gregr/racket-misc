#lang racket/base
(provide
  either?
  (struct-out left)
  (struct-out right)
  either-monad
  )

(require "monad.rkt")
(require "record.rkt")
(require racket/match)

(records either
  (left x)
  (right x))

(define either-monad
  (monad
    right
    (lambda (prev next)
      (match prev
        ((left x) (left x))
        ((right x) (next x))))))
