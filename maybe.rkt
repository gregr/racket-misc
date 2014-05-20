#lang racket/base
(provide
  maybe?
  (struct-out nothing)
  (struct-out just)
  maybe-from
  maybe-monad
  )

(require "monad.rkt")
(require "record.rkt")
(require racket/match)

(records maybe
  (nothing)
  (just x))

(define (maybe-from default maybe-value)
  (match maybe-value
    ((nothing) default)
    ((just x)  x)))

(define maybe-monad
  (monad
    just
    (lambda (prev next)
      (match prev
        ((nothing) (nothing))
        ((just x) (next x))))))
