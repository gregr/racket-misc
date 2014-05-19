#lang racket/base
(provide
  maybe?
  (struct-out nothing)
  (struct-out just)
  maybe-monad
  )

(require "monad.rkt")
(require "record.rkt")
(require racket/match)

(records maybe
  (nothing)
  (just x))

(define maybe-monad
  (monad
    just
    (lambda (prev next)
      (match prev
        ((nothing) (nothing))
        ((just x) (next x))))))
