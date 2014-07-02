#lang racket/base
(provide
  maybe?
  (struct-out nothing)
  (struct-out just)
  maybe-from
  maybe-monad
  maybe-or
  )

(require
  "monad.rkt"
  "record.rkt"
  racket/match
  )

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

(define-syntax maybe-or
  (syntax-rules ()
    ((_ arg ...)
     (cond
       ((let ((result arg))
          (if (just? result) result #f)) => (lambda (result) result))
       ...
       (else (nothing))))))
