#lang racket/base
(provide
  maybe?
  (struct-out nothing)
  (struct-out just)
  maybe-filter
  maybe-fold
  maybe-from
  maybe-iterate
  maybe-map
  maybe-monad
  maybe-or
  )

(require
  "monad.rkt"
  "record.rkt"
  racket/match
  )

(module+ test
  (require
    rackunit
    ))

(records maybe
  (nothing)
  (just x))

(define (maybe-from default maybe-value)
  (match maybe-value
    ((nothing) default)
    ((just x)  x)))

(define (maybe-fold nothing-fold just-fold val)
  (match val
    ((nothing) nothing-fold)
    ((just x)  (just-fold x))))

(define (maybe-map f val)
  (maybe-fold val (compose1 just f) val))

(define (maybe-filter ms) (map just-x (filter just? ms)))

(module+ test
  (check-equal?
    (maybe-filter (list (nothing) (just 3) (nothing) (just 4)))
    '(3 4)
    ))

(define maybe-monad
  (monad
    just
    (lambda (prev next)
      (match prev
        ((nothing) (nothing))
        ((just x)  (next x))))))

(define-syntax maybe-or
  (syntax-rules ()
    ((_ arg ...)
     (cond
       ((let ((result arg))
          (if (just? result) result #f)) => (lambda (result) result))
       ...
       (else (nothing))))))

(define (maybe-iterate f arg)
  (match (f arg)
    ((nothing)  arg)
    ((just arg) (maybe-iterate f arg))))
