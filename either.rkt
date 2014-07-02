#lang racket/base
(provide
  either?
  (struct-out left)
  (struct-out right)
  either-monad
  either-or
  )

(require
  "monad.rkt"
  "record.rkt"
  racket/match
  )

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

(define-syntax either-or
  (syntax-rules ()
    ((_ arg ...)
     (cond
       ((let ((result arg))
          (if (right? result) result #f)) => (lambda (result) result))
       ...
       (else (nothing))))))
