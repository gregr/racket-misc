#lang racket/base
(provide
  either?
  (struct-out left)
  (struct-out right)
  either-fold
  either-from
  either-iterate
  either-map
  either-monad
  either-or
  either->maybe
  maybe->either
  )

(require
  "maybe.rkt"
  "monad.rkt"
  "record.rkt"
  racket/function
  racket/match
  )

(records either
  (left x)
  (right x))

(define (either-fold left-fold right-fold val)
  (match val
    ((left x)  (left-fold x))
    ((right x) (right-fold x))))

(define (either-from default either-value)
  (either-fold (const default) identity either-value))

(define (either-map f val)
  (either-fold (const val) (compose1 right f) val))

(define either-monad
  (monad
    right
    (lambda (prev next)
      (match prev
        ((left x)  (left x))
        ((right x) (next x))))))

(define-syntax either-or
  (syntax-rules ()
    ((_ arg ...)
     (cond
       ((let ((result arg))
          (if (right? result) result #f)) => (lambda (result) result))
       ...
       (else (nothing))))))

(define (either-iterate f arg)
  (match (f arg)
    ((left _)    arg)
    ((right arg) (either-iterate f arg))))

(define (either->maybe either)
  (either-fold (const (nothing)) just either))

(define (maybe->either left-arg maybe)
  (maybe-fold (left left-arg) right maybe))
