#lang racket/base
(provide
  make-immutable-string
  )

(module+ test
  (require rackunit))

(define (make-immutable-string count char)
  (string->immutable-string (make-string count char)))

(module+ test
  (check-equal?
    (make-immutable-string 3 #\+)
    "+++"))
