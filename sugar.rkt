#lang racket/base
(provide
  lets
  )

(require
  racket/match
  )

(module+ test
  (require rackunit))

(define-syntax lets1
  (syntax-rules (=)
    ((_ (pattern = value) body ...)
     (match-let ((pattern value)) body ...))))

(define-syntax lets
  (syntax-rules ()
    ((_ pattern bind-sym value body ...)
     (lets1 (pattern bind-sym value) (lets body ...)))
    ((_ body)
     body)))

(module+ test
  (check-equal?
    7
    (lets
      x = 4
      y = 3
      (+ x y))))
