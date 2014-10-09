#lang racket/base
(provide
  lets
  forf
  )

(require
  (for-syntax racket/base)
  "match.rkt"
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

(define-syntax forf-cont
  (syntax-rules (<-)
    ((_ acc (elem-seqs ...) elem <- seq rest ...)
     (forf-cont acc (elem-seqs ... (elem seq)) rest ...))
    ((_ acc elem-seqs body ...)
     (for/fold/match acc elem-seqs body ...))))

(define-syntax forf
  (syntax-rules (=)
    ((_ acc = acc-init rest ...)
     (forf-cont ((acc acc-init)) () rest ...))))

(module+ test
  (check-equal?
    (list 3 2 1)
    (forf result = '()
          elem <- (list 1 2 3)
      (cons elem result))))
