#lang racket/base
(provide
  def
  forf
  forl
  lets
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
     (for/fold/match acc elem-seqs (lets body ...)))))

(define-syntax forf
  (syntax-rules (=)
    ((_ acc = acc-init rest ...)
     (forf-cont ((acc acc-init)) () rest ...))))

(module+ test
  (check-equal?
    (list 6 4 2)
    (forf result = '()
          elem <- (list 1 2 3)
          doubled = (* 2 elem)
      (cons doubled result))))

(define-syntax forl-cont
  (syntax-rules (<-)
    ((_ (elem-seqs ...) elem <- seq rest ...)
     (forl-cont (elem-seqs ... (elem seq)) rest ...))
    ((_ elem-seqs body ...)
     (for/list/match elem-seqs (lets body ...)))))

(define-syntax forl
  (syntax-rules ()
    ((_ rest ...)
     (forl-cont () rest ...))))

(module+ test
  (check-equal?
    '((a 2) (b 4) (c 6))
    (forl x <- '(a b c)
          y <- '(1 2 3)
          yy = (* 2 y)
      (list x yy))))

(define-syntax fn
  (syntax-rules ()
    ((_ (pattern ...) body ...)
     (lambda/destruct (pattern ...) (lets body ...)))))

(module+ test
  (check-equal?
    ((fn ((list x y) z)
        w = (+ x y)
        (* z w))
     (list 1 2) 3)
    9))

(define-syntax def
  (syntax-rules ()
    ((_ (name pattern ...) body ...)
     (define name
       (fn (pattern ...) body ...)))))

(module+ test
  (def (test-def (list x y) z)
    w = (+ x y)
    (* z w))
  (check-equal?
    (test-def (list 1 2) 3)
    9))
