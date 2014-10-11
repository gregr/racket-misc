#lang racket/base
(provide
  def
  fn
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
    (lets
      x = 4
      y = 3
      (+ x y))
    7
    ))

(define-syntax forf-cont
  (syntax-rules (<-)
    ((_ acc (elem-seqs ...) elem <- seq rest ...)
     (forf-cont acc (elem-seqs ... (elem seq)) rest ...))
    ((_ acc (elem-seqs ...) #:when expr rest ...)
     (forf-cont acc (elem-seqs ... #:when expr) rest ...))
    ((_ acc (elem-seqs ...) #:unless expr rest ...)
     (forf-cont acc (elem-seqs ... #:unless expr) rest ...))
    ((_ acc (elem-seqs ...) #:break expr rest ...)
     (forf-cont acc (elem-seqs ... #:break expr) rest ...))
    ((_ acc (elem-seqs ...) #:final expr rest ...)
     (forf-cont acc (elem-seqs ... #:final expr) rest ...))
    ((_ acc elem-seqs body ...)
     (for/fold/match acc elem-seqs (lets body ...)))))

(define-syntax forf
  (syntax-rules (=)
    ((_ acc = acc-init rest ...)
     (forf-cont ((acc acc-init)) () rest ...))))

(module+ test
  (check-equal?
    (forf result = '()
          elem <- (list 1 2 3)
      doubled = (* 2 elem)
      (cons doubled result))
    (list 6 4 2)
    ))

(module+ test
  (check-equal?
    (forf result = '()
          elem <- (list 1 2 3)
          #:when (odd? elem)
      doubled = (* 2 elem)
      (cons doubled result))
    (list 6 2)
    ))

(define-syntax (forl stx)
  (syntax-case stx ()
    ((_ most ... body)
     (with-syntax ((list-acc (datum->syntax #'this 'list-acc)))
      #'(reverse (forf list-acc = '() most ... (cons body list-acc)))))))

(module+ test
  (check-equal?
    (forl x <- '(a b c)
          y <- '(1 2 3)
          yy = (* 2 y)
      (list x yy))
    '((a 2) (b 4) (c 6))
    ))

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
