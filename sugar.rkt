#lang racket/base
(provide
  def
  fn
  fnr
  forf
  forf*
  forl
  forl*
  gn
  letn
  lets
  letsn
  )

(require
  (for-syntax racket/base)
  "generator.rkt"
  "match.rkt"
  racket/match
  )

(module+ test
  (require rackunit))

(define-syntax match-let1+values
  (syntax-rules (values)
    ((_ (values vals ...) val-expr body ...)
     (let-values (((vals ...) val-expr)) body ...))
    ((_ pattern val-expr body ...)
     (match-let ((pattern val-expr)) body ...))))
(define-syntax lets1
  (syntax-rules (=)
    ((_ (pattern = value) body ...)
     (match-let1+values pattern value body ...))))

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
    7)
  (check-equal?
    (lets
      a = 1
      (values b c) = (values 2 3)
      d = 4
      (list a b c d))
    '(1 2 3 4)))

(define-syntax for_-cont
  (syntax-rules (<-)
    ((_ cont (acc ...) (elem-seqs ...) elem <- seq rest ...)
     (for_-cont cont (acc ...) (elem-seqs ... (elem seq)) rest ...))
    ((_ cont (acc ...) (elem-seqs ...) #:when expr rest ...)
     (for_-cont cont (acc ...) (elem-seqs ... #:when expr) rest ...))
    ((_ cont (acc ...) (elem-seqs ...) #:unless expr rest ...)
     (for_-cont cont (acc ...) (elem-seqs ... #:unless expr) rest ...))
    ((_ cont (acc ...) (elem-seqs ...) #:break expr rest ...)
     (for_-cont cont (acc ...) (elem-seqs ... #:break expr) rest ...))
    ((_ cont (acc ...) (elem-seqs ...) #:final expr rest ...)
     (for_-cont cont (acc ...) (elem-seqs ... #:final expr) rest ...))
    ((_ cont (acc ...) elem-seqs body ...)
     (cont acc ... elem-seqs (lets body ...)))))

(define-syntax forf
  (syntax-rules (=)
    ((_ acc = acc-init rest ...)
     (for_-cont for/fold/match (((acc acc-init))) () rest ...))))

(define-syntax forf*
  (syntax-rules (=)
    ((_ acc = acc-init rest ...)
     (for_-cont for*/fold/match (((acc acc-init))) () rest ...))))

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

(module+ test
  (check-equal?
    (forf* result = '()
          x <- (list 1 2)
          y <- '(a b)
      doubled = (* 2 x)
      (cons (list doubled y) result))
    '((4 b) (4 a) (2 b) (2 a))
    ))

(define-syntax forl
  (syntax-rules ()
    ((_ rest ...)
     (for_-cont for/list/match () () rest ...))))

(define-syntax forl*
  (syntax-rules ()
    ((_ rest ...)
     (for_-cont for*/list/match () () rest ...))))

(module+ test
  (check-equal?
    (forl x <- '(a b c)
          y <- '(1 2 3)
      yy = (* 2 y)
      (list x yy))
    '((a 2) (b 4) (c 6))
    ))

(module+ test
  (check-equal?
    (forl* x <- '(a b)
           y <- '(1 2)
      yy = (* 2 y)
      (list x yy))
    '((a 2) (a 4) (b 2) (b 4))
    ))

(define-syntax for_
  (syntax-rules ()
    ((_ rest ...) (void (forl rest ...)))))

(define-syntax for_*
  (syntax-rules ()
    ((_ rest ...) (void (forl* rest ...)))))

(module+ test
  (check-equal?
    (for_ x <- '(a b c)
          y <- '(1 2 3)
      yy = (* 2 y)
      (list x yy))
    (void)
    ))

(module+ test
  (check-equal?
    (for_* x <- '(a b)
           y <- '(1 2)
      yy = (* 2 y)
      (list x yy))
    (void)
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

(define-syntax fnr
  (syntax-rules ()
    ((_ (name pattern ...) body ...)
     (letrec ((name (fn (pattern ...) body ...))) name))))

(module+ test
  (check-equal?
    ((fnr (len xs)
        (match xs
          ('() 0)
          ((cons _ xs) (+ 1 (len xs)))))
     '(a b c))
    3
    ))

(define-syntax def
  (syntax-rules ()
    ((_ ((pre ...) post ...) body ...)
     (def (pre ...) (fn (post ...) body ...)))
    ((_ (name pattern ...) body ...)
     (define name (fn (pattern ...) body ...)))))

(module+ test
  (def (test-def (list x y) z)
    w = (+ x y)
    (* z w))
  (check-equal?
    (test-def (list 1 2) 3)
    9)
  (def (((test-def-curried (list a b)) c) (list d e))
    result = (list a b c d e)
    result)
  (check-equal?
    (((test-def-curried (list 1 2)) 3) (list 4 5))
    '(1 2 3 4 5)))

(define-syntax gn
  (syntax-rules ()
    ((_ yield (pattern ...) body ...)
     (lambda/destruct (pattern ...) (run* yield (lets body ...))))))

(module+ test
  (check-equal?
    (lets
      gen = (gn yield (arg0)
              arg1 = (yield (+ 10 arg0))
              arg2 = (yield (+ 20 arg1))
              arg2)
      (gen-susp v0 gen) = (gen 0)
      (gen-susp v1 gen) = (gen 1)
      (gen-result r) = (gen 2)
      (list v0 v1 r))
    (list 10 21 2)
    ))

(define-syntax letsn_-cont
  (syntax-rules (=)
    ((_ name (pattern ...) (init-value ...) () body ...)
     ((lambda ()
        (def (name pattern ...) body ...)
        (name init-value ...))))
    ((_ name (pattern ...) (init-value ...)
        (next-pattern = next-value rest ...) body ...)
     (letsn_-cont
       name (pattern ... next-pattern) (init-value ... next-value) (rest ...)
       body ...))))

(define-syntax letsn
  (syntax-rules ()
    ((_ name (assignment ...) body ...)
     (letsn_-cont name () () (assignment ...) body ...))))

(module+ test
  (check-equal?
    (letsn loop (result = '() (cons x xs) = '(a b c d))
      (match xs
        ('() (cons x result))
        (_ (loop (cons x result) xs))))
    '(d c b a)
    ))

(define-syntax letn
  (syntax-rules (=)
    ((_ name pattern = init-value body ...)
     ((lambda ()
        (def (name pattern) body ...)
        (name init-value))))))

(module+ test
  (check-equal?
    (letn loop (list result (cons x xs)) = (list '() '(a b c d))
      (match xs
        ('() (cons x result))
        (_ (loop (list (cons x result) xs)))))
    '(d c b a)
    ))
