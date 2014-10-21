#lang racket/base
(provide
  abstain
  single
  choose
  choice
  maybe-choice
  either-choice
  list-choice
  eff-maybe-choice
  eff-either-choice
  eff-list-choice
  )

(require
  "eff.rkt"
  "either.rkt"
  "maybe.rkt"
  racket/match
  )

(module+ test
  (require
    "sugar.rkt"
    rackunit
    ))

(define (choice) (effect abstain single choose))

(define (abstain ch reason) (@! ch abstain reason))
(define (single ch v)       (@! ch single v))
(define (choose ch xs)      (@! ch choose xs))

(define (maybe-choice ch)
  (handler
    (ch (abstain _ k) (nothing))
    (ch (single v k)  (k (just v)))
    (ch (choose maybe k)
      (match maybe
        ((nothing) (nothing))
        ((just x)  (k x))))
    (return v (just v))))

(define (either-choice ch)
  (handler
    (ch (abstain reason k) (left reason))
    (ch (single v k)       (k (right v)))
    (ch (choose either k)
      (match either
        ((left _)  either)
        ((right x) (k x))))
    (return v (right v))))

(define (list-choice ch)
  (handler
    (ch (abstain _ k) '())
    (ch (single v k)  (k (list v)))
    (ch (choose choices k)
      (apply append (for/list ((choice choices)) (k choice))))
    (return v (list v))))

(define-syntax eff-choice
  (syntax-rules ()
    ((_ choice-handler eff-name body ...)
     (let ((eff-name (choice)))
       (eff-handle (choice-handler eff-name) body ...)))))
(define-syntax eff-maybe-choice
  (syntax-rules ()
    ((_ eff-name body ...) (eff-choice maybe-choice eff-name body ...))))
(define-syntax eff-either-choice
  (syntax-rules ()
    ((_ eff-name body ...) (eff-choice either-choice eff-name body ...))))
(define-syntax eff-list-choice
  (syntax-rules ()
    ((_ eff-name body ...) (eff-choice list-choice eff-name body ...))))

(module+ test
  (check-equal?
    (eff-maybe-choice ch
      (lets
        x = (choose ch (single ch 3))
        y = (choose ch (just 4))
        (+ x y)))
    (just (+ 3 4))
    ))

(module+ test
  (check-equal?
    (eff-maybe-choice ch
      (lets
        x = (choose ch (just 3))
        z = (choose ch (nothing))
        y = (choose ch (just 4))
        (+ x y)))
    (nothing)
    ))

(module+ test
  (check-equal?
    (eff-maybe-choice ch
      (lets
        x = (choose ch (just 3))
        z = (abstain ch 'explicit)
        y = (choose ch (just 4))
        (+ x y)))
    (nothing)
    ))

(module+ test
  (check-equal?
    (eff-either-choice ch
      (lets
        x = (choose ch (right 3))
        y = (choose ch (single ch 4))
        (+ x y)))
    (right (+ 3 4))
    ))

(module+ test
  (check-equal?
    (eff-either-choice ch
      (lets
        x = (choose ch (right 3))
        z = (choose ch (left 'explicit))
        y = (choose ch (right 4))
        (+ x y)))
    (left 'explicit)
    ))

(module+ test
  (check-equal?
    (eff-either-choice ch
      (lets
        x = (choose ch (right 3))
        z = (abstain ch 'implicit)
        y = (choose ch (right 4))
        (+ x y)))
    (left 'implicit)
    ))

(module+ test
  (check-equal?
    (eff-list-choice ch
      (lets
        x = (choose ch (list 1 2))
        y = (choose ch (list 3 4))
        (+ x y)))
    (list 4 5 5 6)
    ))

(module+ test
  (check-equal?
    (eff-list-choice ch
      (lets
        x = (choose ch (list 1 2))
        z = (choose ch (list))
        y = (choose ch (list 3 4))
        (+ x y)))
    (list)
    ))

(module+ test
  (check-equal?
    (eff-list-choice ch
      (lets
        x = (choose ch (list 1 2))
        z = (abstain ch 'explicit)
        y = (choose ch (list 3 4))
        (+ x y)))
    (list)
    ))

(module+ test
  (check-equal?
    (eff-list-choice ch
      (lets
        x = (choose ch (list 1 2))
        y = (choose ch (list 3 4))
        w = (+ x y)
        z = (choose ch (if (= w 5) (list) (list 10)))
        (+ w z)))
    (list 14 16)
    ))
