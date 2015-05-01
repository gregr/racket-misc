#lang racket/base
; described in: http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf
(provide
  ==
  call/fresh
  conj
  disj
  muk-state-empty
  Zzz
  )

(require
  "dict.rkt"
  "list.rkt"
  "maybe.rkt"
  "monad.rkt"
  "record.rkt"
  "sugar.rkt"
  racket/function
  (except-in racket/match ==)
  )

(module+ test
  (require rackunit))

(record muk-var name)
(record muk-sub bindings)
(define muk-sub-empty (muk-sub (hash)))
(define (muk-sub-get sub vr)
  (match (if (muk-var? vr) (dict-get (muk-sub-bindings sub) vr) (nothing))
    ((nothing) vr)
    ((just vr) (muk-sub-get sub vr))))
(def (muk-sub-add (muk-sub bs) vr val) (muk-sub (dict-add bs vr val)))
(record muk-state sub next-var)
(define muk-state-empty (muk-state muk-sub-empty (muk-var 0)))
(def (muk-var-next (muk-var idx)) (muk-var (+ 1 idx)))

(define muk-mzero '())
(define (muk-mplus ss1 ss2)
  (match ss1
    ('() ss2)
    ((? procedure?) (thunk (muk-mplus ss2 (ss1))))
    ((cons st ss) (list* st (muk-mplus ss ss2)))))
(define (muk-unit st) (list* st muk-mzero))
(define (muk-bind ss goal)
  (match ss
    ('() muk-mzero)
    ((? procedure?) (thunk (muk-bind (ss) goal)))
    ((cons st ss) (muk-mplus (goal st) (muk-bind ss goal)))))

(def (pair-components (cons a d)) (list a d))
(define (vector-components vec) (vector->list vec))
(define (struct-components str) (vector-components (struct->vector str)))
(define (hash-components hsh) (hash->list hsh))  ; TODO: generic key sorting

(def (muk-unify sub e0 e1)
  e0 = (muk-sub-get sub e0)
  e1 = (muk-sub-get sub e1)
  (if (equal? e0 e1) (just sub)
    (lets
      (list e0 e1) = (if (muk-var? e1) (list e1 e0) (list e0 e1))
      (if (muk-var? e0) (just (muk-sub-add sub e0 e1))
        (lets
          (list found components) =
          (forf (list found components) = (list #f '())
                (list pred make-components) <- `((,pair? ,pair-components)
                                                 (,vector? ,vector-components)
                                                 (,struct? ,struct-components)
                                                 (,hash? ,hash-components))
                #:break found
                found = (and (pred e0) (pred e1))
                (if found
                  (list found (zip (map make-components (list e0 e1))))
                  (list found components)))
          (if found
            (monad-foldl maybe-monad
              (fn (sub (list e0c e1c)) (muk-unify sub e0c e1c)) sub components)
            (nothing)))))))

(def ((== e0 e1) (muk-state sub next))
  (match (muk-unify sub e0 e1)
    ((nothing) muk-mzero)
    ((just sub) (muk-unit (muk-state sub next)))))

(def ((call/fresh f) (muk-state sub next))
  ((f next) (muk-state sub (muk-var-next next))))

(define ((conj g0 g1) st) (muk-bind (g0 st) g1))
(define ((disj g0 g1) st) (muk-mplus (g0 st) (g1 st)))

(define-syntax Zzz
  (syntax-rules () ((_ goal) (lambda (st) (thunk (goal st))))))

(module+ test
  (define (get-by-name name st) (muk-sub-get (muk-state-sub st) (muk-var 0)))
  (define (one-and-two x) (conj (== x 1) (== x 2)))
  (check-equal?
    ((call/fresh one-and-two) muk-state-empty)
    '())
  (define (fives x) (disj (== x 5) (Zzz (fives x))))
  (check-equal?
    (get-by-name 0 (car ((call/fresh fives) muk-state-empty)))
    5)
  (define (sixes x) (disj (== x 6) (Zzz (sixes x))))
  (define fives-and-sixes
    (call/fresh (lambda (x) (disj (fives x) (sixes x)))))
  (lets
    ss0 = (fives-and-sixes muk-state-empty)
    st0 = (car ss0)
    ss1 = ((cdr ss0))
    st1 = (car ss1)
    (check-equal?
      (map (curry get-by-name 0) (list st0 st1))
      '(5 6)))
  )
