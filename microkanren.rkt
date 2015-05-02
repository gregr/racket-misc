#lang racket/base
; described in: http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf
(provide
  ==
  call/fresh
  conj
  conj*
  disj
  disj*
  muk-state-empty
  muk-state-sub
  muk-take
  muk-take-all
  muk-var
  muk-var?
  muk-var->symbol
  muk-reify
  muk-reify-var
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
(define (muk-split aggs)
  (forf components = (nothing)
        (list pred make-components) <- `((,pair? ,pair-components)
                                         (,vector? ,vector-components)
                                         (,struct? ,struct-components)
                                         (,hash? ,hash-components))
        #:break (just? components)
        (if (andmap pred aggs) (just (map make-components aggs)) components)))
(def (muk-rebuild agg components)
  (values sty _) = (struct-info agg)
  (apply (struct-type-make-constructor sty) components))

(def (muk-unify sub e0 e1)
  e0 = (muk-sub-get sub e0)
  e1 = (muk-sub-get sub e1)
  (if (equal? e0 e1) (just sub)
    (lets
      (list e0 e1) = (if (muk-var? e1) (list e1 e0) (list e0 e1))
      (if (muk-var? e0) (just (muk-sub-add sub e0 e1))
        (begin/with-monad maybe-monad
          components <- (muk-split (list e0 e1))
          (monad-foldl maybe-monad
            (fn (sub (list e0c e1c)) (muk-unify sub e0c e1c)) sub
            (zip components)))))))

(def (muk-var->symbol (muk-var name))
  (string->symbol (string-append "_." (number->string name))))
(def (muk-reify-var sub vr vtrans)
  vr = (muk-sub-get sub vr)
  (if (muk-var? vr) (vtrans vr)
    (match (muk-split (list vr))
      ((nothing) vr)
      ((just components)
       (muk-rebuild
         vr (map (fn (vr) (muk-reify-var sub vr vtrans)) components))))))
(define (muk-reify vtrans vrs states)
  (forl (muk-state sub _) <- states
        (forl vr <- vrs
              (muk-reify-var sub vr vtrans))))

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

(define-syntax conj*-cont
  (syntax-rules ()
    ((_ g0 g1) (conj g0 g1))
    ((_ g0 gs ...) (conj g0 (conj*-cont gs ...)))))
(define-syntax conj*
  (syntax-rules ()
    ((_) muk-unit)
    ((_ g0) g0)
    ((_ gs ...) (Zzz (conj*-cont gs ...)))))
(define-syntax disj*-cont
  (syntax-rules ()
    ((_ g0) (Zzz g0))
    ((_ g0 gs ...) (disj (Zzz g0) (disj*-cont gs ...)))))
(define-syntax disj*
  (syntax-rules ()
    ((_) (const muk-zero))
    ((_ g0) g0)
    ((_ gs ...) (disj*-cont gs ...))))

(define (muk-force ss) (if (procedure? ss) (muk-force (ss)) ss))
(define (muk-take n ss)
  (if (= 0 n) '()
    (match (muk-force ss)
      ('() '())
      ((cons st ss) (list* st (muk-take (- n 1) ss))))))
(define (muk-take-all ss) (muk-take -1 ss))

(module+ test
  (define (reify-states name states)
    (muk-reify muk-var->symbol (list (muk-var name)) states))
  (define (one-and-two x) (conj* (== x 1) (== x 2)))
  (check-equal?
    (muk-take-all ((call/fresh one-and-two) muk-state-empty))
    '())
  (check-equal?
    (reify-states 0 (muk-take-all
                      ((call/fresh (fn (x) (== x x))) muk-state-empty)))
    '((_.0)))
  (define (fives x) (disj* (== x 5) (fives x)))
  (check-equal?
    (reify-states 0 (muk-take 1 ((call/fresh fives) muk-state-empty)))
    '((5)))
  (define (sixes x) (disj* (== x 6) (sixes x)))
  (define fives-and-sixes
    (call/fresh (lambda (x) (disj (fives x) (sixes x)))))
  (lets
    (list st0 st1) = (muk-take 2 (fives-and-sixes muk-state-empty))
    (check-equal?
      (reify-states 0 (list st0 st1))
      '((5) (6)))
    ))