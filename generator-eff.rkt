#lang racket/base
(provide
  eff-gen
  (struct-out gen-choice-state)
  gen-try
  next
  next-try
  send
  send-try
  )

(require
  "choice-eff.rkt"
  "eff.rkt"
  "generator.rkt"
  "match.rkt"
  "record.rkt"
  "state-eff.rkt"
  racket/function
  racket/match
  )

(module+ test
  (require
    "either.rkt"
    "sugar.rkt"
    rackunit
    ))

(record gen-choice-state ch st)

(define-syntax eff-gen
  (syntax-rules ()
    ((_ choice-expr gen-choice-name gen body ...)
     (let ((gen-choice-name
             (gen-choice-state choice-expr (state-ref))))
       (eff-handle (state (gen-choice-state-st gen-choice-name) gen)
          body ...)))))

(define/destruct (send (gen-choice-state ch st) input)
  (choose ch
    (match ((get st) input)
      ((gen-result r) (abstention ch r))
      ((gen-susp v k) (put st k) (single ch v)))))
(define (next gs) (send gs (void)))

(define (gen-try f gs . args)
  (match gs
    ((gen-choice-state ch st)
     (reconsider ch identity identity (apply f (cons gs args))))))
(define next-try (curry gen-try next))
(define send-try (curry gen-try send))

(module+ test
  (check-equal?
    (eff-either-choice ch
      (eff-gen ch gs (generator _ (yield (* 2 (yield 10))))
        (lets
          v0 = (next gs)
          v1 = (send gs (+ 1 v0))
          v1
          )))
    (right 22)
    ))

(module+ test
  (check-equal?
    (eff-either-choice ch
      (eff-gen ch gs (generator _ (yield (* 2 (yield 10))))
        (lets
          v0 = (next gs)
          v1 = (send gs (+ 1 v0))
          v2 = (send gs (* 5 v1))
          'unreached
          )))
    (left (* 22 5))
    ))

(module+ test
  (check-equal?
    (eff-either-choice ch
      (eff-gen ch gs (generator _ (yield (* 2 (yield 10))))
        (lets
          (right v0) = (next-try gs)
          (send gs (+ 1 v0))
          )))
    (right 22)
    ))

(module+ test
  (check-equal?
    (eff-either-choice ch
      (eff-gen ch gs (generator _ (yield (* 2 (yield 10))))
        (lets
          v0 = (next gs)
          v1 = (send gs (+ 1 v0))
          (left v2) = (send-try gs (* 5 v1))
          (list 'normally-unreached v2))))
    (right (list 'normally-unreached (* 22 5)))
    ))
