#lang racket/base
(provide
  get
  put
  modify
  state-ref
  state
  eff-state
  )

(require
  "eff.rkt"
  )

(module+ test
  (require
    "sugar.rkt"
    racket/function
    rackunit
    ))

(define (state-ref) (effect get put))

(define (get sr) (@! sr get))
(define (put sr v) (@! sr put v))
(define (modify sr f) (put sr (f (get sr))))

(define (state sr s0)
  (handler
    (sr (get k)   (lambda (s) ((k s) s)))
    (sr (put v k) (lambda (s) ((k (void)) v)))
    (return v     (lambda (s) v))
    (finally f    (f s0))))

(define-syntax eff-state
  (syntax-rules ()
    ((_ ref-name init-state body ...)
     (let ((ref-name (state-ref)))
       (eff-handle (state ref-name init-state) body ...)))))

(module+ test
  (check-equal?
    (eff-state sr 6
      (lets
        x = (get sr)
        _ = (put sr (+ x 1))
        _ = (modify sr (curry * 2))
        (get sr)))
    14
    ))
