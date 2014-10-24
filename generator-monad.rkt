#lang racket/base
(provide
  gen-eval
  gen-catch
  gen-handle
  gen-monad
  gen-state-eval
  gen-state-monad
  gen-state-run
  next
  next-try
  send
  send-try
  with-gen
  )

(require
  "either.rkt"
  "generator.rkt"
  "match.rkt"
  "monad.rkt"
  "state-monad.rkt"
  racket/function
  racket/match
  )

(module+ test
  (require
    rackunit
    ))

(define/destruct (gen-pure (cons v k)) (gen-susp v k))
(define (gen-bind gresp next)
  (match gresp
    ((gen-result r) gresp)
    ((gen-susp v k) (next (cons v k)))))
(define gen-monad (monad gen-pure gen-bind))
(define (gen-eval gresp)
  (match gresp
    ((gen-result r) r)
    ((gen-susp v k) v)))
(define (gen-handle f gresp)
  (match gresp
    ((gen-result r) (gen-result (f r)))
    ((gen-susp v k) gresp)))
(define (gen-catch on-susp on-result gresp)
  (match gresp
    ((gen-result r) (gen-susp (on-result r) (const gresp)))
    ((gen-susp v k) (gen-susp (on-susp v) k))))

(module+ test
  (check-equal?
    (gen-susp-v
      (begin/with-monad gen-monad
        g0 = (generator _ (yield (yield (* 2 (yield 10)))))
        (cons v0 g0) <- (g0)
        (cons v1 g1-0) <- (g0 (+ 1 v0))
        (cons v2 g1-1) <- (g0 (+ 2 v1))
        (cons v3 g2-0) <- (g1-0 (+ 3 v2))
        (cons v4 g2-1) <- (g1-1 (+ 4 v3))
        (pure (cons (list v0 v1 v2 v3 v4) g2-1))))
    (list 10 22 48 51 55)
    ))

(module+ test
  (check-equal?
    (gen-result-r
      (begin/with-monad gen-monad
        g = (generator _ (yield 1) (yield 2))
        (cons v0 g) <- (g)
        (cons v1 g) <- (g)
        (cons v2 g) <- (gen-handle (const (list v0 v1)) (g))
        (pure (cons 'unreached g))))
    (list 1 2)
    ))

(module+ test
  (check-equal?
    (gen-susp-v
      (begin/with-monad gen-monad
        g = (generator _ (yield 1) (yield 2) 3)
        (cons v0 g) <- (g)
        (cons v1 g) <- (g)
        (cons v2 g) <- (gen-catch right left (g))
        (pure (cons (list v0 v1 v2) g))))
    (list 1 2 (left 3))
    ))

(define gen-state-monad (state-monad-t either-monad))
(define ((gen-state-run gst) gen)
  (match ((state-t-run gst) gen)
    ((left  r)          (gen-result r))
    ((right (cons v k)) (gen-susp v k))))
(define (gen-state-eval gst gen)
  (match ((gen-state-run gst) gen)
    ((gen-result r) r)
    ((gen-susp v k) v)))
(define (gen-response->either gresp)
  (match gresp
    ((gen-result r) (left r))
    ((gen-susp v k) (right v))))

(define (send-try input)
  (begin/with-monad gen-state-monad
    gen <- get
    gresp = (gen input)
    either = (gen-response->either gresp)
    _ <- (put (if (right? either)
                (gen-susp-k gresp)
                (thunk gresp)))
    (pure either)))
(define (send input)
  (begin/with-monad gen-state-monad
    either <- (send-try input)
    (lift (thunk either))))

(define next (send (void)))
(define next-try (send-try (void)))

(define-syntax with-gen
  (syntax-rules ()
    ((_ gen body ...)
     (gen-state-eval (begin/with-monad gen-state-monad body ...) gen))))

(module+ test
  (check-equal?
    (with-gen (generator _ (yield (* 2 (yield 10))))
      v0 <- next
      v1 <- (send (+ 1 v0))
      (pure v1))
    22
    ))

(module+ test
  (check-equal?
    (with-gen (generator _ (yield (* 2 (yield 10))))
      v0 <- next
      v1 <- (send (+ 1 v0))
      v2 <- (send (* 5 v1))
      (pure 'unreached))
    (* 22 5)
    ))

(module+ test
  (check-equal?
    (with-gen (generator _ (yield (* 2 (yield 10))))
      (right v0) <- next-try
      v1 <- (send (+ 1 v0))
      (pure v1))
    22
    ))

(module+ test
  (check-equal?
    (with-gen (generator _ (yield (* 2 (yield 10))))
      v0 <- next
      v1 <- (send (+ 1 v0))
      (left v2) <- (send-try (* 5 v1))
      (pure (list 'normally-unreached v2)))
    (list 'normally-unreached (* 22 5))
    ))
