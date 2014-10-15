#lang racket/base
(provide
  get
  gets
  modify
  put
  state-t-run
  state-t-eval
  state-t-exec
  state-monad-t
  state-run
  state-eval
  state-exec
  state-monad
  )

(require
  "monad.rkt"
  "match.rkt"
  "record.rkt"
  racket/match
  )

(module+ test
  (require
    racket/function
    rackunit
    ))

(record state-t run)
(define ((state-t-eval m) st s)
  (begin/with-monad m
    (cons v s) <- ((state-t-run st) s)
    (pure v)))
(define ((state-t-exec m) st s)
  (begin/with-monad m
    (cons v s) <- ((state-t-run st) s)
    (pure s)))

(define (state-t-pure v) (lift (lambda () (pure v))))
(define (state-t-bind m)
  (lambda/destruct ((state-t run) next)
    (state-t
      (lambda (s)
        (begin/with-monad m
          sm = (state-monad-t m)
          (cons v s) <- (with-monad sm (run s))
          (with-monad sm ((state-t-run (next v)) s)))))))
(define ((state-t-lift m) mc)
  (state-t (lambda (s)
    (begin/with-monad m
      v <- (mc)
      (pure (cons v s))))))
(define (state-monad-t m)
  (monad-t state-t-pure (state-t-bind m) (state-t-lift m)))
(define state-monad (state-monad-t ident-monad))
(define (state-run st) (compose1 ident-x (state-t-run st)))
(define (state-eval st s) (ident-x ((state-t-eval ident-monad) st s)))
(define (state-exec st s) (ident-x ((state-t-exec ident-monad) st s)))

(define get (state-t (lambda (s) ((state-t-run (state-t-pure s)) s))))
(define (put v) (state-t (lambda (s) ((state-t-run (state-t-pure (void))) v))))
(define (gets f)
  (begin/monad
    val <- get
    (pure (f val))))
(define (modify f)
  (begin/monad
    val <- get
    (put (f val))))

(module+ test
  (check-equal?
    (let ((comp (begin/with-monad state-monad
                  val <- (gets (curry + 1))
                  (pure val))))
     (state-eval comp 5))
    6
    ))

(module+ test
  (check-equal?
    (let ((comp (begin/with-monad state-monad
                  val <- (gets (curry + 1))
                  (modify (curry * val)))))
     (state-exec comp 5))
    (* 5 (+ 5 1))
    ))
