#lang racket/base
(provide
  get
  gets
  modify
  put
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
  (require rackunit)
  (require racket/function)
  )

(record state run)
(define (state-eval st s) (car ((state-run st) s)))
(define (state-exec st s) (cdr ((state-run st) s)))

(define (state-pure v) (state (lambda (s) (cons v s))))
(define/destruct (state-bind (state run) next)
  (state
    (lambda (s)
      (with-monad state-monad
        (match-let* (((cons v s) (run s))
                     ((state run) (next v)))
          (run s))))))
(define state-monad (monad state-pure state-bind))

(define get (state (lambda (s) (cons s s))))
(define (put v) (state (lambda (s) (cons (void) v))))
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
                  (modify (curry * val)))))
      (state-exec comp 5))
    (* 5 (+ 5 1))
    ))
