#lang racket/base
(provide
  fetch
  fetch-try
  with-stream
  )

(require
  "state.rkt"
  "maybe.rkt"
  "monad.rkt"
  racket/match
  racket/stream
  )

(module+ test
  (require
    "generator.rkt"
    rackunit
    ))

(define fetch-try
  (begin/with-monad state-monad
    stream <- get
    (if (stream-empty? stream)
      (pure (nothing))
      (begin/monad
        first = (stream-first stream)
        rest = (stream-rest stream)
        _ <- (put rest)
        (pure (just first))))))
(define fetch
  (begin/with-monad state-monad
    maybe-val <- fetch-try
    (match maybe-val
      ((nothing) (error "nothing to fetch"))
      ((just val) (pure val)))))

(define-syntax with-stream
  (syntax-rules ()
    ((_ stream body ...)
     (state-eval (begin/with-monad state-monad body ...) stream))))

(module+ test
  (check-equal?
    (with-stream (gen->stream (generator _ (yield 1) (yield 2)))
      v0 <- fetch
      v1 <- fetch
      (pure (list v0 v1)))
    (list 1 2)
    ))

(module+ test
  (check-equal?
    (with-stream (gen->stream (generator _ (yield 1) (yield 2)))
      (just v0) <- fetch-try
      v1 <- fetch
      (nothing) <- fetch-try
      (pure (list v0 v1)))
    (list 1 2)
    ))
