#lang racket/base
(provide
  fetch
  fetch-try
  with-stream
  fetch-from
  fetch-from-try
  with-streams
  )

(require
  "state.rkt"
  "maybe.rkt"
  "monad.rkt"
  racket/dict
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

(define (fetch-from-try name)
  (begin/monad
    streams <- get
    stream = (dict-ref streams name)
    (if (stream-empty? stream)
      (pure (nothing))
      (begin/monad
        first = (stream-first stream)
        rest = (stream-rest stream)
        streams = (dict-set streams name rest)
        _ <- (put streams)
        (pure (just first))))))
(define (fetch-from name)
  (begin/monad
    maybe-val <- (fetch-from-try name)
    (match maybe-val
      ((nothing) (error (format "nothing to fetch from stream '~a'" name)))
      ((just val) (pure val)))))

(define-syntax with-streams
  (syntax-rules ()
    ((_ ((name stream) ...) body ...)
     (let ((streams (make-immutable-hash (list (cons 'name stream) ...))))
       (state-eval (begin/with-monad state-monad body ...) streams)))))

(module+ test
  (check-equal?
    (with-streams ((one (gen->stream (generator _ (yield 1) (yield 2))))
                   (two (gen->stream (generator _ (yield 3) (yield 4)))))
      v0 <- (fetch-from 'one)
      v1 <- (fetch-from 'two)
      (pure (list v0 v1)))
    (list 1 3)
    ))

(module+ test
  (check-equal?
    (with-streams ((one (gen->stream (generator _ (yield 1) (yield 2))))
                   (two (gen->stream (generator _ (yield 3) (yield 4)))))
      (just v0) <- (fetch-from-try 'one)
      v1 <- (fetch-from 'two)
      v2 <- (fetch-from 'two)
      (nothing) <- (fetch-from-try 'two)
      (pure (list v0 v1 v2)))
    (list 1 3 4)
    ))
