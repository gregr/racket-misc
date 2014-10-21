#lang racket/base
(provide
  stream-monad
  stream-state-monad
  stream-state-run
  peek
  peek-try
  pop
  pop-try
  push
  with-stream
  )

(require
  "match.rkt"
  "maybe.rkt"
  "monad.rkt"
  "state-monad.rkt"
  racket/function
  racket/match
  racket/stream
  )

(module+ test
  (require
    rackunit
    ))

(define/destruct (stream-pure (cons f r)) (stream-cons f r))
(define (stream-bind stream next)
  (if (stream-empty? stream)
    stream
    (next (cons (stream-first stream) (stream-rest stream)))))
(define stream-monad (monad stream-pure stream-bind))

(module+ test
  (check-equal?
    (stream-first
      (begin/with-monad stream-monad
        s0 = (list 1 2 3)
        (cons v0 s1) <- s0
        (cons v1 s2) <- s1
        (cons v2 s3) <- s2
        (pure (cons (list v0 v1 v2) s3))))
    (list 1 2 3)
    ))

(module+ test
  (check-equal?
    (begin/with-monad stream-monad
      s0 = (list 1 2 3)
      (cons v0 s1) <- s0
      (cons v1 s2) <- s1
      (cons v2 s3) <- s2
      (cons v3 s4) <- s3
      (pure (cons 'unreached s4)))
    (list)
    ))

(define stream-state-monad (state-monad-t maybe-monad))
(define stream-state-run state-t-run)
(define (stream->maybe stream)
  (if (stream-empty? stream) (nothing) (just (stream-first stream))))

(define peek-try
  (begin/with-monad stream-state-monad
    stream <- get
    (pure (stream->maybe stream))))
(define peek
  (begin/with-monad stream-state-monad
    maybe <- peek-try
    (lift (thunk maybe))))
(define pop-try
  (begin/with-monad stream-state-monad
    stream <- get
    maybe = (stream->maybe stream)
    _ <- (put (if (stream-empty? stream) stream (stream-rest stream)))
    (pure maybe)))
(define pop
  (begin/with-monad stream-state-monad
    maybe <- pop-try
    (lift (thunk maybe))))
(define (push val)
  (begin/with-monad stream-state-monad
    stream <- get
    (put (stream-cons val stream))))

(define-syntax with-stream
  (syntax-rules ()
    ((_ stream body ...)
     ((stream-state-run (begin/with-monad stream-state-monad body ...)) stream))))

(module+ test
  (check-equal?
    (with-stream (list 1 2)
      v0 <- pop
      v1 <- pop
      (pure (list v1 v0)))
    (just (cons (list 2 1) '()))
    ))

(module+ test
  (check-equal?
    (with-stream (list 1 2)
      (just v0) <- pop-try
      v1 <- pop
      (nothing) <- pop-try
      (pure (list v1 v0)))
    (just (cons (list 2 1) '()))
    ))

(module+ test
  (check-equal?
    (match-let (((just (cons result stream))
        (with-stream (list 1 2)
          v0 <- peek
          v1 <- pop
          v2 <- peek
          v3 <- pop
          (nothing) <- peek-try
          _ <- (push 5)
          v4 <- pop
          (pure (list v0 v1 v2 v3 v4)))))
      (just (cons result (stream->list stream))))
    (just (cons (list 1 1 2 2 5) '()))
    ))
