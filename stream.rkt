#lang racket/base
(provide
  stream-monad
  )

(require
  "match.rkt"
  "monad.rkt"
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




