#lang racket/base
(module+ test
  (require
    "../either.rkt"
    "../monad.rkt"
    racket/list
    rackunit
    ))

(module+ test
  (let ()
    (define (good? name x) (if (eq? name 'bad) (left x) (right x)))
    (check-equal?
      (for/fold/monad either-monad
                      acc '()
                      (((list name x) '((a 0) (b 1) (c 2))) (y (range 5)))
                      x <- (good? name x)
                      (pure (list* (list name x y) acc)))
      (right '((c 2 2) (b 1 1) (a 0 0))))
    (check-equal?
      (for/fold/monad either-monad
                      acc '()
                      (((list name x) '((a 0) (b 1) (bad 5) (c 2))) (y (range 5)))
                      x <- (good? name x)
                      (pure (list* (list name x y) acc)))
      (left 5))
    (check-equal?
      (for/list/monad either-monad
                      (((list name x) '((a 0) (b 1) (c 2))) (y (range 5)))
                      x <- (good? name x)
                      (pure (list name x y)))
      (right '((a 0 0) (b 1 1) (c 2 2))))
    (check-equal?
      (for/list/monad either-monad
                      (((list name x) '((a 0) (b 1) (bad 5) (c 2))) (y (range 5)))
                      x <- (good? name x)
                      (pure (list name x y)))
      (left 5))
    ))
