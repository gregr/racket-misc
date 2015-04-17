#lang racket/base
(provide
  dict-add
  dict-empty
  dict-get
  dict-subtract
  dict-subtract1
  )

(require
  "maybe.rkt"
  racket/dict
  )

(module+ test
  (require rackunit))

(define dict-empty (hash))
(define dict-add dict-set)
(define (dict-get dct key)
  (if (dict-has-key? dct key) (just (dict-ref dct key)) (nothing)))

(define (dict-subtract1 d0 d1)
  (for/fold ((d0 d0))
            ((key (in-dict-keys d1)))
    (dict-remove d0 key)))
(define (dict-subtract d0 . ds)
  (foldl (lambda (dn d0) (dict-subtract1 d0 dn)) d0 ds))

(module+ test
  (check-equal?
    (dict-subtract (hash 'a 1 'b 2 'c 3 'd 4 'e 5 'f 6)
                   (hash 'b 7 'd 4) (hash 'b 4 'e 3))
    (hash 'a 1 'c 3 'f 6)))
