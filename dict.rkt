#lang racket/base
(provide
  dict-empty
  dict-add
  dict-get
  )

(require
  "maybe.rkt"
  racket/dict
  )

(define dict-empty (hash))
(define dict-add dict-set)
(define (dict-get dct key)
  (if (dict-has-key? dct key) (just (dict-ref dct key)) (nothing)))
