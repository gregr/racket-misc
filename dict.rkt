#lang racket/base
(provide
  dict-add
  dict-diff
  dict-empty
  dict-get
  dict-subtract
  dict-subtract1
  )

(require
  "match.rkt"
  "maybe.rkt"
  racket/dict
  )

(module+ test
  (require rackunit))

(define dict-empty (hash))
(define dict-add dict-set)
(define (dict-get dct key)
  (define found? #t)
  (let ((result (dict-ref dct key (lambda () (set! found? #f)))))
    (if found? (just result) (nothing))))

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

(define (dict-diff d0 d1)
  (for/list/match (((cons key val) (dict->list d0))
                   #:unless (equal? (just val) (dict-get d1 key)))
                  (cons key val)))

(module+ test
  (check-equal?
    (make-immutable-hash
      (dict-diff (hash 'b 5 'c 3 'a 1 'e 11 'f 12)
                 (hash 'a 1 'b 2 'c 3 'd 4)))
    (hash 'b 5 'e 11 'f 12)))
