#lang racket/base
(provide
  list-set
  list-has-key?
  list-ref-key
  list-set-key
  list-init
  list-inits
  list-path
  iterate
  )

(require
  "match.rkt"
  racket/function
  racket/list
  racket/match
  )

(module+ test
  (require rackunit))

(define (list-set xs idx val)
  (let-values (((start end) (split-at xs idx)))
              (append start (cons val (cdr end)))))

(define (list-has-key? _ key) (or (eq? key 'first) (eq? key 'rest)))
(define (list-ref-key-failure-result key)
  (error (format "list-ref-key: no value found for key\n  key: ~v" key)))
(define (list-ref-key xs key (failure-result list-ref-key-failure-result))
  (match key
    ('first (first xs))
    ('rest (rest xs))
    (_ (if (procedure? failure-result) (failure-result key) failure-result))))
(define/destruct (list-set-key (cons x xs) key val)
  (match key
    ('first (cons val xs))
    ('rest (cons x val))))

(define (list-init lst) (reverse (cdr (reverse lst))))
(define (list-inits lst) (reverse (iterate list-init lst (length lst))))

(define (list-path index . path) (append (make-list index 'rest) path))

(module+ test
  (check-equal? (list-inits '(a b c d))
                '(() (a) (a b) (a b c) (a b c d))))

(define (iterate proc seed count)
  (if (<= count 0) (list seed)
    (cons seed (iterate proc (proc seed) (- count 1)))))

(define (zip xss) (apply (curry map list) xss))
(define (zip* . xss) (zip xss))

(module+ test
  (check-equal?
    (zip* '(1 2) '(3 4) '(a b))
    '((1 3 a) (2 4 b))))
