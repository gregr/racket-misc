#lang racket/base
(provide
  cross
  cross*
  zip
  zip*
  zip-with
  list->index-hash
  index-hash->list
  list-set
  list-has-key?
  list-ref-key
  list-set-key
  list-init+last
  list-init
  list-inits
  list-path
  iterate
  replicate
  sum
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

(define (list-init+last lst)
  (let ((rlist (reverse lst)))
    (list (reverse (cdr rlist)) (car rlist))))
(define (list-init lst) (car (list-init+last lst)))
(define (list-inits lst) (reverse (iterate list-init lst (length lst))))

(define (list-path index . path) (append (make-list index 'rest) path))

(module+ test
  (check-equal? (list-inits '(a b c d))
                '(() (a) (a b) (a b c) (a b c d))))

(define (iterate proc seed count)
  (if (<= count 0) (list seed)
    (cons seed (iterate proc (proc seed) (- count 1)))))

(define (sum xs) (apply + xs))

(module+ test
  (check-equal? (sum (list 1 2 3)) 6))

(define (replicate k v) (build-list k (lambda _ v)))

(module+ test
  (check-equal? (replicate 4 'x) '(x x x x)))

(define (zip-with f xss) (apply (curry map f) xss))
(define (zip xss) (zip-with list xss))
(define (zip* . xss) (zip xss))

(module+ test
  (check-equal?
    (zip* '(1 2) '(3 4) '(a b))
    '((1 3 a) (2 4 b))))

(define (cross xss)
  (match/cata xss
    ('() '(()))
    ((cons xs (cata xss))
     (for*/list ((x xs)
                 (cur xss))
      (cons x cur)))))
(define (cross* . xss) (cross xss))

(module+ test
  (check-equal?
    (cross* '(1 2) '(3 4) '(a b))
    '((1 3 a) (1 3 b) (1 4 a) (1 4 b) (2 3 a) (2 3 b) (2 4 a) (2 4 b))
    ))

(define (list->index-hash xs)
  (make-immutable-hash (map cons (range (length xs)) xs)))

(define (index-hash->list hx)
  (let loop ((result '()) (remaining (hash-count hx)))
    (if (= 0 remaining) result
      (let* ((idx (- remaining 1)) (value (hash-ref hx idx)))
        (loop (cons value result) idx)))))

(module+ test
  (check-equal?
    (list->index-hash '(a b c))
    (hash 0 'a 1 'b 2 'c)
    )
  (check-equal?
    (index-hash->list (list->index-hash (list 'a 'b 'c)))
    '(a b c)
    )
  )
