#lang racket/base
(provide
  apply-map
  apply-map*
  map*
  cross
  cross*
  zip
  zip-default
  zip*
  zip-with
  zip-with-default
  list-get
  list-index
  list-index-equal
  list->index-hash
  index-hash->list
  list-remove
  list-set
  list-has-key?
  list-ref-default
  list-ref-key
  list-set-key
  list-init+last
  list-init
  list-inits
  list-path
  iterate
  sum
  )

(require
  "match.rkt"
  "maybe.rkt"
  racket/function
  racket/list
  racket/match
  )

(module+ test
  (require rackunit))

(define (list-index xs matches?)
  (let loop ((idx 0) (xs xs))
    (match xs
      ('() -1)
      ((cons x xs) (if (matches? x) idx (loop (+ 1 idx) xs))))))
(define (list-index-equal xs element) (list-index xs (curry equal? element)))

(module+ test
  (check-equal?
    (list-index-equal '(a b c) 'b)
    1)
  (check-equal?
    (list-index-equal '(a b c) 'd)
    -1)
  )

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

(define (map* f . xs) (map f xs))

(module+ test
  (check-equal?
    (map* list 1 2 3)
    '((1) (2) (3))
    ))

(define (apply-map f0 f1 xs) (apply f0 (map f1 xs)))
(define (apply-map* f0 f1 . xs) (apply-map f0 f1 xs))

(module+ test
  (check-equal?
    (apply-map* cons (curry * 3) 3 5)
    (cons 9 15)
    ))

(define (zip-with-default default f xss)
  (if (empty? xss) default (apply map f xss)))
(define (zip-with f xss) (zip-with-default '() f xss))
(define (zip-default default xss) (zip-with-default default list xss))
(define (zip xss) (zip-default '() xss))
(define (zip* . xss) (zip xss))

(module+ test
  (check-equal?
    (zip* '(1 2) '(3 4) '(a b))
    '((1 3 a) (2 4 b)))
  (check-equal?
    (zip-default '(() ()) '(()))
    '())
  (check-equal?
    (zip-default '(() ()) '())
    '(() ())))

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

(define (list-get xs idx)
  (if (< idx (length xs)) (just (list-ref xs idx)) (nothing)))

(module+ test
  (check-equal?
    (list-get '(a b c) 3)
    (nothing))
  (check-equal?
    (list-get '(a b c) 2)
    (just 'c)))

(define (list-ref-default xs idx default)
  (maybe-from default (list-get xs idx)))

(module+ test
  (check-equal?
    (list-ref-default '(a b c) 3 'd)
    'd)
  (check-equal?
    (list-ref-default '(a b c) 2 'd)
    'c))

(define (list-remove xs idx)
  (if (< idx (length xs))
    (let-values (((start end) (split-at xs idx)))
      (append start (rest end)))
    xs))

(module+ test
  (check-equal?
    (list-remove '(a b c d) 2)
    '(a b d))
  (check-equal?
    (list-remove '(a b c d) 4)
    '(a b c d)))
