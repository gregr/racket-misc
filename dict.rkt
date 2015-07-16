#lang racket/base
(provide
  default-hash
  default-hash-ref
  default-hash-set
  dict-add
  dict-diff
  dict-empty
  dict-get
  dict-join
  dict-subtract
  dict-subtract1
  dict-update-if-has
  hash-add
  hash-empty
  hash-get
  hash-update-if-has
  )

(require
  "match.rkt"
  "maybe.rkt"
  racket/dict
  racket/match
  )

(module+ test
  (require
    rackunit
    racket/function
    ))

(define hash-empty (hash))
(define hash-add hash-set)
(define (hash-get hsh key)
  (define found? #t)
  (let ((result (hash-ref hsh key (lambda () (set! found? #f)))))
    (if found? (just result) (nothing))))
(define (hash-update-if-has hsh key update)
  (if (hash-has-key? hsh key) (hash-update hsh key update) hsh))

(define dict-empty hash-empty)
(define dict-add dict-set)
(define (dict-get dct key)
  (define found? #t)
  (let ((result (dict-ref dct key (lambda () (set! found? #f)))))
    (if found? (just result) (nothing))))
(define (dict-update-if-has dct key update)
  (if (dict-has-key? dct key) (dict-update dct key update) dct))

(define (dict-join d0 d1)
  (for/fold ((d0 d0))
            (((key val) (in-dict d1)))
            (dict-set d0 key val)))

(module+ test
  (check-equal?
    (dict-join (default-hash identity (hash 'a 1 'b 2 'd 4))
               (hash 'c 3 'b 5))
    (default-hash identity (hash 'a 1 'b 5 'c 3 'd 4))))

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

(struct default-hash (new hsh) #:transparent
  #:methods gen:dict
  ((define (dict-ref . args) (apply default-hash-ref args))
   (define (dict-set . args) (apply default-hash-set args))
   (define (dict-iterate-first dhsh)
     (hash-iterate-first (default-hash-hsh dhsh)))
   (define (dict-iterate-next dhsh pos)
     (hash-iterate-next (default-hash-hsh dhsh) pos))
   (define (dict-iterate-key dhsh pos)
     (hash-iterate-key (default-hash-hsh dhsh) pos))
   (define (dict-iterate-value dhsh pos)
     (hash-iterate-value (default-hash-hsh dhsh) pos))
   (define (dict-count dhsh) (hash-count (default-hash-hsh dhsh)))))

(define (default-hash-ref dhsh key . args)
  (match-let (((default-hash new hsh) dhsh))
    (hash-ref hsh key (match args
                        ('() (lambda () (new key)))
                        ((list default) default)))))

(define (default-hash-set dhsh key val)
  (match-let (((default-hash new hsh) dhsh))
    (default-hash new (hash-set hsh key val))))

(module+ test
  (check-equal? (dict? (default-hash (const 3) (hash))) #t)
  (check-equal?
    (default-hash-hsh
      (dict-set (default-hash (const '(a b c)) (hash)) 5
                (dict-ref (default-hash (const '(a b c)) (hash)) 5)))
    (hash 5 '(a b c)))
  )
