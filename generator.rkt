#lang racket/base
; generalized yield-run as described in:
; http://www.cs.indiana.edu/~sabry/papers/yield.pdf
(provide
  in-gen
  run-at
  run
  run*
  yield-at
  yield
  generator
  generator*
  gen-co-fold
  gen-co-for
  gen-fold
  gen-for/fold
  gen->list
  gen->stream
  )

(require
  "either.rkt"
  "match.rkt"
  "record.rkt"
  racket/control
  racket/function
  racket/match
  racket/stream
  )

(module+ test
  (require rackunit))

(records gen-response
  (gen-result r)
  (gen-susp v k))

(define-syntax run-at
  (syntax-rules ()
    ((_ tag body ...) (reset-at tag (gen-result (begin body ...))))))
(define-syntax run
  (syntax-rules ()
    ((_ body ...) (run-at (default-continuation-prompt-tag) body ...))))
(define-syntax run*
  (syntax-rules ()
    ((_ yield body ...)
     (let* ((tag (make-continuation-prompt-tag))
            (yield (curry yield-at tag)))
       (run-at tag body ...)))))

(define (yield-at tag v) (shift-at tag k (gen-susp v (lambda (i) (k i)))))
(define (yield v) (yield-at (default-continuation-prompt-tag) v))

(define-syntax generator
  (syntax-rules ()
    ((_ args body ...) (lambda args (run body ...)))))
(define-syntax generator*
  (syntax-rules ()
    ((_ yield args body ...)
     (let* ((tag (make-continuation-prompt-tag))
            (yield (curry yield-at tag)))
       (lambda args (run-at tag body ...))))))

(module+ test
  (check-equal?
    (match-let* ((gen (generator _ (yield 3) (yield 5)))
                 ((gen-susp v0 gen) (gen (void)))
                 ((gen-susp v1 gen) (gen (void)))
                 ((gen-result r) (gen (void))))
      (list v0 v1 r))
    (list 3 5 (void))
    ))

(define (gen-fold on-susp on-result input acc gen)
  (match (gen input)
    ((gen-result r) (on-result r acc))
    ((gen-susp v k)
     (match-let (((list input acc) (on-susp v acc)))
       (gen-fold on-susp on-result input acc k)))))

(define-syntax gen-for/fold
  (syntax-rules ()
    ((_ (acc acc-init) (output gen-expr) on-susp result on-result)
     (gen-fold (lambda/destruct (output acc) on-susp)
               (lambda/destruct (result acc) on-result)
               (void) acc-init (lambda (_) gen-expr)))))

(define (gen-co-fold seed gens)
  (if (= 0 (length gens)) seed
    (let loop ((input seed) (finished '()) (pending gens))
      (match pending
        ('() (loop input '() (reverse finished)))
        ((cons gen gens)
         (match (gen input)
           ((gen-result r) r)
           ((gen-susp v k) (loop v (cons k finished) gens))))))))
(define (gen-co-fold* seed . gens) (gen-co-fold seed gens))

(define-syntax gen-co-for
  (syntax-rules ()
    ((_ gen-expr gens ...)
     (gen-co-fold* (void) (lambda (_) gen-expr) gens ...))))

(module+ test
  (check-equal?
    (gen-co-for
      (run (yield (+ 1 (yield 10))))
      (generator (input) (yield (+ 3 (yield (+ input 2))))))
    (+ 10 1 3 2)
    ))

(module+ test
  (check-equal?
    (gen-co-for
      (run (let* ((i0 (yield '(a)))
                  (i1 (yield (append i0 '(c))))
                  (i2 (yield (append i1 '(e)))))
             i2))
      (generator (i0)
        (let* ((i1 (yield (append i0 '(b))))
               (i2 (yield (append i1 '(d))))
               (i3 (yield (append i2 '(f))))
               (i4 (yield (append i2 '(unreached)))))
          i4)))
    '(a b c d e f)
    ))

(define (gen->list gen)
  (gen-for/fold (vs '()) (v (gen (void)))
    (list (void) (cons v vs))
    _ (reverse vs)))

(module+ test
  (check-equal?
    (gen->list (generator _ (yield 3) (yield 5)))
    (list 3 5)
    ))

(module+ test
  (check-equal?
    (gen->list (generator* yield0 _
                (yield0 1)
                (gen->list (generator* yield1 _
                            (yield1 'ignored)
                            (yield0 3)))
                (yield0 4)))
    (list 1 3 4)
    ))

(struct gen-stream ((state #:mutable)) #:transparent
  #:methods gen:stream
  ((define (state-next gs)
     (match (gen-stream-state gs)
       ((left gen)
        (let ((next (gen (void))))
          (set-gen-stream-state! gs (right next))
          next))
       ((right next) next)))
   (define (stream-empty? gs)
     (match (state-next gs)
       ((gen-result _) #t)
       ((gen-susp _ _) #f)))
   (define (stream-first gs)
     (match (state-next gs)
       ((gen-susp v k) v)
       ((gen-result _) (void))))
   (define (stream-rest gs)
     (match (state-next gs)
       ((gen-susp v k) (gen-stream (left k)))
       ((gen-result _) (void))))
   ))
(define (gen->stream gen) (gen-stream (left gen)))
(define in-gen gen->stream)

(module+ test
  (check-equal?
    (let* ((stream (gen->stream (generator _ (yield 3) (yield 5))))
           (v0 (stream-first stream))
           (stream (stream-rest stream))
           (v1 (stream-first stream)))
      (list v0 v1))
    (list 3 5)
    ))

(module+ test
  (check-equal?
    (for/list ((v (in-gen (generator _
                            (yield 10) (yield 11) (yield 12)))))
      v)
    (list 10 11 12)
    ))
