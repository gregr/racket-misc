#lang racket/base
; generalized yield-run as described in:
; http://www.cs.indiana.edu/~sabry/papers/yield.pdf
(provide
  (struct-out gen-result)
  (struct-out gen-susp)
  const-gen
  either-gen
  fn->gen
  gen->list
  gen->stream
  gen-coloop
  gen-compose
  gen-compose*
  gen-delegate
  gen-fold
  gen-loop
  gen-map
  gen-response?
  generator
  generator*
  identity-gen
  in-gen
  maybe-gen
  sequence->gen
  run
  run-at
  run*
  yield
  yield-at
  )

(require
  "either.rkt"
  "match.rkt"
  "maybe.rkt"
  "record.rkt"
  racket/control
  racket/function
  racket/match
  racket/stream
  )

(module+ test
  (require
    racket/list
    rackunit
    ))

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

(define (yield-at tag v)
  (shift-at tag k (gen-susp v (lambda ((i (void))) (k i)))))
(define (yield v) (yield-at (default-continuation-prompt-tag) v))

(define-syntax generator
  (syntax-rules ()
    ((_ args body ...) (lambda args (run body ...)))))
(define-syntax generator*
  (syntax-rules ()
    ((_ yield args body ...) (lambda args (run* yield body ...)))))

(module+ test
  (check-equal?
    (match-let* ((gen (generator _ (yield 3) (yield 5)))
                 ((gen-susp v0 gen) (gen (void)))
                 ((gen-susp v1 gen) (gen (void)))
                 ((gen-result r) (gen (void))))
      (list v0 v1 r))
    (list 3 5 (void))
    ))

(define (gen-fold f acc gen xs)
  (let loop ((acc acc) (gen gen) (xs xs))
    (match xs
      ('() (gen-susp acc gen))
      ((cons x xs)
       (match (gen x)
         ((gen-result r) (gen-result (list r acc xs)))
         ((gen-susp v k) (loop (f v acc) k xs)))))))

(define (gen-map gen xs)
  (match (gen-fold cons '() gen xs)
    ((gen-result (list r yielded xs))
     (gen-result (list r (reverse yielded) xs)))
    ((gen-susp yielded k) (gen-susp (reverse yielded) k))))

(module+ test
  (check-equal?
    (gen-susp-v
      (gen-map (generator* yield (xa)
                 (yield (+ 4 (yield (+ 3 (yield (+ 2 (yield (+ 1 xa)))))))))
               (list 10 20 30 40)))
    (list 11 22 33 44)))

(module+ test
  (check-equal?
    (gen-map (generator* yield (xa)
               (yield (+ 4 (yield (+ 3 (yield (+ 2 (yield (+ 1 xa)))))))))
             (list 10 20 30 40 50 60))
    (gen-result (list 50 (list 11 22 33 44) (list 60)))))

(records gen-stream-state
  (gen-stream-pending gen)
  (gen-stream-data first rest)
  (gen-stream-empty))
(struct gen-stream ((state #:mutable)) #:transparent
  #:methods gen:stream
  ((define (state-next gs)
     (match (gen-stream-state gs)
       ((gen-stream-pending gen)
        (let ((next (match (gen (void))
                      ((gen-result _) (gen-stream-empty))
                      ((gen-susp v k) (gen-stream-data v (gen->stream k))))))
          (set-gen-stream-state! gs next)
          next))
       (state state)))
   (define (stream-empty? gs) (gen-stream-empty? (state-next gs)))
   (define (stream-first gs) (gen-stream-data-first (state-next gs)))
   (define (stream-rest gs) (gen-stream-data-rest (state-next gs)))
   ))
(define (gen->stream gen) (gen-stream (gen-stream-pending gen)))
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

(module+ test
  (check-equal?
    (let* ((count (box 0))
           (inc-yield (lambda (v)
                        (set-box! count (+ 1 (unbox count)))
                        (yield v)))
           (vs (gen->stream
                 (generator _ (inc-yield 1) (inc-yield 2) (inc-yield 3))))
           (v0 (stream-first vs))
           (vs-extra (stream-rest vs))
           (vs (stream-rest vs))
           (v1 (stream-first vs))
           (v2 (stream-first vs-extra))
           (vs (stream-rest vs))
           (v3 (stream-first vs)))
      (list (list v0 v1 v2 v3) (unbox count)))
    (list '(1 2 2 3) 3)
    ))

(define (sequence->gen stream)
  (generator* yield* (_)
    (for ((val stream)) (yield* val))))

(module+ test
  (check-equal?
    (for/list ((val (gen->stream (sequence->gen (in-range 10 16))))) val)
    (range 10 16)
    ))

(define (gen->list gen) (stream->list (gen->stream gen)))

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

(define ((fn->gen fn) input)
  (gen-susp (fn input) (fn->gen fn)))
(define identity-gen (fn->gen identity))
(define const-gen (compose1 fn->gen const))

(define (gen-compose-resumable resume? inner outer)
  (lambda args
    (match (apply outer args)
      ((gen-result r)
       (gen-result (if resume? (right (gen-susp r inner)) r)))
      ((gen-susp v1 k0)
       (match (inner v1)
         ((gen-result r)
          (gen-result (if resume? (left (gen-susp r k0)) r)))
         ((gen-susp v2 k1)
          (gen-susp v2 (gen-compose-resumable resume? k1 k0))))))))
(define (gen-compose inner outer) (gen-compose-resumable #f inner outer))
(define (gen-compose* gen . gens)
  (foldl (lambda (outer inner) (gen-compose inner outer)) gen gens))

(module+ test
  (check-equal?
    (match-let* ((gen (gen-compose* (fn->gen (curry * 2))
                                    (fn->gen (curry + 3))
                                    (const-gen 1)))
                 ((gen-susp v0 gen) (gen 0))
                 ((gen-susp v1 gen) (gen 1))
                 ((gen-susp v2 gen) (gen 2)))
      (list v0 v1 v2))
    (list 8 8 8)
    ))

(define (gen-loop gen . args)
  (match (apply gen args)
    ((gen-result r) r)
    ((gen-susp v k) (gen-loop k v))))

(module+ test
  (check-equal?
    (gen-loop
      (gen-compose*
        (generator* yield (val)
          (let loop ((val val))
            (if (> val 10) val (loop (yield val)))))
        (fn->gen (curry * 2)))
      1)
    16
    ))

(define (gen-coloop inner outer . args)
  (apply gen-loop (gen-compose-resumable #t inner outer) args))

(module+ test
  (check-equal?
    (gen-susp-v (right-x
      (gen-coloop
        (fn->gen (curry * 2))
        (generator* yield (start)
                    (yield (+ 100 (yield start))))
        4)))
    216
    ))

(define (gen-delegate yield gen input)
  (let loop ((gen gen) (input input))
    (match (gen input)
      ((gen-result r) r)
      ((gen-susp v k) (loop k (yield v))))))

(module+ test
  (check-equal?
    (gen->list
      (generator* yield (_)
        (yield 0)
        (gen-delegate yield (sequence->gen (range 1 4)) (void))
        (yield 4)))
    (list 0 1 2 3 4)
    ))

(define ((either-gen gen) input)
  (define (susp v k) (gen-susp v (either-gen k)))
  (match input
    ((left l) (susp (left l) gen))
    ((right r)
     (match (gen r)
       ((gen-result r) (gen-result r))
       ((gen-susp v k) (susp (right v) k))))))

(define (maybe-gen gen)
  (gen-compose* (fn->gen either->maybe)
                (either-gen gen)
                (fn->gen (curry maybe->either (void)))))

(module+ test
  (check-equal?
    (match-let* ((gen (gen-compose (fn->gen (curry maybe-from 'x))
                                   (maybe-gen identity-gen)))
                 ((gen-susp v0 gen) (gen (just 'a)))
                 ((gen-susp v1 gen) (gen (nothing)))
                 ((gen-susp v2 gen) (gen (just 'b))))
      (list v0 v1 v2))
    '(a x b)
    ))
