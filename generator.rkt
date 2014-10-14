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
  gen-eval
  gen-catch
  gen-handle
  gen-monad
  gen-state-eval
  gen-state-monad
  gen-state-run
  gen-response?
  (struct-out gen-result)
  (struct-out gen-susp)
  generator
  generator*
  gen-fold
  gen-for
  gen-for/fold
  gen-iterate
  gen->list
  gen->stream
  next
  next-try
  send
  send-try
  with-gen
  )

(require
  "either.rkt"
  "match.rkt"
  "monad.rkt"
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

(define (yield-at tag v)
  (shift-at tag k (gen-susp v (lambda ((i (void))) (k i)))))
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

(define (gen-iterate on-susp gen (seed (void)))
  (gen-fold (lambda (v _) (list (on-susp v) (void)))
            (lambda (r _) r)
            seed (void) gen))

(define-syntax gen-for
  (syntax-rules ()
    ((_ (output gen-expr) body ...)
     (gen-iterate (lambda/destruct (output) body ...) (lambda (_) gen-expr)))))

(module+ test
  (check-equal?
    (gen-for
      (v (run (yield (+ 3 (yield (+ 2 (yield 1)))))))
      (* v 10))
    1230
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

(define (gen-pure v) (gen-susp v (const (gen-result (void)))))
(define (gen-bind gresp next)
  (match gresp
    ((gen-result r) gresp)
    ((gen-susp v k) (next (cons v k)))))
(define gen-monad (monad gen-pure gen-bind))
(define (gen-eval gresp)
  (match gresp
    ((gen-result r) r)
    ((gen-susp v k) v)))
(define (gen-handle f gresp)
  (match gresp
    ((gen-result r) (gen-result (f r)))
    ((gen-susp v k) gresp)))
(define (gen-catch on-susp on-result gresp)
  (match gresp
    ((gen-result r) (gen-susp (on-result r) (const gresp)))
    ((gen-susp v k) (gen-susp (on-susp v) k))))

(module+ test
  (check-equal?
    (gen-susp-v
      (begin/with-monad gen-monad
        g0 = (generator _ (yield (yield (* 2 (yield 10)))))
        (cons v0 g0) <- (g0)
        (cons v1 g1-0) <- (g0 (+ 1 v0))
        (cons v2 g1-1) <- (g0 (+ 2 v1))
        (cons v3 g2-0) <- (g1-0 (+ 3 v2))
        (cons v4 g2-1) <- (g1-1 (+ 4 v3))
        (pure (list v0 v1 v2 v3 v4))))
    (list 10 22 48 51 55)
    ))

(module+ test
  (check-equal?
    (gen-result-r
      (begin/with-monad gen-monad
        g = (generator _ (yield 1) (yield 2))
        (cons v0 g) <- (g)
        (cons v1 g) <- (g)
        (cons v2 g) <- (gen-handle (const (list v0 v1)) (g))
        (pure 'unreached)))
    (list 1 2)
    ))

(module+ test
  (check-equal?
    (gen-susp-v
      (begin/with-monad gen-monad
        g = (generator _ (yield 1) (yield 2) 3)
        (cons v0 g) <- (g)
        (cons v1 g) <- (g)
        (cons v2 g) <- (gen-catch right left (g))
        (pure (list v0 v1 v2))))
    (list 1 2 (left 3))
    ))

(record gen-state run)
(define (gen-state-eval gst gen)
  (match ((gen-state-run gst) gen)
    ((gen-result r) r)
    ((gen-susp v k) v)))
(define (gen-state-pure v) (gen-state (lambda (k) (gen-susp v k))))
(define/destruct (gen-state-bind (gen-state run) next)
  (gen-state
    (lambda (k)
      (with-monad gen-state-monad
        (match (run k)
          ((gen-result r) (gen-result r))
          ((gen-susp v k) ((gen-state-run (next v)) k)))))))
(define gen-state-monad (monad gen-state-pure gen-state-bind))

(define (send input) (gen-state (lambda (k) (k input))))
(define (send-try input)
  (gen-state (lambda (k)
               (match (k input)
                 ((gen-result r) (gen-susp (left r)
                                           (lambda (_) (gen-result r))))
                 ((gen-susp v k) (gen-susp (right v) k))))))
(define next (curry send (void)))
(define next-try (curry send-try (void)))

(define-syntax with-gen
  (syntax-rules ()
    ((_ gen body ...)
     (gen-state-eval (begin/with-monad gen-state-monad body ...) gen))))

(module+ test
  (check-equal?
    (with-gen (generator _ (yield (* 2 (yield 10))))
      v0 <- next
      v1 <- (send (+ 1 v0))
      (pure v1))
    22
    ))

(module+ test
  (check-equal?
    (with-gen (generator _ (yield (* 2 (yield 10))))
      v0 <- next
      v1 <- (send (+ 1 v0))
      v2 <- (send (* 5 v1))
      (pure 'unreached))
    (* 22 5)
    ))

(module+ test
  (check-equal?
    (with-gen (generator _ (yield (* 2 (yield 10))))
      (right v0) <- next-try
      v1 <- (send (+ 1 v0))
      (pure v1))
    22
    ))

(module+ test
  (check-equal?
    (with-gen (generator _ (yield (* 2 (yield 10))))
      v0 <- next
      v1 <- (send (+ 1 v0))
      (left v2) <- (send-try (* 5 v1))
      (pure (list 'normally-unreached v2)))
    (list 'normally-unreached (* 22 5))
    ))
