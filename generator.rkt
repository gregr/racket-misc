#lang racket/base
; generalized yield-run as described in:
; http://www.cs.indiana.edu/~sabry/papers/yield.pdf
(provide
  run-at
  run
  run*
  yield-at
  yield
  generator
  generator*
  gen-fold
  gen->list
  )

(require
  "record.rkt"
  racket/control
  racket/function
  racket/match
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

(define (yield-at tag v) (shift-at tag k (gen-susp v k)))
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

(define (gen->list gen)
  (gen-fold (lambda (v vs) (list (void) (cons v vs)))
            (lambda (_ vs) (reverse vs))
            (void) '() gen))

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
