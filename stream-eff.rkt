#lang racket/base
(provide
  eff-stream
  peek
  pop
  push
  peek-try
  pop-try
  stream->choice
  stream-try
  (struct-out stream-choice-state)
  )

(require
  "choice-eff.rkt"
  "eff.rkt"
  "maybe.rkt"
  "match.rkt"
  "record.rkt"
  "state-eff.rkt"
  racket/function
  racket/match
  racket/stream
  )

(module+ test
  (require
    "sugar.rkt"
    rackunit
    ))

(record stream-choice-state ch st)

(define (stream->choice ch stream)
  (if (stream-empty? stream)
    (abstention ch 'empty-stream)
    (single ch (stream-first stream))))

(define/destruct (peek (stream-choice-state ch st))
  (choose ch (stream->choice ch (get st))))
(define/destruct (pop (stream-choice-state ch st))
  (let ((stream (get st)))
    (if (stream-empty? stream)
      (void)
      (put st (stream-rest stream)))
    (choose ch (stream->choice ch stream))))
(define/destruct (push (stream-choice-state ch st) v)
  (let ((rest (get st))) (put st (stream-cons v rest))))

(define (stream-try f ss)
  (match ss
    ((stream-choice-state ch st)
     (reconsider ch identity identity (f ss)))))
(define peek-try (curry stream-try peek))
(define pop-try (curry stream-try pop))

(define-syntax eff-stream
  (syntax-rules ()
    ((_ choice-expr stream-choice-name stream body ...)
     (let ((stream-choice-name
             (stream-choice-state choice-expr (state-ref))))
       (eff-handle (state (stream-choice-state-st stream-choice-name) stream)
          body ...)))))

(module+ test
  (check-equal?
    (eff-maybe-choice ch
      (eff-stream ch ss (list 1 2)
        (lets
          v0 = (pop ss)
          v1 = (peek ss)
          v2 = (pop-try ss)
          _ = (push ss 3)
          v3 = (pop ss)
          v4 = (pop-try ss)
          (list v0 v1 v2 v3 v4)
          )))
    (just (list 1 2 (just 2) 3 (nothing)))
    ))

(module+ test
  (check-equal?
    (eff-maybe-choice ch
      (eff-stream ch ss (list 1)
        (lets
          v0 = (pop ss)
          v1 = (pop ss)
          (list 'unreached)
          )))
    (nothing)
    ))
