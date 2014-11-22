#lang racket/base
(provide
  eff-cursor
  eff-cursor*
  cursor-try
  get-cursor
  put-cursor
  modify-cursor
  :::^
  :::^*
  :::@
  :::.
  :::=
  :::~
  :::@*
  :::.*
  :::=*
  :::~*
  )

(require
  "choice-eff.rkt"
  "cursor.rkt"
  "eff.rkt"
  "either.rkt"
  "match.rkt"
  "record.rkt"
  "state-eff.rkt"
  racket/function
  racket/match
  )

(module+ test
  (require
    "sugar.rkt"
    rackunit
    ))

(record cursor-choice-state ch st)

(define (cursor-try f cs . args)
  (match cs
    ((cursor-choice-state ch st)
     (reconsider ch identity identity (apply f (cons cs args))))))

(define/destruct (get-cursor (cursor-choice-state ch st)) (get st))
(define/destruct (put-cursor (cursor-choice-state ch st) cur) (put st cur))
(define/destruct (modify-cursor (cursor-choice-state ch st) f) (modify st f))

(define-syntax eff-cursor
  (syntax-rules ()
    ((_ choice-expr cur-choice-name cursor body ...)
     (let ((cur-choice-name (cursor-choice-state choice-expr (state-ref))))
       (eff-handle (state (cursor-choice-state-st cur-choice-name) cursor)
        body ...)))))

(define-syntax eff-cursor*
  (syntax-rules ()
    ((_ choice-expr cur-choice-name precursor body ... last)
     (eff-cursor choice-expr cur-choice-name (::0 precursor)
      body ...
      (list last (::^*. (get-cursor cur-choice-name)))))))

(define/destruct (:::^ (cursor-choice-state ch st))
  (match (get st)
    ((cursor focus '() '()) (abstain ch 'cannot-ascend))
    ((cursor focus _ _)     (modify st ::^))))
(define/destruct (:::^* (cursor-choice-state ch st)) (modify st ::^*))

(define/destruct (cur-with-descent (cursor-choice-state ch st) path f)
  (match (::@*? (get st) (list path))
    ((left keys) (abstain ch (list 'cannot-descend keys)))
    ((right cur) (f cur))))

(define (:::@ cs path)
  (cur-with-descent cs path (curry put (cursor-choice-state-st cs))))
(define (:::. cs path) (cur-with-descent cs path ::.))
(define (:::~ cs trans path)
  (cur-with-descent cs path
    (lambda (cur) (put-cursor cs (::^ (::~ cur trans) (get-cursor cs))))))
(define (:::= cs val path) (:::~ cs (const val) path))

(define (:::@* cs . path)       (:::@ cs path))
(define (:::.* cs . path)       (:::. cs path))
(define (:::=* cs val . path)   (:::= cs val path))
(define (:::~* cs trans . path) (:::~ cs trans path))

(module+ test
  (check-equal?
    (eff-either-choice ch
      (eff-cursor* ch cur '(1 (2 3) 4 (5 ((6) 7) 8))
        (lets
          (left 'cannot-ascend) = (cursor-try :::^ cur)
          v0 = (:::.* cur 'first)
          v1 = (:::.* cur 'rest 'first 'first)
          _ = (:::@* cur 'rest 'rest 'rest)
          v2 = (:::.* cur 'first 'rest 'first 'first 'first)
          _ = (:::=* cur 10 'first 'first)
          _ = (:::~* cur (curry + 10) 'first 'rest 'first 'rest 'first)
          _ = (:::^ cur)
          v3 = (:::.* cur 'first)
          result = (cursor-try :::@* cur 'first 'first 'rest)
          (list v0 v1 v2 v3 result)
          )))
    (right (list (list 1 2 6 4 (left '(cannot-descend (first rest))))
                 '(1 (2 3) 4 (10 ((6) 17) 8))))
    ))
