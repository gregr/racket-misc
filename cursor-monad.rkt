#lang racket/base
(provide
  with-cursor
  with-cursor*
  :::^
  :::^*
  :::@
  :::@?
  :::.
  :::=
  :::~
  :::@*
  :::@?*
  :::.*
  :::=*
  :::~*
  )

(require
  "cursor.rkt"
  "either.rkt"
  "monad.rkt"
  "state-monad.rkt"
  racket/function
  racket/match
  )

(module+ test
  (require rackunit))

(define-syntax with-cursor
  (syntax-rules ()
    ((_ cursor body ...)
     ((state-run (begin/with-monad state-monad body ...)) cursor))))
(define-syntax with-cursor*
  (syntax-rules ()
    ((_ structure body ...)
     (match-let (((cons val cursor)
                  ((state-run (begin/with-monad state-monad body ...))
                   (::0 structure))))
       (cons val (::^*. cursor))))))

(define :::^ (with-monad state-monad (modify ::^)))
(define :::^* (with-monad state-monad (modify ::^*)))

(define (:::@ path)
  (begin/with-monad state-monad
    cur <- get
    (put (::@* cur (list path)))))
(define (:::@? path)
  (begin/with-monad state-monad
    cur <- get
    (match (::@*? cur (list path))
      ((right cur) (begin/monad
                     _ <- (put cur)
                     (pure '())))
      ((left keys) (pure keys)))))
(define (:::. path)
  (begin/with-monad state-monad
    cur <- get
    (pure (apply ::. (list cur path)))))
(define (:::= val path)
  (begin/with-monad state-monad
    cur <- get
    (put (apply ::= (list cur val path)))))
(define (:::~ trans path)
  (begin/with-monad state-monad
    cur <- get
    (put (apply ::~ (list cur trans path)))))

(define (:::@* . path)       (:::@ path))
(define (:::@?* . path)      (:::@? path))
(define (:::.* . path)       (:::. path))
(define (:::=* val . path)   (:::= val path))
(define (:::~* trans . path) (:::~ trans path))

(module+ test
  (check-equal?
    (with-cursor* '(1 (2 3) 4 (5 ((6) 7) 8))
      v0 <- (:::.* 'first)
      v1 <- (:::.* 'rest 'first 'first)
      _ <- (:::@* 'rest 'rest 'rest)
      v2 <- (:::.* 'first 'rest 'first 'first 'first)
      _ <- (:::=* 10 'first 'first)
      _ <- (:::~* (curry + 10) 'first 'rest 'first 'rest 'first)
      _ <- :::^
      v3 <- (:::.* 'first)
      keys <- (:::@?* 'first 'first 'rest)
      (pure (list v0 v1 v2 v3 keys)))
    (cons (list 1 2 6 4 '(first rest))
          '(1 (2 3) 4 (10 ((6) 17) 8)))
  ))
