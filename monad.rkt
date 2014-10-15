#lang racket/base
(provide
  (struct-out monad)
  pure
  bind
  (struct-out ident)
  ident-monad
  with-monad
  let1/monad
  let/monad
  let/with-monad
  begin/monad
  begin/with-monad
  )

(require
  (for-syntax racket/base)
  "match.rkt"
  "record.rkt"
  racket/match
  )

(module+ test
  (require rackunit))

(record monad pure bind)

(record ident x)
(define ident-monad
  (monad
    ident
    (lambda/destruct ((ident value) next) (next value))))

(define current-monad (make-parameter ident-monad))

(define (pure value) ((monad-pure (current-monad)) value))
(define (bind prev next) ((monad-bind (current-monad)) prev next))

(define-syntax with-monad
  (syntax-rules ()
    ((_ monad body ...)
     (parameterize ((current-monad monad)) body ...))))

(define-syntax let1/monad
  (syntax-rules (<- =)
    ((_ (pattern <- value) body ...)
     (bind value (lambda/destruct (pattern) body ...)))
    ((_ (pattern = value) body ...)
     (match-let ((pattern value)) body ...))))

(define-syntax (let/monad stx)
  (syntax-case stx ()
    ((_ (binding ...) body ...)
     (for/fold ((body #'(begin body ...)))
               ((binding (reverse (syntax->list #'(binding ...)))))
      #`(let1/monad #,binding #,body)))))

(define-syntax let/with-monad
  (syntax-rules ()
    ((_ monad bindings body ...)
     (with-monad monad
      (let/monad bindings body ...)))))

(define-syntax begin/monad
  (syntax-rules ()
    ((_ pattern bind-sym value body ...)
     (let1/monad (pattern bind-sym value) (begin/monad body ...)))
    ((_ body)
     body)))

(define-syntax begin/with-monad
  (syntax-rules ()
    ((_ monad body ...)
     (with-monad monad
      (begin/monad body ...)))))

(module+ test
  (check-equal?
    7
    (begin/with-monad ident-monad
      x <- (pure 4)
      y = 3
      (+ x y))))
