#lang racket/base
(provide
  monad
  monad-t
  pure
  bind
  lift
  (struct-out ident)
  ident-monad
  with-monad
  let1/monad
  let/monad
  let/with-monad
  begin/monad
  begin/with-monad
  for/fold/monad
  for/list/monad
  monad-map
  monad-foldl
  )

(require
  (for-syntax racket/base)
  "match.rkt"
  "record.rkt"
  racket/match
  racket/sequence
  )

(module+ test
  (require rackunit))

(record monad-rec pure bind extra)
(record monad-rec-t lift)
(define (monad pure bind (extra (void))) (monad-rec pure bind extra))
(define (monad-t pure bind lift) (monad pure bind (monad-rec-t lift)))

(record ident x)
(define ident-monad
  (monad
    ident
    (lambda/destruct ((ident value) next) (next value))))

(define current-monad (make-parameter ident-monad))
(define (pure value) ((monad-rec-pure (current-monad)) value))
(define (bind prev next) ((monad-rec-bind (current-monad)) prev next))
(define (lift mc) ((monad-rec-t-lift (monad-rec-extra (current-monad))) mc))

(define-syntax with-monad
  (syntax-rules ()
    ((_ monad body ...)
     (parameterize ((current-monad monad)) body ...))))

(define-syntax let1/monad
  (syntax-rules (<- =)
    ((_ (pattern <- value) body ...)
     (bind value (lambda/destruct (pattern) body ...)))
    ((_ (pattern = value) body ...)
     (match-let1+values pattern value body ...))))

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

(define (monad-foldl monad proc seed xs)
  (match xs
    ('() (begin/with-monad monad (pure seed)))
    ((cons y ys)
      (begin/with-monad monad
        next-seed <- (proc seed y)
        (monad-foldl monad proc next-seed ys)))))

(module+ test
  (check-equal?
    (monad-foldl ident-monad (lambda (a b) (ident (+ a b)))
                 0 '(1 2 3))
    (ident 6)))

(define (monad-map monad proc xs)
  (begin/with-monad monad
    ys <- (monad-foldl monad
            (lambda (ys x)
              (begin/with-monad monad
                y <- (proc x)
                (pure (cons y ys)))) '() xs)
    (pure (reverse ys))))

(module+ test
  (check-equal?
    (monad-map ident-monad (compose1 ident add1) '(1 2 3))
    (ident '(2 3 4))))

(define-syntax (for/fold/monad stx)
  (syntax-case stx ()
    ((_ monad acc acc-init ((seq seq-src) ...) body ...)
     (with-syntax (((seqname ...) (generate-temporaries #'(seq-src ...))))
       #'(begin/with-monad monad
           (match-let loop ((acc-lifted (pure acc-init))
                            (seqname (sequence->list seq-src)) ...)
             (if (null? (filter null? (list seqname ...)))
               (begin/with-monad monad
                 acc <- acc-lifted
                 (list seq ...) = (list (car seqname) ...)
                 (loop (begin/monad body ...) (cdr seqname) ...))
               acc-lifted)))))))

(define-syntax for/list/monad
  (syntax-rules ()
    ((_ monad seqs body ... final)
     (begin/with-monad monad
       result <- (for/fold/monad monad acc '() seqs body ...
                                 result <- final
                                 (pure (list* result acc)))
       (pure (reverse result))))))
