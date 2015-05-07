#lang racket/base
(provide
  ==
  conde
  exist
  matche
  run
  run*
  )

(require
  "maybe.rkt"
  "microkanren.rkt"
  "monad.rkt"
  "sugar.rkt"
  racket/list
  (except-in racket/match ==)
  racket/set
  (for-syntax
    racket/base
    racket/list
    ))

(module+ test
  (require rackunit))

(define-syntax conde
  (syntax-rules ()
    ((_ (gs ...) ...) (disj* (conj* gs ...) ...))))

(define-syntax exist
  (syntax-rules ()
    ((_ () gs ...) (conj* gs ...))
    ((_ (x0 xs ...) gs ...)
     (call/var (lambda (x0) (exist (xs ...) gs ...))))))

(define-syntax run
  (syntax-rules ()
    ((_ n (xs ...) gs ...)
     (muk-reify muk-var->symbol
                (map muk-var (range (length '(xs ...))))
                (muk-take n ((exist (xs ...) gs ...) muk-state-empty))))))
(define-syntax run*
  (syntax-rules () ((_ body ...) (run -1 body ...))))

(define-for-syntax (pattern->identifiers pat)
  (define (unquote-pats stx)
    (syntax-case stx (unquote)
      ((unquote pat) (list #'pat))
      ((head . tail) (append (unquote-pats #'head) (unquote-pats #'tail)))
      (_ '())))
  (if (identifier? pat) (list pat)
    (syntax-case pat (quote quasiquote)
      ((quote _) '())
      ((quasiquote stx)
       (append* (map pattern->identifiers (unquote-pats #'stx))))
      ((_ args ...)
       (append* (map pattern->identifiers (syntax->list #'(args ...)))))
      (_ '()))))
(define-syntax (match1e stx)
  (syntax-case stx ()
    ((_ arg pattern gs ...)
     (let ((vnames (pattern->identifiers #'pattern)))
       #`(exist (#,@vnames) (== pattern arg) gs ...)))))
(define-syntax matche
  (syntax-rules ()
    ((_ arg (pattern gs ...) ...)
     (let ((param arg)) (disj* (match1e param pattern gs ...) ...)))))

(define (interp-=/= . or-diseqs)
  (match (monad-foldl maybe-monad
          (fn (st (cons e0 e1)) (muk-unify-and-update st e0 e1))
          muk-state-empty or-diseqs)
    ((nothing) #t)
    ((just st-new)
     (lets
       or-diseqs = (forl
                     vr <- (muk-sub-prefix muk-state-empty st-new)
                     val = (muk-sub-get-var st-new vr)
                     (cons vr val))
       (if (null? or-diseqs) #f (muk-func-app '=/= or-diseqs))))))

(define interpretations
  (hash
    '=/= interp-=/=
    ))

(define with-constraints (interpret interpretations))

(define (=/= e0 e1) (== #t (muk-func-app '=/= (list (cons e0 e1)))))
(define (all-diffo xs)
  (matche xs
    ('())
    (`(,_))
    (`(,a ,ad . ,dd)
      (=/= a ad)
      (all-diffo `(,a . ,dd))
      (all-diffo `(,ad . ,dd)))))

(module+ test
  (check-equal?
    (run* (x y) (== (cons (list x 3) 5) (cons (list 4 y) 5)))
    '((4 3)))
  (check-equal?
    (run* (x y) (== (cons (list x 3) 5) (list (list 4 y) 5)))
    '())
  (define (appendo ls rs lsrs)
    (matche ls
      ('() (== rs lsrs))
      ((cons l0 ms) (exist (msrs)
                      (== (cons l0 msrs) lsrs)
                      (appendo ms rs msrs)))))
  (check-equal?
    (run* (x y) (appendo x y (range 1 6)))
    '((() (1 2 3 4 5))
      ((1) (2 3 4 5))
      ((1 2) (3 4 5))
      ((1 2 3) (4 5))
      ((1 2 3 4) (5))
      ((1 2 3 4 5) ())))
  (check-match
    (run 1 (q) with-constraints (all-diffo `(2 3 ,q)))
    `((,q : ((=/= (,q . 2)) == #t) ((=/= (,q . 3)) == #t))))
  (define (rembero x ls out)
    (conde
      ((== '() ls) (== '() out))
      ((exist (a d res)
        (== `(,a . ,d) ls)
        (rembero x d res)
        (conde
          ((== a x) (== res out))
          ((=/= a x) (== `(,a . ,res) out)))))))
  (check-equal?
    (run* (q) with-constraints (rembero 'a '(a b a c) q))
    '(((b c))))
  (check-equal?
    (run* (q) with-constraints (rembero 'a '(a b c) '(a b c)))
    '())
  )
