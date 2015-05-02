#lang racket/base
(provide
  conde
  exist
  run
  run*
  )

(require
  "microkanren.rkt"
  racket/list
  )

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

(module+ test
  (check-equal?
    (run* (x y) (== (cons (list x 3) 5) (cons (list 4 y) 5)))
    '((4 3)))
  (check-equal?
    (run* (x y) (== (cons (list x 3) 5) (list (list 4 y) 5)))
    '())
  (define (appendo l r lr)
    (conde
      ((== '() l) (== r lr))
      ((exist (lfirst lrest lrestr)
        (== (cons lfirst lrest) l)
        (== (cons lfirst lrestr) lr)
        (appendo lrest r lrestr)
        ;(== (list lrest r) lrestr)
        ))))
  (check-equal?
    (run* (x y) (appendo x y (range 1 6)))
    '((() (1 2 3 4 5))
      ((1) (2 3 4 5))
      ((1 2) (3 4 5))
      ((1 2 3) (4 5))
      ((1 2 3 4) (5))
      ((1 2 3 4 5) ())))
  (define (rember*o tr o)
    (conde
      ((== '() tr) (== '() o))
      ((exist (a d)
        (== (cons a d) tr)
        (conde
          ((exist (aa da)
            (== (cons aa da) a)
            (exist (a^ d^)
              (rember*o a a^)
              (rember*o d d^)
              (== (cons a^ d^) o))))
          ((== a 8) (rember*o d o))
          ((exist (d^)
            (rember*o d d^)
            (== (cons a d^) o))))))))
  (check-equal?
    (run 8 (q) (rember*o q '(1 2 8 3 4 5)))
    '(((1 2 8 3 4 5))
      ((1 2 8 3 4 5 8))
      ((1 2 8 3 4 8 5))
      ((1 2 8 3 8 4 5))
      ((1 2 8 8 3 4 5))
      ((1 2 8 8 3 4 5))
      ((1 8 2 8 3 4 5))
      ((8 1 2 8 3 4 5))))
  )
