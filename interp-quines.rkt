#lang racket/base
(require
  "dakanren.rkt"
  "microkanren.rkt"
  "minikanren.rkt"
  (except-in racket/match ==)
  )

(module+ test
  (require rackunit))

(define eval-expo
  (lambda (exp env val)
    (conde
      ((exist (v)
         (== `(quote ,v) exp)
         (not-in-envo 'quote env)
         (absento 'closure v)
         (== v val)))
      ((exist (a*)
         (== `(list . ,a*) exp)
         (not-in-envo 'list env)
         (absento 'closure a*)
         (proper-listo a* env val)))
      ((symbolo exp) (lookupo exp env val))
      ((exist (rator rand x body env^ a)
         (== `(,rator ,rand) exp)
         (eval-expo rator env `(closure ,x ,body ,env^))
         (eval-expo rand env a)
         (eval-expo body `((,x . ,a) . ,env^) val)))
      ((exist (x body)
         (== `(lambda (,x) ,body) exp)
         (symbolo x)
         (not-in-envo 'lambda env)
         (== `(closure ,x ,body ,env) val))))))

(define lookupo
  (lambda (x env t)
    (exist (y v rest)
      (== `((,y . ,v) . ,rest) env)
      (conde
        ((== y x) (== v t))
        ((=/= y x) (lookupo x rest t))))))

(define not-in-envo
  (lambda (x env)
    (conde
      ((== '() env))
      ((exist (y v rest)
         (== `((,y . ,v) . ,rest) env)
         (=/= y x)
         (not-in-envo x rest))))))

(define proper-listo
  (lambda (exp env val)
    (conde
      ((== '() exp)
       (== '() val))
      ((exist (a d v-a v-d)
         (== `(,a . ,d) exp)
         (== `(,v-a . ,v-d) val)
         (eval-expo a env v-a)
         (proper-listo d env v-d))))))

(define quinec
  '((lambda (_.0)
      (list _.0 (list (quote quote) _.0)))
    (quote
      (lambda (_.0)
        (list _.0 (list (quote quote) _.0))))))

(define twine1
  '((lambda (_.0) (list 'quote (list _.0 (list 'quote _.0))))
    '(lambda (_.0) (list 'quote (list _.0 (list 'quote _.0))))))
(define twine0 (list 'quote twine1))

(module+ test
  (check-equal?
    (run-da 1 q (eval-expo '(quote 5) '() q))
    '(5))

  (check-equal?
    (run-da 1 q (eval-expo '(lambda (x) x) '() q))
    '((closure x x ())))

  (check-equal?
    (run*-da q (eval-expo '(quote 5) '() q))
    '(5))

  (check-equal?
    (run*-da q (eval-expo '(lambda (x) x) '() q))
    '((closure x x ())))

  (check-equal?
    (run-da-dls 1 () q (eval-expo
                  `((lambda (x)
                     (list x ,q))
                   (quote
                     (lambda (x)
                       (list x ,q))))
                  '()
                  `((lambda (x)
                     (list x ,q))
                   (quote
                     (lambda (x)
                       (list x ,q))))
                  ))
    '((list (quote quote) x)))

  (check-equal?
    (run-da-dls 1 () q (eval-expo
                  `((lambda (x) ,q)
                   (quote
                     (lambda (x) ,q)))
                  '()
                  `((lambda (x) ,q)
                   (quote
                     (lambda (x) ,q)))
                  ))
    '(((lambda (_.0)  (list x _.0))  (list (quote quote) x))))

  (check-equal?
    (run-da-dls 1 (10) q (eval-expo q '() q))
    `(,quinec))

  (check-equal?
    (run-da-dls 1 (13) (p q)
                (=/= p q) (eval-expo p '() q) (eval-expo q '() p))
    `((,twine0 ,twine1)))
  )
