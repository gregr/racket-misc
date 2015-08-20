#lang racket/base
(provide
  )

(require
  "dict.rkt"
  "maybe.rkt"
  "record.rkt"
  "sugar.rkt"
  racket/list
  racket/match
  )

(records term
  (literal v)
  (pair l r)
  (pair-head p)
  (pair-tail p)
  (lam param body)
  (bvar name)
  (type t)
  (if-equal arg0 arg1 t f)
  (app proc arg))

(define env-empty hash-empty)
(define env-ref hash-ref)
(define env-get hash-get)
(define env-add hash-set)
(define env->list hash->list)
(define list->env make-immutable-hash)
(define (env-single k v) (env-add env-empty k v))
(define (env-merge env0 env1)
  (list->env (append* (map env->list (list env0 env1)))))
(define (env-lookup env ident)
  (match (env-get env ident)
    ((nothing) (error (format "undefined identifier: ~a" ident)))
    ((just val) val)))
(define (env-extend env params)
  (forf env = env
        param <- params
        (env-add env param #f)))

(define (denote term)
  (match term
    ((literal v) (lambda (_) v))
    ((pair l r) (lets dl = (denote l) dr = (denote r)
                      (lambda (env) (cons (dl env) (dr env)))))
    ((pair-head p) (lets dp = (denote p) (lambda (env) (car (dp env)))))
    ((pair-tail p) (lets dp = (denote p) (lambda (env) (cdr (dp env)))))
    ((lam param body)
     (lets dbody = (denote body)
           (lambda (env) (lambda (arg) (dbody (env-add env param arg))))))
    ((bvar name) (lambda (env) (env-ref env name)))
    ((type t)
     (lets dt = (denote t)
           (lambda (env) (match (dt env)
                           ((? symbol?) 'symbol)
                           ((? pair?) 'pair)
                           ('() 'nil)
                           ((? procedure?) 'procedure)
                           ((? boolean?) 'boolean)
                           ((? number?) 'number)
                           ((? char?) 'char)
                           ((? string?) 'string)
                           (_ #f)))))
    ((if-equal arg0 arg1 t f)
     (lets (list da0 da1 dt df) = (map denote (list arg0 arg1 t f))
           (lambda (env) (if (equal? (da0 env) (da1 env)) (dt env) (df env)))))
    ((app proc arg)
     (lets dproc = (denote proc) darg = (denote arg)
           (lambda (env) ((dproc env) (darg env)))))))
