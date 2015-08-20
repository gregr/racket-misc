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
