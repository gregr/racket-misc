#lang racket/base
(provide
  number->type
  numeric-type-natural
  numeric-type-integer
  numeric-type-exact
  numeric-type-inexact
  numeric-type-complex-exact
  numeric-type-complex-inexact
  repr
  repr->value
  repr-type->constructor
  struct->type
  value->repr
  )

(require
  "comparison.rkt"
  "record.rkt"
  "sugar.rkt"
  racket/function
  racket/match
  racket/set
  )

(module+ test
  (require rackunit))

(record repr type components)

(define numeric-type-natural '(number real exact integer natural))
(define numeric-type-integer '(number real exact integer))
(define numeric-type-exact '(number real exact))
(define numeric-type-inexact '(number real inexact))
(define numeric-type-complex-exact '(number complex exact))
(define numeric-type-complex-inexact '(number complex inexact))

(define (number->type num)
  (if (real? num)
    (if (exact? num)
      (if (integer? num)
        (if (<= 0 num) numeric-type-natural numeric-type-integer)
        numeric-type-exact)
      numeric-type-inexact)
    (if (exact? num) numeric-type-complex-exact numeric-type-complex-inexact)))

(def (struct->type val)
  (values sty _) = (struct-info val)
  sty)
(define repr-entries
  `((,void? ,(const 'void) ,identity)
    (,boolean? ,(const 'boolean) ,identity)
    (,symbol? ,(const 'symbol) ,identity)
    (,char? ,(const 'char) ,identity)
    (,string? ,(const 'string) ,identity)
    (,number? ,number->type ,identity)
    (,null? ,(const 'nil) ,identity)
    (,pair? ,(const 'pair) ,(fn ((cons a d)) (list a d)))
    (,vector? ,(const 'vector) ,vector->list)
    (,hash? ,(const 'hash) ,hash->list-sorted)
    (,set? ,(const 'set) ,set->list-sorted)
    (,struct? ,struct->type ,(compose1 cdr vector->list struct->vector))
    (,procedure? ,(const 'procedure) ,identity)
    (,(const #t) ,(const 'unknown) ,identity)))

(define (value->repr val)
  (forf result = (void)
        (list found? val->type val->components) <- repr-entries
        #:break (not (void? result))
        (when (found? val) (repr (val->type val) (val->components val)))))
(define (repr-type->constructor type)
  (match type
    ('void identity)
    ('boolean identity)
    ('symbol identity)
    ('char identity)
    ('string identity)
    (`(number . ,_) identity)
    ('nil identity)
    ('pair (curry apply cons))
    ('vector list->vector)
    ('hash make-immutable-hash)
    ('set list->set)
    ((? struct-type?) (curry apply (struct-type-make-constructor type)))
    ('procedure identity)
    ('unknown identity)))
(def (repr->value (repr type components))
  ((repr-type->constructor type) components))

(module+ test
  (lets
    vals = (list
             (void)
             #f
             'name
             #\c
             "string"
             4
             '()
             (cons (cons 5 'a) (cons 6 '()))
             #(7 8 9)
             (hash 'one 1 'two 2)
             (set 'one 'three 'four)
             (repr 'repr-type 'repr-component)
             identity
             (box 'box)
             )
    (list vvoid vbool vsym vchar vstring vnum vnil
          vpair vvec vhash vset vstruct vproc vunk) = vals
    expected-reprs = (map (curry apply repr)
      `((void ,(void))
        (boolean #f)
        (symbol name)
        (char #\c)
        (string "string")
        (,numeric-type-natural 4)
        (nil ())
        (pair ((5 . a) (6)))
        (vector (7 8 9))
        (hash ,(hash->list-sorted vhash))
        (set ,(set->list-sorted vset))
        (,(struct->type vstruct) (repr-type repr-component))
        (procedure ,vproc)
        (unknown ,vunk)))
    reprs = (map value->repr vals)
    (begin
      (check-equal? (map repr->value reprs) vals)
      (check-equal? reprs expected-reprs)
      )))
