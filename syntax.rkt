#lang racket/base
(provide
  identifier-concat
  identifier-with-?
  typenames-free
  typenames-used
  )

(require
  "idset.rkt"
  "typed/syntax.rkt"
  racket/function
  racket/list
  racket/match
  racket/string
  )

(module+ test
  (require
    rackunit
    racket/set
    ))

(define (identifier-concat stx idents)
  (datum->syntax
    stx
    (string->symbol
      (string-append* (map symbol->string (syntax->datum idents))))))

(define (identifier-with-? ident) (identifier-concat ident #`(#,ident ?)))

(define (typenames-free type)
  (match (syntax->list type)
    ((cons ctor args)
     (cond
       ((identifier=All? ctor)
        (match-let (((list params body) args))
          (idset-subtract (typenames-free body)
                          (list->idset (syntax->list params)))))
       ((identifier=->*? ctor)
        (match-let (((list mandatory optional result) args))
          (typenames-free
            #`(() #,result
                  #,@(append* (map syntax->list (list mandatory optional)))))))
       (else (idset-union* (map typenames-free args)))))
    (#f (idset-single type))))

(define (typenames-used params type)
  (let ((used (idset-intersect (list->idset params) (typenames-free type))))
    (filter (curry idset-member? used) params)))

(module+ test
  (check-equal?
    (list->set (map syntax->datum (idset->list
      (typenames-free
        #'(All (a b) (-> (->* (a b) (a) Number) c (Listof String) Number))))))
    (list->set '(Number String c)))
  (check-equal?
    (map syntax->datum
      (typenames-used
        (syntax->list #'(a b c))
        #'(All (a b) (-> (->* (a b) (a) Number) c (Listof String) Number))))
    '(c)))
