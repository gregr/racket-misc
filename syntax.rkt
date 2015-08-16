#lang racket/base
(provide
  identifier-concat
  identifier-with-?
  )

(require
  racket/list
  racket/string
  )

(define (identifier-concat stx idents)
  (datum->syntax
    stx
    (string->symbol
      (string-append* (map symbol->string (syntax->datum idents))))))

(define (identifier-with-? ident) (identifier-concat ident #`(#,ident ?)))
