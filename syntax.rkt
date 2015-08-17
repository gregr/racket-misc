#lang racket/base
(provide
  identifier-concat
  identifier-with-?
  )

(require
  ;(for-syntax racket/base racket/match)
  racket/list
  racket/string
  )

(define (identifier-concat stx idents)
  (datum->syntax
    stx
    (string->symbol
      (string-append* (map symbol->string (syntax->datum idents))))))

(define (identifier-with-? ident) (identifier-concat ident #`(#,ident ?)))

;(define-for-syntax (make-begin-top stx parts)
  ;(let* ((body (match parts
                 ;((list single) single)
                 ;((cons fst parts)
                  ;(datum->syntax
                    ;stx `(,#'begin ,fst ,(make-begin-top stx parts))))))
         ;(ti-body #`(#%top-interaction . #,body))
        ;)
    ;(datum->syntax stx `(eval ,ti-body))))

;(define-syntax (begin-top stx)
  ;(syntax-case stx ()
    ;((_ body ...)
     ;(displayln (make-begin-top stx (syntax->list #'(body ...))))
     ;(make-begin-top stx (syntax->list #'(body ...)))
     ;)))
