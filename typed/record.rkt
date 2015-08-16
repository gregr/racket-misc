#lang typed/racket/base
(provide
  record
  record-struct
  )

(require
  (for-syntax
    racket/base
    ))

(define-syntax (record-struct stx)
  (syntax-case stx (:)
    ((_ (name type-params ...) ((field-name : field-type) ...) struct-rest ...)
     #'(begin
         (struct (type-params ...) name ((field-name : field-type) ...)
                 #:transparent struct-rest ...)))))

(define-syntax record
  (syntax-rules ()
    ((_ (name type-params ...) field ...)
     (record-struct (name type-params ...) (field ...)))
    ((_ name field ...) (record (name) field ...))))
