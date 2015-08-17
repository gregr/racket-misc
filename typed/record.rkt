#lang typed/racket/base
(provide
  record
  record-struct
  )

(require
  (for-syntax
    ;"../syntax.rkt"
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

;(define-syntax (records stx)
  ;(syntax-case stx ()
    ;((_ (name type-params ...) (rname rfield ...) ...)
     ;#`(begin-top
         ;(begin (record (rname type-params ...) rfield ...) ...)
         ;(define-type name (U rname ...))
         ;(define-predicate #,(identifier-with-? #'name) name))

     ;;#`(eval #'(#%top-interaction .
        ;;(begin
         ;;(begin (record (rname type-params ...) rfield ...) ...)
         ;;(eval #'(#%top-interaction .
          ;;(begin
            ;;(define-type name (U rname ...))
            ;;(eval #'(#%top-interaction .
              ;;(define-predicate #,(identifier-with-? #'name) name)))))))))

     ;)
    ;((_ name body ...)
     ;#'(records (name) body ...))))
