#lang typed/racket/base
(provide
  record
  records
  record-struct
  )

(require
  (for-syntax
    "../idset.rkt"
    "../sugar.rkt"
    "../syntax.rkt"
    racket/base
    racket/function
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

(define-syntax (records stx)
  (syntax-case stx (:)
    ((_ (name type-params ...) (rec-name (field-name : field-type) ...) ...)
     (let* ((params (syntax->list #'(type-params ...)))
            (useds (map (curry typenames-used params)
                        (syntax->list #'((() field-type ...) ...))))
            (templates
              (map syntax->list (syntax->list
                #'((rec-name ((field-name : field-type) ...)) ...))))
            (recs (forl
                    used <- useds
                    (list rname rfields) <- templates
                    #`(record (#,rname #,@used) #,@rfields))))
       #`(begin #,@recs)))))
