#lang typed/racket/base
(provide
  identifier=All?
  identifier=->*?
  )

(: identifier=All? (-> Any Boolean : #:+ Identifier))
(define (identifier=All? val)
  (and (identifier? val) (free-identifier=? #'All val #f)))
(: identifier=->*? (-> Any Boolean : #:+ Identifier))
(define (identifier=->*? val)
  (and (identifier? val) (free-identifier=? #'->* val #f)))
