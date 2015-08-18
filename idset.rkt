#lang racket/base
(provide
  idset->list
  idset-add
  idset-empty
  idset-intersect
  idset-member?
  idset-remove
  idset-single
  idset-subtract
  idset-symmetric-difference
  idset-union
  idset-union*
  list->idset
  )

(require
  racket/list
  syntax/id-table
  )

(define idset-empty (make-immutable-free-id-table))
(define (idset-member? ids id) (free-id-table-ref ids id #f))
(define (idset-add ids id) (free-id-table-set ids id #t))
(define (idset-remove ids id) (free-id-table-remove ids id))
(define (idset-single ident) (idset-add idset-empty ident))
(define (idset-union ids0 ids1) (list->idset (append (idset->list ids0) (idset->list ids1))))
(define (idset-union* idss) (list->idset (append* (map idset->list idss))))
(define (idset-subtract ids0 ids1)
  (foldl (lambda (id ids) (idset-remove ids id)) ids0 (idset->list ids1)))
(define (idset-symmetric-difference ids0 ids1)
  (idset-union (idset-subtract ids0 ids1) (idset-subtract ids1 ids0)))
(define (idset-intersect ids0 ids1)
  (idset-subtract ids0 (idset-subtract ids0 ids1)))
(define (idset->list ids) (free-id-table-map ids (lambda (id _) id)))
(define (list->idset ids)
  (foldl (lambda (id ids) (idset-add ids id)) idset-empty ids))
