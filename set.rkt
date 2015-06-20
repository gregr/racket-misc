#lang racket
(provide
  set-empty
  set-filter
  )

(define set-empty (set))

(define (set-filter keep? xs) (list->set (filter keep? (set->list xs))))
