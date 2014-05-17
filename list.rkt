#lang racket/base
(provide
  list-set
  list-init
  list-inits
  iterate
  )

(require racket/list)

(define (list-set xs idx val)
  (let-values (((start end) (split-at xs idx)))
              (append start (cons val (cdr end)))))

(define (list-init lst) (reverse (cdr (reverse lst))))
(define (list-inits lst) (reverse (iterate list-init lst (length lst))))

(define (iterate proc seed count)
  (if (<= count 0) (list seed)
    (cons seed (iterate proc (proc seed) (- count 1)))))
