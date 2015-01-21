#lang racket/base
(provide
  flip
  )

(define ((flip proc) x y) (proc y x))
