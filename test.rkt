#lang racket/base
(provide
  visual-check-equal?
  )

(require
  rackunit
  )

(define (visual-check-equal? visualize actual expected)
  (unless (equal? actual expected)
    (displayln "--------------------")
    (displayln "visualized actual:")
    (displayln (visualize actual))
    (displayln "--------------------")
    (displayln "visualized expected:")
    (displayln (visualize expected)))
  (check-equal? actual expected))
