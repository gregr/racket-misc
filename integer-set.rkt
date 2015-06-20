#lang racket
(provide
  integer-set-extrema
  integer-set-lb-subtract
  integer-set-ub-subtract
  list->integer-set
  )

(require
  "sugar.rkt"
  data/integer-set
  )

(module+ test
  (require
    rackunit
    ))

(def (list->integer-set xs)
  (values wfs lb ub) =
  (forf wfs = '() lb = #f ub = #f
        elem <- (sort xs >)
        (if lb
          (if (= elem (- lb 1)) (values wfs elem ub)
            (values (list* (cons lb ub) wfs) elem elem))
          (values wfs elem elem)))
  wfs = (if lb (list* (cons lb ub) wfs) wfs)
  (make-integer-set wfs))

(module+ test
  (check-equal?
    (list->integer-set '(-3 5 -2 -4 7 6 8))
    (integer-set '((-4 . -2) (5 . 8)))))

(def (integer-set-extrema int-set)
  wfs = (integer-set-contents int-set)
  (values (car (car wfs)) (cdr (last wfs))))

(module+ test
  (check-equal?
    (lets
      (values mn mx) = (integer-set-extrema (integer-set '((-4 . -2) (5 . 8))))
      (list mn mx))
    (list -4 8)))

(define (integer-set-lb-subtract lb not-in)
  (forf lb = lb
        (cons rl ru) <- (integer-set-contents not-in)
        #:break (or (not lb) (< lb rl))
        (if (<= lb ru) (+ ru 1) lb)))

(define (integer-set-ub-subtract ub not-in)
  (forf ub = ub
        (cons rl ru) <- (reverse (integer-set-contents not-in))
        #:break (or (not ub) (> ub ru))
        (if (>= ub rl) (- rl 1) ub)))

(module+ test
  (lets
    not-in = (integer-set '((-3 . 5) (7 . 9) (15 . 20)))
    (begin
      (check-equal? (integer-set-lb-subtract -4 not-in) -4)
      (check-equal? (integer-set-lb-subtract -3 not-in) 6)
      (check-equal? (integer-set-lb-subtract 6 not-in) 6)
      (check-equal? (integer-set-lb-subtract 8 not-in) 10)
      (check-equal? (integer-set-lb-subtract 20 not-in) 21)
      (check-equal? (integer-set-lb-subtract 21 not-in) 21)
      (check-equal? (integer-set-ub-subtract 21 not-in) 21)
      (check-equal? (integer-set-ub-subtract 20 not-in) 14)
      (check-equal? (integer-set-ub-subtract 8 not-in) 6)
      (check-equal? (integer-set-ub-subtract 6 not-in) 6)
      (check-equal? (integer-set-ub-subtract -3 not-in) -4)
      (check-equal? (integer-set-ub-subtract -4 not-in) -4)
      )))
