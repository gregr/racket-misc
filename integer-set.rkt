#lang racket
(provide
  integer-set-+
  integer-set--
  integer-set-*-imprecise
  integer-set-empty
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

(define integer-set-empty (make-range))

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

(define (integer-set-invert is)
  (make-integer-set
    (forf iwfs = '()
          (cons lb ub) <- (integer-set-contents is)
          (list* (cons (- ub) (- lb)) iwfs))))

(module+ test
  (check-equal?
    (integer-set-invert (integer-set '((-3 . 5) (7 . 9))))
    (integer-set '((-9 . -7) (-5 . 3)))
    ))

(define (integer-set-+ a b)
  (forf result = integer-set-empty
        (cons alb aub) <- (integer-set-contents a)
        (union result
               (forf result = integer-set-empty
                     (cons blb bub) <- (integer-set-contents b)
                     (union result (make-range (+ alb blb) (+ aub bub)))))))

(define (integer-set-- a b) (integer-set-+ a (integer-set-invert b)))

(define (cross-binop-range op l0 l1 r0 r1)
  (make-range (min (op l0 r0) (op l0 r1) (op l1 r0) (op l1 r1))
              (max (op l0 r0) (op l0 r1) (op l1 r0) (op l1 r1))))

(define (integer-set-*-imprecise a b)
  (forf result = integer-set-empty
        (cons alb aub) <- (integer-set-contents a)
        (union result
               (forf result = integer-set-empty
                     (cons blb bub) <- (integer-set-contents b)
                     (union result (cross-binop-range * alb aub blb bub))))))

(module+ test
  (lets
    lhs0 = (integer-set '((2 . 3)))
    lhs = (integer-set '((2 . 3) (100 . 200)))
    rhs = (integer-set '((-3 . 5) (7 . 9)))
    (begin
      (check-equal?
        (integer-set-+ lhs0 rhs)
        (make-range -1 12))
      (check-equal?
        (integer-set-+ lhs rhs)
        (make-integer-set '((-1 . 12) (97 . 209))))
      (check-equal?
        (integer-set-- lhs0 rhs)
        (make-range -7 6))
      (check-equal?
        (integer-set-- lhs rhs)
        (make-integer-set '((-7 . 6) (91 . 203))))
      (check-equal?
        (integer-set-*-imprecise lhs0 rhs)
        (make-range -9 27))
      (check-equal?
        (integer-set-*-imprecise lhs rhs)
        (make-integer-set '((-600 . 1800))))
      )))
