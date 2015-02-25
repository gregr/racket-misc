#lang racket/base
(provide
  list-navigator-keys
  navigator-new
  navigator-focus
  navigator-focus-set
  navigator-path
  navigator-ascend
  navigator-descend
  navigator-shift
  )

(require
  "cursor.rkt"
  "list.rkt"
  "maybe.rkt"
  "record.rkt"
  "sugar.rkt"
  racket/list
  racket/match
  )

(module+ test
  (require rackunit))

(define (list-navigator-keys xs)
  (let loop ((current '(first)) (xs xs))
    (match xs
      ('() '())
      ((cons x xs)
       (lets
         remaining = (loop (list* 'rest current) xs)
         (list* current remaining))))))

(module+ test
  (check-equal?
    (list-navigator-keys '())
    '()
    )
  (check-equal?
    (list-navigator-keys '(a b c))
    '((first) (rest first) (rest rest first))
    )
  (check-equal?
    (:.* '(a b c) 'rest 'first)
    'b)
  )

(record navigator-frame steps index keys)
(record navigator focus->keys cursor keys trail)
(define (navigator-from-cursor f->k cursor trail)
  (navigator f->k cursor (f->k (::.* cursor)) trail))
(define (navigator-new f->k focus)
  (navigator-from-cursor f->k (::0 focus) '()))
(def (navigator-focus (navigator _ cursor _ _))
  (::.* cursor))
(def (navigator-focus-set (navigator f->k cursor keys trail) focus)
  (navigator-from-cursor f->k (::=* cursor focus) trail))

(def (navigator-reset (navigator f->k cursor _ trail))
  (navigator-from-cursor f->k cursor trail))
(def (navigator-previous (navigator f->k cursor keys trail))
  (match trail
    ('() (nothing))
    ((cons (navigator-frame steps index keys) trail)
     (just (navigator f->k (last (iterate ::^ cursor steps)) keys trail)))))
(define (navigator-ascend nav)
  (maybe-fold
    (nothing) (compose1 just navigator-reset) (navigator-previous nav)))
(define (navigator-descend nav (idx 0))
  (lets
    (navigator f->k cursor keys trail) = nav
    (if (and (<= 0 idx) (< idx (length keys)))
      (lets
        key = (list-ref keys idx)
        steps = (length key)
        frame = (navigator-frame steps idx keys)
        cursor = (::@ cursor key)
        (just (navigator-from-cursor f->k cursor (list* frame trail))))
      (nothing))))
(def (navigator-shift nav offset)
  (navigator f->k cursor keys trail) = nav
  (match trail
    ('() (nothing))
    ((cons (navigator-frame steps index keys) trail)
     (lets
       index = (+ index offset)
       (just nav) = (navigator-previous nav)
       (navigator-descend nav index)))))

(def (navigator-path nav)
  (navigator _ _ _ trail) = nav
  focus = (navigator-focus nav)
  (list _ path) =
  (forf
    (list nav path) = (list nav (list (list focus (nothing))))
    (navigator-frame steps index keys) <- trail
    (just nav) = (navigator-previous nav)
    (navigator _ _ keys _) = nav
    key = (list-ref keys index)
    next = (list (navigator-focus nav) (just (list index key)))
    (list nav (list* next path)))
  path)

(module+ test
  (lets
    f->k = (fn (focus) (if (list? focus) (list-navigator-keys focus) '()))
    nav0 = (navigator-new f->k '(a b () (c (d ((e)) f)) g))
    (just nav1) = (navigator-descend nav0 1)
    _ = (check-equal? (navigator-focus nav1) 'b)
    _ =
    (check-equal?
      (navigator-descend nav1 2)
      (nothing))
    (just nav2) = (navigator-descend nav0 2)
    _ =
    (check-equal?
      (navigator-focus nav2)
      '())
    _ =
    (check-equal?
      (navigator-descend nav2 0)
      (nothing))
    (just nav3) = (navigator-shift nav2 2)
    _ = (check-equal? (navigator-focus nav3) 'g)
    nav3 = (navigator-focus-set nav3 'changed)
    (just nav4) = (navigator-shift nav3 -1)
    (nothing) = (navigator-shift nav3 1)
    (just nav5) = (navigator-descend nav4 1)
    (just nav6) = (navigator-descend nav5 1)
    (just nav7) = (navigator-descend nav6 0)
    (just nav8) = (navigator-descend nav7 0)
    _ = (check-equal? (navigator-focus nav8) 'e)
    (check-equal?
      (navigator-path nav8)
      (list
        (list '(a b () (c (d ((e)) f)) changed)
              (just (list 3 '(rest rest rest first))))
        (list '(c (d ((e)) f)) (just (list 1 '(rest first))))
        (list '(d ((e)) f) (just (list 1 '(rest first))))
        (list '((e)) (just (list 0 '(first))))
        (list '(e) (just (list 0 '(first))))
        (list 'e (nothing))
        )
      )
    ))
