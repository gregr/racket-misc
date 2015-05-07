#lang racket/base
; variant of: http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf
(provide
  ==
  call/var
  conj
  conj*
  disj
  disj*
  muk-state-empty
  muk-take
  muk-take-all
  muk-var
  muk-var?
  muk-var->symbol
  muk-reify
  muk-reify-var
  Zzz
  )

(require
  "cursor.rkt"
  "dict.rkt"
  "list.rkt"
  "maybe.rkt"
  "monad.rkt"
  "record.rkt"
  "sugar.rkt"
  racket/dict
  racket/function
  racket/set
  (except-in racket/match ==)
  )

(module+ test
  (require
    racket/list
    rackunit
    ))

(records muk-term
  (muk-var name)
  (muk-func name args))
(def (muk-var-next (muk-var idx)) (muk-var (+ 1 idx)))
(define (muk-sub-get-var sub vr)
  (match (if (muk-var? vr) (dict-get sub vr) (nothing))
    ((nothing) vr)
    ((just vr) (muk-sub-get-var sub vr))))
(def (muk-sub-add bs vr val) (dict-add bs vr val))
(record muk-state sub-vars sub-funcs func-deps func-interps next-var)
(define muk-state-empty (muk-state (hash) (hash) (hash) (hash) (muk-var 0)))
(define ((muk-state-interpret name op) st)
  (:~* st (lambda (fis) (dict-set fis name op)) 'func-interps))
(def (muk-sub-prefix (muk-state sub-vars-old _ _ _ _)
                     (muk-state sub-vars-new _ _ _ _))
  (forl
    (cons key val) <- (dict->list sub-vars-new)
    #:unless (equal? (just val) (dict-get sub-vars-old key))
    (cons key val)))

(module+ test
  (check-equal?
    (make-immutable-hash
      (apply muk-sub-prefix
             (map (fn (sub) (:=* muk-state-empty sub 'sub-vars))
                  (list (hash 'a 1 'b 2 'c 3 'd 4)
                        (hash 'b 5 'c 3 'a 1 'e 11 'f 12)))))
    (hash 'b 5 'e 11 'f 12)))

(define muk-mzero '())
(define (muk-mplus ss1 ss2)
  (match ss1
    ('() ss2)
    ((? procedure?) (thunk (muk-mplus ss2 (ss1))))
    ((cons st ss) (list* st (muk-mplus ss ss2)))))
(define (muk-unit st) (list* st muk-mzero))
(define (muk-bind ss goal)
  (match ss
    ('() muk-mzero)
    ((? procedure?) (thunk (muk-bind (ss) goal)))
    ((cons st ss) (muk-mplus (goal st) (muk-bind ss goal)))))

(def (pair-components (cons a d)) (list a d))
(define (vector-components vec) (vector->list vec))
(define (struct-components str) (vector-components (struct->vector str)))
;(define (hash-components hsh) (hash->list hsh))  ; TODO: generic key sorting
(define (muk-split aggs)
  (forf components = (nothing)
        (list pred make-components) <- `((,pair? ,pair-components)
                                         (,vector? ,vector-components)
                                         (,struct? ,struct-components))
        #:break (just? components)
        (if (andmap pred aggs) (just (map make-components aggs)) components)))
(def (muk-rebuild agg components)
  rebuild =
  (cond ((pair? agg) (curry apply cons))
        ((vector? agg) list->vector)
        ((struct? agg)
         (lets (values sty _) = (struct-info agg)
               (compose1 (curry apply (struct-type-make-constructor sty))
                         cdr))))
  (rebuild components))

(define (muk-term->vars term)
  (define (recur xs) (foldl set-union (set) (map muk-term->vars xs)))
  (match term
    ((muk-var _) (set term))
    ((muk-func _ args) (recur args))
    (_ (match (muk-split (list term))
         ((nothing) (set))
         ((just (list components)) (recur components))))))

(module+ test
  (lets
    vars = (map muk-var (range 3))
    (list v0 v1 v2) = vars
    f0 = (muk-func 'zero (list v0 v1))
    f1 = (muk-func 'one (list v2 f0))
    f2 = (muk-func 'two (list f0 f1 v1))
    (begin
      (check-equal?
        (map muk-term->vars vars)
        (map set vars))
      (check-equal?
        (muk-term->vars f0)
        (set v0 v1))
      (check-equal?
        (muk-term->vars f1)
        (set v0 v1 v2))
      (check-equal?
        (muk-term->vars f2)
        (set v0 v1 v2))
      )))

(def (muk-sub-get-term st term)
  (muk-state sub-vars sub-funcs func-deps func-interps next-var) = st
  (if (muk-func? term)
    (match (dict-get sub-funcs term)
      ((nothing)
       (lets
         term-var = next-var
         next-var = (muk-var-next next-var)
         sub-funcs = (dict-add sub-funcs term term-var)
         func-deps = (forf
           func-deps = func-deps
           vr <- (muk-term->vars term)
           deps = (set-add (dict-ref func-deps vr (set)) term)
           (dict-set func-deps vr deps))
         st = (muk-state sub-vars sub-funcs func-deps func-interps next-var)
         (list st term-var)))
      ((just expected) (list st expected)))
    (list st term)))

(define (muk-normalize-get st term)
  (apply muk-sub-get-term (muk-normalize st term)))

(def (muk-normalize st term)
  normalize-get = (fn (st args)
    (forf (list st normalized) = (list st '())
          arg <- (reverse args)
          (list st narg) = (muk-normalize-get st arg)
          (list st (list* narg normalized))))
  (muk-state sub-vars sub-funcs func-deps func-interps next-var) = st
  (match term
    ((muk-var _) (list st (muk-sub-get-var sub-vars term)))
    ((muk-func name args)
     (lets (list st normalized) = (normalize-get st args)
           op = (dict-ref func-interps name)
           (list st (apply op normalized))))
    (_ (match (muk-split (list term))
         ((nothing) (list st term))
         ((just (list components))
          (lets (list st ncomps) = (normalize-get st components)
                (list st (muk-rebuild term ncomps))))))))

(module+ test
  (lets
    st = (:=* muk-state-empty (muk-var 3) 'next-var)
    id-func-op = (fn (fname) (lambda xs (muk-func fname xs)))
    st = (forf st = st
               fname <- (list 'zero 'one 'two)
               ((muk-state-interpret fname (id-func-op fname)) st))
    id-func = (fn (name args) (apply (id-func-op name) args))
    vars = (map muk-var (range 5))
    (list v0 v1 v2 v3 v4) = vars
    f0 = (id-func 'zero (list v0 v1))
    f1 = (id-func 'one (list v2 f0))
    f2 = (id-func 'two (list f0 f1 f0 v1))
    (list _ nf0) = (muk-normalize st f0)
    (list _ nf1) = (muk-normalize st f1)
    (list _ nf2) = (muk-normalize st f2)
    (begin
      (check-equal? (muk-term->vars nf0) (muk-term->vars f0))
      (check-equal? (muk-term->vars nf1) (set v2 v3))
      (check-equal? (muk-term->vars nf2) (set v4 v3 v1))
      )))

(def (muk-unify sub e0 e1)
  e0 = (muk-sub-get-var sub e0)
  e1 = (muk-sub-get-var sub e1)
  (if (equal? e0 e1) (just sub)
    (lets
      (list e0 e1) = (if (muk-var? e1) (list e1 e0) (list e0 e1))
      (if (muk-var? e0) (just (muk-sub-add sub e0 e1))
        (begin/with-monad maybe-monad
          components <- (muk-split (list e0 e1))
          (monad-foldl maybe-monad
            (fn (sub (list e0c e1c)) (muk-unify sub e0c e1c)) sub
            (zip components)))))))

(def (muk-var->symbol (muk-var name))
  (string->symbol (string-append "_." (number->string name))))
(def (muk-reify-var sub vr vtrans)
  vr = (muk-sub-get-var sub vr)
  (if (muk-var? vr) (vtrans vr)
    (match (muk-split (list vr))
      ((nothing) vr)
      ((just (list components))
       (muk-rebuild
         vr (map (fn (vr) (muk-reify-var sub vr vtrans)) components))))))
(define (muk-reify vtrans vrs states)
  (forl (muk-state sub _ _ _ _) <- states
        (forl vr <- vrs
              (muk-reify-var sub vr vtrans))))

(def ((== e0 e1) (muk-state sub sub-func func-deps func-interps next))
  (match (muk-unify sub e0 e1)
    ((nothing) muk-mzero)
    ((just sub) (muk-unit (muk-state sub sub-func func-deps func-interps next)))))

(define ((call/var f) st)
  ((f (:.* st 'next-var)) (:~* st muk-var-next 'next-var)))

(define ((conj g0 g1) st) (muk-bind (g0 st) g1))
(define ((disj g0 g1) st) (muk-mplus (g0 st) (g1 st)))

(define-syntax Zzz
  (syntax-rules () ((_ goal) (lambda (st) (thunk (goal st))))))

(define-syntax conj*
  (syntax-rules ()
    ((_) muk-unit)
    ((_ g0) g0)
    ((_ g0 gs ...) (conj g0 (conj* gs ...)))))
(define-syntax disj*-cont
  (syntax-rules ()
    ((_ g0) (Zzz g0))
    ((_ g0 gs ...) (disj (Zzz g0) (disj*-cont gs ...)))))
(define-syntax disj*
  (syntax-rules ()
    ((_) (const muk-zero))
    ((_ g0) g0)
    ((_ gs ...) (disj*-cont gs ...))))

(define (muk-force ss) (if (procedure? ss) (muk-force (ss)) ss))
(define (muk-take n ss)
  (if (= 0 n) '()
    (match (muk-force ss)
      ('() '())
      ((cons st ss) (list* st (muk-take (- n 1) ss))))))
(define (muk-take-all ss) (muk-take -1 ss))

(module+ test
  (define (reify-states name states)
    (muk-reify muk-var->symbol (list (muk-var name)) states))
  (define (one-and-two x) (conj* (== x 1) (== x 2)))
  (check-equal?
    (muk-take-all ((call/var one-and-two) muk-state-empty))
    '())
  (check-equal?
    (reify-states 0 (muk-take-all
                      ((call/var (fn (x) (== x x))) muk-state-empty)))
    '((_.0)))
  (define (fives x) (disj* (== x 5) (fives x)))
  (check-equal?
    (reify-states 0 (muk-take 1 ((call/var fives) muk-state-empty)))
    '((5)))
  (define (sixes x) (disj* (== x 6) (sixes x)))
  (define fives-and-sixes
    (call/var (lambda (x) (disj (fives x) (sixes x)))))
  (lets
    (list st0 st1) = (muk-take 2 (fives-and-sixes muk-state-empty))
    (check-equal?
      (reify-states 0 (list st0 st1))
      '((5) (6)))
    )
  (record thing one two)
  (for_
    build <- (list cons vector thing)
    rel = (call/var
            (lambda (x) (call/var
                          (lambda (y) (conj (== (build 1 y) x) (== y 2))))))
    (check-equal?
      (reify-states
        0 (muk-take 1 (rel muk-state-empty)))
      `((,(build 1 2)))))
  )
