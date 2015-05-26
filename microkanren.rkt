#lang racket/base
; variant of: http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf
(provide
  ==
  call/var
  conj
  conj-seq
  conj*
  conj*-seq
  disj
  disj*
  interpret
  muk-conj-conc
  muk-conj-seq
  muk-eval
  muk-func-app
  muk-mzero
  muk-reify
  muk-state-empty
  muk-sub-get-var
  muk-sub-prefix
  muk-success
  muk-take
  muk-take-all
  muk-term?
  muk-unify-and-update
  muk-unit
  muk-var
  muk-var?
  muk-var->symbol
  Zzz
  )

(require
  "cursor.rkt"
  "dict.rkt"
  "list.rkt"
  "maybe.rkt"
  "monad.rkt"
  "record.rkt"
  "repr.rkt"
  "sugar.rkt"
  racket/dict
  racket/function
  racket/list
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
  (muk-func-app name args))
(def (muk-var-next (muk-var idx)) (muk-var (+ 1 idx)))
(record muk-state
        bound-vars sub-vars sub-funcs func-deps func-interps next-var)
(define muk-state-empty (muk-state '() (hash) (hash) (hash) (hash) (muk-var 0)))
(define (muk-sub-get-var st vr)
  (let loop ((sub (:.* st 'sub-vars)) (vr vr))
    (match (if (muk-var? vr) (dict-get sub vr) (nothing))
      ((nothing) vr)
      ((just vr) (loop sub vr)))))
(define (muk-sub-add st vr val)
  (:~* (:~* st (lambda (bs) (dict-add bs vr val)) 'sub-vars)
       (curry list* vr) 'bound-vars))
(define (muk-state-interpret st interpretations)
  (:~* st (fn (func-interps)
              (forf
                interps = func-interps
                (cons name op) <- (dict->list interpretations)
                (dict-set interps name op)))
       'func-interps))
(def (muk-sub-prefix (muk-state vars-old _ _ _ _ _)
                     (muk-state vars-new _ _ _ _ _))
  (let loop ((current vars-new))
    (if (eq? current vars-old) '()
      (match current
        ((cons vr more) (list* vr (loop more)))))))

(module+ test
  (lets
    s0 = '(d c b a)
    s1 = (list* 'g 'f 'e s0)
    (check-equal?
      (apply muk-sub-prefix
             (map (fn (bvs) (:=* muk-state-empty bvs 'bound-vars))
                  (list s0 s1)))
      '(g f e))))

(records muk-computation
  (muk-success)
  (muk-conj-conc c0 c1)
  (muk-conj-seq c0 c1)
  )

(define (muk-step-depth st comp depth)
  (define next-depth (- depth 1))
  (if (= depth 0) (list (list st comp))
    (append*
      (match comp
        ((muk-success) (list (list (list st comp))))
        ((muk-conj-conc c0 c1)
         (forl (list st c0) <- (muk-step-depth st c0 depth)
               (forl (list st c1) <- (muk-step-depth st c1 depth)
                     (list st (match* (c0 c1)
                                (((muk-success) _) c1)
                                ((_ (muk-success)) c0)
                                ((_ _) (muk-conj-conc c0 c1)))))))
        ((muk-conj-seq c0 c1)
         (forl (list st c0) <- (muk-step-depth st c0 depth)
               (match c0
                 ((muk-success) (muk-step-depth st c1 depth))
                 (_ (list (list st (muk-conj-seq c0 c1)))))))
        (_ (forl (list st comp) <- (comp st)
                 (muk-step-depth st comp next-depth)))))))

(def (muk-eval-loop pending depth)
  (list finished pending) =
  (forf
    (list finished unfinished) = '(() ())
    (list st comp) <- (append* (forl (list st comp) <- pending
                                     (muk-step-depth st comp depth)))
    (match comp
      ((muk-success) (list (list* st finished) unfinished))
      (_ (list finished (list* (list st comp) unfinished)))))
  (append finished (if (null? pending)
                     '() (thunk (muk-eval-loop pending depth)))))

(define (muk-eval st comp (depth 1))
  (muk-eval-loop (list (list st comp)) depth))

(define conj muk-conj-conc)
(define conj-seq muk-conj-seq)
(define ((disj g0 g1) st) (list (list st g0) (list st g1)))

(define (muk-force ss) (if (procedure? ss) (muk-force (ss)) ss))

(define muk-mzero '())
(define (muk-unit st) (list* (list st (muk-success)) muk-mzero))

(define (muk-split aggs)
  (forf components = (nothing)
        pred <- (list pair? vector? hash? set? struct?)
        #:break (just? components)
        (if (andmap pred aggs) (just (map value->repr aggs)) components)))
(define muk-rebuild repr->value)

(define (muk-term->vars term)
  (define (recur xs) (foldl set-union (set) (map muk-term->vars xs)))
  (match term
    ((muk-var _) (set term))
    ((muk-func-app _ args) (recur args))
    (_ (match (muk-split (list term))
         ((nothing) (set))
         ((just (list (repr _ components))) (recur components))))))

(module+ test
  (lets
    vars = (map muk-var (range 3))
    (list v0 v1 v2) = vars
    f0 = (muk-func-app 'zero (list v0 v1))
    f1 = (muk-func-app 'one (list v2 f0))
    f2 = (muk-func-app 'two (list f0 f1 v1))
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
  (muk-state bvars sub-vars sub-funcs func-deps func-interps next-var) = st
  (if (muk-func-app? term)
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
         st = (muk-state
                bvars sub-vars sub-funcs func-deps func-interps next-var)
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
  (muk-state bvars sub-vars sub-funcs func-deps func-interps next-var) = st
  (match term
    ((muk-var _) (list st (muk-sub-get-var st term)))
    ((muk-func-app name args)
     (lets (list st normalized) = (normalize-get st args)
           op = (dict-ref func-interps name)
           new-term = (apply op normalized)
           (if (equal? new-term term) (list st new-term)
             (muk-normalize st new-term))))
    (_ (match (muk-split (list term))
         ((nothing) (list st term))
         ((just (list (repr type components)))
          (lets (list st ncomps) = (normalize-get st components)
                (list st (muk-rebuild (repr type ncomps)))))))))

(module+ test
  (lets
    st = (:=* muk-state-empty (muk-var 3) 'next-var)
    id-func-op = (fn (fname) (lambda xs (muk-func-app fname xs)))
    interps = (forl fname <- (list 'zero 'one 'two)
                    (cons fname (id-func-op fname)))
    st = (muk-state-interpret st interps)
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

(define (muk-normalize-term st term)
  (if (muk-term? term) (muk-normalize-get st term) (list st term)))

(def (muk-unify st e0 e1)
  (list st e0) = (muk-normalize-term st e0)
  (list st e1) = (muk-normalize-term st e1)
  (muk-state bvars sub-vars sub-funcs func-deps func-interps next-var) = st
  (if (equal? e0 e1) (just st)
    (lets
      (list e0 e1) = (if (muk-var? e1) (list e1 e0) (list e0 e1))
      (if (muk-var? e0) (just (muk-sub-add st e0 e1))
        (begin/with-monad maybe-monad
          reprs <- (muk-split (list e0 e1))
          components = (forl (repr type components) <- reprs
                             (list* type components))
          (list l0 l1) = (map length components)
          _ <- (if (= l0 l1) (just (void)) (nothing))
          (monad-foldl maybe-monad
            (fn (st (list e0c e1c)) (muk-unify st e0c e1c)) st
            (zip components)))))))

(def (muk-func-app-update st term-old)
  (list st term-new) = (muk-normalize st term-old)
  (if (equal? term-old term-new) (just st)
    (lets
      (list st expected-old) = (muk-sub-get-term st term-old)
      (muk-state bvars sub-vars sub-funcs func-deps func-interps next-var) = st
      func-deps =
      (forf func-deps = func-deps
            old-var <- (muk-term->vars term-old)
            ; TODO: if empty, remove completely
            (dict-update func-deps old-var
                         (fn (terms) (set-remove terms term-old))))
      sub-funcs = (dict-remove sub-funcs term-old)
      st = (muk-state bvars sub-vars sub-funcs func-deps func-interps next-var)
      (list st expected-new) = (muk-sub-get-term st term-new)
      (muk-unify st expected-old expected-new))))

(define (muk-unify-and-update st e0 e1)
  (begin/with-monad maybe-monad
    st-new <- (muk-unify st e0 e1)
    (letn loop (list st-old st-new) = (list st st-new)
      (if (eq? st-old st-new) (just st-new)
        (lets
          (muk-state
            bvars sub-vars sub-funcs func-deps func-interps next-var) = st-new
          (if (dict-empty? func-deps) (just st-new)
            (begin/monad
              new = (muk-sub-prefix st-old st-new)
              fterms = (foldl set-union (set)
                              (forl vr <- new (dict-ref func-deps vr (set))))
              st-new-new <- (monad-foldl maybe-monad muk-func-app-update st-new
                                         (set->list fterms))
              (loop (list st-new st-new-new)))))))))

(def (muk-var->symbol (muk-var name))
  (string->symbol (string-append "_." (number->string name))))
(def (muk-reify-term st term vtrans)
  term = (muk-sub-get-var st term)
  (match term
    ((muk-var _) (vtrans term))
    ((muk-func-app name args)
     `(,name ,@(map (fn (el) (muk-reify-term st el vtrans)) args)))
    (_ (match (muk-split (list term))
         ((nothing) term)
         ((just (list (repr type components)))
          (muk-rebuild
            (repr type (map (fn (el) (muk-reify-term st el vtrans))
                            components))))))))
(define (muk-reify vtrans vrs states)
  (forl st <- states
        reify = (fn (term) (muk-reify-term st term vtrans))
        vars = (map reify vrs)
        func-apps =
        (forl (cons fterm val) <- (dict->list (:.* st 'sub-funcs))
              `(,(reify fterm) == ,(reify val)))
        constraints = (if (null? func-apps) '() `(: ,@func-apps))
        `(,@vars ,@constraints)))

(define ((== e0 e1) st)
  (match (muk-unify-and-update st e0 e1)
    ((nothing) muk-mzero)
    ((just st) (muk-unit st))))

(define ((call/var f) st)
  (list (list (:~* st muk-var-next 'next-var) (f (:.* st 'next-var)))))

(define ((interpret interpretations) st)
  (muk-unit (muk-state-interpret st interpretations)))

(define-syntax Zzz
  (syntax-rules () ((_ goal) (lambda (st) (list (list st goal))))))

(define-syntax conj*
  (syntax-rules ()
    ((_) muk-unit)
    ((_ g0) (Zzz g0))
    ((_ g0 gs ...) (conj (Zzz g0) (conj* gs ...)))))
(define-syntax disj*
  (syntax-rules ()
    ((_) (const muk-mzero))
    ((_ g0) (Zzz g0))
    ((_ g0 gs ...) (disj (Zzz g0) (disj* gs ...)))))

(define-syntax conj*-seq
  (syntax-rules ()
    ((_) muk-unit)
    ((_ g0) (Zzz g0))
    ((_ g0 gs ...) (conj-seq (Zzz g0) (conj* gs ...)))))

(define (muk-take n ss)
  (if (= 0 n) '()
    (match (muk-force ss)
      ('() '())
      ((cons st ss) (list* st (muk-take (- n 1) ss))))))
(define (muk-take-all ss) (muk-take -1 ss))

(module+ test
  (define (run comp) (muk-eval muk-state-empty comp))
  (define (reify-states name states)
    (muk-reify muk-var->symbol (list (muk-var name)) states))
  (check-equal?
    (muk-take-all (run (== '#(a b) '#(c))))
    '())
  (define (one-and-two x) (conj* (== x 1) (== x 2)))
  (check-equal?
    (muk-take-all (run (call/var one-and-two)))
    '())
  (check-equal?
    (reify-states 0 (muk-take-all (run (call/var (fn (x) (== x x))))))
    '((_.0)))
  (define (fives x) (disj* (== x 5) (fives x)))
  (check-equal?
    (reify-states 0 (muk-take 1 (run (call/var fives))))
    '((5)))
  (define (sixes x) (disj* (== x 6) (sixes x)))
  (define fives-and-sixes
    (call/var (lambda (x) (disj (fives x) (sixes x)))))
  (lets
    (list st0 st1) = (muk-take 2 (run fives-and-sixes))
    (check-equal?
      (list->set (reify-states 0 (list st0 st1)))
      (list->set '((5) (6))))
    )
  (record thing one two)
  (for_
    build <- (list cons vector thing)
    rel = (call/var
            (lambda (x) (call/var
                          (lambda (y) (conj (== (build 1 y) x) (== y 2))))))
    (check-equal?
      (reify-states 0 (muk-take 1 (run rel)))
      `((,(build 1 2)))))
  )
