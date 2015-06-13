#lang racket/base
; variant of: http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf
(provide
  ==
  call/var
  let/vars
  conj
  conj-seq
  conj*
  conj*-seq
  disj
  disj*
  disj+-Zzz
  interpret
  muk-conj-conc
  muk-conj-seq
  muk-eval
  muk-func-app
  muk-mzero
  muk-pause
  muk-reify
  muk-state-empty
  muk-step-unification
  muk-sub-get-var
  muk-sub-prefix
  muk-success
  muk-take
  muk-term?
  muk-unification
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
(define (muk-var-next (name '?)) (muk-var (gensym name)))
(record muk-state bound-vars sub-vars sub-funcs func-deps func-interps)
(define muk-state-empty (muk-state '() (hasheq) (hash) (hash) (hash)))
(define (muk-sub-get-var st vr)
  (define sub (muk-state-sub-vars st))
  (let loop ((vr vr))
    (if (muk-var? vr)
      (let ((result (hash-ref sub (muk-var-name vr) vr)))
        (if (eq? result vr) vr (loop result)))
      vr)))
(def (muk-sub-add (muk-state bound-vars sub-vars sfs fds fis) vr val)
  sub-vars = (hash-set sub-vars (muk-var-name vr) val)
  bound-vars = (list* vr bound-vars)
  (muk-state bound-vars sub-vars sfs fds fis))
(define (muk-state-interpret st interpretations)
  (:~* st (fn (func-interps)
              (forf
                interps = func-interps
                (cons name op) <- (dict->list interpretations)
                (hash-set interps name op)))
       'func-interps))
(def (muk-sub-prefix (muk-state vars-old _ _ _ _) (muk-state vars-new _ _ _ _))
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
  (muk-success result)
  (muk-unification e0 e1)
  (muk-conj-conc cost c0 c1)
  (muk-conj-seq cost c0 c1)
  (muk-pause paused)
  )

(define muk-cost-unknown #f)
(define muk-cost-unification 0)
(define (muk-cost-min c0 c1)
  (if c0 (if c1 (min c0 c1) c0) c1))
(define (muk-computation-cost comp)
  (match comp
    ((muk-success _) muk-cost-unknown)
    ((muk-unification e0 e1) muk-cost-unification)
    ((muk-conj-conc cost c0 c1) cost)
    ((muk-conj-seq cost c0 c1) cost)
    ((muk-pause _) muk-cost-unknown)
    (_ muk-cost-unknown)))
(define (muk-comps->cost c0 c1)
  (muk-cost-min (muk-computation-cost c0) (muk-computation-cost c1)))

(define (muk-step-conj-conc cont arg st c0 c1)
  (append* (forl (list st c0) <- (cont st c0 arg)
                 (forl (list st c1) <- (cont st c1 arg)
                       (list st (match* (c0 c1)
                                  (((muk-success _) _) c1)
                                  ((_ (muk-success (? void?))) c0)
                                  ((_ (muk-success _)) (conj-seq c0 c1))
                                  ((_ _) (conj c0 c1))))))))
(define (muk-step-conj-seq cont arg st c0 c1)
  (append* (forl (list st c0) <- (cont st c0 arg)
                 (match c0
                   ((muk-success _) (cont st c1 arg))
                   (_ (list (list st (conj-seq c0 c1))))))))
(define (muk-step-results cont arg results)
  (append* (forl (list st comp) <- results (cont st comp arg))))

(define (muk-step-known st comp cost-max)
  (define (cost? cost) (and cost (<= cost cost-max)))
  (match comp
    ((muk-conj-conc (? cost?) c0 c1)
     (muk-step-conj-conc muk-step-known cost-max st c0 c1))
    ((muk-conj-seq (? cost?) c0 c1)
     (muk-step-conj-seq muk-step-known cost-max st c0 c1))
    ((muk-unification e0 e1) (muk-step-unification st e0 e1))
    (_ (list (list st comp)))))

(define (muk-step-depth st comp depth)
  (define next-depth (- depth 1))
  (if (= depth 0) (list (list st comp))
    (match comp
      ((muk-success _) (list (list st comp)))
      ((muk-conj-conc cost c0 c1)
       (muk-step-conj-conc muk-step depth st c0 c1))
      ((muk-conj-seq cost c0 c1)
       (muk-step-conj-seq muk-step depth st c0 c1))
      ((muk-pause paused) (list (list st paused)))
      (_ (muk-step-results muk-step next-depth (comp st))))))

(define (muk-step st comp depth)
  (let ((cost (muk-computation-cost comp)))
    (if cost (muk-step-results muk-step depth (muk-step-known st comp cost))
      (muk-step-depth st comp depth))))

(def (muk-eval-loop pending depth)
  (list finished pending) =
  (forf
    (list finished unfinished) = '(() ())
    (list st comp) <- (muk-step-results muk-step depth pending)
    (match comp
      ((muk-success _) (list (list* st finished) unfinished))
      (_ (list finished (list* (list st comp) unfinished)))))
  (append finished (if (null? pending)
                     '() (thunk (muk-eval-loop pending depth)))))

(define (muk-eval st comp (depth 1))
  (muk-eval-loop (list (list st comp)) depth))

(define (conj c0 c1) (muk-conj-conc (muk-comps->cost c0 c1) c0 c1))
(define (conj-seq c0 c1) (muk-conj-seq (muk-computation-cost c0) c0 c1))
(define ((disj g0 g1) st) (list (list st g0) (list st g1)))

(define (muk-force ss) (if (procedure? ss) (muk-force (ss)) ss))

(define muk-mzero '())
(define (muk-unit st (result (void)))
  (list* (list st (muk-success result)) muk-mzero))

(define split-entries
  (list repr-entry-pair repr-entry-vector repr-entry-struct repr-entry-hash))
(define (muk-split aggs)
  (forf components = (nothing)
        (list found? val->type val->components) <- split-entries
        #:break (just? components)
        (if (andmap found? aggs)
          (just (forl agg <- aggs
                      (repr (val->type agg) (val->components agg))))
          components)))
(define muk-rebuild repr->value)

(define (muk-term->vars term)
  (define (recur xs) (foldl set-union (set) (map muk-term->vars xs)))
  (match term
    ((muk-var _) (set term))
    ((muk-func-app _ args) (recur args))
    (_ (match (muk-split (list term))
         ((nothing) (set))
         ((just (list rpr)) (recur (repr-components rpr)))))))

(module+ test
  (lets
    vars = (map muk-var '(a b c))
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
  (muk-state bvars sub-vars sub-funcs func-deps func-interps) = st
  (if (muk-func-app? term)
    (match (dict-get sub-funcs term)
      ((nothing)
       (lets
         term-var = (muk-var-next)
         sub-funcs = (hash-set sub-funcs term term-var)
         func-deps = (forf
           func-deps = func-deps
           vr <- (muk-term->vars term)
           deps = (set-add (hash-ref func-deps vr (set)) term)
           (hash-set func-deps vr deps))
         st = (muk-state bvars sub-vars sub-funcs func-deps func-interps)
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
  (muk-state bvars sub-vars sub-funcs func-deps func-interps) = st
  (match term
    ((muk-var _) (list st (muk-sub-get-var st term)))
    ((muk-func-app name args)
     (lets (list st normalized) = (normalize-get st args)
           op = (hash-ref func-interps name)
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
    st = muk-state-empty
    id-func-op = (fn (fname) (lambda xs (muk-func-app fname xs)))
    interps = (forl fname <- (list 'zero 'one 'two)
                    (cons fname (id-func-op fname)))
    st = (muk-state-interpret st interps)
    id-func = (fn (name args) (apply (id-func-op name) args))
    vars = (map muk-var '(a b c d e))
    (list v0 v1 v2 v3 v4) = vars
    f0 = (id-func 'zero (list v0 v1))
    f1 = (id-func 'one (list v2 f0))
    f2 = (id-func 'two (list f0 f1 f0 v1))
    (list _ nf0) = (muk-normalize st f0)
    (list _ nf1) = (muk-normalize st f1)
    (list _ nf2) = (muk-normalize st f2)
    (begin
      (check-equal? (muk-term->vars nf0) (muk-term->vars f0))
      (check-true (set-member? (muk-term->vars nf1) v2))
      (check-true (set-member? (muk-term->vars nf2) v1))
      )))

(define (muk-normalize-term st term)
  (if (muk-term? term) (muk-normalize-get st term) (list st term)))

(def (muk-unify st e0 e1)
  (list st e0) = (muk-normalize-term st e0)
  (list st e1) = (muk-normalize-term st e1)
  (cond
    ((eq? e0 e1) (just st))
    ((muk-var? e0) (just (muk-sub-add st e0 e1)))
    ((muk-var? e1) (just (muk-sub-add st e1 e0)))
    (else
      (match* (e0 e1)
        (((cons h0 t0) (cons h1 t1))
         (match (muk-unify st h0 h1)
           ((nothing) (nothing))
           ((just st) (muk-unify st t0 t1))))
        ((_ _)
         (if (equal? e0 e1) (just st)
           (begin/with-monad maybe-monad
             reprs <- (muk-split (list e0 e1))
             components = (map repr-components reprs)
             (list l0 l1) = (map length components)
             _ <- (if (= l0 l1) (just (void)) (nothing))
             (monad-foldl maybe-monad
                          (fn (st (list e0c e1c)) (muk-unify st e0c e1c)) st
                          (zip components)))))))))

(def (muk-func-app-update st term-old)
  (list st term-new) = (muk-normalize st term-old)
  (if (equal? term-old term-new) (just st)
    (lets
      (list st expected-old) = (muk-sub-get-term st term-old)
      (muk-state bvars sub-vars sub-funcs func-deps func-interps) = st
      func-deps =
      (forf func-deps = func-deps
            old-var <- (muk-term->vars term-old)
            ; TODO: if empty, remove completely
            (hash-update func-deps old-var
                         (fn (terms) (set-remove terms term-old))))
      sub-funcs = (hash-remove sub-funcs term-old)
      st = (muk-state bvars sub-vars sub-funcs func-deps func-interps)
      (list st expected-new) = (muk-sub-get-term st term-new)
      (muk-unify st expected-old expected-new))))

(define (muk-unify-and-update st e0 e1)
  (match (muk-unify st e0 e1)
    ((nothing) (nothing))
    ((just st-new)
     (letn loop (values st-old st-new) = (values st st-new)
       (if (eq? st-old st-new) (just st-new)
         (lets
           (muk-state bvars sub-vars sub-funcs func-deps func-interps) = st-new
           (if (hash-empty? func-deps) (just st-new)
             (lets
               new = (muk-sub-prefix st-old st-new)
               fterms = (foldl set-union (set)
                               (forl vr <- new (hash-ref func-deps vr (set))))
               (match (monad-foldl maybe-monad muk-func-app-update st-new
                                   (set->list fterms))
                 ((nothing) (nothing))
                 ((just st-new-new) (loop st-new st-new-new)))))))))))

(define (no-split? v) (not (or (vector? v) (struct? v) (hash? v))))
(def (muk-var->symbol (muk-var name))
  (string->symbol (string-append "_." (symbol->string name))))
(def (muk-reify-term st term vtrans)
  term = (muk-sub-get-var st term)
  (match term
    ((muk-var _) (vtrans term))
    ((cons hd tl) (cons (muk-reify-term st hd vtrans)
                        (muk-reify-term st tl vtrans)))
    ((? no-split?) term)
    ((muk-func-app name args)
     `(,name ,@(map (fn (el) (muk-reify-term st el vtrans)) args)))
    (_ (match (muk-split (list term))
         ((nothing) term)
         ((just (list (repr type components)))
          (muk-rebuild
            (repr type (map (fn (el) (muk-reify-term st el vtrans))
                            components))))))))
(def (muk-reify vtrans vr st)
  reify = (fn (term) (muk-reify-term st term vtrans))
  reified-var = (reify vr)
  func-apps =
  (forl (cons fterm val) <- (hash->list (muk-state-sub-funcs st))
        `(,(reify fterm) == ,(reify val)))
  constraints = (if (null? func-apps) '() `(: ,@func-apps))
  (if (null? constraints) reified-var
    `(,reified-var ,@constraints)))

(define (muk-step-unification st e0 e1)
  (match (muk-unify-and-update st e0 e1)
    ((nothing) muk-mzero)
    ((just st) (muk-unit st))))
(define == muk-unification)

(define (call/var f (name '?)) (f (muk-var-next name)))
(define-syntax let/vars
  (syntax-rules ()
    ((_ () body) body)
    ((_ () body ...) (begin body ...))
    ((_ (qvar qvars ...) body ...)
     (call/var (lambda (qvar) (let/vars (qvars ...) body ...)) 'qvar))))

(define ((interpret interpretations) st)
  (muk-unit (muk-state-interpret st interpretations)))

(define-syntax Zzz
  (syntax-rules () ((_ goal) (lambda (st) (list (list st goal))))))

(define-syntax conj*
  (syntax-rules ()
    ((_) muk-unit)
    ((_ g0) g0)
    ((_ g0 gs ...) (conj g0 (conj* gs ...)))))
(define-syntax disj*
  (syntax-rules ()
    ((_) (const muk-mzero))
    ((_ g0) g0)
    ((_ g0 gs ...) (disj g0 (disj* gs ...)))))
(define-syntax disj+-Zzz
  (syntax-rules ()
    ((_ g0) g0)
    ((_ g0 gs ...) (Zzz (disj* g0 gs ...)))))

(define-syntax conj*-seq
  (syntax-rules ()
    ((_) muk-unit)
    ((_ g0) g0)
    ((_ g0 gs ...) (conj-seq g0 (conj* gs ...)))))

(define (muk-take n ss)
  (if (and n (zero? n)) '()
    (match (muk-force ss)
      ('() '())
      ((cons st ss) (list* st (muk-take (and n (- n 1)) ss))))))

(module+ test
  (define (run comp) (muk-eval muk-state-empty comp))
  (define (reify-states vr states)
    (forl st <- states (muk-reify muk-var->symbol vr st)))
  (check-equal?
    (muk-take #f (run (== '#(a b) '#(c))))
    '())
  (define (one-and-two x) (conj* (== x 1) (== x 2)))
  (check-equal?
    (muk-take #f (run (call/var one-and-two)))
    '())
  (let/vars (x)
    (check-equal? (reify-states x (muk-take #f (run (== x x))))
                  `(,(muk-var->symbol x))))
  (define (fives x) (disj+-Zzz (== x 5) (fives x)))
  (let/vars (x)
    (check-equal?
      (reify-states x (muk-take 1 (run (fives x))))
      '(5)))
  (define (sixes x) (disj+-Zzz (== x 6) (sixes x)))
  (define (fives-and-sixes x) (disj (fives x) (sixes x)))
  (call/var (fn (x)
    (list st0 st1) = (muk-take 2 (run (fives-and-sixes x)))
    (check-equal?
      (list->set (reify-states x (list st0 st1)))
      (list->set '(5 6)))))

  (record thing one two)
  (for_
    build <- (list cons vector thing)
    (let/vars (x y)
      (check-equal?
        (reify-states x (muk-take 1 (run (conj (== (build 1 y) x) (== y 2)))))
        `(,(build 1 2)))))
  )
