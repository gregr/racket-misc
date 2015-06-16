#lang racket/base
; variant of: http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf
(provide
  ==
  call/var
  let/vars
  conj
  conj-seq
  disj
  interpret
  muk-conj-conc
  muk-conj-seq
  muk-cost-goal
  muk-eval
  muk-fof-apply
  muk-func-app
  muk-goal
  muk-mzero
  muk-pause
  muk-reify
  muk-state-empty
  muk-sub-get
  muk-sub-prefix
  muk-success
  muk-take
  muk-term?
  muk-unification
  muk-unify
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
(record muk-fof-constraints func-interps func-deps sub-funcs)
(define muk-fof-constraints-empty (muk-fof-constraints (hash) (hash) (hash)))
(record muk-state bound-vars substitution constraints)
(define muk-state-empty (muk-state '() (hasheq) muk-fof-constraints-empty))
(def (muk-sub-get st vr)
  (muk-state bound-vars sub constraints) = st
  compress = (lambda (path result)
    (if (null? path) (values st result)
      (values (muk-state bound-vars
                         (forf sub = sub
                               (muk-var name) <- path
                               (hash-set sub name result))
                         constraints) result)))
  (let ((result (hash-ref sub (muk-var-name vr) vr)))
    (if (eq? result vr) (compress '() vr)
      (if (muk-var? result)
        (let loop ((vr result) (path (list vr)))
          (let ((result (hash-ref sub (muk-var-name vr) vr)))
            (if (eq? result vr) (compress (rest path) vr)
              (if (muk-var? result)
                (loop result (list* vr path))
                (compress path result)))))
        (compress '() result)))))
(def (muk-sub-add (muk-state bound-vars sub constraints) vr val)
  sub = (hash-set sub (muk-var-name vr) val)
  bound-vars = (list* vr bound-vars)
  (muk-state bound-vars sub constraints))
(define (muk-state-interpret st interpretations)
  (:~* st (fn (func-interps)
              (forf
                interps = func-interps
                (cons name op) <- (dict->list interpretations)
                (hash-set interps name op)))
       'constraints 'func-interps))
(def (muk-sub-prefix (muk-state bound-vars sub cxs))
  (values (muk-state '() sub cxs) bound-vars))

(records muk-computation
  (muk-success result)
  (muk-unification e0 e1)
  (muk-conj-conc cost c0 c1)
  (muk-conj-seq cost c0 c1)
  (muk-cost-goal cost goal)
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
    ((muk-cost-goal cost goal) cost)
    ((muk-pause _) muk-cost-unknown)
    (_ muk-cost-unknown)))
(define (muk-comps->cost c0 c1)
  (muk-cost-min (muk-computation-cost c0) (muk-computation-cost c1)))

(define (muk-goal st comp) (list (list st comp)))
(define muk-mzero '())
(define (muk-unit st (result (void))) (muk-goal st (muk-success result)))

(define == muk-unification)
(define (conj c0 c1) (muk-conj-conc (muk-comps->cost c0 c1) c0 c1))
(define (conj-seq c0 c1) (muk-conj-seq (muk-computation-cost c0) c0 c1))
(define ((disj g0 g1) st) (list (list st g0) (list st g1)))

(define (call/var f (name '?)) (f (muk-var-next name)))
(define-syntax let/vars
  (syntax-rules ()
    ((_ () body) body)
    ((_ () body ...) (begin body ...))
    ((_ (qvar qvars ...) body ...)
     (call/var (lambda (qvar) (let/vars (qvars ...) body ...)) 'qvar))))

(define-syntax Zzz
  (syntax-rules () ((_ goal) (lambda (st) (muk-goal st goal)))))

(define (muk-force ss) (if (procedure? ss) (muk-force (ss)) ss))

(define (muk-take n ss)
  (if (and n (zero? n)) '()
    (match (muk-force ss)
      ('() '())
      ((cons st ss) (list* st (muk-take (and n (- n 1)) ss))))))

(define ((interpret interpretations) st)
  (muk-unit (muk-state-interpret st interpretations)))

(define (muk-evaluator unify constrain)
  (define (muk-step-conj-conc cont arg st c0 c1)
    (for*/list ((r0 (in-list (cont st c0 arg)))
                (r1 (in-list (cont (first r0) c1 arg))))
               (lets (list _ c0) = r0
                     (list st c1) = r1
                     (list st (match* (c0 c1)
                                (((muk-success _) _) c1)
                                ((_ (muk-success (? void?))) c0)
                                ((_ _) (conj c0 c1)))))))
  (define (muk-step-conj-seq cont arg st c0 c1)
    (append* (forl (list st c0) <- (in-list (cont st c0 arg))
                   (match c0
                     ((muk-success _) (cont st c1 arg))
                     (_ (muk-goal st (conj-seq c0 c1)))))))
  (define (muk-step-results cont arg results)
    (append* (forl (list st comp) <- (in-list results) (cont st comp arg))))

  (define (muk-step-known st comp cost-max)
    (define (cost? cost) (and cost (<= cost cost-max)))
    (match comp
      ((muk-conj-conc (? cost?) c0 c1)
       (muk-step-conj-conc muk-step-known cost-max st c0 c1))
      ((muk-conj-seq (? cost?) c0 c1)
       (muk-step-conj-seq muk-step-known cost-max st c0 c1))
      ((muk-unification e0 e1) (unify st e0 e1))
      ((muk-cost-goal (? cost?) goal)
       (muk-step-results muk-step-known cost-max (goal st)))
      (_ (muk-goal st comp))))

  (define (muk-step-depth st comp depth)
    (define next-depth (- depth 1))
    (if (= depth 0) (muk-goal st comp)
      (match comp
        ((muk-success _) (muk-goal st comp))
        ((muk-conj-conc cost c0 c1)
         (muk-step-conj-conc muk-step depth st c0 c1))
        ((muk-conj-seq cost c0 c1)
         (muk-step-conj-seq muk-step depth st c0 c1))
        ((muk-pause paused) (muk-goal st paused))
        (_ (muk-step-results muk-step next-depth (comp st))))))

  (define (muk-step st comp depth)
    (let ((cost (muk-computation-cost comp)))
      (if cost (muk-step-results muk-step depth (muk-step-known st comp cost))
        (match (constrain st)
          ((nothing) muk-mzero)
          ((just st) (muk-step-depth st comp depth))))))

  (def (muk-eval-loop pending depth)
       (values finished pending) =
       (forf finished = '() unfinished = '()
             (list st comp) <- (in-list (muk-step-results muk-step depth pending))
             (match comp
               ((muk-success _) (values (list* st finished) unfinished))
               (_ (values finished (list* (list st comp) unfinished)))))
       (append finished (if (null? pending)
                          '() (thunk (muk-eval-loop pending depth)))))

  (define (muk-eval st comp (depth 1))
    (muk-eval-loop (muk-goal st comp) depth))

  muk-eval)

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

(def (muk-func-app-add st term)
  (muk-state bvars sub constraints) = st
  (muk-fof-constraints func-interps func-deps sub-funcs) = constraints
  (match (dict-get sub-funcs term)
    ((nothing)
     (lets term-var = (muk-var-next)
           sub-funcs = (hash-set sub-funcs term term-var)
           func-deps = (forf
                         func-deps = func-deps
                         vr <- (muk-term->vars term)
                         deps = (set-add (hash-ref func-deps vr (set)) term)
                         (hash-set func-deps vr deps))
           constraints = (muk-fof-constraints func-interps func-deps sub-funcs)
           st = (muk-state bvars sub constraints)
           (values st term-var)))
    ((just expected) (values st expected))))

(define (muk-sub-get-term st term)
  (if (muk-func-app? term) (muk-func-app-add st term) (values st term)))

(def (muk-normalize-get st term)
  (values st nterm) = (muk-normalize st term)
  (muk-sub-get-term st nterm))

(def ((muk-fof-apply name args result) st)
  (values st result-var) = (muk-normalize-get st (muk-func-app name args))
  (muk-goal st (== result-var result)))

(define (muk-normalize-get-args st args)
  (forf st = st normalized = '()
        arg <- (reverse args)
        (values st narg) = (muk-normalize-get st arg)
        (values st (list* narg normalized))))

(def (muk-func-app-normalize st term)
  (muk-func-app name args) = term
  (muk-state _ _ constraints) = st
  (muk-fof-constraints func-interps _ _) = constraints
  (values st normalized) = (muk-normalize-get-args st args)
  op = (hash-ref func-interps name)
  new-term = (apply op normalized)
  (if (equal? new-term term) (values st new-term)
    (muk-normalize st new-term)))

(def (muk-normalize st term)
  (match term
    ((muk-var _) (muk-sub-get st term))
    ((muk-func-app _ _) (muk-func-app-normalize st term))
    (_ (match (muk-split (list term))
         ((nothing) (values st term))
         ((just (list (repr type components)))
          (lets (values st ncomps) = (muk-normalize-get-args st components)
                (values st (muk-rebuild (repr type ncomps)))))))))

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
    (values _ nf0) = (muk-normalize st f0)
    (values _ nf1) = (muk-normalize st f1)
    (values _ nf2) = (muk-normalize st f2)
    (begin
      (check-equal? (muk-term->vars nf0) (muk-term->vars f0))
      (check-true (set-member? (muk-term->vars nf1) v2))
      (check-true (set-member? (muk-term->vars nf2) v1))
      )))

(define (muk-walk st term)
  (if (muk-var? term) (muk-sub-get st term) (values st term)))

(def (muk-unify st e0 e1)
  (values st e0) = (muk-walk st e0)
  (values st e1) = (muk-walk st e1)
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
  (values st term-new) = (muk-func-app-normalize st term-old)
  (if (equal? term-old term-new) (just st)
    (lets
      (values st expected-old) = (muk-sub-get-term st term-old)
      (muk-state bvars sub constraints) = st
      (muk-fof-constraints func-interps func-deps sub-funcs) = constraints
      func-deps =
      (forf func-deps = func-deps
            old-var <- (muk-term->vars term-old)
            ; TODO: if empty, remove completely
            (hash-update func-deps old-var
                         (fn (terms) (set-remove terms term-old))))
      sub-funcs = (hash-remove sub-funcs term-old)
      constraints = (muk-fof-constraints func-interps func-deps sub-funcs)
      st = (muk-state bvars sub constraints)
      (values st expected-new) = (muk-sub-get-term st term-new)
      (muk-unify st expected-old expected-new))))

(def (muk-fof-constrain st)
  (muk-state _ _ (muk-fof-constraints _ func-deps _)) = st
  (values st new) = (muk-sub-prefix st)
  (if (or (null? new) (hash-empty? func-deps)) (just st)
    (lets
      fterms = (foldl set-union (set)
                      (forl vr <- new (hash-ref func-deps vr (set))))
      (match (monad-foldl maybe-monad muk-func-app-update st
                          (set->list fterms))
        ((nothing) (nothing))
        ((just st-new) (muk-fof-constrain st-new))))))

(define (no-split? v) (not (or (vector? v) (struct? v) (hash? v))))
(def (muk-var->symbol (muk-var name))
  (string->symbol (string-append "_." (symbol->string name))))
(def (muk-reify-term st term vtrans)
  (values st term) = (muk-walk st term)
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
  (muk-state _ _ (muk-fof-constraints _ _ sub-funcs)) = st
  func-apps =
  (forl (cons fterm val) <- (hash->list sub-funcs)
        `(,(reify fterm) == ,(reify val)))
  constraints = (if (null? func-apps) '() `(: ,@func-apps))
  (if (null? constraints) reified-var
    `(,reified-var ,@constraints)))

(define (muk-step-unification st e0 e1)
  (match (muk-unify st e0 e1)
    ((nothing) muk-mzero)
    ((just st) (muk-unit st))))

(define muk-fof-eval (muk-evaluator muk-step-unification muk-fof-constrain))
(define muk-eval muk-fof-eval)

(module+ test
  (define (run comp) (muk-eval muk-state-empty comp))
  (define (reify-states vr states)
    (forl st <- states (muk-reify muk-var->symbol vr st)))
  (check-equal?
    (muk-take #f (run (== '#(a b) '#(c))))
    '())
  (define (one-and-two x) (conj (== x 1) (== x 2)))
  (check-equal?
    (muk-take #f (run (call/var one-and-two)))
    '())
  (let/vars (x)
    (check-equal? (reify-states x (muk-take #f (run (== x x))))
                  `(,(muk-var->symbol x))))
  (define (fives x) (disj (== x 5) (Zzz (fives x))))
  (let/vars (x)
    (check-equal?
      (reify-states x (muk-take 1 (run (fives x))))
      '(5)))
  (define (sixes x) (disj (== x 6) (Zzz (sixes x))))
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
