#lang racket/base
(provide
  interpret
  muk-eval
  muk-fof-apply
  (struct-out muk-func-app)
  muk-reify
  muk-state-empty
  )

(require
  "cursor.rkt"
  "dict.rkt"
  "maybe.rkt"
  "microkanren.rkt"
  "monad.rkt"
  "record.rkt"
  "repr.rkt"
  "sugar.rkt"
  racket/dict
  (except-in racket/match ==)
  racket/set
  )

(module+ test
  (require
    rackunit
    ))

(record muk-func-app name args)
(record muk-fof-constraints func-interps func-deps sub-funcs)
(define muk-fof-constraints-empty (muk-fof-constraints (hash) (hash) (hash)))
(define muk-fof-state-empty
  (muk-state-empty/constraints muk-fof-constraints-empty))
(define (muk-state-interpret st interpretations)
  (:~* st (fn (func-interps)
              (forf
                interps = func-interps
                (cons name op) <- (dict->list interpretations)
                (hash-set interps name op)))
       'constraints 'func-interps))
(define ((interpret interpretations) st)
  (muk-unit (muk-state-interpret st interpretations)))

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
  (match (hash-get sub-funcs term)
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
    ; TODO: normalization unnecessary unless under a func-app
    ; such as when new-term is func-app or everything here is
    ; under a higher level func-app (track this for efficiency?)

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
    st = muk-fof-state-empty
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

(define muk-fof-eval (muk-evaluator muk-unify muk-fof-constrain))

(def (muk-reify-func-app st (muk-func-app name args) vtrans)
  `(,name ,@(map (fn (el) (muk-reify-term st el vtrans)) args)))
(def (muk-fof-reify vtrans vr st)
  reified-var = (muk-reify-term st vr vtrans)
  (muk-state _ _ (muk-fof-constraints _ _ sub-funcs)) = st
  func-apps =
  (forl (cons ft val) <- (hash->list sub-funcs)
    `(,(muk-reify-func-app st ft vtrans) == ,(muk-reify-term st val vtrans)))
  constraints = (if (null? func-apps) '() `(: ,@func-apps))
  (if (null? constraints) reified-var
    `(,reified-var ,@constraints)))

; temporary definitions
(define muk-state-empty muk-fof-state-empty)
(define muk-reify muk-fof-reify)
(define muk-eval muk-fof-eval)
