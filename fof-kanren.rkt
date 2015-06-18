#lang racket/base
(provide
  interpret
  fof-apply
  (struct-out fof-func-app)
  run-config-fof
  runfof
  runfof*
  runfof-depth
  runfof*-depth
  )

(require
  "cursor.rkt"
  "dict.rkt"
  "maybe.rkt"
  "microkanren.rkt"
  "minikanren.rkt"
  "monad.rkt"
  "record.rkt"
  "repr.rkt"
  "sugar.rkt"
  racket/dict
  racket/function
  racket/list
  (except-in racket/match ==)
  racket/set
  )

(module+ test
  (require
    rackunit
    ))

(record fof-func-app name args)
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
    ((fof-func-app _ args) (recur args))
    (_ (match (muk-split (list term))
         ((nothing) (set))
         ((just (list rpr)) (recur (repr-components rpr)))))))

(module+ test
  (lets
    vars = (map muk-var '(a b c))
    (list v0 v1 v2) = vars
    f0 = (fof-func-app 'zero (list v0 v1))
    f1 = (fof-func-app 'one (list v2 f0))
    f2 = (fof-func-app 'two (list f0 f1 v1))
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

(def (fof-func-app-add st term)
  constraints = (muk-state-constraints st)
  (muk-fof-constraints func-interps func-deps sub-funcs) = constraints
  (match (hash-get sub-funcs term)
    ((nothing)
     (lets term-var = (let/vars (app-result) app-result)
           sub-funcs = (hash-set sub-funcs term term-var)
           func-deps = (forf
                         func-deps = func-deps
                         vr <- (muk-term->vars term)
                         deps = (set-add (hash-ref func-deps vr (set)) term)
                         (hash-set func-deps vr deps))
           constraints = (muk-fof-constraints func-interps func-deps sub-funcs)
           st = (muk-state-constraints-set st constraints)
           (values st term-var)))
    ((just expected) (values st expected))))

(define (muk-sub-get-term st term)
  (if (fof-func-app? term) (fof-func-app-add st term) (values st term)))

(def (muk-normalize-get st term)
  (values st nterm) = (muk-normalize st term)
  (muk-sub-get-term st nterm))

(def ((fof-apply name args result) st)
  (values st result-var) = (muk-normalize-get st (fof-func-app name args))
  (muk-goal st (== result-var result)))

(define (muk-normalize-get-args st args)
  (forf st = st normalized = '()
        arg <- (reverse args)
        (values st narg) = (muk-normalize-get st arg)
        (values st (list* narg normalized))))

(def (fof-func-app-normalize st term)
  (fof-func-app name args) = term
  (muk-fof-constraints func-interps _ _) = (muk-state-constraints st)
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
    ((fof-func-app _ _) (fof-func-app-normalize st term))
    (_ (match (muk-split (list term))
         ((nothing) (values st term))
         ((just (list (repr type components)))
          (lets (values st ncomps) = (muk-normalize-get-args st components)
                (values st (muk-rebuild (repr type ncomps)))))))))

(module+ test
  (lets
    st = muk-fof-state-empty
    id-func-op = (fn (fname) (lambda xs (fof-func-app fname xs)))
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

(def (fof-func-app-update st term-old)
  (values st term-new) = (fof-func-app-normalize st term-old)
  (if (equal? term-old term-new) (just st)
    (lets
      (values st expected-old) = (muk-sub-get-term st term-old)
      constraints = (muk-state-constraints st)
      (muk-fof-constraints func-interps func-deps sub-funcs) = constraints
      func-deps =
      (forf func-deps = func-deps
            old-var <- (muk-term->vars term-old)
            ; TODO: if empty, remove completely
            (hash-update func-deps old-var
                         (fn (terms) (set-remove terms term-old))))
      sub-funcs = (hash-remove sub-funcs term-old)
      constraints = (muk-fof-constraints func-interps func-deps sub-funcs)
      st = (muk-state-constraints-set st constraints)
      (values st expected-new) = (muk-sub-get-term st term-new)
      (muk-unify st expected-old expected-new))))

(def (muk-fof-constrain st)
  (muk-fof-constraints _ func-deps _) = (muk-state-constraints st)
  (values st new) = (muk-sub-new-bindings st)
  (if (or (null? new) (hash-empty? func-deps)) (just st)
    (lets
      fterms = (foldl set-union (set)
                      (forl vr <- new (hash-ref func-deps vr (set))))
      (match (monad-foldl maybe-monad fof-func-app-update st
                          (set->list fterms))
        ((nothing) (nothing))
        ((just st-new) (muk-fof-constrain st-new))))))

; TODO: use constraint-adding in fof-apply?
(define fof-eval
  (muk-evaluator muk-unify muk-add-constraint-default muk-fof-constrain))

(def (muk-reify-func-app st (fof-func-app name args) vtrans)
  `(,name ,@(map (fn (el) (muk-reify-term st el vtrans)) args)))
(def (fof-reify vtrans vr st)
  reified-var = (muk-reify-term st vr vtrans)
  (muk-fof-constraints _ _ sub-funcs) = (muk-state-constraints st)
  func-apps =
  (forl (cons ft val) <- (hash->list sub-funcs)
    `(,(muk-reify-func-app st ft vtrans) == ,(muk-reify-term st val vtrans)))
  constraints = (if (null? func-apps) '() `(: ,@func-apps))
  (if (null? constraints) reified-var
    `(,reified-var ,@constraints)))

(define run-config-fof
  (run-config (curry fof-eval muk-fof-state-empty)
              (curry fof-reify muk-var->symbol)))

(define-syntax runfof-depth
  (syntax-rules ()
    ((_ n depth body ...) (run/config run-config-fof n depth body ...))))
(define-syntax runfof*-depth
  (syntax-rules () ((_ body ...) (runfof-depth #f body ...))))
(define-syntax runfof
  (syntax-rules () ((_ n body ...) (runfof-depth n 1 body ...))))
(define-syntax runfof*
  (syntax-rules () ((_ body ...) (runfof #f body ...))))

(define (muk-term? val) (or (muk-var? val) (fof-func-app? val)))

(define (interp-type val)
  (if (muk-term? val) (fof-func-app 'type (list val))
    (lets (repr type components) = (value->repr val)
          components = (if (list? components) (map interp-type components) '())
          (list type components))))

(define (interp-=/= . or-diseqs)
  (def (muk-var< (muk-var n0) (muk-var n1)) (symbol<? n0 n1))
  (def (total< e0 e1)
    (or (not (muk-var? e1)) (and (muk-var? e0) (muk-var< e0 e1))))
  (def (list< (list k0 v0) (list k1 v1)) (muk-var< k0 k1))
  (match (monad-foldl maybe-monad
          (fn (st (list e0 e1)) (muk-unify st e0 e1))
          muk-fof-state-empty or-diseqs)
    ((nothing) #t)
    ((just st-new)
     (lets
       (values st-new vr-new) = (muk-sub-new-bindings st-new)
       or-diseqs = (forl
                     vr <- vr-new
                     (values _ val) = (muk-sub-get st-new vr)
                     (sort (list vr val) total<))
       or-diseqs = (sort or-diseqs list<)
       (if (null? or-diseqs) #f (fof-func-app '=/= or-diseqs))))))

(define ((interp-numeric-op name op) a b)
  (if (or (muk-term? a) (muk-term? b)) (fof-func-app name (list a b))
    (if (and (number? a) (number? b)) (op a b) (void))))
(define interp-+ (interp-numeric-op '+ +))
(define interp-< (interp-numeric-op '< <))

(define interpretations
  (hash
    'type interp-type
    '=/= interp-=/=
    '+ interp-+
    '< interp-<
    ))

; TODO: this was a bad idea that's now easier to fix
(define with-constraints (interpret interpretations))

(define (typeo val result) (fof-apply 'type (list val) result))
(define (symbolo val) (typeo val '(symbol ())))
(define (numbero val)
  (exist (sub-type) (typeo val `((number . ,sub-type) ()))))

(define (=/= e0 e1)
  (let/vars (t0 t1)
    (conj* (typeo e0 t0) (typeo e1 t1)
           (fof-apply '=/= (list (list (list t0 e0) (list t1 e1))) #t))))
(define (all-diffo xs)
  (matche xs
    ('())
    (`(,_))
    (`(,a ,ad . ,dd)
      (=/= a ad)
      (all-diffo `(,a . ,dd))
      (all-diffo `(,ad . ,dd)))))
(define (+o a b a+b)
  (conj* (numbero a) (numbero b) (numbero a+b)
         (fof-apply '+ (list a b) a+b)))
(define (<o a b)
  (conj* (numbero a) (numbero b)
         (fof-apply '< (list a b) #t)))
(define (<=o a b) (conde ((numbero a) (numbero b) (== a b)) ((<o a b))))

(module+ test
  ; TODO: re-enable with deterministic sub-func reification order
  ;(check-match
    ;(runfof 1 (q) with-constraints (all-diffo `(2 3 ,q)))
    ;`((,q :
          ;((type ,q) == ,r)
          ;((=/= (,r ((number real exact integer natural) ())) (,q 3)) == #t)
          ;((=/= (,r ((number real exact integer natural) ())) (,q 2)) == #t)
          ;)))
  (define (rembero x ls out)
    (conde
      ((== '() ls) (== '() out))
      ((exist (a d res)
        (== `(,a . ,d) ls)
        (rembero x d res)
        (conde
          ((== a x) (== res out))
          ((=/= a x) (== `(,a . ,res) out)))))))
  (check-equal?
    (runfof* q (conj-seq* with-constraints (rembero 'a '(a b a c) q)))
    '((b c)))
  (check-equal?
    (runfof* q (conj-seq* with-constraints (rembero 'a '(a b c) '(a b c))))
    '())
  (check-equal?
    (list->set
      (runfof* (x y) (conj-seq* with-constraints (ino (range 3) x y) (all-diffo (list x y)))))
    (list->set '((0 1) (0 2) (1 0) (1 2) (2 0) (2 1))))
  (check-equal?
    (runfof* (w x y z) (conj-seq* with-constraints (ino (range 3) w x y z) (all-diffo (list w x y z))))
    '())
  (check-equal?
    (runfof* (w x y z) (conj-seq* with-constraints (symbolo x) (symbolo z) (+o y y w) (ino (list 5 'five) x y z)))
    '((10 five 5 five)))
  (check-match
    (runfof* (p r) (conj-seq* with-constraints
      (=/= '(1 2) `(,p ,r))
      (== 1 p)
      (symbolo r)))
    `(((1 ,r) : ((type ,r) == (symbol ())))))

  ; slow test
  ;(lets
    ;;   S E N D
    ;; + M O R E
    ;; ---------
    ;; M O N E Y
    ;add-digitso = (fn (augend addend carry-in carry-out digit)
      ;(exist (partial-sum sum)
        ;(+o augend addend partial-sum)
        ;(+o partial-sum carry-in sum)
        ;(conde
          ;((<o 9 sum) (== carry-out 1) (+o digit 10 sum))
          ;((<=o sum 9) (== carry-out 0) (== digit sum)))
        ;(ino (range 19) partial-sum)
        ;(ino (range 20) sum)))
    ;send-more-moneyo = (fn (letters)
      ;(exist (s e n d m o r y carry0 carry1 carry2)
        ;(== letters (list s e n d m o r y))
        ;(all-diffo letters)
        ;(ino (range 2) carry0)
        ;(ino (range 10) e d y)
        ;(add-digitso d e 0 carry0 y)
        ;(ino (range 2) carry1 carry2)
        ;(ino (range 10) n o)
        ;(add-digitso e o carry1 carry2 n)
        ;(ino (range 10) r)
        ;(add-digitso n r carry0 carry1 e)
        ;(ino (range 1 10) s m)
        ;(add-digitso s m carry2 m o)))
    ;(check-equal?
      ;(runfof*-depth 1000 q (conj-seq* with-constraints (send-more-moneyo q)))
      ;'((9 5 6 7 1 0 8 2))))
  )
