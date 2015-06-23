#lang racket/base
; variant of: http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf
(provide
  ==
  call/var
  let/vars
  conj
  conj-seq
  disj
  muk-conj-conc
  muk-conj-seq
  muk-constraint
  muk-cost-goal
  muk-evaluator
  muk-goal
  muk-mzero
  muk-pause
  muk-rebuild
  muk-reify-term
  muk-split
  muk-state-constraints
  muk-state-constraints-set
  muk-state-empty/constraints
  muk-sub-get
  muk-sub-new-bindings
  muk-success
  muk-take
  muk-unification
  muk-unify
  muk-walk
  muk-add-constraint-default
  muk-constrain-default
  muk-unit
  (struct-out muk-var)
  muk-var->symbol
  Zzz
  )

(require
  "dict.rkt"
  "list.rkt"
  "maybe.rkt"
  "monad.rkt"
  "record.rkt"
  "repr.rkt"
  "sugar.rkt"
  racket/function
  racket/list
  (except-in racket/match ==)
  )

(module+ test
  (require
    racket/list
    racket/set
    rackunit
    ))

(record muk-var name)
(record muk-state new-bindings substitution constraints)
(def (muk-state-constraints-set (muk-state nbs sub _) cxs)
  (muk-state nbs sub cxs))
(define (muk-state-empty/constraints constraints)
  (muk-state '() (hasheq) constraints))
(def (muk-sub-get st vr)
  (muk-state new-bindings sub constraints) = st
  compress = (lambda (path result)
    (if (null? path) (values st result)
      (values (muk-state new-bindings
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
(def (muk-sub-add (muk-state new-bindings sub constraints) vr val)
  sub = (hash-set sub (muk-var-name vr) val)
  new-bindings = (list* vr new-bindings)
  (muk-state new-bindings sub constraints))
(def (muk-sub-new-bindings (muk-state new-bindings sub cxs))
  (values (muk-state '() sub cxs) new-bindings))

(records muk-computation
  (muk-success result)
  (muk-unification e0 e1)
  (muk-constraint name args)
  (muk-conj-conc cost c0 c1)
  (muk-conj-seq cost c0 c1)
  (muk-cost-goal cost goal)
  (muk-pause paused)
  )

(define muk-cost-unknown #f)
(define muk-cost-unification 0)
(define muk-cost-constraint 0)
(define (muk-cost-min c0 c1)
  (if c0 (if c1 (min c0 c1) c0) c1))
(define (muk-computation-cost comp)
  (match comp
    ((muk-success _) muk-cost-unknown)
    ((muk-unification _ _) muk-cost-unification)
    ((muk-constraint _ _) muk-cost-constraint)
    ((muk-conj-conc cost _ _) cost)
    ((muk-conj-seq cost _ _) cost)
    ((muk-cost-goal cost _) cost)
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

(define (call/var f (name '?)) (f (muk-var (gensym name))))
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

(define (muk-evaluator unify add-constraint constrain)
  (define (muk-step-unification st e0 e1)
    (match (unify st e0 e1)
      ((nothing) muk-mzero)
      ((just st) (muk-unit st))))
  (define (muk-step-constraint st name args)
    (match (add-constraint st name args)
      (#f muk-mzero)
      (st (muk-unit st))))
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
      ((muk-unification e0 e1) (muk-step-unification st e0 e1))
      ((muk-constraint name args) (muk-step-constraint st name args))
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

(define (muk-add-constraint-default st name args)
  (error (format "unsupported constraint: ~a ~a" name args)))
(def (muk-constrain-default st)
  (values st _) = (muk-sub-new-bindings st)
  (just st))

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
    (_ (match (muk-split (list term))
         ((nothing) term)
         ((just (list (repr type components)))
          (muk-rebuild
            (repr type (map (fn (el) (muk-reify-term st el vtrans))
                            components))))))))

(module+ test
  (define eval-simple
    (muk-evaluator muk-unify muk-add-constraint-default muk-constrain-default))
  (define (run comp) (eval-simple (muk-state-empty/constraints (void)) comp))
  (define (reify-states vr states)
    (forl st <- states (muk-reify-term st vr muk-var->symbol)))
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
