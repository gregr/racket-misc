#lang racket/base
; variant of: http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf
(provide
  ==
  call/var
  let/vars
  conj
  conj-seq
  disj
  muk-choices
  muk-conj-conc
  muk-conj-seq
  muk-constraint
  muk-cost-goal
  muk-disj
  muk-evaluator
  muk-evaluator-dls
  muk-fail
  muk-failure
  muk-goal
  muk-mzero
  muk-pause
  muk-reify-term
  muk-state-constraints
  muk-state-constraints-set
  muk-state-empty/constraints
  muk-sub-get
  muk-sub-new-bindings
  muk-succeed
  muk-success
  muk-take
  muk-unification
  muk-unify
  muk-walk
  muk-add-constraint-default
  muk-constrain-default
  muk-unit
  (struct-out muk-var)
  muk-var->indexed-symbol-trans
  muk-var->indexed-symbol-trans-default
  muk-var->symbol
  muk-var->symbol-trans
  muk-Zzz
  Zzz
  )

(require
  "dict.rkt"
  "list.rkt"
  "maybe.rkt"
  "record.rkt"
  "sugar.rkt"
  racket/control
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
  (muk-failure details)
  (muk-success result)
  (muk-unification e0 e1)
  (muk-constraint name args)
  (muk-conj-conc cost c0 c1)
  (muk-conj-seq cost c0 c1)
  (muk-disj c0 c1)
  (muk-cost-goal cost goal)
  (muk-pause paused)
  (muk-Zzz thunk)
  )

(define muk-cost-cheap 0)
(define muk-cost-expensive #f)
(define muk-cost-unknown muk-cost-expensive)
(define muk-cost-Zzz muk-cost-expensive)
(define muk-cost-unification muk-cost-cheap)
(define muk-cost-constraint muk-cost-cheap)
(define (muk-cost-min c0 c1)
  (if c0 (if c1 (min c0 c1) c0) c1))
(define (muk-computation-cost comp)
  (match comp
    ((muk-failure _) muk-cost-cheap)
    ((muk-success _) muk-cost-unknown)
    ((muk-unification _ _) muk-cost-unification)
    ((muk-constraint _ _) muk-cost-constraint)
    ((muk-conj-conc cost _ _) cost)
    ((muk-conj-seq cost _ _) cost)
    ((muk-disj _ _) muk-cost-unknown)
    ((muk-cost-goal cost _) cost)
    ((muk-pause _) muk-cost-unknown)
    ((muk-Zzz _) muk-cost-Zzz)
    (_ muk-cost-unknown)))
(define (muk-comps->cost c0 c1)
  (muk-cost-min (muk-computation-cost c0) (muk-computation-cost c1)))

(define (muk-fail (details (void))) (muk-failure details))
(define (muk-succeed (result (void))) (muk-success result))
(define (muk-goal st comp) (list (list st comp)))
(define (muk-choices st c0 c1) (list (list st c0) (list st c1)))
(define muk-mzero '())
(define (muk-unit st (result (void))) (muk-goal st (muk-success result)))

(define == muk-unification)
(define (conj c0 c1)
  (match* (c0 c1)
    (((muk-failure _) _) c0)
    ((_ (muk-failure _)) c1)
    (((muk-success _) _) c1)
    ((_ (muk-success (? void?))) c0)
    ((_ _) (muk-conj-conc (muk-comps->cost c0 c1) c0 c1))))
(define (conj-seq c0 c1)
  (match c0
    ((muk-failure _) c0)
    ((muk-success _) c1)
    (_ (muk-conj-seq (muk-computation-cost c0) c0 c1))))
(define (disj c0 c1)
  (match* (c0 c1)
    (((muk-failure _) _) c1)
    ((_ (muk-failure _)) c0)
    ((_ _) (muk-disj c0 c1))))

(define (call/var f (name '?)) (f (muk-var (gensym name))))
(define-syntax let/vars
  (syntax-rules ()
    ((_ () body) body)
    ((_ () body ...) (begin body ...))
    ((_ (qvar qvars ...) body ...)
     (call/var (lambda (qvar) (let/vars (qvars ...) body ...)) 'qvar))))

(define-syntax Zzz
  (syntax-rules () ((_ goal) (muk-Zzz (thunk goal)))))

(define (muk-force ss) (if (procedure? ss) (muk-force (ss)) ss))

(define (muk-take n ss)
  (if (and n (zero? n)) '()
    (match (muk-force ss)
      ('() '())
      ((cons st ss) (list* st (muk-take (and n (- n 1)) ss))))))

(record muk-incomplete resume state goal)
(define (muk-evaluator-dls unify add-constraint constrain)
  (define ptag (make-continuation-prompt-tag))
  (define (muk-step-unification st e0 e1)
    (let ((st (unify st e0 e1))) (if st (muk-unit st) muk-mzero)))
  (define (muk-step-constraint st name args)
    (match (add-constraint st name args)
      (#f muk-mzero)
      (st (muk-unit st))))
  (define (muk-step-conj-conc cont arg st c0 c1)
    (for*/list ((r0 (in-list (cont st c0 arg)))
                (r1 (in-list (cont (first r0) c1 arg))))
               (lets (list _ c0) = r0
                     (list st c1) = r1
                     (list st (conj c0 c1)))))
  (define (muk-step-conj-seq cont arg st c0 c1)
    (append* (forl (list st c0) <- (in-list (cont st c0 arg))
                   (match c0
                     ((muk-success _) (cont st c1 arg))
                     (_ (muk-goal st (conj-seq c0 c1)))))))

  (define (muk-step-known st comp cost-max)
    (define (cost? cost) (and cost (<= cost cost-max)))
    (match comp
      ((muk-failure _) muk-mzero)
      ((muk-conj-conc (? cost?) c0 c1)
       (muk-step-conj-conc muk-step-known cost-max st c0 c1))
      ((muk-conj-seq (? cost?) c0 c1)
       (muk-step-conj-seq muk-step-known cost-max st c0 c1))
      ((muk-unification e0 e1) (muk-step-unification st e0 e1))
      ((muk-constraint name args) (muk-step-constraint st name args))
      ((muk-cost-goal (? cost?) goal)
       (muk-step-results muk-step-known cost-max (goal st)))
      (_ (muk-goal st comp))))

  (define (muk-mplus ss1 ss2)
    (match ss1
      ('() ss2)
      ((? procedure?) (thunk (muk-mplus (ss1) ss2)))
      ((cons result ss) (list* result (muk-mplus ss ss2)))))
  (define (muk-bind-depth depth ss comp)
    (match ss
      ('() muk-mzero)
      ((? procedure?) (thunk (muk-bind-depth/incomplete depth ss comp)))
      ((cons (list st _) ss) (muk-mplus (muk-step-depth st comp depth)
                                        (muk-bind-depth depth ss comp)))))
  (define (muk-bind-depth/incomplete depth th comp)
    (let loop ((result (reset-at ptag (th))))
      (match result
        ((muk-incomplete k st _)
         (let loop2 ((scout (muk-step-depth st comp depth)))
           (match scout
             ('() (loop (k muk-mzero)))
             ((? procedure?) (loop2 (scout)))
             ((cons (list st comp) ss)
              (begin (raise-incomplete st comp)
                     (if (unbox incomplete?!)
                       (loop (k muk-mzero)) (loop2 ss)))))))
        (ss (muk-bind-depth depth ss comp)))))
  (define incomplete?! (box #f))
  (define (raise-incomplete st comp)
    (if (unbox incomplete?!) muk-mzero
      (shift-at ptag k (muk-incomplete k st comp))))

  (define (muk-step-depth st comp depth)
    (define next-depth (- depth 1))
    (if (= depth 0) (raise-incomplete st comp)
      (match comp
        ((muk-failure _) muk-mzero)
        ((muk-success _) (muk-goal st comp))
        ((muk-conj-conc cost c0 c1)
         (muk-bind-depth/incomplete
           depth (thunk (muk-step-depth st c0 depth)) c1))
        ((muk-conj-seq cost c0 c1)
         (muk-bind-depth/incomplete
           depth (thunk (muk-step-depth st c0 depth)) c1))
        ((muk-disj c0 c1)
         (muk-mplus (muk-step st c0 depth) (thunk (muk-step st c1 depth))))
        ((muk-pause paused) (muk-goal st paused))
        ((muk-Zzz thunk) (muk-step-depth st (thunk) next-depth))
        (_ (comp st)))))

  (define (muk-step-results cont arg results)
    (append* (forl (list st comp) <- (in-list results) (cont st comp arg))))
  (define (muk-step st comp depth)
    (let ((cost (muk-computation-cost comp)))
      (if cost
        (muk-step-results muk-step depth (muk-step-known st comp cost))
        (muk-bind-depth depth
                        (forl st <- (constrain st) (list st (muk-succeed)))
                        comp))))

  (define (muk-strip n results)
    (match results
      ('() '())
      ((? procedure?)
       (thunk (muk-strip (results))))
      ((cons (list st _) rs) (list* st (muk-strip rs)))))
  (define (muk-eval st comp n (depth-min 1) (depth-inc add1) (depth-max #f))
    (let loop0 ((depth depth-min))
      (set-box! incomplete?! #f)
      (match (reset-at ptag
        (let loop1 ((n n) (results (thunk (muk-step st comp depth))))
          (if (equal? n 0) '()
            (match results
              ('() (if (and (unbox incomplete?!) n)
                     (shift-at ptag k (muk-incomplete k (void) (void)))
                     muk-mzero))
              ((? procedure?)
               (let loop2 ((results (reset-at ptag (results))))
                 (match results
                   ((muk-incomplete k _ _)
                    (set-box! incomplete?! #t)
                    (if n (loop2 (k muk-mzero))
                      (loop2 (shift-at ptag k
                                       (muk-incomplete k (void) (void))))))
                   (_ (loop1 n results)))))
              ((cons (list st _) rs)
               (list* st (loop1 (and n (- n 1)) rs)))))))
        ((muk-incomplete k _ _)
         (lets depth = (depth-inc depth)
               (if (and depth-max (> depth depth-max))
                 (k muk-mzero) (loop0 depth))))
        (results results))))

  muk-eval)

(define (muk-evaluator unify add-constraint constrain)
  (define (muk-step-unification st e0 e1)
    (let ((st (unify st e0 e1))) (if st (muk-unit st) muk-mzero)))
  (define (muk-step-constraint st name args)
    (match (add-constraint st name args)
      (#f muk-mzero)
      (st (muk-unit st))))
  (define (muk-step-conj-conc cont arg st c0 c1)
    (for*/list ((r0 (in-list (cont st c0 arg)))
                (r1 (in-list (cont (first r0) c1 arg))))
               (lets (list _ c0) = r0
                     (list st c1) = r1
                     (list st (conj c0 c1)))))
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
      ((muk-failure _) muk-mzero)
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
        ((muk-failure _) muk-mzero)
        ((muk-success _) (muk-goal st comp))
        ((muk-conj-conc cost c0 c1)
         (muk-step-conj-conc muk-step depth st c0 c1))
        ((muk-conj-seq cost c0 c1)
         (muk-step-conj-seq muk-step depth st c0 c1))
        ((muk-disj c0 c1)
         (muk-step-results muk-step depth (muk-choices st c0 c1)))
        ((muk-pause paused) (muk-goal st paused))
        ((muk-Zzz thunk) (muk-step st (thunk) next-depth))
        (_ (muk-step-results muk-step next-depth (comp st))))))

  (define (muk-step st comp depth)
    (let ((cost (muk-computation-cost comp)))
      (if cost (muk-step-results muk-step depth (muk-step-known st comp cost))
        (append* (forl st <- (constrain st)
                       (muk-step-depth st comp depth))))))

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

(define (muk-walk st term)
  (if (muk-var? term) (muk-sub-get st term) (values st term)))

(define (muk-occurs? st v tm)
  (match tm
    ((? muk-var?) (eq? v tm))
    ((cons h0 t0)
     (lets (values st h0) = (muk-walk st h0)
           (values st t0) = (muk-walk st t0)
           (or (muk-occurs? st v h0) (muk-occurs? st v t0))))
    (_ #f)))
(define (sub-add st v tm) (if (muk-occurs? st v tm) #f (muk-sub-add st v tm)))

(def (muk-unify st e0 e1)
  (values st e0) = (muk-walk st e0)
  (values st e1) = (muk-walk st e1)
  (cond
    ((eqv? e0 e1) st)
    ((muk-var? e0) (sub-add st e0 e1))
    ((muk-var? e1) (sub-add st e1 e0))
    (else (match* (e0 e1)
            (((cons h0 t0) (cons h1 t1))
             (let ((st (muk-unify st h0 h1))) (and st (muk-unify st t0 t1))))
            ((_ _) #f)))))

(define (muk-add-constraint-default st name args)
  (error (format "unsupported constraint: ~a ~a" name args)))
(def (muk-constrain-default st)
  (values st _) = (muk-sub-new-bindings st)
  (list st))

(def (muk-var->symbol (muk-var name))
  (string->symbol (string-append "_." (symbol->string name))))
(define (muk-var->symbol-trans mv)
  (values muk-var->symbol-trans (muk-var->symbol mv)))
(def ((muk-var->indexed-symbol-trans n->i index) (muk-var name))
  (values n->i index ni) =
  (match (hash-get n->i name)
    ((nothing) (values (hash-set n->i name index) (+ 1 index) index))
    ((just ni) (values n->i index ni)))
  (values (muk-var->indexed-symbol-trans n->i index)
          (string->symbol (string-append "_." (number->string ni)))))
(define muk-var->indexed-symbol-trans-default
  (muk-var->indexed-symbol-trans hash-empty 0))
(def (muk-reify-term st term vtrans)
  (values _ result) =
  (letn loop (values st term vtrans) = (values st term vtrans)
    (values st term) = (muk-walk st term)
    (match term
      ((muk-var _) (vtrans term))
      ((cons hd tl) (lets (values vtrans rhd) = (loop st hd vtrans)
                          (values vtrans rtl) = (loop st tl vtrans)
                          (values vtrans (cons rhd rtl))))
      (_ (values vtrans term))))
  result)

(module+ test
  (define eval-simple
    (muk-evaluator muk-unify muk-add-constraint-default muk-constrain-default))
  (define (run comp) (eval-simple (muk-state-empty/constraints (void)) comp))
  (define (reify-states vr states)
    (forl st <- states (muk-reify-term st vr muk-var->symbol-trans)))
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

  (let/vars (x y)
    (check-equal?
      (reify-states x (muk-take 1 (run (conj (== (cons 1 y) x) (== y 2)))))
      `(,(cons 1 2))))
  )
