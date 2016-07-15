#lang racket/base
(provide
  )

(require
  )

(module+ test
  (require
    rackunit
    ))

;; References
;;   Determinism analysis in the Mercury compiler
;;   Fergus Henderson, Zoltan Somogyi and Thomas Conway.
;;   Proceedings of the Australian Computer Science Conference, Melbourne, Australia, January 1996, pages 337-346.
;;   http://www.mercurylang.org/documentation/papers/acsc96.ps.gz
;;   longer version: http://www.mercurylang.org/documentation/papers/detism.ps.gz

(define-syntax record
  (syntax-rules ()
    ((_ name field-names ...) (record-cont name () field-names ...))))
(define-syntax record-cont
  (syntax-rules ()
    ((_ name entries) (struct name entries #:transparent))
    ((_ name (entries ...) fname fnames ...)
     (record-cont name (entries ... (fname #:mutable)) fnames ...))))
(define-syntax records
  (syntax-rules ()
    ((_ name) (void))
    ((_ name (record-entry ...) record-entries ...)
     (begin (record record-entry ...) (records name record-entries ...)))))

(record var name)

(record constraints type absents diseqs)
(define constraints-empty (constraints #f '() '()))
(define (constraints-type-set cxs t1)
  (let ((t0 (constraints-type cxs)))
    (if t0 (and (eq? t0 t1) cxs)
      (constraints t1 (constraints-absents cxs) (constraints-diseqs cxs)))))
(define (constraints-absents-add cxs atoms)
  (let* ((as0 (constraints-absents cxs))
         (as1 (foldl (lambda (atom as) (if (memv atom as0) as0 (cons atom as)))
                     as0 atoms)))
    (if (eq? as0 as1) cxs
      (constraints (constraints-type cxs) as1 (constraints-diseqs cxs)))))
(define (constraints-apply bs cxs0 val)
  (let ((ty-tag (constraints-type cxs0))
        (absents (constraints-absents cxs0)))
    (if (var? val)
      (let* ((cxs1 (bindings-cxs-ref bs val))
             (cxs1 (constraints-type-set cxs1 ty-tag))
             (cxs1 (and cxs1 (constraints-absents-add cxs1 absents))))
        (and cxs1 (bindings-cxs-set bs val cxs1)))
      (and (constrain-value-type ty-tag val)
           (let loop ((bs bs) (absents absents))
             (and bs (if (null? absents) bs
                       (loop (constrain-value-absent bs (car absents) val)
                             (cdr absents)))))))))

(define (constrain-value-type tag val)
  (or (and (number? val) (eq? tag 'num)) (and (symbol? val) (eq? tag 'sym))))
(define (constrain-type bs tag tm)
  (let-values (((bs tm) (walk bs tm)))
    (if (var? tm)
      (let ((cxs (constraints-type-set (bindings-cxs-ref bs tm) tag)))
        (and cxs (bindings-cxs-set bs tm cxs)))
      (and (constrain-value-type tag tm) bs))))

(define (constrain-value-absent bs atom val)
  (if (pair? val)
    (let ((bs (constrain-absent bs atom (car val))))
      (and bs (constrain-absent bs atom (cdr val))))
    (and (not (eqv? atom val)) bs)))
(define (constrain-absent bs atom tm)
  (let-values (((bs tm) (walk bs tm)))
    (if (var? tm)
      (bindings-cxs-set bs tm (constraints-absents-add
                                (bindings-cxs-ref bs tm) (list atom)))
      (constrain-value-absent bs atom tm))))

(record hypotheticals assignments constrained)
(define hypotheticals-empty (hypotheticals '() '()))
(define (hypotheticals-assign hs vr val)
  (hypotheticals (cons (cons vr val) (hypotheticals-assignments hs))
                 (hypotheticals-constrained hs)))
(define (hypotheticals-constrain hs vr)
  (hypotheticals (hypotheticals-assignments hs)
                 (cons vr (hypotheticals-constrained hs))))

(record bindings actual hypothetical)
(define bindings-empty (bindings (hash) #f))
(define (bindings->hypothetical bs)
  (bindings (bindings-actual bs) hypotheticals-empty))
(define (bindings-actual-ref bs vr default)
  (hash-ref (bindings-actual bs) vr default))
(define (bindings-actual-set bs vr rhs)
  (bindings (hash-set (bindings-actual bs) vr rhs) (bindings-hypothetical bs)))
(define (bindings-cxs-ref bs vr) (bindings-actual-ref bs vr constraints-empty))
(define bindings-cxs-set bindings-actual-set)

(define (bindings-assign bs vr val)
  (let* ((hs (bindings-hypothetical bs))
         (hs (and hs (hypotheticals-assign hs vr val)))
         (cxs (bindings-actual-ref bs vr #f))
         (bs (bindings (hash-set (bindings-actual bs) vr val) hs)))
    (if cxs (constraints-apply bs cxs val) bs)))

(define (bindings-get bs vr)
  (let* ((r0 (bindings-actual-ref bs vr vr)) (r0 (if (constraints? r0) vr r0)))
    (if (or (eq? r0 vr) (not (var? r0))) (values bs r0)
      (let-values (((bs r1) (bindings-get bs r0)))
        (if (eq? r0 r1) (values bs r1)
          (values (bindings (hash-set (bindings-actual bs) vr r1)
                            (bindings-hypothetical bs))
                  r1))))))
(define (walk bs term)
  (if (var? term) (bindings-get bs term) (values bs term)))

(define (not-occurs? bs vr term)
  (if (pair? term) (let-values (((bs h0) (walk bs (car term))))
                     (let ((bs (not-occurs? bs vr h0)))
                       (and bs (let-values (((bs t0) (walk bs (cdr term))))
                                 (not-occurs? bs vr t0)))))
    (if (eq? vr term) #f bs)))

(define (checked-assign bs0 vr term)
  (let ((bs1 (not-occurs? bs0 vr term)))
    (and bs1 (bindings-assign bs1 vr term))))

(define (unify bs e0 e1)
  (let-values (((bs e0) (walk bs e0)))
    (let-values (((bs e1) (walk bs e1)))
      (cond
        ((eqv? e0 e1) bs)
        ((var? e0) (checked-assign bs e0 e1))
        ((var? e1) (checked-assign bs e1 e0))
        (else (and (pair? e0) (pair? e1)
                   (let ((bs (unify bs (car e0) (car e1))))
                     (and bs (unify bs (cdr e0) (cdr e1))))))))))


(record state bindings cxs apps disjs)
(define state-empty (state bindings-empty '() '() '()))
(define (state-bindings-set st bs)
  (state bs (state-cxs st) (state-apps st) (state-disjs st)))
(define (state-apps-add st app)
  (state (state-bindings st)
         (state-cxs st)
         (cons app (state-apps st))
         (state-disjs st)))
(define (state-apps-clear st)
  (state (state-bindings st)
         (state-cxs st)
         '()
         (state-disjs st)))
(define (state-disjs-add st disj)
  (state (state-bindings st)
         (state-cxs st)
         (state-apps st)
         (cons disj (state-disjs st))))
(define (state-disjs-pop st)
  (let ((disjs (state-disjs st)))
    (values (state (state-bindings st)
                   (state-cxs st)
                   (state-apps st)
                   (cdr disjs))
            (car disjs))))

(define (== e0 e1)
  (lambda (st)
    (let ((bs (unify (state-bindings st) e0 e1)))
      (and bs (state-bindings-set st bs)))))
(define (typeo tag term)
  (lambda (st)
    (let ((bs (constrain-type (state-bindings st) tag term)))
      (and bs (state-bindings-set st bs)))))
(define (numbero term) (typeo 'num term))
(define (symbolo term) (typeo 'sym term))
(define (absento atom term)
  (lambda (st)
    (let ((bs (constrain-absent (state-bindings st) atom term)))
      (and bs (state-bindings-set st bs)))))

(define-syntax zzz
  (syntax-rules () ((_ body ...) (lambda () body ...))))

(record procedure-attrs name active?)

(define (app-step st attrs zproc)
  (if (procedure-attrs-active? attrs)
    (state-apps-add st (cons attrs zproc))
    (begin (set-procedure-attrs-active?! attrs #t)
           (let ((st ((zproc) st)))
             (set-procedure-attrs-active?! attrs #f)
             st))))
(define (state-apps-step st)
  (let loop ((apps (state-apps st)) (st (state-apps-clear st)))
    (if (null? apps) st
      (and st (loop (cdr apps) (app-step st (caar apps) (cdar apps)))))))

(define (disj-split st disj)
  (let loop ((disj (map (lambda (goal) (zzz (state-step (goal st)))) disj))
             (unfinished '()))
    (if (null? disj) (if (null? unfinished)
                       '() (loop (reverse unfinished) '()))
      (zzz (let extract-answers ((ss ((car disj))))
             (cond ((procedure? ss) (loop (cdr disj) (cons ss unfinished)))
                   ((pair? ss) (cons (car ss)
                                     (extract-answers (cdr ss))))
                   (else (loop (cdr disj) unfinished))))))))

(define (state-disjs-step st)
  (if (null? (state-disjs st)) (list (state-bindings st))
    (let-values (((st disj) (state-disjs-pop st)))
      (disj-split st disj))))

(define (state-step st)
  (if st (if (pair? (state-apps st)) (zzz (state-step (state-apps-step st)))
           (state-disjs-step st))
    '()))

(define (unit st) st)
(define (conj g0 g1) (lambda (st) (let ((st1 (g0 st))) (and st1 (g1 st1)))))
(define-syntax conj*
  (syntax-rules ()
    ((_) unit)
    ((_ goal) goal)
    ((_ goal goals ...) (conj goal (conj* goals ...)))))
(define-syntax fresh
  (syntax-rules ()
    ((_ () body ...) (conj* body ...))
    ((_ (lvar lvars ...) body ...) (let ((lvar (var (gensym 'lvar))))
                                     (fresh (lvars ...) body ...)))))
(define-syntax disj-branches
  (syntax-rules ()
    ((_) '())
    ((_ goal goals ...) (cons goal (disj-branches goals ...)))))
(define-syntax disj*
  (syntax-rules ()
    ((_) (lambda (st) #f))
    ((_ goal) goal)
    ((_ goals ...) (lambda (st)
                     (state-disjs-add st (disj-branches goals ...))))))
(define-syntax conde
  (syntax-rules () ((_ (goal ...) ...) (disj* (conj* goal ...) ...))))

(define var-initial (var 'initial))
(define (reify vi)
  (lambda (bs)
    (let-values
      (((bs ixs rterm)
        (let loop ((bs bs) (ixs (hash)) (term vi))
          (let-values (((bs term) (walk bs term)))
            (cond ((var? term)
                   (let ix-loop ((ixs ixs) (ix (hash-ref ixs term #f)))
                     (if ix
                       (values bs ixs (string->symbol
                                        (string-append
                                          "_." (number->string ix))))
                       (ix-loop (hash-set ixs term (hash-count ixs))
                                (hash-count ixs)))))
                  ((pair? term)
                    (let-values (((bs ixs rhd) (loop bs ixs (car term))))
                      (let-values (((bs ixs rtl) (loop bs ixs (cdr term))))
                        (values bs ixs (cons rhd rtl)))))
                  (else (values bs ixs term)))))))
      rterm)))

(define (force-answer ss) (if (procedure? ss) (force-answer (ss)) ss))
(define (take n ss)
  (if (and n (zero? n)) '()
    (let ((ss (force-answer ss)))
      (if (null? ss) '()
        (cons (car ss) (take (and n (- n 1)) (cdr ss)))))))

(define-syntax run
  (syntax-rules ()
    ((_ n (qs ...) gs ...)
     (map (reify var-initial)
       (take n (state-step
                 ((fresh (qs ...) (== (list qs ...) var-initial) gs ...)
                  state-empty)))))))
(define-syntax run* (syntax-rules () ((_ body ...) (run #f body ...))))

(define-syntax kanren
  (syntax-rules ()
    ((_ (define (name params ...) body ...) kdefs ...)
     (begin (define name
              (let ((proc-attrs (procedure-attrs 'name #f)))
                (lambda (params ...)
                  (lambda (st)
                    (app-step st proc-attrs (zzz (conj* body ...)))))))
            (kanren kdefs ...)))
    ((_ (define name (lambda (params ...) body)) kdefs ...)
     (kanren (define (name params ...) body) kdefs ...))
    ((_ (define name body) kdefs ...)
     (begin (define name body) (kanren kdefs ...)))
    ((_ rest ...) (begin rest ...))))
(define-syntax kanren-define
  (syntax-rules () ((_ kdef ...) (kanren (define kdef ...)))))

(module+ test
  (kanren-define (appendo ls rs lsrs)
    (conde ((== '() ls) (== rs lsrs))
           ((fresh (l0 ms msrs)
              (== `(,l0 . ,ms) ls)
              (== `(,l0 . ,msrs) lsrs)
              (appendo ms rs msrs)))))

  (check-equal?
    (run* (q) (appendo '(1 2 3) '(4 5) q))
    '(((1 2 3 4 5))))
  (check-equal?
    (run* (q) (appendo q '(4 5) '(1 2 3 4 5)))
    '(((1 2 3))))
  (check-equal?
    (run* (q) (appendo '(1 2 3) q '(1 2 3 4 5)))
    '(((4 5))))
  (check-equal?
    (run* (q r) (appendo q r '(1 2 3 4 5)))
    '((() (1 2 3 4 5))
      ((1) (2 3 4 5))
      ((1 2) (3 4 5))
      ((1 2 3) (4 5))
      ((1 2 3 4) (5))
      ((1 2 3 4 5) ())))
  )

;; TODO

;; definition grammar
;;   query: (run count (qvars) goal ...)
;;   definition group
;;     (kanren definition ...)
;;     (kanren-define (proc-name svname ...) goal ...)
;;       ; singleton, when mutual recursion isn't needed
;;   definition
;;     (define name goal-expr)
;;     (define (proc-name svname ...) goal ...)
;;       ; defined procedures may be transformed by optimizer
;;   goal
;;     high-level
;;       (fresh (lvname ...) goal ...)
;;       (conde (goal ...) ...)
;;       (== goal-expr goal-expr)
;;       (=/=* `((,goal-expr . ,goal-expr) ...))
;;       (numbero goal-expr)
;;       (symbolo goal-expr)
;;       (absento goal-expr goal-expr)
;;       (proc-name goal-expr ...)
;;     lower-level
;;       (fragment goal-fragment ...)
;;         ; produced by optimizer
;;         ; this sequence must be order-insensitive relative to other goals
;;       conj
;;       disj ; biased, nested disjunctions
;;       disj^ ; fairness-seeking disjunctions that flatten into parent disj
;;       zzz ; pause for interleaving
;;       (let ((svname goal-expr) ...) goal ...)
;;       ? (switches (goal-expr (mutually-exclusive-pattern goal ...) ...) ...)
;;   goal-expr
;;     scheme-var
;;       ; typical, lambda bound variables
;;     atom
;;     `(,goal-expr . ,goal-expr)
;;   value
;;     var
;;       ; logical
;;     atom
;;     `(,value . ,value)
;;   atom
;;     '(), #t, #f, {symbol}, {number}

;; optimization grammar (deal with this later)
;;   fragment-definition group
;;     (fragments fragment-definition ...)
;;   fragment-definition
;;     (define name goal-fragment-expr)
;;     (define (proc-name svname ...) goal-fragment-expr)
;;       ; goal-fragment-expr-proc
;;     (define-goal-fragment (proc-name svname ...) goal-fragment ...)
;;       ; produced by optimizer
;;       ; may be order-sensitive, unlike full procedures
;;   goal-fragment (low-level, semidet, sensitive to ordering, unlike goals)
;;     goal
;;       ; in the middle of a fragment sequence
;;       ;   goal must be applied before rest of fragments
;;       ; in tail position of a fragment sequence
;;       ;   goal behaves normally
;;     (update goal-fragment-expr-proc-name)
;;       ; where the update proc has the form
;;       ; (define (goal-fragment-expr-proc-name old-state:goal-fragment-expr)
;;       ;   new-state:goal-fragment-expr)
;;     (let [goal-fragment-proc-name] ((svname goal-fragment-expr) ...)
;;       goal-fragment ...)
;;     (switches (goal-fragment-expr
;;                 (mutually-exclusive-pattern goal-fragment ...) ...) ...)
;;     (commit)
;;       ; immediately causes current and all sibling disjuncts to succeed
;;       ; only valid if all disjunct answers are guaranteed to be redundant
;;     (goal-fragment-proc-name goal-fragment-expr ...)
;;   goal-fragment-expr
;;     goal-expr
;;     (let [goal-fragment-expr-proc-name] ((svname goal-fragment-expr) ...)
;;       goal-fragment-expr)
;;     (cond (goal-fragment-expr goal-fragment-expr) ...)
;;     (goal-fragment-expr-proc-name goal-fragment-expr ...)
;;     (var=?|eqv? goal-fragment-expr goal-fragment-expr)
;;     (var?|null?|pair?|number?|symbol? goal-fragment-expr)
;;     (car|cdr goal-fragment-expr)
;;     (var-new name:{symbol} state:goal-fragment-expr)
;;     state-empty
;;     (state-put
;;       state:goal-fragment-expr
;;       key:goal-fragment-expr
;;       val:goal-fragment-expr)
;;     (state-get
;;       state:goal-fragment-expr
;;       key:goal-fragment-expr)
;;     (state-get-default
;;       state:goal-fragment-expr
;;       key:goal-fragment-expr
;;       default:goal-fragment-expr)
;;     (unify state:goal-fragment-expr goal-fragment-expr goal-fragment-expr)
;;       ; returns new state, new bindings, and affected constraints
;;     (unify-and-constrain
;;       state:goal-fragment-expr goal-fragment-expr goal-fragment-expr)
;;       ; returns new state, new bindings
;;     constraint-attrs?
;;     constraint-attrs-empty
;;     (constraint-attrs-domain goal-fragment-expr)
;;     (constraint-attrs-domain-set goal-fragment-expr goal-fragment-expr)
;;     (constraint-attrs-absents goal-fragment-expr)
;;     (constraint-attrs-absents-add goal-fragment-expr goal-fragment-expr)
;;     (constraint-attrs-diseqs goal-fragment-expr)
;;     (constraint-attrs-diseqs-add goal-fragment-expr goal-fragment-expr)
;;     (constrain state:goal-fragment-expr constraint:goal-fragment-expr)
;;       ; pre-defined but specializable operations for each constraint type

;; staged scheme unquoting for metaprogramming

;; optional greedy procedure modes to avoid pre-emption while interleaving

;; determinism metrics
;;   at-least : nat (default 1)
;;   at-most : nat or #f (default 0)
;;   at-least=1, at-most=0 corresponds to an error that aborts

;; determinism annotations for goals
;;   conjunctions and fragment sequences
;;     pre-branch unifiable and constrainable var set
;;       these contribute tests, assignments, and expensive constraints
;;   disjunctions
;;     prioritized, switchable vars with determinism metrics for each
;;       these contribute tests and expose more goals at low cost
;;     annotated branches, up to recursion (pre-analysis for recursive info?)
;;       need some measure of determinism within non-switchable branches
;;         decide which of two branching disjunctions will hurt us less
;;         this is where the test vs. assign vs. etc. priorities really matter
;;         when comparing non-switch disjunctions
;;           more tests and expensive constraints are a lot better
;;           more assignments of known vars is better
;;           more recursion is worse
;;           more branching is worse (worse than recursion?)
;;         do we need scoring heuristics?
;;   procedures/zzz
;;     pre-branch unifiable and constrainable param set
;;     priotiized, switchable params with determinism metrics for each

;; dynamically reorderable conjunctions
;;   toggle-able for performance tests, to determine its utility
;;   prefer low branching factors (and seek failure, not just determinism)
;;     least 0, most 0
;;     least 0, most 1
;;     least 1, most 1
;;     least 0, most 2, etc.
;;     ...
;;     least 0, most #f
;;     least 1, most #f, etc.
;;   scheduling priority
;;     tests (including switches)
;;       unification, inexpensive constraints
;;     assignment
;;     expensive constraints
;;     recursion
;;     branching
;;   dynamically inspect bindings in state
;;     to determine which priorities each determinism annotation affects
;;   pre-schedule as much as possible before branching, to share effort
;;     before imminent branching, could follow a greedier strategy

;; simplified strategy operating on normal goals
;;   process deterministic
;;     process all immediately available unifications and constraints
;;     expand procedure applications
;;     loop until only disjunctions remain, or until failure (prune)
;;   prune disjuntions with switch indices
;;     for each such disjunction
;;       for each indexed variable in priority order
;;         match current state's binding in index and return sub-disjunction
;;         if no binding, try next indexed variable
;;   prune and build switch indices for new disjunctions
;;     for each disjunction
;;       start an empty switch index
;;       for each branch
;;         process immediates, but without expanding procedures
;;         then prune their disjunctions
;;           fail if any become empty
;;           merge singleton branches into parent and process
;;           merge entries from sub-indices into current switch index
;;             each sub-branch appears deterministically embedded in its parent
;;               e.g.  (disj (conj X=a (disj (conj Y=d P...) (conj Y=e Q...)))
;;                           (conj X=b (disj (conj Y=e R...) (conj Y=f S...)))
;;                           (conj X=c Y=e)))
;;               This disj has an index for X with single entries for a,b,c:
;;                 X=a: (disj (conj Y=d P...) (conj Y=e Q...))
;;                 X=b: (disj (conj Y=e R...) (conj Y=f S...))
;;                 X=c: Y=e
;;               The first and second branches have sub-indices for Y
;;                 with d,e and e,f respectively
;;               Each sub-index is merged into the parent Y index:
;;                 Y=d: (conj X=a P...)
;;                 Y=e: (disj (conj X=a Q...) (conj X=b R...) X=c)
;;                 Y=f: (conj X=b S...)
;;                 Notice the sub-branches embedded directly in parents
;;               Note: Although both X and Y discriminate 3 ways
;;               and Y appears more embedded in X, Y's entries seem more
;;               deterministic, so we should prioritize it.  Bucket count
;;               seems an imperfect heuristic.  Maybe not a big deal.  Even
;;               after switching on X, if Y was also set, it will prune easily
;;               when processing "new" disjunctions (same in this case, but not
;;               in general; consider switching on Y instead).
;;         replace immediates with residual unifications and constraints
;;         add to switch index for tested variables
;;           for each variable tested (not newly-assigned) in any branch
;;             add this branch to bucket for the value type tested
;;             or, if it doesn't test it, the non-test bucket
;;         forget state and return updated branch to parent
;;       if new determinism available (single branch remains)
;;         abort pruning and loop from the top
;;       otherwise, process built switch
;;         for pair-test buckets with multiple entries
;;           reduce to component tests; build sub-indices for bucketed branches
;;         sort variables to prioritize number of buckets (more is better)
;;         optionally build cross/join indices for simultaneously-assigned vars
;;           embed these within var with earliest index priority
;;           just like building a normal index, but per-bucket of embedding var
;;           could do this for all pairs, all triples, etc. is it worth it?
;;             devise "worth it" heuristic to avoid spending too much time
;;   still only disjunctions remain
;;     choose a branch and split state
;;       prefer informative branches (more relevant assignments)
;;         relevant assignments are for vars that are widely tested
;;         fresh vars introduced in a branch are not informative
;;       prefer longer/deeper (yes!) branches
;;         particularly those with recursive calls (with relevant arguments)
;;           branches with recursion may be hiding helpful info
;;         why longer? branches with unhelpful info are useless, shallow or not
;;           while traversing longer branch, unhelpful info in shallow branches
;;           may turn helpful, in which case they will be revisited naturally
;;       otherwise, prefer disjunctions with fewer branches
;;       remember: when considering two conjuncted disjunctions, it may be
;;       helpful to traverse some branches in one, then some branches in
;;       the other before completing the first (no fixed order)
;;   Note: When pruning subsequent states, would be nice to only consider
;;   unifications/constraints that may be affected by new information.  It also
;;   might be helpful to support multiple simultaneous variable lookup.  This
;;   could start looking like database joining.

;; basic path-sensitive flow analysis
;;   for each definition not yet processed
;;     partially evaluate up to procedure calls
;;       should eliminate unnecessary logic vars and simplify some goals
;;       possibly extract common sub-expressions and identify switches here
;;         switch summary information could improve dynamic pruning performance
;;     enter called definitions
;;       process that definition independently
;;       if it turns out the call is (mutually-)recursive, truncate it
;;         recursion indicated by call to unfinished proc definition
;;         later, might allow inlining of recursive deterministic prefix
;;       otherwise, inline the processed result and partially evaluate
;;   later, may analyze multiple parameter modes for exported definitions
;;     exports determine entry points, so parameter modes could be anything

;; lift common sub-exprs out of disjunctions
;;   MSG?

;; switches: mutually-exclusive disjunctions
;;   'switchable?' flags/priorities for relation arguments
;;     priorities for attempting best indexing first

;; states
;;   known value OR (domain-info, attributed constraints)
;;   constraints
;;     initially
;;       disequality
;;       absence
;;     eventually
;;       finite domain operations
;;   domain info
;;     initially, just possible type vs. known value
;;     eventually, lattice that subsumes variable binding
;;       unknown, optional not-types, optional not-values
;;       finite domain, set of values across types
;;       finite domain, any value of a particular type
;;       finite domain, set of values within one type
;;       numeric intervals
;;       known value

;; TODO later

;; simplified unifications
;;   simple tests
;;   assignments
;;   constructions
;;   deconstructions
;;   recursively apply simplifications
;; analogous simplifications for general constraints?
;; split complex operations (like unification)
;;   e.g. minimize/share lookups/derefs
;; commits for eliminating redundant answers

;; low-level optimization
;;   fact support (regular, large disjunctions)
;;     exo-compilation
;;     limited forward-chaining
;;     embedding fact tables in substitutions
;;       delay splitting states (disjunctions normally split)
;;       avoids mostly-redundant state exploration
;;   region-based garbage collection
;;   path compression
;;   mutation of locally-scoped (non-split) vars
;;   substitution vectors (registerization?) for faster lookup
;;     only for guaranteed use

;; optional static det/type checking

;; relation tagging for dynamic recursion/termination analysis?
;; step quota to preempt expensive deterministic processes (ackerman)

;; abstract interpretation
;;   shape and instantiation states for vars
;;     unknown boundness
;;     unbound
;;     bound but unknown shape
;;     bound to shape from a finite set
;;     bound to a particular shape
;;     instantiation/shape information is recursive for pairs

(module+ test
  (require racket/set)

  (define-syntax mk-test-cont
    (syntax-rules ()
      ((_ test-name exact? query expected)
       (let* ((result-set (list->set query))
              (expected-set (list->set expected))
              (overlap (set-intersect result-set expected-set)))
         (if exact?
           (begin
             (when (not (equal? result-set expected-set))
               (displayln (format "failed test: ~a" test-name)))
             ;(check-equal? (set-subtract expected-set result-set) (set))
             ;(check-equal? (set-subtract result-set expected-set) (set))
             (check-equal? result-set expected-set))
           (check-equal? overlap expected-set))))))
  (define-syntax mk-test
    (syntax-rules ()
      ((_ test-name query expected)
        (mk-test-cont test-name #t query expected))))

  (mk-test "numbero-2"
    (run* (q) (numbero q) (== 5 q))
    '((5)))

  (mk-test "numbero-3"
    (run* (q) (== 5 q) (numbero q))
    '((5)))

  (mk-test "numbero-4"
    (run* (q) (== 'x q) (numbero q))
    '())

  (mk-test "numbero-5"
    (run* (q) (numbero q) (== 'x q))
    '())

  (mk-test "numbero-6"
    (run* (q) (numbero q) (== `(1 . 2) q))
    '())

  (mk-test "numbero-7"
    (run* (q) (== `(1 . 2) q) (numbero q))
    '())

  (mk-test "numbero-8"
    (run* (q) (fresh (x) (numbero x)))
    '((_.0)))

  (mk-test "numbero-9"
    (run* (q) (fresh (x) (numbero x)))
    '((_.0)))

  (mk-test "numbero-14-b"
    (run* (q) (fresh (x) (numbero q) (== 5 x) (== x q)))
    '((5)))

  (mk-test "numbero-15"
    (run* (q) (fresh (x) (== q x) (numbero q) (== 'y x)))
    '())

  (mk-test "symbolo-2"
    (run* (q) (symbolo q) (== 'x q))
    '((x)))

  (mk-test "symbolo-3"
    (run* (q) (== 'x q) (symbolo q))
    '((x)))

  (mk-test "symbolo-4"
    (run* (q) (== 5 q) (symbolo q))
    '())

  (mk-test "symbolo-5"
    (run* (q) (symbolo q) (== 5 q))
    '())

  (mk-test "symbolo-6"
    (run* (q) (symbolo q) (== `(1 . 2) q))
    '())

  (mk-test "symbolo-7"
    (run* (q) (== `(1 . 2) q) (symbolo q))
    '())

  (mk-test "symbolo-8"
    (run* (q) (fresh (x) (symbolo x)))
    '((_.0)))

  (mk-test "symbolo-9"
    (run* (q) (fresh (x) (symbolo x)))
    '((_.0)))

  (mk-test "symbolo-14-b"
    (run* (q) (fresh (x) (symbolo q) (== 'y x) (== x q)))
    '((y)))

  (mk-test "symbolo-15"
    (run* (q) (fresh (x) (== q x) (symbolo q) (== 5 x)))
    '())

  (mk-test "symbolo-numbero-1"
    (run* (q) (symbolo q) (numbero q))
    '())

  (mk-test "symbolo-numbero-2"
    (run* (q) (numbero q) (symbolo q))
    '())

  (mk-test "symbolo-numbero-3"
    (run* (q)
      (fresh (x)
        (numbero x)
        (symbolo x)))
    '())

  (mk-test "symbolo-numbero-4"
    (run* (q)
      (fresh (x)
        (symbolo x)
        (numbero x)))
    '())

  (mk-test "symbolo-numbero-5"
    (run* (q)
      (numbero q)
      (fresh (x)
        (symbolo x)
        (== x q)))
    '())

  (mk-test "symbolo-numbero-6"
    (run* (q)
      (symbolo q)
      (fresh (x)
        (numbero x)
        (== x q)))
    '())

  (mk-test "symbolo-numbero-7"
    (run* (q)
      (fresh (x)
        (numbero x)
        (== x q))
      (symbolo q))
    '())

  (mk-test "symbolo-numbero-7"
    (run* (q)
      (fresh (x)
        (symbolo x)
        (== x q))
      (numbero q))
    '())

  (mk-test "symbolo-numbero-8"
    (run* (q)
      (fresh (x)
        (== x q)
        (symbolo x))
      (numbero q))
    '())

  (mk-test "symbolo-numbero-9"
    (run* (q)
      (fresh (x)
        (== x q)
        (numbero x))
      (symbolo q))
    '())

  (mk-test "test 24"
    (run* (q) (== 5 q) (absento 5 q))
    '())

  (mk-test "test 25"
    (run* (q) (== q `(5 6)) (absento 5 q))
    '())

  (mk-test "test 25b"
    (run* (q) (absento 5 q) (== q `(5 6)))
    '())

  (mk-test "test 26"
    (run* (q) (absento 5 q) (== 5 q))
    '())

  (mk-test "test 33"
    (run* (q)
      (fresh (a b c)
        (== `(,a ,b) c)
        (== `(,c ,c) q)
        (symbolo b)
        (numbero c)))
    '())

  (mk-test "test 41"
    (run* (q)
      (fresh (a)
        (== `(,a . ,a) q)))
    '(((_.0 . _.0))))

  (mk-test "test 64"
    (run* (q) (symbolo q) (== 'tag q))
    '((tag)))

  (mk-test "test 66"
    (run* (q) (absento 6 5))
    '((_.0)))

  (mk-test "absento 'closure-1a"
    (run* (q) (absento 'closure q) (== q 'closure))
    '())

  (mk-test "absento 'closure-1b"
    (run* (q) (== q 'closure) (absento 'closure q))
    '())

  (mk-test "absento 'closure-2a"
    (run* (q) (fresh (a d) (== q 'closure) (absento 'closure q)))
    '())

  (mk-test "absento 'closure-2b"
    (run* (q) (fresh (a d) (absento 'closure q) (== q 'closure)))
    '())

  (mk-test "absento 'closure-4a"
    (run* (q) (fresh (a d) (absento 'closure q) (== `(,a . ,d) q) (== 'closure a)))
    '())

  (mk-test "absento 'closure-4b"
    (run* (q) (fresh (a d) (absento 'closure q) (== 'closure a) (== `(,a . ,d) q)))
    '())

  (mk-test "absento 'closure-4c"
    (run* (q) (fresh (a d) (== 'closure a) (absento 'closure q) (== `(,a . ,d) q)))
    '())

  (mk-test "absento 'closure-4d"
    (run* (q) (fresh (a d) (== 'closure a) (== `(,a . ,d) q) (absento 'closure q)))
    '())

  (mk-test "absento 'closure-5a"
    (run* (q) (fresh (a d) (absento 'closure q) (== `(,a . ,d) q) (== 'closure d)))
    '())

  (mk-test "absento 'closure-5b"
    (run* (q) (fresh (a d) (absento 'closure q) (== 'closure d) (== `(,a . ,d) q)))
    '())

  (mk-test "absento 'closure-5c"
    (run* (q) (fresh (a d) (== 'closure d) (absento 'closure q) (== `(,a . ,d) q)))
    '())

  (mk-test "absento 'closure-5d"
    (run* (q) (fresh (a d) (== 'closure d) (== `(,a . ,d) q) (absento 'closure q)))
    '())

  (mk-test "absento 'closure-6"
    (run* (q)
      (== `(3 (closure x (x x) ((y . 7))) #t) q)
      (absento 'closure q))
    '())
    )
