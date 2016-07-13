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

(define (unit st) st)
(define (conj g0 g1) (lambda (st) (g1 (g0 st))))
(define-syntax conj*
  (syntax-rules ()
    ((_) unit)
    ((_ goal) goal)
    ((_ goal goals ...) (conj goal (conj* goals ...)))))

(record ok-state bindings cxs apps disjs)
(define ok-state-empty (ok-state '() '() '() '()))
(define (ok-state-apps-add st app)
  (ok-state (ok-state-bindings st)
            (ok-state-cxs st)
            (cons app (ok-state-apps st))
            (ok-state-disjs st)))

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
