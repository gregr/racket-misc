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

;; optimization grammar
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
;;     (goal goal)
;;       ; in the middle of a fragment sequence
;;       ;   goal must be applied before rest of fragments
;;       ;   must be guaranteed to produce at most one answer
;;       ; in tail position of a fragment sequence
;;       ;   goal behaves normally
;;     (update goal-fragment-expr-proc-name)
;;       ; where the update proc has the form
;;       ; (define (goal-fragment-expr-proc-name old-state:goal-fragment-expr)
;;       ;   new-state:goal-fragment-expr)
;;     (let [goal-fragment-proc-name] ((svname goal-fragment-expr) ...)
;;       goal-fragment ...)
;;     (switch goal-expr (mutually-exclusive-pattern goal-fragment ...) ...)
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

;; determinism annotations for goals
;;   TODO

;; determinism flags
;;   at-least : nat (default 1)
;;   at-most : nat or #f (default 0)
;;   at-least=1, at-most=0 corresponds to an error that aborts

;; dynamically reorderable conjuntions
;;   toggle-able for performance tests, to determine its utility
;;   prefer low branching factors (and seek failure, not just determinism)
;;     least 0, most 0
;;     least 0, most 1
;;     least 1, most 1
;;     least 0, most 2, etc.
;;     ...
;;     least 0, most #f
;;     least 1, most #f, etc.
;;   priority
;;     tests (including switches)
;;       unification, inexpensive constraints
;;     assignment
;;     expensive constraints
;;     recursion
;;     branching

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
