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

;; grammar
;;   query: (run count (qvars) goal ...)
;;   procedure-definition group
;;     (procedure-definitions procedure-definition ...)
;;   procedure-definition
;;     (define proc-name (lambda (svname ...) goal ...))
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
;;     low-level
;;       conj, disj, disj^, zzz
;;   goal-expr
;;     scheme-var
;;     atom
;;     `(,goal-expr . ,goal-expr)
;;   value
;;     logic-var
;;     atom
;;     `(,value . ,value)
;;   atom
;;     '(), #t, #f, {symbol}, {number}
;;   goal-fragment (low-level, sensitive to ordering, unlike goals)
;;     goal
;;     (state-current-put goal-fragment-expr)
;;       ; maybe replace this with a (lambda (st) ...)
;;     (begin goal-fragment ...)
;;     (let ((svname goal-fragment-expr) ...) goal-fragment)
;;     (switch goal-expr (mutually-exclusive-pattern goal-fragment ...) ...)
;;     (commit)
;;   goal-fragment-expr
;;     goal-expr
;;     (let ((svname goal-fragment-expr) ...) goal-fragment-expr)
;;     (cond (goal-fragment-expr goal-fragment-expr) ...)
;;     (app goal-fragment-expr goal-fragment-expr ...)
;;     var?, var=?, eqv?, null?, pair?, number?, symbol?
;;     car, cdr
;;     (var-new name:{symbol} state:goal-fragment-expr)
;;     state-empty
;;     (state-current-get)
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
;;     (constrain state:goal-fragment-expr constraint:goal-fragment-expr)
;;       ; pre-defined but specializable operations for each constraint type
;; staged scheme unquoting for metaprogramming

;; determinism annotations for goals
;;   TODO

;; biased, nested disjunctions
;; fairness-seeking flattening disjunctions
;; dynamically re-orderable conjuntions
;;   toggle-able for performance tests, to determine its utility
;;   what goal annotations do we need?
;;   prefer low branching factors (and seek failure!)
;;     least 0, most 0
;;     least 0, most 1
;;     least 1, most 1
;;     least 0, most 2, etc.
;;     ...
;;     least 0, most #f
;;     least 1, most #f, etc.

;; determinism flags
;;   at-least : nat (default 1)
;;   at-most : nat or #f (default 0)
;;   at-least=1, at-most=0 corresponds to an error that aborts

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
