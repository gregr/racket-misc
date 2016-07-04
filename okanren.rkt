#lang racket/base
(provide

  )

(require

  )

(module+ test
  (require
    rackunit
    ))


;; TODO

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

;; shape and instantiation states for vars
;;   unbound
;;   bound but unknown shape
;;   bound to shape from a finite set
;;   bound to a particular shape
;;   instantiation/shape information is recursive for pairs
;; switches: mutually-exclusive disjunctions
;;   'switchable?' flags/priorities for relation arguments
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

;; staged scheme for metaprogramming
;; optional static det/type checking

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

;; relation tagging for dynamic recursion/termination analysis?
;; step quota to preempt expensive deterministic processes (ackerman)

;; terms
;;   logic vars
;;   pairs
;;   eqv?-relatable atoms
;;     void, nil, bool, sym, num
;;     eq? non-vector aggs

;; constraint lattice that subsumes variable binding
