#lang racket/base
(provide
  run-config-c
  runc
  runc*
  runc-depth
  runc*-depth
  )

(require
  "dict.rkt"
  "integer-set.rkt"
  "maybe.rkt"
  "microkanren.rkt"
  "minikanren.rkt"
  "num.rkt"
  "record.rkt"
  "set.rkt"
  "sugar.rkt"
  data/integer-set
  racket/function
  (except-in racket/match ==)
  (except-in racket/set subset?)
  )

(module+ test
  (require
    rackunit
    ))

(define (set->integer-set lb ub xs)
  (define (valid-int? val) (and (exact-integer? val)
                                (or (not lb) (<= lb val))
                                (or (not ub) (<= val ub))))
  (list->integer-set (filter valid-int? (set->list xs))))

(module+ test
  (check-equal? (set->integer-set #f 10 (set 3 7 10 12 14 -6 5 8 6 -7))
                (integer-set '((-7 . -6) (3 . 3) (5 . 8) (10 . 10)))))

(record constraints var=>desc pending)
(def (constraints-var=>desc-set (constraints _ pending) var=>desc)
  (constraints var=>desc pending))
(def (constraints-pending-set (constraints v=>d _) pending)
  (constraints v=>d pending))
(define constraints-empty (constraints (hasheq) set-empty))
(define state-empty (muk-state-empty/constraints constraints-empty))
(define (state-constraints-var=>desc st)
  (constraints-var=>desc (muk-state-constraints st)))
(define (state-constraints-pending st)
  (constraints-pending (muk-state-constraints st)))
(define (state-constraints-var=>desc-set st var=>desc)
  (muk-state-constraints-set
    st (constraints-var=>desc-set (muk-state-constraints st) var=>desc)))
(define (state-constraints-pending-set st pending)
  (muk-state-constraints-set
    st (constraints-pending-set (muk-state-constraints st) pending)))

; TODO: enums and intervals: infd, not-infd, all-difffd
; TODO: integer intervals: <fd, -fd

; ideally this would support aggregate values and be expressed as a lattice...
(records fd-domain
  (unknown-fd not-in)
  (typed name type? not-in)
  (enumeration domain)
  (int-interval-unbounded lb ub not-in)
  (int-interval int-set))
(record fd-desc dom cxs)
(define fd-desc-empty (fd-desc #t set-empty))
(define fd-invalid (fd-desc #f set-empty))

(define-syntax def-cx
  (syntax-rules ()
    ((_ def-name cx-name args ...)
     (define (def-name args ...) (muk-constraint 'cx-name (list args ...))))))

(def-cx typeo type val ty)
(def-cx domainfd domain val domain)
(def-cx betweenfd between val lb ub)
(def-cx not-infd not-in val domain)
(def-cx not-betweenfd not-between val wfs)
(def-cx !=fd != lhs rhs)
(def-cx <=fd <= lhs rhs)
(def-cx +fd + lhs rhs result)
(def-cx *fd * lhs rhs result)

(define types (make-immutable-hash
                `((symbol . ,symbol?)
                  (number . ,number?)
                  (char . ,char?)
                  (string . ,string?)
                  )))

(define (fd-enum domain)
  (cond ((set-empty? domain) #f)
        ((andmap exact-integer? (set->list domain))
         (fd-int-interval (set->integer-set #f #f domain)))
        (else (enumeration domain))))

(define (fd-int-interval-unbounded lb ub not-in)
  (if (and lb ub)
    (and (<= lb ub) (fd-int-interval (subtract (make-range lb ub) not-in)))
    (int-interval-unbounded
      (integer-set-lb-subtract lb not-in)
      (integer-set-ub-subtract ub not-in)
      not-in)))

(define (fd-int-interval int-set)
  (and (get-integer int-set)
       (match (integer-set-contents int-set)
         ((list (cons lb ub)) (if (= lb ub) (enumeration (set lb))
                                (int-interval int-set)))
         (_ (int-interval int-set)))))

(define (fd-domain-satisfy dom val)
  (match dom
    ((unknown-fd not-in) (not (set-member? not-in val)))
    ((typed _ type? not-in) (and (type? val) (not (set-member? not-in val))))
    ((enumeration domain) (set-member? domain val))
    ((int-interval-unbounded lb ub not-in)
     (and (exact-integer? val)
          (or (not lb) (<= lb val)) (or (not ub) (<= val ub))
          (not (member? val not-in))))
    ((int-interval int-set) (and (exact-integer? val) (member? val int-set)))
    (#f #f)))

(define (fd-domain-meet lhs rhs)
  (match* (lhs rhs)
    ((#f _) #f)
    ((#t _) rhs)
    (((unknown-fd not-in-lhs) (unknown-fd not-in-rhs))
     (unknown-fd (set-union not-in-lhs not-in-rhs)))
    (((typed name-lhs type? not-in-lhs) (typed name-rhs _ not-in-rhs))
     (and (eq? name-lhs name-rhs)
          (typed name-lhs type? (set-union not-in-lhs not-in-rhs))))
    (((typed name type? not-in-lhs) (unknown-fd not-in-rhs))
     (typed name type? (set-union not-in-lhs (set-filter type? not-in-rhs))))
    (((enumeration domain-lhs) (enumeration domain-rhs))
     (fd-enum (set-intersect domain-lhs domain-rhs)))
    (((enumeration domain) (typed name type? not-in))
     (fd-enum (set-subtract (set-filter type? domain) not-in)))
    (((enumeration domain) (unknown-fd not-in))
     (fd-enum (set-subtract domain not-in)))
    (((int-interval-unbounded lb-lhs ub-lhs not-in-lhs)
      (int-interval-unbounded lb-rhs ub-rhs not-in-rhs))
     (fd-int-interval-unbounded
       (or (and lb-lhs lb-rhs (max lb-lhs lb-rhs)) lb-lhs lb-rhs)
       (or (and ub-lhs ub-rhs (min ub-lhs ub-rhs)) ub-lhs ub-rhs)
       (union not-in-lhs not-in-rhs)))
    (((int-interval-unbounded lb ub not-in) (enumeration domain))
     (fd-int-interval (subtract (set->integer-set lb ub domain) not-in)))
    (((int-interval-unbounded lb ub not-b) (typed name type? not-in)) #f)
    (((int-interval-unbounded lb ub not-b) (unknown-fd not-in))
     (fd-int-interval-unbounded
       lb ub (union not-b (set->integer-set lb ub not-in))))
    (((int-interval int-set-lhs) (int-interval int-set-rhs))
     (fd-int-interval (intersect int-set-lhs int-set-rhs)))
    (((int-interval int-set) (int-interval-unbounded lb ub not-b))
     (lets (values mn mx) = (integer-set-extrema int-set)
           (fd-int-interval
             (intersect (make-range (or lb mn) (or ub mx))
                        (subtract int-set not-b)))))
    (((int-interval int-set) (enumeration domain))
     (fd-int-interval (intersect int-set (set->integer-set #f #f domain))))
    (((int-interval int-set) (typed name type? not-in)) #f)
    (((int-interval int-set) (unknown-fd not-in))
     (fd-int-interval (subtract int-set (set->integer-set #f #f not-in))))
    ((_ _) (fd-domain-meet rhs lhs))))

(define (unify st e0 e1) (match (muk-unify st e0 e1)
                           ((nothing) #f)
                           ((just st) st)))

(define (fd-domain-update st obj dom-rhs)
  (and st
    (if (muk-var? obj)
      (lets
        vr = obj
        var=>desc = (state-constraints-var=>desc st)
        (fd-desc dom-lhs cxs) = (hash-ref var=>desc vr fd-desc-empty)
        result = (fd-domain-meet dom-lhs dom-rhs)
        (match result
          (#f #f)
          ((enumeration (? (compose1 (curry = 1) set-count) sset))
           (lets st = (state-constraints-var=>desc-set
                        st (hash-remove var=>desc vr))
                 st = (reschedule-constraints st cxs vr)
                 (list singleton) = (set->list sset)
                 (unify st vr singleton)))
          (_ (lets (values update-cxs keep-cxs) =
                   (if (not (equal? dom-lhs result))
                     (values cxs set-empty) (values set-empty cxs))
                   st = (state-constraints-var=>desc-set
                          st (hash-set var=>desc vr (fd-desc result keep-cxs)))
                   (reschedule-constraints st update-cxs vr)))))
      (and (fd-domain-satisfy dom-rhs obj) st))))

(def (reschedule-constraints st cxs vr-source)
  peers = (forf peers = set-empty
                (cons _ args) <- cxs
                (set-union peers (list->set (filter muk-var? args))))
  peers = (set-remove peers vr-source)
  st = (state-constraints-var=>desc-set st
         (forf var=>desc = (state-constraints-var=>desc st)
               peer <- peers
               (hash-update-if-has var=>desc peer
                 (fn ((fd-desc dom peer-cxs))
                   (fd-desc dom (set-subtract peer-cxs cxs))))))
  pending = (set-union cxs (state-constraints-pending st))
  (state-constraints-pending-set st pending))

(def (type->fd-domain name)
  type? = (hash-ref types name #f)
  (if type? (typed name type? set-empty) #f))
(define (domain->fd-domain domain)
  (if (andmap exact-integer? domain)
    (fd-int-interval (list->integer-set domain))
    (fd-enum (list->set domain))))
(define (between->fd-domain lb ub) (fd-int-interval (make-range lb ub)))
(define (not-in->fd-domain domain) (unknown-fd (list->set domain)))
(define (not-between->fd-domain wfs)
  (fd-int-interval-unbounded #f #f (make-integer-set wfs)))

(def (add-constraint st name args)
  (cons obj rargs) = args
  fdd = (match name
          ('between (lets (list lb ub) = rargs
                          (between->fd-domain lb ub)))
          ('not-between (lets (list wfs) = rargs
                              (not-between->fd-domain wfs)))
          ('domain (lets (list domain) = rargs
                         (domain->fd-domain domain)))
          ('not-in (lets (list domain) = rargs
                         (not-in->fd-domain domain)))
          ('type (lets (list type-name) = rargs
                       (type->fd-domain type-name)))
          (_ #f))
  (if fdd (fd-domain-update st obj fdd)
    (state-constraints-pending-set
      st (set-add (state-constraints-pending st) (cons name args)))))

(def (constrain-new-bindings st)
  (values st new-bindings) = (muk-sub-new-bindings st)
  st-new = (forf st = st
                 vr <- new-bindings
                 #:break (not st)
                 var=>desc = (state-constraints-var=>desc st)
                 current = (hash-ref var=>desc vr #f)
                 (if current
                   (lets (fd-desc rhs cxs) = current
                         st = (state-constraints-var=>desc-set
                                st (hash-remove var=>desc vr))
                         st = (reschedule-constraints st cxs vr)
                         (values st lhs) = (muk-sub-get st vr)
                         (fd-domain-update st lhs rhs))
                   st))
  (if (or (not st-new) (eq? st st-new)) st-new
    (constrain-new-bindings st-new)))

(define (suspend-constraint st name args)
  (and st
       (lets
         vars = (filter muk-var? args)
         (state-constraints-var=>desc-set
           st (forf var=>desc = (state-constraints-var=>desc st)
                    vr <- vars
                    (hash-update var=>desc vr
                      (fn ((fd-desc dom cxs))
                          (fd-desc dom (set-add cxs (cons name args))))
                      fd-desc-empty))))))

(define ii-empty (int-interval-unbounded #f #f integer-set-empty))
(define fd-ii-empty (fd-desc ii-empty set-empty))

(define (fdd->ii fdd)
  (match fdd
    ((enumeration domain) (fd-int-interval (set->integer-set #f #f domain)))
    ((typed name _ _) #f)
    ((unknown-fd not-in)
     (int-interval-unbounded #f #f (set->integer-set #f #f not-in)))
    (#t ii-empty)
    (_ fdd)))

(define (scalar->ii scalar) (int-interval (make-range scalar)))

(def (lookup-integer st key)
  v=>d = (state-constraints-var=>desc st)
  (values v=>d fd) =
  (if (muk-var? key)
    (lets (fd-desc fdd cxs) = (hash-ref v=>d key fd-ii-empty)
          fd = (fd-desc (fdd->ii fdd) cxs)
          v=>d = (hash-set v=>d key fd)
          (values v=>d fd))
    (if (exact-integer? key)
      (values v=>d (fd-desc (scalar->ii key) set-empty))
      (values #f fd-invalid)))
  st = (and v=>d (state-constraints-var=>desc-set st v=>d))
  (values st fd))

(define (walk st val) (if st (muk-walk st val) (values #f val)))

(def (constrain-eval-binop solve st name args)
  (list lhs rhs) = args
  (values st lfdd) = (lookup-integer st lhs)
  (values st rfdd) = (lookup-integer st rhs)
  (fd-desc lfd lcxs) = lfdd
  (fd-desc rfd rcxs) = rfdd
  (and st
       (lets
         (values lfd rfd) = (solve lfd rfd)
         st = (fd-domain-update st lhs lfd)
         st = (fd-domain-update st rhs rfd)
         (values st lhs) = (walk st lhs)
         (values st rhs) = (walk st rhs)
         args = (list lhs rhs)
         (if (= 2 (length (filter muk-var? (list lhs rhs))))
           (suspend-constraint st name args)
           st))))

; TODO: generalize this and the binop case
(def (constrain-eval-arithop solve st name args)
  (list lrand rrand result) = args
  (values st lfdd) = (lookup-integer st lrand)
  (values st rfdd) = (lookup-integer st rrand)
  (values st resfdd) = (lookup-integer st result)
  (fd-desc lfd lcxs) = lfdd
  (fd-desc rfd rcxs) = rfdd
  (fd-desc resfd rescxs) = resfdd
  (and st
       (lets
         (values lfd rfd resfd) = (solve lfd rfd resfd)
         st = (fd-domain-update st lrand lfd)
         st = (fd-domain-update st rrand rfd)
         st = (fd-domain-update st result resfd)
         (values st lrand) = (walk st lrand)
         (values st rrand) = (walk st rrand)
         (values st result) = (walk st result)
         args = (list lrand rrand result)
         (suspend-constraint st name args))))

(define (int-interval-extrema ii)
  (match ii
    ((int-interval-unbounded lb ub _) (values lb ub))
    ((int-interval iset) (integer-set-extrema iset))
    ((enumeration (? (compose1 (curry = 1) set-count) dom))
     (values (set-first dom) (set-first dom)))))

(def (int-interval-invert ii)
  (values lb ub) = (int-interval-extrema ii)
  ub-new = (and lb (- lb))
  lb-new = (and ub (- ub))
  (fd-int-interval-unbounded lb-new ub-new integer-set-empty))

(def (constrain-!= st args)
  (list lhs rhs) = args
  (and (not (equal? lhs rhs))
       (if (muk-var? lhs)
         (if (muk-var? rhs)
           (lets var=>desc = (state-constraints-var=>desc st)
                 (fd-desc dom-lhs cxs) = (hash-ref var=>desc lhs fd-desc-empty)
                 (fd-desc dom-rhs cxs) = (hash-ref var=>desc rhs fd-desc-empty)
                 (if (fd-domain-meet dom-lhs dom-rhs)
                   (suspend-constraint st '!= args)
                   st))
           (fd-domain-update st lhs (unknown-fd (set rhs))))
         (if (muk-var? rhs)
           (fd-domain-update st rhs (unknown-fd (set lhs)))
           st))))

(define (solve-+ ld rd ad)
  (define (solve ld rd ad)
    (and ld rd ad
         (lets (values llb lub) = (int-interval-extrema ld)
               (values rlb rub) = (int-interval-extrema rd)
               (values alb aub) = (int-interval-extrema ad)
               ub = (minb (and lub rub (+ lub rub)) aub)
               lb = (maxb (and llb rlb (+ llb rlb)) alb)
               (fd-int-interval-unbounded lb ub integer-set-empty))))
  (lets
    ad = (fd-domain-meet ad (solve ld rd ad))
    ld = (fd-domain-meet ld (solve ad (and rd (int-interval-invert rd)) ld))
    rd = (fd-domain-meet rd (solve ad (and ld (int-interval-invert ld)) rd))
    (values ld rd ad)))

(def (constrain-eval st)
  pending = (state-constraints-pending st)
  (if (set-empty? pending) st
    (lets fst = (set-first pending)
          pending = (set-remove pending fst)
          st = (state-constraints-pending-set st pending)
          (cons name args) = fst
          (values st rargs) =
          (forf st = st wargs = '()
                arg <- args
                (values st wa) = (muk-walk st arg)
                (values st (list* wa wargs)))
          args = (reverse rargs)
          (match name
            ('<= (constrain-eval-binop
                   (fn (lfd rfd)
                     (values llb lub) = (int-interval-extrema lfd)
                     (values rlb rub) = (int-interval-extrema rfd)
                     lub = (minb lub rub)
                     rlb = (maxb llb rlb)
                     (values
                       (fd-int-interval-unbounded llb lub integer-set-empty)
                       (fd-int-interval-unbounded rlb rub integer-set-empty)))
                   st '<= args))
            ('!= (constrain-!= st args))
            ('+ (constrain-eval-arithop solve-+ st '+ args))
            ;('* (constrain-eval-arithop ))
            ))))

(define (constrain st)
  (letn loop st = st
    st = (constrain-new-bindings st)
    st-new = (and st (constrain-eval st))
    (if (not st-new) '()
      (if (eq? st st-new) (list st-new) (loop st-new)))))

(define c-eval (muk-evaluator muk-unify add-constraint constrain))
; TODO: improve constraint visualization
(def (reify-constraints st)
  (constraints var=>desc pending) = (muk-state-constraints st)
  (forl (cons mv fdd) <- (hash->list var=>desc)
        (cons (muk-var-name mv) fdd)))
(define (c-reify vr st)
  (list* (muk-reify-term st vr muk-var->symbol)
         (reify-constraints st)))

(define run-config-c
  (run-config (curry c-eval state-empty) c-reify))

(define-syntax runc-depth
  (syntax-rules ()
    ((_ n depth body ...) (run/config run-config-c n depth body ...))))
(define-syntax runc*-depth
  (syntax-rules () ((_ body ...) (runc-depth #f body ...))))
(define-syntax runc
  (syntax-rules () ((_ n body ...) (runc-depth n 1 body ...))))
(define-syntax runc*
  (syntax-rules () ((_ body ...) (runc #f body ...))))

; TODO: runc*
(module+ test
  (check-equal?
    (runc 1 q (typeo q 'symbol) (== q 'a))
    '((a)))
  (check-equal?
    (runc 1 q (typeo q 'symbol) (== q 3))
    '())
  (check-equal?
    (runc 1 q (typeo q 'symbol) (domainfd q '(3 a #t)) (== q 'a))
    '((a)))
  (check-equal?
    (runc 1 q (typeo q 'symbol) (domainfd q '(3 a #t)) (== q 'b))
    '())
  (check-equal?
    (runc 1 q (typeo q 'symbol) (domainfd q '(3 #t)))
    '())
  (check-equal?
    (runc 1 q (typeo q 'symbol) (domainfd q '(3 a #t)) (== q 3))
    '())
  (check-equal?
    (runc 1 q (domainfd q '(c)))
    '((c)))
  (check-equal?
    (runc 1 q (domainfd q '(3)))
    '((3)))
  (check-equal?
    (runc 1 q (domainfd q '(4 a)) (!=fd q 'a))
    '((4)))
  (check-equal?
    (runc 1 (q r) (domainfd q '(4 b)) (== r 'b) (!=fd q r))
    '(((4 b))))
  (check-equal?
    (runc 1 (q r) (!=fd q r) (domainfd q '(4 b)) (== r 'b))
    '(((4 b))))
  (check-equal?
    (runc 1 q (betweenfd q -3 10) (== q -4))
    '())
  (check-equal?
    (runc 1 q (betweenfd q -3 10) (== q -3))
    '((-3)))
  (check-equal?
    (runc 1 q (betweenfd q -3 10) (== q 5))
    '((5)))
  (check-equal?
    (runc 1 q (betweenfd q -3 10) (== q 10))
    '((10)))
  (check-equal?
    (runc 1 q (betweenfd q -3 10) (== q 11))
    '())
  (check-equal?
    (runc 1 q (not-betweenfd q '((-3 . 10))) (betweenfd q -3 10))
    '())
  (check-equal?
    (runc 1 q (not-betweenfd q '((-4 . 9))) (betweenfd q -3 10))
    '((10)))
  (check-equal?
    (runc 1 q (betweenfd q -3 10) (<=fd q -4))
    '())
  (check-equal?
    (runc 1 q (betweenfd q -3 10) (<=fd q -3))
    '((-3)))
  (check-equal?
    (runc 1 q (betweenfd q -3 10) (<=fd 10 q))
    '((10)))
  (check-equal?
    (runc 1 q (!=fd 10 q) (betweenfd q -3 10) (<=fd 8 q) (!=fd q 9))
    '((8)))
  (check-equal?
    (runc 1 (q r s) (betweenfd q -3 5) (betweenfd r 0 1)
          (+fd q r s) (<=fd 6 s) (!=fd s 7))
    '(((5 1 6))))
  )
