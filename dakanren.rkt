#lang racket/base
(provide
  =/=
  =/=*
  absento
  numbero
  symbolo
  run-da
  run-da-depth
  run*-da
  run*-da-depth
  run-da-dls
  run*-da-dls
  )

(require
  "dict.rkt"
  "maybe.rkt"
  "microkanren.rkt"
  "minikanren.rkt"
  "monad.rkt"
  "record.rkt"
  "set.rkt"
  "sugar.rkt"
  racket/function
  (except-in racket/match ==)
  racket/set
  )

(module+ test
  (require
    rackunit
    ))

(define (cx->vars tm)
  (match tm
    ((? muk-var?) (set tm))
    ((cons h0 t0) (set-union (cx->vars h0) (cx->vars t0)))
    (_ set-empty)))
(record constraints current pending var=>cxs)
(define constraints-empty (constraints set-empty '() (hasheq)))
(def (constraints-current-set (constraints _ p vc) c) (constraints c p vc))
(def (constraints-pending-add (constraints cxs p vc) c)
  (constraints cxs (cons c p) vc))
(def (constraints-pending-clear (constraints cxs _ vc))
  (constraints cxs '() vc))
(def (constraints-var=>cxs-set (constraints c p _) vc) (constraints c p vc))
(def (var=>cxs-add var=>cxs vr cx)
  (hash-set var=>cxs vr (match (hash-get var=>cxs vr)
                          ((nothing) (set cx))
                          ((just cxs) (set-add cxs cx)))))
(def (constraints-new-bindings (constraints current pending var=>cxs) vrs)
  (values current pending var=>cxs) =
  (forf current = current pending = pending var=>cxs = var=>cxs
        vr <- vrs
        (match (hash-get var=>cxs vr)
          ((nothing) (values current pending var=>cxs))
          ((just cxs)
           (forf current = current pending = pending var=>cxs = var=>cxs
                 cx <- cxs
                 (values
                   (set-remove current cx)
                   (cons cx pending)
                   (forf var=>cxs = var=>cxs
                         peer <- (cx->vars cx)
                         (match (hash-get var=>cxs peer)
                           ((nothing) var=>cxs)
                           ((just cxs)
                            (lets
                              cxs = (set-remove cxs cx)
                              (if (set-empty? cxs)
                                (hash-remove var=>cxs peer)
                                (hash-set var=>cxs peer cxs)))))))))))
  (constraints current pending var=>cxs))
(def (constraints-constrain cxs state-constrain simplify vr-new)
  cs = (constraints-new-bindings cxs vr-new)
  new =
  (let loop ((new '()) (pending (constraints-pending cs)))
    (match pending
      ('() new)
      ((cons cx pending)
       (lets cxs = (state-constrain cx)
             (and cxs (loop (append cxs new) pending))))))
  new = (and new (simplify cxs new))
  (and new
       (lets
         cxs =
         (constraints-var=>cxs-set
           cxs
           (forf var=>cxs = (constraints-var=>cxs cxs)
                 cx <- new
                 (forf var=>cxs = var=>cxs
                       vr <- (cx->vars cx)
                       (var=>cxs-add var=>cxs vr cx))))
         cxs = (constraints-pending-clear cxs)
         current = (set-union (constraints-current cxs) (list->set new))
         (constraints-current-set cxs current))))

(record da-constraints diseqs absents types)
(define da-constraints-empty
  (da-constraints constraints-empty constraints-empty constraints-empty))
(def (da-constraints-diseqs-set (da-constraints _ as ts) ds)
  (da-constraints ds as ts))
(def (da-state-constraints-diseqs-pending-add st args)
  cxs = (muk-state-constraints st)
  diseqs = (da-constraints-diseqs cxs)
  (muk-state-constraints-set st
    (da-constraints-diseqs-set
      cxs (constraints-pending-add diseqs args))))
(def (da-constraints-absents-set (da-constraints ds _ ts) as)
  (da-constraints ds as ts))
(def (da-state-constraints-absents-pending-add st args)
  cxs = (muk-state-constraints st)
  absents = (da-constraints-absents cxs)
  (muk-state-constraints-set st
    (da-constraints-absents-set
      cxs (constraints-pending-add absents args))))
(def (da-constraints-types-set (da-constraints ds as _) ts)
  (da-constraints ds as ts))
(def (da-state-constraints-types-pending-add st args)
  cxs = (muk-state-constraints st)
  types = (da-constraints-types cxs)
  (muk-state-constraints-set st
    (da-constraints-types-set
      cxs (constraints-pending-add types args))))
(define da-state-empty (muk-state-empty/constraints da-constraints-empty))
(def (da-add-constraint st name args)
  (match name
    ('=/=* (da-state-constraints-diseqs-pending-add st args))
    ('absento (da-state-constraints-absents-pending-add st args))
    ('type (da-state-constraints-types-pending-add st args))
    (_ (error (format "unsupported constraint: ~a ~a" name args)))))
(def (da-constrain st)
  (values st vr-new) = (muk-sub-new-bindings st)
  st =
  (forf st = st
        (list cxs-get cxs-put cstrain simplify) <-
        (list (list da-state-constraints-diseqs
                    da-state-constraints-diseqs-set
                    da-constrain-diseq
                    da-simplify-diseq)
              (list da-state-constraints-absents
                    da-state-constraints-absents-set
                    da-constrain-absent
                    da-simplify-absent)
              (list da-state-constraints-types
                    da-state-constraints-types-set
                    da-constrain-type
                    da-simplify-type)
              )
        cxs = (and st (constraints-constrain
                        (cxs-get st) (curry cstrain st) simplify vr-new))
        (and cxs (cxs-put st cxs)))
  (if st (list st) '()))

(define (da-state-constraints-diseqs st)
  (da-constraints-diseqs (muk-state-constraints st)))
(def (da-state-constraints-diseqs-set st diseqs)
  (muk-state-constraints-set
    st (da-constraints-diseqs-set (muk-state-constraints st) diseqs)))
(define (da-constrain-diseq st or-diseqs)
  (def (muk-var< (muk-var n0) (muk-var n1)) (symbol<? n0 n1))
  (def (total< e0 e1)
    (or (not (muk-var? e1)) (and (muk-var? e0) (muk-var< e0 e1))))
  (def (cons< (cons k0 v0) (cons k1 v1)) (muk-var< k0 k1))
  (match (monad-foldl maybe-monad
           (fn (st (cons e0 e1)) (muk-unify st e0 e1))
           st or-diseqs)
    ((nothing) '())
    ((just st)
     (lets (values st vr-new) = (muk-sub-new-bindings st)
           or-diseqs = (forl vr <- vr-new
                             (values _ val) = (muk-sub-get st vr)
                             (apply cons (sort (list vr val) total<)))
           or-diseqs = (sort or-diseqs cons<)

           (and (pair? or-diseqs) (list or-diseqs))))))
(define (da-simplify-diseq cxs new) new)
(define (=/=* or-diseqs) (muk-constraint '=/=* or-diseqs))
(define (=/= e0 e1) (=/=* `((,e0 . ,e1))))

(define (da-state-constraints-absents st)
  (da-constraints-absents (muk-state-constraints st)))
(def (da-state-constraints-absents-set st absents)
  (muk-state-constraints-set
    st (da-constraints-absents-set (muk-state-constraints st) absents)))
(def (da-constrain-absent st (list ground tm))
  (values st tm) = (muk-walk st tm)
  (match tm
    ((? muk-var?) (list (list ground tm)))
    ((cons h0 t0)
     (let ((next0 (da-constrain-absent st (list ground h0))))
       (and next0
            (let ((next1 (da-constrain-absent st (list ground t0))))
              (and next1 (append next0 next1))))))
    (_ (if (eqv? ground tm) #f '()))))
(define (da-simplify-absent cxs new) new)
(define (absento ground tm)
  (if (pair? ground)
    (error (format "absento only supports absence of ground terms: ~a ~a"
                   ground tm))
    (muk-constraint 'absento (list ground tm))))

(define (da-state-constraints-types st)
  (da-constraints-types (muk-state-constraints st)))
(def (da-state-constraints-types-set st types)
  (muk-state-constraints-set
    st (da-constraints-types-set (muk-state-constraints st) types)))
(def (da-constrain-type st (list tag tm))
  (values st tm) = (muk-walk st tm)
  (cond
    ((muk-var? tm) (list (list tag tm)))
    ((or (and (symbol? tm) (eq? tag 'sym))
         (and (number? tm) (eq? tag 'num))) '())
    (else #f)))
(define (da-simplify-type cxs new)
  (and (forf vr=>tag = (hasheq)
             (list tag vr) <- new
             #:break (not vr=>tag)
             (match (hash-get vr=>tag vr)
               ((nothing) (hash-set vr=>tag vr tag))
               ((just t0) (and (eq? t0 tag) vr=>tag))))
       new))
(define (typeo tag tm)
  (if (set-member? (set 'num 'sym) tag) (muk-constraint 'type (list tag tm))
    (error (format "invalid type tag: ~a ~a" tag tm))))
(define (symbolo tm) (typeo 'sym tm))
(define (numbero tm) (typeo 'num tm))

(define da-eval (muk-evaluator muk-unify da-add-constraint da-constrain))
(define da-eval-dls (muk-evaluator-dls muk-unify da-add-constraint da-constrain))
; TODO: improve constraint visualization
;(def (da-reify-constraints st)
  ;(constraints var=>desc pending) = (muk-state-constraints st)
  ;(forl (cons mv fdd) <- (hash->list var=>desc)
        ;(cons (muk-var-name mv) fdd)))
;(define (da-reify vr st)
  ;(list* (muk-reify-term st vr muk-var->symbol)
         ;(reify-constraints st)))

(define (da-reify tm st)
  ;(list*
    (muk-reify-term st tm muk-var->indexed-symbol-trans-default)
    ;(reify-constraints st)
    ;)
    )

(define run-config-da (run-config (curry da-eval da-state-empty) da-reify))
(define run-config-da-dls (run-config (curry da-eval-dls da-state-empty) da-reify))

(define-syntax run/config-da
  (syntax-rules ()
    ((_ cfg n depth (xs ...) gs ...)
     (run/config-da cfg n depth qvar
                 (exist (xs ...) (== qvar (list xs ...)) gs ...)))
    ((_ cfg n depth qvar gs ...)
     (lets (run-config eval reify) = cfg
           (let/vars (qvar)
             (forl st <- (in-list (muk-take n (eval (conj* gs ...) depth)))
                   (reify qvar st)))))))
(define-syntax run-da-depth
  (syntax-rules ()
    ((_ n depth body ...) (run/config-da run-config-da n depth body ...))))
(define-syntax run*-da-depth
  (syntax-rules () ((_ body ...) (run-da-depth #f body ...))))
(define-syntax run-da
  (syntax-rules () ((_ n body ...) (run-da-depth n 1 body ...))))
(define-syntax run*-da
  (syntax-rules () ((_ body ...) (run-da #f body ...))))

(define-syntax run/config-da-dls
  (syntax-rules ()
    ((_ cfg n () body ...)
     (run/config-da-dls cfg n (1 add1 #f) body ...))
    ((_ cfg n (depth) body ...)
     (run/config-da-dls cfg n (depth add1 #f) body ...))
    ((_ cfg n (depth-min depth-max) body ...)
     (run/config-da-dls cfg n (depth-min add1 depth-max) body ...))
    ((_ cfg n (depth-min depth-inc depth-max) (xs ...) gs ...)
     (run/config-da-dls cfg n (depth-min depth-inc depth-max) qvar
                     (exist (xs ...) (== qvar (list xs ...)) gs ...)))
    ((_ cfg n (depth-min depth-inc depth-max) qvar gs ...)
     (lets (run-config eval reify) = cfg
           (let/vars (qvar)
             (forl st <- (in-list (eval (conj* gs ...)
                                        n depth-min depth-inc depth-max))
                   (reify qvar st)))))))
(define-syntax run-da-dls
  (syntax-rules ()
    ((_ n body ...) (run/config-da-dls run-config-da-dls n body ...))))
(define-syntax run*-da-dls
  (syntax-rules ()
    ((_ body ...) (run-da-dls #f body ...))))

(module+ test
  (define-syntax mk-test-cont
    (syntax-rules ()
      ((_ test-name exact? query expected)
       (lets
         result-set = (list->set query)
         expected-set = (list->set expected)
         overlap = (set-intersect result-set expected-set)
         (if exact?
           (begin
             (when (not (equal? result-set expected-set))
               (displayln (format "failed test: ~a" test-name)))
             ;(check-equal? (set-subtract expected-set result-set) (set))
             ;(check-equal? (set-subtract result-set expected-set) (set))
             (check-equal? result-set expected-set)
             )
           (check-equal? overlap expected-set))))))
  (define-syntax mk-test
    (syntax-rules ()
      ((_ test-name query expected)
        (mk-test-cont test-name #t query expected))))

  (check-equal?
    (run-da-dls #f () (p r)
      (=/= '(1 2) `(,p ,r))
      (== 2 p))
    `((2 _.0)))
  (check-equal?
    (run-da-dls #f () (p r)
      (=/= '(1 2) `(,p ,r))
      (== 1 p))
    `((1 _.0)))
  (check-equal?
    (run-da-dls #f () (p r)
      (=/= '(1 2) `(,p ,r))
      (== 2 r)
      (== 2 p))
    `((2 2)))
  (check-equal?
    (run-da-dls #f () (p r)
      (=/= '(1 2) `(,p ,r))
      (== 2 r)
      (== 1 p))
    `())

  (define (evalo expr env val)
    (matche `(,expr ,val)
      (`((cons ,e1 ,e2) (,v1 . ,v2))
        (evalo e1 env v1)
        (evalo e2 env v2))
      ; poor man's numbero for the test example
      ('(3 3))
      ('(4 4))))

  (check-true
    (= 1 (length (run-da-dls 1 () (e v) (evalo `(cons 3 ,e) '() `(3 . ,v))))))
  (check-true
    (= 1 (length (run-da-dls 1 () (e v) (evalo `(cons ,e 3) '() `(,v . 3))))))

  (check-equal?
    (run-da-dls 1 () (e v) (evalo `(cons 3 ,e) '() `(4 . ,v)))
    '())
  (check-equal?
    (run-da-dls 1 () (e v) (evalo `(cons ,e 3) '() `(,v . 4)))
    '())

  ; non-dls
  (check-equal?
    (run*-da (p r)
      (=/= '(1 2) `(,p ,r))
      (== 2 p))
    `((2 _.0)))
  (check-equal?
    (run*-da (p r)
      (=/= '(1 2) `(,p ,r))
      (== 1 p))
    `((1 _.0)))
  (check-equal?
    (run*-da (p r)
      (=/= '(1 2) `(,p ,r))
      (== 2 r)
      (== 2 p))
    `((2 2)))
  (check-equal?
    (run*-da (p r)
      (=/= '(1 2) `(,p ,r))
      (== 2 r)
      (== 1 p))
    `())

  (check-true
    (= 1 (length (run-da 1 (e v) (evalo `(cons 3 ,e) '() `(3 . ,v))))))
  (check-true
    (= 1 (length (run-da 1 (e v) (evalo `(cons ,e 3) '() `(,v . 3))))))

  (check-equal?
    (run-da 1 (e v) (evalo `(cons 3 ,e) '() `(4 . ,v)))
    '())
  (check-equal?
    (run-da 1 (e v) (evalo `(cons ,e 3) '() `(,v . 4)))
    '())

  ;(mk-test "=/=-0"
    ;(run*-da q (=/= 5 q))
    ;'((_.0 (=/= ((_.0 5))))))

  (mk-test "=/=-1"
    (run*-da q
      (=/= 3 q)
      (== q 3))
    '())

  (mk-test "=/=-2"
    (run*-da q
      (== q 3)
      (=/= 3 q))
    '())

  (mk-test "=/=-3"
    (run*-da q
      (exist (x y)
        (=/= x y)
        (== x y)))
    '())

  (mk-test "=/=-4"
    (run*-da q
      (exist (x y)
        (== x y)
        (=/= x y)))
    '())

  (mk-test "=/=-5"
    (run*-da q
      (exist (x y)
        (=/= x y)
        (== 3 x)
        (== 3 y)))
    '())

  (mk-test "=/=-6"
    (run*-da q
      (exist (x y)
        (== 3 x)
        (=/= x y)
        (== 3 y)))
    '())

  (mk-test "=/=-7"
    (run*-da q
      (exist (x y)
        (== 3 x)
        (== 3 y)
        (=/= x y)))
    '())

  (mk-test "=/=-8"
    (run*-da q
      (exist (x y)
        (== 3 x)
        (== 3 y)
        (=/= y x)))
    '())

  (mk-test "=/=-9"
    (run*-da q
      (exist (x y z)
        (== x y)
        (== y z)
        (=/= x 4)
        (== z (+ 2 2))))
    '())

  (mk-test "=/=-10"
    (run*-da q
      (exist (x y z)
        (== x y)
        (== y z)
        (== z (+ 2 2))
        (=/= x 4)))
    '())

  (mk-test "=/=-11"
    (run*-da q
      (exist (x y z)
        (=/= x 4)
        (== y z)
        (== x y)
        (== z (+ 2 2))))
    '())

  (mk-test "=/=-12"
    (run*-da q
      (exist (x y z)
        (=/= x y)
        (== x `(0 ,z 1))
        (== y `(0 1 1))))
    '(_.0))

  (mk-test "=/=-13"
    (run*-da q
      (exist (x y z)
        (=/= x y)
        (== x `(0 ,z 1))
        (== y `(0 1 1))
        (== z 1)
        (== `(,x ,y) q)))
    '())

  (mk-test "=/=-14"
    (run*-da q
      (exist (x y z)
        (=/= x y)
        (== x `(0 ,z 1))
        (== y `(0 1 1))
        (== z 0)))
    '(_.0))

  (mk-test "=/=-15"
    (run*-da q
      (exist (x y z)
        (== z 0)
        (=/= x y)
        (== x `(0 ,z 1))
        (== y `(0 1 1))))
    '(_.0))

  (mk-test "=/=-16"
    (run*-da q
      (exist (x y z)
        (== x `(0 ,z 1))
        (== y `(0 1 1))
        (=/= x y)))
    '(_.0))

  (mk-test "=/=-17"
    (run*-da q
      (exist (x y z)
        (== z 1)
        (=/= x y)
        (== x `(0 ,z 1))
        (== y `(0 1 1))))
    '())

  (mk-test "=/=-18"
    (run*-da q
      (exist (x y z)
        (== z 1)
        (== x `(0 ,z 1))
        (== y `(0 1 1))
        (=/= x y)))
    '())

  (mk-test "=/=-19"
    (run*-da q
      (exist (x y)
        (=/= `(,x 1) `(2 ,y))
        (== x 2)))
    '(_.0))

  (mk-test "=/=-20"
    (run*-da q
      (exist (x y)
        (=/= `(,x 1) `(2 ,y))
        (== y 1)))
    '(_.0))

  (mk-test "=/=-21"
    (run*-da q
      (exist (x y)
        (=/= `(,x 1) `(2 ,y))
        (== x 2)
        (== y 1)))
    '())

  ;(mk-test "=/=-22"
    ;(run*-da q
      ;(exist (x y)
        ;(=/= `(,x 1) `(2 ,y))
        ;(== `(,x ,y) q)))
    ;'(((_.0 _.1) (=/= ((_.0 2) (_.1 1))))))

  ;(mk-test "=/=-23"
    ;(run*-da q
      ;(exist (x y)
        ;(=/= `(,x 1) `(2 ,y))
        ;(== x 2)
        ;(== `(,x ,y) q)))
    ;'(((2 _.0) (=/= ((_.0 1))))))

  (mk-test "=/=-24"
    (run*-da q
      (exist (x y)
        (=/= `(,x 1) `(2 ,y))
        (== x 2)
        (== y 9)
        (== `(,x ,y) q)))
    '((2 9)))

  (mk-test "=/=-24b"
    (run*-da q
    (exist (a d)
      (== `(,a . ,d) q)
      (=/= q `(5 . 6))
      (== a 5)
      (== d 6)))
    '())

  (mk-test "=/=-25"
    (run*-da q
      (exist (x y)
        (=/= `(,x 1) `(2 ,y))
        (== x 2)
        (== y 1)
        (== `(,x ,y) q)))
    '())

  (mk-test "=/=-26"
    (run*-da q
      (exist (a x z)
        (=/= a `(,x 1))
        (== a `(,z 1))
        (== x z)))
    '())

  ;(mk-test "=/=-27"
    ;(run*-da q
      ;(exist (a x z)
        ;(=/= a `(,x 1))
        ;(== a `(,z 1))
        ;(== x 5)
        ;(== `(,x ,z) q)))
    ;'(((5 _.0) (=/= ((_.0 5))))))

  (mk-test "=/=-28"
    (run*-da q
      (=/= 3 4))
    '(_.0))

  (mk-test "=/=-29"
    (run*-da q
      (=/= 3 3))
    '())

  (mk-test "=/=-30"
    (run*-da q (=/= 5 q)
        (=/= 6 q)
        (== q 5))
    '())

  ;(mk-test "=/=-31"
    ;(run*-da q
    ;(exist (a d)
      ;(== `(,a . ,d) q)
      ;(=/= q `(5 . 6))
      ;(== a 5)))
    ;'(((5 . _.0) (=/= ((_.0 6))))))

  (mk-test "=/=-32"
    (run*-da q
      (exist (a)
        (== 3 a)
        (=/= a 4)))
    '(_.0))

  ;(mk-test "=/=-33"
    ;(run*-da q
      ;(=/= 4 q)
      ;(=/= 3 q))
    ;'((_.0 (=/= ((_.0 3)) ((_.0 4))))))

  ;(mk-test "=/=-34"
    ;(run*-da q (=/= q 5) (=/= q 5))
    ;'((_.0 (=/= ((_.0 5))))))

  (mk-test "=/=-35"
    (let ((foo (lambda (x)
                (exist (a)
                  (=/= x a)))))
      (run*-da q (exist (a) (foo a))))
    '(_.0))

  (mk-test "=/=-36"
    (let ((foo (lambda (x)
                (exist (a)
                  (=/= x a)))))
      (run*-da q (exist (b) (foo b))))
    '(_.0))

  ;(mk-test "=/=-37"
    ;(run*-da q
      ;(exist (x y)
        ;(== `(,x ,y) q)
        ;(=/= x y)))
    ;'(((_.0 _.1) (=/= ((_.0 _.1))))))

  ;(mk-test "=/=-37b"
    ;(run*-da q
    ;(exist (a d)
      ;(== `(,a . ,d) q)
      ;(=/= q `(5 . 6))))
    ;'(((_.0 . _.1) (=/= ((_.0 5) (_.1 6))))))

  (mk-test "=/=-37c"
    (run*-da q
    (exist (a d)
      (== `(,a . ,d) q)
      (=/= q `(5 . 6))
      (== a 3)))
    '((3 . _.0)))

  ;(mk-test "=/=-38"
    ;(run*-da q
      ;(exist (x y)
        ;(== `(,x ,y) q)
        ;(=/= y x)))
    ;'(((_.0 _.1) (=/= ((_.0 _.1))))))

  ;(mk-test "=/=-39"
    ;(run*-da q
      ;(exist (x y)
        ;(== `(,x ,y) q)
        ;(=/= x y)
        ;(=/= y x)))
    ;'(((_.0 _.1) (=/= ((_.0 _.1))))))

  ;(mk-test "=/=-40"
    ;(run*-da q
      ;(exist (x y)
        ;(== `(,x ,y) q)
        ;(=/= x y)
        ;(=/= x y)))
    ;'(((_.0 _.1) (=/= ((_.0 _.1))))))

  ;(mk-test "=/=-41"
    ;(run*-da q (=/= q 5) (=/= 5 q))
    ;'((_.0 (=/= ((_.0 5))))))

  ;(mk-test "=/=-42"
    ;(run*-da q
      ;(exist (x y)
        ;(== `(,x ,y) q)
        ;(=/= `(,x ,y) `(5 6))
        ;(=/= x 5)))
    ;'(((_.0 _.1) (=/= ((_.0 5))))))

  ;(mk-test "=/=-43"
    ;(run*-da q
      ;(exist (x y)
        ;(== `(,x ,y) q)
        ;(=/= x 5)
        ;(=/= `(,x ,y) `(5 6))))
    ;'(((_.0 _.1) (=/= ((_.0 5))))))

  ;(mk-test "=/=-44"
    ;(run*-da q
      ;(exist (x y)
        ;(=/= x 5)
        ;(=/= `(,x ,y) `(5 6))
        ;(== `(,x ,y) q)))
    ;'(((_.0 _.1) (=/= ((_.0 5))))))

  ;(mk-test "=/=-45"
    ;(run*-da q
      ;(exist (x y)
        ;(=/= 5 x)
        ;(=/= `(,x ,y) `(5 6))
        ;(== `(,x ,y) q)))
    ;'(((_.0 _.1) (=/= ((_.0 5))))))

  ;(mk-test "=/=-46"
    ;(run*-da q
      ;(exist (x y)
        ;(=/= 5 x)
        ;(=/= `( ,y ,x) `(6 5))
        ;(== `(,x ,y) q)))
    ;'(((_.0 _.1) (=/= ((_.0 5))))))

  (mk-test "=/=-47"
    (run*-da x
      (exist (y z)
        (=/= x `(,y 2))
        (== x `(,z 2))))
    '((_.0 2)))

  (mk-test "=/=-48"
    (run*-da x
      (exist (y z)
        (=/= x `(,y 2))
        (== x `((,z) 2))))
    '(((_.0) 2)))

  (mk-test "=/=-49"
    (run*-da x
      (exist (y z)
        (=/= x `((,y) 2))
        (== x `(,z 2))))
    '((_.0 2)))

  (define distincto
    (lambda (l)
      (conde
        ((== l '()))
        ((exist (a) (== l `(,a))))
        ((exist (a ad dd)
          (== l `(,a ,ad . ,dd))
          (=/= a ad)
          (distincto `(,a . ,dd))
          (distincto `(,ad . ,dd)))))))

  ;(mk-test "=/=-50"
    ;(run*-da q
      ;(distincto `(2 3 ,q)))
    ;'((_.0 (=/= ((_.0 2)) ((_.0 3))))))

  (define rembero0
    (lambda (x ls out)
      (conde
        ((== '() ls) (== '() out))
        ((exist (a d res)
          (== `(,a . ,d) ls)
          (rembero0 x d res)
          (conde
            ((== a x) (== out res))
            ((== `(,a . ,res) out))

            ))))))

  (mk-test "=/=-51"
    (run*-da q (rembero0 'a '(a b a c) q))
    '((b c) (b a c) (a b c) (a b a c)))

  (mk-test "=/=-52"
    (run*-da q (rembero0 'a '(a b c) '(a b c)))
    '(_.0))

  (define rembero
    (lambda (x ls out)
      (conde
        ((== '() ls) (== '() out))
        ((exist (a d res)
          (== `(,a . ,d) ls)
          (rembero x d res)
          (conde
            ((== a x) (== out res))
            ((=/= a x) (== `(,a . ,res) out))))))))

  ;(mk-test "=/=-53"
    ;(run*-da q (rembero 'a '(a b a c) q))
    ;'((b c)))

  (mk-test "=/=-54"
    (run*-da q (rembero 'a '(a b c) '(a b c)))
    '())

  ;(mk-test "=/=-55"
    ;(run-da 1 q (=/= q #f))
    ;'((_.0 (=/= ((_.0 #f))))))

  ;(mk-test "numbero-1"
    ;(run*-da q (numbero q))
    ;'((_.0 (num _.0))))

  (mk-test "numbero-2"
    (run*-da q (numbero q) (== 5 q))
    '(5))

  (mk-test "numbero-3"
    (run*-da q (== 5 q) (numbero q))
    '(5))

  (mk-test "numbero-4"
    (run*-da q (== 'x q) (numbero q))
    '())

  (mk-test "numbero-5"
    (run*-da q (numbero q) (== 'x q))
    '())

  (mk-test "numbero-6"
    (run*-da q (numbero q) (== `(1 . 2) q))
    '())

  (mk-test "numbero-7"
    (run*-da q (== `(1 . 2) q) (numbero q))
    '())

  (mk-test "numbero-8"
    (run*-da q (exist (x) (numbero x)))
    '(_.0))

  (mk-test "numbero-9"
    (run*-da q (exist (x) (numbero x)))
    '(_.0))

  ;(mk-test "numbero-10"
    ;(run*-da q (exist (x) (numbero x) (== x q)))
    ;'((_.0 (num _.0))))

  ;(mk-test "numbero-11"
    ;(run*-da q (exist (x) (numbero q) (== x q) (numbero x)))
    ;'((_.0 (num _.0))))

  ;(mk-test "numbero-12"
    ;(run*-da q (exist (x) (numbero q) (numbero x) (== x q)))
    ;'((_.0 (num _.0))))

  ;(mk-test "numbero-13"
    ;(run*-da q (exist (x) (== x q) (numbero q) (numbero x)))
    ;'((_.0 (num _.0))))

  ;(mk-test "numbero-14-a"
    ;(run*-da q (exist (x) (numbero q) (== 5 x)))
    ;'((_.0 (num _.0))))

  (mk-test "numbero-14-b"
    (run*-da q (exist (x) (numbero q) (== 5 x) (== x q)))
    '(5))

  (mk-test "numbero-15"
    (run*-da q (exist (x) (== q x) (numbero q) (== 'y x)))
    '())

  ;(mk-test "numbero-16-a"
    ;(run*-da q (numbero q) (=/= 'y q))
    ;'((_.0 (num _.0))))

  ;(mk-test "numbero-16-b"
    ;(run*-da q (=/= 'y q) (numbero q))
    ;'((_.0 (num _.0))))

  ;(mk-test "numbero-17"
    ;(run*-da q (numbero q) (=/= `(1 . 2) q))
    ;'((_.0 (num _.0))))

  ;(mk-test "numbero-18"
    ;(run*-da q (numbero q) (=/= 5 q))
    ;'((_.0 (=/= ((_.0 5))) (num _.0))))

  ;(mk-test "numbero-19"
    ;(run*-da q
      ;(exist (x y)
        ;(numbero x)
        ;(numbero y)
        ;(== `(,x ,y) q)))
    ;'(((_.0 _.1) (num _.0 _.1))))

  ;(mk-test "numbero-20"
    ;(run*-da q
      ;(exist (x y)
        ;(== `(,x ,y) q)
        ;(numbero x)
        ;(numbero y)))
    ;'(((_.0 _.1) (num _.0 _.1))))

  ;(mk-test "numbero-21"
    ;(run*-da q
      ;(exist (x y)
        ;(== `(,x ,y) q)
        ;(numbero x)
        ;(numbero x)))
    ;'(((_.0 _.1) (num _.0))))

  ;(mk-test "numbero-22"
    ;(run*-da q
      ;(exist (x y)
        ;(numbero x)
        ;(numbero x)
        ;(== `(,x ,y) q)))
    ;'(((_.0 _.1) (num _.0))))

  ;(mk-test "numbero-23"
    ;(run*-da q
      ;(exist (x y)
        ;(numbero x)
        ;(== `(,x ,y) q)
        ;(numbero x)))
    ;'(((_.0 _.1) (num _.0))))

  (mk-test "numbero-24-a"
    (run*-da q
      (exist (w x y z)
        (=/= `(,w . ,x) `(,y . ,z))
        (numbero w)
        (numbero z)))
    '(_.0))

  ;(mk-test "numbero-24-b"
    ;(run*-da q
      ;(exist (w x y z)
        ;(=/= `(,w . ,x) `(,y . ,z))
        ;(numbero w)
        ;(numbero z)
        ;(== `(,w ,x ,y ,z) q)))
    ;'(((_.0 _.1 _.2 _.3)
      ;(=/= ((_.0 _.2) (_.1 _.3)))
      ;(num _.0 _.3))))

  ;(mk-test "numbero-24-c"
    ;(run*-da q
      ;(exist (w x y z)
        ;(=/= `(,w . ,x) `(,y . ,z))
        ;(numbero w)
        ;(numbero y)
        ;(== `(,w ,x ,y ,z) q)))
    ;'(((_.0 _.1 _.2 _.3)
      ;(=/= ((_.0 _.2) (_.1 _.3)))
      ;(num _.0 _.2))))

  ;(mk-test "numbero-24-d"
    ;(run*-da q
      ;(exist (w x y z)
        ;(=/= `(,w . ,x) `(,y . ,z))
        ;(numbero w)
        ;(numbero y)
        ;(== w y)
        ;(== `(,w ,x ,y ,z) q)))
    ;'(((_.0 _.1 _.0 _.2)
      ;(=/= ((_.1 _.2)))
      ;(num _.0))))

  ;(mk-test "numbero-25"
    ;(run*-da q
      ;(exist (w x)
        ;(=/= `(,w . ,x) `(a . b))
        ;(== `(,w ,x) q)))
    ;'(((_.0 _.1) (=/= ((_.0 a) (_.1 b))))))

  ;(mk-test "numbero-26"
    ;(run*-da q
      ;(exist (w x)
        ;(=/= `(,w . ,x) `(a . b))
        ;(numbero w)
        ;(== `(,w ,x) q)))
    ;'(((_.0 _.1) (num _.0))))

  ;(mk-test "numbero-27"
    ;(run*-da q
      ;(exist (w x)
        ;(numbero w)
        ;(=/= `(,w . ,x) `(a . b))
        ;(== `(,w ,x) q)))
    ;'(((_.0 _.1) (num _.0))))

  ;(mk-test "numbero-28"
    ;(run*-da q
      ;(exist (w x)
        ;(numbero w)
        ;(=/= `(a . b) `(,w . ,x))
        ;(== `(,w ,x) q)))
    ;'(((_.0 _.1) (num _.0))))

  ;(mk-test "numbero-29"
    ;(run*-da q
      ;(exist (w x)
        ;(numbero w)
        ;(=/= `(a . ,x) `(,w . b))
        ;(== `(,w ,x) q)))
    ;'(((_.0 _.1) (num _.0))))

  ;(mk-test "numbero-30"
    ;(run*-da q
      ;(exist (w x)
        ;(numbero w)
        ;(=/= `(5 . ,x) `(,w . b))
        ;(== `(,w ,x) q)))
    ;'(((_.0 _.1) (=/= ((_.0 5) (_.1 b))) (num _.0))))

  ;(mk-test "numbero-31"
  ;(run*-da q
    ;(exist (x y z a b)
      ;(numbero x)
      ;(numbero y)
      ;(numbero z)
      ;(numbero a)
      ;(numbero b)
      ;(== `(,y ,z ,x ,b) `(,z ,x ,y ,a))
      ;(== q `(,x ,y ,z ,a ,b))))
  ;'(((_.0 _.0 _.0 _.1 _.1) (num _.0 _.1))))

  ;(mk-test "numbero-32"
  ;(run*-da q
    ;(exist (x y z a b)
      ;(== q `(,x ,y ,z ,a ,b))
      ;(== `(,y ,z ,x ,b) `(,z ,x ,y ,a))
      ;(numbero x)
      ;(numbero a)))
  ;'(((_.0 _.0 _.0 _.1 _.1) (num _.0 _.1))))

  ;(mk-test "symbolo-1"
    ;(run*-da q (symbolo q))
    ;'((_.0 (sym _.0))))

  (mk-test "symbolo-2"
    (run*-da q (symbolo q) (== 'x q))
    '(x))

  (mk-test "symbolo-3"
    (run*-da q (== 'x q) (symbolo q))
    '(x))

  (mk-test "symbolo-4"
    (run*-da q (== 5 q) (symbolo q))
    '())

  (mk-test "symbolo-5"
    (run*-da q (symbolo q) (== 5 q))
    '())

  (mk-test "symbolo-6"
    (run*-da q (symbolo q) (== `(1 . 2) q))
    '())

  (mk-test "symbolo-7"
    (run*-da q (== `(1 . 2) q) (symbolo q))
    '())

  (mk-test "symbolo-8"
    (run*-da q (exist (x) (symbolo x)))
    '(_.0))

  (mk-test "symbolo-9"
    (run*-da q (exist (x) (symbolo x)))
    '(_.0))

  ;(mk-test "symbolo-10"
    ;(run*-da q (exist (x) (symbolo x) (== x q)))
    ;'((_.0 (sym _.0))))

  ;(mk-test "symbolo-11"
    ;(run*-da q (exist (x) (symbolo q) (== x q) (symbolo x)))
    ;'((_.0 (sym _.0))))

  ;(mk-test "symbolo-12"
    ;(run*-da q (exist (x) (symbolo q) (symbolo x) (== x q)))
    ;'((_.0 (sym _.0))))

  ;(mk-test "symbolo-13"
    ;(run*-da q (exist (x) (== x q) (symbolo q) (symbolo x)))
    ;'((_.0 (sym _.0))))

  ;(mk-test "symbolo-14-a"
    ;(run*-da q (exist (x) (symbolo q) (== 'y x)))
    ;'((_.0 (sym _.0))))

  (mk-test "symbolo-14-b"
    (run*-da q (exist (x) (symbolo q) (== 'y x) (== x q)))
    '(y))

  (mk-test "symbolo-15"
    (run*-da q (exist (x) (== q x) (symbolo q) (== 5 x)))
    '())

  ;(mk-test "symbolo-16-a"
    ;(run*-da q (symbolo q) (=/= 5 q))
    ;'((_.0 (sym _.0))))

  ;(mk-test "symbolo-16-b"
    ;(run*-da q (=/= 5 q) (symbolo q))
    ;'((_.0 (sym _.0))))

  ;(mk-test "symbolo-17"
    ;(run*-da q (symbolo q) (=/= `(1 . 2) q))
    ;'((_.0 (sym _.0))))

  ;(mk-test "symbolo-18"
    ;(run*-da q (symbolo q) (=/= 'y q))
    ;'((_.0 (=/= ((_.0 y))) (sym _.0))))

  ;(mk-test "symbolo-19"
    ;(run*-da q
      ;(exist (x y)
        ;(symbolo x)
        ;(symbolo y)
        ;(== `(,x ,y) q)))
    ;'(((_.0 _.1) (sym _.0 _.1))))

  ;(mk-test "symbolo-20"
    ;(run*-da q
      ;(exist (x y)
        ;(== `(,x ,y) q)
        ;(symbolo x)
        ;(symbolo y)))
    ;'(((_.0 _.1) (sym _.0 _.1))))

  ;(mk-test "symbolo-21"
    ;(run*-da q
      ;(exist (x y)
        ;(== `(,x ,y) q)
        ;(symbolo x)
        ;(symbolo x)))
    ;'(((_.0 _.1) (sym _.0))))

  ;(mk-test "symbolo-22"
    ;(run*-da q
      ;(exist (x y)
        ;(symbolo x)
        ;(symbolo x)
        ;(== `(,x ,y) q)))
    ;'(((_.0 _.1) (sym _.0))))

  ;(mk-test "symbolo-23"
    ;(run*-da q
      ;(exist (x y)
        ;(symbolo x)
        ;(== `(,x ,y) q)
        ;(symbolo x)))
    ;'(((_.0 _.1) (sym _.0))))

  (mk-test "symbolo-24-a"
    (run*-da q
      (exist (w x y z)
        (=/= `(,w . ,x) `(,y . ,z))
        (symbolo w)
        (symbolo z)))
    '(_.0))

  ;(mk-test "symbolo-24-b"
    ;(run*-da q
      ;(exist (w x y z)
        ;(=/= `(,w . ,x) `(,y . ,z))
        ;(symbolo w)
        ;(symbolo z)
        ;(== `(,w ,x ,y ,z) q)))
    ;'(((_.0 _.1 _.2 _.3)
      ;(=/= ((_.0 _.2) (_.1 _.3)))
      ;(sym _.0 _.3))))

  ;(mk-test "symbolo-24-c"
    ;(run*-da q
      ;(exist (w x y z)
        ;(=/= `(,w . ,x) `(,y . ,z))
        ;(symbolo w)
        ;(symbolo y)
        ;(== `(,w ,x ,y ,z) q)))
    ;'(((_.0 _.1 _.2 _.3)
      ;(=/= ((_.0 _.2) (_.1 _.3)))
      ;(sym _.0 _.2))))

  ;(mk-test "symbolo-24-d"
    ;(run*-da q
      ;(exist (w x y z)
        ;(=/= `(,w . ,x) `(,y . ,z))
        ;(symbolo w)
        ;(symbolo y)
        ;(== w y)
        ;(== `(,w ,x ,y ,z) q)))
    ;'(((_.0 _.1 _.0 _.2)
      ;(=/= ((_.1 _.2)))
      ;(sym _.0))))

  ;(mk-test "symbolo-25"
    ;(run*-da q
      ;(exist (w x)
        ;(=/= `(,w . ,x) `(5 . 6))
        ;(== `(,w ,x) q)))
    ;'(((_.0 _.1) (=/= ((_.0 5) (_.1 6))))))

  ;(mk-test "symbolo-26"
    ;(run*-da q
      ;(exist (w x)
        ;(=/= `(,w . ,x) `(5 . 6))
        ;(symbolo w)
        ;(== `(,w ,x) q)))
    ;'(((_.0 _.1) (sym _.0))))

  ;(mk-test "symbolo-27"
    ;(run*-da q
      ;(exist (w x)
        ;(symbolo w)
        ;(=/= `(,w . ,x) `(5 . 6))
        ;(== `(,w ,x) q)))
    ;'(((_.0 _.1) (sym _.0))))

  ;(mk-test "symbolo-28"
    ;(run*-da q
      ;(exist (w x)
        ;(symbolo w)
        ;(=/= `(5 . 6) `(,w . ,x))
        ;(== `(,w ,x) q)))
    ;'(((_.0 _.1) (sym _.0))))

  ;(mk-test "symbolo-29"
    ;(run*-da q
      ;(exist (w x)
        ;(symbolo w)
        ;(=/= `(5 . ,x) `(,w . 6))
        ;(== `(,w ,x) q)))
    ;'(((_.0 _.1) (sym _.0))))

  ;(mk-test "symbolo-30"
    ;(run*-da q
      ;(exist (w x)
        ;(symbolo w)
        ;(=/= `(z . ,x) `(,w . 6))
        ;(== `(,w ,x) q)))
    ;'(((_.0 _.1) (=/= ((_.0 z) (_.1 6))) (sym _.0))))

  ;(mk-test "symbolo-31-a"
    ;(run*-da q
      ;(exist (w x y z)
        ;(== x 5)
        ;(=/= `(,w ,y) `(,x ,z))
        ;(== w 5)
        ;(== `(,w ,x ,y ,z) q)))
    ;'(((5 5 _.0 _.1) (=/= ((_.0 _.1))))))

  ;(mk-test "symbolo-31-b"
    ;(run*-da q
      ;(exist (w x y z)
        ;(=/= `(,w ,y) `(,x ,z))
        ;(== w 5)
        ;(== x 5)
        ;(== `(,w ,x ,y ,z) q)))
    ;'(((5 5 _.0 _.1) (=/= ((_.0 _.1))))))

  ;(mk-test "symbolo-31-c"
    ;(run*-da q
      ;(exist (w x y z)
        ;(== w 5)
        ;(=/= `(,w ,y) `(,x ,z))
        ;(== `(,w ,x ,y ,z) q)
        ;(== x 5)))
    ;'(((5 5 _.0 _.1) (=/= ((_.0 _.1))))))

  ;(mk-test "symbolo-31-d"
    ;(run*-da q
      ;(exist (w x y z)
        ;(== w 5)
        ;(== x 5)
        ;(=/= `(,w ,y) `(,x ,z))
        ;(== `(,w ,x ,y ,z) q)))
    ;'(((5 5 _.0 _.1) (=/= ((_.0 _.1))))))


  ;(mk-test "symbolo-32-a"
    ;(run*-da q
      ;(exist (w x y z)
        ;(== x 'a)
        ;(=/= `(,w ,y) `(,x ,z))
        ;(== w 'a)
        ;(== `(,w ,x ,y ,z) q)))
    ;'(((a a _.0 _.1) (=/= ((_.0 _.1))))))

  ;(mk-test "symbolo-32-b"
    ;(run*-da q
      ;(exist (w x y z)
        ;(=/= `(,w ,y) `(,x ,z))
        ;(== w 'a)
        ;(== x 'a)
        ;(== `(,w ,x ,y ,z) q)))
    ;'(((a a _.0 _.1) (=/= ((_.0 _.1))))))

  ;(mk-test "symbolo-32-c"
    ;(run*-da q
      ;(exist (w x y z)
        ;(== w 'a)
        ;(=/= `(,w ,y) `(,x ,z))
        ;(== `(,w ,x ,y ,z) q)
        ;(== x 'a)))
    ;'(((a a _.0 _.1) (=/= ((_.0 _.1))))))

  ;(mk-test "symbolo-32-d"
    ;(run*-da q
      ;(exist (w x y z)
        ;(== w 'a)
        ;(== x 'a)
        ;(=/= `(,w ,y) `(,x ,z))
        ;(== `(,w ,x ,y ,z) q)))
    ;'(((a a _.0 _.1) (=/= ((_.0 _.1))))))

  (mk-test "symbolo-numbero-1"
    (run*-da q (symbolo q) (numbero q))
    '())

  (mk-test "symbolo-numbero-2"
    (run*-da q (numbero q) (symbolo q))
    '())

  (mk-test "symbolo-numbero-3"
    (run*-da q
      (exist (x)
        (numbero x)
        (symbolo x)))
    '())

  (mk-test "symbolo-numbero-4"
    (run*-da q
      (exist (x)
        (symbolo x)
        (numbero x)))
    '())

  (mk-test "symbolo-numbero-5"
    (run*-da q
      (numbero q)
      (exist (x)
        (symbolo x)
        (== x q)))
    '())

  (mk-test "symbolo-numbero-6"
    (run*-da q
      (symbolo q)
      (exist (x)
        (numbero x)
        (== x q)))
    '())

  (mk-test "symbolo-numbero-7"
    (run*-da q
      (exist (x)
        (numbero x)
        (== x q))
      (symbolo q))
    '())

  (mk-test "symbolo-numbero-7"
    (run*-da q
      (exist (x)
        (symbolo x)
        (== x q))
      (numbero q))
    '())

  (mk-test "symbolo-numbero-8"
    (run*-da q
      (exist (x)
        (== x q)
        (symbolo x))
      (numbero q))
    '())

  (mk-test "symbolo-numbero-9"
    (run*-da q
      (exist (x)
        (== x q)
        (numbero x))
      (symbolo q))
    '())

  ;(mk-test "symbolo-numbero-10"
    ;(run*-da q
      ;(symbolo q)
      ;(exist (x)
        ;(numbero x)))
    ;'((_.0 (sym _.0))))

  ;(mk-test "symbolo-numbero-11"
    ;(run*-da q
      ;(numbero q)
      ;(exist (x)
        ;(symbolo x)))
    ;'((_.0 (num _.0))))

  ;(mk-test "symbolo-numbero-12"
    ;(run*-da q
      ;(exist (x y)
        ;(symbolo x)
        ;(== `(,x ,y) q)))
    ;'(((_.0 _.1) (sym _.0))))

  ;(mk-test "symbolo-numbero-13"
    ;(run*-da q
      ;(exist (x y)
        ;(numbero x)
        ;(== `(,x ,y) q)))
    ;'(((_.0 _.1) (num _.0))))

  ;(mk-test "symbolo-numbero-14"
    ;(run*-da q
      ;(exist (x y)
        ;(numbero x)
        ;(symbolo y)
        ;(== `(,x ,y) q)))
    ;'(((_.0 _.1) (num _.0) (sym _.1))))

  ;(mk-test "symbolo-numbero-15"
    ;(run*-da q
      ;(exist (x y)
        ;(numbero x)
        ;(== `(,x ,y) q)
        ;(symbolo y)))
    ;'(((_.0 _.1) (num _.0) (sym _.1))))

  ;(mk-test "symbolo-numbero-16"
    ;(run*-da q
      ;(exist (x y)
        ;(== `(,x ,y) q)
        ;(numbero x)
        ;(symbolo y)))
    ;'(((_.0 _.1) (num _.0) (sym _.1))))

  ;(mk-test "symbolo-numbero-17"
    ;(run*-da q
      ;(exist (x y)
        ;(== `(,x ,y) q)
        ;(numbero x)
        ;(symbolo y))
      ;(exist (w z)
        ;(== `(,w ,z) q)))
    ;'(((_.0 _.1) (num _.0) (sym _.1))))

  ;(mk-test "symbolo-numbero-18"
    ;(run*-da q
      ;(exist (x y)
        ;(== `(,x ,y) q)
        ;(numbero x)
        ;(symbolo y))
      ;(exist (w z)
        ;(== `(,w ,z) q)
        ;(== w 5)))
    ;'(((5 _.0) (sym _.0))))

  ;(mk-test "symbolo-numbero-19"
    ;(run*-da q
      ;(exist (x y)
        ;(== `(,x ,y) q)
        ;(numbero x)
        ;(symbolo y))
      ;(exist (w z)
        ;(== 'a z)
        ;(== `(,w ,z) q)))
    ;'(((_.0 a) (num _.0))))

  ;(mk-test "symbolo-numbero-20"
    ;(run*-da q
      ;(exist (x y)
        ;(== `(,x ,y) q)
        ;(numbero x)
        ;(symbolo y))
      ;(exist (w z)
        ;(== `(,w ,z) q)
        ;(== 'a z)))
    ;'(((_.0 a) (num _.0))))

  ;(mk-test "symbolo-numbero-21"
    ;(run*-da q
      ;(exist (x y)
        ;(== `(,x ,y) q)
        ;(=/= `(5 a) q)))
    ;'(((_.0 _.1) (=/= ((_.0 5) (_.1 a))))))

  ;(mk-test "symbolo-numbero-22"
    ;(run*-da q
      ;(exist (x y)
        ;(== `(,x ,y) q)
        ;(=/= `(5 a) q)
        ;(symbolo x)))
    ;'(((_.0 _.1) (sym _.0))))

  ;(mk-test "symbolo-numbero-23"
    ;(run*-da q
      ;(exist (x y)
        ;(== `(,x ,y) q)
        ;(symbolo x)
        ;(=/= `(5 a) q)))
    ;'(((_.0 _.1) (sym _.0))))

  ;(mk-test "symbolo-numbero-24"
    ;(run*-da q
      ;(exist (x y)
        ;(symbolo x)
        ;(== `(,x ,y) q)
        ;(=/= `(5 a) q)))
    ;'(((_.0 _.1) (sym _.0))))

  ;(mk-test "symbolo-numbero-25"
    ;(run*-da q
      ;(exist (x y)
        ;(=/= `(5 a) q)
        ;(symbolo x)
        ;(== `(,x ,y) q)))
    ;'(((_.0 _.1) (sym _.0))))

  ;(mk-test "symbolo-numbero-26"
    ;(run*-da q
      ;(exist (x y)
        ;(=/= `(5 a) q)
        ;(== `(,x ,y) q)
        ;(symbolo x)))
    ;'(((_.0 _.1) (sym _.0))))

  ;(mk-test "symbolo-numbero-27"
    ;(run*-da q
      ;(exist (x y)
        ;(== `(,x ,y) q)
        ;(=/= `(5 a) q)
        ;(numbero y)))
    ;'(((_.0 _.1) (num _.1))))

  ;(mk-test "symbolo-numbero-28"
    ;(run*-da q
      ;(exist (x y)
        ;(== `(,x ,y) q)
        ;(numbero y)
        ;(=/= `(5 a) q)))
    ;'(((_.0 _.1) (num _.1))))

  ;(mk-test "symbolo-numbero-29"
    ;(run*-da q
      ;(exist (x y)
        ;(numbero y)
        ;(== `(,x ,y) q)
        ;(=/= `(5 a) q)))
    ;'(((_.0 _.1) (num _.1))))

  ;(mk-test "symbolo-numbero-30"
    ;(run*-da q
      ;(exist (x y)
        ;(=/= `(5 a) q)
        ;(numbero y)
        ;(== `(,x ,y) q)))
    ;'(((_.0 _.1) (num _.1))))

  ;(mk-test "symbolo-numbero-31"
    ;(run*-da q
      ;(exist (x y)
        ;(=/= `(5 a) q)
        ;(== `(,x ,y) q)
        ;(numbero y)))
    ;'(((_.0 _.1) (num _.1))))

  (mk-test "symbolo-numbero-32"
    (run*-da q
      (exist (x y)
        (=/= `(,x ,y) q)
        (numbero x)
        (symbolo y)))
    '(_.0))

  (mk-test "symbolo-numbero-33"
    (run*-da q
      (exist (x y)
        (numbero x)
        (=/= `(,x ,y) q)
        (symbolo y)))
    '(_.0))

  (mk-test "symbolo-numbero-34"
    (run*-da q
      (exist (x y)
        (numbero x)
        (symbolo y)
        (=/= `(,x ,y) q)))
    '(_.0))

  ;(mk-test "test 8"
    ;(run*-da q
      ;(exist (a b)
        ;(absento 5 a)
        ;(symbolo b)
        ;(== `(,q ,b) a)))
    ;'((_.0 (absento (5 _.0)))))

  ;(mk-test "test 9"
    ;(run*-da q
      ;(exist (a b)
        ;(absento 5 a)
        ;(== `(,q ,b) a)))
    ;'((_.0 (absento (5 _.0)))))

  ;(mk-test "test 19"
    ;(run*-da q (absento 5 q) (absento 5 q))
    ;'((_.0 (absento (5 _.0)))))

  ;(mk-test "test 20"
    ;(run*-da q (absento 5 q) (absento 6 q))
    ;'((_.0 (absento (5 _.0) (6 _.0)))))

  ;(mk-test "test 21"
    ;(run*-da q (absento 5 q) (symbolo q))
    ;'((_.0 (sym _.0))))

  ;(mk-test "test 22"
    ;(run*-da q (numbero q) (absento 'tag q))
    ;'((_.0 (num _.0))))

  ;(mk-test "test 23"
    ;(run*-da q (absento 'tag q) (numbero q))
    ;'((_.0 (num _.0))))

  (mk-test "test 24"
    (run*-da q (== 5 q) (absento 5 q))
    '())

  (mk-test "test 25"
    (run*-da q (== q `(5 6)) (absento 5 q))
    '())

  (mk-test "test 25b"
    (run*-da q (absento 5 q) (== q `(5 6)))
    '())

  (mk-test "test 26"
    (run*-da q (absento 5 q) (== 5 q))
    '())

  ;(mk-test "test 27"
    ;(run*-da q (absento 'tag1 q) (absento 'tag2 q))
    ;'((_.0 (absento (tag1 _.0) (tag2 _.0)))))

  ;(mk-test "test 28"
    ;(run*-da q (absento 'tag q) (numbero q))
    ;'((_.0 (num _.0))))

  ;(mk-test "test 32"
    ;(run*-da q
      ;(exist (a b)
        ;(absento 5 a)
        ;(absento 5 b)
        ;(== `(,a . ,b) q)))
    ;'(((_.0 . _.1) (absento (5 _.0) (5 _.1)))))

  (mk-test "test 33"
    (run*-da q
      (exist (a b c)
        (== `(,a ,b) c)
        (== `(,c ,c) q)
        (symbolo b)
        (numbero c)))
    '())

  ;(mk-test "test 34"
    ;(run*-da q (absento 'tag q) (symbolo q))
    ;'((_.0 (=/= ((_.0 tag))) (sym _.0))))

  ;(mk-test "test 35"
    ;(run*-da q (absento 5 q) (numbero q))
    ;'((_.0 (=/= ((_.0 5))) (num _.0))))

  ;(mk-test "test 38"
    ;(run*-da q (absento '() q))
    ;'((_.0 (absento (() _.0)))))

  (mk-test "test 40"
    (run*-da q
      (exist (d a c)
        (== `(3 . ,d) q)
        (=/= `(,c . ,a) q)
        (== '(3 . 4) d)))
    '((3 3 . 4)))

  (mk-test "test 41"
    (run*-da q
      (exist (a)
        (== `(,a . ,a) q)))
    '((_.0 . _.0)))

  (mk-test "test 63"
    (run*-da q (exist (a b c) (=/= a b) (=/= b c) (=/= c q) (symbolo a)))
    '(_.0))

  (mk-test "test 64"
    (run*-da q (symbolo q) (== 'tag q))
    '(tag))

  (mk-test "test 66"
    (run*-da q (absento 6 5))
    '(_.0))

  ;(mk-test "test 67"
    ;(run*-da q
      ;(exist (a b)
        ;(=/= a b)
        ;(symbolo a)
        ;(numbero b)
        ;(== `(,a ,b) q)))
    ;'(((_.0 _.1) (num _.1) (sym _.0))))

  ;(mk-test "test 68"
    ;(run*-da q
      ;(exist (a b c d)
        ;(=/= `(,a ,b) `(,c ,d))
        ;(symbolo a)
        ;(numbero c)
        ;(symbolo b)
        ;(numbero c)
        ;(== `(,a ,b ,c ,d) q)))
    ;'(((_.0 _.1 _.2 _.3) (num _.2) (sym _.0 _.1))))

  ;(mk-test "test 69"
    ;(run*-da q
      ;(exist (a b)
        ;(=/= `(,a . 3) `(,b . 3))
        ;(symbolo a)
        ;(numbero b)
        ;(== `(,a ,b) q)))
    ;'(((_.0 _.1) (num _.1) (sym _.0))))

  (mk-test "absento 'closure-1a"
    (run*-da q (absento 'closure q) (== q 'closure))
    '())

  (mk-test "absento 'closure-1b"
    (run*-da q (== q 'closure) (absento 'closure q))
    '())

  (mk-test "absento 'closure-2a"
    (run*-da q (exist (a d) (== q 'closure) (absento 'closure q)))
    '())

  (mk-test "absento 'closure-2b"
    (run*-da q (exist (a d) (absento 'closure q) (== q 'closure)))
    '())

  ;(mk-test "absento 'closure-3a"
    ;(run*-da q (exist (a d) (absento 'closure q) (== `(,a . ,d) q)))
    ;'(((_.0 . _.1) (absento (closure _.0) (closure _.1)))))

  ;(mk-test "absento 'closure-3b"
    ;(run*-da q (exist (a d) (== `(,a . ,d) q) (absento 'closure q)))
    ;'(((_.0 . _.1) (absento (closure _.0) (closure _.1)))))

  (mk-test "absento 'closure-4a"
    (run*-da q (exist (a d) (absento 'closure q) (== `(,a . ,d) q) (== 'closure a)))
    '())

  (mk-test "absento 'closure-4b"
    (run*-da q (exist (a d) (absento 'closure q) (== 'closure a) (== `(,a . ,d) q)))
    '())

  (mk-test "absento 'closure-4c"
    (run*-da q (exist (a d) (== 'closure a) (absento 'closure q) (== `(,a . ,d) q)))
    '())

  (mk-test "absento 'closure-4d"
    (run*-da q (exist (a d) (== 'closure a) (== `(,a . ,d) q) (absento 'closure q)))
    '())

  (mk-test "absento 'closure-5a"
    (run*-da q (exist (a d) (absento 'closure q) (== `(,a . ,d) q) (== 'closure d)))
    '())

  (mk-test "absento 'closure-5b"
    (run*-da q (exist (a d) (absento 'closure q) (== 'closure d) (== `(,a . ,d) q)))
    '())

  (mk-test "absento 'closure-5c"
    (run*-da q (exist (a d) (== 'closure d) (absento 'closure q) (== `(,a . ,d) q)))
    '())

  (mk-test "absento 'closure-5d"
    (run*-da q (exist (a d) (== 'closure d) (== `(,a . ,d) q) (absento 'closure q)))
    '())

  (mk-test "absento 'closure-6"
    (run*-da q
      (== `(3 (closure x (x x) ((y . 7))) #t) q)
      (absento 'closure q))
    '())
  )
