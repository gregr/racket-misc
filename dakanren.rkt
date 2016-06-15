#lang racket/base
(provide
  =/=
  =/=*
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
  "repr.rkt"
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

(define (cx->vars args)
  (let tm->vars ((tm args))
    (match tm
      ((? muk-var?) (set tm))
      (_ (match (muk-split (list tm))
           ((nothing) set-empty)
           ((just (list (repr _ components)))
            (foldl set-union set-empty (map tm->vars components))
            ))))))
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
(def (constraints-constrain cxs state-constrain vr-new)
  cs = (constraints-new-bindings cxs vr-new)
  new =
  (let loop ((new '()) (pending (constraints-pending cs)))
    (match pending
      ('() new)
      ((cons cx pending)
       (lets cxs = (state-constrain cx)
             (and cxs (loop (append cxs new) pending))))))
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

(record da-constraints diseqs absents)
(define da-constraints-empty
  (da-constraints constraints-empty constraints-empty))
(def (da-constraints-diseqs-set (da-constraints _ as) ds)
  (da-constraints ds as))
(def (da-state-constraints-diseqs-pending-add st args)
  cxs = (muk-state-constraints st)
  diseqs = (da-constraints-diseqs cxs)
  (muk-state-constraints-set st
    (da-constraints-diseqs-set
      cxs (constraints-pending-add diseqs args))))
(define da-state-empty (muk-state-empty/constraints da-constraints-empty))
(def (da-add-constraint st name args)
  (match name
    ('=/=* (da-state-constraints-diseqs-pending-add st args))
    ;('absent )
    (_ (error (format "unsupported constraint: ~a ~a" name args)))))
(def (da-constrain st)
  (values st vr-new) = (muk-sub-new-bindings st)
  st =
  (forf st = st
        (list cxs-get cxs-put cstrain) <-
        (list (list da-state-constraints-diseqs
                    da-state-constraints-diseqs-set
                    da-constrain-diseq))
        cxs = (and st (constraints-constrain
                        (cxs-get st) (curry cstrain st) vr-new))
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
(define (=/=* or-diseqs) (muk-constraint '=/=* or-diseqs))
(define (=/= e0 e1) (=/=* `((,e0 . ,e1))))

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
  )
