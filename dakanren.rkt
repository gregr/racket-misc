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
      ((cons t0 t1) (set-union (tm->vars t0) (tm->vars t1)))
      (_ set-empty))))
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
  (if (null? vr-new) st
    (forf st = st
          (list cxs-get cxs-put cstrain) <-
          (list (list da-state-constraints-diseqs
                      da-state-constraints-diseqs-set
                      da-constrain-diseq))
          cxs = (and st (constraints-constrain
                          (cxs-get st) (curry cstrain st) vr-new))
          (and cxs (cxs-put st cxs))))
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
  )
