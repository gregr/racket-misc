#lang racket/base
(provide
  ==
  conde
  conj*
  conj-seq*
  disj*
  exist
  ino
  matche
  (struct-out run-config)
  run-config-default
  run/config
  run
  run*
  run-depth
  run*-depth
  run-dls
  )

(require
  "list.rkt"
  "maybe.rkt"
  "microkanren.rkt"
  "monad.rkt"
  "record.rkt"
  "repr.rkt"
  "sugar.rkt"
  racket/function
  racket/list
  (except-in racket/match ==)
  racket/set
  (for-syntax
    racket/base
    racket/list
    ))

(module+ test
  (require
    "list.rkt"
    rackunit
    ))

(define-syntax conj*
  (syntax-rules ()
    ((_) (muk-succeed))
    ((_ g0) g0)
    ((_ g0 gs ...) (conj g0 (conj* gs ...)))))
(define-syntax conj-seq*
  (syntax-rules ()
    ((_) (muk-succeed))
    ((_ g0) g0)
    ((_ g0 gs ...) (conj-seq g0 (conj-seq* gs ...)))))
(define-syntax disj*
  (syntax-rules ()
    ((_) (muk-fail))
    ((_ g0) g0)
    ((_ g0 gs ...) (disj g0 (disj* gs ...)))))
(define-syntax disj+-Zzz
  (syntax-rules ()
    ((_ g0) g0)
    ((_ g0 gs ...) (Zzz (disj* g0 gs ...)))))

(define-syntax conde
  (syntax-rules ()
    ((_ (gs ...) ...) (disj+-Zzz (conj* gs ...) ...))))

(define-syntax exist
  (syntax-rules ()
    ((_ xs gs ...) (let/vars xs (conj* gs ...)))))

(define state-empty (muk-state-empty/constraints (void)))
(record run-config eval reify)
(define run-config-default
  (run-config
    (curry (muk-evaluator muk-unify muk-add-constraint-default
                          muk-constrain-default) state-empty)
    (lambda (vr st)
      (muk-reify-term st vr muk-var->indexed-symbol-trans-default))))

(define-syntax run/config
  (syntax-rules ()
    ((_ cfg n depth (xs ...) gs ...)
     (run/config cfg n depth qvar
                 (exist (xs ...) (== qvar (list xs ...)) gs ...)))
    ((_ cfg n depth qvar gs ...)
     (lets (run-config eval reify) = cfg
           (let/vars (qvar)
             (forl st <- (in-list (muk-take n (eval (conj* gs ...) depth)))
                   (reify qvar st)))))))
(define-syntax run-depth
  (syntax-rules ()
    ((_ n depth body ...) (run/config run-config-default n depth body ...))))
(define-syntax run*-depth
  (syntax-rules () ((_ body ...) (run-depth #f body ...))))
(define-syntax run
  (syntax-rules () ((_ n body ...) (run-depth n 1 body ...))))
(define-syntax run*
  (syntax-rules () ((_ body ...) (run #f body ...))))

(define-syntax run/config-dls
  (syntax-rules ()
    ((_ cfg n (depth) body ...)
     (run/config-dls cfg n (depth add1 #f) body ...))
    ((_ cfg n (depth-min depth-max) body ...)
     (run/config-dls cfg n (depth-min add1 depth-max) body ...))
    ((_ cfg n (depth-min depth-inc depth-max) (xs ...) gs ...)
     (run/config-dls cfg n (depth-min depth-inc depth-max) qvar
                     (exist (xs ...) (== qvar (list xs ...)) gs ...)))
    ((_ cfg n (depth-min depth-inc depth-max) qvar gs ...)
     (lets (run-config eval reify) = cfg
           (let/vars (qvar)
             (forl st <- (in-list (eval (conj* gs ...)
                                        n depth-min depth-inc depth-max))
                   (reify qvar st)))))))
(define run-config-default-dls
  (run-config
    (curry (muk-evaluator-dls muk-unify muk-add-constraint-default
                              muk-constrain-default) state-empty)
    (lambda (vr st)
      (muk-reify-term st vr muk-var->indexed-symbol-trans-default))))
(define-syntax run-dls
  (syntax-rules ()
    ((_ n depth body ...) (run/config-dls run-config-default-dls n depth body ...))))

(define-for-syntax (pattern->identifiers pat)
  (define (unquote-pats stx)
    (syntax-case stx (unquote)
      ((unquote pat) (list #'pat))
      ((head . tail) (append (unquote-pats #'head) (unquote-pats #'tail)))
      (_ '())))
  (if (identifier? pat) (list pat)
    (syntax-case pat (quote quasiquote)
      ((quote _) '())
      ((quasiquote stx)
       (append* (map pattern->identifiers (unquote-pats #'stx))))
      ((_ args ...)
       (append* (map pattern->identifiers (syntax->list #'(args ...)))))
      (_ '()))))
(define-syntax (match1e stx)
  (syntax-case stx ()
    ((_ arg pattern gs ...)
     (let ((vnames (pattern->identifiers #'pattern)))
       #`(exist (#,@vnames) (== pattern arg) gs ...)))))
(define-syntax matche
  (syntax-rules ()
    ((_ arg (pattern gs ...) ...)
     (let ((param arg)) (disj+-Zzz (match1e param pattern gs ...) ...)))))

(define (ino domain . xs)
  (forf goal = (conj*)
        x <- xs
        (conj goal
              (forf goal = (disj*)
                    el <- domain
                    (disj goal (== x el))))))

(define (nat->bits nat)
  (if (zero? nat) '()
    (lets
      (values bit nat) =
      (if (odd? nat) (values 1 (- nat 1)) (values 2 (- nat 2)))
      (list* bit (nat->bits (quotient nat 2))))))

(module+ test
  (check-equal?
    (list (nat->bits 6) (nat->bits 7) (nat->bits 8) (nat->bits 9))
    '((2 2) (1 1 1) (2 1 1) (1 2 1))))

(define (nat-ino nats . lexprs)
  (define (compressed-nats)
    (define (get-lvar) (call/var identity))
    (let loop ((nats nats) (cur-result '()) (results '()))
      (if (null? nats) results
        (lets
          results = (if (member '() nats)
                      (list* (reverse cur-result) results)
                      results)
          nats = (filter-not null? nats)
          (list firsts nats) =
          (zip-default '(() ()) (forl nat <- nats
                                      (list (first nat) (rest nat))))
          bits = (list->set firsts)
          next = (cond ((= 2 (set-count bits)) (get-lvar))
                       ((set-member? bits 1) 1)
                       (else 2))
          cur-result = (list* next cur-result)
          (loop nats cur-result results)))))
  (forf goal = (conj*)
        lexpr <- lexprs
        domain = (compressed-nats)
        (conj goal (ino domain lexpr))))

(module+ test
  (check-true
    (match (run* q (nat-ino (list (nat->bits 6)
                                  (nat->bits 7)
                                  (nat->bits 8)
                                  (nat->bits 9)) q))
      ((list (list v0 v1) (list v2 v3 1)) (and (eq? v0 v2) (eq? v1 v3)))
      (_ #f))))

(define (nat<o a b)
  (conde
    ((== '() a) (exist (b0 bd) (== `(,b0 . ,bd) b)))
    ((exist (a0 ad b0 bd)
      (== `(,a0 . ,ad) a) (== `(,b0 . ,bd) b)
      (conde ((nat<o ad bd))
             ((== ad bd) (== 1 a0) (== 2 b0)))))))
(define (nat<=o a b) (conde ((nat<o a b)) ((== a b))))

(module+ test
  (lets
    (list actual expected) =
    (zip (forl
           (list a b) <- '((0 0) (0 1) (1 0) (1 1) (1 2) (2 1) (2 2)
                           (3 3) (3 4) (4 3) (4 4) (4 5) (5 4) (5 5))
           (list (pair? (run* r (nat<o (nat->bits a) (nat->bits b))))
                 (< a b))))
    (check-equal? actual expected)))

(define (poso n) (exist (a d) (== `(,a . ,d) n)))

(define (full-addero p a b r c)
  (conde
    ((== 0 p) (== 1 a) (== 1 b) (== 2 r) (== 0 c))
    ((== 0 p) (== 1 a) (== 2 b) (== 1 r) (== 1 c))
    ((== 0 p) (== 2 a) (== 1 b) (== 1 r) (== 1 c))
    ((== 0 p) (== 2 a) (== 2 b) (== 2 r) (== 1 c))
    ((== 1 p) (== 1 a) (== 1 b) (== 1 r) (== 1 c))
    ((== 1 p) (== 1 a) (== 2 b) (== 2 r) (== 1 c))
    ((== 1 p) (== 2 a) (== 1 b) (== 2 r) (== 1 c))
    ((== 1 p) (== 2 a) (== 2 b) (== 1 r) (== 2 c))
    ((== 2 p) (== 1 a) (== 1 b) (== 2 r) (== 1 c))
    ((== 2 p) (== 1 a) (== 2 b) (== 1 r) (== 2 c))
    ((== 2 p) (== 2 a) (== 1 b) (== 1 r) (== 2 c))
    ((== 2 p) (== 2 a) (== 2 b) (== 2 r) (== 2 c))))

(define (addero p a b r)
  (conde
    ((== 0 p) (== '() a) (== b r))
    ((== 0 p) (== '() b) (poso a) (== a r))
    ((== 1 p) (== '() a) (addero 0 '(1) b r))
    ((== 1 p) (== '() b) (poso a) (addero 0 a '(1) r))
    ((== 2 p) (== '() a) (addero 0 '(2) b r))
    ((== 2 p) (== '() b) (poso a) (addero 0 a '(2) r))
    ((exist (a0 ad b0 bd r0 rd c)
      (== `(,a0 . ,ad) a) (== `(,b0 . ,bd) b) (== `(,r0 . ,rd) r)
      (full-addero p a0 b0 r0 c)
      (addero c ad bd rd)))))

(define (nat-addo a b r) (addero 0 a b r))
(define (nat-subo a b r) (nat-addo r b a))

(module+ test
  (lets
    (list actual expected) =
    (zip (forl
           (list a b) <- '((0 0) (0 1) (1 0) (1 2) (2 1) (2 2) (3 4) (6 6))
           (list (run*-depth 1000 r (nat-addo (nat->bits a) (nat->bits b) r))
                 `(,(nat->bits (+ a b))))))
    (check-equal? actual expected))
  (lets
    (list actual expected) =
    (zip (forl
           (list a b) <- '((0 0) (1 0) (2 1) (2 2) (3 1) (4 1) (4 2) (4 3)
                           (5 1) (5 2) (6 6) (7 1) (7 2) (7 3) (7 4) (7 5))
           (list (run*-depth 1000 r (nat-subo (nat->bits a) (nat->bits b) r))
                 `(,(nat->bits (- a b))))))
    (check-equal? actual expected))
  )

(define (nat-doubleo n r) (nat-addo n n r))

(define (nat-mulo a b r)
  (conde
    ((== '() a) (== '() r))
    ((poso a) (== '() b) (== '() r))
    ((exist (a0 ad r-later-half r-later r-current)
      (== `(,a0 . ,ad) a) (poso b)
      (nat-mulo ad b r-later-half)
      (nat-doubleo r-later-half r-later)
      (conde
        ((== 1 a0) (== b r-current))
        ((== 2 a0) (nat-doubleo b r-current)))
      (nat-addo r-current r-later r)
      ))))

(define (gt1o n) (conde ((== '(2) n))
                        ((exist (a d) (== `(, a . ,d) n) (poso d)))))

(define (nat-divo a b q r)
  (conde
    ((== '(1) b) (== '() r) (== a q))
    ((exist (mr) (gt1o b)
      (nat-mulo b q mr)
      (nat<o r b)
      (nat-subo a mr r)))))

(module+ test
  (lets
    (list actual expected) =
    (zip (forl
           (list a b) <- '((0 0) (0 1) (1 0) (1 2) (2 1) (2 2) (3 4) (6 6))
           (list (run*-depth 1000 r (nat-mulo (nat->bits a) (nat->bits b) r))
                 `(,(nat->bits (* a b))))))
    (check-equal? actual expected))
  ; slow test
  ;(lets
    ;(list actual expected) =
    ;(zip (forl
           ;(list a b) <- '((0 1) (1 1) (1 2) (2 1) (3 2) (3 4) (4 2))
           ;`(,(run-depth 1 1 (q r) (nat-divo (nat->bits a) (nat->bits b) q r))
              ;(,(nat->bits (quotient a b)) ,(nat->bits (remainder a b))))))
    ;(check-equal? actual expected))
  )

(define (nat-squareo n r) (nat-mulo n n r))

(define (nat-expo b p r)
  (conde
    ((== '() p) (== '(1) r))
    ((exist (p0 pd r-current r-later-sqrt r-later)
      (== `(,p0 . ,pd) p)
      (nat-expo b pd r-later-sqrt)
      (nat-squareo r-later-sqrt r-later)
      (conde
        ((== 1 p0) (== b r-current))
        ((== 2 p0) (nat-squareo b r-current)))
      (nat-mulo r-current r-later r)))))

(module+ test
  (lets
    (list actual expected) =
    (zip (forl
           (list a b) <- '((1 0) (1 1) (1 2) (2 1) (2 2) (2 3) (3 2))
           (list (run*-depth 100 r (nat-expo (nat->bits a) (nat->bits b) r))
                 `(,(nat->bits (expt a b))))))
    (check-equal? actual expected))
  ; slow test
  ;(lets
    ;(list actual expected) =
    ;(zip (forl
           ;(list b a) <- '((0 1) (1 1) ;(1 2) (2 1)
                           ;)
           ;(list p r) <- '((0 0) (0 0) ;(0 1) (0 0)
                           ;)
           ;`(,(run-depth 1 1 (p r) (nat-logo (nat->bits b) (nat->bits a) p r))
              ;(,(nat->bits p) ,(nat->bits r)))))
    ;(check-equal? actual expected))
  )

(module+ test
  (check-equal?
    (run* (x y) (== (cons (list x 3) 5) (cons (list 4 y) 5)))
    '((4 3)))
  (check-equal?
    (run* (x y) (== (cons (list x 3) 5) (list (list 4 y) 5)))
    '())
  (define (appendo ls rs lsrs)
    (matche ls
      ('() (== rs lsrs))
      ((cons l0 ms) (exist (msrs)
                      (appendo ms rs msrs)
                      (== (cons l0 msrs) lsrs)))))
  (check-equal?
    (list->set (run* (x y) (appendo x y (range 1 6))))
    (list->set
      '((() (1 2 3 4 5))
        ((1) (2 3 4 5))
        ((1 2) (3 4 5))
        ((1 2 3) (4 5))
        ((1 2 3 4) (5))
        ((1 2 3 4 5) ()))))

  (define (evalo expr env val)
    (matche `(,expr ,val)
      (`((cons ,e1 ,e2) (,v1 . ,v2))
        (evalo e1 env v1)
        (evalo e2 env v2))
      ; poor man's numbero for the test example
      ('(3 3))
      ('(4 4))))

  (check-true
    (= 1 (length (run 1 (e v) (evalo `(cons 3 ,e) '() `(3 . ,v))))))
  (check-true
    (= 1 (length (run 1 (e v) (evalo `(cons ,e 3) '() `(,v . 3))))))

  (check-equal?
    (run 1 (e v) (evalo `(cons 3 ,e) '() `(4 . ,v)))
    '())
  (check-equal?
    (run 1 (e v) (evalo `(cons ,e 3) '() `(,v . 4)))
    '())

  ; slow test (faster without compression)
  ;(lets
    ;;   S E N D
    ;; + M O R E
    ;; ---------
    ;; M O N E Y
    ;nat-ino = ino  ; toggle state compression
    ;nat-range = (lambda (rmin rmax) (map nat->bits (range rmin rmax)))
    ;add-digitso = (fn (augend addend carry-in carry-out digit)
      ;(exist (partial-sum sum)
        ;(nat-addo augend addend partial-sum)
        ;(nat-addo partial-sum carry-in sum)
        ;(conde
          ;((nat<o (nat->bits 9) sum) (== carry-out (nat->bits 1)) (nat-addo digit (nat->bits 10) sum))
          ;((nat<=o sum (nat->bits 9)) (== carry-out (nat->bits 0)) (== digit sum)))
        ;(nat-ino (nat-range 0 19) partial-sum)
        ;(nat-ino (nat-range 0 20) sum)))
    ;send-more-moneyo = (fn (letters)
      ;(exist (s e n d m o r y carry0 carry1 carry2)
        ;(== letters (list s e n d m o r y))
        ;(all-diffo letters)
        ;(nat-ino (nat-range 0 2) carry0)
        ;(nat-ino (nat-range 0 10) e d y)
        ;(add-digitso d e (nat->bits 0) carry0 y)
        ;(nat-ino (nat-range 0 2) carry1 carry2)
        ;(nat-ino (nat-range 0 10) n o)
        ;(add-digitso e o carry1 carry2 n)
        ;(nat-ino (nat-range 0 10) r)
        ;(add-digitso n r carry0 carry1 e)
        ;(nat-ino (nat-range 1 10) s m)
        ;(add-digitso s m carry2 m o)))
    ;(check-equal?
      ;(run*-depth 1000 q (conj-seq* with-constraints (send-more-moneyo q)))
      ;(list (map nat->bits (list 9 5 6 7 1 0 8 2)))))
  )
