#lang racket/base
(provide
  ==
  conde
  exist
  matche
  run
  run*
  )

(require
  "maybe.rkt"
  "microkanren.rkt"
  "monad.rkt"
  "repr.rkt"
  "sugar.rkt"
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

(define-syntax conde
  (syntax-rules ()
    ((_ (gs ...) ...) (disj* (conj* gs ...) ...))))

(define-syntax exist
  (syntax-rules ()
    ((_ () gs ...) (conj* gs ...))
    ((_ (x0 xs ...) gs ...)
     (call/var (lambda (x0) (exist (xs ...) gs ...))))))

(define-syntax run-depth
  (syntax-rules ()
    ((_ n depth (xs ...) gs ...)
     (muk-reify muk-var->symbol (map muk-var (range (length '(xs ...))))
       (muk-take n (muk-eval muk-state-empty (exist (xs ...) gs ...) depth))))))
(define-syntax run*-depth
  (syntax-rules () ((_ body ...) (run-depth -1 body ...))))
(define-syntax run
  (syntax-rules ()
    ((_ n body ...)
     (run-depth n 1 body ...))))
(define-syntax run*
  (syntax-rules () ((_ body ...) (run -1 body ...))))

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
     (let ((param arg)) (disj* (match1e param pattern gs ...) ...)))))

(define (interp-type val)
  (if (muk-term? val) (muk-func-app 'type (list val))
    (lets (repr type components) = (value->repr val)
          components = (if (list? components) (map interp-type components) '())
          (list type components))))

(define (interp-=/= . or-diseqs)
  (def (muk-var< (muk-var n0) (muk-var n1)) (< n0 n1))
  (def (total< e0 e1)
    (or (not (muk-var? e1)) (and (muk-var? e0) (muk-var< e0 e1))))
  (def (list< (list k0 v0) (list k1 v1)) (muk-var< k0 k1))
  (match (monad-foldl maybe-monad
          (fn (st (list e0 e1)) (muk-unify-and-update st e0 e1))
          muk-state-empty or-diseqs)
    ((nothing) #t)
    ((just st-new)
     (lets
       or-diseqs = (forl
                     vr <- (muk-sub-prefix muk-state-empty st-new)
                     val = (muk-sub-get-var st-new vr)
                     (sort (list vr val) total<))
       or-diseqs = (sort or-diseqs list<)
       (if (null? or-diseqs) #f (muk-func-app '=/= or-diseqs))))))

(define ((interp-numeric-op name op) a b)
  (if (or (muk-term? a) (muk-term? b)) (muk-func-app name (list a b))
    (if (and (number? a) (number? b)) (op a b) (void))))
(define interp-+ (interp-numeric-op '+ +))
(define interp-< (interp-numeric-op '< <))

(define interpretations
  (hash
    'type interp-type
    '=/= interp-=/=
    '+ interp-+
    '< interp-<
    ))

(define with-constraints (interpret interpretations))

(define (type val) (muk-func-app 'type (list val)))
(define (typeo val ty) (== ty (type val)))
(define (symbolo val) (typeo val '(symbol ())))
(define (numbero val)
  (exist (sub-type) (typeo val `((number . ,sub-type) ()))))
(define (full-repr val) (list (type val) val))
(define (ino domain . xs)
  (forf goal = (conj*)
        x <- xs
        (conj goal
              (forf goal = (disj*)
                    el <- domain
                    (disj goal (== x el))))))
(define (=/= e0 e1)
  (== #t (muk-func-app '=/= (list (list (full-repr e0) (full-repr e1))))))
(define (all-diffo xs)
  (matche xs
    ('())
    (`(,_))
    (`(,a ,ad . ,dd)
      (=/= a ad)
      (all-diffo `(,a . ,dd))
      (all-diffo `(,ad . ,dd)))))
(define (+o a b a+b)
  (conj* (numbero a) (numbero b) (numbero a+b)
         (== (muk-func-app '+ (list a b)) a+b)))
(define (<o a b)
  (conj* (numbero a) (numbero b) (== (muk-func-app '< (list a b)) #t)))
(define (<=o a b) (conde ((numbero a) (numbero b) (== a b)) ((<o a b))))

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

(define (nat<o a b)
  (conde
    ((== '() a) (exist (b0 bd) (== `(,b0 . ,bd) b)))
    ((exist (a0 ad b0 bd)
      (== `(,a0 . ,ad) a) (== `(,b0 . ,bd) b)
      (conde ((nat<o ad bd))
             ((== ad bd) (== 1 a0) (== 2 b0)))))))

(module+ test
  (lets
    (list actual expected) =
    (zip (forl
           (list a b) <- '((0 0) (0 1) (1 0) (1 1) (1 2) (2 1) (2 2)
                           (3 3) (3 4) (4 3) (4 4) (4 5) (5 4) (5 5))
           (list (pair? (run* (r) (nat<o (nat->bits a) (nat->bits b))))
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
           (list (run*-depth 1000 (r) (nat-addo (nat->bits a) (nat->bits b) r))
                 `((,(nat->bits (+ a b)))))))
    (check-equal? actual expected))
  (lets
    (list actual expected) =
    (zip (forl
           (list a b) <- '((0 0) (1 0) (2 1) (2 2) (3 1) (4 1) (4 2) (4 3)
                           (5 1) (5 2) (6 6) (7 1) (7 2) (7 3) (7 4) (7 5))
           (list (run*-depth 1000 (r) (nat-subo (nat->bits a) (nat->bits b) r))
                 `((,(nat->bits (- a b)))))))
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

(define (nat-divo a b q r)
  (exist (mr) (nat<o r b) (nat-mulo b q mr) (nat-addo r mr a)))

(module+ test
  (lets
    (list actual expected) =
    (zip (forl
           (list a b) <- '((0 0) (0 1) (1 0) (1 2) (2 1) (2 2) (3 4) (6 6))
           (list (run*-depth 1000 (r) (nat-mulo (nat->bits a) (nat->bits b) r))
                 `((,(nat->bits (* a b)))))))
    (check-equal? actual expected))
  ; slow test
  ;(lets
    ;(list actual expected) =
    ;(zip (forl
           ;(list a b) <- '((0 1) (1 1) (1 2) (2 1) (3 2) (3 4) (4 2))
           ;`(,(run-depth 1 1 (q r) (nat-divo (nat->bits a) (nat->bits b) q r))
              ;((,(nat->bits (quotient a b)) ,(nat->bits (remainder a b)))))))
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

(define (nat-logo b a p r)
  (exist (mr) (nat<o r a) (nat-expo b p mr) (nat-subo a mr r)))

(module+ test
  (lets
    (list actual expected) =
    (zip (forl
           (list a b) <- '((1 0) (1 1) (1 2) (2 1) (2 2) (2 3) (3 2))
           (list (run*-depth 100 (r) (nat-expo (nat->bits a) (nat->bits b) r))
                 `((,(nat->bits (expt a b)))))))
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
              ;((,(nat->bits p) ,(nat->bits r))))))
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
  ; TODO: re-enable with deterministic sub-func reification order
  ;(check-match
    ;(run 1 (q) with-constraints (all-diffo `(2 3 ,q)))
    ;`((,q :
          ;((type ,q) == ,r)
          ;((=/= (,r ((number real exact integer natural) ())) (,q 3)) == #t)
          ;((=/= (,r ((number real exact integer natural) ())) (,q 2)) == #t)
          ;)))
  (define (rembero x ls out)
    (conde
      ((== '() ls) (== '() out))
      ((exist (a d res)
        (== `(,a . ,d) ls)
        (rembero x d res)
        (conde
          ((== a x) (== res out))
          ((=/= a x) (== `(,a . ,res) out)))))))
  (check-equal?
    (run* (q) with-constraints (rembero 'a '(a b a c) q))
    '(((b c))))
  (check-equal?
    (run* (q) with-constraints (rembero 'a '(a b c) '(a b c)))
    '())
  (check-equal?
    (list->set
      (run* (x y) with-constraints (ino (range 3) x y) (all-diffo (list x y))))
    (list->set '((0 1) (0 2) (1 0) (1 2) (2 0) (2 1))))
  (check-equal?
    (run* (w x y z) with-constraints (ino (range 3) w x y z)
          (all-diffo (list w x y z)))
    '())
  (check-equal?
    (run* (w x y z) with-constraints (symbolo x) (symbolo z) (+o y y w)
          (ino (list 5 'five) x y z))
    '((10 five 5 five)))
  (lets
    ;   S E N D
    ; + M O R E
    ; ---------
    ; M O N E Y
    add-digitso = (fn (augend addend carry-in carry-out digit)
      (exist (partial-sum sum)
        (conj*-seq
          (+o augend addend partial-sum)
          (+o partial-sum carry-in sum)
          (conde
            ((<o 9 sum) (== carry-out 1) (+o digit 10 sum))
            ((<=o sum 9) (== carry-out 0) (== digit sum)))
          (ino (range 19) partial-sum)
          (ino (range 20) sum))))
    send-more-moneyo = (fn (letters)
      (exist (s e n d m o r y carry0 carry1 carry2)
        (conj*-seq
          (== letters (list s e n d m o r y))
          (all-diffo letters)
          (add-digitso s m carry2 m o)
          (add-digitso e o carry1 carry2 n)
          (add-digitso n r carry0 carry1 e)
          (add-digitso d e 0 carry0 y)
          (ino (range 1 10) s m)
          (ino (range 10) e n d o r y)
          (ino (range 2) carry0 carry1 carry2))))
    (check-equal?
      (run*-depth 1000 (a b c) with-constraints
        (send-more-moneyo (list a 5 6 b 1 0 c 2)))
      '((9 7 8))))
  (check-match
    (run* (p r) with-constraints
      (=/= '(1 2) `(,p ,r))
      (== 1 p)
      (symbolo r))
    `((1 ,r : ((type ,r) == (symbol ())))))
  )
