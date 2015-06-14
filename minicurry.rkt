#lang racket/base
(provide
  denote
  denote-eval
  env-empty
  senv-new
  )

(require
  "dict.rkt"
  "list.rkt"
  "maybe.rkt"
  "microkanren.rkt"
  "sugar.rkt"
  racket/dict
  racket/function
  racket/list
  (except-in racket/match ==)
  racket/set
  )

(module+ test
  (require
    (only-in "minikanren.rkt" run run*)
    rackunit
    ))

; TODO: more general letr
; TODO: unquote-splicing

(define ((app1 arg) f) (f arg))
(define (atom? x)
  (ormap (lambda (p) (p x))
         (list muk-var? symbol? boolean? number? string? char?)))

(define muk-value muk-success)
(define val-unit (void))
(define val-nil '())
(define val-cons cons)
(define denote-unit (const (muk-value val-unit)))
(define (build-cons fst snd) (val-cons (build-datum fst) (build-datum snd)))
(define (build-datum stx) (match stx
                            ((? atom?) stx)
                            ('() val-nil)
                            ((cons fst snd) (build-cons fst snd))))

(define (env-get env ident) (dict-get env ident))
(define (env-add env ident val) (dict-set env ident val))
(define (env-extend env params) (forf env = env
                                      param <- params
                                      (env-add env param #f)))
(define env-empty (hash))

(define (((eval-goal-cont cont) value-goal) st)
  (define (absorb-results results)
    (forl (list st comp) <- results
          (list st ((eval-goal-cont cont) comp))))
  (match value-goal
    ((muk-success value) (list (list st (cont value))))
    ((muk-conj-seq _ c0 c1)
     (list (list st (conj-seq c0 ((eval-goal-cont cont) c1)))))
    ((muk-conj-conc _ c0 c1)
     (list (list st (conj c0 ((eval-goal-cont cont) c1)))))
    ((muk-pause paused)
     (list (list st (muk-pause ((eval-goal-cont cont) paused)))))
    ((muk-unification e0 e1) (absorb-results (muk-step-unification st e0 e1)))
    ((muk-cost-goal cost goal) (absorb-results (goal st)))
    (_ (absorb-results (value-goal st)))))
(define (eval-logic-var value)
  (if (muk-var? value)
    (let loop ((value value))
      (muk-cost-goal 0
        (fn (st)
            result = (muk-sub-get-var st value)
            (if (muk-var? result)
              (list (list st (muk-pause (loop result))))
              (muk-unit st result)))))
    (muk-value value)))
(define (eval-application gproc gargs)
  (define (eval-app1 garg gproc)
    ((eval-goal-cont
       (lambda (arg) ((eval-goal-cont (compose1 (eval-goal-cont (app1 arg))
                                                eval-logic-var))
                      gproc))) garg))
  (foldl eval-app1 gproc gargs))
(define (possibly-strict strict? gbody)
  (if strict? gbody
    (let/vars (r0)
      (conj (apply-special-proc == (list (muk-value r0) gbody))
            (muk-value r0)))))
(def ((build-application strict? dproc dargs) env)
  gproc = (dproc env)
  gargs = (map (app1 env) dargs)
  gapp = (eval-application gproc gargs)
  (possibly-strict strict? gapp))
(def (denote-application strict? senv head tail)
  dproc = (denote-with senv head #t)
  dargs = (map (curry denote-with senv) tail)
  (build-application strict? dproc dargs))
(define (denote-quote strict? senv tail)
  (match tail
    ((list single) (const (muk-value (build-datum single))))
    (_ (error (format "invalid quote: ~a" `(quote . ,tail))))))
(define (denote-quasi-datum error-msg strict? senv stx)
  (match stx
    (`(unquote . ,tail) (match tail
                         ((list single) (denote-with senv single strict?))
                         (_ (error error-msg))))
    (`(,head . ,tail)
      (wrap-special-proc (compose1 muk-value cons)
        (map (curry denote-quasi-datum error-msg #f senv) (list head tail))))
    (_ (const (muk-value (build-datum stx))))))
(def (denote-quasiquote strict? senv tail)
  error-msg = (format "invalid quote: ~a" `(quote . ,tail))
  (match tail
    ((list single) (denote-quasi-datum error-msg strict? senv single))
    (_ (error error-msg))))

(define (pattern->identifiers pat)
  (define (unquote-pats stx)
    (match stx
      ((list 'unquote pat) (list pat))
      (`(,head . ,tail) (append (unquote-pats head) (unquote-pats tail)))
      (_ '())))
  (if (symbol? pat) (list pat)
    (match pat
      (`(quote ,_) '())
      (`(quasiquote ,stx)
       (append* (map pattern->identifiers (unquote-pats stx))))
      (`(,head . ,tail) (append* (map pattern->identifiers tail)))
      (_ '()))))

(def (pattern-matcher senv patterns)
  new-ident = (lambda () (gensym 'match-param))
  (list params pattern-identss m-arg-patterns) =
  (zip-default '(() () ())
               (forl pattern <- patterns
                     (if (symbol? pattern)
                       (list pattern '() (nothing))
                       (lets param = (new-ident)
                             (list param (pattern->identifiers pattern)
                                   (just (list param pattern)))))))
  pattern-idents = (list->set (append* pattern-identss))
  (list params m-arg-patterns) =
  (zip-default '(() ())
    (forl param <- params
          mppat <- m-arg-patterns
          (match mppat
            ((nothing)
             (if (set-member? pattern-idents param)
               (lets actual-param = (new-ident)
                     (list actual-param (just (list actual-param param))))
               (list param (nothing))))
            ((? just?) (list param mppat)))))
  arg-patterns = (maybe-filter m-arg-patterns)
  senv = (env-extend senv (append params (set->list pattern-idents)))
  dmatches =
  (forl (list param pattern) <- arg-patterns
        dpattern = (denote-with senv pattern)
        (wrap-special-proc == (list (denote-with senv param) dpattern)))
  dmatch = (if (null? dmatches) #f
             (foldr (curry build-conj #t) (last dmatches)
                    (list-init dmatches)))
  build-match =
  (fn (conditions dbody)
    dcond0 = (if (null? conditions) #f (denote-conj #t senv conditions))
    (build-exist
      pattern-idents
      (if (not (or dmatch dcond0)) dbody
        (lets dcond = (cond ((not dmatch) dcond0)
                            ((not dcond0) dmatch)
                            (else (build-conj dmatch dcond0)))
              (build-seq #t dcond dbody)))))
  (list params senv build-match))

(define (build-lam senv params dbody)
  (foldr (lambda (param body)
           (lambda (env)
             (muk-value
               (lambda (arg) (body (env-add env param (muk-value arg)))))))
         dbody params))
(define ((denote-lam-err err) _ senv tail)
  (match tail
    ((cons (? list? (? (compose1 (curry < 0) length) patterns))
           (? list? (? (compose1 (curry < 0) length) tail)))
     (lets (list conditions body) = (list-init+last tail)
           (list params senv build-match) = (pattern-matcher senv patterns)
           dbody = (build-match conditions (denote-with senv body #t))
           (build-lam senv params dbody)))
    (_ (err))))
(define (denote-lam strict? senv tail)
  ((denote-lam-err
     (lambda () (error (format "invalid lam: ~a" `(lam . ,tail)))))
   strict? senv tail))
(define (denote-letr strict? senv tail)
  (define (err) (error (format "invalid letr: ~a" `(letr . ,tail))))
  (if (and (not (null? tail)) (list? tail))
    (lets
      (list procs body) = (list-init+last tail)
      (list pnames ptails) =
      (zip-default '(() ())
                   (forl proc <- procs
                         (match proc
                           ((list (cons pname (? list? params)) pbody)
                            (list pname (list params pbody)))
                           (_ (err)))))
      senv = (env-extend senv pnames)
      dprocs = (map (curry denote-lam #t senv) ptails)
      dbody = (denote-with senv body strict?)
      (fn (env)
        boxes = (forl _ <- pnames (box (void)))
        env = (forf env = env
                    param <- pnames
                    bx <- boxes
                    (env-add env param bx))
        _ = (for_ bx <- boxes
                  dproc <- dprocs
                  proc = (dproc env)
                  (set-box! bx proc))
        (dbody env)))
    (err)))
(define (denote-let strict? senv tail)
  (define (err) (error (format "invalid let: ~a" `(let . ,tail))))
  (if (and (not (null? tail)) (list? tail))
    (lets
      (list assignments body) = (list-init+last tail)
      (list patterns args) =
      (zip-default '(() ()) (forl assignment <- assignments
                                  (match assignment
                                    ((list _ _) assignment)
                                    (_ (err)))))
      (build-application strict? (denote-lam strict? senv `(,patterns ,body))
                         (map (denote-with-strictness #f senv) args)))
    (err)))
(define (denote-let* strict? senv tail)
  (define (err) (error (format "invalid let*: ~a" `(let* . ,tail))))
  (if (and (not (null? tail)) (list? tail))
    (lets
      (list assignments body) = (list-init+last tail)
      (list senv rdassignments) =
      (forf (list senv rdassignments) = (list senv '())
            assignment <- assignments
            (match assignment
              ((list pattern arg)
               (lets (list (list param) senv build-match) =
                     (pattern-matcher senv (list pattern))
                     rdassignment = (list param (denote-with senv arg #f)
                                          build-match)
                     (list senv (list* rdassignment rdassignments))))
              (_ (err))))
      (forf dbody = (denote-with senv body #t)
            (list param darg build-match) <- rdassignments
            dbody = (build-match '() dbody)
            (build-application
              strict? (build-lam senv `(,param) dbody) `(,darg))))
    (err)))

(define (denote-match strict? senv tail)
  (define (err) (error (format "invalid match: ~a" `(match . ,tail))))
  (match tail
    ((cons arg alternatives)
     (lets lam-tails = (forl (cons pattern tail) <- alternatives
                             (cons (list pattern) tail))
           ((denote-match*-err err) strict? senv (cons (list arg) lam-tails))))
    (_ (err))))
(define ((denote-match*-err err) strict? senv tail)
  (match tail
    ((cons (? list? (? (compose1 (curry < 0) length) args))
           (? list? (? (compose1 (curry < 0) length) alternatives)))
     (lets dlams = (map (curry (denote-lam-err err) strict? senv) alternatives)
           (build-application strict? (build-disj #t dlams)
                              (map (denote-with-strictness #f senv) args))))
    (_ (err))))
(define (denote-match* strict? senv tail)
  ((denote-match*-err
     (lambda () (error (format "invalid match*: ~a" `(match* . ,tail)))))
   strict? senv tail))
(define (denote-if strict? senv tail)
  (match tail
    ((list condition true false)
     (lets
       dtail = (map (denote-with-strictness #t senv) tail)
       (fn (env)
         (list gcond gtrue gfalse) = (map (app1 env) dtail)
         body = (lambda (cnd)
          (if (muk-var? cnd)
            (disj (conj-seq (== #t cnd) gtrue) (conj-seq (== #f cnd) gfalse))
            (match cnd (#t gtrue) (#f gfalse)
              (_ (error (format "non-boolean if condition: ~a" cnd))))))
         (possibly-strict strict? ((eval-goal-cont body) gcond)))))
    (_ (error (format "invalid if statement: ~a" `(if . ,tail))))))

(define (eval-all-args gargs (rargs '()))
  (match gargs
    ('() (muk-value (reverse rargs)))
    ((cons garg gargs)
     ((eval-goal-cont
        (lambda (arg) (eval-all-args gargs (list* arg rargs)))) garg))))
(def (apply-special-proc proc gargs)
  ((eval-goal-cont (lambda (args) (apply proc args))) (eval-all-args gargs)))
(define ((wrap-special-proc proc dargs) env)
  (apply-special-proc proc (map (app1 env) dargs)))
(define ((denote-special-proc proc-name nargs strict-args? proc)
         strict? senv tail)
  (match tail
    ((? list? (? (compose1 (curry = nargs) length)))
     (wrap-special-proc
       proc (map (denote-with-strictness (and strict-args? strict?) senv)
                 tail)))
    (_ (error (format "'~a' expects ~a argument(s): ~a"
                      proc-name nargs `(,proc-name . ,tail))))))
(define denote-type
  (denote-special-proc 'type 1 #f
    (lambda (arg)
      (if (muk-var? arg)
        (disj (conj-seq (== '() arg) (muk-value 'nil))
              (conj-seq (let/vars (a0 d0) (== `(,a0 . ,d0) arg))
                        (muk-value 'pair)))
        (muk-value
          (cond ((null? arg) 'nil)
                ((pair? arg) 'pair)
                (else (error (format "cannot determine type of: ~a"
                                     arg)))))))))

(define ((build-conj strict? dc0 dtail) env)
  (possibly-strict strict? (conj (dc0 env) (dtail env))))
(define ((build-seq strict? dc0 dtail) env)
  (possibly-strict strict? (conj-seq (dc0 env) (dtail env))))
(define (denote-conj+seq strict? senv tail)
  (match tail
    ((? list? (? (compose1 (curry < 0) length)))
     (lets (list conditions body) = (list-init+last tail)
           dbody = (denote-with senv body #t)
           (if (null? conditions) dbody
             (build-seq strict? (denote-conj #t senv conditions) dbody))))
    (_ (error (format "invalid conjunction sequence: ~a" tail)))))

(define denote-== (denote-special-proc '== 2 #f ==))
(define (build-exist params dbody)
  (forf dbody = dbody
        param <- params
        (lambda (env)
          (let/vars (x0)
            (dbody (env-add env param (muk-value x0)))))))
(define (denote-exist strict? senv tail)
  (match tail
    ((cons (? list? (? (fn (ps) (andmap symbol? ps)) params)) body)
     (lets senv = (env-extend senv params)
           error-msg = (format "invalid 'exist': ~a" `(exist ,params . ,body))
           dbody = (denote-conj+seq strict? senv body)
           (build-exist params dbody)))
    (_ (format "invalid 'exist': ~a" `(exist . ,tail)))))
(define (denote-conj strict? senv tail)
  (match tail
    ((? list? (? (compose1 (curry < 0) length)))
     (lets (list prefixes body) = (list-init+last tail)
           dprefixes = (map (lambda (arg) (denote-with senv arg #t)) prefixes)
           dbody = (denote-with senv body strict?)
           (foldr (curry build-conj #t) dbody dprefixes)))
    (_ (error (format "invalid conjunction: ~a" `(conj . ,tail))))))
(define (denote-seq strict? senv tail)
  (match tail
    ((list body) (denote-with senv body strict?))
    ((cons c0 tail)
     (lets dc0 = (denote-with senv c0 #t)
           dtail = (denote-seq #t senv tail)
           (build-seq strict? dc0 dtail)))
    (_ (error (format "invalid sequential conjunction: ~a" `(seq . ,tail))))))
(def (build-disj strict? dalternatives)
  (list dinitial dfinal) = (list-init+last dalternatives)
  (possibly-strict
    strict? (foldr (lambda (dhead dtail)
                     (lambda (env) (disj (dhead env) (dtail env))))
                   dfinal dinitial)))
(define (denote-disj strict? senv tail)
  (match tail
    ((? list? (? (compose1 (curry < 0) length) tail))
     (build-disj strict? (map (curry denote-conj+seq #t senv) tail)))
    (_ (error (format "invalid disjunction: ~a" `(disj . ,tail))))))

(define senv-new (hash
                   'quote denote-quote
                   'quasiquote denote-quasiquote
                   'lam denote-lam
                   'letr denote-letr
                   'let denote-let
                   'let* denote-let*
                   'match denote-match
                   'match* denote-match*
                   'if denote-if
                   'type denote-type
                   '== denote-==
                   'exist denote-exist
                   'conj denote-conj
                   'seq denote-seq
                   'disj denote-disj
                   ))

(define (denote-identifier senv ident)
  (match (env-get senv ident)
    ((nothing) (error (format "undefined identifier: ~a" ident)))
    ((just special?)
     (if special?
       (error (format "invalid use of special identifier: ~a" ident))
       (lambda (env) (match (just-x (env-get env ident))
                       ((? box? val) (unbox val))
                       (val val)))))))
(define (denote-atom atom) (const (muk-value atom)))

(define (denote-with senv stx (strict? #f))
  (match stx
    ((? symbol?) (denote-identifier senv stx))
    ((? atom?) (denote-atom stx))
    ('() denote-unit)
    ((cons head tail)
     (match (if (symbol? head) (env-get senv head) (nothing))
       ((just (? procedure? denote-special))
        (denote-special strict? senv tail))
       (_ (denote-application strict? senv head tail))))))
(define ((denote-with-strictness strict? senv) stx)
  (denote-with senv stx strict?))

(define (denote stx) (denote-with senv-new stx #t))
(define (denote-eval stx) ((denote stx) env-empty))

(module+ test
  (check-equal?
    (run* q (denote-eval `(== ,q (quote (a b)))))
    '((a b)))
  (check-equal?
    (run* q (denote-eval `(== ,q ((lam (x y) x) 5 (quote (a b c))))))
    '(5))
  (check-equal?
    (run* (q r)
      (denote-eval `(== ,q ((lam (x y) (seq (== ,r y) x)) 5 (quote (a b c))))))
    '((5 (a b c))))
  (check-equal?
    (run* q (denote-eval `(== ,q ((lam (rec val) `(,val . ,rec)) '() 6))))
    '((6)))
  (check-equal?
    (run* q (denote-eval `(== ,q (let (rec '()) (val 6) `(,val . ,rec)))))
    '((6)))
  (check-equal?
    (run* q (denote-eval `(== ,q (let* (val 7) (pr `(,val)) pr))))
    '((7)))
  (check-equal?
    (run* (q c) (denote-eval `(== ,q (if ,c `(,(if #t 3 4) . ,(if #f 3 4))
                                       'else))))
    '((else #f) ((3 . 4) #t)))
  (check-equal?
    (run* q (denote-eval `(== ,q `(a ,`(b . c) (d e)))))
    '((a (b . c) (d e))))
  (check-equal?
    (run* q
      (denote-eval `((exist (a b) (== 1 a) (== 2 b) (== ,q `(,a ,b))))))
    '((1 2)))
  (check-equal?
    (run* q
      (denote-eval `(== ,q (exist (f) (seq (== f (lam (x) x)) (f 11))))))
    '(11))
  (check-equal?
    (run* q
      (denote-eval `(== ,q ((lam (4 `(,a b ,c)) `(,a . ,c)) 4 '(8 b 9)))))
    '((8 . 9)))
  (check-equal?
    (run* q (denote-eval `(== ,q (let (4 4)
                                        (`(,a b ,c) '(8 b 7))
                                     `(,a . ,c)))))
    '((8 . 7)))
  (check-equal?
    (run* q (denote-eval `(== ,q (let* (`(,a b ,c) `(4 b 5))
                                         (`(,d . ,e) `(,c . ,a))
                                     `(,d ,e 3)))))
    '((5 4 3)))
  (check-equal?
    (list->set (run* q (denote-eval `(== ,q (match `(3 . a)
                                              (`(,x . a) x)
                                              (`(3 . ,y) y))))))
    (set 'a 3))
  (check-equal?
    (list->set (run* q (denote-eval `(== ,q (match* (17 `(3 . a))
                                              ((17 `(,x . a)) x)
                                              ((x `(3 . ,y)) `(,x . ,y)))))))
    (set 3 '(17 . a)))
  (check-equal?
    (run* q
      (denote-eval
        `(== ,q
           (letr ((test x y) x)
                 (test 3 4)))))
    '(3))

  (lets
    shared =
    '(((even? xs) (match xs
                    ('() #t)
                    (`(,hd . ,tl) (odd? tl))))
      ((odd? xs) (match xs
                   ('() #f)
                   (`(,hd . ,tl) (even? tl))))
      ((cons a b) `(,a . ,b))
      ((single x) `(,x))
      ((flip f x y) (f y x))
      ((compose f g x) (f (g x)))

      ((foldl f acc xs) (match xs
                           ('() acc)
                           (`(,y . ,ys) (foldl f (f y acc) ys))))
      ((foldr f acc xs) (match xs
                           ('() acc)
                           (`(,y . ,ys) (f y (foldr f acc ys)))))

      ((map f xs) (foldr (compose cons f) '() xs))
      ((filter p? xs) (foldr (lam (y ys) (if (p? y) (cons y ys) ys)) '() xs))

      ((append xs ys) (foldr cons ys xs))
      ((rev xs) (foldl cons '() xs))  ; not well-behaved when run backwards
      ((reverse xs) (foldr (compose (flip append) single) '() xs))
      ((last (append xs `(,result))) result)

      ((member element (append xs (cons element ys))) ())
      )
    (begin
      (check-equal?
        (run* q
          (denote-eval
            `(== ,q
                 (letr ,@shared
                   `((is-even ,(even? '(a b c)))
                     (is-odd ,(odd? '(a b c))))))))
        '(((is-even #f) (is-odd #t))))
      (check-equal?
        (run* q
          (denote-eval `(== ,q (letr ,@shared
                                 (append '(a b c) '(d e f))))))
        '((a b c d e f)))
      (check-equal?
        (run* (r s)
          (denote-eval `(letr ,@shared
                          (== (append ,r ,s) '(1 2 3)))))
        '((() (1 2 3))
          ((1) (2 3))
          ((1 2) (3))
          ((1 2 3) ())))
      (check-equal?
        (run* q
          (denote-eval `(letr ,@shared
                          ((== ,q (last '(1 2 3)))))))
        '(3))
      (check-equal?
        (run 1 q (denote-eval
                     `(letr ,@shared (== '(1 2 3) (rev ,q)))))
        '((3 2 1)))
      (check-equal?
        (run* q
          (denote-eval `(letr ,@shared
                          ((== ,q (reverse '(1 2 3)))))))
        '((3 2 1)))
      (check-equal?
        (run* q
          (denote-eval `(letr ,@shared
                          (== ,q (== (rev '(1 2 3)) (reverse '(1 2 3)))))))
        (list (void)))
      (check-equal?
        (run* q (denote-eval
          `(== ,q (letr ,@shared
                    (map reverse '((a b c) (1 2 3)))))))
        '(((c b a) (3 2 1))))
      (check-equal?
        (run* q (denote-eval
          `(letr ,@shared
             (== '((c b a) (3 2 1)) (map reverse '((a b c) ,q))))))
        '((1 2 3)))
      (check-equal?
        (run* q (denote-eval
          `(letr ,@shared
             (== '((c b 3) (3 2 1)) (map reverse '((,q b c) (1 2 ,q)))))))
        '(3))
      (check-equal?
        (list->set
          (run* q (denote-eval
            `(letr ,@shared
                   ((next-day day) (match day
                                     ('mon 'tue)
                                     ('tue 'wed)
                                     ('wed 'thur)
                                     ('thur 'fri)
                                     ('fri 'sat)
                                     ('sat 'sun)))
                   ((weekday? day) (match day
                                     ('mon #t)
                                     ('tue #t)
                                     ('wed #t)
                                     ('thur #t)
                                     ('fri #t)
                                     ('sat #f)
                                     ('sun #f)))
                   (== '() (filter (compose weekday? next-day) '(,q)))))))
        (set 'sat 'fri))
      (check-equal?
        (run* q (denote-eval
          `(letr ,@shared
             (conj (member ,q '(1 2 3))
                   (member ,q '(2 3 4))))))
        '(2 3))
      )))
