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
  (except-in racket/match ==)
  )

(module+ test
  (require
    (only-in "minikanren.rkt" run run*)
    rackunit
    ))

; TODO:
; syntactic sugar for general match, more general letr
; application-like laziness for other constructs

(define ((app1 arg) f) (f arg))
(define (atom? x)
  (ormap (lambda (p) (p x))
         (list muk-var? symbol? boolean? number? string? char?)))

(define ((muk-value val) st) (muk-unit st val))
(define val-unit '())
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
  (match value-goal
    ((muk-success value) ((cont value) st))
    ((muk-conj-seq c0 c1)
     (list (list st (muk-conj-seq c0 ((eval-goal-cont cont) c1)))))
    ((muk-conj-conc c0 c1)
     (list (list st (muk-conj-conc c0 ((eval-goal-cont cont) c1)))))
    ((muk-pause paused)
     (list (list st (muk-pause ((eval-goal-cont cont) paused)))))
    (_ (forl (list st comp) <- (value-goal st)
             (list st ((eval-goal-cont cont) comp))))))
(define (eval-logic-var value)
  (if (muk-var? value)
    (let loop ((value value))
      (fn (st)
        result = (muk-sub-get-var st value)
        (if (muk-var? result)
          (list (list st (muk-pause (loop result))))
          ((muk-value result) st))))
    (muk-value value)))
(define ((eval-application gargs) proc)
  (match gargs
    ('() (muk-value proc))
    ((cons garg gargs)
     ((eval-goal-cont
        (lambda (actual-proc)
          ((eval-goal-cont (compose1 (eval-goal-cont (eval-application gargs))
                                     actual-proc)) garg)))
      (eval-logic-var proc)))))
(define (possibly-strict strict? gbody)
  (if strict? gbody
    (call/var
      (lambda (r0)
        (conj (apply-special-proc == (list (muk-value r0) gbody))
              (muk-value r0))))))
(def ((build-application strict? dproc dargs) env)
  gproc = (dproc env)
  gargs = (map (app1 env) dargs)
  gapp = ((eval-goal-cont (eval-application gargs)) gproc)
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

(define (build-lam senv params dbody)
  (foldr (lambda (param body)
           (lambda (env)
             (muk-value
               (lambda (arg) (body (env-add env param (muk-value arg)))))))
         dbody params))
(define (denote-lam _ senv tail)
  (match tail
    ((list (? list? (? (fn (ps) (andmap symbol? ps)) params)) body)
     (build-lam senv params (denote-with (env-extend senv params) body #t)))
    (_ (error (format "invalid lam: ~a" `(lam . ,tail))))))
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
      (list params args) =
      (zip-default '(() ()) (forl assignment <- assignments
                                  (match assignment
                                    ((list _ _) assignment)
                                    (_ (err)))))
      (build-application strict? (denote-lam strict? senv `(,params ,body))
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
              ((list param arg)
               (lets senv = (env-extend senv `(,param))
                     rdassignment = (list param (denote-with senv arg #f))
                     (list senv (list* rdassignment rdassignments))))
              (_ (err))))
      (forf dbody = (denote-with senv body #t)
            (list param darg) <- rdassignments
            (build-application strict? (build-lam senv `(,param) dbody)
                               `(,darg))))
    (err)))
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
         (possibly-strict strict? ((eval-application `(,gcond)) body)))))
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
              (conj-seq (call/var (lambda (a0) (call/var (lambda (d0)
                (== `(,a0 . ,d0) arg))))) (muk-value 'pair)))
        (muk-value
          (cond ((null? arg) 'nil)
                ((pair? arg) 'pair)
                (else (error (format "cannot determine type of: ~a"
                                     arg)))))))))
(define ((eval-pair-proc proc) pr)
  (if (muk-var? pr)
    (call/var (lambda (a0) (call/var (fn (d0)
      actual-pair = `(,a0 . ,d0)
      (conj-seq (== actual-pair pr) (muk-value (proc actual-pair)))))))
    (muk-value (proc pr))))
(define denote-pair (denote-special-proc 'pair 2 #f (compose1 muk-value cons)))
(define denote-head (denote-special-proc 'head 1 #t (eval-pair-proc car)))
(define denote-tail (denote-special-proc 'tail 1 #t (eval-pair-proc cdr)))

(define ((eval-seq dc0 dtail) env) (conj-seq (dc0 env) (dtail env)))
(define (denote-conj+seq strict? senv tail)
  (match tail
    ((? list? (? (compose1 (curry < 0) length)))
     (lets (list conditions body) = (list-init+last tail)
           dbody = (denote-with senv body strict?)
           (if (null? conditions) dbody
             (eval-seq (denote-conj #t senv conditions) dbody))))
    (_ (error (format "invalid conjunction sequence: ~a" tail)))))

(define denote-== (denote-special-proc '== 2 #t ==))
(define (denote-exist strict? senv tail)
  (match tail
    ((cons (? list? (? (fn (ps) (andmap symbol? ps)) params)) body)
     (lets senv = (env-extend senv params)
           error-msg = (format "invalid 'exist': ~a" `(exist ,params . ,body))
           dbody = (denote-conj+seq strict? senv body)
           (forf dbody = dbody
                 param <- params
                 (lambda (env)
                   (call/var (lambda (x0)
                               (dbody (env-add env param (muk-value x0)))))))))
    (_ (format "invalid 'exist': ~a" `(exist . ,tail)))))
(define (denote-conj strict? senv tail)
  (match tail
    ((? list? (? (compose1 (curry < 0) length)))
     (lets (list prefixes body) = (list-init+last tail)
           dprefixes = (map (lambda (arg) (denote-with senv arg #t)) prefixes)
           dbody = (denote-with senv body strict?)
           (lambda (env) (foldr conj (dbody env) (map (app1 env) dprefixes)))))
    (_ (error (format "invalid conjunction: ~a" `(conj . ,tail))))))
(define (denote-seq strict? senv tail)
  (match tail
    ((list body) (denote-with senv body strict?))
    ((cons c0 tail)
     (lets dc0 = (denote-with senv c0 #t)
           dtail = (denote-seq strict? senv tail)
           (eval-seq dc0 dtail)))
    (_ (error (format "invalid sequential conjunction: ~a" `(seq . ,tail))))))
(define (denote-disj strict? senv tail)
  (match tail
    ((list head) (denote-conj+seq strict? senv head))
    ((cons head tail) (lets dhead = (denote-conj+seq strict? senv head)
                            dtail = (denote-disj strict? senv tail)
                            (lambda (env) (disj (dhead env) (dtail env)))))
    (_ (error (format "invalid disjunction: ~a" `(disj . ,tail))))))

(define senv-new (hash
                   'quote denote-quote
                   'quasiquote denote-quasiquote
                   'lam denote-lam
                   'letr denote-letr
                   'let denote-let
                   'let* denote-let*
                   'if denote-if
                   'type denote-type
                   'pair denote-pair
                   'head denote-head
                   'tail denote-tail
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
    (run* (q) (denote-eval `(== ,q (quote (a b)))))
    '(((a b))))
  (check-equal?
    (run* (q) (denote-eval `(== ,q ((lam (x y) x) 5 (quote (a b c))))))
    '((5)))
  (check-equal?
    (run* (q r)
      (denote-eval `(== ,q ((lam (x y) (seq (== ,r y) x)) 5 (quote (a b c))))))
    '((5 (a b c))))
  (check-equal?
    (run* (q) (denote-eval `(== ,q ((lam (rec val) (pair val rec)) () 6))))
    '(((6))))
  (check-equal?
    (run* (q) (denote-eval `(== ,q (let (rec ()) (val 6) (pair val rec)))))
    '(((6))))
  (check-equal?
    (run* (q) (denote-eval `(== ,q (let* (val 7) (pr (pair val ())) pr))))
    '(((7))))
  (check-equal?
    (run* (q c) (denote-eval `(== ,q (if ,c (pair (if #t 3 4) (if #f 3 4))
                                       'else))))
    '((else #f) ((3 . 4) #t)))
  (check-equal?
    (run* (q)
      (denote-eval `(== ,q ((lam (rec val) (head (pair val rec))) () 4))))
    '((4)))
  (check-equal?
    (run* (q)
      (denote-eval `(== ,q ((lam (rec val) (tail (pair val rec))) () 4))))
    '((())))
  (check-equal?
    (run* (q) (denote-eval `(== ,q `(a ,(pair 'b 'c) (d e)))))
    '(((a (b . c) (d e)))))
  (check-equal?
    (run* (q)
      (denote-eval `((exist (a b) (== 1 a) (== 2 b) (== ,q `(,a ,b))))))
    '(((1 2))))
  (check-equal?
    (run* (q)
      (denote-eval `(== ,q (exist (f) (seq (== f (lam (x) x)) (f 11))))))
    '((11)))
  (check-equal?
    (run* (q r) (denote-eval `(== ,r (type ,q))))
    '((() nil) ((_.2 . _.3) pair)))
  (check-equal?
    (run* (q r) (denote-eval `(== ,r (head ,q))))
    '(((_.1 . _.3) _.1)))
  (check-equal?
    (run* (q r) (denote-eval `(== ,r (tail ,q))))
    '(((_.2 . _.1) _.1)))
  (check-equal?
    (run* (q)
      (denote-eval
        `(== ,q
           (letr ((test x y) x)
                 (test 3 4)))))
    '((3)))
  (check-equal?
    (run* (q)
      (denote-eval
        `(== ,q
           (letr
             ((list-case xs nil-case pair-case)
              (disj ((== 'nil (type xs)) (nil-case '()))
                    ((== 'pair (type xs)) (pair-case (head xs) (tail xs)))))
             ((even? xs) (list-case xs
                                    (lam (_) #t)
                                    (lam (hd tl) (odd? tl))))
             ((odd? xs) (list-case xs
                                   (lam (_) #f)
                                   (lam (hd tl) (even? tl))))
             `((is-even ,(even? '(a b c)))
               (is-odd ,(odd? '(a b c))))))))
    '((((is-even #f) (is-odd #t)))))
  (check-equal?
    (run* (q r s)
      (denote-eval
        `(== ,q
           (letr
             ((list-case xs nil-case pair-case)
              (disj ((== 'nil (type xs)) (nil-case '()))
                    ((== 'pair (type xs)) (pair-case (head xs) (tail xs)))))
             ((append xs ys)
              (list-case xs
                         (lam (_) ys)
                         (lam (hd tl) (pair hd (append tl ys)))))
             (seq (== (append ,r ,s) '(1 2 3))
                  (append '(a b c) '(d e f)))))))
    '(((a b c d e f) () (1 2 3))
      ((a b c d e f) (1) (2 3))
      ((a b c d e f) (1 2) (3))
      ((a b c d e f) (1 2 3) ())))
  (check-equal?
    (run* (q)
      (denote-eval
        `(letr
           ((list-case xs nil-case pair-case)
            (disj ((== 'nil (type xs)) (nil-case '()))
                  ((== 'pair (type xs)) (pair-case (head xs) (tail xs)))))
           ((append xs ys)
            (list-case xs
                       (lam (_) ys)
                       (lam (hd tl) (pair hd (append tl ys)))))
           ((last xs) (exist (ys result)
                             (== (append ys (pair result ())) xs)
                             result))
           ((== ,q (last '(1 2 3)))))))
    '((3)))
  )
