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
; syntactic sugar for if, tag-case, general match

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
(def (denote-application senv head tail)
  dproc = (denote-with senv head)
  dargs = (map (curry denote-with senv) tail)
  (fn (env)
    gproc = (dproc env)
    gargs = (map (app1 env) dargs)
    gapp = ((eval-goal-cont (eval-application gargs)) gproc)
    (call/var
      (lambda (r0)
        (conj (apply-special-proc == (list (muk-value r0) gapp))
              (muk-value r0))))))
(define (denote-quote _ tail)
  (match tail
    ((list single) (const (muk-value (build-datum single))))
    (_ (error (format "invalid quote: ~a" `(quote . ,tail))))))

(define (denote-lam senv tail)
  (match tail
    ((list (? list? (? (fn (ps) (andmap symbol? ps)) params)) body)
     (foldr (lambda (param body)
              (lambda (env)
                (muk-value
                  (lambda (arg) (body (env-add env param (muk-value arg)))))))
            (denote-with (env-extend senv params) body)
            params))
    (_ (error (format "invalid lam: ~a" `(lam . ,tail))))))
(define (denote-letr senv tail)
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
      dprocs = (map (curry denote-lam senv) ptails)
      dbody = (denote-with senv body)
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

(define (eval-all-args gargs (rargs '()))
  (match gargs
    ('() (muk-value (reverse rargs)))
    ((cons garg gargs)
     ((eval-goal-cont
        (lambda (arg) (eval-all-args gargs (list* arg rargs)))) garg))))
(def (apply-special-proc proc gargs)
  ((eval-goal-cont (lambda (args) (apply proc args))) (eval-all-args gargs)))
(define ((denote-special-proc proc-name nargs proc) senv tail)
  (match tail
    ((? list? (? (compose1 (curry = nargs) length)))
     (lets args = (map (curry denote-with senv) tail)
           (fn (env)
             gargs = (map (app1 env) args)
             (apply-special-proc proc gargs))))
    (_ (error (format "'~a' expects ~a argument(s): ~a"
                      proc-name nargs `(,proc-name . ,tail))))))
(define denote-type
  (denote-special-proc 'type 1
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
(define denote-pair (denote-special-proc 'pair 2 (compose1 muk-value cons)))
(define denote-head (denote-special-proc 'head 1 (eval-pair-proc car)))
(define denote-tail (denote-special-proc 'tail 1 (eval-pair-proc cdr)))

(define ((eval-seq dc0 dtail) env) (conj-seq (dc0 env) (dtail env)))
(define ((denote-conj+seq error-msg) senv tail)
  (match tail
    ((? list? (? (compose1 (curry < 0) length)) tail)
     (lets (list conditions body) = (list-init+last tail)
           dconj = (denote-conj senv conditions)
           dbody = (denote-with senv body)
           (eval-seq dconj dbody)))
    (_ (error error-msg))))

(define denote-== (denote-special-proc '== 2 ==))
(define (denote-exist senv tail)
  (match tail
    ((cons (? list? (? (fn (ps) (andmap symbol? ps)) params)) body)
     (lets senv = (env-extend senv params)
           error-msg = (format "invalid 'exist': ~a" `(exist ,params . ,body))
           dbody = ((denote-conj+seq error-msg) senv body)
           (forf dbody = dbody
                 param <- params
                 (lambda (env)
                   (call/var (lambda (x0)
                               (dbody (env-add env param (muk-value x0)))))))))
    (_ (format "invalid 'exist': ~a" `(exist . ,tail)))))
(define (denote-conj senv tail)
  (if (not (list? tail))
    (error (format "invalid conjunction: ~a" `(conj . ,tail)))
    (lets args = (map (curry denote-with senv) tail)
          (fn (env)
            gargs = (map (app1 env) args)
            (foldr conj muk-unit gargs)))))
(define (denote-seq senv tail)
  (match tail
    ((list body) (denote-with senv body))
    ((cons c0 tail)
     (lets dc0 = (denote-with senv c0)
           dtail = (denote-seq senv tail)
           (eval-seq dc0 dtail)))
    (_ (error (format "invalid sequential conjunction: ~a" `(seq . ,tail))))))
(define (denote-disj senv tail)
  (match tail
    ('() (lambda (_) (const muk-mzero)))
    ((cons (? list? (? (compose1 (curry < 0) length)) head) tail)
     (lets (list conditions body) = (list-init+last head)
           dconj = (denote-conj senv conditions)
           dbody = (denote-with senv body)
           dtail = (denote-disj senv tail)
           (lambda (env) (disj ((eval-seq dconj dbody) env) (dtail env)))))
    (_ (error (format "invalid disjunction: ~a" `(disj . ,tail))))))

(define senv-new (hash
                   'quote denote-quote
                   'lam denote-lam
                   'letr denote-letr
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

(define (denote-with senv stx)
  (match stx
    ((? symbol?) (denote-identifier senv stx))
    ((? atom?) (denote-atom stx))
    ('() denote-unit)
    ((cons head tail)
     (match (if (symbol? head) (env-get senv head) (nothing))
       ((just (? procedure? denote-special)) (denote-special senv tail))
       (_ (denote-application senv head tail))))))

(define (denote stx) (denote-with senv-new stx))
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
    (run* (q)
      (denote-eval `(== ,q ((lam (rec val) (head (pair val rec))) () 4))))
    '((4)))
  (check-equal?
    (run* (q)
      (denote-eval `(== ,q ((lam (rec val) (tail (pair val rec))) () 4))))
    '((())))
  (check-equal?
    (run* (q)
      (denote-eval
        `((exist (a b) (== 1 a) (== 2 b) (== ,q (pair a (pair b ())))))))
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
             (pair (pair 'is-even (pair (even? '(a b c)) ()))
                   (pair (pair 'is-odd (pair (odd? '(a b c)) ())) ()))))))
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
