#lang racket/base
(provide
  )

(require
  "dict.rkt"
  "list.rkt"
  "maybe.rkt"
  "sugar.rkt"
  racket/dict
  racket/function
  racket/match
  )

(module+ test
  (require
    rackunit
    ))

; TODO:
; syntactic sugar for if, tag-case, general match
; logic terms
  ; exist, logic vars
; denote : syntax -> env -> logic-result -> st -> [st]
;   or?
; denote : syntax -> env -> st -> [st]

(define ((app1 arg) f) (f arg))
(define (atom? x)
  (ormap (lambda (p) (p x)) (list symbol? boolean? number? string? char?)))

(define val-unit '())
(define val-nil '())
(define val-cons cons)
(define denote-unit (const val-unit))
(define (build-cons fst snd) (val-cons (build-datum fst) (build-datum snd)))
(define (build-datum stx) (match stx
                            ((? atom?) stx)
                            ('() val-nil)
                            ((cons fst snd) (build-cons fst snd))))
(define pretty-datum identity)

(define (env-get env ident) (dict-get env ident))
(define (env-add env ident val) (dict-set env ident val))
(define (env-extend env params) (forf env = env
                                      param <- params
                                      (env-add env param #f)))
(define env-empty (hash))

(def (denote-application senv head tail)
  dproc = (denote-with senv head)
  dargs = (map (curry denote-with senv) tail)
  (lambda (env)
    (forf proc = (dproc env)
          arg <- (map (app1 env) dargs)
          (proc arg))))
(define (denote-quote _ tail)
  (match tail
    ((list single) (const (build-datum single)))
    (_ (error (format "invalid quote: ~a" `(quote . ,tail))))))

(define (denote-lam senv tail)
  (match tail
    ((list (? list? params) body)
     (foldr (lambda (param body)
              (lambda (env)
                (lambda (arg) (body (env-add env param arg)))))
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

(define ((denote-special-proc proc-name nargs proc) senv tail)
  (match tail
    ((? list? (? (compose1 (curry = nargs) length)))
     (lets args = (map (curry denote-with senv) tail)
           (lambda (env) (apply proc (map (app1 env) args)))))
    (_ (error (format "'~a' expects ~a argument(s): ~a"
                      proc-name nargs `(,proc-name . ,tail))))))
(define denote-type
  (denote-special-proc 'type 1
    (lambda (arg)
      (cond ((null? arg) 'nil)
            ((pair? arg) 'pair)
            ((atom? arg) 'atom)
            ((procedure? arg) 'procedure)
            (else (error (format "cannot determine type of: ~a" arg)))))))
(define denote-pair (denote-special-proc 'pair 2 cons))
(define denote-head (denote-special-proc 'head 1 car))
(define denote-tail (denote-special-proc 'tail 1 cdr))

(define denote-== (denote-special-proc '== 2 equal?))
(define (denote-conj senv tail)
  (if (not (list? tail))
    (error (format "invalid conjunction: ~a" `(conj . ,tail)))
    (lets args = (map (curry denote-with senv) tail)
          (lambda (env) (andmap (app1 env) args)))))
(define (denote-seq senv tail)
  (match tail
    ((list body) (denote-with senv body))
    ((cons c0 tail)
     (lets dc0 = (denote-with senv c0)
           dtail = (denote-seq senv tail)
           (lambda (env)
             (if (dc0 env) (dtail env) (error "sequential conjunction failure")))))
    (_ (error (format "invalid sequential conjunction: ~a" `(seq . ,tail))))))
(define (denote-disj senv tail)
  (match tail
    ('() (lambda (_) (error "disjunction failure")))
    ((cons (? list? (? (compose1 (curry < 0) length)) head) tail)
     (lets (list conditions body) = (list-init+last head)
           dconj = (denote-conj senv conditions)
           dbody = (denote-with senv body)
           dtail = (denote-disj senv tail)
           (lambda (env) (if (dconj env) (dbody env) (dtail env)))))
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
       (lambda (env)
         (match (just-x (env-get env ident))
           ((? box? val) (unbox val))
           (val val)))))))
(define (denote-atom atom) (const atom))

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
    (pretty-datum (denote-eval '(quote (a b))))
    '(a b))
  (check-equal?
    (pretty-datum (denote-eval '((lam (x y) x) 5 (quote (a b c)))))
    5)
  (check-equal?
    (pretty-datum
      (denote-eval '((lam (rec val) (type 'sym)) () 5)))
    'atom)
  (check-equal?
    (pretty-datum
      (denote-eval '((lam (rec val) (pair val rec)) () 5)))
    '(5))
  (check-equal?
    (pretty-datum
      (denote-eval '((lam (rec val) (head (pair val rec))) () 4)))
    4)
  (check-equal?
    (pretty-datum
      (denote-eval '((lam (rec val) (tail (pair val rec))) () 4)))
    '())
  (check-equal?
    (pretty-datum
      (denote-eval
        '(letr
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
                 (pair (pair 'is-odd (pair (odd? '(a b c)) ())) ())))))
    '((is-even #f) (is-odd #t)))
  )
