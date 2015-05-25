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
  ; ==
  ; disj
  ; conj
  ; conj-seq
; denote : syntax -> env -> logic-result -> st -> [st]
;   or?
; denote : syntax -> env -> st -> [st]

(define (atom? x)
  (ormap (lambda (p) (p x)) (list symbol? boolean? number? string? char?)))

(define (tagged tag payload) (hash 'tag tag 'payload payload))

(define val-unit (hash))
(define val-nil (tagged 'nil val-unit))
(define (val-cons head tail) (tagged 'pair (hash 'head head 'tail tail)))
(define denote-unit (const val-unit))
(define (build-cons fst snd) (val-cons (build-datum fst) (build-datum snd)))
(define (build-datum stx) (match stx
                            ((? atom?) stx)
                            ('() val-nil)
                            ((cons fst snd) (build-cons fst snd))))

(define (pretty-datum datum)
  (match datum
    ((? hash?)
     (forl
       (cons key val) <- (hash->list datum)
       (list key (pretty-datum val))))
    (_ datum)))

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
          arg <- (map (lambda (arg) (arg env)) dargs)
          (proc arg))))
(define (denote-quote _ tail)
  (match tail
    ((list single) (const (build-datum single)))
    (_ (error (format "invalid quote: ~a" `(quote . ,tail))))))
(define (denote-radd senv tail)
  (match tail
    ((list rec key val)
     (lets
       drec = (denote-with senv rec)
       dkey = (denote-with senv key)
       dval = (denote-with senv val)
       (lambda (env) (hash-set (drec env) (dkey env) (dval env)))))))
(define (denote-rremove senv tail)
  (match tail
    ((list rec key)
     (lets
       drec = (denote-with senv rec)
       dkey = (denote-with senv key)
       (lambda (env) (hash-remove (drec env) (dkey env)))))))
(define (denote-rget senv tail)
  (match tail
    ((list rec key)
     (lets
       drec = (denote-with senv rec)
       dkey = (denote-with senv key)
       (lambda (env) (hash-ref (drec env) (dkey env)))))))

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

(define senv-new (hash
                   'quote denote-quote
                   'lam denote-lam
                   'letr denote-letr
                   'record-add denote-radd
                   'record-remove denote-rremove
                   'record-get denote-rget
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
    '((tag pair)
      (payload ((head a)
                (tail ((tag pair)
                       (payload ((head b)
                                 (tail ((tag nil)
                                        (payload ())))))))))))
  (check-equal?
    (pretty-datum (denote-eval '((lam (x y) x) 5 (quote (a b c)))))
    5)
  (check-equal?
    (pretty-datum
      (denote-eval '((lam (rec val) (record-add rec 'result val)) () 5)))
    '((result 5)))
  (check-equal?
    (pretty-datum
      (denote-eval '((lam (rec val)
                      (record-remove (record-add rec 'result val) 'result))
                     () 5)))
    '())
  (check-equal?
    (pretty-datum
      (denote-eval '((lam (rec val)
                      (record-get (record-add rec 'result val) 'result))
                     () 5)))
    5)
  (check-equal?
    (pretty-datum
      (denote-eval
        '(letr
           ((tag-dispatch datum choices)
              ((record-get choices (record-get datum 'tag))
               (record-get datum 'payload)))
           ((even? xs)
              (tag-dispatch xs
                (record-add (record-add ()
                  'pair (lam (payload) (odd? (record-get payload 'tail))))
                  'nil (lam (_) #t))))
           ((odd? xs)
              (tag-dispatch xs
                (record-add (record-add ()
                  'pair (lam (payload) (even? (record-get payload 'tail))))
                  'nil (lam (_) #f))))
           (record-add (record-add ()
             'is-even (even? '(a b c)))
             'is-odd (odd? '(a b c)))
           )))
    '((is-even #f) (is-odd #t)))
  )
