#lang racket/base
(provide
  run/builtins
  )

(require
  "dict.rkt"
  "list.rkt"
  "maybe.rkt"
  "record.rkt"
  "sugar.rkt"
  racket/function
  racket/list
  racket/match
  )

(module+ test (require rackunit))

(records term
  (literal v)
  (pair l r)
  (pair-head p)
  (pair-tail p)
  (lam param body)
  (bvar name)
  (type t)
  (if-equal arg0 arg1 t f)
  (app proc arg))

(define env-empty hash-empty)
(define env-ref hash-ref)
(define env-get hash-get)
(define env-add hash-set)
(define env->list hash->list)
(define list->env make-immutable-hash)
(define (env-single k v) (env-add env-empty k v))
(define (env-merge env0 env1)
  (list->env (append* (map env->list (list env0 env1)))))
(define (env-lookup env ident)
  (match (env-get env ident)
    ((nothing) (error (format "undefined identifier: ~a" ident)))
    ((just val) val)))
(define (env-extend env params)
  (forf env = env
        param <- params
        (env-add env param #f)))

(define (denote term)
  (match term
    ((literal v) (lambda (_) v))
    ((pair l r) (lets dl = (denote l) dr = (denote r)
                      (lambda (env) (cons (dl env) (dr env)))))
    ((pair-head p) (lets dp = (denote p) (lambda (env) (car (dp env)))))
    ((pair-tail p) (lets dp = (denote p) (lambda (env) (cdr (dp env)))))
    ((lam param body)
     (lets dbody = (denote body)
           (lambda (env) (lambda (arg) (dbody (env-add env param arg))))))
    ((bvar name) (lambda (env) (env-ref env name)))
    ((type t)
     (lets dt = (denote t)
           (lambda (env) (match (dt env)
                           ((? symbol?) 'symbol)
                           ((? pair?) 'pair)
                           ('() 'nil)
                           ((? procedure?) 'procedure)
                           ((? boolean?) 'boolean)
                           ((? number?) 'number)
                           ((? char?) 'char)
                           ((? string?) 'string)
                           (_ #f)))))
    ((if-equal arg0 arg1 t f)
     (lets (list da0 da1 dt df) = (map denote (list arg0 arg1 t f))
           (lambda (env) (if (equal? (da0 env) (da1 env)) (dt env) (df env)))))
    ((app proc arg)
     (lets dproc = (denote proc) darg = (denote arg)
           (lambda (env) ((dproc env) (darg env)))))))

(define nil (literal '()))
(define (build-lambda params body)
  (forf body = body
        param <- (reverse params)
        (lam param body)))
(define (build-application proc args)
  (foldl (lambda (arg proc) (app proc arg)) proc args))

(define (env-reify env)
  (def (binding<? (cons s0 _) (cons s1 _)) (symbol<? s0 s1))
  (forf reified-env = nil
        (cons sym val) <- (sort (env->list env) binding<?)
        (pair (pair (literal sym) val) reified-env)))

(define (parse-identifier senv ident)
  (unless boolean? (env-lookup senv ident)
    (error (format "invalid use of special identifier")))
  (bvar ident))

(def (parse-quoted senv stx)
  (list senv renv term) =
  (let loop ((senv senv) (stx stx))
    (match stx
      ((? symbol?)
       (match (env-get senv stx)
         ((nothing) (list env-empty env-empty (literal stx)))
         ((just syntax-type)
          (list (env-single stx (literal syntax-type))
                (env-single stx (parse senv stx))
                (literal stx)))))
      ((cons head tail)
       (lets (list senv-h renv-h qhead) = (loop senv head)
             (list senv-t renv-t qtail) = (loop senv tail)
             (list (env-merge senv-h senv-t) (env-merge renv-h renv-t)
                   (pair qhead qtail))))
      (_ (list env-empty env-empty (literal stx)))))
  (list (pair (env-reify senv) (env-reify renv)) term))

(define (syntactic? senv stx) (and (symbol? stx) (env-lookup senv stx)))

(define (parse-application senv head tail)
  (build-application (parse senv head)
    (if (syntactic? senv head)
      (parse-quoted senv tail) (map (curry parse senv) tail))))

(define (parse senv stx)
  (match stx
    ((? symbol?)      (parse-identifier senv stx))
    ((cons head tail) (parse-application senv head tail))
    ('()              (literal (void)))
    (_                (literal stx))))

(define (parse-applicative senv stx)
  (match stx
    ((cons head tail)
     (match (if (symbol? head) (env-get senv head) (nothing))
       ((just (? procedure? special)) (special senv tail))
       (_ (build-application
            (parse-applicative senv head)
            (map (curry parse-applicative senv) tail)))))
    (_ (parse senv stx))))

(define (parse-special-quote senv tail)
  (match tail
    ('(()) nil)
    ((list (? symbol? sym)) (literal sym))
    (_ (error (format "invalid quote: ~a" `(quote . ,tail))))))
(define (parse-special-lambda senv tail)
  (match tail
    ((list (? non-empty-list? params) body)
     (build-lambda params (parse-applicative (env-extend senv params) body)))
    (_ (error (format "invalid lambda: ~a" `(lambda . ,tail))))))
(define (parse-special-pair senv tail)
  (match tail
    ((list l r) (apply pair (map (curry parse-applicative senv) tail)))
    (_ (error (format "invalid pair: ~a" `(pair . ,tail))))))
(define (parse-special-pair-head senv tail)
  (match tail
    ((list t) (pair-head (parse-applicative senv tail)))
    (_ (error (format "invalid pair-head: ~a" `(pair-head . ,tail))))))
(define (parse-special-pair-tail senv tail)
  (match tail
    ((list t) (pair-tail (parse-applicative senv tail)))
    (_ (error (format "invalid pair-tail: ~a" `(pair-tail . ,tail))))))
(define (parse-special-type senv tail)
  (match tail
    ((list t) (type (parse-applicative senv tail)))
    (_ (error (format "invalid type: ~a" `(type . ,tail))))))
(define (parse-special-if-equal senv tail)
  (match tail
    ((list a0 a1 t f)
     (apply if-equal (map (curry parse-applicative senv) tail)))
    (_ (error (format "invalid if-equal: ~a" `(if-equal . ,tail))))))
(define (parse-special-if senv tail)
  (match tail
    ((list cnd t f)
     (apply (lambda (cnd t f) (if-equal (literal #f) cnd f t))
            (map (curry parse-applicative senv) tail)))
    (_ (error (format "invalid if: ~a" `(if-equal . ,tail))))))

(define specials `(
  (quote ,parse-special-quote)
  (lambda ,parse-special-lambda)
  (pair ,parse-special-pair)
  (pair-head ,parse-special-pair-head)
  (pair-tail ,parse-special-pair-tail)
  (type ,parse-special-type)
  (if-equal ,parse-special-if-equal)
  (if ,parse-special-if)
  ))
(define senv-applicative-new (list->env (map (curry apply cons) specials)))

; TODO: should be able to embed this within the term language
(def ((eval-applicative env) tree)
  (cons senv-assoc renv-assoc) = env
  senv = (list->env (reverse senv-assoc))
  renv = (list->env (reverse renv-assoc))
  parsed = (parse senv tree)
  ((denote parsed) renv))

(define bootstrap/builtins
  (parse-applicative senv-applicative-new
    '(lambda (eval prog-stx)
       ((lambda (fix nil? cons head tail type env-add)
          ((lambda (foldr)
             ((lambda ($lambda/syntax-type)
                ((lambda ($lambda $lambda$ $if-equal)
                   (($lambda$ (cons '() '())
                      (cons
                        (cons '$lambda (cons '$lambda$ (cons '$if-equal '())))
                        (cons
                          (cons '$lambda
                                (cons
                                  (cons 'cons (cons 'head (cons 'tail
                                    (cons 'type (cons 'eval '())))))
                                  (cons prog-stx '())))
                          '())))
                    $lambda $lambda$ $if-equal
                    cons head tail type eval))
                 ($lambda/syntax-type #f)
                 ($lambda/syntax-type #t)
                 (lambda (env tree)
                   (if-equal (eval env (head tree))
                             (eval env (head (tail tree)))
                             (eval env (head (tail (tail tree))))
                             (eval env (head (tail (tail (tail tree)))))))))
              (lambda (syntax-type env tree)
                (((lambda (params body)
                    (foldr
                      (lambda (param body)
                        (lambda (env arg)
                          (body (env-add env param arg syntax-type))))
                      (lambda (env) (eval env body))
                      params))
                  (head tree)
                  (head (tail tree)))
                 env))))
           (fix (lambda (foldr f acc xs)
                  (if (nil? xs) acc
                    (f (head xs) (foldr f acc (tail xs))))))))
        (lambda (f) ((lambda (d) (d d))
                     (lambda (x) (f (lambda (a) ((x x) a))))))
        (lambda (v) (if-equal 'nil (type v) #t #f))
        (lambda (l r) (pair l r))
        (lambda (p) (pair-head p))
        (lambda (p) (pair-tail p))
        (lambda (v) (type v))
        (lambda (env key val syntax-type)
          (pair (pair (pair key syntax-type) (pair-head env))
                (pair (pair key val) (pair-tail env))))))))

; run a minikernel program, providing it access to the following builtins:
; operatives: $lambda, $lambda$, $if-equal
; applicatives: cons, head, tail, type, eval
(define run/builtins
  (((denote bootstrap/builtins) env-empty) eval-applicative))

(module+ test
  (check-equal?
    (run/builtins '(($lambda$ (f) ($lambda (g) (f (cons f g) 9)))
                    ($lambda (e t) (cons (cons (head e) (head (tail e))) t))
                    4))
    '((((g . #f) (f . #t) (cons . #f)) g . 4) (cons f g) 9))
  (check-equal?
    (run/builtins '(($lambda$ (f) ($lambda (g) ((($lambda (x) x) f) (cons f g) 9)))
                    ($lambda (e t) t)
                    4))
    9))
