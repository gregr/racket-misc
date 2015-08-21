#lang racket/base
; Inspired by John Shutt's Kernel Programming Language
; http://web.cs.wpi.edu/~jshutt/kernel.html
; Differences from the original Kernel include:
; - Applicative vs. Operative behavior can be statically specified per-binding.
;   Names bound by $lambda$ are considered operative.  Their appearance at the
;   head of what would normally be a procedure application causes the program
;   text of that application tree to be passed directly as an argument,
;   without the usual interpretation.  An environment is also built to be
;   passed alongside the tree.  Behavior from the original Kernel PL can be
;   recovered by always using $lambda$ instead of $lambda, and defining
;   applicatives in terms of a wrapper that explicitly evaluates the elements
;   of the application tree passed as an argument.
; - Environments passed to operatives are constrained to include only bindings
;   for symbols appearing in the application tree that is being passed to the
;   operative.  This reduces the risk of unintentional context capture.
; - Procedures are built with single-argument lambdas, with applications being
;   automatically curried.  Procedures applied operatively will receive the
;   entire application tree as a single argument.
; - A different set of primitives are built in due to simpler core evaluation
;   machinery.  Some former primitives can now be derived instead.
(provide
  run/builtins
  run/std
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
                           ((cons _ _) 'pair)
                           ('() 'nil)
                           ((? procedure?) 'procedure)
                           ((? boolean?) 'boolean)
                           ((? number?) 'number)
                           ((? char?) 'char)
                           ((? string?) 'string)
                           (_ #f)))))
    ((if-equal arg0 arg1 t f)
     (lets (list da0 da1 dt df) = (map denote (list arg0 arg1 t f))
           (lambda (env)
             (let ((v0 (da0 env)) (v1 (da1 env)))
               (if (match v0 ((cons _ _) #f) (_ (equal? v0 v1)))
                 (dt env) (df env))))))
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
  (unless (boolean? (env-lookup senv ident))
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
                              (cons 'cons (cons 'head (cons 'tail (cons 'type
                                (cons 'eval (cons 'env-add (cons 'null?
                                  (cons 'fix (cons 'foldr '())))))))))
                              (cons prog-stx '())))
                          '())))
                    $lambda $lambda$ $if-equal
                    cons head tail type eval env-add
                    nil? fix foldr))
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
; applicatives: cons, head, tail, type, eval, env-add, null?, fix
(define run/builtins
  (((denote bootstrap/builtins) env-empty) eval-applicative))

(module+ test
  (check-equal?
    (run/builtins
      '(($lambda$ (f) ($lambda (g) (f (cons f g) 9)))
        ($lambda (e t) (cons (cons (head e) (head (tail e))) t))
        4))
    '((((g . #f) (f . #t) (cons . #f)) g . 4) (cons f g) 9))
  (check-equal?
    (run/builtins
      '(($lambda$ (f) ($lambda (g) ((($lambda (x) x) f) (cons f g) 9)))
        ($lambda (e t) t)
        4))
    9))

; run a minikernel program, providing it a more complete standard library:
; operatives:
;   quote: named without a prefix-$ for convenience
;   $: treats its first argument like an operative
;   $if, $cond, $and?, $or?, $let, $let$, $let*, $letrec, $match
; applicatives:
;   type=?: determine whether a value has a particular type
;   not?, and?, or?, pair?, symbol?, eqv?, equal?,
;   fix*, apply, list, list*, assoc
;   foldl, foldr, filter, map, append, reverse
(define (run/std prog)
  (run/builtins
    `(($lambda$ (quote $ $if)
        (($lambda$ ($and? $or)
           ($lambda (type=? foldl map append first second)
             (($lambda (not? and? or? apply reverse filter)
               ($lambda$ (list)
                 (($lambda ($let/lambda fix*)
                    (($lambda$ ($let $let$)
  ($let$
    ((list* ($lambda (env tree)
              ($let ((rargs (reverse (map (eval env) tree))))
                    (foldl cons (head rargs) (tail rargs)))))
     ($let* ($lambda (env tree)
              ($let ((bindings (first tree))
                    (body (second tree)))
                    (eval
                      (foldl
                        ($lambda (binding env)
                          (env-add env (first binding)
                                   (eval env (second binding)) #f))
                        env bindings)
                      body))))
     ($cond (fix ($lambda ($cond env tree)
                   ($let ((cond0 (first (head tree)))
                          (body0 (second (head tree)))
                          (rest (tail tree)))
                         ($if (eval env cond0)
                           (eval env body0) ($cond env rest)))))))
    ($let$
      (($letrec ($lambda (env tree)
                  ($let*
                    ((defs (first tree))
                     (body (second tree))
                     (names (map ($lambda (def) (head (first def))) defs))
                     (procs-raw
                       (map ($lambda (def)
                              (apply $lambda
                                (list env
                                  (list (append names (tail (first def)))
                                        (second def)))))
                            defs))
                     (procs-final (fix* procs-raw)))
                    (apply
                      (apply $lambda (list env (list names body)))
                      procs-final)
                    ))))
      ($let*
        ((pair? ($lambda (v) (type=? 'pair v)))
         (symbol? ($lambda (v) (type=? 'symbol v)))
         (eqv? ($lambda (v0 v1) ($if-equal v0 v1 #t #f)))
         (equal?
           (fix ($lambda (equal? v0 v1)
             ($let ((t0 (type v0)) (t1 (type v1)))
               ($and? (eqv? t0 t1)
                      ($if (pair? v0)
                           ($and? (equal? (head v0) (head v1))
                                  (equal? (tail v0) (tail v1)))
                           (eqv? v0 v1)))))))
         (assoc
           (fix ($lambda (assoc key kvs)
                  ($if (pair? kvs)
                    ($if (equal? key (head (head kvs)))
                         (head kvs) (assoc key (tail kvs)))
                    kvs)))))
        ($let$
          (($match
             ($let*
               ((pattern-matcher
                  ($lambda (on-extract on-match on-pair? on-head on-tail)
                    ($letrec
                      (((singleton-list? xs) ($and? (pair? xs) (null? (tail xs))))
                       ((self pattern arg)
                        ($cond
                          ((symbol? pattern) (on-extract pattern arg))
                          ((pair? pattern)
                           ($let ((hd (head pattern)))
                                 ($cond
                                   ((equal? hd 'quote)
                                    ($and? (singleton-list? (tail pattern))
                                           (on-match (second pattern) arg)))
                                   ((equal? hd 'quasiquote)
                                    ($and? (singleton-list? (tail pattern))
                                           (on-quasiquote (second pattern) arg)))
                                   (#t #f))))
                          (#t (on-match pattern arg))))
                       ((on-quasiquote pattern arg)
                        ($if (pair? pattern)
                             ($if (equal? (head pattern) ,''unquote)
                               ($and? (singleton-list? (tail pattern))
                                      (self (second pattern) arg))
                               ($let* ((subs
                                         (list ($and? (on-pair? arg)
                                                      (on-quasiquote (head pattern) (on-head arg)))
                                               ($and? (on-pair? arg)
                                                      (on-quasiquote (tail pattern) (on-tail arg)))))
                                       (continue? (null? (filter not? subs))))
                                      ($and? continue? (foldr append '() subs))))
                             (on-match pattern arg))))
                      self)))
                (pattern->params
                  ($let ((self (pattern-matcher
                                 ($lambda (pattern _) (list pattern))
                                 ($lambda (_ _) '())
                                 ($lambda (_) #t) ($lambda (x) x) ($lambda (x) x))))
                        ($lambda (pattern) (self pattern #f))))
                (pattern-match (pattern-matcher
                                 ($lambda (_ arg) (list arg))
                                 ($lambda (pattern arg)
                                          ($and? (equal? pattern arg) '()))
                                 pair? head tail))
                (clause->lambda
                  ($lambda (env clause)
                    (apply $lambda (list env
                      (list (pattern->params (first clause))
                            (second clause))))))
                )
               ($lambda (env tree)
                 ($let* ((arg (eval env (first tree))) (clauses (tail tree))
                         (loop
                           (fix ($lambda (loop clauses)
                             ($and? (pair? clauses)
                               ($let ((extracted (pattern-match (first (head clauses)) arg))
                                      (cont (clause->lambda env (head clauses))))
                                 ($if extracted
                                   (apply cont extracted)
                                   (loop (tail clauses)))))))))
                        (loop clauses)))))
           )
          ,prog)))))
                   ; $let
                   ($let/lambda $lambda)
                   ; $let$
                   ($let/lambda $lambda$)))
                ; $let/lambda
                ($lambda (lambda env tree)
                  (($lambda (params args body)
                     (apply (lambda env (list params body))
                            (map (eval env) args)))
                   (map first (first tree))
                   (map second (first tree))
                   (second tree)))
                ; fix*: similar to http://okmij.org/ftp/Computation/fixed-point-combinators.html#Poly-variadic
                (fix ($lambda (self ps)
                       (map ($lambda (pi x) ((apply pi (self ps)) x)) ps))))))
            ; not?
            ($lambda (b) ($if b #f #t))
            ; and?
            ($lambda (a b) ($and? a b))
            ; or?
            ($lambda (a b) ($or? a b))
            ; apply
            ($lambda (f xs) (foldl ($lambda (arg f) (f arg)) f xs))
            ; reverse
            (foldl cons '())
            ; filter
            ($lambda (keep? xs)
              (foldr ($lambda (x ys) ($if (keep? x) (cons x ys) ys)) '() xs))
            ; list
            ($lambda (env tree) (map (eval env) tree)))))
         ; $and?
         ($lambda (env tree)
           ($if (eval env (head tree)) (eval env (head (tail tree))) #f))
         ; $or?
         ($lambda (env tree)
           ($if (eval env (head tree)) #t (eval env (head (tail tree)))))
         ; type=?
         ($lambda (type-tag val) ($if-equal type-tag (type val) #t #f))
         ; foldl
         (fix ($lambda (foldl f acc xs)
                ($if (null? xs) acc
                  (foldl f (f (head xs) acc) (tail xs)))))
         ; map
         ($lambda (f xs) (foldr ($lambda (x ys) (cons (f x) ys)) '() xs))
         ; append
         ($lambda (xs ys) (foldr cons ys xs))
         ; first
         head
         ; second
         ($lambda (xs) (head (tail xs)))))
      ; quote
      ($lambda (_ t) (head t))
      ; $
      ($lambda (env tree) ((eval env (head tree)) env (tail tree)))
      ; $if
      ($lambda (env tree)
        ($if-equal #f (eval env (head tree))
                   (eval env (head (tail (tail tree))))
                   (eval env (head (tail tree))))))))

(module+ test
  (check-equal? (run/std ''()) '())
  (check-equal? (run/std '($if (type=? 'nil '()) 'yes 'no)) 'yes)
  (check-equal?
    (run/std '(apply ($lambda (a b c) (list a c b)) (list 1 2 3)))
    '(1 3 2))
  (check-equal?
    (run/std
      '(((($lambda (x) x) $lambda)
         ($ ($lambda (env _) env) (list))
         (list (list 'a 'b 'c) (list 'list 'c 'b 'a)))
        9 8 7))
    '(7 8 9))
  (check-equal? (run/std '($let* ((a 5) (b (list a 7))) b)) '(5 7))
  (check-equal? (run/std '(list* 1 2 (list 3 4))) '(1 2 3 4))
  (check-equal?
    (run/std
      '($cond
         (#f 'wrong)
         ((not? #t) 'wrong)
         ((null? '()) 'ok)
         (#t 'wrong)))
    'ok)
  (check-equal?
    (run/std
      '($let ((input (list (list '() 0) (list 1 1) (list '() 2) (list 3 3))))
         (append
           (filter ($lambda (p) (null? (first p))) input)
           (filter ($lambda (p) (not? (null? (first p)))) input))))
    '((() 0)  (() 2)  (1 1)  (3 3)))
  (check-equal?
    (run/std
      '((first (fix* (list
                       ($lambda (even-length? odd-length? xs)
                                ($if (null? xs) #t (odd-length? (tail xs))))
                       ($lambda (even-length? odd-length? xs)
                                ($if (null? xs) #f (even-length? (tail xs)))))))
        (list 1 2 3 4)))
    #t)
  (check-equal?
    (run/std
      '($letrec (((even-length? xs)
                  ($if (null? xs) #t (odd-length? (tail xs))))
                 ((odd-length? xs)
                  ($if (null? xs) #f (even-length? (tail xs)))))
         (list
           (even-length? (list 1 2 3 4 5))
           (even-length? (list 1 2 3 4 5 6 7 8)))))
    '(#f #t))
  (check-equal?
    (run/std
      '(assoc 'needle
        '(((a b) . 0) (c . 1) (2 . 2) (() . 3) (#t . 4) (#f . 5)
          (needle . found) (missed . 6))))
    '(needle . found))
  (check-equal?
    (run/std
      '(assoc '(burried needle)
        '(((a b) . 0) (c . 1) (2 . 2) (() . 3) (#t . 4) (#f . 5)
          ((burried needle) . found) (missed . 6))))
    '((burried needle) . found))
  (check-equal?
    (run/std '($match 3 (4 'no) (3 'yes) (2 'no)))
    'yes)
  (check-equal?
    (run/std
      '($match (list (list 0 1) 2 (cons 3 4))
         (`(a b) 'no)
         (`((0 ,a) 2 (,b . 4)) (list a b))
         (2 'no)))
    '(1 3))
  )
