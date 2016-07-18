#lang racket/base
(require
  "okanren.rkt"
  "sugar.rkt"
  (except-in racket/match ==)
  )
(module+ test
  (require
    racket/set
    rackunit
    )

  (define-syntax mk-test-cont
    (syntax-rules ()
      ((_ test-name exact? query expected)
       (let* ((result-set (list->set query))
              (expected-set (list->set expected))
              (overlap (set-intersect result-set expected-set)))
         (if exact?
           (begin
             (when (not (equal? result-set expected-set))
               (displayln (format "failed test: ~a" test-name)))
             ;(check-equal? (set-subtract expected-set result-set) (set))
             ;(check-equal? (set-subtract result-set expected-set) (set))
             (check-equal? result-set expected-set))
           (check-equal? overlap expected-set))))))
  (define-syntax mk-test
    (syntax-rules ()
      ((_ test-name query expected)
        (mk-test-cont test-name #t query expected))))
  (define-syntax mk-test-subsumed
    (syntax-rules ()
      ((_ test-name query expected)
        (mk-test-cont test-name #f query expected))))
  (define-syntax mk-test-time
    (syntax-rules ()
      ((_ test-name query expected)
        (begin
          (displayln test-name)
          (time (mk-test-cont test-name #t query expected))))))
  )

;; interpreter
(define (evalo expr val)
  (eval-expo expr initial-env val))

(define (eval-expo expr env val)
  (try-lookup-before expr env val (eval-expo-rest expr env val)))

(kanren
  (define (eval-expo-rest expr env val)
    (conde
      ((numbero expr) (== expr val))

      ((fresh (rator x* rands a* prim-id)
         (== `(,rator . ,rands) expr)
         (eval-expo rator env `(prim . ,prim-id))
         (eval-primo prim-id a* val)
         (eval-listo rands env a*)))

      ((fresh (rator x* rands body env^ a* res)
         (== `(,rator . ,rands) expr)
         ;; Multi-argument
         (eval-expo rator env `(closure (lambda ,x* ,body) ,env^))
         (ext-env*o x* a* env^ res)
         (eval-application rands env a* (eval-expo body res val))))

      ((fresh (rator x rands body env^ a* res)
         (== `(,rator . ,rands) expr)
         ;; variadic
         (symbolo x)
         (== `((,x . (val . ,a*)) . ,env^) res)
         (eval-expo rator env `(closure (lambda ,x ,body) ,env^))
         (eval-expo body res val)
         (eval-listo rands env a*)))

      ((== `(quote ,val) expr)
       (absento 'closure val)
       (absento 'prim val)
       (not-in-envo 'quote env))

      ((fresh (x body)
         (== `(lambda ,x ,body) expr)
         (== `(closure (lambda ,x ,body) ,env) val)
         (conde
           ;; Variadic
           ((symbolo x))
           ;; Multi-argument
           ((list-of-symbolso x)))
         (not-in-envo 'lambda env)))

      ;; WEB 25 May 2016 -- This rather budget version of 'begin' is
      ;; useful for separating 'define' from the expression 'e',
      ;; specifically for purposes of Barliman.
      ((fresh (defn args name body e)
         (== `(begin ,defn ,e) expr)
         (== `(define ,name (lambda ,args ,body)) defn)
         (eval-expo `(letrec ((,name (lambda ,args ,body))) ,e) env val)))

      ((handle-matcho expr env val))

      ((fresh (p-name x body letrec-body)
         ;; single-function variadic letrec version
         (== `(letrec ((,p-name (lambda ,x ,body)))
                ,letrec-body)
             expr)
         (conde
           ; Variadic
           ((symbolo x))
           ; Multiple argument
           ((list-of-symbolso x)))
         (not-in-envo 'letrec env)
         (eval-expo letrec-body
                    `((,p-name . (rec . (lambda ,x ,body))) . ,env)
                    val)))

      ((prim-expo expr env val))))

  (define (lookupo x env t)
    (fresh (y b rest)
      (== `((,y . ,b) . ,rest) env)
      (conde
        ((== x y)
         (conde
           ((== `(val . ,t) b))
           ((fresh (lam-expr)
              (== `(rec . ,lam-expr) b)
              (== `(closure ,lam-expr ,env) t)))))
        ((=/= x y)
         (lookupo x rest t))))))

(define empty-env '())

(define (state-walk st term)
  (let-values (((bs term) (walk (state-bindings st) term)))
    (values (state-bindings-set st bs) term)))

(define (list-split-ground st xs)
  (letn loop (values st rprefix xs) = (values st '() xs)
    (values st xs) = (state-walk st xs)
    (match xs
      ((cons item xs) (loop st (cons item rprefix) xs))
      (_ (values st rprefix xs)))))

(def ((try-lookup-before x env t alts) st)
  (values st rgenv venv) = (list-split-ground st env)
  ;_ = (when (< 18 (length rgenv)) (newline) (displayln `(lookup prefix ,rgenv)))
  (values st env) = (state-walk st env)
  goal =
  (forf alts = (conde ((symbolo x) (lookupo x venv t))
                      (alts))
        `(,y . ,b) <- rgenv
        (conde
          ((symbolo x) (== x y)
           (conde
             ((== `(val . ,t) b))
             ((fresh (lam-expr)
                     (== `(rec . ,lam-expr) b)
                     (== `(closure ,lam-expr ,env) t)))))
          ((=/= x y) alts)))
  (goal st))

(kanren
  (define (not-in-envo x env)
    (conde
      ((== empty-env env))
      ((fresh (y b rest)
              (== `((,y . ,b) . ,rest) env)
              (=/= y x)
              (not-in-envo x rest)))))
  (define (eval-listo expr env val)
    (conde
      ((== '() expr)
       (== '() val))
      ((fresh (a d v-a v-d)
              (== `(,a . ,d) expr)
              (== `(,v-a . ,v-d) val)
              (eval-expo a env v-a)
              (eval-listo d env v-d))))))

(def ((eval-application rands aenv a* body-goal) st)
  (values st rrands rands-suffix) = (list-split-ground st rands)
  (values st ggoals vgoals args-suffix) =
  (forf st = st
        ggoals = unit
        vgoals = unit
        args = a*
        rand <- (reverse rrands)
        (values st rand) = (state-walk st rand)
        (let* ((args-rest (var (gensym 'args-rest)))
               (goal (fresh (arg)
                       (== `(,arg . ,args-rest) args)
                       (eval-expo rand aenv arg))))
          (if (var? rand)
            (values st ggoals (conj vgoals goal) args-rest)
            (values st (conj ggoals goal) vgoals args-rest))))
  (values st a*) = (state-walk st a*)
  goal = (conj* ggoals    ; try ground argument goals first
                body-goal ; then try the body
                vgoals    ; then fill in the unbound arguments
                ; any unbound final segment of arguments
                (eval-listo rands-suffix aenv args-suffix))
  (goal st))

(kanren
  ;; need to make sure lambdas are well formed.
  ;; grammar constraints would be useful here!!!
  (define (list-of-symbolso los)
    (conde
      ((== '() los))
      ((fresh (a d)
         (== `(,a . ,d) los)
         (symbolo a)
         (list-of-symbolso d)))))

  (define (ext-env*o x* a* env out)
    (conde
      ((== '() x*) (== '() a*) (== env out))
      ((fresh (x a dx* da* env2)
         (== `(,x . ,dx*) x*)
         (== `(,a . ,da*) a*)
         (== `((,x . (val . ,a)) . ,env) env2)
         (symbolo x)
         (ext-env*o dx* da* env2 out))))))

(define (eval-primo prim-id a* val)
  (conde
    [(== prim-id 'car)
     (fresh (d)
       (== `((,val . ,d)) a*)
       (=/= 'closure val))]
    [(== prim-id 'cdr)
     (fresh (a)
       (== `((,a . ,val)) a*)
       (=/= 'closure a))]
    [(== prim-id 'not)
     (fresh (b)
       (== `(,b) a*)
       (conde
         ((=/= #f b) (== #f val))
         ((== #f b) (== #t val))))]
    [(== prim-id 'equal?)
     (fresh (v1 v2)
       (== `(,v1 ,v2) a*)
       (conde
         ((== v1 v2) (== #t val))
         ((=/= v1 v2) (== #f val))))]
    [(== prim-id 'symbol?)
     (fresh (v)
       (== `(,v) a*)
       (conde
         ((symbolo v) (== #t val))
         ((numbero v) (== #f val))
         ((fresh (a d)
            (== `(,a . ,d) v)
            (== #f val)))))]
    [(== prim-id 'null?)
     (fresh (v)
       (== `(,v) a*)
       (conde
         ((== '() v) (== #t val))
         ((=/= '() v) (== #f val))))]
    [(== prim-id 'cons)
     (fresh (a d)
       (== `(,a ,d) a*)
       (== `(,a . ,d) val))]
    ))

(define (prim-expo expr env val)
  (conde
    ((boolean-primo expr env val))
    ((and-primo expr env val))
    ((or-primo expr env val))
    ((if-primo expr env val))))

(define (boolean-primo expr env val)
  (conde
    ((== #t expr) (== #t val))
    ((== #f expr) (== #f val))))

(define (and-primo expr env val)
  (fresh (e*)
    (== `(and . ,e*) expr)
    (not-in-envo 'and env)
    (ando e* env val)))

(define (or-primo expr env val)
  (fresh (e*)
    (== `(or . ,e*) expr)
    (not-in-envo 'or env)
    (oro e* env val)))

(kanren
  (define (ando e* env val)
    (conde
      ((== '() e*) (== #t val))
      ((fresh (e)
         (== `(,e) e*)
         (eval-expo e env val)))
      ((fresh (e1 e2 e-rest v)
         (== `(,e1 ,e2 . ,e-rest) e*)
         (conde
           ((== #f v)
            (== #f val)
            (eval-expo e1 env v))
           ((=/= #f v)
            (eval-expo e1 env v)
            (ando `(,e2 . ,e-rest) env val)))))))

  (define (oro e* env val)
    (conde
      ((== '() e*) (== #f val))
      ((fresh (e)
         (== `(,e) e*)
         (eval-expo e env val)))
      ((fresh (e1 e2 e-rest v)
         (== `(,e1 ,e2 . ,e-rest) e*)
         (conde
           ((=/= #f v)
            (== v val)
            (eval-expo e1 env v))
           ((== #f v)
            (eval-expo e1 env v)
            (oro `(,e2 . ,e-rest) env val))))))))

(define (if-primo expr env val)
  (fresh (e1 e2 e3 t)
    (== `(if ,e1 ,e2 ,e3) expr)
    (not-in-envo 'if env)
    (eval-expo e1 env t)
    (conde
      ((=/= #f t) (eval-expo e2 env val))
      ((== #f t) (eval-expo e3 env val)))))

(define initial-env `((car . (val . (prim . car)))
                      (cdr . (val . (prim . cdr)))
                      (null? . (val . (prim . null?)))
                      (symbol? . (val . (prim . symbol?)))
                      (cons . (val . (prim . cons)))
                      (not . (val . (prim . not)))
                      (equal? . (val . (prim . equal?)))
                      (list . (val . (closure (lambda x x) ,empty-env)))
                      . ,empty-env))

(define handle-matcho
  (lambda  (expr env val)
    (fresh (against-expr mval clause clauses)
      (== `(match ,against-expr ,clause . ,clauses) expr)
      (not-in-envo 'match env)
      (eval-expo against-expr env mval)
      (match-clauses mval `(,clause . ,clauses) env val))))

(define (not-symbolo t)
  (conde
    ((== #f t))
    ((== #t t))
    ((== '() t))
    ((numbero t))
    ((fresh (a d)
       (== `(,a . ,d) t)))))

(define (not-numbero t)
  (conde
    ((== #f t))
    ((== #t t))
    ((== '() t))
    ((symbolo t))
    ((fresh (a d)
       (== `(,a . ,d) t)))))

(define (self-eval-literalo t)
  (conde
    ((numbero t))
    ((booleano t))))

(define (literalo t)
  (conde
    ((numbero t))
    ((symbolo t) (=/= 'closure t))
    ((booleano t))
    ((== '() t))))

(define (booleano t)
  (conde
    ((== #f t))
    ((== #t t))))

(kanren
  (define (regular-env-appendo env1 env2 env-out)
    (conde
      ((== empty-env env1) (== env2 env-out))
      ((fresh (y v rest res)
         (== `((,y . (val . ,v)) . ,rest) env1)
         (== `((,y . (val . ,v)) . ,res) env-out)
         (regular-env-appendo rest env2 res)))))

  (define (match-clauses mval clauses env val)
    (fresh (p result-expr d penv)
      (== `((,p ,result-expr) . ,d) clauses)
      (conde
        ((fresh (env^)
           (p-match p mval '() penv)
           (regular-env-appendo penv env env^)
           (eval-expo result-expr env^ val)))
        ((p-no-match p mval '() penv)
         (match-clauses mval d env val))))))

(define (var-p-match var mval penv penv-out)
  (fresh (val)
    (symbolo var)
    (=/= 'closure mval)
    (conde
      ((== mval val)
       (== penv penv-out)
       (lookupo var penv val))
      ((== `((,var . (val . ,mval)) . ,penv) penv-out)
       (not-in-envo var penv)))))

(define (var-p-no-match var mval penv penv-out)
  (fresh (val)
    (symbolo var)
    (=/= mval val)
    (== penv penv-out)
    (lookupo var penv val)))

(define (p-match p mval penv penv-out)
  (conde
    ((self-eval-literalo p)
     (== p mval)
     (== penv penv-out))
    ((var-p-match p mval penv penv-out))
    ((fresh (var pred val)
      (== `(? ,pred ,var) p)
      (conde
        ((== 'symbol? pred)
         (symbolo mval))
        ((== 'number? pred)
         (numbero mval)))
      (var-p-match var mval penv penv-out)))
    ((fresh (quasi-p)
      (== (list 'quasiquote quasi-p) p)
      (quasi-p-match quasi-p mval penv penv-out)))))

(define (p-no-match p mval penv penv-out)
  (conde
    ((self-eval-literalo p)
     (=/= p mval)
     (== penv penv-out))
    ((var-p-no-match p mval penv penv-out))
    ((fresh (var pred val)
       (== `(? ,pred ,var) p)
       (== penv penv-out)
       (symbolo var)
       (conde
         ((== 'symbol? pred)
          (conde
            ((not-symbolo mval))
            ((symbolo mval)
             (var-p-no-match var mval penv penv-out))))
         ((== 'number? pred)
          (conde
            ((not-numbero mval))
            ((numbero mval)
             (var-p-no-match var mval penv penv-out)))))))
    ((fresh (quasi-p)
      (== (list 'quasiquote quasi-p) p)
      (quasi-p-no-match quasi-p mval penv penv-out)))))

(kanren
  (define (quasi-p-match quasi-p mval penv penv-out)
    (conde
      ((== quasi-p mval)
       (== penv penv-out)
       (literalo quasi-p))
      ((fresh (p)
         (== (list 'unquote p) quasi-p)
         (p-match p mval penv penv-out)))
      ((fresh (a d v1 v2 penv^)
         (== `(,a . ,d) quasi-p)
         (== `(,v1 . ,v2) mval)
         (=/= 'unquote a)
         (quasi-p-match a v1 penv penv^)
         (quasi-p-match d v2 penv^ penv-out)))))

  (define (quasi-p-no-match quasi-p mval penv penv-out)
    (conde
      ((=/= quasi-p mval)
       (== penv penv-out)
       (literalo quasi-p))
      ((fresh (p)
         (== (list 'unquote p) quasi-p)
         (=/= 'closure mval)
         (p-no-match p mval penv penv-out)))
      ((fresh (a d)
         (== `(,a . ,d) quasi-p)
         (=/= 'unquote a)
         (== penv penv-out)
         (literalo mval)))
      ((fresh (a d v1 v2 penv^)
         (== `(,a . ,d) quasi-p)
         (=/= 'unquote a)
         (== `(,v1 . ,v2) mval)
         (conde
           ((quasi-p-no-match a v1 penv penv^))
           ((quasi-p-match a v1 penv penv^)
            (quasi-p-no-match d v2 penv^ penv-out))))))))

(module+ test
  (mk-test "number"
    (run* (q) (evalo '6 q))
    '(((6))))

  (mk-test "quote"
    (run* (q) (evalo '(quote foo) q))
    '(((foo))))

  (mk-test "and"
    (run* (q) (evalo '(and 9) q))
    '(((9))))

  (mk-test "append empty lists"
    (run* (q)
      (evalo
        `(begin
           (define append
             (lambda (l s)
               (if (null? l)
                 s
                 (cons (car l)
                       (append (cdr l) s)))))
           (append '() '()))
        '()))
    '(((_.0))))

  (mk-test "append all argument pairs"
    (run* (l1 l2)
      (evalo `(letrec ((append (lambda (l s)
                                 (if (null? l)
                                   s
                                   (cons (car l)
                                         (append (cdr l) s))))))
                (append ',l1 ',l2))
             '(1 2 3 4 5)))
    '(((() (1 2 3 4 5)))
      (((1) (2 3 4 5)))
      (((1 2) (3 4 5)))
      (((1 2 3) (4 5)))
      (((1 2 3 4) (5)))
      (((1 2 3 4 5) ()))))

  (mk-test "append cons-first-arg"
    (run 1 (q)
      (evalo `(letrec ((append (lambda (l s)
                                 (if (null? l)
                                   s
                                   (cons ,q
                                         (append (cdr l) s))))))
                (append '(1 2 3) '(4 5)))
             '(1 2 3 4 5)))
    '((((car l)))))

  (mk-test "append cdr-arg"
    (run 1 (q)
      (evalo `(letrec ((append (lambda (l s)
                                     (if (null? l)
                                         s
                                         (cons (car l)
                                               (append (cdr ,q) s))))))
                    (append '(1 2 3) '(4 5)))
                 '(1 2 3 4 5)))
    '(((l))))

  (mk-test-time "append cdr-prim"
    (run 1 (q)
      (evalo `(letrec ((append (lambda (l s)
                                 (if (null? l)
                                   s
                                   (cons (car l)
                                         (append (,q l) s))))))
                    (append '(1 2 3) '(4 5)))
                 '(1 2 3 4 5)))
    '(((cdr))))

  (mk-test-time "append cdr-both"
    (run 1 (q r)
      (evalo `(letrec ((append (lambda (l s)
                                     (if (null? l)
                                         s
                                         (cons (car l)
                                               (append (,q ,r) s))))))
                    (append '(1 2 3) '(4 5)))
                 '(1 2 3 4 5)))
    '(((cdr l))))

  (mk-test-time "append cdr-entire"
    (run 1 (q)
      (evalo `(letrec ((append (lambda (l s)
                                     (if (null? l)
                                         s
                                         (cons (car l)
                                               (append ,q s))))))
                    (append '(1 2 3) '(4 5)))
                 '(1 2 3 4 5))
      )
    '((((cdr l)))))

  (mk-test-time "append both recursive args"
    (run 1 (q r)
      (evalo `(letrec ((append (lambda (l s)
                                     (if (null? l)
                                         s
                                         (cons (car l)
                                               (append ,q ,r))))))
                    (list
                      (append '(foo) '(bar))
                      (append '(1 2 3) '(4 5)))
                    )
                 (list '(foo bar) '(1 2 3 4 5)))
      )
    '((((cdr l) s))))

  (mk-test-time "append recursive var-args"
    (run 1 (q)
      (evalo `(letrec ((append (lambda (l s)
                                     (if (null? l)
                                         s
                                         (cons (car l)
                                               (append . ,q))))))
                    (list
                      (append '(foo) '(bar))
                      (append '(1 2 3) '(4 5)))
                    )
                 (list '(foo bar) '(1 2 3 4 5)))
      )
    '(((((cdr l) s)))))

  (mk-test-time "append cons-first-arg recursive var-args"
    (run 1 (q r)
      (evalo `(letrec ((append (lambda (l s)
                                     (if (null? l)
                                         s
                                         (cons ,q
                                               (append . ,r))))))
                    (list
                      (append '() '())
                      (append '(foo) '(bar))
                      (append '(1 2 3) '(4 5)))
                    )
                 (list '() '(foo bar) '(1 2 3 4 5)))
      )
    '((((car l) ((cdr l) s)))))

  ; runs out of memory
  ;(mk-test-time "append recursive-entire"
    ;(run 1 (q)
      ;(evalo `(letrec ((append (lambda (l s)
                                     ;(if (null? l)
                                         ;s
                                         ;(cons (car l)
                                               ;,q)))))
                    ;(list
                      ;(append '() '())
                      ;(append '(foo) '(bar))
                      ;(append '(1 2 3) '(4 5)))
                    ;)
                 ;(list '() '(foo bar) '(1 2 3 4 5)))
      ;)
    ;'(((((append (cdr l) s))))))

  ;(mk-test-time "append cons-both-args"
    ;(run 1 (q r)
      ;(evalo `(letrec ((append (lambda (l s)
                                     ;(if (null? l)
                                         ;s
                                         ;(cons ,q
                                               ;,r)))))
                    ;(list
                      ;(append '() '())
                      ;(append '(foo) '(bar))
                      ;(append '(1 2 3) '(4 5)))
                    ;)
                 ;(list '() '(foo bar) '(1 2 3 4 5)))
      ;)
    ;'((((car l) (append (cdr l) s)))))

  ;(mk-test-time "append cons-entire"
    ;(run 1 (q)
      ;(evalo `(letrec ((append (lambda (l s)
                                     ;(if (null? l)
                                         ;s
                                         ;,q))))
                    ;(list
                      ;(append '() '())
                      ;(append '(foo) '(bar))
                      ;(append '(1 2 3) '(4 5)))
                    ;)
                 ;(list '() '(foo bar) '(1 2 3 4 5)))
      ;)
    ;'((cons (car l)  (append (cdr l) s))))

  ;(mk-test-time "append if-both-branches"
    ;(run 1 (q r)
      ;(evalo `(letrec ((append (lambda (l s)
                                     ;(if (null? l)
                                         ;,q
                                         ;,r))))
                    ;(list
                      ;(append '() '())
                      ;(append '(foo) '(bar))
                      ;(append '(1 2 3) '(4 5)))
                    ;)
                 ;(list '() '(foo bar) '(1 2 3 4 5)))
      ;)
    ;'((s (cons (car l) (append (cdr l) s)))))

  ; this starts producing nonsense results that game the test examples
  ; example of its "cleverness":
  ; (s (match s ((quasiquote ()) s)
  ;             ((quasiquote (bar)) (quote (foo bar)))
  ;             (_.0 (quote (1 2 3 4 5))) . _.1) _.2)
  ;(mk-test-time "append if-all-subforms"
    ;(run 1 (q r s)
      ;(evalo `(letrec ((append (lambda (l s)
                                     ;(if ,q ,r ,s))))
                    ;(list
                      ;(append '() '())
                      ;(append '(foo) '(bar))
                      ;(append '(1 2 3) '(4 5)))
                    ;)
                 ;(list '() '(foo bar) '(1 2 3 4 5)))
      ;)
    ;'())

  (define quinec
  '((lambda (_.0)
      (list _.0 (list (quote quote) _.0)))
    (quote
      (lambda (_.0)
        (list _.0 (list (quote quote) _.0))))))

  ;(mk-test-time "quine"
    ;(run 4 (q) (evalo q q))
    ;'())
  )
