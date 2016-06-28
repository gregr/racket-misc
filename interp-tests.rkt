#lang racket/base

(require
  "dakanren.rkt"
  "microkanren.rkt"
  "minikanren.rkt"
  "sugar.rkt"
  (except-in racket/match ==)
  )

(module+ test
  (require rackunit))

;; interpreter
(define (evalo expr val)
  (eval-expo expr initial-env val))

(define (eval-expo expr env val)
  (try-lookup-before expr env val (eval-expo-rest expr env val)))

(define (eval-expo-rest expr env val)
  (conde
    ((numbero expr) (== expr val))

    ((exist (rator x* rands a* prim-id)
       (== `(,rator . ,rands) expr)
       (eval-expo rator env `(prim . ,prim-id))
       (eval-primo prim-id a* val)
       (eval-listo rands env a*)))

    ((exist (rator x* rands body env^ a* res)
       (== `(,rator . ,rands) expr)
       ;; Multi-argument
       (eval-expo rator env `(closure (lambda ,x* ,body) ,env^))
       (ext-env*o x* a* env^ res)
       (eval-expo body res val)
       (eval-listo rands env a*)
       ))

    ((exist (rator x rands body env^ a* res)
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

    ((exist (x body)
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
    ((exist (defn args name body e)
       (== `(begin ,defn ,e) expr)
       (== `(define ,name (lambda ,args ,body)) defn)
       (eval-expo `(letrec ((,name (lambda ,args ,body))) ,e) env val)))

    ((handle-matcho expr env val))

    ((exist (p-name x body letrec-body)
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

(define empty-env '())

(define (lookupo x env t)
  (exist (y b rest)
    (== `((,y . ,b) . ,rest) env)
    (conde
      ((== x y)
       (conde
         ((== `(val . ,t) b))
         ((exist (lam-expr)
            (== `(rec . ,lam-expr) b)
            (== `(closure ,lam-expr ,env) t)))))
      ((=/= x y)
       (lookupo x rest t)))))

(define (list-split-ground st xs)
  (letn loop (values st rprefix xs) = (values st '() xs)
    (values st xs) = (muk-walk st xs)
    (match xs
      ((cons item xs) (loop st (cons item rprefix) xs))
      (_ (values st rprefix xs)))))

(def ((try-lookup-before x env t alts) st)
  (values st rgenv venv) = (list-split-ground st env)
  ;_ = (when (< 18 (length rgenv)) (newline) (displayln `(lookup prefix ,rgenv)))
  (values st env) = (muk-walk st env)
  goal =
  (forf alts = (conde$ ((symbolo x) (lookupo x venv t))
                       (alts))
        `(,y . ,b) <- rgenv
        (conde$
          ((symbolo x) (== x y)
           (conde$
             ((== `(val . ,t) b))
             ((exist (lam-expr)
                     (== `(rec . ,lam-expr) b)
                     (== `(closure ,lam-expr ,env) t)))))
          ((=/= x y) alts)))
  (muk-goal st goal))

(define (not-in-envo x env)
  (conde
    ((== empty-env env))
    ((exist (y b rest)
       (== `((,y . ,b) . ,rest) env)
       (=/= y x)
       (not-in-envo x rest)))))

(define (eval-listo expr env val)
  (conde
    ((== '() expr)
     (== '() val))
    ((exist (a d v-a v-d)
            (== `(,a . ,d) expr)
            (== `(,v-a . ,v-d) val)
            (eval-expo a env v-a)
            (eval-listo d env v-d)))))

; this specialization was unnecessary
;(def ((eval-listo expr env val) st)
  ;(values st goal) =
  ;(letn loop (values st expr val) = (values st expr val)
    ;(values st expr) = (muk-walk st expr)
    ;(match expr
      ;('() (values st (== '() val)))
      ;((cons a d)
       ;(let/vars (v-d)
         ;(lets (values st goal) = (loop st d v-d)
               ;(values st (exist (v-a)
                            ;(== `(,v-a . ,v-d) val)
                            ;(eval-expo a env v-a)
                            ;goal)))))
      ;(_ (values st (conde
           ;((== '() expr)
            ;(== '() val))
           ;((exist (a d v-a v-d)
              ;(== `(,a . ,d) expr)
              ;(== `(,v-a . ,v-d) val)
              ;(eval-expo a env v-a)
              ;(eval-listo d env v-d))))))))
  ;(muk-goal st goal))

;; need to make sure lambdas are well formed.
;; grammar constraints would be useful here!!!
(define (list-of-symbolso los)
  (conde
    ((== '() los))
    ((exist (a d)
       (== `(,a . ,d) los)
       (symbolo a)
       (list-of-symbolso d)))))

(define (ext-env*o x* a* env out)
  (conde
    ((== '() x*) (== '() a*) (== env out))
    ((exist (x a dx* da* env2)
       (== `(,x . ,dx*) x*)
       (== `(,a . ,da*) a*)
       (== `((,x . (val . ,a)) . ,env) env2)
       (symbolo x)
       (ext-env*o dx* da* env2 out)))))

(define (eval-primo prim-id a* val)
  (conde
    [(== prim-id 'car)
     (exist (d)
       (== `((,val . ,d)) a*)
       (=/= 'closure val))]
    [(== prim-id 'cdr)
     (exist (a)
       (== `((,a . ,val)) a*)
       (=/= 'closure a))]
    [(== prim-id 'not)
     (exist (b)
       (== `(,b) a*)
       (conde
         ((=/= #f b) (== #f val))
         ((== #f b) (== #t val))))]
    [(== prim-id 'equal?)
     (exist (v1 v2)
       (== `(,v1 ,v2) a*)
       (conde
         ((== v1 v2) (== #t val))
         ((=/= v1 v2) (== #f val))))]
    [(== prim-id 'symbol?)
     (exist (v)
       (== `(,v) a*)
       (conde
         ((symbolo v) (== #t val))
         ((numbero v) (== #f val))
         ((exist (a d)
            (== `(,a . ,d) v)
            (== #f val)))))]
    [(== prim-id 'null?)
     (exist (v)
       (== `(,v) a*)
       (conde
         ((== '() v) (== #t val))
         ((=/= '() v) (== #f val))))]
    [(== prim-id 'cons)
     (exist (a d)
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
  (exist (e*)
    (== `(and . ,e*) expr)
    (not-in-envo 'and env)
    (ando e* env val)))

(define (ando e* env val)
  (conde
    ((== '() e*) (== #t val))
    ((exist (e)
       (== `(,e) e*)
       (eval-expo e env val)))
    ((exist (e1 e2 e-rest v)
       (== `(,e1 ,e2 . ,e-rest) e*)
       (conde
         ((== #f v)
          (== #f val)
          (eval-expo e1 env v))
         ((=/= #f v)
          (eval-expo e1 env v)
          (ando `(,e2 . ,e-rest) env val)))))))

(define (or-primo expr env val)
  (exist (e*)
    (== `(or . ,e*) expr)
    (not-in-envo 'or env)
    (oro e* env val)))

(define (oro e* env val)
  (conde
    ((== '() e*) (== #f val))
    ((exist (e)
       (== `(,e) e*)
       (eval-expo e env val)))
    ((exist (e1 e2 e-rest v)
       (== `(,e1 ,e2 . ,e-rest) e*)
       (conde
         ((=/= #f v)
          (== v val)
          (eval-expo e1 env v))
         ((== #f v)
          (eval-expo e1 env v)
          (oro `(,e2 . ,e-rest) env val)))))))

(define (if-primo expr env val)
  (exist (e1 e2 e3 t)
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
    (exist (against-expr mval clause clauses)
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
    ((exist (a d)
       (== `(,a . ,d) t)))))

(define (not-numbero t)
  (conde
    ((== #f t))
    ((== #t t))
    ((== '() t))
    ((symbolo t))
    ((exist (a d)
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

(define (regular-env-appendo env1 env2 env-out)
  (conde
    ((== empty-env env1) (== env2 env-out))
    ((exist (y v rest res)
       (== `((,y . (val . ,v)) . ,rest) env1)
       (== `((,y . (val . ,v)) . ,res) env-out)
       (regular-env-appendo rest env2 res)))))

(define (match-clauses mval clauses env val)
  (exist (p result-expr d penv)
    (== `((,p ,result-expr) . ,d) clauses)
    (conde
      ((exist (env^)
         (p-match p mval '() penv)
         (regular-env-appendo penv env env^)
         (eval-expo result-expr env^ val)))
      ((p-no-match p mval '() penv)
       (match-clauses mval d env val)))))

(define (var-p-match var mval penv penv-out)
  (exist (val)
    (symbolo var)
    (=/= 'closure mval)
    (conde
      ((== mval val)
       (== penv penv-out)
       (lookupo var penv val))
      ((== `((,var . (val . ,mval)) . ,penv) penv-out)
       (not-in-envo var penv)))))

(define (var-p-no-match var mval penv penv-out)
  (exist (val)
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
    ((exist (var pred val)
      (== `(? ,pred ,var) p)
      (conde
        ((== 'symbol? pred)
         (symbolo mval))
        ((== 'number? pred)
         (numbero mval)))
      (var-p-match var mval penv penv-out)))
    ((exist (quasi-p)
      (== (list 'quasiquote quasi-p) p)
      (quasi-p-match quasi-p mval penv penv-out)))))

(define (p-no-match p mval penv penv-out)
  (conde
    ((self-eval-literalo p)
     (=/= p mval)
     (== penv penv-out))
    ((var-p-no-match p mval penv penv-out))
    ((exist (var pred val)
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
    ((exist (quasi-p)
      (== (list 'quasiquote quasi-p) p)
      (quasi-p-no-match quasi-p mval penv penv-out)))))

(define (quasi-p-match quasi-p mval penv penv-out)
  (conde
    ((== quasi-p mval)
     (== penv penv-out)
     (literalo quasi-p))
    ((exist (p)
      (== (list 'unquote p) quasi-p)
      (p-match p mval penv penv-out)))
    ((exist (a d v1 v2 penv^)
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
    ((exist (p)
       (== (list 'unquote p) quasi-p)
       (=/= 'closure mval)
       (p-no-match p mval penv penv-out)))
    ((exist (a d)
       (== `(,a . ,d) quasi-p)
       (=/= 'unquote a)
       (== penv penv-out)
       (literalo mval)))
    ((exist (a d v1 v2 penv^)
       (== `(,a . ,d) quasi-p)
       (=/= 'unquote a)
       (== `(,v1 . ,v2) mval)
       (conde
         ((quasi-p-no-match a v1 penv penv^))
         ((quasi-p-match a v1 penv penv^)
          (quasi-p-no-match d v2 penv^ penv-out)))))))

(module+ test
  (check-equal?
    (run*-da q (== q 5))
    '(5))

  (check-equal?
    (run-da 1 q (evalo '6 q))
    '(6))

  (check-equal?
    (run-da 1 q (evalo '7 q))
    '(7))

  (check-equal?
    (run-da-dls 1 () q (evalo '(quote foo) q))
    '(foo))

  (check-equal?
    (run-da-dls 1 () q (evalo '(and 9) q))
    '(9))

  ; these three test results are too unstable to keep on
  ;(check-equal?
    ;(run-da-dls 1 () q (evalo '(lambda y 8) q))
    ;'((closure (lambda y 8)
        ;((list val closure (lambda x x) ())
         ;(not val prim . not)
         ;(equal? val prim . equal?)
         ;(symbol? val prim . symbol?)
         ;(cons val prim . cons)
         ;(null? val prim . null?)
         ;(car val prim . car)
         ;(cdr val prim . cdr)))))
  ;(check-equal?
    ;(run-da-dls 1 () q (evalo '(lambda (x) x) q))
    ;'((closure (lambda (x) x)
        ;((list val closure (lambda x x) ())
         ;(not val prim . not)
         ;(equal? val prim . equal?)
         ;(symbol? val prim . symbol?)
         ;(cons val prim . cons)
         ;(null? val prim . null?)
         ;(car val prim . car)
         ;(cdr val prim . cdr)))))
  ;(check-equal?
    ;(run-da-dls 10 () (e v) (evalo e v))
    ;'((_.0 _.0)
      ;(list (closure (lambda x x) ()))
      ;(not (prim . not))
      ;(equal? (prim . equal?))
      ;((list) ())
      ;((list _.0) (_.0))
      ;((list list) ((closure (lambda x x) ())))
      ;(#t #t)
      ;((list _.0 _.1) (_.0 _.1))
      ;(#f #f)))

  (check-equal?
    (run-da-dls 1 (10000) q
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
    '(_.0))

  (check-equal?
    (run*-da-dls (100)
      (l1 l2)
      (evalo `(letrec ((append (lambda (l s)
                                 (if (null? l)
                                   s
                                   (cons (car l)
                                         (append (cdr l) s))))))
                (append ',l1 ',l2))
             '(1 2 3 4 5)))
    '((() (1 2 3 4 5))
      ((1) (2 3 4 5))
      ((1 2) (3 4 5))
      ((1 2 3) (4 5))
      ((1 2 3 4) (5))
      ((1 2 3 4 5) ())))

  ;; flipping rand/body eval order makes this one too hard!
  ;(check-equal?
    ;(run-da-dls 1 (100) q
;;                (== q '(car l))
      ;(evalo `(letrec ((append (lambda (l s)
                                 ;(if (null? l)
                                   ;s
                                   ;(cons ,q
                                         ;(append (cdr l) s))))))
                ;(append '(1 2 3) '(4 5)))
             ;'(1 2 3 4 5)))
    ;'((car l)))

  (check-equal?
    (run-da-dls 1 (100) q
      (evalo `(letrec ((append (lambda (l s)
                                     (if (null? l)
                                         s
                                         (cons (car l)
                                               (append (cdr ,q) s))))))
                    (append '(1 2 3) '(4 5)))
                 '(1 2 3 4 5)))
    '(l))

  (check-equal?
    (run-da-dls 1 (100) q
      (evalo `(letrec ((append (lambda (l s)
                                 (if (null? l)
                                   s
                                   (cons (car l)
                                         (append (,q l) s))))))
                    (append '(1 2 3) '(4 5)))
                 '(1 2 3 4 5)))
    '(cdr))

  ;; hard 1: now only takes 0.9s!
  (check-equal?
    (run-da-dls 1 (100) (q r)
      (evalo `(letrec ((append (lambda (l s)
                                     (if (null? l)
                                         s
                                         (cons (car l)
                                               (append (,q ,r) s))))))
                    (append '(1 2 3) '(4 5)))
                 '(1 2 3 4 5)))
    '((cdr l)))

  ;; hard 2: now only takes about 2.25s!
  (check-equal?
    (run-da-dls 1 (100) q
      (evalo `(letrec ((append (lambda (l s)
                                     (if (null? l)
                                         s
                                         (cons (car l)
                                               (append ,q s))))))
                    (append '(1 2 3) '(4 5)))
                 '(1 2 3 4 5))
      )
    '((cdr l)))

  ;; hard 3
  (check-equal?
    (run-da-dls 1 (100) (q r)
;                (== q '(cdr l)) (== r 's)
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
    '(((cdr l) s)))

  ;; hard 4
  (check-equal?
    (run-da-dls 1 (100) q
;                (== q '((cdr l) s))
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
    '(((cdr l) s)))

  (define quinec
  '((lambda (_.0)
      (list _.0 (list (quote quote) _.0)))
    (quote
      (lambda (_.0)
        (list _.0 (list (quote quote) _.0))))))

  ;; runs out of memory at 4m30s
  ;(check-equal?
    ;(run-da-dls 4 (18) q (evalo q q))
    ;'())
  )
