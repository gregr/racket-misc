#lang racket/base
(provide

  )
(require
  "dakanren.rkt"
  "minikanren.rkt"
  )

(module+ test
  (require
    "list.rkt"
    "sugar.rkt"
    racket/set
    rackunit
    ))

(define appendo
  (lambda (l s out)
    (conde
      [(== '() l) (== s out)]
      [(exist (a d res)
         (== `(,a . ,d) l)
         (== `(,a . ,res) out)
         (appendo d s res))])))

(define build-num
  (lambda (n)
    (cond
      ((odd? n)
       (cons 1
         (build-num (quotient (- n 1) 2))))
      ((and (not (zero? n)) (even? n))
       (cons 0
         (build-num (quotient n 2))))
      ((zero? n) '()))))

(define zeroo
  (lambda (n)
    (== '() n)))

(define poso
  (lambda (n)
    (exist (a d)
      (== `(,a . ,d) n))))

(define >1o
  (lambda (n)
    (exist (a ad dd)
      (== `(,a ,ad . ,dd) n))))

(define full-addero
  (lambda (b x y r c)
    (conde
      ((== 0 b) (== 0 x) (== 0 y) (== 0 r) (== 0 c))
      ((== 1 b) (== 0 x) (== 0 y) (== 1 r) (== 0 c))
      ((== 0 b) (== 1 x) (== 0 y) (== 1 r) (== 0 c))
      ((== 1 b) (== 1 x) (== 0 y) (== 0 r) (== 1 c))
      ((== 0 b) (== 0 x) (== 1 y) (== 1 r) (== 0 c))
      ((== 1 b) (== 0 x) (== 1 y) (== 0 r) (== 1 c))
      ((== 0 b) (== 1 x) (== 1 y) (== 0 r) (== 1 c))
      ((== 1 b) (== 1 x) (== 1 y) (== 1 r) (== 1 c)))))

(define addero
  (lambda (d n m r)
    (conde
      ((== 0 d) (== '() m) (== n r))
      ((== 0 d) (== '() n) (== m r)
       (poso m))
      ((== 1 d) (== '() m)
       (addero 0 n '(1) r))
      ((== 1 d) (== '() n) (poso m)
       (addero 0 '(1) m r))
      ((== '(1) n) (== '(1) m)
       (exist (a c)
         (== `(,a ,c) r)
         (full-addero d 1 1 a c)))
      ((== '(1) n) (gen-addero d n m r))
      ((== '(1) m) (>1o n) (>1o r)
       (addero d '(1) n r))
      ((>1o n) (gen-addero d n m r)))))

(define gen-addero
  (lambda (d n m r)
    (exist (a b c e x y z)
      (== `(,a . ,x) n)
      (== `(,b . ,y) m) (poso y)
      (== `(,c . ,z) r) (poso z)
      (full-addero d a b c e)
      (addero e x y z))))

(define pluso
  (lambda (n m k)
    (addero 0 n m k)))

(define minuso
  (lambda (n m k)
    (pluso m k n)))

(define *o
  (lambda (n m p)
    (conde
      ((== '() n) (== '() p))
      ((poso n) (== '() m) (== '() p))
      ((== '(1) n) (poso m) (== m p))
      ((>1o n) (== '(1) m) (== n p))
      ((exist (x z)
         (== `(0 . ,x) n) (poso x)
         (== `(0 . ,z) p) (poso z)
         (>1o m)
         (*o x m z)))
      ((exist (x y)
         (== `(1 . ,x) n) (poso x)
         (== `(0 . ,y) m) (poso y)
         (*o m n p)))
      ((exist (x y)
         (== `(1 . ,x) n) (poso x)
         (== `(1 . ,y) m) (poso y)
         (odd-*o x n m p))))))

(define odd-*o
  (lambda (x n m p)
    (exist (q)
      (bound-*o q p n m)
      (*o x m q)
      (pluso `(0 . ,q) m p))))

(define bound-*o
  (lambda (q p n m)
    (conde
      ((== '() q) (poso p))
      ((exist (a0 a1 a2 a3 x y z)
         (== `(,a0 . ,x) q)
         (== `(,a1 . ,y) p)
         (conde
           ((== '() n)
            (== `(,a2 . ,z) m)
            (bound-*o x y z '()))
           ((== `(,a3 . ,z) n)
            (bound-*o x y z m))))))))

(define =lo
  (lambda (n m)
    (conde
      ((== '() n) (== '() m))
      ((== '(1) n) (== '(1) m))
      ((exist (a x b y)
         (== `(,a . ,x) n) (poso x)
         (== `(,b . ,y) m) (poso y)
         (=lo x y))))))

(define <lo
  (lambda (n m)
    (conde
      ((== '() n) (poso m))
      ((== '(1) n) (>1o m))
      ((exist (a x b y)
         (== `(,a . ,x) n) (poso x)
         (== `(,b . ,y) m) (poso y)
         (<lo x y))))))

(define <=lo
  (lambda (n m)
    (conde
      ((=lo n m))
      ((<lo n m)))))

(define <o
  (lambda (n m)
    (conde
      ((<lo n m))
      ((=lo n m)
       (exist (x)
         (poso x)
         (pluso n x m))))))

(define <=o
  (lambda (n m)
    (conde
      ((== n m))
      ((<o n m)))))

(define /o
  (lambda (n m q r)
    (conde
      ((== r n) (== '() q) (<o n m))
      ((== '(1) q) (=lo n m) (pluso r m n)
       (<o r m))
      ((<lo m n)
       (<o r m)
       (poso q)
       (exist (nh nl qh ql qlm qlmr rr rh)
         (splito n r nl nh)
         (splito q r ql qh)
         (conde
           ((== '() nh)
            (== '() qh)
            (minuso nl r qlm)
            (*o ql m qlm))
           ((poso nh)
            (*o ql m qlm)
            (pluso qlm r qlmr)
            (minuso qlmr nl rr)
            (splito rr r '() rh)
            (/o nh m qh rh))))))))

(define splito
  (lambda (n r l h)
    (conde
      ((== '() n) (== '() h) (== '() l))
      ((exist (b n^)
         (== `(0 ,b . ,n^) n)
         (== '() r)
         (== `(,b . ,n^) h)
         (== '() l)))
      ((exist (n^)
         (== `(1 . ,n^) n)
         (== '() r)
         (== n^ h)
         (== '(1) l)))
      ((exist (b n^ a r^)
         (== `(0 ,b . ,n^) n)
         (== `(,a . ,r^) r)
         (== '() l)
         (splito `(,b . ,n^) r^ '() h)))
      ((exist (n^ a r^)
         (== `(1 . ,n^) n)
         (== `(,a . ,r^) r)
         (== '(1) l)
         (splito n^ r^ '() h)))
      ((exist (b n^ a r^ l^)
         (== `(,b . ,n^) n)
         (== `(,a . ,r^) r)
         (== `(,b . ,l^) l)
         (poso l^)
         (splito n^ r^ l^ h))))))

(define logo
  (lambda (n b q r)
    (conde
      ((== '(1) n) (poso b) (== '() q) (== '() r))
      ((== '() q) (<o n b) (pluso r '(1) n))
      ((== '(1) q) (>1o b) (=lo n b) (pluso r b n))
      ((== '(1) b) (poso q) (pluso r '(1) n))
      ((== '() b) (poso q) (== r n))
      ((== '(0 1) b)
       (exist (a ad dd)
         (poso dd)
         (== `(,a ,ad . ,dd) n)
         (exp2 n '() q)
         (exist (s)
           (splito n dd r s))))
      ((exist (a ad add ddd)
         (conde
           ((== '(1 1) b))
           ((== `(,a ,ad ,add . ,ddd) b))))
       (<lo b n)
       (exist (bw1 bw nw nw1 ql1 ql s)
         (exp2 b '() bw1)
         (pluso bw1 '(1) bw)
         (<lo q n)
         (exist (q1 bwq1)
           (pluso q '(1) q1)
           (*o bw q1 bwq1)
           (<o nw1 bwq1))
         (exp2 n '() nw1)
         (pluso nw1 '(1) nw)
         (/o nw bw ql1 s)
         (pluso ql '(1) ql1)
         (<=lo ql q)
         (exist (bql qh s qdh qd)
           (repeated-mul b ql bql)
           (/o nw bw1 qh s)
           (pluso ql qdh qh)
           (pluso ql qd q)
           (<=o qd qdh)
           (exist (bqd bq1 bq)
             (repeated-mul b qd bqd)
             (*o bql bqd bq)
             (*o b bq bq1)
             (pluso bq r n)
             (<o n bq1))))))))

(define exp2
  (lambda (n b q)
    (conde
      ((== '(1) n) (== '() q))
      ((>1o n) (== '(1) q)
       (exist (s)
         (splito n b s '(1))))
      ((exist (q1 b2)
         (== `(0 . ,q1) q)
         (poso q1)
         (<lo b n)
         (appendo b `(1 . ,b) b2)
         (exp2 n b2 q1)))
      ((exist (q1 nh b2 s)
         (== `(1 . ,q1) q)
         (poso q1)
         (poso nh)
         (splito n b s nh)
         (appendo b `(1 . ,b) b2)
         (exp2 nh b2 q1))))))

(define repeated-mul
  (lambda (n q nq)
    (conde
      ((poso n) (== '() q) (== '(1) nq))
      ((== '(1) q) (== n nq))
      ((>1o q)
       (exist (q1 nq1)
         (pluso q1 '(1) q)
         (repeated-mul n q1 nq1)
         (*o nq1 n nq))))))

(define expo
  (lambda (b q n)
    (logo n b q '())))


(module+ test
  (define-syntax mk-test-cont
    (syntax-rules ()
      ((_ test-name exact? query expected)
       (lets
         result-set = (list->set query)
         expected-set = (list->set expected)
         overlap = (set-intersect result-set expected-set)
         (if exact?
           (begin
             (check-equal? (set-subtract expected-set result-set) (set))
             (check-equal? (set-subtract result-set expected-set) (set))
             (check-equal? result-set expected-set))
           (check-equal? overlap expected-set))))))
  (define-syntax mk-test
    (syntax-rules ()
      ((_ test-name query expected)
       (mk-test-cont test-name #t query expected))))

  (mk-test "test 1"
    (run* q (*o (build-num 2) (build-num 3) q))
    '((0 1 1)))

  (mk-test "test 2"
    (run* (n m) (*o n m (build-num 6)))
    '(((1) (0 1 1)) ((0 1 1) (1)) ((0 1) (1 1)) ((1 1) (0 1))))

  (mk-test "sums"
    (run 5 (x y z) (pluso x y z))
    '((_.0 () _.0)
      (() (_.0 . _.1) (_.0 . _.1))
      ((1) (1) (0 1))
      ((1) (0 _.0 . _.1) (1 _.0 . _.1))
      ; other implementation finds ((1) (1 1) (0 0 1)) first
      ((0 1) (0 1) (0 0 1))
      ))

  (mk-test "factors"
    (run* q
      (exist (x y)
        (*o x y (build-num 24))
        (== `(,x ,y ,(build-num 24)) q)))
    '(((1) (0 0 0 1 1) (0 0 0 1 1))
      ((0 0 0 1 1) (1) (0 0 0 1 1))
      ((0 1) (0 0 1 1) (0 0 0 1 1))
      ((0 0 1) (0 1 1) (0 0 0 1 1))
      ((0 0 0 1) (1 1) (0 0 0 1 1))
      ((1 1) (0 0 0 1) (0 0 0 1 1))
      ((0 1 1) (0 0 1) (0 0 0 1 1))
      ((0 0 1 1) (0 1) (0 0 0 1 1))))

  (lets
    (list actual expected) =
    (zip (forl
           (list a b) <- '((0 0) (0 1) (1 0) (1 2) (2 1) (2 2) (3 4) (6 6))
           (list (run* r (pluso (build-num a) (build-num b) r))
                 `(,(build-num (+ a b))))))
    (check-equal? actual expected))

  (lets
    (list actual expected) =
    (zip (forl
           (list a b) <- '((0 0) (1 0) (2 1) (2 2) (3 1) (4 1) (4 2) (4 3)
                           (5 1) (5 2) (6 6) (7 1) (7 2) (7 3) (7 4) (7 5))
           (list (run* r (minuso (build-num a) (build-num b) r))
                 `(,(build-num (- a b))))))
    (check-equal? actual expected))

  (lets
    (list actual expected) =
    (zip (forl
           (list a b) <- '((0 0) (0 1) (1 0) (1 2) (2 1) (2 2) (3 4) (6 6))
           (list (run* r (*o (build-num a) (build-num b) r))
                 `(,(build-num (* a b))))))
    (check-equal? actual expected))

  ; works, but slow
  ;(lets
    ;(list actual expected) =
    ;(zip (forl
           ;(list a b) <- '((0 1) (1 1) (1 2) (2 1) (3 2) (3 4) (4 2))
           ;(list (run 1 (q r) (/o (build-num a) (build-num b) q r))
              ;`((,(build-num (quotient a b)) ,(build-num (remainder a b)))))))
    ;(check-equal? actual expected))

  (lets
    (list actual expected) =
    (zip (forl
           (list a b) <- '((1 0) (1 1) (1 2) (2 1) (2 2) (2 3) (3 2))
           (list (run*-depth 100 r (expo (build-num a) (build-num b) r))
                 `(,(build-num (expt a b))))))
    (check-equal? actual expected))

  ; what do each of the logo parameters mean?
  ;(lets
    ;(list actual expected) =
    ;(zip (forl
           ;(list b a) <- '((0 1) (1 1) ;(1 2) (2 1)
                           ;)
           ;(list p r) <- '((0 0) (0 0) ;(0 1) (0 0)
                           ;)
           ;`(,(run-depth 1 1 (p r) (logo (build-num b) (build-num a) p r))
              ;(,(build-num p) ,(build-num r)))))
    ;(check-equal? actual expected))

  ; too slow to find the second answer
  ;(print (run 2 (b q r)
    ;(logo '(0 0 1 0 0 0 1) b q r)
    ;(>1o q)))

  ;(time (run 9 (b q r)
    ;(logo '(0 0 1 0 0 0 1) b q r)
    ;(>1o q)))
  ;(time (run 9 ...))
      ;246 collections
      ;3.404931000s elapsed cpu time, including 0.274265000s collecting
      ;3.407526000s elapsed real time, including 0.274941000s collecting
      ;2 071 928 368 bytes allocated, including 2059553856 bytes reclaimed
  ;((() (_0 _1 . _2) (0 0 1 0 0 0 1))
  ;((1) (_0 _1 . _2) (1 1 0 0 0 0 1))
  ;((0 1) (0 1 1) (0 0 1))
  ;((1 1) (1 1) (1 0 0 1 0 1))
  ;((0 0 1) (1 1) (0 0 1))
  ;((0 0 0 1) (0 1) (0 0 1))
  ;((1 0 1) (0 1) (1 1 0 1 0 1))
  ;((0 1 1) (0 1) (0 0 0 0 0 1))
  ;((1 1 1) (0 1) (1 1 0 0 1)))

  ; depth=20 gives these 9 answers in 4.25s
  (check-equal? (list->set (run-da-dls
                             9 (20 (lambda (d) (+ 10 d)) #f)
                             (b q r) (logo '(0 0 1 0 0 0 1) b q r) (>1o q)))
                (list->set
                  '((() (_.0 _.1 . _.2) (0 0 1 0 0 0 1))
                    ((1) (_.0 _.1 . _.2) (1 1 0 0 0 0 1))
                    ((0 1) (0 1 1) (0 0 1))
                    ((1 1) (1 1) (1 0 0 1 0 1))
                    ((0 0 1) (1 1) (0 0 1))
                    ((0 0 0 1) (0 1) (0 0 1))
                    ((1 0 1) (0 1) (1 1 0 1 0 1))
                    ((0 1 1) (0 1) (0 0 0 0 0 1))
                    ((1 1 1) (0 1) (1 1 0 0 1)))))

  ; missing dependencies for these

  ;(define number-primo
    ;(lambda (exp env val)
      ;(exist (n)
        ;(== `(intexp ,n) exp)
        ;(== `(intval ,n) val)
        ;(not-in-envo 'numo env))))

  ;(define sub1-primo
    ;(lambda (exp env val)
      ;(exist (e n n-1)
        ;(== `(sub1 ,e) exp)
        ;(== `(intval ,n-1) val)
        ;(not-in-envo 'sub1 env)
        ;(eval-expo e env `(intval ,n))
        ;(minuso n '(1) n-1))))

  ;(define zero?-primo
    ;(lambda (exp env val)
      ;(exist (e n)
        ;(== `(zero? ,e) exp)
        ;(conde
          ;((zeroo n) (== #t val))
          ;((poso n) (== #f val)))
        ;(not-in-envo 'zero? env)
        ;(eval-expo e env `(intval ,n)))))

  ;(define *-primo
    ;(lambda (exp env val)
      ;(exist (e1 e2 n1 n2 n3)
        ;(== `(* ,e1 ,e2) exp)
        ;(== `(intval ,n3) val)
        ;(not-in-envo '* env)
        ;(eval-expo e1 env `(intval ,n1))
        ;(eval-expo e2 env `(intval ,n2))
        ;(*o n1 n2 n3))))

  ;(define if-primo
    ;(lambda (exp env val)
      ;(exist (e1 e2 e3 t)
        ;(== `(if ,e1 ,e2 ,e3) exp)
        ;(not-in-envo 'if env)
        ;(eval-expo e1 env t)
        ;(conde
          ;((== #t t) (eval-expo e2 env val))
          ;((== #f t) (eval-expo e3 env val))))))

  (define boolean-primo
    (lambda (exp env val)
      (conde
        ((== #t exp) (== #t val))
        ((== #f exp) (== #f val)))))

  ;(define eval-expo
    ;(lambda (exp env val)
      ;(conde
        ;((boolean-primo exp env val))
        ;((number-primo exp env val))
        ;((sub1-primo exp env val))
        ;((zero?-primo exp env val))
        ;((*-primo exp env val))
        ;((if-primo exp env val))
        ;((symbolo exp) (lookupo exp env val))
        ;((exist (rator rand x body env^ a)
          ;(== `(,rator ,rand) exp)
          ;(eval-expo rator env `(closure ,x ,body ,env^))
          ;(eval-expo rand env a)
          ;(eval-expo body `((,x . ,a) . ,env^) val)))
        ;((exist (x body)
          ;(== `(lambda (,x) ,body) exp)
          ;(symbolo x)
          ;(== `(closure ,x ,body ,env) val)
          ;(not-in-envo 'lambda env))))))

  ;(define not-in-envo
    ;(lambda (x env)
      ;(conde
        ;((exist (y v rest)
          ;(== `((,y . ,v) . ,rest) env)
          ;(=/= y x)
          ;(not-in-envo x rest)))
        ;((== '() env)))))

  ;(define lookupo
    ;(lambda (x env t)
      ;(exist (rest y v)
        ;(== `((,y . ,v) . ,rest) env)
        ;(conde
          ;((== y x) (== v t))
          ;((=/= y x) (lookupo x rest t))))))

  ;(mk-test "push-down problems 2"
    ;(run* (q)
    ;(exist (x a d)
      ;(absento 'intval x)
      ;(== 'intval a)
      ;(== `(,a . ,d) x)))
    ;'())

  ;(mk-test "push-down problems 3"
    ;(run* (q)
    ;(exist (x a d)
      ;(== `(,a . ,d) x)
      ;(absento 'intval x)
      ;(== 'intval a)))
    ;'())

  ;(mk-test "push-down problems 4"
    ;(run* (q)
    ;(exist (x a d)
      ;(== `(,a . ,d) x)
      ;(== 'intval a)
      ;(absento 'intval x)))
    ;'())

  ;(mk-test "push-down problems 6"
    ;(run* (q)
    ;(exist (x a d)
      ;(== 'intval a)
      ;(== `(,a . ,d) x)
      ;(absento 'intval x)))
    ;'())

  ;(mk-test "push-down problems 1"
    ;(run* (q)
    ;(exist (x a d)
      ;(absento 'intval x)
      ;(== `(,a . ,d) x)
      ;(== 'intval a)))
    ;'())

  ;(mk-test "push-down problems 5"
    ;(run* (q)
    ;(exist (x a d)
      ;(== 'intval a)
      ;(absento 'intval x)
      ;(== `(,a . ,d) x)))
    ;'())

  ;(mk-test "zero?"
    ;(run 1 (q)
        ;(eval-expo `(zero? (sub1 (intexp ,(build-num 1)))) '() q))
    ;'(#t))

  ;(mk-test "*"
    ;(run 1 (q)
        ;(eval-expo `(* (intexp ,(build-num 3)) (intexp ,(build-num 2))) '() `(intval ,(build-num 6))))
    ;'(_.0))

  ;(mk-test "sub1"
    ;(run 1 (q)
        ;(eval-expo q '() `(intval ,(build-num 6))) (== `(sub1 (intexp ,(build-num 7))) q))
    ;'((sub1 (intexp (1 1 1)))))

  ;(mk-test "sub1 bigger WAIT a minute"
    ;(run 1 (q)
      ;(eval-expo q '() `(intval ,(build-num 6)))
      ;(== `(sub1 (sub1 (intexp ,(build-num 8)))) q))
    ;'((sub1 (sub1 (intexp (0 0 0 1))))))

  ;(mk-test "sub1 biggest WAIT a minute"
    ;(run 1 (q)
      ;(eval-expo q '() `(intval ,(build-num 6)))
      ;(== `(sub1 (sub1 (sub1 (intexp ,(build-num 9))))) q))
    ;'((sub1 (sub1 (sub1 (intexp (1 0 0 1)))))))

  ;(mk-test "lots of programs to make a 6"
    ;(run 12 (q) (eval-expo q '() `(intval ,(build-num 6))))
    ;'((intexp (0 1 1)) (sub1 (intexp (1 1 1)))
  ;(* (intexp (1)) (intexp (0 1 1)))
  ;(* (intexp (0 1 1)) (intexp (1)))
  ;(if #t (intexp (0 1 1)) _.0)
  ;(* (intexp (0 1)) (intexp (1 1)))
  ;(if #f _.0 (intexp (0 1 1)))
  ;(sub1 (* (intexp (1)) (intexp (1 1 1))))
  ;(((lambda (_.0) (intexp (0 1 1))) #t)
    ;(=/= ((_.0 numo)))
    ;(sym _.0))
  ;(sub1 (* (intexp (1 1 1)) (intexp (1))))
  ;(sub1 (sub1 (intexp (0 0 0 1))))
  ;(sub1 (if #t (intexp (1 1 1)) _.0))))

  ;(define rel-fact5
    ;`((lambda (f)
        ;((f f) (intexp ,(build-num 5))))
      ;(lambda (f)
        ;(lambda (n)
          ;(if (zero? n)
              ;(intexp ,(build-num 1))
              ;(* n ((f f) (sub1 n))))))))

  ;(mk-test "rel-fact5"
    ;(run* (q) (eval-expo rel-fact5 '() q))
    ;`((intval ,(build-num 120))))

  ;(mk-test "rel-fact5-backwards"
    ;(run 1 (q)
      ;(eval-expo
      ;`((lambda (f)
          ;((f ,q) (intexp ,(build-num 5))))
        ;(lambda (f)
          ;(lambda (n)
            ;(if (zero? n)
                ;(intexp ,(build-num 1))
                ;(* n ((f f) (sub1 n)))))))
      ;'()
      ;`(intval ,(build-num 120))))
    ;`(f))
  )
