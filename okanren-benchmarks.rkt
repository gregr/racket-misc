#lang racket/base
(require "okanren.rkt")
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
    (fresh (a d)
      (== `(,a . ,d) n))))

(define >1o
  (lambda (n)
    (fresh (a ad dd)
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

(kanren
  (define appendo
    (lambda (l s out)
      (conde
        ((== '() l) (== s out))
        ((fresh (a d res)
                (== `(,a . ,d) l)
                (== `(,a . ,res) out)
                (appendo d s res))))))

  (define addero
    (lambda (d n m r)
      (conde
        ((== 0 d) (== '() m) (== n r))
        ((== 0 d) (== '() n) (== m r) (poso m))
        ((== 1 d) (== '() m) (addero 0 n '(1) r))
        ((== 1 d) (== '() n) (poso m) (addero 0 '(1) m r))
        ((== '(1) n) (== '(1) m)
         (fresh (a c) (== `(,a ,c) r) (full-addero d 1 1 a c)))
        ((== '(1) n) (gen-addero d n m r))
        ((== '(1) m) (>1o n) (>1o r) (addero d '(1) n r))
        ((>1o n) (gen-addero d n m r)))))
  )

(define gen-addero
  (lambda (d n m r)
    (fresh (a b c e x y z)
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

(kanren
  (define *o
    (lambda (n m p)
      (conde
        ((== '() n) (== '() p))
        ((poso n) (== '() m) (== '() p))
        ((== '(1) n) (poso m) (== m p))
        ((>1o n) (== '(1) m) (== n p))
        ((fresh (x z)
           (== `(0 . ,x) n) (poso x)
           (== `(0 . ,z) p) (poso z)
           (>1o m)
           (*o x m z)))
        ((fresh (x y)
           (== `(1 . ,x) n) (poso x)
           (== `(0 . ,y) m) (poso y)
           (*o m n p)))
        ((fresh (x y)
           (== `(1 . ,x) n) (poso x)
           (== `(1 . ,y) m) (poso y)
           (odd-*o x n m p))))))

  (define odd-*o
    (lambda (x n m p)
      (fresh (q)
        (bound-*o q p n m)
        (*o x m q)
        (pluso `(0 . ,q) m p))))

  (define bound-*o
    (lambda (q p n m)
      (conde
        ((== '() q) (poso p))
        ((fresh (a0 a1 a2 a3 x y z)
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
        ((fresh (a x b y)
           (== `(,a . ,x) n) (poso x)
           (== `(,b . ,y) m) (poso y)
           (=lo x y))))))

  (define <lo
    (lambda (n m)
      (conde
        ((== '() n) (poso m))
        ((== '(1) n) (>1o m))
        ((fresh (a x b y)
           (== `(,a . ,x) n) (poso x)
           (== `(,b . ,y) m) (poso y)
           (<lo x y))))))
  )

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
       (fresh (x)
         (poso x)
         (pluso n x m))))))

(define <=o
  (lambda (n m)
    (conde
      ((== n m))
      ((<o n m)))))

(kanren
  (define /o
    (lambda (n m q r)
      (conde
        ((== r n) (== '() q) (<o n m))
        ((== '(1) q) (=lo n m) (pluso r m n) (<o r m))
        ((<lo m n) (<o r m) (poso q)
         (fresh (nh nl qh ql qlm qlmr rr rh)
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
        ((fresh (b n^)
           (== `(0 ,b . ,n^) n)
           (== '() r)
           (== `(,b . ,n^) h)
           (== '() l)))
        ((fresh (n^)
           (== `(1 . ,n^) n)
           (== '() r)
           (== n^ h)
           (== '(1) l)))
        ((fresh (b n^ a r^)
           (== `(0 ,b . ,n^) n)
           (== `(,a . ,r^) r)
           (== '() l)
           (splito `(,b . ,n^) r^ '() h)))
        ((fresh (n^ a r^)
           (== `(1 . ,n^) n)
           (== `(,a . ,r^) r)
           (== '(1) l)
           (splito n^ r^ '() h)))
        ((fresh (b n^ a r^ l^)
           (== `(,b . ,n^) n)
           (== `(,a . ,r^) r)
           (== `(,b . ,l^) l)
           (poso l^)
           (splito n^ r^ l^ h))))))

  (define exp2
    (lambda (n b q)
      (conde
        ((== '(1) n) (== '() q))
        ((>1o n) (== '(1) q) (fresh (s) (splito n b s '(1))))
        ((fresh (q1 b2)
           (== `(0 . ,q1) q)
           (poso q1)
           (<lo b n)
           (appendo b `(1 . ,b) b2)
           (exp2 n b2 q1)))
        ((fresh (q1 nh b2 s)
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
         (fresh (q1 nq1)
           (pluso q1 '(1) q)
           (repeated-mul n q1 nq1)
           (*o nq1 n nq))))))
  )

(define logo
  (lambda (n b q r)
    (conde
      ((== '(1) n) (poso b) (== '() q) (== '() r))
      ((== '() q) (<o n b) (pluso r '(1) n))
      ((== '(1) q) (>1o b) (=lo n b) (pluso r b n))
      ((== '(1) b) (poso q) (pluso r '(1) n))
      ((== '() b) (poso q) (== r n))
      ((== '(0 1) b)
       (fresh (a ad dd)
         (poso dd)
         (== `(,a ,ad . ,dd) n)
         (exp2 n '() q)
         (fresh (s)
           (splito n dd r s))))
      ((fresh (a ad add ddd)
         (conde
           ((== '(1 1) b))
           ((== `(,a ,ad ,add . ,ddd) b))))
       (<lo b n)
       (fresh (bw1 bw nw nw1 ql1 ql s)
         (exp2 b '() bw1)
         (pluso bw1 '(1) bw)
         (<lo q n)
         (fresh (q1 bwq1)
           (pluso q '(1) q1)
           (*o bw q1 bwq1)
           (<o nw1 bwq1))
         (exp2 n '() nw1)
         (pluso nw1 '(1) nw)
         (/o nw bw ql1 s)
         (pluso ql '(1) ql1)
         (<=lo ql q)
         (fresh (bql qh s qdh qd)
           (repeated-mul b ql bql)
           (/o nw bw1 qh s)
           (pluso ql qdh qh)
           (pluso ql qd q)
           (<=o qd qdh)
           (fresh (bqd bq1 bq)
             (repeated-mul b qd bqd)
             (*o bql bqd bq)
             (*o b bq bq1)
             (pluso bq r n)
             (<o n bq1))))))))

(define expo
  (lambda (b q n)
    (logo n b q '())))

(module+ test
  (mk-test "test 1"
    (run* (q) (*o (build-num 2) (build-num 3) q))
    '((((0 1 1)))))

  (mk-test "test 2"
    (run* (n m) (*o n m (build-num 6)))
    '((((1) (0 1 1))) (((0 1 1) (1))) (((0 1) (1 1))) (((1 1) (0 1)))))

  (mk-test-subsumed "sums"
    (run 17 (x y z) (pluso x y z))
    '(((_.0 () _.0))
      ((() (_.0 . _.1) (_.0 . _.1)))
      (((1) (1) (0 1)))
      (((1) (0 _.0 . _.1) (1 _.0 . _.1)))
      (((1) (1 1) (0 0 1)))
      (((0 1) (0 1) (0 0 1)))))

  (mk-test "factors"
    (run* (q)
      (fresh (x y)
        (*o x y (build-num 24))
        (== `(,x ,y ,(build-num 24)) q)))
    '(((((1) (0 0 0 1 1) (0 0 0 1 1))))
      ((((0 0 0 1 1) (1) (0 0 0 1 1))))
      ((((0 1) (0 0 1 1) (0 0 0 1 1))))
      ((((0 0 1) (0 1 1) (0 0 0 1 1))))
      ((((0 0 0 1) (1 1) (0 0 0 1 1))))
      ((((1 1) (0 0 0 1) (0 0 0 1 1))))
      ((((0 1 1) (0 0 1) (0 0 0 1 1))))
      ((((0 0 1 1) (0 1) (0 0 0 1 1))))))

  (mk-test-time "logo 3 answers"
    (run 3 (b q r)
      (logo '(0 0 1 0 0 0 1) b q r)
      (>1o q))
    '(((() (_.0 _.1 . _.2) (0 0 1 0 0 0 1)))
      (((1) (_.0 _.1 . _.2) (1 1 0 0 0 0 1)))
      (((0 1) (0 1 1) (0 0 1)))))

  (mk-test-time "logo 9 answers"
    (run 9 (b q r)
      (logo '(0 0 1 0 0 0 1) b q r)
      (>1o q))
    '(((() (_.0 _.1 . _.2) (0 0 1 0 0 0 1)))
      (((1) (_.0 _.1 . _.2) (1 1 0 0 0 0 1)))
      (((0 1) (0 1 1) (0 0 1)))
      (((1 1) (1 1) (1 0 0 1 0 1)))
      (((0 0 1) (1 1) (0 0 1)))
      (((0 0 0 1) (0 1) (0 0 1)))
      (((1 0 1) (0 1) (1 1 0 1 0 1)))
      (((0 1 1) (0 1) (0 0 0 0 0 1)))
      (((1 1 1) (0 1) (1 1 0 0 1)))))
  )

(kanren
  (define eval-expo
    (lambda (exp env val)
      (conde
        ((fresh (v)
           (== `(quote ,v) exp)
           (not-in-envo 'quote env)
           (absento 'closure v)
           (== v val)))
        ((fresh (a*)
           (== `(list . ,a*) exp)
           (not-in-envo 'list env)
           (absento 'closure a*)
           (proper-listo a* env val)))
        ((symbolo exp) (lookupo exp env val))
        ((fresh (rator rand x body env^ a)
           (== `(,rator ,rand) exp)
           (eval-expo rator env `(closure ,x ,body ,env^))
           (eval-expo rand env a)
           (eval-expo body `((,x . ,a) . ,env^) val)))
        ((fresh (x body)
           (== `(lambda (,x) ,body) exp)
           (symbolo x)
           (not-in-envo 'lambda env)
           (== `(closure ,x ,body ,env) val))))))

  (define lookupo
    (lambda (x env t)
      (fresh (y v rest)
        (== `((,y . ,v) . ,rest) env)
        (conde
          ((== y x) (== v t))
          ((=/= y x) (lookupo x rest t))))))

  (define not-in-envo
    (lambda (x env)
      (conde
        ((== '() env))
        ((fresh (y v rest)
           (== `((,y . ,v) . ,rest) env)
           (=/= y x)
           (not-in-envo x rest))))))

  (define proper-listo
    (lambda (exp env val)
      (conde
        ((== '() exp)
         (== '() val))
        ((fresh (a d v-a v-d)
           (== `(,a . ,d) exp)
           (== `(,v-a . ,v-d) val)
           (eval-expo a env v-a)
           (proper-listo d env v-d)))))))

(define quinec
  '((lambda (_.0)
      (list _.0 (list (quote quote) _.0)))
    (quote
      (lambda (_.0)
        (list _.0 (list (quote quote) _.0))))))

(define twine1
  '((lambda (_.0) (list 'quote (list _.0 (list 'quote _.0))))
    '(lambda (_.0) (list 'quote (list _.0 (list 'quote _.0))))))
(define twine0 (list 'quote twine1))

(define thrine2
  '((lambda (_.0) (list 'quote (list 'quote (list _.0 (list 'quote _.0)))))
    '(lambda (_.0) (list 'quote (list 'quote (list _.0 (list 'quote _.0)))))))
(define thrine1 (list 'quote thrine2))
(define thrine0 (list 'quote thrine1))

(module+ test
  (mk-test "quote"
    (run* (q) (eval-expo '(quote 5) '() q))
    '(((5))))

  (mk-test "lambda"
    (run* (q) (eval-expo '(lambda (x) x) '() q))
    '((((closure x x ())))))

  (mk-test "quine parts"
    (run 1 (q) (eval-expo
                 `((lambda (x) (list x ,q))
                   (quote
                     (lambda (x) (list x ,q))))
                 '()
                 `((lambda (x) (list x ,q))
                   (quote
                     (lambda (x) (list x ,q))))))
    '((((list (quote quote) x)))))

  (mk-test "quine more parts"
    (run 1 (q) (eval-expo
                 `((lambda (x) ,q)
                   (quote (lambda (x) ,q)))
                 '()
                 `((lambda (x) ,q)
                   (quote (lambda (x) ,q)))))
    '((((list x (list (quote quote) x))))))

  (mk-test-time "quine full"
    (run 1 (q) (eval-expo q '() q))
    `(((,quinec) (sym _.0) (absento (_.0 closure)) (=/=* ((_.0 . quote)) ((_.0 . list))))))

  (mk-test-time "twine"
    (run 1 (p q) (=/= p q) (eval-expo p '() q) (eval-expo q '() p))
    `(((,twine0 ,twine1)
       (sym _.0) (absento (_.0 closure)) (=/=* ((_.0 . quote)) ((_.0 . list))))))

  ; aim for 3 seconds
  (mk-test-time "thrine"
    (run 1 (p q r) (=/= p q) (=/= q r) (=/= r p)
      (eval-expo p '() q) (eval-expo q '() r) (eval-expo r '() p))
    `(((,thrine0 ,thrine1 ,thrine2)
       (sym _.0) (absento (_.0 closure)) (=/=* ((_.0 . quote)) ((_.0 . list))))))
  )