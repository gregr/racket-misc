#lang racket/base
(provide
  <-=-<=
  never<?
  any<?
  any<=?
  boolean<?
  boolean<=?
  symbol<=?
  number<?
  number<=?
  pair<?
  pair<=?
  sequence<?
  list<?
  list<=?
  vector<?
  vector<=?
  hash<?
  hash<=?
  set<?
  set<=?
  struct<?
  struct<=?
  )

(require
  "sugar.rkt"
  racket/bool
  racket/function
  racket/match
  racket/set
  racket/vector
  )

(module+ test
  (require rackunit))

(define ((<-=-<= f< f=) e0 e1) (or (f= e0 e1) (f< e0 e1)))
(def (never<? _ _) #f)
(define (boolean<? b0 b1) (match* (b0 b1) ((#f #t) #t) ((_ _) #f)))
(define boolean<=? (<-=-<= boolean<? boolean=?))
(define symbol<=? (<-=-<= symbol<? symbol=?))
(define (number<? n0 n1) (and (real? n0) (or (not (real? n1)) (< n0 n1))))
(define number<=? (<-=-<= number<? =))
(def ((pair<? l< r<) (cons l0 r0) (cons l1 r1))
  (or (l< l0 l1) (and (not (l< l1 l0)) (r< r0 r1))))
(define (pair<=? l< r<) (<-=-<= (pair<? l< r<) equal?))

(def ((sequence<? count item<) s0 s1)
  c0 = (count s0)
  c1 = (count s1)
  (or (< c0 c1)
    (and (= c0 c1)
      (forf result = #f
            i0 <- s0
            i1 <- s1
            #:break (or result (item< i1 i0))
            (item< i0 i1)))))
(define (list<? item<) (sequence<? length item<))
(define (list<=? item<) (<-=-<= (list<? item<) equal?))
(define (vector<? item<) (sequence<? vector-length item<))
(define (vector<=? item<) (<-=-<= (vector<? item<) equal?))
(def ((hash<? k< v<) h0 h1)
  initial< = (pair<? k< never<?)
  lp0 = (sort (hash->list h0) initial<)
  lp1 = (sort (hash->list h1) initial<)
  ((sequence<? length (pair<? k< v<)) lp0 lp1))
(define (hash<=? k< v<) (<-=-<= (hash<? k< v<) equal?))
(def ((set<? item<) s0 s1)
  l0 = (sort (set->list s0) item<)
  l1 = (sort (set->list s1) item<)
  ((sequence<? length item<) l0 l1))
(define (set<=? item<) (<-=-<= (set<? item<) equal?))
(def ((struct<? item<) s0 s1)
  n0 = (object-name s0)
  n1 = (object-name s1)
  (or (symbol<? n0 n1)
    (and (symbol=? n0 n1)
      (lets v0 = (vector-drop (struct->vector s0) 1)
            v1 = (vector-drop (struct->vector s1) 1)
            ((sequence<? vector-length item<) v0 v1)))))
(define (struct<=? item<) (<-=-<= (struct<? item<) equal?))

(define (any<? a0 a1)
  (forf result = (void)
        (list type? type<) <- comparator-entries
        #:break (not (void? result))
        new-result = (if (type? a0) (or (not (type? a1)) (type< a0 a1))
          (if (type? a1) #f (void)))
        new-result
        ))
(define (any<=? item<) (<-=-<= any<? equal?))
(define comparator-entries
  `((,void? ,never<?)
    (,boolean? ,boolean<?)
    (,symbol? ,symbol<?)
    (,char? ,char<?)
    (,string? ,string<?)
    (,number? ,number<?)
    (,null? ,never<?)
    (,pair? ,(pair<? any<? any<?))
    (,vector? ,(vector<? any<?))
    (,hash? ,(hash<? any<? any<?))
    (,set? ,(set<? any<?))
    (,struct? ,(struct<? any<?))
    (,procedure? ,never<?)
    (,(const #t) ,never<?)))

(module+ test
  (struct thing (one two) #:transparent)
  (lets
    vals = (list
             (cons (cons 5 'a) (cons 6 '()))
             "string"
             (void)
             'name
             identity
             '()
             #t
             (box 'box)
             identity
             #(10 3 2)
             (thing 1 2)
             'name
             2+i
             #(7 30 2)
             (set 3 4)
             (box 'box)
             (void)
             18
             (thing 'one 'two)
             4
             (cons (cons 3 (void)) (cons 100 '()))
             "another string"
             #(7 8 9)
             '()
             (set 'three 'four)
             #\c
             (hash 'one 1 'two 2)
             #f
             (hash 'five 5)
             )
    sorted-vals = (list
                    (void) (void)
                    #f #t
                    'name 'name
                    #\c
                    "another string" "string"
                    4 18 2+i
                    '() '()
                    (cons (cons 3 (void)) (cons 100 '()))
                    (cons (cons 5 'a) (cons 6 '()))
                    #(7 8 9) #(7 30 2) #(10 3 2)
                    (hash 'five 5) (hash 'one 1 'two 2)
                    (set 'three 'four) (set 3 4)
                    (thing 'one 'two) (thing 1 2)
                    identity identity
                    (box 'box) (box 'box)
                    )
    (check-equal?
      (sort vals any<?)
      sorted-vals)
    ))
