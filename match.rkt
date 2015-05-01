#lang racket/base
(provide
  lambda/destruct
  define/destruct
  cata
  lambda/cata
  define/cata
  match/cata
  match-let1+values
  for/fold/match/derived
  for*/fold/match/derived
  for/fold/match
  for*/fold/match
  for/list/match
  for*/list/match
  )

(require
  (for-syntax racket/base)
  racket/function
  racket/match
  )

(module+ test
  (require rackunit))

(define-syntax match-let1+values
  (syntax-rules (values)
    ((_ (values vals ...) val-expr body ...)
     (let-values (((vals ...) val-expr)) body ...))
    ((_ pattern val-expr body ...)
     (match-let ((pattern val-expr)) body ...))))

(define-syntax (lambda/destruct stx)
  (syntax-case stx ()
    ((_ (pattern ...) body ...)
     (with-syntax (((argname ...)
                    (generate-temporaries #'(pattern ...))))
      #`(lambda (argname ...)
          (match* (argname ...)
            ((pattern ...) body ...)))))))

(define-syntax define/destruct
  (syntax-rules ()
    ((_ (name pattern ...) body ...)
     (define name
       (lambda/destruct (pattern ...) body ...)))))

(module+ test
  (define/destruct (list-2nd-of-4 (list a b c d)) b)
  (check-equal? (list-2nd-of-4 '(a b c d)) 'b))

(define current-cata
  (make-parameter
    (lambda args (error "use of current-cata not in a catamorphism" args))))

(define-match-expander cata
  (lambda (stx)
    (syntax-case stx ()
      ((_ pats ...)
       #'(app (current-cata) pats ...)))))

(define-syntax (lambda/cata stx)
  (syntax-case stx ()
    ((_ (pattern body ...) ...)
     (with-syntax (((cata-name) (generate-temporaries #'(cata-name))))
      #'((thunk
           (define (cata-name value)
             (parameterize ((current-cata cata-name))
              (match value (pattern body ...) ...)))
           cata-name))))))

(define-syntax define/cata
  (syntax-rules ()
    ((_ name body ...)
     (define name (lambda/cata body ...)))))

(define-syntax match/cata
  (syntax-rules ()
    ((_ value body ...)
     ((lambda/cata body ...) value))))

(module+ test
  (check-equal?
    (match/cata (list 1 2 3 4)
      ('()               '())
      ((cons a (cata b)) (cons (+ a 1) b)))
    (list 2 3 4 5)))

(define-syntax (for_/fold/match/derived-cont stx)
  (syntax-case stx ()
    ((_ cont original acc for-clauses ()
        (source ...) (pattern ...) body ...)
      #'(cont original acc for-clauses
          (match* (source ...) ((pattern ...) body ...))))
    ((_ cont original acc (for-clause ...) ((pat seq) pat-for-clause ...)
        (source ...) (pattern ...) body ...)
     (with-syntax (((elem) (generate-temporaries #'(pat))))
     #'(for_/fold/match/derived-cont
         cont original acc
         (for-clause ... (elem seq))
         (pat-for-clause ...)
         (source ... elem) (pattern ... pat)
         body ...)))
    ((_ cont original acc (for-clause ...) (kw expr pat-for-clause ...)
        (source ...) (pattern ...) body ...)
     #'(for_/fold/match/derived-cont
         cont original acc
         (for-clause ... kw (match* (source ...) ((pattern ...) expr)))
         (pat-for-clause ...)
         (source ...) (pattern ...)
         body ...))))

(define-syntax (for_/fold/match/derived stx)
  (syntax-case stx ()
    ((_ cont original
        ((acc-pattern acc-init) ...)
        (pat-for-clause ...)
        body ...)
     (with-syntax (((acc ...)
                    (generate-temporaries #'((acc-pattern acc-init) ...))))
      #'(for_/fold/match/derived-cont
          cont original ((acc acc-init) ...)
          () (pat-for-clause ...)
          (acc ...) (acc-pattern ...)
          body ...)))))

(define-syntax for/fold/match/derived
  (syntax-rules ()
    ((_ rest ...) (for_/fold/match/derived for/fold/derived rest ...))))

(define-syntax for*/fold/match/derived
  (syntax-rules ()
    ((_ rest ...) (for_/fold/match/derived for*/fold/derived rest ...))))

(define-syntax (for/fold/match stx)
  (syntax-case stx ()
    ((_ accs seqs body ...)
     #`(for/fold/match/derived #,stx accs seqs body ...))))

(define-syntax (for*/fold/match stx)
  (syntax-case stx ()
    ((_ accs seqs body ...)
     #`(for*/fold/match/derived #,stx accs seqs body ...))))

(module+ test
  (check-equal?
    (for/fold/match
        (((cons sum _) (cons 0 'irrelevant)))
        (((cons a b) (list (cons 1 2) (cons 7 4))))
      (cons (+ a b sum) 'something))
    (cons 14 'something)))

(module+ test
  (check-equal?
    (for/fold/match
        (((cons sum _) (cons 0 'irrelevant)))
        (((cons a b) (list (cons 1 2) (cons 7 4)))
         #:when #t
         (c (list 10 20))
         )
      (cons (+ a b c sum) 'something))
    (cons (* 2 (+ 1 2 7 4 10 20)) 'something)))

(module+ test
  (check-equal?
    (for/fold/match
        (((list junk sum) (list '() 0)))
        ((x (list 1 2 3))
         ((list y tag) '((4 i) (5 j) (6 k)))
         #:when (even? y)
         (z '(a b c))
         )
      (list (cons (list tag z) junk) (+ x y sum)))
    (list (reverse '((i a) (i b) (i c) (k a) (k b) (k c))) (* 3 (+ 1 3 4 6)))))

(module+ test
  (check-equal?
    (for*/fold/match
        ((results '()))
        (((list x y) '((1 2) (3 4)))
         (sym '(a b)))
      (cons (list (+ x y) sym) results))
    '((7 b) (7 a) (3 b) (3 a))
    ))

(define-syntax (for_/list/match stx)
  (syntax-case stx ()
    ((_ cont seqs body ...)
     (with-syntax ((original stx)
                   (list-acc (datum->syntax #'this 'list-acc)))
     #'(reverse
         (cont original ((list-acc '())) seqs
          (cons (begin body ...) list-acc)))))))

(define-syntax for/list/match
  (syntax-rules ()
    ((_ rest ...) (for_/list/match for/fold/match/derived rest ...))))

(define-syntax for*/list/match
  (syntax-rules ()
    ((_ rest ...) (for_/list/match for*/fold/match/derived rest ...))))

(module+ test
  (check-equal?
    (for/list/match
      (((list a b) '((a b) (c d)))
       ((list c d) '((1 2) (3 4))))
      (list a b c d))
    '((a b 1 2) (c d 3 4))))

(module+ test
  (check-equal?
    (for/list/match
        ((x (list 1 2 3))
         ((list y tag) '((4 i) (5 j) (6 k)))
         #:when (even? y)
         (z '(a b c))
         )
      (list tag z (+ x y)))
    '((i a 5) (i b 5) (i c 5) (k a 9) (k b 9) (k c 9))))

(module+ test
  (check-equal?
    (for*/list/match
      (((list a b) '((a b) (c d)))
       (c '(1 2)))
      (list a b c))
    '((a b 1) (a b 2) (c d 1) (c d 2))))
