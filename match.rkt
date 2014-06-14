#lang racket/base
(provide
  lambda/destruct
  define/destruct
  cata
  lambda/cata
  define/cata
  match/cata
  for/fold/match/derived
  for/fold/match
  )

(require
  (for-syntax racket/base)
  racket/function
  racket/match
  )

(module+ test
  (require rackunit))

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

(define-syntax (for/fold/match/derived stx)
  (syntax-case stx ()
    ((_ original
        ((acc-pattern acc-init) ...)
        ((element-pattern seq) ...)
        body ...)
     (with-syntax (((acc ...)
                    (generate-temporaries #'((acc-pattern acc-init) ...)))
                   ((element ...)
                    (generate-temporaries #'((element-pattern seq) ...))))
      #'(for/fold/derived original ((acc acc-init) ...) ((element seq) ...)
          (match* (acc ...)
            ((acc-pattern ...)
             (match* (element ...)
               ((element-pattern ...) body ...)))))))))

(define-syntax (for/fold/match stx)
  (syntax-case stx ()
    ((_ accs seqs body ...)
     #`(for/fold/match/derived #,stx accs seqs body ...))))

(module+ test
  (check-equal?
    (for/fold/match
        (((cons sum _) (cons 0 'irrelevant)))
        (((cons a b) (list (cons 1 2) (cons 7 4))))
      (cons (+ a b sum) 'something))
    (cons 14 'something)))
