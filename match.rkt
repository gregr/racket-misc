#lang racket/base
(provide
  lambda/destruct
  define/destruct
  cata
  lambda/cata
  define/cata
  match/cata
  )

(require (for-syntax racket/base))
(require racket/function)
(require racket/match)

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
