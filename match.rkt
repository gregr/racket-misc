#lang racket/base
(provide
  lambda/destruct
  define/destruct
  )

(require (for-syntax racket/base))
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
