#lang racket/base
; algebraic effects and handlers as found in:
; http://www.eff-lang.org/
(provide
  effect
  handler
  handler-compose
  eff-handle
  @!
  @!!
  )

(require
  racket/control
  racket/function
  )

(module+ test
  (require
    "sugar.rkt"
    rackunit
    ))

(define-syntax effect
  (syntax-rules ()
    ((_ op-name ...)
     (make-immutable-hash (list (cons 'op-name (make-parameter
      (lambda _ (error (format "unhandled effect: ~a" 'op-name))))) ...)))))

(define-syntax handler-full
  (syntax-rules ()
    ((_ ((effect-expr (op-name op-param ... cont) op-body ...) ...)
        (return v return-body ...)
        (finally r finally-body ...))
     (lambda (body-thunk)
       (define (return v) return-body ...)
       (define (finally r) finally-body ...)
       (define tag (make-continuation-prompt-tag))
       (parameterize
         (((hash-ref effect-expr 'op-name)
           (lambda (op-param ...) (shift-at tag cont op-body ...))) ...)
         (finally (reset-at tag (return (body-thunk)))))))))

(define-syntax handler-finally
  (syntax-rules (finally)
    ((_ ops ret (finally r finally-body ...))
     (handler-full ops ret (finally r finally-body ...)))
     ;(let ((finally (lambda (r) finally-body ...))) main-expr))
    ((_ ops ret)
     (handler-finally ops ret (finally r r)))))

(define-syntax handler-return+finally
  (syntax-rules (return)
    ((_ ops (return v return-body ...) finally ...)
     (handler-finally ops (return v return-body ...) finally ...))
      ;(let ((return (lambda (v) return-body ...)))
        ;main-expr)
      ;finally ...))
    ((_ ops finally ...)
     (handler-return+finally ops (return v v) finally ...))))

(define-syntax handler-ops
  (syntax-rules ()
    ((_ (acc ...) (ee (on op ... k) ob ...) rest ...)
     (handler-ops (acc ... (ee (on op ... k) ob ...)) rest ...))
    ((_ ops rest ...)
     (handler-return+finally ops rest ...))))
(define-syntax handler
  (syntax-rules ()
    ((_ body ...) (handler-ops () body ...))))

(define-syntax @!!
  (syntax-rules ()
    ((_ effect-expr op-name-expr arg ...)
     (((hash-ref effect-expr op-name-expr)) arg ...))))
(define-syntax @!
  (syntax-rules ()
    ((_ effect-expr op-name arg ...) (@!! effect-expr 'op-name arg ...))))

(define-syntax eff-handle
  (syntax-rules ()
    ((_ handler-expr body ...) (handler-expr (thunk body ...)))))

(define (handler-compose h0 h1)
  (lambda (body-thunk) (h0 (thunk (h1 body-thunk)))))

; test cases based on examples found at:
; https://github.com/matijapretnar/eff/blob/master/examples/choice.eff

(module+ test
  (define (choice) (effect decide))
  (define (choose_all ch)
    (handler
      (ch (decide k) (append (k #t) (k #f)))
      (return v (list v))))
  )

(module+ test
  (check-equal?
    (lets
      ch = (choice)
      (eff-handle (choose_all ch)
        (lets
          x = (if (@! ch decide) 10 20)
          y = (if (@! ch decide) 0 5)
          (- x y))))
    '(10 5 20 15)
    ))

(module+ test
  (check-equal?
    (lets
      ch1 = (choice)
      ch2 = (choice)
      (eff-handle (choose_all ch1)
        (eff-handle (choose_all ch2)
          (lets
            x = (if (@! ch1 decide) 10 20)
            y = (if (@! ch2 decide) 0 5)
            (- x y)))))
    '((10 5) (20 15))
    ))

(module+ test
  (check-equal?
    (lets
      ch1 = (choice)
      ch2 = (choice)
      (eff-handle (choose_all ch2)
        (eff-handle (choose_all ch1)
          (lets
            y = (if (@! ch2 decide) 0 5)
            x = (if (@! ch1 decide) 10 20)
            (- x y)))))
    '((10 20) (5 15))
    ))

(module+ test
  (check-equal?
    (lets
      ch1 = (choice)
      ch2 = (choice)
      (eff-handle (choose_all ch2)
        (eff-handle (choose_all ch1)
          (lets
            x = (if (@! ch1 decide) 10 20)
            y = (if (@! ch2 decide) 0 5)
            (- x y)))))
    '((10 20) (10 15) (5 20) (5 15))
    ))
