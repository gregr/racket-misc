#lang racket/base
(provide
  class
  method-table
  o@
  object-empty
  object-method-names
  object-new
  )

(require
  "dict.rkt"
  "record.rkt"
  "sugar.rkt"
  racket/dict
  )

(record object methods)
(define object-empty (object hash-empty))
(def (object-inherit (object methods) (object prototype-methods))
  prototype-methods =
  (if (hash? prototype-methods)
    prototype-methods (dict-join hash-empty prototype-methods))
  (object (dict-join prototype-methods methods)))
(define (object-new prototypes (methods hash-empty))
  (object-inherit (object methods)
                  (foldl object-inherit object-empty prototypes)))
(def (object-method-names (object methods)) (dict-keys methods))
(define (o@ obj method . args)
  (apply (hash-ref (object-methods obj) method) obj args))

(define-syntax method-table
  (syntax-rules ()
    ((_ this (method-name method-params method-body ...) ...)
     (make-immutable-hash
       (list (cons 'method-name
                   (lambda (this . method-params) method-body ...)) ...)))))

(define-syntax class
  (syntax-rules ()
    ((_ this (constructor-params ...) (member-bindings ...) (prototypes ...)
        methods ...)
     (lambda (constructor-params ...)
       (let* (member-bindings ...)
         (object-new (list prototypes ...)
                     (method-table this methods ...)))))))

(module+ test
  (require
    rackunit
    racket/set
    )
  (lets
    c0 = (class this (one two) ((three (+ one two))
                                (four (+ three one)))
                ()
                (one () one)
                (three+ args (apply + three args))
                (five+ args (apply o@ this 'three+ two args)))
    c1 = (class this (motd one) ((two (+ one one)))
                ((c0 one two))
                (format (format-str . args)
                  (format format-str motd (apply o@ this 'five+ args))))
    obj0 = (c1 "welcome!" 1)
    obj1 = (object-new `(,obj0)
             (method-table this
               (three+ args (+ 100 (apply o@ obj0 'three+ args)))))
    (begin
      (check-equal?
        (o@ obj0 'format "motd: ~a; result: ~a" 7 3)
        "motd: welcome!; result: 15")
      (check-equal?
        (o@ obj1 'format "~a; ~a" 1 2)
        "welcome!; 108")
      (check-equal?
        (list->set (object-method-names obj1))
        (set 'one 'three+ 'five+ 'format))
      )))
