#lang racket/base
(provide
  class
  method-table
  o@
  object-empty
  object-method-names
  object-new
  object-understands?
  )

(require
  "dict.rkt"
  "record.rkt"
  "sugar.rkt"
  racket/dict
  racket/function
  )

(define ((unknown-method method) self . args)
  (error (format "accessed unknown method ~a of ~v with args: ~v"
                 method self args)))
(define unknown-understands? (const #f))
(record object methods default-method default-understands?)
(define object-empty (object hash-empty unknown-method unknown-understands?))
(def (object-inherit (object methods dm du?) (object prototype-methods _ _))
  prototype-methods =
  (if (hash? prototype-methods)
    prototype-methods (dict-join hash-empty prototype-methods))
  (object (dict-join prototype-methods methods) dm du?))
(define (object-new prototypes (methods hash-empty)
                    (default-method unknown-method)
                    (default-understands? unknown-understands?))
  (object-inherit (object methods default-method default-understands?)
                  (foldl object-inherit object-empty prototypes)))
(def (object-method-names (object methods _ _)) (dict-keys methods))
(def (object-understands? (object methods _ default-understands?) method)
  (or (default-understands? method) (dict-has-key? methods method)))
(define (o@ obj method . args)
  (lets (object methods default-method _) = obj
        (apply (dict-ref methods method (thunk (default-method method)))
               obj args)))

(define-syntax method-table
  (syntax-rules ()
    ((_) hash-empty)
    ((_ self (method-name method-params method-body ...) ...)
     (make-immutable-hash
       (list (cons 'method-name
                   (lambda (self . method-params) method-body ...)) ...)))))

(define-syntax class
  (syntax-rules ()
    ((_ self (constructor-params ...) (member-bindings ...) (prototypes ...)
        methods ...)
     (lambda (constructor-params ...)
       (let* (member-bindings ...)
         (object-new (list prototypes ...)
                     (method-table self methods ...)))))))

(module+ test
  (require
    rackunit
    racket/set
    )
  (lets
    c0 = (class self (one two) ((three (+ one two))
                                (four (+ three one)))
                ()
                (one () one)
                (three+ args (apply + three args))
                (five+ args (apply o@ self 'three+ two args)))
    c1 = (class self (motd one) ((two (+ one one)))
                ((c0 one two))
                (format (format-str . args)
                  (format format-str motd (apply o@ self 'five+ args))))
    obj0 = (c1 "welcome!" 1)
    obj1 = (object-new `(,obj0)
             (method-table self
               (three+ args (+ 100 (apply o@ obj0 'three+ args)))))
    default = (lambda (method)
                (lambda (self . args)
                  (format "received ~a with args: ~v" method args)))
    obj2 = (object-new (list obj1) (method-table) default (const #t))
    obj3 = (object-new (list obj2))
    (begin
      (check-equal? (method-table) hash-empty)
      (check-equal?
        (o@ obj0 'format "motd: ~a; result: ~a" 7 3)
        "motd: welcome!; result: 15")
      (check-equal?
        (o@ obj1 'format "~a; ~a" 1 2)
        "welcome!; 108")
      (check-equal?
        (o@ obj2 'format "~a; ~a" 1 2)
        "welcome!; 108")
      (check-equal?
        (o@ obj2 'format2 "~a; ~a" 1 2)
        "received format2 with args: '(\"~a; ~a\" 1 2)")
      (check-equal?
        (list->set (object-method-names obj1))
        (set 'one 'three+ 'five+ 'format))
      (check-equal?
        (list->set (object-method-names obj2))
        (list->set (object-method-names obj1)))
      (check-true (object-understands? obj1 'format))
      (check-true (object-understands? obj2 'format))
      (check-false (object-understands? obj1 'format2))
      (check-true (object-understands? obj2 'format2))
      (check-false (object-understands? obj3 'format2))
      )))
