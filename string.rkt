#lang racket/base
(provide
  make-immutable-string
  string-insert
  string-range-remove
  string-range-replace
  string-range-transform
  string-remove
  )

(require
  racket/function
  )

(module+ test
  (require rackunit))

(define (make-immutable-string count char)
  (string->immutable-string (make-string count char)))

(module+ test
  (check-equal?
    (make-immutable-string 3 #\+)
    "+++"))

(define ((string-range-transform f) str start end)
  (string-append (substring str 0 start)
                 (f (substring str start end))
                 (substring str end (string-length str))))

(define (string-range-replace new) (string-range-transform (const new)))

(define (string-insert str idx new-str)
  ((string-range-replace new-str) str idx idx))

(module+ test
  (check-equal?
    (string-insert "abcde" 0 "fgh")
    "fghabcde")
  (check-equal?
    (string-insert "abcde" 2 "fgh")
    "abfghcde")
  (check-equal?
    (string-insert "abcde" 5 "fgh")
    "abcdefgh")
  )

(define string-range-remove (string-range-replace ""))

(module+ test
  (check-equal?
    (string-range-remove "abcdefg" 2 4)
    "abefg"))

(define (string-remove str idx)
  (if (and (<= 0 idx) (< idx (string-length str)))
    (string-range-remove str idx (+ idx 1))
    str))
