#lang racket/base
(provide
  encode-base32hex
  decode-base32hex
  )

(require
  "dict.rkt"
  "sugar.rkt"
  math/base
  racket/dict
  racket/function
  racket/list
  )

(define (list->chunks xs size)
  (letn loop (values rchunks xs) = (values '() xs)
    (if (<= size (length xs))
      (lets (values prefix suffix) = (split-at xs size)
            (loop (list* prefix rchunks) suffix))
      (values (reverse rchunks) xs))))

(def ((codec in-size out-size in-transform out-transform in-pad out-pad
             nchars-round) str)
  (values chunks final) = (list->chunks
                            (bytes->list (string->bytes/utf-8 str)) out-size)
  (bytes->string/utf-8
    (list->bytes
      (append*
        (forl chunk <- (if (empty? final) chunks (append chunks (list final)))
              in-npads = (if in-pad (length (filter (curry = in-pad) chunk)) 0)
              len = (- (length chunk) in-npads)
              bits = (sum (map (lambda (val offset)
                                 (arithmetic-shift (in-transform val)
                                                   (* in-size offset)))
                               (take chunk len)
                               (take (reverse (range out-size)) len)))
              nchars = (nchars-round (/ (* in-size len) out-size))
              (append (forl idx <- (range nchars)
                            high = (* (- in-size idx) out-size)
                            low = (- high out-size)
                            (out-transform (bitwise-bit-field bits low high)))
                      (if out-pad (make-list (- in-size nchars) out-pad)
                        '())))))))

(define base32hex-pad (char->integer #\=))
(define integer=>base32hex (list->vector (append (range 48 58) (range 65 87))))
(define base32hex=>integer (dict-invert integer=>base32hex))
(define encode-base32hex
  (codec 8 5 identity (curry dict-ref integer=>base32hex) #f base32hex-pad
         ceiling))
(define decode-base32hex
  (codec 5 8 (curry dict-ref base32hex=>integer) identity base32hex-pad #f
         floor))

(module+ test
  (require rackunit)
  (check-equal?
    (encode-base32hex "")
    "")
  (check-equal?
    (encode-base32hex "f")
    "CO======")
  (check-equal?
    (encode-base32hex "fo")
    "CPNG====")
  (check-equal?
    (encode-base32hex "foo")
    "CPNMU===")
  (check-equal?
    (encode-base32hex "foob")
    "CPNMUOG=")
  (check-equal?
    (encode-base32hex "fooba")
    "CPNMUOJ1")
  (check-equal?
    (encode-base32hex "foobar")
    "CPNMUOJ1E8======")
  (check-equal?
    (decode-base32hex "")
    "")
  (check-equal?
    (decode-base32hex "CO======")
    "f")
  (check-equal?
    (decode-base32hex "CPNG====")
    "fo")
  (check-equal?
    (decode-base32hex "CPNMU===")
    "foo")
  (check-equal?
    (decode-base32hex "CPNMUOG=")
    "foob")
  (check-equal?
    (decode-base32hex "CPNMUOJ1")
    "fooba")
  (check-equal?
    (decode-base32hex "CPNMUOJ1E8======")
    "foobar")
  (check-equal?
    (decode-base32hex (encode-base32hex "/one/twoλthree/fourλ"))
    "/one/twoλthree/fourλ")
  )
