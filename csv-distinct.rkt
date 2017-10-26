#lang racket/base
(require
  "csv.rkt"
  (except-in racket/control set)
  racket/set)

(define argv (current-command-line-arguments))
(define argv-expected '#(CSV_NAME FIELD_INDEX OUT_NAME))

(when (not (= (vector-length argv-expected) (vector-length argv)))
  (error 'cmd-line-args (format "expected ~s; given ~s" argv-expected argv)))

(define csv-file-name (vector-ref argv 0))
(define field-index (string->number (vector-ref argv 1)))
(define output-file-name (vector-ref argv 2))

(define (print-distinct column-number)
  (define (yield record) (shift k (cons (list-ref record column-number) k)))
  (lambda (out)
    (lambda (in)
      (let loop ((count 1) (seen (set)) (next (reset (and ((csv-records yield) in) #f))))
        (when (= 0 (remainder count 100000))
          (printf "processed ~s rows\n" count)
          (flush-output out))
        (when next
          (define field (car next))
          (define k (cdr next))
          (define (continue seen) (loop (+ 1 count) seen (k #t)))
          (if (not (set-member? seen field))
            (begin (printf "~s\n" `(new distinct column value: ,field))
                   (fprintf out "~s\n" field)
                   (continue (set-add seen field)))
            (continue seen)))))))

;; Print the distinct values of the indexed field.
(time (call-with-output-file
        output-file-name
        (lambda (out) (call-with-input-file
                        (expand-user-path csv-file-name)
                        (lambda (in)
                          (read-line in 'any) ;; Skip header.
                          (((print-distinct field-index) out) in))))))
