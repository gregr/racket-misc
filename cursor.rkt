#lang racket/base
(provide
  (struct-out cursor)

  ;; cursor notation
  ::0   ; create a new cursor focusing on the given datum
  ::^   ; ascend one level or optionally to the same depth as another cursor
  ::^.  ; ascend as in ::^, then retrieve the focus
  ::^*  ; ascend completely
  ::^*. ; ascend completely, then retrieve the focus
  ::@*  ; descend through all paths in a given list of paths
  ::@   ; descend as in ::@*, but take each path as an additional argument
  ::@?  ; like ::@?* but return left (unmatchable path) or right (cursor)
  ::@?* ; like ::@* but return left (unmatchable path) or right (cursor)
  ::.   ; descend as in ::@, then retrieve the focus
  ::=   ; descend as in ::@, refocus with a new value, then ascend to the
        ; original position
  ::~   ; like ::=, but refocus by applying a transformation to the target
        ; focus

  ;; lens operators
  :o  ; merge a list of paths into one path
  :.  ; follow all paths given as arguments and get the target value
  :=  ; follow all paths given as arguments and set the target value
  :~  ; follow all paths given as arguments and apply a transformation to the
      ; target value
  :.* ; like :. but the arguments taken are segments of a single path
  :=* ; like := but the arguments taken are segments of a single path
  :~* ; like :~ but the arguments taken are segments of a single path
  )

(require
  "either.rkt"
  "list.rkt"
  "record.rkt"
  racket/dict
  racket/function
  racket/match
  )

(module+ test
  (require rackunit))

(define (ref+set datum)
  (cond
    ((pair? datum) (list list-ref-key list-set-key))
    ((dict? datum) (list dict-ref dict-set))))
(define (datum-has-key? datum key)
  ((cond
     ((pair? datum) list-has-key?)
     ((dict? datum) dict-has-key?)
     (else (const #f))) datum key))

(record cursor focus trail ancestors)
(define (cursor-new datum) (cursor datum '() '()))
(define (cursor-refocus cur new-focus) (dict-set cur 'focus new-focus))
(define (cursor-ascend cur)
  (match cur
    ((cursor focus (cons key keys) (cons parent ancestors))
     (match-let* ((`(,_ ,p-set) (ref+set parent))
                  (new-focus (p-set parent key focus)))
       (cursor new-focus keys ancestors)))))
(define (cursor-ascend-to cur-src cur-tgt)
  (for/fold ((cur cur-src))
            ((idx (in-range (- (length (cursor-trail cur-src))
                               (length (cursor-trail cur-tgt))))))
    (cursor-ascend cur)))
(define (cursor-ascend* cur) (cursor-ascend-to cur (cursor-new '())))
(define (cursor-descend cur key)
  (match cur
    ((cursor focus keys ancestors)
     (match-let* ((`(,p-ref ,_) (ref+set focus))
                  (new-focus (p-ref focus key)))
       (cursor new-focus (cons key keys) (cons focus ancestors))))))
(define (cursor-descend* cur keys)
  (foldl (flip cursor-descend) cur keys))
(define (cursor-descend*/either cur keys)
  (match keys
    ('()             (right cur))
    ((cons key keys)
     (if (datum-has-key? (cursor-focus cur) key)
       (cursor-descend*/either (cursor-descend cur key) keys)
       (left (cons key keys))))))

(define ((flip proc) x y) (proc y x))

(define :o (curry apply append))

(define ::0 cursor-new)
(define ::^
  (case-lambda
    ((cur) (cursor-ascend cur))
    ((cur-src cur-tgt) (cursor-ascend-to cur-src cur-tgt))))
(define (::^. cur-src cur-tgt)
  (cursor-focus (cursor-ascend-to cur-src cur-tgt)))
(define ::^* cursor-ascend*)
(define ::^*. (compose1 cursor-focus cursor-ascend*))

(define (::@ cur path) (cursor-descend* cur path))
(define (::@? cur path) (cursor-descend*/either cur path))
(define (::. cur path) (cursor-focus (::@ cur path)))
(define (::= cur val path)
  (cursor-ascend-to (cursor-refocus (::@ cur path) val)
                    cur))
(define (::~ cur trans path)
  (let ((cur-next (::@ cur path)))
    (cursor-ascend-to
      (cursor-refocus cur-next (trans (cursor-focus cur-next)))
      cur)))

(define (::@* cur . path)       (::@ cur path))
(define (::@?* cur . path)      (::@? cur path))
(define (::.* cur . path)       (::. cur path))
(define (::=* cur val . path)   (::= cur val path))
(define (::~* cur trans . path) (::~ cur trans path))

(define (:. src path)          (::. (::0 src) path))
(define (:= src val path)      (::.* (::= (::0 src) val path)))
(define (:~ src trans path)    (::.* (::~ (::0 src) trans path)))
(define (:.* src . path)       (:. src path))
(define (:=* src val . path)   (:= src val path))
(define (:~* src trans . path) (:~ src trans path))

(module+ test
  (record foo x y)
  (record bar a b)
  (define foobar (foo (bar 5 1) '(one two three)))
  (check-equal? (:.* foobar 'x 'b)
                1)
  (check-equal? (:.* foobar 'y 'rest 'first)
                'two)
  (check-equal? (:.* (:~* foobar (curry + 3) 'x 'a) 'x 'a)
                8)
  (check-equal? (:=* 'src 'tgt) 'tgt)
  )
