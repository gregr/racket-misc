#lang racket/base
(provide
  (struct-out cursor)

  ;; cursor notation
  ::0   ; create a new cursor focusing on the given datum
  ::^   ; ascend one level or optionally to the same depth as another cursor
  ::^.  ; ascend as in ::^ then retrieve the focus
  ::^*  ; ascend completely
  ::^*. ; ascend completely then retrieve the focus
  ::@   ; descend through a given path
  ::@?  ; like ::@ but return left (unmatchable path) or right (cursor)
  ::.   ; descend as in ::@ then retrieve the focus
  ::=   ; descend as in ::@, refocus with a new value, then ascend to the
        ; original position
  ::~   ; like ::= but refocus by applying a transformation to the target
        ; focus
  ::@*  ; like ::@ but take each path component as an additional argument
  ::@?* ; like ::@* but return left (unmatchable path) or right (cursor)
  ::.*  ; like ::. but take each path component as an additional argument
  ::=*  ; like ::= but take each path component as an additional argument
  ::~*  ; like ::~ but take each path component as an additional argument
  ; like the above operators, but fill in empty paths during traversal using
  ; a constructor (which takes current focus and missing key as arguments)
  ::%@
  ::%.
  ::%=
  ::%~
  ::%@*
  ::%.*
  ::%=*
  ::%~*

  ;; lens operators
  :o  ; merge a list of paths into one path
  :.  ; follow all paths given as arguments and get the target value
  :=  ; follow all paths given as arguments and set the target value
  :~  ; follow all paths given as arguments and apply a transformation to the
      ; target value
  :.* ; like :. but the arguments taken are segments of a single path
  :=* ; like := but the arguments taken are segments of a single path
  :~* ; like :~ but the arguments taken are segments of a single path
  ; like the above operators, but fill in empty paths during traversal using
  ; a constructor (which takes current focus and missing key as arguments)
  :%.
  :%=
  :%~
  :%.*
  :%=*
  :%~*
  )

(require
  "either.rkt"
  "function.rkt"
  "list.rkt"
  "record.rkt"
  "sugar.rkt"
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
(def (cursor-descend% new cur key)
  focus = (cursor-focus cur)
  `(,_ ,p-set) = (ref+set focus)
  cur = (if (datum-has-key? focus key)
          cur (cursor-refocus cur (p-set focus key (new focus key))))
  (cursor-descend cur key))
(define (cursor-descend* cur keys)
  (foldl (flip cursor-descend) cur keys))
(define (cursor-descend%* new cur keys)
  (foldl (flip (curry cursor-descend% new)) cur keys))
(define (cursor-descend*/either cur keys)
  (match keys
    ('()             (right cur))
    ((cons key keys)
     (if (datum-has-key? (cursor-focus cur) key)
       (cursor-descend*/either (cursor-descend cur key) keys)
       (left (cons key keys))))))

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
(define (::%@ new cur path) (cursor-descend%* new cur path))
(define (::. cur path) (cursor-focus (::@ cur path)))
(define (::%. new cur path) (cursor-focus (::%@ new cur path)))
(define (::= cur val path)
  (cursor-ascend-to (cursor-refocus (::@ cur path) val)
                    cur))
(define (::%= new cur val path)
  (cursor-ascend-to (cursor-refocus (::%@ new cur path) val)
                    cur))
(define (::~ cur trans path)
  (let ((cur-next (::@ cur path)))
    (cursor-ascend-to
      (cursor-refocus cur-next (trans (cursor-focus cur-next)))
      cur)))
(define (::%~ new cur trans path)
  (let ((cur-next (::%@ new cur path)))
    (cursor-ascend-to
      (cursor-refocus cur-next (trans (cursor-focus cur-next)))
      cur)))

(define (::@* cur . path)       (::@ cur path))
(define (::@?* cur . path)      (::@? cur path))
(define (::.* cur . path)       (::. cur path))
(define (::=* cur val . path)   (::= cur val path))
(define (::~* cur trans . path) (::~ cur trans path))

(define (::%@* new cur . path)       (::%@ new cur path))
(define (::%.* new cur . path)       (::%. new cur path))
(define (::%=* new cur val . path)   (::%= new cur val path))
(define (::%~* new cur trans . path) (::%~ new cur trans path))

(define (:. src path)          (::. (::0 src) path))
(define (:= src val path)      (::.* (::= (::0 src) val path)))
(define (:~ src trans path)    (::.* (::~ (::0 src) trans path)))
(define (:.* src . path)       (:. src path))
(define (:=* src val . path)   (:= src val path))
(define (:~* src trans . path) (:~ src trans path))

(define (:%. new src path)          (::%. new (::0 src) path))
(define (:%= new src val path)      (::.* (::%= new (::0 src) val path)))
(define (:%~ new src trans path)    (::.* (::%~ new (::0 src) trans path)))
(define (:%.* new src . path)       (:%. new src path))
(define (:%=* new src val . path)   (:%= new src val path))
(define (:%~* new src trans . path) (:%~ new src trans path))

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
  (check-equal?
    (:%=* (lambda _ (hash 'default 0))
          (hash 'a 1 'b (hash 'c 3)) 5
          'b 'd 'e)
    (hash 'a 1 'b (hash 'c 3 'd (hash 'default 0 'e 5)))
    )
  )
