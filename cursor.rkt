#lang racket/base
(provide
  ;; cursor notation
  ::0   ; create a new cursor focusing on the given datum
  ::^   ; ascend one level or optionally to the same depth as another cursor
  ::^.  ; ascend as in ::^, then retrieve the focus
  ::^*  ; ascend completely
  ::^*. ; ascend completely, then retrieve the focus
  ::@*  ; descend through all paths in a given list of paths
  ::@   ; descend as in ::@*, but take each path as an additional argument
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

(require "list.rkt")
(require "record.rkt")
(require racket/dict)
(require racket/function)
(require racket/match)

(define (ref+set datum)
  (cond
    ((list? datum) (list list-ref list-set))
    ((dict? datum) (list dict-ref dict-set))))

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
(define (::@* cur paths) (cursor-descend* cur (:o paths)))
(define (::@ cur . paths) (::@* cur paths))
(define (::. cur . paths) (cursor-focus (::@* cur paths)))
(define (::= cur val . paths)
  (cursor-ascend-to (cursor-refocus (::@* cur paths) val)
                    cur))
(define (::~ cur trans . paths)
  (let ((cur-next (::@* cur paths)))
    (cursor-ascend-to
      (cursor-refocus cur-next (trans (cursor-focus cur-next)))
      cur)))

(define (:. src . paths)       (::. (::0 src) (:o paths)))
(define (:= src val . paths)   (::. (::= (::0 src) val (:o paths))))
(define (:~ src trans . paths) (::. (::~ (::0 src) trans (:o paths))))
(define (:.* src . path)       (:. src path))
(define (:=* src val . path)   (:= src val path))
(define (:~* src trans . path) (:~ src trans path))
