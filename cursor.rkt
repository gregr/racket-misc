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

  ::** ; efficiently perform a sequence of cursor transformations

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

  :** ; efficiently perform a sequence of lens transformations and queries
  )

(require
  "either.rkt"
  "function.rkt"
  "list.rkt"
  "record.rkt"
  "sugar.rkt"
  racket/dict
  racket/function
  racket/list
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

(define (paths->deltas current paths)
  (define (compare cur path)
    (match* (cur path)
      (('() path) (list 0 path))
      ((cur '()) (list (length cur) '()))
      (((cons c0 cs) (cons p0 ps))
       (if (equal? c0 p0) (compare cs ps) (list (length cur) path)))))
  (match paths
    ('() '())
    ((cons path paths)
     (list* (compare current path) (paths->deltas path paths)))))

(module+ test
  (check-equal?
    (paths->deltas '() '((a b c d e f)
                              (a b c d e f)
                              (a b c d e f g h)
                              (a b d e f)
                              (a b d 1 2)
                              (a b c 1 2)
                              (z y x w v)
                              (z y x 5)
                              (z y x 5)))
    '((0 (a b c d e f))
      (0 ())
      (0 (g h))
      (6 (d e f))
      (2 (1 2))
      (3 (c 1 2))
      (5 (z y x w v))
      (2 (5))
      (0 ()))
    ))

(define (paths->transitions initial-path paths)
  (forl (list up down) <- (paths->deltas initial-path paths)
        up-trans = (if (= 0 up) identity
                     (lambda (cur) (last (iterate ::^ cur up))))
        down-trans = (if (null? down) identity
                       (lambda (cur) (::@ cur down)))
        (match up
          (0 down-trans)
          (_ (match down
               ('() up-trans)
               (_ (compose1 down-trans up-trans)))))))

(define (::**-process cursor initial-path ops paths)
  (forf cursor = cursor
        op <- ops
        transition <- (paths->transitions initial-path paths)
        (op (transition cursor))))

(define (::** cursor initial-path op&path-list)
  (apply ::**-process cursor initial-path (zip-default '(() ()) op&path-list)))

(module+ test
  (check-equal?
    (::** (::0 '(a (b c) d (e f g) h)) '()
      `((,(lambda (cur) (::=* cur 3)) (rest rest rest first rest rest first))
        (,(lambda (cur) (::=* cur 4)) (rest rest rest first rest first))
        (,(lambda (cur) (::=* cur 5)) (rest first rest first))
        (,identity ())
        (,identity (rest rest first))))
    (lets datum = '(a (b c) d (e f g) h)
          datum = (:= datum 3 '(rest rest rest first rest rest first))
          datum = (:= datum 4 '(rest rest rest first rest first))
          datum = (:= datum 5 '(rest first rest first))
          (::@ (::0 datum) '(rest rest first)))
    ))

(define-syntax :**-cont
  (syntax-rules (:. := :~ =)
    ((_ initial-path (ops ...) (paths ...) cursor (:= value path body ...))
     (:**-cont initial-path
       (ops ... (lambda (cur) (::=* cur value))) (paths ... path)
       cursor (body ...)))
    ((_ initial-path (ops ...) (paths ...) cursor (:~ update path body ...))
     (:**-cont initial-path
       (ops ... (lambda (cur) (::~* cur update))) (paths ... path)
       cursor (body ...)))
    ((_ initial-path (ops ...) (paths ...) cursor (:. name path body ...))
     (:**-cont initial-path (ops ... identity) (paths ... path) cursor
               (name = (::.* cursor) body ...)))
    ((_ initial-path () () cursor (lhs = rhs body ...))
     (lets lhs = rhs (:**-cont initial-path () () cursor (body ...))))
    ((_ initial-path () () cursor (body)) (values (::^*. cursor) body))
    ((_ initial-path () () cursor ()) (::^*. cursor))
    ((_ initial-path (ops ...) (paths ... final-path) cursor body)
     (let ((cursor (::**-process cursor initial-path
                                 (list ops ...) (list paths ... final-path))))
       (:**-cont final-path () () cursor body)))))

(define-syntax :**
  (syntax-rules ()
    ((_ datum body ...) (let ((cursor (::0 datum)))
                          (:**-cont '() () () cursor (body ...))))))

(module+ test
  (check-equal?
    (lets (values datum result) =
      (:** '(a (b c) d (e f g) h)
        := 3                           '(rest rest rest first rest rest first)
        :~ (lambda (val) (list val 4)) '(rest rest rest first rest first)
        := 5                           '(rest first rest first)
        :. one                         '(rest rest rest first rest first first)
        two = (list one one)
        := two                         '(rest rest rest first rest first first)
        :. result                      '(rest rest first)
        result)
      (list datum result))
    '((a (b 5) d (e ((f f) 4) 3) h) d)
    ))
