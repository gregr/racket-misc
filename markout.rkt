#lang racket/base
(provide
  attr-loose-aligned
  attr-loose-indented
  attr-tight-aligned
  attr-tight-indented
  bordered-table
  bracketed-chain
  doc->styled-block
  expander-neither
  expander-width
  expander-height
  expander-both
  separated
  simple-bordered-table
  sizing-context-new
  sizing-context-new-default
  tight-pair
  vertical-list
  widths
  (struct-out doc-preformatted)
  (struct-out doc-atom)
  (struct-out doc-chain)
  (struct-out doc-expander)
  (struct-out doc-table)
  (struct-out doc-filler)
  (struct-out doc-frame)
  (struct-out frame-flexible)
  (struct-out frame-fixed)
  (struct-out frame-fixed-height)
  )

(require
  "cursor.rkt"
  "either.rkt"
  "list.rkt"
  "maybe.rkt"
  "record.rkt"
  "string.rkt"
  "sugar.rkt"
  "terminal.rkt"
  racket/dict
  racket/function
  racket/list
  racket/match
  )

(module+ test
  (require
    "test.rkt"
    rackunit
    ))

(define indent-width-default 2)
(define space-width-default 1)

(define (widths-memo-new) (make-hasheq))
(define (widths-memo-ref memo doc) (hash-ref memo doc (nothing)))
(define (widths-memo-set! memo doc ws) (hash-set! memo doc (just ws)))

(record sizing-context memo space-width indent-width)
(define (sizing-context-new space-width indent-width)
  (sizing-context (widths-memo-new) space-width indent-width))
(define (sizing-context-new-default)
  (sizing-context-new space-width-default indent-width-default))

(record chain-attr spaced? indented?)
(define attr-tight-aligned (chain-attr #f #f))
(define attr-tight-indented (chain-attr #f #t))
(define attr-loose-aligned (chain-attr #t #f))
(define attr-loose-indented (chain-attr #t #t))

(records frame-attr
  (frame-flexible coord)
  (frame-fixed rect)
  (frame-fixed-height coord height))

(record expander-attr width? height?)
(define expander-neither (expander-attr #f #f))
(define expander-width (expander-attr #t #f))
(define expander-height (expander-attr #f #t))
(define expander-both (expander-attr #t #t))

(records doc
  (doc-preformatted block)
  (doc-atom style str)
  (doc-chain style attr items)
  (doc-table style rows)
  (doc-filler min-sz max-w sz->block)
  (doc-frame style attr doc)
  (doc-expander attr doc)
  )

(define (tight-pair style lhs rhs)
  (doc-chain style attr-tight-aligned (list lhs rhs)))
(define (separated separator style items)
  (if (empty? items) '()
    (lets
      (list init-items last-item) = (list-init+last items)
      init-items = (forl
                     item <- init-items
                     (tight-pair style item separator))
      (append init-items (list last-item)))))
(def (bracketed-chain prefix suffix attr outer-style inner-style items)
  elements = (doc-chain inner-style attr items)
  suffix-chain = (doc-chain outer-style attr-tight-aligned (list elements suffix))
  (doc-chain outer-style attr-tight-indented (list prefix suffix-chain)))
(define (vertical-list style docs)
  (doc-table style (map list docs)))

(def (bordered-table
       inner-style style border-size divider-size
       (list t b ih
             l r iv
             tl tr bl br
             tj bj lj rj ij)
       rows)
  bs = border-size
  ds = divider-size
  (size bw bh) = border-size
  (size dw dh) = divider-size
  tbjs = (size dw bh)
  lrjs = (size bw dh)
  (list tl tr bl br tj bj lj rj ij) =
  (forl
    char <- (list tl tr bl br tj bj lj rj ij)
    sz <- (list bs bs bs bs tbjs tbjs lrjs lrjs ds)
    (doc-preformatted (styled-block-fill style char sz)))
  (list t b ih) =
  (forl
    char <- (list t b ih)
    height <- (list bh bh dh)
    (doc-filler (size 0 height) 0 (curry styled-block-fill style char)))
  (list l r iv) =
  (forl
    char <- (list l r iv)
    width <- (list bw bw dw)
    (doc-filler (size width 0) width (curry styled-block-fill style char)))
  num-cols = (if (empty? rows) 0 (length (first rows)))
  add-between-around = (lambda (xs l i r)
                         (append (list l) (add-between xs i) (list r)))
  hdiv = (add-between-around (make-list num-cols ih) lj ij rj)
  top = (add-between-around (make-list num-cols t) tl tj tr)
  bottom = (add-between-around (make-list num-cols b) bl bj br)
  rows = (forl row <- rows (add-between-around row l iv r))
  rows = (add-between-around rows top hdiv bottom)
  (doc-table inner-style rows))

(define (simple-bordered-table inner-style style char rows)
  (bordered-table inner-style style
                  (size 1 1) (size 1 1) (make-list 15 char) rows))

(define (separator-count xs) (max 0 (- (length xs) 1)))

(def (width-scored-deltas w-start ws)
  ws = (sort ws <)
  len = (length ws)
  (reverse
    (car (forf
           (list scores offset height) = (list '() w-start len)
           wmax <- ws
           wdelta = (max 0 (- wmax offset))
           score = height
           offset = (max wmax offset)
           scores = (if (> wdelta 0) (cons (cons score wdelta) scores) scores)
           (list scores offset (- height 1))))))

(define (width-allocation-order col-scores)
  (define (head-pair-> c0 c1)
    (match* ((cadr c0) (cadr c1))
      (('() '()) #f)
      ((_ '()) #t)
      (((cons (cons l0 r0) t0) (cons (cons l1 r1) t1))
       (if (> l0 l1) #t
         (if (< l0 l1) #f
           (head-pair-> (list #f t0) (list #f t1)))))))
  (letsn loop (choices = '() scores = col-scores)
    scores = (filter-not (compose1 empty? cadr) scores)
    scores = (sort scores head-pair->)
    (match scores
      ('() (reverse choices))
      ((cons (list idx (cons (cons _ wdelta) rest)) losers)
       (loop (cons (cons idx wdelta) choices)
             (cons (list idx rest) losers))))))

(def (widths ctx doc)
  (sizing-context memo space-width indent-width) = ctx
  widths-grouped = (lambda (xs) (zip-default '(() () () () () ())
                                             (map (curry widths ctx) xs)))
  expander-attr-aggregate = (lambda (eas)
    (forf
      (expander-attr width? height?) = (expander-attr #f #f)
      (expander-attr w? h?) <- eas
      (expander-attr (or w? width?) (or h? height?))))
  (match (widths-memo-ref memo doc)
    ((just result) result)
    ((nothing)
     (lets
       result =
       (match doc
         ((doc-preformatted block)
          (lets
            sz = (styled-block-size block)
            (size width height) = sz
            (list sz width expander-neither '() '() '())))
         ((doc-atom _ str)
          (lets
            len = (string-length str)
            (list (size len 1) len expander-neither '() '() '())))
         ((doc-chain _ (chain-attr spaced? indented?) items)
          (lets
            (list min-sizes max-widths eas _ _ _) = (widths-grouped items)
            ea = (expander-attr-aggregate eas)
            min-widths = (map size-w min-sizes)
            spacing = (if spaced? (* space-width (separator-count items)) 0)
            indent = (if indented? indent-width 0)
            (list _ min-width) =
            (forf
              (list prefix-width final-min-width) = (list 0 0)
              min-width <- min-widths
              min-prefix = (min prefix-width indent)
              width = (+ min-prefix min-width)
              (list (+ spacing width) (max width final-min-width)))
            max-width = (+ spacing (sum max-widths))
            min-width = (min min-width max-width)
            (list (size min-width 0) max-width ea '() '() '())))
         ((doc-table _ rows)
          (lets
            cols = (zip rows)
            (list min-widths max-widths eas scores) =
            (zip-default '(() () () ())
              (forl
                col <- cols
                (list min-sizes max-widths eas _ _ _) = (widths-grouped col)
                ea = (expander-attr-aggregate eas)
                min-widths = (map size-w min-sizes)
                min-width = (apply max min-widths)
                max-width = (apply max max-widths)
                scored-deltas = (width-scored-deltas min-width max-widths)
                (list min-width max-width ea scored-deltas)))
            ea = (expander-attr-aggregate eas)
            min-width = (sum min-widths)
            max-width = (sum max-widths)
            scores = (zip* (range (length scores)) scores)
            allocation-order = (width-allocation-order scores)
            (list (size min-width 0) max-width ea
                  max-widths eas allocation-order)))
         ((doc-filler min-sz max-w _)
          (list min-sz max-w expander-neither '() '() '()))
         ((doc-frame _ fattr doc)
          (lets
            (list _ max-width ea _ _ _) = (widths ctx doc)
            flexible = (list (size 0 0) max-width ea '() '() '())
            (expander-attr w? h?) = ea
            (match fattr
              ((frame-flexible _) flexible)
              ((frame-fixed (rect _ (size width height)))
               (list (size width 0) width expander-neither '() '() '()))
              ((frame-fixed-height _ _)
               (:=* flexible (expander-attr w? #f) 'rest 'rest 'first)))))
         ((doc-expander attr doc)
          (lets
            (list min-sz max-w _ _ _ _) = (widths ctx doc)
            (list min-sz max-w attr '() '() '()))))
       _ = (widths-memo-set! memo doc result)
       result))))

(def (table-col-widths available maxes eas)
  col-count = (length maxes)
  cols = (list->index-dict (make-list (length maxes) 0))
  pair<= = (fn ((cons _ a) (cons _ b)) (<= a b))
  max-indexed = (list->index-list maxes)
  (list col-widths available) =
  (forf
    (list col-widths avail) = (list cols available)
    count <- (reverse (range 1 (+ 1 col-count)))
    (cons idx maxw) <- (sort max-indexed pair<=)
    alloc = (quotient avail count)
    used = (min maxw alloc)
    col-widths = (dict-update col-widths idx (curry + used))
    (list col-widths (- avail used)))
  ews = (map expander-attr-width? eas)
  ew-count = (length (filter identity ews))
  (list col-widths _ _) =
  (forf
    (list col-widths avail count) = (list col-widths available ew-count)
    #:break (= 0 count)
    idx <- (range (length ews))
    w? <- ews
    used = (if w? (quotient avail count) 0)
    count = (if w? (- count 1) count)
    col-widths = (dict-update col-widths idx (curry + used))
    (list col-widths (- avail used) count))
  (index-dict->list col-widths))

(module+ test
  (define bw-test 3)
  (define dw-test 2)
  (define (unbordered-test-table style rows)
    (doc-table style rows))
  (define (bordered-test-table sty rows)
    (bordered-table sty (style 'default 'default #f #f #f #t)
                    (size bw-test 1) (size dw-test 1)
                    (list #\= #\= #\-
                          #\# #\# #\|
                          #\^ #\> #\< #\v
                          #\+ #\+ #\+ #\+ #\+)
                    rows))
  )

(module+ test
  (lets
    style = style-empty
    ctx = (sizing-context-new-default)
    chain-empty = (bracketed-chain (doc-atom style "[") (doc-atom style "]")
                                   attr-loose-aligned style style '())
    chain-empties = (doc-chain style attr-loose-aligned
                               (list chain-empty chain-empty))
    chain-empties-tail = (doc-chain style attr-tight-aligned
                                    (list chain-empties (doc-atom style "}")))
    chain-empties-tail-head = (doc-chain style attr-tight-indented
                                         (list (doc-atom style "{")
                                               chain-empties-tail))
    chain-pair = (lambda (a b) (bracketed-chain
                    (doc-atom style "{") (doc-atom style "}")
                    attr-loose-aligned style style (list a b)))
    chain-small = (chain-pair chain-empty chain-empty)
    chain-nested =
    (chain-pair
      chain-empty
      (chain-pair
        chain-empty
        (chain-pair chain-empty (chain-pair chain-empty chain-empty))))
    chain-nested-vlist =
    (vertical-list
      style-empty
      (list chain-nested))
    items-0 = (list (doc-atom style "hello") (doc-atom style "world"))
    chain-0 = (bracketed-chain (doc-atom style "test(") (doc-atom style ")")
                               attr-loose-aligned style style items-0)
    items-1 = (list (doc-atom style "testing") chain-0)
    chain-1 = (bracketed-chain (doc-atom style "[") (doc-atom style "]")
                               attr-loose-aligned style style items-1)
    table-0 = (bordered-test-table
                style (list (list chain-0 chain-1) (list chain-0 chain-0)))
    table-1 = (bordered-test-table
                style-empty (list (list chain-0 chain-1)
                                  (list (doc-expander expander-both chain-0) chain-0)))
    table-2 = (bordered-test-table
                style-empty (list (list chain-0 (doc-expander expander-both chain-1))
                                  (list (doc-expander expander-both chain-0) chain-0)))
    d0 = (- 17 7)
    d1 = (- 27 9)
    padding = (+ (* 2 bw-test) dw-test)
    max-width = (+ 17 27 padding)
    table-0-widths = (widths ctx table-0)
    (list t0c-min t0c-snug t0c-extra t0c-meh) =
    (lets
      (list _ _ _ cmaxes ceas _) = table-0-widths
      calc = (lambda (avail) (table-col-widths avail cmaxes ceas))
      (list (calc (+ 7 8 padding)) (calc max-width) (calc 100) (calc 35)))
    splice-border-widths =
    (lambda (xs)
      (append (list bw-test) (add-between xs dw-test) (list bw-test)))
    col-widths-for =
    (fn (doc full-width)
      (list _ _ _ maxes eas _) = (widths ctx doc)
      (table-col-widths full-width maxes eas))
    (begin
      (check-equal?
        (widths ctx chain-empty)
        (list (size 2 0) 2 expander-neither '() '() '())
        )
      (check-equal?
        (widths ctx chain-empties)
        (list (size 2 0) 5 expander-neither '() '() '())
        )
      (check-equal?
        (widths ctx chain-empties-tail)
        (list (size 2 0) 6 expander-neither '() '() '())
        )
      (check-equal?
        (widths ctx chain-empties-tail-head)
        (list (size 3 0) 7 expander-neither '() '() '())
        )
      (check-equal?
        (widths ctx chain-small)
        (list (size 3 0) 7 expander-neither '() '() '())
        )
      (check-equal?
        (widths ctx chain-nested)
        (list (size 6 0) 22 expander-neither '() '() '())
        )
      (check-equal?
        (widths ctx chain-nested-vlist)
        (list (size 6 0) 22 expander-neither (list 22) (list expander-neither) (list (cons 0 16)))
        )
      (check-equal?
        (widths ctx chain-0)
        (list (size 7 0) 17 expander-neither '() '() '())
        )
      (check-equal?
        (widths ctx chain-1)
        (list (size 8 0) 27 expander-neither '() '() '())
        )
      (check-equal?
        table-0-widths
        (list (size (+ 7 8 padding) 0) max-width
              expander-neither
              (splice-border-widths (list 17 27)) (make-list 5 expander-neither)
              (list (cons bw-test (- 17 8)) (cons 1 d0) (cons bw-test (- d1 (- 17 9)))))
        )
      (check-equal?
        t0c-min
        (splice-border-widths (list 7 8))
        )
      (check-equal?
        t0c-snug
        (splice-border-widths (list 17 27))
        )
      (check-equal?
        t0c-extra
        (splice-border-widths (list 17 27))
        )
      (check-equal?
        t0c-meh
        (splice-border-widths (list 13 14))
        )
      (check-equal?
        (col-widths-for table-1 (+ 17 27 padding))
        (splice-border-widths (list 17 27)))
      (check-equal?
        (col-widths-for table-1 100)
        (splice-border-widths (list (- 100 (+ 27 padding)) 27)))
      (check-equal?
        (col-widths-for table-2 101)
        (splice-border-widths (list 41 52)))
      )))

(define (space-block style sz) (styled-block-fill style #\space sz))
(define (block-append-horiz style prefix block)
  (styled-block-append-horizontal style #\space #f prefix block))
(define (block-append-vert style header block)
  (styled-block-append-vertical style #\space #t header block))
(define (block-expand style block sz)
  (styled-block-expand style #\space block sz #t #t))

(def (table->styled-block ctx style col-widths full-height rows)
  flex-frame = (curry doc-frame style (frame-flexible (coord 0 0)))
  row->height*cols = (fn (avail-height row)
    row = (forl
            doc <- row
            (match doc
              ((doc-filler _ _ _) (left doc))
              (_ (right doc))))
    cols = (forl
             col <- row
             col-width <- col-widths
             (either-map
               (compose1
                 (curry doc->styled-block ctx style
                        (size col-width avail-height))
                 flex-frame)
               col))
    sizes = (map (curry either-fold (const (size 0 0)) styled-block-size) cols)
    row-height = (max avail-height
                      (apply max 0 (map (fn ((size _ h)) h) sizes)))
    cols = (forl
             col <- cols
             col-width <- col-widths
             sz = (size col-width row-height)
             expand = (lambda (col) (block-expand style col sz))
             (either-fold
               (compose1 expand (curry doc->styled-block ctx style sz))
               expand col))
    (list row-height cols))
  erows =
    (forl
      row <- rows
      h? = (forf
             height? = #f
             col <- row
             (list _ _ (expander-attr _ h?) _ _ _) = (widths ctx col)
             (or height? h?))
      (if h? (left row) (right (row->height*cols 0 row))))
  finished-rows = (map right-x (filter right? erows))
  unfinished-row-count = (- (length rows) (length finished-rows))
  (list _ rows) =
  (zip-default
    '(() ())
    (if (= 0 unfinished-row-count) finished-rows
      (lets
        used-height = (sum (map car finished-rows))
        remaining-height = (- full-height used-height)
        shared = (quotient remaining-height unfinished-row-count)
        extra = (remainder remaining-height unfinished-row-count)
        indices = (range (length rows))
        (list extra-offset _) =
        (forf
          (list index count) = (list 0 0)
          idx <- indices
          erow <- erows
          #:break (>= count extra)
          (list (+ 1 idx) (if (left? erow) (+ count 1) 0)))
        (forl
          idx <- indices
          erow <- erows
          (match erow
            ((right result) result)
            ((left row)
             (row->height*cols
               (+ shared (if (< idx extra-offset) 1 0)) row)))))))
  (forf
    header = '()
    row <- rows
    row = (forf
            prefix = '()
            col <- row
            (block-append-horiz style prefix col))
    (block-append-vert style header row)))

(def (chain->blocks
       context style (chain-attr spaced? indented?) full-width items)
  (sizing-context _ space-width indent-width) = context
  space-new = (if spaced? (space-block style (size space-width 1)) '())
  prefix-new = (if indented? (space-block style (size indent-width 1)) '())
  (size space-width _) = (styled-block-size space-new)
  (size prefix-width _) = (styled-block-size prefix-new)
  after-indent-width = (- full-width prefix-width)
  next-state =
  (fn (prefix header avail-width item)
    blocks = (doc->blocks context (size avail-width 0) item)
    (list blocks first-block) = (list-init+last blocks)
    (size align-width _) = (styled-block-size prefix)
    alignment = (space-block style (size align-width 1))
    prefix = (block-append-horiz style prefix first-block)
    blocks =
    (forl
      block <- blocks
      (block-append-horiz style alignment block))
    blocks = (append blocks (list prefix))
    (cons prefix sub-header) = blocks
    header = (append sub-header header)
    (size pw _) = (styled-block-size prefix)
    (list prefix header (- full-width (+ pw space-width))))
  (list prefix header _) =
  (forf
    (list prefix header avail-width) = (list '() '() full-width)
    item <- items
    (list _ max-width _ _ _ _) = (widths context item)
    (if (>= avail-width (min max-width after-indent-width))
      (lets
        prefix = (if (empty? prefix) prefix
                   (block-append-horiz style prefix space-new))
        (next-state prefix header avail-width item))
      (lets
        header = (cons prefix header)
        (next-state prefix-new header after-indent-width item))))
  (cons prefix header))

(def (frame->blocks context style fattr full-sz doc)
  (size full-width full-height) = full-sz
  frame-rect = (fn (crd height)
    (list _ max-width _ _ _ _) = (widths context doc)
    width = (min max-width full-width)
    (rect crd (size width height)))
  (rect (coord x y) sz) =
  (match fattr
    ((frame-flexible crd) (frame-rect crd (void)))
    ((frame-fixed rct) rct)
    ((frame-fixed-height crd height) (frame-rect crd height)))
  (size width height) = sz
  inner-height = (if (void? height) full-height height)
  block = (doc->styled-block context style (size width inner-height) doc)
  (size bw bh) = (styled-block-size block)
  height = (if (void? height) bh height)
  sz = (size width height)
  block = (block-expand style block sz)
  pos = (coord (min x (max 0 (- bw width)))
               (min y (max 0 (- bh height))))
  block = (styled-block-sub block (rect pos sz))
  (list block))

(def (doc->blocks ctx full-size doc)
  (size full-width full-height) = full-size
  (match doc
    ((doc-preformatted block) (list block))
    ((doc-atom sty str)
     (list (styled-block (list (styled-line (list (styled-string sty str)))))))
    ((doc-chain sty attr items)
     (chain->blocks ctx sty attr full-width items))
    ((doc-table sty rows)
     (lets
       (list _ _ _ maxes eas _) = (widths ctx doc)
       col-widths = (table-col-widths full-width maxes eas)
       (list (table->styled-block ctx sty col-widths full-height rows))))
    ((doc-filler (size min-w min-h) _ sz->block)
     (list (sz->block (size (max full-width min-w) (max full-height min-h)))))
    ((doc-frame sty attr doc) (frame->blocks ctx sty attr full-size doc))
    ((doc-expander _ doc) (doc->blocks ctx full-size doc))))

(def (doc->styled-block ctx style full-size doc)
  blocks = (doc->blocks ctx full-size doc)
  (vertical-blocks->block style #\space #t blocks))

(module+ test
  (lets
    ctx = (sizing-context-new-default)
    style-outer = (style 'black 'red #f #f #f #f)
    style-0 = (style 'white 'blue #f #f #f #f)
    style-1 = (style 'red 'black #t #t #t #f)
    style-2 = (style 'white 'magenta #f #f #f #f)
    style-3 = (style 'default 'green #f #f #f #f)
    style-4 = (style 'default 'default #f #f #f #t)
    style-5 = (style 'default 'default #f #f #f #f)
    style-6 = (style 'cyan 'default #f #f #f #f)
    style-7 = (style 'cyan 'default #f #f #f #t)
    style-8 = (style 'black 'yellow #f #f #f #f)

    preformatted-0 = (doc-preformatted (styled-block-fill style-2 #\$ (size 4 3)))
    preformatted-1 = (doc-preformatted (styled-block-fill style-1 #\* (size 10 2)))

    atom-0 = (doc-atom style-0 "hello")
    atom-1 = (doc-atom style-0 "world")
    atom-2 = (doc-atom style-1 "and")
    atom-3 = (doc-atom style-0 "things")

    chain-empty = (bracketed-chain
                    (doc-atom style-0 "[") (doc-atom style-0 "]")
                    attr-loose-aligned style-0 style-0 '())
    chain-pair = (lambda (a b) (bracketed-chain
                    (doc-atom style-0 "{") (doc-atom style-0 "}")
                    attr-loose-aligned style-0 style-0 (list a b)))
    chain-nested =
    (chain-pair
      chain-empty
      (chain-pair
        chain-empty
        (chain-pair chain-empty (chain-pair chain-empty chain-empty))))
    chain-nested-vlist =
    (vertical-list
      style-empty
      (list chain-nested))
    items-0 = (list atom-0 atom-1 atom-2 atom-3)
    chain-0 = (bracketed-chain (doc-atom style-2 "test(") (doc-atom style-2 ")")
                               attr-loose-aligned style-3 style-4 items-0)

    items-1 = (list (doc-atom style-5 "testing") chain-0)
    chain-1 = (bracketed-chain (doc-atom style-5 "[") (doc-atom style-5 "]")
                               attr-loose-aligned style-6 style-7 items-1)
    table-0 = (bordered-test-table
                style-4 (list (list chain-0 chain-1) (list chain-0 chain-0)))
    table-1 = (bordered-test-table style-4 '())
    table-2 = (bordered-test-table style-4 (list '() '()))
    table-3 = (unbordered-test-table
                style-4 (list (list chain-0 chain-1)
                              (list preformatted-0 chain-0)))

    items-2 = (list chain-1 atom-2 atom-3)
    chain-2 = (bracketed-chain (doc-atom style-2 "(nested") (doc-atom style-2 ")")
                               attr-loose-aligned style-3 style-4 items-2)

    items-3 = (list chain-2 table-0 chain-1)
    chain-3 = (bracketed-chain (doc-atom style-6 "with-a-table(") (doc-atom style-6 ")")
                               attr-loose-aligned style-2 style-0 items-3)

    items-4 = (list atom-0 atom-1 preformatted-0)
    chain-4 = (bracketed-chain (doc-atom style-5 "[") (doc-atom style-5 "]")
                               attr-loose-aligned style-3 style-7 items-4)

    items-5 = (list atom-0 preformatted-1 atom-1 preformatted-0)
    chain-5 = (bracketed-chain (doc-atom style-5 "[") (doc-atom style-5 "]")
                               attr-loose-aligned style-3 style-7 items-5)

    frame-attr-0 = (frame-fixed (rect (coord 0 0) (size 20 6)))
    frame-0 = (doc-frame style-8 frame-attr-0 chain-5)
    frame-attr-1 = (frame-fixed (rect (coord 0 0) (size 8 6)))
    frame-1 = (doc-frame style-8 frame-attr-1 chain-5)
    frame-attr-2 = (frame-fixed (rect (coord 2 1) (size 8 6)))
    frame-2 = (doc-frame style-8 frame-attr-2 chain-5)
    frame-attr-3 = (frame-fixed (rect (coord 200 100) (size 8 6)))
    frame-3 = (doc-frame style-8 frame-attr-3 chain-5)
    frame-attr-4 = (frame-fixed-height (coord 0 0) 6)
    frame-4 = (doc-frame style-8 frame-attr-4 chain-5)
    frame-attr-5 = (frame-fixed-height (coord 1 1) 6)
    frame-5 = (doc-frame style-8 frame-attr-5 chain-5)
    frame-attr-6 = (frame-flexible (coord 1 1))
    frame-6 = (doc-frame style-8 frame-attr-6 chain-5)

    filler-0 = (doc-filler (size 4 1) 10
                           (curry styled-block-fill style-0 #\*))
    filler-1 = (doc-filler (size 1 1) 2
                           (curry styled-block-fill style-8 #\+))
    filler-2 = (doc-filler (size 4 1) 4
                           (curry styled-block-fill style-2 #\+))
    filler-3 = (doc-filler (size 1 1) 1
                           (curry styled-block-fill style-0 #\|))
    filler-4 = (doc-filler (size 1 1) 1
                           (curry styled-block-fill style-0 #\x))
    filler-5 = (doc-filler (size 1 1) 1
                           (curry styled-block-fill style-0 #\-))
    table-4 = (unbordered-test-table
                style-4
                (list (list filler-4 filler-5 filler-4 filler-5 filler-4)
                      (list filler-3 chain-0 filler-1 chain-1 filler-3)
                      (list filler-3 preformatted-0 filler-2 chain-0 filler-3)
                      (list filler-4 filler-5 filler-4 filler-5 filler-4)))
    table-5 = (unbordered-test-table
                style-4 (list (list (doc-expander expander-both chain-0) chain-1)
                              (list preformatted-0 chain-0)))

    test-equalities =
    (list
      (list
        (list (size 2 0) filler-0)
        "\e[0m\e[27;25;24;22;44;37m****\e[0m")
      (list
        (list (size 6 2) filler-0)
        "\e[0m\e[27;25;24;22;44;37m******\e[0m\n\e[27;25;24;22;44;37m******\e[0m")
      (list
        (list (size 12 4) filler-0)
        "\e[0m\e[27;25;24;22;44;37m************\e[0m\n\e[27;25;24;22;44;37m************\e[0m\n\e[27;25;24;22;44;37m************\e[0m\n\e[27;25;24;22;44;37m************\e[0m")
      (list
        (list (size 30 10) table-4)
        "\e[0m\e[27;25;24;22;44;37mx------------xxxx------------x\e[0m\n\e[27;25;24;22;44;37m|\e[45mtest(\e[7;49;39m       \e[27;43;30m++++\e[49;39m[testing\e[7m    \e[27;44;37m|\e[0m\n\e[27;25;24;22;44;37m|\e[42;39m  \e[44;37mhello\e[7;49;39m     \e[27;43;30m++++\e[49;36m \e[45;37mtest(\e[7;49;39m      \e[27;44;37m|\e[0m\n\e[27;25;24;22;44;37m|\e[42;39m  \e[44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;43;30m++++\e[49;36m \e[42;39m  \e[44;37mhello\e[7;49;39m    \e[27;44;37m|\e[0m\n\e[27;25;24;22;44;37m|\e[42;39m  \e[44;37mthings\e[45m)\e[7;49;39m   \e[27;43;30m++++\e[49;36m \e[42;39m  \e[44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[25;24;22;44;37m|\e[0m\n\e[27;25;24;22;44;37m|\e[7;49;39m            \e[27;43;30m++++\e[49;36m \e[42;39m  \e[44;37mthings\e[45m)\e[49;39m]\e[7m \e[27;44;37m|\e[0m\n\e[27;25;24;22;44;37m|\e[45m$$$$\e[7;49;39m        \e[27;45;37m++++test(\e[7;49;39m       \e[27;44;37m|\e[0m\n\e[27;25;24;22;44;37m|\e[45m$$$$\e[7;49;39m        \e[27;45;37m++++\e[42;39m  \e[44;37mhello\e[7;49;39m     \e[27;44;37m|\e[0m\n\e[27;25;24;22;44;37m|\e[45m$$$$\e[7;49;39m        \e[27;45;37m++++\e[42;39m  \e[44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37m|\e[0m\n\e[27;25;24;22;44;37m|\e[7;49;39m            \e[27;45;37m++++\e[42;39m  \e[44;37mthings\e[45m)\e[7;49;39m   \e[27;44;37m|\e[0m\n\e[27;25;24;22;44;37mx------------xxxx------------x\e[0m")
      (list
        (list (size 5 0) chain-nested)
        "\e[0m\e[27;25;24;22;44;37m{[]\e[41;30m   \e[0m\n\e[27;25;24;22;44;37m {[]\e[41;30m  \e[0m\n\e[27;25;24;22;44;37m  {[]\e[41;30m \e[0m\n\e[27;25;24;22;44;37m   {[]\e[0m\n\e[27;25;24;22;44;37m    []\e[0m\n\e[27;25;24;22;44;37m    }\e[41;30m \e[0m\n\e[27;25;24;22;44;37m   }}\e[41;30m \e[0m\n\e[27;25;24;22;44;37m }\e[41;30m    \e[0m")
      (list
        (list (size 1 0) chain-nested)
        "\e[0m\e[27;25;24;22;44;37m{[]\e[41;30m   \e[0m\n\e[27;25;24;22;44;37m {[]\e[41;30m  \e[0m\n\e[27;25;24;22;44;37m  {[]\e[41;30m \e[0m\n\e[27;25;24;22;44;37m   {[]\e[0m\n\e[27;25;24;22;44;37m    []\e[0m\n\e[27;25;24;22;44;37m    }\e[41;30m \e[0m\n\e[27;25;24;22;44;37m   }\e[41;30m  \e[0m\n\e[27;25;24;22;44;37m  }\e[41;30m   \e[0m\n\e[27;25;24;22;44;37m }\e[41;30m    \e[0m")
      (list
        (list (size 6 0) chain-nested-vlist)
        "\e[0m\e[27;25;24;22;44;37m{[]\e[49;39m   \e[0m\n\e[27;25;24;22;44;37m {[]\e[49;39m  \e[0m\n\e[27;25;24;22;44;37m  {[]\e[49;39m \e[0m\n\e[27;25;24;22;44;37m   {[]\e[0m\n\e[27;25;24;22;44;37m    []\e[0m\n\e[27;25;24;22;44;37m    }}\e[0m\n\e[27;25;24;22;44;37m  }}\e[49;39m  \e[0m")
      (list
        (list (size 10 0) table-1)
        "\e[0m\e[7;25;24;22;49;39m^^^>>>\e[0m\n\e[7;25;24;22;49;39m<<<vvv\e[0m")
      (list
        (list (size 10 0) table-2)
        "\e[0m\e[7;25;24;22;49;39m^^^>>>\e[0m\n\e[7;25;24;22;49;39m++++++\e[0m\n\e[7;25;24;22;49;39m<<<vvv\e[0m")
      (list
        (list (size 25 0) table-3)
        "\e[0m\e[27;25;24;22;45;37mtest(\e[7;49;39m       \e[27m[testing\e[7m     \e[0m\n\e[27;25;24;22;42;39m  \e[44;37mhello\e[7;49;39m     \e[27;36m \e[45;37mtest(\e[7;49;39m       \e[0m\n\e[27;25;24;22;42;39m  \e[44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;36m \e[42;39m  \e[44;37mhello\e[7;49;39m     \e[0m\n\e[27;25;24;22;42;39m  \e[44;37mthings\e[45m)\e[7;49;39m   \e[27;36m \e[42;39m  \e[44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[0m\n\e[7;25;24;22;49;39m            \e[27;36m \e[42;39m  \e[44;37mthings\e[45m)\e[49;39m]\e[7m  \e[0m\n\e[27;25;24;22;45;37m$$$$\e[7;49;39m        \e[27;45;37mtest(\e[7;49;39m        \e[0m\n\e[27;25;24;22;45;37m$$$$\e[7;49;39m        \e[27;42m  \e[44;37mhello\e[7;49;39m \e[27;44;37mworld\e[0m\n\e[27;25;24;22;45;37m$$$$\e[7;49;39m        \e[27;42m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[0m")
      (list
        (list (size 80 0) table-3)
        "\e[0m\e[27;25;24;22;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[49;39m[testing\e[7;36m \e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[49;39m]\e[0m\n\e[27;25;24;22;45;37m$$$$\e[7;49;39m                        \e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[7;49;39m          \e[0m\n\e[27;25;24;22;45;37m$$$$\e[7;49;39m                                                              \e[0m\n\e[27;25;24;22;45;37m$$$$\e[7;49;39m                                                              \e[0m")
      (list
        (list (size 80 0) table-5)
        "\e[0m\e[27;25;24;22;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[7;49;39m              \e[27m[testing\e[7;36m \e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[49;39m]\e[0m\n\e[27;25;24;22;45;37m$$$$\e[7;49;39m                                      \e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[7;49;39m          \e[0m\n\e[27;25;24;22;45;37m$$$$\e[7;49;39m                                                                            \e[0m\n\e[27;25;24;22;45;37m$$$$\e[7;49;39m                                                                            \e[0m")
      (list
        (list (size 20 0) frame-0)
        "\e[0m\e[27;25;24;22;42;39m \e[7;49;36m      \e[27;5;4;1;40;31m**********\e[25;24;22;43;30m   \e[0m\n\e[27;25;24;22;49;39m[\e[44;37mhello\e[7;49;36m \e[27;5;4;1;40;31m**********\e[25;24;22;43;30m   \e[0m\n\e[27;25;24;22;42;39m \e[7;49;36m      \e[27;45;37m$$$$\e[42;39m \e[43;30m        \e[0m\n\e[27;25;24;22;42;39m \e[7;49;36m      \e[27;45;37m$$$$\e[42;39m \e[43;30m        \e[0m\n\e[27;25;24;22;42;39m \e[44;37mworld\e[7;49;36m \e[27;45;37m$$$$\e[49;39m]\e[43;30m        \e[0m\n\e[27;25;24;22;43;30m                    \e[0m")
      (list
        (list (size 20 0) frame-1)
        "\e[0m\e[27;25;24;22;49;39m[\e[44;37mhello\e[43;30m  \e[0m\n\e[27;25;24;22;42;39m \e[5;4;1;40;31m*******\e[0m\n\e[27;25;24;22;42;39m \e[5;4;1;40;31m*******\e[0m\n\e[27;25;24;22;42;39m \e[44;37mworld\e[43;30m  \e[0m\n\e[27;25;24;22;42;39m \e[45;37m$$$$\e[42;39m \e[43;30m  \e[0m\n\e[27;25;24;22;42;39m \e[45;37m$$$$\e[42;39m \e[43;30m  \e[0m")
      (list
        (list (size 20 0) frame-2)
        "\e[0m\e[27;5;4;1;40;31m********\e[0m\n\e[27;5;4;1;40;31m********\e[0m\n\e[27;25;24;22;44;37morld\e[43;30m    \e[0m\n\e[27;25;24;22;45;37m$$$\e[42;39m \e[43;30m    \e[0m\n\e[27;25;24;22;45;37m$$$\e[42;39m \e[43;30m    \e[0m\n\e[27;25;24;22;45;37m$$$\e[49;39m]\e[43;30m    \e[0m")
      (list
        (list (size 20 0) frame-3)
        "\e[0m\e[27;5;4;1;40;31m********\e[0m\n\e[27;5;4;1;40;31m********\e[0m\n\e[27;25;24;22;44;37mrld\e[43;30m     \e[0m\n\e[27;25;24;22;45;37m$$\e[42;39m \e[43;30m     \e[0m\n\e[27;25;24;22;45;37m$$\e[42;39m \e[43;30m     \e[0m\n\e[27;25;24;22;45;37m$$\e[49;39m]\e[43;30m     \e[0m")
      (list
        (list (size 20 0) frame-4)
        "\e[0m\e[27;25;24;22;42;39m \e[7;49;36m      \e[27;5;4;1;40;31m**********\e[25;24;22;43;30m   \e[0m\n\e[27;25;24;22;49;39m[\e[44;37mhello\e[7;49;36m \e[27;5;4;1;40;31m**********\e[25;24;22;43;30m   \e[0m\n\e[27;25;24;22;42;39m \e[7;49;36m      \e[27;45;37m$$$$\e[42;39m \e[43;30m        \e[0m\n\e[27;25;24;22;42;39m \e[7;49;36m      \e[27;45;37m$$$$\e[42;39m \e[43;30m        \e[0m\n\e[27;25;24;22;42;39m \e[44;37mworld\e[7;49;36m \e[27;45;37m$$$$\e[49;39m]\e[43;30m        \e[0m\n\e[27;25;24;22;43;30m                    \e[0m")
      (list
        (list (size 8 0) frame-5)
        "\e[0m\e[27;5;4;1;40;31m********\e[0m\n\e[27;5;4;1;40;31m********\e[0m\n\e[27;25;24;22;44;37mworld\e[43;30m   \e[0m\n\e[27;25;24;22;45;37m$$$$\e[42;39m \e[43;30m   \e[0m\n\e[27;25;24;22;45;37m$$$$\e[42;39m \e[43;30m   \e[0m\n\e[27;25;24;22;45;37m$$$$\e[49;39m]\e[43;30m   \e[0m")
      (list
        (list (size 8 0) frame-6)
        "\e[0m\e[27;25;24;22;44;37mhello\e[43;30m   \e[0m\n\e[27;5;4;1;40;31m********\e[0m\n\e[27;5;4;1;40;31m********\e[0m\n\e[27;25;24;22;44;37mworld\e[43;30m   \e[0m\n\e[27;25;24;22;45;37m$$$$\e[42;39m \e[43;30m   \e[0m\n\e[27;25;24;22;45;37m$$$$\e[42;39m \e[43;30m   \e[0m\n\e[27;25;24;22;45;37m$$$$\e[49;39m]\e[43;30m   \e[0m")
      (list
        (list (size 18 0) chain-4)
        "\e[0m\e[27;25;24;22;42;39m \e[7;49;36m            \e[27;45;37m$$$$\e[42;39m \e[0m\n\e[27;25;24;22;42;39m \e[7;49;36m            \e[27;45;37m$$$$\e[42;39m \e[0m\n\e[27;25;24;22;49;39m[\e[44;37mhello\e[7;49;36m \e[27;44;37mworld\e[7;49;36m \e[27;45;37m$$$$\e[49;39m]\e[0m")
      (list
        (list (size 16 0) chain-4)
        "\e[0m\e[27;25;24;22;49;39m[\e[44;37mhello\e[7;49;36m \e[27;44;37mworld\e[0m\n\e[27;25;24;22;42;39m \e[45;37m$$$$\e[42;39m \e[41;30m      \e[0m\n\e[27;25;24;22;42;39m \e[45;37m$$$$\e[42;39m \e[41;30m      \e[0m\n\e[27;25;24;22;42;39m \e[45;37m$$$$\e[49;39m]\e[41;30m      \e[0m")
      (list
        (list (size 16 0) chain-0)
        "\e[0m\e[27;25;24;22;45;37mtest(\e[41;30m        \e[0m\n\e[27;25;24;22;42;39m  \e[44;37mhello\e[7;49;39m \e[27;44;37mworld\e[0m\n\e[27;25;24;22;42;39m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[0m")
      (list
        (list (size 16 0) chain-1)
        "\e[0m\e[27;25;24;22;49;39m[testing\e[41;30m       \e[0m\n\e[27;25;24;22;49;36m \e[45;37mtest(\e[41;30m         \e[0m\n\e[27;25;24;22;49;36m \e[42;39m  \e[44;37mhello\e[7;49;39m \e[27;44;37mworld\e[41;30m \e[0m\n\e[27;25;24;22;49;36m \e[42;39m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[49;39m]\e[0m")
      (list
        (list (size 20 0) chain-1)
        "\e[0m\e[27;25;24;22;49;39m[testing\e[41;30m          \e[0m\n\e[27;25;24;22;49;36m \e[45;37mtest(\e[41;30m            \e[0m\n\e[27;25;24;22;49;36m \e[42;39m  \e[44;37mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[0m\n\e[27;25;24;22;49;36m \e[42;39m  \e[44;37mthings\e[45m)\e[49;39m]\e[41;30m       \e[0m")
      (list
        (list (size 20 0) table-0)
        "\e[0m\e[7;25;24;22;49;39m^^^======++======>>>\e[0m\n\e[7;25;24;22;49;39m###\e[27;45;37mtest(\e[7;49;39m ||\e[27m[testi\e[7m###\e[0m\n\e[7;25;24;22;49;39m###\e[27;42m  \e[44;37mhell\e[7;49;39m||\e[27;36m \e[45;37mtest(\e[7;49;39m###\e[0m\n\e[7;25;24;22;49;39m###\e[27;42m  \e[44;37mworl\e[7;49;39m||\e[27;36m \e[42;39m  \e[44;37mhel\e[7;49;39m###\e[0m\n\e[7;25;24;22;49;39m###\e[27;42m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m ||\e[27;36m \e[42;39m  \e[44;37mwor\e[7;49;39m###\e[0m\n\e[7;25;24;22;49;39m###\e[27;42m  \e[44;37mthin\e[7;49;39m||\e[27;36m \e[42;39m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m###\e[0m\n\e[7;25;24;22;49;39m###\e[27;42m  \e[45;37m)\e[7;49;39m   ||\e[27;36m \e[42;39m  \e[44;37mthi\e[7;49;39m###\e[0m\n\e[7;25;24;22;49;39m###      ||\e[27;36m \e[42;39m  \e[45;37m)\e[49;39m]\e[7m ###\e[0m\n\e[7;25;24;22;49;39m+++------++------+++\e[0m\n\e[7;25;24;22;49;39m###\e[27;45;37mtest(\e[7;49;39m ||\e[27;45;37mtest(\e[7;49;39m ###\e[0m\n\e[7;25;24;22;49;39m###\e[27;42m  \e[44;37mhell\e[7;49;39m||\e[27;42m  \e[44;37mhell\e[7;49;39m###\e[0m\n\e[7;25;24;22;49;39m###\e[27;42m  \e[44;37mworl\e[7;49;39m||\e[27;42m  \e[44;37mworl\e[7;49;39m###\e[0m\n\e[7;25;24;22;49;39m###\e[27;42m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m ||\e[27;42m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m ###\e[0m\n\e[7;25;24;22;49;39m###\e[27;42m  \e[44;37mthin\e[7;49;39m||\e[27;42m  \e[44;37mthin\e[7;49;39m###\e[0m\n\e[7;25;24;22;49;39m###\e[27;42m  \e[45;37m)\e[7;49;39m   ||\e[27;42m  \e[45;37m)\e[7;49;39m   ###\e[0m\n\e[7;25;24;22;49;39m<<<======++======vvv\e[0m")
      (list
        (list (size 22 0) chain-2)
        "\e[0m\e[27;25;24;22;45;37m(nested\e[41;30m             \e[0m\n\e[27;25;24;22;42;39m  \e[49m[testing\e[41;30m          \e[0m\n\e[27;25;24;22;42;39m  \e[49;36m \e[45;37mtest(\e[41;30m            \e[0m\n\e[27;25;24;22;42;39m  \e[49;36m \e[42;39m  \e[44;37mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[0m\n\e[27;25;24;22;42;39m  \e[49;36m \e[42;39m  \e[44;37mthings\e[45m)\e[49;39m]\e[7m \e[27;5;4;1;40;31mand\e[25;24;22;41;30m   \e[0m\n\e[27;25;24;22;42;39m  \e[44;37mthings\e[45m)\e[41;30m           \e[0m")
      (list
        (list (size 23 0) chain-3)
        "\e[0m\e[27;25;24;22;49;36mwith-a-table(\e[41;30m          \e[0m\n\e[27;25;24;22;45;37m  (nested\e[41;30m              \e[0m\n\e[27;25;24;22;45;37m  \e[42;39m  \e[49m[testing\e[41;30m           \e[0m\n\e[27;25;24;22;45;37m  \e[42;39m  \e[49;36m \e[45;37mtest(\e[41;30m             \e[0m\n\e[27;25;24;22;45;37m  \e[42;39m  \e[49;36m \e[42;39m  \e[44;37mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[25;24;22;41;30m \e[0m\n\e[27;25;24;22;45;37m  \e[42;39m  \e[49;36m \e[42;39m  \e[44;37mthings\e[45m)\e[49;39m]\e[7m \e[27;5;4;1;40;31mand\e[25;24;22;41;30m    \e[0m\n\e[27;25;24;22;45;37m  \e[42;39m  \e[44;37mthings\e[45m)\e[41;30m            \e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m^^^======++=======>>>\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m###\e[27;45;37mtest(\e[7;49;39m ||\e[27m[testin\e[7m###\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m###\e[27;42m  \e[44;37mhell\e[7;49;39m||\e[27;36m \e[45;37mtest(\e[7;49;39m ###\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m###\e[27;42m  \e[44;37mworl\e[7;49;39m||\e[27;36m \e[42;39m  \e[44;37mhell\e[7;49;39m###\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m###\e[27;42m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m ||\e[27;36m \e[42;39m  \e[44;37mworl\e[7;49;39m###\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m###\e[27;42m  \e[44;37mthin\e[7;49;39m||\e[27;36m \e[42;39m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m ###\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m###\e[27;42m  \e[45;37m)\e[7;49;39m   ||\e[27;36m \e[42;39m  \e[44;37mthin\e[7;49;39m###\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m###      ||\e[27;36m \e[42;39m  \e[45;37m)\e[49;39m]\e[7m  ###\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m+++------++-------+++\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m###\e[27;45;37mtest(\e[7;49;39m ||\e[27;45;37mtest(\e[7;49;39m  ###\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m###\e[27;42m  \e[44;37mhell\e[7;49;39m||\e[27;42m  \e[44;37mhello\e[7;49;39m###\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m###\e[27;42m  \e[44;37mworl\e[7;49;39m||\e[27;42m  \e[44;37mworld\e[7;49;39m###\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m###\e[27;42m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m ||\e[27;42m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m  ###\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m###\e[27;42m  \e[44;37mthin\e[7;49;39m||\e[27;42m  \e[44;37mthing\e[7;49;39m###\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m###\e[27;42m  \e[45;37m)\e[7;49;39m   ||\e[27;42m  \e[45;37m)\e[7;49;39m    ###\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m<<<======++=======vvv\e[0m\n\e[27;25;24;22;45;37m  \e[49;39m[testing\e[41;30m             \e[0m\n\e[27;25;24;22;45;37m  \e[49;36m \e[45;37mtest(\e[41;30m               \e[0m\n\e[27;25;24;22;45;37m  \e[49;36m \e[42;39m  \e[44;37mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[25;24;22;41;30m   \e[0m\n\e[27;25;24;22;45;37m  \e[49;36m \e[42;39m  \e[44;37mthings\e[45m)\e[49;39m]\e[36m)\e[41;30m         \e[0m")
      (list
        (list (size 200 0) chain-3)
        "\e[0m\e[27;25;24;22;45;37m             \e[44m                                                          \e[7;49;39m^^^============================++======================================>>>\e[27;44;37m                                       \e[45m \e[0m\n\e[27;25;24;22;45;37m             \e[44m                                                          \e[7;49;39m###\e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[7;49;39m||\e[27m[testing\e[7;36m \e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[49;39m]\e[7m###\e[27;44;37m                                       \e[45m \e[0m\n\e[27;25;24;22;45;37m             \e[44m                                                          \e[7;49;39m+++----------------------------++--------------------------------------+++\e[27;44;37m                                       \e[45m \e[0m\n\e[27;25;24;22;45;37m             \e[44m                                                          \e[7;49;39m###\e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[7;49;39m||\e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[7;49;39m          ###\e[27;44;37m                                       \e[45m \e[0m\n\e[27;25;24;22;49;36mwith-a-table(\e[45;37m(nested\e[49;39m[testing\e[7;36m \e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[49;39m]\e[7m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[44m \e[7;49;39m<<<============================++======================================vvv\e[27;44;37m \e[49;39m[testing\e[7;36m \e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[49;39m]\e[36m)\e[0m")
      (list
        (list (size 160 0) chain-3)
        "\e[0m\e[27;25;24;22;49;36mwith-a-table(\e[41;30m                                                                                                                         \e[0m\n\e[27;25;24;22;45;37m  \e[44m                                                          \e[7;49;39m^^^============================++======================================>>>\e[0m\n\e[27;25;24;22;45;37m  \e[44m                                                          \e[7;49;39m###\e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[7;49;39m||\e[27m[testing\e[7;36m \e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[49;39m]\e[7m###\e[0m\n\e[27;25;24;22;45;37m  \e[44m                                                          \e[7;49;39m+++----------------------------++--------------------------------------+++\e[0m\n\e[27;25;24;22;45;37m  \e[44m                                                          \e[7;49;39m###\e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[7;49;39m||\e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[7;49;39m          ###\e[0m\n\e[27;25;24;22;45;37m  (nested\e[49;39m[testing\e[7;36m \e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[49;39m]\e[7m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[44m \e[7;49;39m<<<============================++======================================vvv\e[0m\n\e[27;25;24;22;45;37m  \e[49;39m[testing\e[7;36m \e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[49;39m]\e[36m)\e[41;30m                                                                                             \e[0m")
      )
    _ =
    (forl
      (list (list sz doc) expected) <- test-equalities
      (visual-check-equal?
        identity
        (styled-block->string (doc->styled-block ctx style-outer sz doc))
        expected))
    (void)
    ))
