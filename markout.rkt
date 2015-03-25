#lang racket/base
(provide
  attr-tight-aligned
  attr-tight-indented
  attr-loose-aligned
  attr-loose-indented
  bracketed-chain
  separated
  tight-pair
  vertical-list
  (struct-out doc-preformatted)
  (struct-out doc-atom)
  (struct-out doc-chain)
  (struct-out doc-table)
  (struct-out doc-frame)
  (struct-out frame-fixed)
  (struct-out frame-fixed-height)
  doc->styled-block
  sizing-context-new
  sizing-context-new-default
  (struct-out table-style)
  table-style-basic-bordered
  table-style-empty
  )

(require
  "list.rkt"
  "maybe.rkt"
  "record.rkt"
  "string.rkt"
  "sugar.rkt"
  "terminal.rkt"
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
(define table-border-width-default 1)

(define (widths-memo-new) (make-hasheq))
(define (widths-memo-ref memo doc) (hash-ref memo doc (nothing)))
(define (widths-memo-set! memo doc ws) (hash-set! memo doc (just ws)))

(record sizing-context memo space-width indent-width)
(define (sizing-context-new space-width indent-width)
  (sizing-context (widths-memo-new) space-width indent-width))
(define (sizing-context-new-default)
  (sizing-context-new space-width-default indent-width-default))

(record table-style border-width divider-width blocks->final-block)

(def (table-blocks->plain-block style _ _ rows)
  (forf
    header = '()
    row <- rows
    row = (forf
            prefix = '()
            col <- row
            (block-append-horiz style prefix col))
    (block-append-vert style header row)))
(record table-basic-border-maker
  make-top make-bottom make-hdiv
  make-left make-right make-vdiv
  )
(def (table-blocks->basic-bordered-block
       (table-basic-border-maker make-top make-bottom make-hdiv
                                 make-left make-right make-vdiv)
       style row-heights col-widths rows)
  (list top-border bottom-border hdiv) =
  (map (lambda (f) (f col-widths)) (list make-top make-bottom make-hdiv))
  rows =
  (forl
    blocks <- rows
    row-height <- row-heights
    (list vleft vright vdiv) =
    (map (lambda (f) (f row-height)) (list make-left make-right make-vdiv))
    internal = (if (empty? blocks) '()
                 (forf
                   prefix = (car blocks)
                   block <- (cdr blocks)
                   prefix = (block-append-horiz style prefix vdiv)
                   (block-append-horiz style prefix block)))
    prefix = (block-append-horiz style vleft internal)
    (block-append-horiz style prefix vright))
  rows = (if (empty? rows) '()
           (forf
             header = (car rows)
             row <- (cdr rows)
             header = (block-append-vert style header hdiv)
             (block-append-vert style header row)))
  header = (block-append-vert style top-border rows)
  (block-append-vert style header bottom-border))
(def (table-style-basic-bordered
       border-width divider-width
       t b ih
       l r iv
       tl tr bl br
       tj bj lj rj ij
       ts bs ihs
       ls rs ivs
       tls trs bls brs
       tjs bjs ljs rjs ijs
       )
  bw = border-width
  dw = divider-width
  (list tl tr bl br tj bj lj rj ij) =
  (forl
    char <- (list tl tr bl br tj bj lj rj ij)
    style <- (list tls trs bls brs tjs bjs ljs rjs ijs)
    width <- (list bw bw bw bw dw dw bw bw dw)
    (styled-string style (make-immutable-string width char)))
  hborder =
  (lambda (style left right middle junc)
    (fn (col-widths)
      col-parts =
      (forl
        col-width <- col-widths
        (styled-string style (make-immutable-string col-width middle)))
      rmid =
      (if (empty? col-parts) '()
        (forf
          prefix = (list (car col-parts))
          col-part <- (cdr col-parts)
          (list* col-part (list* junc prefix))))
      (styled-block
        (list (styled-line (list* left (reverse (list* right rmid))))))))
  hspans =
  (forl
    args <- (list (list tl tr t tj) (list bl br b bj) (list lj rj ih ij))
    style <- (list ts bs ihs)
    (apply hborder style args))
  vspans =
  (forl
    char <- (list l r iv)
    style <- (list ls rs ivs)
    width <- (list bw bw dw)
    (lambda (height)
      (styled-block-fill style char (size width height))))
  blocks->final-block =
  (curry table-blocks->basic-bordered-block
         (apply table-basic-border-maker (append hspans vspans)))
  (table-style border-width divider-width blocks->final-block))

(define table-style-empty (table-style 0 0 table-blocks->plain-block))

(record chain-attr spaced? indented?)
(define attr-tight-aligned (chain-attr #f #f))
(define attr-tight-indented (chain-attr #f #t))
(define attr-loose-aligned (chain-attr #t #f))
(define attr-loose-indented (chain-attr #t #t))

(records frame-attr
  (frame-fixed rect)
  (frame-fixed-height coord height))

(records doc
  (doc-preformatted block)
  (doc-atom style str)
  (doc-chain style attr items)
  (doc-table style table-style rows)
  (doc-frame style attr doc)
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
  (doc-table style table-style-empty (map list docs)))

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
  widths-grouped = (lambda (xs) (zip-default '(() () () ())
                                             (map (curry widths ctx) xs)))
  (match (widths-memo-ref memo doc)
    ((just result) result)
    ((nothing)
     (lets
       result =
       (match doc
         ((doc-preformatted block)
          (lets
            (size width _) = (styled-block-size block)
            (list width width '() '())))
         ((doc-atom _ str)
          (lets
            len = (string-length str)
            (list len len '() '())))
         ((doc-chain _ (chain-attr spaced? indented?) items)
          (lets
            (list min-widths max-widths _ _) = (widths-grouped items)
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
            (list min-width max-width '() '())))
         ((doc-table _ (table-style border-width divider-width _) rows)
          (lets
            cols = (zip rows)
            (list min-widths max-widths scores) =
            (zip-default '(() () ())
              (forl
                col <- cols
                (list min-widths max-widths _ _) = (widths-grouped col)
                min-width = (apply max min-widths)
                max-width = (apply max max-widths)
                scored-deltas = (width-scored-deltas min-width max-widths)
                (list min-width max-width scored-deltas)))
            padding = (+ (* 2 border-width)
                         (* divider-width (separator-count cols)))
            min-width = (+ padding (sum min-widths))
            max-width = (+ padding (sum max-widths))
            scores = (zip* (range (length scores)) scores)
            allocation-order = (width-allocation-order scores)
            (list min-width max-width min-widths allocation-order)))
         ((doc-frame _ fattr doc)
          (match fattr
            ((frame-fixed (rect _ (size width height)))
             (list width width '() '()))
            ((frame-fixed-height _ height)
             (lets
               (list _ max-width _ _) = (widths ctx doc)
               (list 0 max-width '() '()))))))
       _ = (widths-memo-set! memo doc result)
       result))))

(def (table-col-widths available initial mins allocs)
  cols = (list->index-hash mins)
  (let loop
    ((col-widths cols) (allocs allocs) (avail (max 0 (- available initial))))
    (if (= 0 avail) (index-hash->list col-widths)
      (match allocs
        ('() (loop col-widths '() 0))
        ((cons (cons idx amount) allocs)
         (lets
           amount = (min avail amount)
           avail = (- avail amount)
           col-widths = (hash-update col-widths idx (curry + amount))
           (loop col-widths allocs avail)))))))

(module+ test
  (define bw-test 3)
  (define dw-test 2)
  (define table-style-test
    (apply table-style-basic-bordered
           bw-test dw-test
           (append (list #\= #\= #\-
                         #\# #\# #\|
                         #\^ #\> #\< #\v
                         #\+ #\+ #\+ #\+ #\+)
                   (make-list 15 (style 'default 'default #f #f #f #t))))))

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
    table-0 = (doc-table style table-style-test
                         (list (list chain-0 chain-1) (list chain-0 chain-0)))
    d0 = (- 17 7)
    d1 = (- 27 9)
    padding = (+ (* 2 bw-test) dw-test)
    max-width = (+ 17 27 padding)
    table-0-widths = (widths ctx table-0)
    (list t0c-min t0c-snug t0c-extra t0c-meh) =
    (lets
      (list initial _ cmins callocs) = table-0-widths
      calc = (lambda (avail) (table-col-widths avail initial cmins callocs))
      (list (calc (+ 7 8 padding)) (calc max-width) (calc 100) (calc 35)))
    (begin
      (check-equal?
        (widths ctx chain-empty)
        (list 2 2 '() '())
        )
      (check-equal?
        (widths ctx chain-empties)
        (list 2 5 '() '())
        )
      (check-equal?
        (widths ctx chain-empties-tail)
        (list 2 6 '() '())
        )
      (check-equal?
        (widths ctx chain-empties-tail-head)
        (list 3 7 '() '())
        )
      (check-equal?
        (widths ctx chain-small)
        (list 3 7 '() '())
        )
      (check-equal?
        (widths ctx chain-nested)
        (list 6 22 '() '())
        )
      (check-equal?
        (widths ctx chain-nested-vlist)
        (list 6 22 (list 6) (list (cons 0 16)))
        )
      (check-equal?
        (widths ctx chain-0)
        (list 7 17 '() '())
        )
      (check-equal?
        (widths ctx chain-1)
        (list 8 27 '() '())
        )
      (check-equal?
        table-0-widths
        (list (+ 7 8 padding) max-width
              (list 7 8)
              (list (cons 1 (- 17 8)) (cons 0 d0) (cons 1 (- d1 (- 17 9)))))
        )
      (check-equal?
        t0c-min
        (list 7 8)
        )
      (check-equal?
        t0c-snug
        (list 17 27)
        )
      (check-equal?
        t0c-extra
        (list 17 27)
        )
      (check-equal?
        t0c-meh
        (list 10 17)
        )
      )))

(define (space-block style sz) (styled-block-fill style #\space sz))
(define (block-append-horiz style prefix block)
  (styled-block-append-horizontal style #\space #f prefix block))
(define (block-append-vert style header block)
  (styled-block-append-vertical style #\space #t header block))
(define (block-expand style block sz)
  (styled-block-expand style #\space block sz #t #t))

(def (table->styled-block
       ctx style (table-style _ _ blocks->final-block) col-widths rows)
  (list row-heights rows) =
  (zip-default '(() ())
    (forl
      row <- rows
      cols = (forl
               col <- row
               col-width <- col-widths
               (doc->styled-block ctx style col-width col))
      sizes = (map styled-block-size cols)
      row-height = (apply max 0 (map (fn ((size _ h)) h) sizes))
      cols = (forl
               col <- cols
               col-width <- col-widths
               (block-expand style col (size col-width row-height)))
      (list row-height cols)))
  (blocks->final-block style row-heights col-widths rows))

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
    blocks = (doc->blocks context avail-width item)
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
    (list _ max-width _ _) = (widths context item)
    (if (>= avail-width (min max-width after-indent-width))
      (lets
        prefix = (if (empty? prefix) prefix
                   (block-append-horiz style prefix space-new))
        (next-state prefix header avail-width item))
      (lets
        header = (cons prefix header)
        (next-state prefix-new header after-indent-width item))))
  (cons prefix header))

(def (frame->blocks context style fattr full-width doc)
  (rect (coord x y) sz) =
  (match fattr
    ((frame-fixed rct) rct)
    ((frame-fixed-height crd height)
     (lets
       (list _ max-width _ _) = (widths context doc)
       width = (min max-width full-width)
       (rect crd (size width height)))))
  (size width height) = sz
  block = (doc->styled-block context style width doc)
  (size bw bh) = (styled-block-size block)
  block = (block-expand style block sz)
  pos = (coord (min x (max 0 (- bw width)))
               (min y (max 0 (- bh height))))
  block = (styled-block-sub block (rect pos sz))
  (list block))

(define (doc->blocks ctx full-width doc)
  (match doc
    ((doc-preformatted block) (list block))
    ((doc-atom sty str)
     (list (styled-block (list (styled-line (list (styled-string sty str)))))))
    ((doc-chain sty attr items)
     (chain->blocks ctx sty attr full-width items))
    ((doc-table sty table-sty rows)
     (lets
       (list initial _ mins allocs) = (widths ctx doc)
       col-widths = (table-col-widths full-width initial mins allocs)
       (list (table->styled-block ctx sty table-sty col-widths rows))))
    ((doc-frame sty attr doc) (frame->blocks ctx sty attr full-width doc))))

(def (doc->styled-block ctx style full-width doc)
  blocks = (doc->blocks ctx full-width doc)
  (forf
    result = (car blocks)
    block <- (cdr blocks)
    (block-append-vert style block result)))  ; bottom to top

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
    table-0 = (doc-table style-4 table-style-test
                         (list (list chain-0 chain-1) (list chain-0 chain-0)))
    table-1 = (doc-table style-4 table-style-test '())
    table-2 = (doc-table style-4 table-style-test (list '() '()))
    table-3 = (doc-table style-4 table-style-empty
                         (list (list chain-0 chain-1) (list preformatted-0 chain-0)))

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

    test-equalities =
    (list
      (list
        (list 5 chain-nested)
        "\e[0m\e[27;25;24;22;44;37m{[]\e[41;30m   \e[0m\n\e[27;25;24;22;44;37m {[]\e[41;30m  \e[0m\n\e[27;25;24;22;44;37m  {[]\e[41;30m \e[0m\n\e[27;25;24;22;44;37m   {[]\e[0m\n\e[27;25;24;22;44;37m    []\e[0m\n\e[27;25;24;22;44;37m    }\e[41;30m \e[0m\n\e[27;25;24;22;44;37m   }}\e[41;30m \e[0m\n\e[27;25;24;22;44;37m }\e[41;30m    \e[0m")
      (list
        (list 1 chain-nested)
        "\e[0m\e[27;25;24;22;44;37m{[]\e[41;30m   \e[0m\n\e[27;25;24;22;44;37m {[]\e[41;30m  \e[0m\n\e[27;25;24;22;44;37m  {[]\e[41;30m \e[0m\n\e[27;25;24;22;44;37m   {[]\e[0m\n\e[27;25;24;22;44;37m    []\e[0m\n\e[27;25;24;22;44;37m    }\e[41;30m \e[0m\n\e[27;25;24;22;44;37m   }\e[41;30m  \e[0m\n\e[27;25;24;22;44;37m  }\e[41;30m   \e[0m\n\e[27;25;24;22;44;37m }\e[41;30m    \e[0m")
      (list
        (list 1 chain-nested-vlist)
        "\e[0m\e[27;25;24;22;44;37m{[]\e[49;39m   \e[0m\n\e[27;25;24;22;44;37m {[]\e[49;39m  \e[0m\n\e[27;25;24;22;44;37m  {[]\e[49;39m \e[0m\n\e[27;25;24;22;44;37m   {[]\e[0m\n\e[27;25;24;22;44;37m    []\e[0m\n\e[27;25;24;22;44;37m    }}\e[0m\n\e[27;25;24;22;44;37m  }}\e[49;39m  \e[0m")
      (list
        (list 10 table-1)
        "\e[0m\e[7;25;24;22;49;39m^^^>>>\e[0m\n\e[7;25;24;22;49;39m<<<vvv\e[0m")
      (list
        (list 10 table-2)
        "\e[0m\e[7;25;24;22;49;39m^^^>>>\e[0m\n\e[7;25;24;22;49;39m++++++\e[0m\n\e[7;25;24;22;49;39m<<<vvv\e[0m")
      (list
        (list 25 table-3)
        "\e[0m\e[27;25;24;22;45;37mtest(\e[7;49;39m   \e[27m[testing\e[7m         \e[0m\n\e[27;25;24;22;42;39m  \e[44;37mhello\e[7;49;39m \e[27;36m \e[45;37mtest(\e[7;49;39m           \e[0m\n\e[27;25;24;22;42;39m  \e[44;37mworld\e[7;49;39m \e[27;36m \e[42;39m  \e[44;37mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m   \e[0m\n\e[27;25;24;22;42;39m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m   \e[27;36m \e[42;39m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[49;39m]\e[7m  \e[0m\n\e[27;25;24;22;42;39m  \e[44;37mthings\e[7;49;39m                 \e[0m\n\e[27;25;24;22;42;39m  \e[45;37m)\e[7;49;39m                      \e[0m\n\e[27;25;24;22;45;37m$$$$\e[7;49;39m    \e[27;45;37mtest(\e[7;49;39m            \e[0m\n\e[27;25;24;22;45;37m$$$$\e[7;49;39m    \e[27;42m  \e[44;37mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[0m\n\e[27;25;24;22;45;37m$$$$\e[7;49;39m    \e[27;42m  \e[44;37mthings\e[45m)\e[7;49;39m        \e[0m")
      (list
        (list 20 frame-0)
        "\e[0m\e[27;25;24;22;42;39m \e[7;49;36m      \e[27;5;4;1;40;31m**********\e[25;24;22;43;30m   \e[0m\n\e[27;25;24;22;49;39m[\e[44;37mhello\e[7;49;36m \e[27;5;4;1;40;31m**********\e[25;24;22;43;30m   \e[0m\n\e[27;25;24;22;42;39m \e[7;49;36m      \e[27;45;37m$$$$\e[42;39m \e[43;30m        \e[0m\n\e[27;25;24;22;42;39m \e[7;49;36m      \e[27;45;37m$$$$\e[42;39m \e[43;30m        \e[0m\n\e[27;25;24;22;42;39m \e[44;37mworld\e[7;49;36m \e[27;45;37m$$$$\e[49;39m]\e[43;30m        \e[0m\n\e[27;25;24;22;43;30m                    \e[0m")
      (list
        (list 20 frame-1)
        "\e[0m\e[27;25;24;22;49;39m[\e[44;37mhello\e[43;30m  \e[0m\n\e[27;25;24;22;42;39m \e[5;4;1;40;31m*******\e[0m\n\e[27;25;24;22;42;39m \e[5;4;1;40;31m*******\e[0m\n\e[27;25;24;22;42;39m \e[44;37mworld\e[43;30m  \e[0m\n\e[27;25;24;22;42;39m \e[45;37m$$$$\e[42;39m \e[43;30m  \e[0m\n\e[27;25;24;22;42;39m \e[45;37m$$$$\e[42;39m \e[43;30m  \e[0m")
      (list
        (list 20 frame-2)
        "\e[0m\e[27;5;4;1;40;31m********\e[0m\n\e[27;5;4;1;40;31m********\e[0m\n\e[27;25;24;22;44;37morld\e[43;30m    \e[0m\n\e[27;25;24;22;45;37m$$$\e[42;39m \e[43;30m    \e[0m\n\e[27;25;24;22;45;37m$$$\e[42;39m \e[43;30m    \e[0m\n\e[27;25;24;22;45;37m$$$\e[49;39m]\e[43;30m    \e[0m")
      (list
        (list 20 frame-3)
        "\e[0m\e[27;5;4;1;40;31m********\e[0m\n\e[27;5;4;1;40;31m********\e[0m\n\e[27;25;24;22;44;37mrld\e[43;30m     \e[0m\n\e[27;25;24;22;45;37m$$\e[42;39m \e[43;30m     \e[0m\n\e[27;25;24;22;45;37m$$\e[42;39m \e[43;30m     \e[0m\n\e[27;25;24;22;45;37m$$\e[49;39m]\e[43;30m     \e[0m")
      (list
        (list 20 frame-4)
        "\e[0m\e[27;25;24;22;42;39m \e[7;49;36m      \e[27;5;4;1;40;31m**********\e[25;24;22;43;30m   \e[0m\n\e[27;25;24;22;49;39m[\e[44;37mhello\e[7;49;36m \e[27;5;4;1;40;31m**********\e[25;24;22;43;30m   \e[0m\n\e[27;25;24;22;42;39m \e[7;49;36m      \e[27;45;37m$$$$\e[42;39m \e[43;30m        \e[0m\n\e[27;25;24;22;42;39m \e[7;49;36m      \e[27;45;37m$$$$\e[42;39m \e[43;30m        \e[0m\n\e[27;25;24;22;42;39m \e[44;37mworld\e[7;49;36m \e[27;45;37m$$$$\e[49;39m]\e[43;30m        \e[0m\n\e[27;25;24;22;43;30m                    \e[0m")
      (list
        (list 8 frame-5)
        "\e[0m\e[27;5;4;1;40;31m********\e[0m\n\e[27;5;4;1;40;31m********\e[0m\n\e[27;25;24;22;44;37mworld\e[43;30m   \e[0m\n\e[27;25;24;22;45;37m$$$$\e[42;39m \e[43;30m   \e[0m\n\e[27;25;24;22;45;37m$$$$\e[42;39m \e[43;30m   \e[0m\n\e[27;25;24;22;45;37m$$$$\e[49;39m]\e[43;30m   \e[0m")
      (list
        (list 18 chain-4)
        "\e[0m\e[27;25;24;22;42;39m \e[7;49;36m            \e[27;45;37m$$$$\e[42;39m \e[0m\n\e[27;25;24;22;42;39m \e[7;49;36m            \e[27;45;37m$$$$\e[42;39m \e[0m\n\e[27;25;24;22;49;39m[\e[44;37mhello\e[7;49;36m \e[27;44;37mworld\e[7;49;36m \e[27;45;37m$$$$\e[49;39m]\e[0m")
      (list
        (list 16 chain-4)
        "\e[0m\e[27;25;24;22;49;39m[\e[44;37mhello\e[7;49;36m \e[27;44;37mworld\e[0m\n\e[27;25;24;22;42;39m \e[45;37m$$$$\e[42;39m \e[41;30m      \e[0m\n\e[27;25;24;22;42;39m \e[45;37m$$$$\e[42;39m \e[41;30m      \e[0m\n\e[27;25;24;22;42;39m \e[45;37m$$$$\e[49;39m]\e[41;30m      \e[0m")
      (list
        (list 16 chain-0)
        "\e[0m\e[27;25;24;22;45;37mtest(\e[41;30m        \e[0m\n\e[27;25;24;22;42;39m  \e[44;37mhello\e[7;49;39m \e[27;44;37mworld\e[0m\n\e[27;25;24;22;42;39m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[0m")
      (list
        (list 16 chain-1)
        "\e[0m\e[27;25;24;22;49;39m[testing\e[41;30m       \e[0m\n\e[27;25;24;22;49;36m \e[45;37mtest(\e[41;30m         \e[0m\n\e[27;25;24;22;49;36m \e[42;39m  \e[44;37mhello\e[7;49;39m \e[27;44;37mworld\e[41;30m \e[0m\n\e[27;25;24;22;49;36m \e[42;39m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[49;39m]\e[0m")
      (list
        (list 20 chain-1)
        "\e[0m\e[27;25;24;22;49;39m[testing\e[41;30m          \e[0m\n\e[27;25;24;22;49;36m \e[45;37mtest(\e[41;30m            \e[0m\n\e[27;25;24;22;49;36m \e[42;39m  \e[44;37mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[0m\n\e[27;25;24;22;49;36m \e[42;39m  \e[44;37mthings\e[45m)\e[49;39m]\e[41;30m       \e[0m")
      (list
        (list 20 table-0)
        "\e[0m\e[7;25;24;22;49;39m^^^========++=========>>>\e[0m\n\e[7;25;24;22;49;39m###\e[27;45;37mtest(\e[7;49;39m   ||\e[27m[testing\e[7m ###\e[0m\n\e[7;25;24;22;49;39m###\e[27;42m  \e[44;37mhello\e[7;49;39m ||\e[27;36m \e[45;37mtest(\e[7;49;39m   ###\e[0m\n\e[7;25;24;22;49;39m###\e[27;42m  \e[44;37mworld\e[7;49;39m ||\e[27;36m \e[42;39m  \e[44;37mhello\e[7;49;39m ###\e[0m\n\e[7;25;24;22;49;39m###\e[27;42m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m   ||\e[27;36m \e[42;39m  \e[44;37mworld\e[7;49;39m ###\e[0m\n\e[7;25;24;22;49;39m###\e[27;42m  \e[44;37mthings\e[7;49;39m||\e[27;36m \e[42;39m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m   ###\e[0m\n\e[7;25;24;22;49;39m###\e[27;42m  \e[45;37m)\e[7;49;39m     ||\e[27;36m \e[42;39m  \e[44;37mthings\e[7;49;39m###\e[0m\n\e[7;25;24;22;49;39m###        ||\e[27;36m \e[42;39m  \e[45;37m)\e[49;39m]\e[7m    ###\e[0m\n\e[7;25;24;22;49;39m+++--------++---------+++\e[0m\n\e[7;25;24;22;49;39m###\e[27;45;37mtest(\e[7;49;39m   ||\e[27;45;37mtest(\e[7;49;39m    ###\e[0m\n\e[7;25;24;22;49;39m###\e[27;42m  \e[44;37mhello\e[7;49;39m ||\e[27;42m  \e[44;37mhello\e[7;49;39m  ###\e[0m\n\e[7;25;24;22;49;39m###\e[27;42m  \e[44;37mworld\e[7;49;39m ||\e[27;42m  \e[44;37mworld\e[7;49;39m  ###\e[0m\n\e[7;25;24;22;49;39m###\e[27;42m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m   ||\e[27;42m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m    ###\e[0m\n\e[7;25;24;22;49;39m###\e[27;42m  \e[44;37mthings\e[7;49;39m||\e[27;42m  \e[44;37mthings\e[45m)\e[7;49;39m###\e[0m\n\e[7;25;24;22;49;39m###\e[27;42m  \e[45;37m)\e[7;49;39m     ||         ###\e[0m\n\e[7;25;24;22;49;39m<<<========++=========vvv\e[0m")
      (list
        (list 22 chain-2)
        "\e[0m\e[27;25;24;22;45;37m(nested\e[41;30m             \e[0m\n\e[27;25;24;22;42;39m  \e[49m[testing\e[41;30m          \e[0m\n\e[27;25;24;22;42;39m  \e[49;36m \e[45;37mtest(\e[41;30m            \e[0m\n\e[27;25;24;22;42;39m  \e[49;36m \e[42;39m  \e[44;37mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[0m\n\e[27;25;24;22;42;39m  \e[49;36m \e[42;39m  \e[44;37mthings\e[45m)\e[49;39m]\e[7m \e[27;5;4;1;40;31mand\e[25;24;22;41;30m   \e[0m\n\e[27;25;24;22;42;39m  \e[44;37mthings\e[45m)\e[41;30m           \e[0m")
      (list
        (list 23 chain-3)
        "\e[0m\e[27;25;24;22;49;36mwith-a-table(\e[41;30m              \e[0m\n\e[27;25;24;22;45;37m  (nested\e[41;30m                  \e[0m\n\e[27;25;24;22;45;37m  \e[42;39m  \e[49m[testing\e[41;30m               \e[0m\n\e[27;25;24;22;45;37m  \e[42;39m  \e[49;36m \e[45;37mtest(\e[41;30m                 \e[0m\n\e[27;25;24;22;45;37m  \e[42;39m  \e[49;36m \e[42;39m  \e[44;37mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[25;24;22;41;30m     \e[0m\n\e[27;25;24;22;45;37m  \e[42;39m  \e[49;36m \e[42;39m  \e[44;37mthings\e[45m)\e[49;39m]\e[7m \e[27;5;4;1;40;31mand\e[25;24;22;41;30m        \e[0m\n\e[27;25;24;22;45;37m  \e[42;39m  \e[44;37mthings\e[45m)\e[41;30m                \e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m^^^========++=========>>>\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m###\e[27;45;37mtest(\e[7;49;39m   ||\e[27m[testing\e[7m ###\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m###\e[27;42m  \e[44;37mhello\e[7;49;39m ||\e[27;36m \e[45;37mtest(\e[7;49;39m   ###\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m###\e[27;42m  \e[44;37mworld\e[7;49;39m ||\e[27;36m \e[42;39m  \e[44;37mhello\e[7;49;39m ###\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m###\e[27;42m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m   ||\e[27;36m \e[42;39m  \e[44;37mworld\e[7;49;39m ###\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m###\e[27;42m  \e[44;37mthings\e[7;49;39m||\e[27;36m \e[42;39m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m   ###\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m###\e[27;42m  \e[45;37m)\e[7;49;39m     ||\e[27;36m \e[42;39m  \e[44;37mthings\e[7;49;39m###\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m###        ||\e[27;36m \e[42;39m  \e[45;37m)\e[49;39m]\e[7m    ###\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m+++--------++---------+++\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m###\e[27;45;37mtest(\e[7;49;39m   ||\e[27;45;37mtest(\e[7;49;39m    ###\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m###\e[27;42m  \e[44;37mhello\e[7;49;39m ||\e[27;42m  \e[44;37mhello\e[7;49;39m  ###\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m###\e[27;42m  \e[44;37mworld\e[7;49;39m ||\e[27;42m  \e[44;37mworld\e[7;49;39m  ###\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m###\e[27;42m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m   ||\e[27;42m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m    ###\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m###\e[27;42m  \e[44;37mthings\e[7;49;39m||\e[27;42m  \e[44;37mthings\e[45m)\e[7;49;39m###\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m###\e[27;42m  \e[45;37m)\e[7;49;39m     ||         ###\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m<<<========++=========vvv\e[0m\n\e[27;25;24;22;45;37m  \e[49;39m[testing\e[41;30m                 \e[0m\n\e[27;25;24;22;45;37m  \e[49;36m \e[45;37mtest(\e[41;30m                   \e[0m\n\e[27;25;24;22;45;37m  \e[49;36m \e[42;39m  \e[44;37mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[25;24;22;41;30m       \e[0m\n\e[27;25;24;22;45;37m  \e[49;36m \e[42;39m  \e[44;37mthings\e[45m)\e[49;39m]\e[36m)\e[41;30m             \e[0m")
      (list
        (list 200 chain-3)
        "\e[0m\e[27;25;24;22;45;37m             \e[44m                                                          \e[7;49;39m^^^============================++======================================>>>\e[27;44;37m                                       \e[45m \e[0m\n\e[27;25;24;22;45;37m             \e[44m                                                          \e[7;49;39m###\e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[7;49;39m||\e[27m[testing\e[7;36m \e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[49;39m]\e[7m###\e[27;44;37m                                       \e[45m \e[0m\n\e[27;25;24;22;45;37m             \e[44m                                                          \e[7;49;39m+++----------------------------++--------------------------------------+++\e[27;44;37m                                       \e[45m \e[0m\n\e[27;25;24;22;45;37m             \e[44m                                                          \e[7;49;39m###\e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[7;49;39m||\e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[7;49;39m          ###\e[27;44;37m                                       \e[45m \e[0m\n\e[27;25;24;22;49;36mwith-a-table(\e[45;37m(nested\e[49;39m[testing\e[7;36m \e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[49;39m]\e[7m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[44m \e[7;49;39m<<<============================++======================================vvv\e[27;44;37m \e[49;39m[testing\e[7;36m \e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[49;39m]\e[36m)\e[0m")
      (list
        (list 160 chain-3)
        "\e[0m\e[27;25;24;22;49;36mwith-a-table(\e[41;30m                                                                                                                         \e[0m\n\e[27;25;24;22;45;37m  \e[44m                                                          \e[7;49;39m^^^============================++======================================>>>\e[0m\n\e[27;25;24;22;45;37m  \e[44m                                                          \e[7;49;39m###\e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[7;49;39m||\e[27m[testing\e[7;36m \e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[49;39m]\e[7m###\e[0m\n\e[27;25;24;22;45;37m  \e[44m                                                          \e[7;49;39m+++----------------------------++--------------------------------------+++\e[0m\n\e[27;25;24;22;45;37m  \e[44m                                                          \e[7;49;39m###\e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[7;49;39m||\e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[7;49;39m          ###\e[0m\n\e[27;25;24;22;45;37m  (nested\e[49;39m[testing\e[7;36m \e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[49;39m]\e[7m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[44m \e[7;49;39m<<<============================++======================================vvv\e[0m\n\e[27;25;24;22;45;37m  \e[49;39m[testing\e[7;36m \e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[49;39m]\e[36m)\e[41;30m                                                                                             \e[0m")
      )
    _ =
    (forl
      (list (list width doc) expected) <- test-equalities
      (visual-check-equal?
        identity
        (styled-block->string (doc->styled-block ctx style-outer width doc))
        expected))
    (void)
    ))
