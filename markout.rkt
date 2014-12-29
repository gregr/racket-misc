#lang racket
(provide
  (struct-out doc-atom)
  (struct-out doc-chain)
  (struct-out doc-table)
  attr-tight-aligned
  attr-tight-indented
  attr-loose-aligned
  attr-loose-indented
  tight-pair
  separated
  bracketed-chain
  )

(require
  "list.rkt"
  "maybe.rkt"
  "record.rkt"
  "string.rkt"
  "sugar.rkt"
  "terminal.rkt"
  )

(module+ test
  (require rackunit))

(record chain-attr spaced? indented?)

(records doc
  (doc-atom style str)
  (doc-chain style attr items)
  (doc-table style rows)
  )

(define attr-tight-aligned (chain-attr #f #f))
(define attr-tight-indented (chain-attr #f #t))
(define attr-loose-aligned (chain-attr #t #f))
(define attr-loose-indented (chain-attr #t #t))

(define (tight-pair style lhs rhs)
  (doc-chain style attr-tight-aligned (list lhs rhs)))

(define (separated separator style items)
  (if (empty? items) '()
    (lets
      (list init-items last-item) = (list-init+last items)
      init-items = (forl
                     item <- init-items
                     (tight-pair style item separator))
      (append init-items last-item))))

(def (bracketed-chain prefix suffix attr outer-style inner-style items)
  elements = (doc-chain inner-style attr items)
  suffix-chain = (doc-chain outer-style attr-tight-aligned (list elements suffix))
  (doc-chain outer-style attr-tight-indented (list prefix suffix-chain)))

(define indent-width 2)
(define space-width 1)
(define table-border-width 1)
(define table-divider-width 1)
(define (separator-count xs) (max 0 (- (length xs) 1)))

(define (widths-memo-new) (make-hasheq))
(define (widths-memo-ref memo doc) (hash-ref memo doc (nothing)))
(define (widths-memo-set! memo doc ws) (hash-set! memo doc (just ws)))

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
  (let loop ((choices '()) (scores col-scores))
    (lets
      scores = (filter-not (compose1 empty? cadr) scores)
      scores = (sort scores head-pair->)
      (match scores
        ('() (reverse choices))
        ((cons (list idx (cons (cons _ wdelta) rest)) losers)
         (loop (cons (cons idx wdelta) choices)
               (cons (list idx rest) losers)))))))

(define (widths memo doc)
  (define (widths-grouped xs) (zip (map (curry widths memo) xs)))
  (match (widths-memo-ref memo doc)
    ((just result) result)
    ((nothing)
     (lets
       result =
       (match doc
         ((doc-atom _ str)
          (lets
            len = (string-length str)
            (list len len '() '())))
         ((doc-chain _ (chain-attr spaced? indented?) items)
          (lets
            (list min-widths max-widths _ _) = (widths-grouped items)
            spacing = (if spaced? (* space-width (separator-count items)) 0)
            indent = (if indented? indent-width 0)
            min-width = (apply max
                               (car min-widths)  ; never indented
                               (map (curry + indent) (cdr min-widths)))
            max-width = (+ spacing (apply + max-widths))
            min-width = (min min-width max-width)
            (list min-width max-width '() '())))
         ((doc-table _ rows)
          (lets
            cols = (zip rows)
            (list min-widths max-widths scores) =
            (zip (forl
                   col <- cols
                   (list min-widths max-widths _ _) = (widths-grouped col)
                   min-width = (apply max min-widths)
                   max-width = (apply max max-widths)
                   scored-deltas = (width-scored-deltas min-width max-widths)
                   (list min-width max-width scored-deltas)))
            padding = (+ (* 2 table-border-width)
                         (* table-divider-width (separator-count cols)))
            min-width = (+ padding (apply + min-widths))
            max-width = (+ padding (apply + max-widths))
            scores = (zip* (range (length scores)) scores)
            allocation-order = (width-allocation-order scores)
            (list min-width max-width min-widths allocation-order))))
       _ = (widths-memo-set! memo doc result)
       result))))

(def (table-col-widths available initial mins allocs)
  cols = (list->index-hash mins)
  (let loop ((col-widths cols) (allocs allocs) (avail (- available initial)))
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
  (lets
    style = (void)
    memo = (widths-memo-new)
    items-0 = (list (doc-atom style "hello") (doc-atom style "world"))
    chain-0 = (bracketed-chain (doc-atom style "test(") (doc-atom style ")")
                               attr-loose-aligned style style items-0)
    items-1 = (list (doc-atom style "testing") chain-0)
    chain-1 = (bracketed-chain (doc-atom style "[") (doc-atom style "]")
                               attr-loose-aligned style style items-1)
    table-0 = (doc-table style (list (list chain-0 chain-1) (list chain-0 chain-0)))
    d0 = (- 17 7)
    d1 = (- 27 9)
    table-0-widths = (widths memo table-0)
    (list t0c-min t0c-snug t0c-extra t0c-meh) =
    (lets
      (list initial _ cmins callocs) = table-0-widths
      calc = (lambda (avail) (table-col-widths avail initial cmins callocs))
      (list (calc 19) (calc 47) (calc 100) (calc 30)))
    (begin
      (check-equal?
        (widths memo chain-0)
        (list 7 17 '() '())
        )
      (check-equal?
        (widths memo chain-1)
        (list 9 27 '() '())
        )
      (check-equal?
        table-0-widths
        (list 19 47 (list 7 9) (list (cons 1 (- 17 9)) (cons 0 d0) (cons 1 (- d1 (- 17 9)))))
        )
      (check-equal?
        t0c-min
        (list 7 9)
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

(def (table->styled-block memo style col-widths rows)
  ; TODO: get border chars from style
  ul = (styled-string style "^")
  ur = (styled-string style ">")
  br = (styled-string style "v")
  bl = (styled-string style "<")
  junc = (styled-string style "+")
  rboundary =
  (fn (char)
    col-parts =
    (forl
      col-width <- col-widths
      (styled-string style (make-immutable-string col-width char)))
    (forf
      prefix = (list (car col-parts))
      col-part <- (cdr col-parts)
      (cons col-part (cons junc prefix))))
  hrinternal = (rboundary #\=)
  top-border = (list (cons ul (reverse (cons ur hrinternal))))
  bottom-border = (list (cons bl (reverse (cons br hrinternal))))
  hrinternal = (rboundary #\-)
  hdiv = (list (cons junc (reverse (cons junc hrinternal))))
  rows =
  (forl
    row <- rows
    blocks =
    (forl
      col <- row
      col-width <- col-widths
      (doc->styled-block memo style col-width col))
    sizes = (map styled-block-size blocks)
    max-height = (apply max (map (fn ((size _ h)) h) sizes))
    vborder = (styled-block-fill style #\# (size 1 max-height))
    vdiv = (styled-block-fill style #\| (size 1 max-height))
    new-sizes = (map size col-widths (replicate (length blocks) max-height))
    blocks = (map (curry block-expand style) blocks new-sizes)
    prefix =
    (forf
      prefix = (block-append-horiz style vborder (car blocks))
      block <- (cdr blocks)
      prefix = (block-append-horiz style prefix vdiv)
      (block-append-horiz style prefix block))
    (block-append-horiz style prefix vborder))
  header =
  (forf
    header = (block-append-vert style top-border (car rows))
    row <- (cdr rows)
    header = (block-append-vert style header hdiv)
    (block-append-vert style header row)
    )
  (block-append-vert style header bottom-border))

(def (chain->blocks memo style (chain-attr spaced? indented?) full-width items)
  space-new = (if spaced? (space-block style (size space-width 1)) '())
  prefix-new = (if indented? (space-block style (size indent-width 1)) '())
  (size space-width _) = (styled-block-size space-new)
  (size prefix-width _) = (styled-block-size prefix-new)
  after-indent-width = (- full-width prefix-width)
  next-state =
  (fn (prefix header avail-width item)
    blocks = (doc->blocks memo avail-width item)
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
    (list _ max-width _ _) = (widths memo item)
    (if (>= avail-width (min max-width after-indent-width))
      (lets
        prefix = (if (empty? prefix) prefix
                   (block-append-horiz style prefix space-new))
        (next-state prefix header avail-width item))
      (lets
        header = (cons prefix header)
        (next-state prefix-new header after-indent-width item))))
  (cons prefix header))

(define (doc->blocks memo full-width doc)
  (match doc
    ((doc-atom sty str) (list (list (list (styled-string sty str)))))
    ((doc-chain sty attr items)
     (chain->blocks memo sty attr full-width items))
    ((doc-table sty rows)
     (lets
       (list initial _ mins allocs) = (widths memo doc)
       col-widths = (table-col-widths full-width initial mins allocs)
       (list (table->styled-block memo sty col-widths rows))))))

(def (doc->styled-block memo style full-width doc)
  blocks = (doc->blocks memo full-width doc)
  (forf
    result = (car blocks)
    block <- (cdr blocks)
    (block-append-vert style block result)))  ; bottom to top
