#lang racket
(provide
  attr-tight-aligned
  attr-tight-indented
  attr-loose-aligned
  attr-loose-indented
  bracketed-chain
  separated
  tight-pair
  (struct-out doc-atom)
  (struct-out doc-chain)
  (struct-out doc-table)
  doc->styled-block
  sizing-context-new
  sizing-context-new-default
  (struct-out styling)
  styling-empty
  table-styling-new
  table-styling-empty
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
  (require
    "test.rkt"
    rackunit
    ))

(define indent-width-default 2)
(define space-width-default 1)
(define table-border-width 1)
(define table-divider-width table-border-width)

(define (widths-memo-new) (make-hasheq))
(define (widths-memo-ref memo doc) (hash-ref memo doc (nothing)))
(define (widths-memo-set! memo doc ws) (hash-set! memo doc (just ws)))

(record sizing-context memo space-width indent-width)
(define (sizing-context-new space-width indent-width)
  (sizing-context (widths-memo-new) space-width indent-width))
(define (sizing-context-new-default)
  (sizing-context-new space-width-default indent-width-default))

(record table-styling
  make-top make-bottom make-hdiv
  make-left make-right make-vdiv
  )
(def (table-styling-new
       t b ih
       l r iv
       tl tr bl br
       tj bj lj rj ij
       ts bs ihs
       ls rs ivs
       tls trs bls brs
       tjs bjs ljs rjs ijs
       )
  (list tl tr bl br tj bj lj rj ij) =
  (forl
    char <- (list tl tr bl br tj bj lj rj ij)
    style <- (list tls trs bls brs tjs bjs ljs rjs ijs)
    (styled-string style (make-immutable-string 1 char)))
  hborder =
  (lambda (style left right middle junc)
    (fn (col-widths)
      col-parts =
      (forl
        col-width <- col-widths
        (styled-string style (make-immutable-string col-width middle)))
      rmid =
      (forf
        prefix = (list (car col-parts))
        col-part <- (cdr col-parts)
        (cons col-part (cons junc prefix)))
      (list (cons left (reverse (cons right rmid))))))
  hspans =
  (forl
    args <- (list (list tl tr t tj) (list bl br b bj) (list lj rj ih ij))
    style <- (list ts bs ihs)
    (apply hborder style args))
  vspans =
  (forl
    char <- (list l r iv)
    style <- (list ls rs ivs)
    (lambda (height)
      (styled-block-fill style char (size table-border-width height))))
  (apply table-styling (append hspans vspans)))
(define table-styling-empty
  (apply table-styling-new
         (append (replicate 15 #\space) (replicate 15 style-empty))))

(record styling style table)
(define styling-empty (styling style-empty table-styling-empty))

(record chain-attr spaced? indented?)
(define attr-tight-aligned (chain-attr #f #f))
(define attr-tight-indented (chain-attr #f #t))
(define attr-loose-aligned (chain-attr #t #f))
(define attr-loose-indented (chain-attr #t #t))

(records doc
  (doc-atom style str)
  (doc-chain style attr items)
  (doc-table style rows)
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
      (append init-items last-item))))

(def (bracketed-chain prefix suffix attr outer-style inner-style items)
  elements = (doc-chain inner-style attr items)
  suffix-chain = (doc-chain outer-style attr-tight-aligned (list elements suffix))
  (doc-chain outer-style attr-tight-indented (list prefix suffix-chain)))

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
  (let loop ((choices '()) (scores col-scores))
    (lets
      scores = (filter-not (compose1 empty? cadr) scores)
      scores = (sort scores head-pair->)
      (match scores
        ('() (reverse choices))
        ((cons (list idx (cons (cons _ wdelta) rest)) losers)
         (loop (cons (cons idx wdelta) choices)
               (cons (list idx rest) losers)))))))

(def (widths ctx doc)
  (sizing-context memo space-width indent-width) = ctx
  widths-grouped = (lambda (xs) (zip (map (curry widths ctx) xs)))
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
            max-width = (+ spacing (sum max-widths))
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
            min-width = (+ padding (sum min-widths))
            max-width = (+ padding (sum max-widths))
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
  (define table-styling-test
    (apply table-styling-new
           (append (list #\= #\= #\-
                         #\# #\# #\|
                         #\^ #\> #\< #\v
                         #\+ #\+ #\+ #\+ #\+)
                   (replicate 15 (style 'default 'default #f #f #f #t))))))

(module+ test
  (lets
    style = (styling style-empty table-styling-empty)
    ctx = (sizing-context-new-default)
    items-0 = (list (doc-atom style "hello") (doc-atom style "world"))
    chain-0 = (bracketed-chain (doc-atom style "test(") (doc-atom style ")")
                               attr-loose-aligned style style items-0)
    items-1 = (list (doc-atom style "testing") chain-0)
    chain-1 = (bracketed-chain (doc-atom style "[") (doc-atom style "]")
                               attr-loose-aligned style style items-1)
    table-0 = (doc-table style (list (list chain-0 chain-1) (list chain-0 chain-0)))
    d0 = (- 17 7)
    d1 = (- 27 9)
    table-0-widths = (widths ctx table-0)
    (list t0c-min t0c-snug t0c-extra t0c-meh) =
    (lets
      (list initial _ cmins callocs) = table-0-widths
      calc = (lambda (avail) (table-col-widths avail initial cmins callocs))
      (list (calc 19) (calc 47) (calc 100) (calc 30)))
    (begin
      (check-equal?
        (widths ctx chain-0)
        (list 7 17 '() '())
        )
      (check-equal?
        (widths ctx chain-1)
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

(def (table->styled-block ctx sty col-widths rows)
  (styling style (table-styling
                   make-top make-bottom make-hdiv
                   make-left make-right make-vdiv)) = sty
  (list top-border bottom-border hdiv) =
  (map (lambda (f) (f col-widths)) (list make-top make-bottom make-hdiv))
  rows =
  (forl
    row <- rows
    blocks =
    (forl
      col <- row
      col-width <- col-widths
      (doc->styled-block ctx sty col-width col))
    sizes = (map styled-block-size blocks)
    max-height = (apply max (map (fn ((size _ h)) h) sizes))
    (list vleft vright vdiv) =
    (map (lambda (f) (f max-height)) (list make-left make-right make-vdiv))
    new-sizes = (map size col-widths (replicate (length blocks) max-height))
    blocks = (map (curry block-expand style) blocks new-sizes)
    prefix =
    (forf
      prefix = (block-append-horiz style vleft (car blocks))
      block <- (cdr blocks)
      prefix = (block-append-horiz style prefix vdiv)
      (block-append-horiz style prefix block))
    (block-append-horiz style prefix vright))
  header =
  (forf
    header = (block-append-vert style top-border (car rows))
    row <- (cdr rows)
    header = (block-append-vert style header hdiv)
    (block-append-vert style header row)
    )
  (block-append-vert style header bottom-border))

(def (chain->blocks
       context
       (styling style _) (chain-attr spaced? indented?) full-width items)
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

(define (doc->blocks ctx full-width doc)
  (match doc
    ((doc-atom (styling sty _) str)
     (list (list (list (styled-string sty str)))))
    ((doc-chain sty attr items)
     (chain->blocks ctx sty attr full-width items))
    ((doc-table sty rows)
     (lets
       (list initial _ mins allocs) = (widths ctx doc)
       col-widths = (table-col-widths full-width initial mins allocs)
       (list (table->styled-block ctx sty col-widths rows))))))

(def (doc->styled-block ctx (styling style _) full-width doc)
  blocks = (doc->blocks ctx full-width doc)
  (forf
    result = (car blocks)
    block <- (cdr blocks)
    (block-append-vert style block result)))  ; bottom to top

(module+ test
  (lets
    ctx = (sizing-context-new-default)
    style-outer = (styling (style 'black 'red #f #f #f #f) table-styling-test)
    style-0 = (styling (style 'white 'blue #f #f #f #f) table-styling-test)
    style-1 = (styling (style 'red 'black #t #t #t #f) table-styling-test)
    style-2 = (styling (style 'white 'magenta #f #f #f #f) table-styling-test)
    style-3 = (styling (style 'default 'green #f #f #f #f) table-styling-test)
    style-4 = (styling (style 'default 'default #f #f #f #t) table-styling-test)
    style-5 = (styling (style 'default 'default #f #f #f #f) table-styling-test)
    style-6 = (styling (style 'cyan 'default #f #f #f #f) table-styling-test)
    style-7 = (styling (style 'cyan 'default #f #f #f #t) table-styling-test)

    atom-0 = (doc-atom style-0 "hello")
    atom-1 = (doc-atom style-0 "world")
    atom-2 = (doc-atom style-1 "and")
    atom-3 = (doc-atom style-0 "things")
    items-0 = (list atom-0 atom-1 atom-2 atom-3)

    chain-0 = (bracketed-chain (doc-atom style-2 "test(") (doc-atom style-2 ")")
                               attr-loose-aligned style-3 style-4 items-0)

    items-1 = (list (doc-atom style-5 "testing") chain-0)
    chain-1 = (bracketed-chain (doc-atom style-5 "[") (doc-atom style-5 "]")
                               attr-loose-aligned style-6 style-7 items-1)
    table-0 = (doc-table style-4 (list (list chain-0 chain-1) (list chain-0 chain-0)))

    items-2 = (list chain-1 atom-2 atom-3)
    chain-2 = (bracketed-chain (doc-atom style-2 "(nested") (doc-atom style-2 ")")
                               attr-loose-aligned style-3 style-4 items-2)

    items-3 = (list chain-2 table-0 chain-1)
    chain-3 = (bracketed-chain (doc-atom style-6 "with-a-table(") (doc-atom style-6 ")")
                               attr-loose-aligned style-2 style-0 items-3)

    test-equalities =
    (list
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
        "\e[0m\e[7;25;24;22;49;39m^========+=========>\e[0m\n\e[7;25;24;22;49;39m#\e[27;45;37mtest(\e[7;49;39m   |\e[27m[testing\e[7m #\e[0m\n\e[7;25;24;22;49;39m#\e[27;42m  \e[44;37mhello\e[7;49;39m |\e[27;36m \e[45;37mtest(\e[7;49;39m   #\e[0m\n\e[7;25;24;22;49;39m#\e[27;42m  \e[44;37mworld\e[7;49;39m |\e[27;36m \e[42;39m  \e[44;37mhello\e[7;49;39m #\e[0m\n\e[7;25;24;22;49;39m#\e[27;42m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m   |\e[27;36m \e[42;39m  \e[44;37mworld\e[7;49;39m #\e[0m\n\e[7;25;24;22;49;39m#\e[27;42m  \e[44;37mthings\e[7;49;39m|\e[27;36m \e[42;39m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m   #\e[0m\n\e[7;25;24;22;49;39m#\e[27;42m  \e[45;37m)\e[7;49;39m     |\e[27;36m \e[42;39m  \e[44;37mthings\e[7;49;39m#\e[0m\n\e[7;25;24;22;49;39m#        |\e[27;36m \e[42;39m  \e[45;37m)\e[49;39m]\e[7m    #\e[0m\n\e[7;25;24;22;49;39m+--------+---------+\e[0m\n\e[7;25;24;22;49;39m#\e[27;45;37mtest(\e[7;49;39m   |\e[27;45;37mtest(\e[7;49;39m    #\e[0m\n\e[7;25;24;22;49;39m#\e[27;42m  \e[44;37mhello\e[7;49;39m |\e[27;42m  \e[44;37mhello\e[7;49;39m  #\e[0m\n\e[7;25;24;22;49;39m#\e[27;42m  \e[44;37mworld\e[7;49;39m |\e[27;42m  \e[44;37mworld\e[7;49;39m  #\e[0m\n\e[7;25;24;22;49;39m#\e[27;42m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m   |\e[27;42m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m    #\e[0m\n\e[7;25;24;22;49;39m#\e[27;42m  \e[44;37mthings\e[7;49;39m|\e[27;42m  \e[44;37mthings\e[45m)\e[7;49;39m#\e[0m\n\e[7;25;24;22;49;39m#\e[27;42m  \e[45;37m)\e[7;49;39m     |         #\e[0m\n\e[7;25;24;22;49;39m<========+=========v\e[0m")
      (list
        (list 22 chain-2)
        "\e[0m\e[27;25;24;22;45;37m(nested\e[41;30m             \e[0m\n\e[27;25;24;22;42;39m  \e[49m[testing\e[41;30m          \e[0m\n\e[27;25;24;22;42;39m  \e[49;36m \e[45;37mtest(\e[41;30m            \e[0m\n\e[27;25;24;22;42;39m  \e[49;36m \e[42;39m  \e[44;37mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[0m\n\e[27;25;24;22;42;39m  \e[49;36m \e[42;39m  \e[44;37mthings\e[45m)\e[49;39m]\e[7m \e[27;5;4;1;40;31mand\e[25;24;22;41;30m   \e[0m\n\e[27;25;24;22;42;39m  \e[44;37mthings\e[45m)\e[41;30m           \e[0m")
      (list
        (list 23 chain-3)
        "\e[0m\e[27;25;24;22;49;36mwith-a-table(\e[41;30m          \e[0m\n\e[27;25;24;22;45;37m  (nested\e[41;30m              \e[0m\n\e[27;25;24;22;45;37m  \e[42;39m  \e[49m[testing\e[41;30m           \e[0m\n\e[27;25;24;22;45;37m  \e[42;39m  \e[49;36m \e[45;37mtest(\e[41;30m             \e[0m\n\e[27;25;24;22;45;37m  \e[42;39m  \e[49;36m \e[42;39m  \e[44;37mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[25;24;22;41;30m \e[0m\n\e[27;25;24;22;45;37m  \e[42;39m  \e[49;36m \e[42;39m  \e[44;37mthings\e[45m)\e[49;39m]\e[7m \e[27;5;4;1;40;31mand\e[25;24;22;41;30m    \e[0m\n\e[27;25;24;22;45;37m  \e[42;39m  \e[44;37mthings\e[45m)\e[41;30m            \e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m^========+==========>\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m#\e[27;45;37mtest(\e[7;49;39m   |\e[27m[testing\e[7m  #\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m#\e[27;42m  \e[44;37mhello\e[7;49;39m |\e[27;36m \e[45;37mtest(\e[7;49;39m    #\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m#\e[27;42m  \e[44;37mworld\e[7;49;39m |\e[27;36m \e[42;39m  \e[44;37mhello\e[7;49;39m  #\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m#\e[27;42m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m   |\e[27;36m \e[42;39m  \e[44;37mworld\e[7;49;39m  #\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m#\e[27;42m  \e[44;37mthings\e[7;49;39m|\e[27;36m \e[42;39m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m    #\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m#\e[27;42m  \e[45;37m)\e[7;49;39m     |\e[27;36m \e[42;39m  \e[44;37mthings\e[45m)\e[7;49;39m#\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m#        |\e[27;36m \e[39m]\e[7m        #\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m+--------+----------+\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m#\e[27;45;37mtest(\e[7;49;39m   |\e[27;45;37mtest(\e[7;49;39m     #\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m#\e[27;42m  \e[44;37mhello\e[7;49;39m |\e[27;42m  \e[44;37mhello\e[7;49;39m   #\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m#\e[27;42m  \e[44;37mworld\e[7;49;39m |\e[27;42m  \e[44;37mworld\e[7;49;39m   #\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m#\e[27;42m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m   |\e[27;42m  \e[5;4;1;40;31mand\e[7;25;24;22;49;39m     #\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m#\e[27;42m  \e[44;37mthings\e[7;49;39m|\e[27;42m  \e[44;37mthings\e[45m)\e[7;49;39m #\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m#\e[27;42m  \e[45;37m)\e[7;49;39m     |          #\e[0m\n\e[27;25;24;22;45;37m  \e[7;49;39m<========+==========v\e[0m\n\e[27;25;24;22;45;37m  \e[49;39m[testing\e[41;30m             \e[0m\n\e[27;25;24;22;45;37m  \e[49;36m \e[45;37mtest(\e[41;30m               \e[0m\n\e[27;25;24;22;45;37m  \e[49;36m \e[42;39m  \e[44;37mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[25;24;22;41;30m   \e[0m\n\e[27;25;24;22;45;37m  \e[49;36m \e[42;39m  \e[44;37mthings\e[45m)\e[49;39m]\e[36m)\e[41;30m         \e[0m")
      (list
        (list 200 chain-3)
        "\e[0m\e[27;25;24;22;45;37m             \e[44m                                                          \e[7;49;39m^============================+======================================>\e[27;44;37m                                       \e[45m \e[0m\n\e[27;25;24;22;45;37m             \e[44m                                                          \e[7;49;39m#\e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[7;49;39m|\e[27m[testing\e[7;36m \e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[49;39m]\e[7m#\e[27;44;37m                                       \e[45m \e[0m\n\e[27;25;24;22;45;37m             \e[44m                                                          \e[7;49;39m+----------------------------+--------------------------------------+\e[27;44;37m                                       \e[45m \e[0m\n\e[27;25;24;22;45;37m             \e[44m                                                          \e[7;49;39m#\e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[7;49;39m|\e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[7;49;39m          #\e[27;44;37m                                       \e[45m \e[0m\n\e[27;25;24;22;49;36mwith-a-table(\e[45;37m(nested\e[49;39m[testing\e[7;36m \e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[49;39m]\e[7m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[44m \e[7;49;39m<============================+======================================v\e[27;44;37m \e[49;39m[testing\e[7;36m \e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[49;39m]\e[36m)\e[0m")
      (list
        (list 160 chain-3)
        "\e[0m\e[27;25;24;22;49;36mwith-a-table(\e[41;30m                                                                                                                    \e[0m\n\e[27;25;24;22;45;37m  \e[44m                                                          \e[7;49;39m^============================+======================================>\e[0m\n\e[27;25;24;22;45;37m  \e[44m                                                          \e[7;49;39m#\e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[7;49;39m|\e[27m[testing\e[7;36m \e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[49;39m]\e[7m#\e[0m\n\e[27;25;24;22;45;37m  \e[44m                                                          \e[7;49;39m+----------------------------+--------------------------------------+\e[0m\n\e[27;25;24;22;45;37m  \e[44m                                                          \e[7;49;39m#\e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[7;49;39m|\e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[7;49;39m          #\e[0m\n\e[27;25;24;22;45;37m  (nested\e[49;39m[testing\e[7;36m \e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[49;39m]\e[7m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[44m \e[7;49;39m<============================+======================================v\e[0m\n\e[27;25;24;22;45;37m  \e[49;39m[testing\e[7;36m \e[27;45;37mtest(\e[44mhello\e[7;49;39m \e[27;44;37mworld\e[7;49;39m \e[27;5;4;1;40;31mand\e[7;25;24;22;49;39m \e[27;44;37mthings\e[45m)\e[49;39m]\e[36m)\e[41;30m                                                                                        \e[0m")
      )
    _ = (forl
      (list (list width doc) expected) <- test-equalities
      (visual-check-equal?
        identity
        (styled-block->string (doc->styled-block ctx style-outer width doc))
        expected))
    (void)
    ))
