#lang racket/base
(provide
  (struct-out coord)
  (struct-out rect)
  (struct-out style)
  style-empty
  styled-string
  styled-block-fill
  styled-block-blit
  styled-block->string
  screen-clear
  screen-save
  screen-restore
  cursor-hide
  cursor-show
  )

(require
  "record.rkt"
  "sugar.rkt"
  racket/list
  racket/match
  racket/string
  racket/system
  )

(module+ test
  (require rackunit))

(define (screen-clear) (system* (find-executable-path "clear")))
; \e[?47h
(define (screen-save) (system* (find-executable-path "tput") "smcup"))
; \e[?47l
(define (screen-restore) (system* (find-executable-path "tput") "rmcup"))

; \e[?25l
(define (cursor-hide) (system* (find-executable-path "tput") "civis"))
; \e[?25h
(define (cursor-show) (system* (find-executable-path "tput") "cnorm"))

(define colors
  (make-immutable-hash
    (forl
      name <- '(black red green yellow blue magenta cyan white default)
      intensity <- (append (range 8) (list 9))
      (cons name intensity))))
(define (intensity-fg->sgrcode intensity) (+ 30 intensity))
(define (intensity-bg->sgrcode intensity) (+ 40 intensity))
(define (color->intensity color) (hash-ref colors color))
(define color-fg->sgrcode (compose1 intensity-fg->sgrcode color->intensity))
(define color-bg->sgrcode (compose1 intensity-bg->sgrcode color->intensity))

(define modifiers
  (hash
    'reset 0
    'on-bold 1
    'on-underline 4
    'on-blink 5
    'on-invert 7
    'off-bold 22
    'off-underline 24
    'off-blink 25
    'off-invert 27
    ))
(define (modifier->sgrcode modifier) (hash-ref modifiers modifier))

(record style color-fg color-bg bold? underline? blink? invert?)
(define style-empty (style 'default 'default #f #f #f #f))

(def (style->sgrcodes (style fgc bgc bold? underline? blink? invert?))
  (append
    (list (color-fg->sgrcode fgc) (color-bg->sgrcode bgc))
    (forl
      (list on? on off) <- (list
                            (list bold? 'on-bold 'off-bold)
                            (list underline? 'on-underline 'off-underline)
                            (list blink? 'on-blink 'off-blink)
                            (list invert? 'on-invert 'off-invert))
      (modifier->sgrcode (if on? on off)))))

(module+ test
  (check-equal?
    (style->sgrcodes (style 'red 'blue #f #t #f #f))
    (list 31 44 22 4 25 27)
    ))

(record sgrstr codes str)
(define (styled-string sty str) (sgrstr (style->sgrcodes sty) str))

(define (styled-line-split styled-line idx)
  (let loop ((lhs '()) (styled-line styled-line) (idx idx))
    (if (= 0 idx)
      (list lhs styled-line)
      (match styled-line
        ('() (cons lhs '()))
        ((cons ss rhs)
         (match-let* (((sgrstr sgrcs str) ss)
                      (len (string-length str)))
           (if (<= len idx)
             (loop (cons ss lhs) rhs (- idx len))
             (loop (cons (sgrstr sgrcs (substring str 0 idx)) lhs)
                   (cons (sgrstr sgrcs (substring str idx)) rhs)
                   0))))))))

(define (styled-line-revappend lhs rhs)
  (match* (lhs rhs)
    (('() _) rhs)
    (((cons (sgrstr llc lls) lhs) (cons (sgrstr rfc rfs) rhs))
     #:when (empty? (sgrcodes-delta llc rfc))
     (styled-line-revappend lhs (cons (sgrstr rfc (string-append lls rfs)) rhs)))
    (((cons llast lhs) rhs)
     (styled-line-revappend lhs (cons llast rhs)))))

(module+ test
  (define test-style-0 (style 'green 'white #t #f #f #f))
  (define test-style-1 (style 'green 'white #t #t #f #f))
  (define test-style-2 (style 'blue 'white #f #t #f #f))
  (define test-sgrs-0 (style->sgrcodes test-style-0))
  (define test-ss-0 (sgrstr test-sgrs-0 "one two "))
  (define test-sgrs-1 (style->sgrcodes test-style-1))
  (define test-ss-1 (sgrstr test-sgrs-1 "three four"))
  (define test-sgrs-2 (style->sgrcodes test-style-2))
  (define test-ss-2 (sgrstr test-sgrs-2 "five six seven eight"))
  (define test-ss-1-0 (sgrstr test-sgrs-1 "three "))
  (define test-ss-1-1 (sgrstr test-sgrs-1 "four"))
  (define test-input (list test-ss-0 test-ss-1 test-ss-2))
  (check-equal?
    (styled-line-split test-input 0)
    (list '() test-input)
    )
  (check-equal?
    (styled-line-split test-input 14)
    (list (reverse (list test-ss-0 test-ss-1-0)) (list test-ss-1-1 test-ss-2))
    )
  (check-equal?
    (styled-line-split test-input 38)
    (list (reverse test-input) '())
    )
  (check-equal?
    (match-let (((list lhs rhs) (styled-line-split test-input 0)))
      (styled-line-revappend lhs rhs))
    test-input
    )
  (check-equal?
    (match-let (((list lhs rhs) (styled-line-split test-input 14)))
      (styled-line-revappend lhs rhs))
    test-input
    )
  (check-equal?
    (match-let (((list lhs rhs) (styled-line-split test-input 32)))
      (styled-line-revappend lhs rhs))
    test-input
    )
  )

(define (styled-line-fill sgrc char count)
  (list (sgrstr sgrc (string->immutable-string (make-string count char)))))
(define (styled-line-length styled-line)
  (apply +
    (forl
      (sgrstr _ str) <- styled-line
      (string-length str))))
(def (styled-line-rextract styled-line start len)
  (list _ styled-line) = (styled-line-split styled-line start)
  (list rstyled-line _) = (styled-line-split styled-line len)
  rstyled-line)
(def (styled-line-replace styled-line rstyled-line start len)
  (list rprefix styled-line) = (styled-line-split styled-line start)
  (list _ suffix) = (styled-line-split styled-line len)
  (styled-line-revappend rprefix (styled-line-revappend rstyled-line suffix)))
(def (styled-line-blit tgt tgt-start src src-start src-len)
  len = (min (- (styled-line-length src) src-start) src-len)
  rline = (styled-line-rextract src src-start len)
  (styled-line-replace tgt rline tgt-start len))

(module+ test
  (check-equal?
    (styled-line-blit (list test-ss-2) 5 (list test-ss-0 test-ss-1) 4 9)
    (list
      (sgrstr test-sgrs-2 "five ")
      (sgrstr test-sgrs-0 "two ")
      (sgrstr test-sgrs-1 "three")
      (sgrstr test-sgrs-2 " eight"))
    ))

(record coord x y)
(record rect loc w h)

(define (styled-block-fill sty char w h)
  (define sgrc (style->sgrcodes sty))
  (build-list h (lambda _ (styled-line-fill sgrc char w))))
(def (styled-block-sub styled-block (rect (coord x y) w h))
  bh = (length styled-block)
  y = (min y bh)
  h = (min h (- bh y))
  styled-block = (take (drop styled-block y) h)
  (map (lambda (line) (reverse (styled-line-rextract line x w))) styled-block))
(def (styled-block-blit tgt (coord tx ty) src src-rect)
  (rect (coord x y) w h) = src-rect
  src = (styled-block-sub src src-rect)
  h = (length src)
  prefix = (take tgt ty)
  tgt = (drop tgt ty)
  suffix = (drop tgt h)
  blitted = (forl
              tgt-line <- tgt
              src-line <- src
              (styled-line-blit tgt-line tx src-line 0 w))
  (append prefix blitted suffix))

(module+ test
  (define test-block-0 (styled-block-fill test-style-0 #\- 20 30))
  (define test-block-1 (styled-block-fill test-style-1 #\o 10 12))
  (check-equal?
    (styled-block-blit test-block-0 (coord 5 10) test-block-1 (rect (coord 1 2) 6 8))
    (list
      (list (sgrstr test-sgrs-0 "--------------------"))
      (list (sgrstr test-sgrs-0 "--------------------"))
      (list (sgrstr test-sgrs-0 "--------------------"))
      (list (sgrstr test-sgrs-0 "--------------------"))
      (list (sgrstr test-sgrs-0 "--------------------"))
      (list (sgrstr test-sgrs-0 "--------------------"))
      (list (sgrstr test-sgrs-0 "--------------------"))
      (list (sgrstr test-sgrs-0 "--------------------"))
      (list (sgrstr test-sgrs-0 "--------------------"))
      (list (sgrstr test-sgrs-0 "--------------------"))
      (list (sgrstr test-sgrs-0 "-----") (sgrstr test-sgrs-1 "oooooo") (sgrstr test-sgrs-0 "---------"))
      (list (sgrstr test-sgrs-0 "-----") (sgrstr test-sgrs-1 "oooooo") (sgrstr test-sgrs-0 "---------"))
      (list (sgrstr test-sgrs-0 "-----") (sgrstr test-sgrs-1 "oooooo") (sgrstr test-sgrs-0 "---------"))
      (list (sgrstr test-sgrs-0 "-----") (sgrstr test-sgrs-1 "oooooo") (sgrstr test-sgrs-0 "---------"))
      (list (sgrstr test-sgrs-0 "-----") (sgrstr test-sgrs-1 "oooooo") (sgrstr test-sgrs-0 "---------"))
      (list (sgrstr test-sgrs-0 "-----") (sgrstr test-sgrs-1 "oooooo") (sgrstr test-sgrs-0 "---------"))
      (list (sgrstr test-sgrs-0 "-----") (sgrstr test-sgrs-1 "oooooo") (sgrstr test-sgrs-0 "---------"))
      (list (sgrstr test-sgrs-0 "-----") (sgrstr test-sgrs-1 "oooooo") (sgrstr test-sgrs-0 "---------"))
      (list (sgrstr test-sgrs-0 "--------------------"))
      (list (sgrstr test-sgrs-0 "--------------------"))
      (list (sgrstr test-sgrs-0 "--------------------"))
      (list (sgrstr test-sgrs-0 "--------------------"))
      (list (sgrstr test-sgrs-0 "--------------------"))
      (list (sgrstr test-sgrs-0 "--------------------"))
      (list (sgrstr test-sgrs-0 "--------------------"))
      (list (sgrstr test-sgrs-0 "--------------------"))
      (list (sgrstr test-sgrs-0 "--------------------"))
      (list (sgrstr test-sgrs-0 "--------------------"))
      (list (sgrstr test-sgrs-0 "--------------------"))
      (list (sgrstr test-sgrs-0 "--------------------"))
      )
    ))

(define (sgrcodes-delta cs0 cs1)
  (forf
    sgrcodes = '()
    c0 <- cs0
    c1 <- cs1
    (if (= c0 c1) sgrcodes (cons c1 sgrcodes))))

(module+ test
  (check-equal?
    (sgrcodes-delta
      (style->sgrcodes (style 'red 'blue #f #t #f #f))
      (style->sgrcodes (style 'green 'blue #t #t #f #f)))
    (reverse (list 32 1))
    ))

(define (sgrcodes->string sgrcodes)
  (if (empty? sgrcodes)
    ""
    (format "\e[~am" (string-join (map number->string sgrcodes) ";"))))

(def (styled-block->string sb)
  str-reset = (sgrcodes->string (list 0))
  ss-empty = (sgrstr (list 0 0 0 0 0 0) "")
  block = (forl
            slp <- (cons (list) sb)
            sline <- sb
            ss-prev = (last (cons ss-empty slp))
            (string-append*
              (forl
                (sgrstr codes-prev _) <- (cons ss-prev sline)
                (sgrstr codes str) <- sline
                delta = (sgrcodes-delta codes-prev codes)
                (string-append (sgrcodes->string delta) str))))
  (string-append str-reset (string-join block "\n") str-reset))

(module+ test
  (define test-style-3 (style 'white 'blue #t #f #f #f))
  (define test-style-4 (style 'yellow 'green #f #f #f #f))
  (define test-block-2 (styled-block-fill test-style-3 #\~ 30 20))
  (define test-block-3 (styled-block-fill test-style-4 #\, 10 12))
  (define test-block-4 (styled-block-blit test-block-2 (coord 10 5)
                                      test-block-3 (rect (coord 1 2) 6 8)))
  (check-equal?
    (styled-block->string test-block-4)
    (string-append
      "\e[0m\e[27;25;24;1;44;37m"
      "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n"
      "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n"
      "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n"
      "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n"
      "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n"
      "~~~~~~~~~~\e[22;42;33m,,,,,,\e[1;44;37m~~~~~~~~~~~~~~\n"
      "~~~~~~~~~~\e[22;42;33m,,,,,,\e[1;44;37m~~~~~~~~~~~~~~\n"
      "~~~~~~~~~~\e[22;42;33m,,,,,,\e[1;44;37m~~~~~~~~~~~~~~\n"
      "~~~~~~~~~~\e[22;42;33m,,,,,,\e[1;44;37m~~~~~~~~~~~~~~\n"
      "~~~~~~~~~~\e[22;42;33m,,,,,,\e[1;44;37m~~~~~~~~~~~~~~\n"
      "~~~~~~~~~~\e[22;42;33m,,,,,,\e[1;44;37m~~~~~~~~~~~~~~\n"
      "~~~~~~~~~~\e[22;42;33m,,,,,,\e[1;44;37m~~~~~~~~~~~~~~\n"
      "~~~~~~~~~~\e[22;42;33m,,,,,,\e[1;44;37m~~~~~~~~~~~~~~\n"
      "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n"
      "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n"
      "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n"
      "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n"
      "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n"
      "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n"
      "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\e[0m")
    ))
