#lang racket/base
(provide
  (struct-out coord)
  (struct-out rect)
  (struct-out style)
  style-empty
  blank-string
  styled-string
  styled-block-fill
  styled-block-fill-blank
  styled-block-sub
  styled-block-blit
  styled-block->string
  screen-clear
  screen-save
  screen-restore
  with-screen-fresh
  cursor-hide
  cursor-show
  with-cursor-hidden
  stty
  with-stty
  with-stty-direct
  with-stty-previous
  maybe-read-char
  )

(require
  "maybe.rkt"
  "record.rkt"
  "sugar.rkt"
  racket/function
  racket/list
  racket/match
  racket/port
  racket/string
  racket/system
  )

(module+ test
  (require rackunit))

(define (tput arg) (system* (find-executable-path "tput") arg))

(define (screen-clear) (system* (find-executable-path "clear")))
; \e[?47h
(define (screen-save) (tput "smcup"))
; \e[?47l
(define (screen-restore) (tput "rmcup"))
(define-syntax with-screen-fresh
  (syntax-rules ()
    ((_ body ...)
     (dynamic-wind
       (lambda () (screen-save) (screen-clear))
       (lambda () body ...)
       screen-restore))))

; \e[?25l
(define (cursor-hide) (tput "civis"))
; \e[?25h
(define (cursor-show) (tput "cnorm"))
(define-syntax with-cursor-hidden
  (syntax-rules ()
    ((_ body ...)
     (dynamic-wind
       cursor-hide
       (lambda () body ...)
       cursor-show))))

(define (stty . args)
  (apply (curry system* (find-executable-path "stty")) args))
(define (stty-state-current)
  (string-trim (with-output-to-string (lambda () (stty "-g")))))
(define stty-state-saved (make-parameter (stty-state-current)))
(define (stty-state-recover) (stty (stty-state-saved)))
(define-syntax with-stty-saved
  (syntax-rules ()
    ((_ body ...)
     (parameterize ((stty-state-saved (stty-state-current)))
        body ...))))
(define-syntax with-stty
  (syntax-rules ()
    ((_ stty-args body ...)
     (let ((args stty-args))
       (with-stty-saved
         (dynamic-wind
           (lambda () (apply stty args))
           (lambda () body ...)
           stty-state-recover))))))
(define-syntax with-stty-direct
  (syntax-rules ()
    ((_ body ...)
     (with-stty (list "raw" "-echo") body ...))))
(define-syntax with-stty-previous
  (syntax-rules ()
    ((_ body ...)
     (with-stty (list (stty-state-saved)) body ...))))

(module+ test
  (check-equal?
    (with-stty-direct
      (stty-state-saved))
    (stty-state-current)
    ))

(module+ test
  (check-equal?
    (with-stty-direct
      (with-stty-previous
        (stty-state-current)))
    (stty-state-current)
    ))

(define (maybe-read-char) (if (char-ready?) (just (read-char)) (nothing)))

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
(define blank-codes (list 0 0 0 0 0 0))
(define (blank-string len)
  (sgrstr blank-codes (string->immutable-string (make-string len #\space))))
(def (sgrstr-blank? (sgrstr codes _)) (equal? codes blank-codes))

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

(def (sgrstr-length (sgrstr _ str)) (string-length str))
(define (styled-line-fill sgrc char count)
  (list (sgrstr sgrc (string->immutable-string (make-string count char)))))
(define (styled-line-length styled-line)
  (apply +
    (forl
      (sgrstr _ str) <- styled-line
      (string-length str))))
(def (styled-line-sub styled-line start len)
  (list _ styled-line) = (styled-line-split styled-line start)
  (list rstyled-line _) = (styled-line-split styled-line len)
  (reverse rstyled-line))
(def (styled-line-overlay overs unders)
  (let loop ((result '()) (overs overs) (pos 0))
    (match overs
      ('() (append* (reverse result)))
      ((cons over overs)
       (lets
         len = (sgrstr-length over)
         next = (if (sgrstr-blank? over)
                  (styled-line-sub unders pos len)
                  (list over))
         (loop (cons next result) overs (+ pos len)))))))
(def (styled-line-replace styled-line overlay start len)
  (list rprefix styled-line) = (styled-line-split styled-line start)
  (list runderlay suffix) = (styled-line-split styled-line len)
  rline = (reverse (styled-line-overlay overlay (reverse runderlay)))
  (styled-line-revappend rprefix (styled-line-revappend rline suffix)))
(def (styled-line-blit tgt tgt-start src)
  len = (styled-line-length src)
  (styled-line-replace tgt src tgt-start len))

(module+ test
  (check-equal?
    (styled-line-blit (list test-ss-2) 5 (styled-line-sub (list test-ss-0 test-ss-1) 4 9))
    (list
      (sgrstr test-sgrs-2 "five ")
      (sgrstr test-sgrs-0 "two ")
      (sgrstr test-sgrs-1 "three")
      (sgrstr test-sgrs-2 " eight"))
    ))

(module+ test
  (lets
    style-0 = style-empty
    style-1 = style-empty
    style-2 = (style 'red 'default #f #f #f #t)
    source = (list
               (styled-string style-0 "1234")
               (blank-string 3)
               (styled-string style-0 "567")
               (blank-string 4)
               (styled-string style-0 "890"))
    target = (list
               (styled-string style-1 "abcdef")
               (styled-string style-2 "ghijklmnop")
               (styled-string style-1 "qrstuvwxyz"))
    (check-equal?
      (styled-line-blit target 2 (styled-line-sub source 1 14))
      (list
        (styled-string style-1 "ab234f")
        (styled-string style-2 "gh")
        (styled-string style-0 "567")
        (styled-string style-2 "lmno")
        (styled-string style-1 "8qrstuvwxyz"))
      )))

(record coord x y)
(record rect loc w h)

(define (styled-block-fill sty char w h)
  (define sgrc (style->sgrcodes sty))
  (define row (styled-line-fill sgrc char w))
  (build-list h (lambda _ row)))
(define (styled-block-fill-blank w h)
  (define row (list (blank-string w)))
  (build-list h (lambda _ row)))
(def (styled-block-sub styled-block (rect (coord x y) w h))
  bh = (length styled-block)
  y = (min y bh)
  h = (min h (- bh y))
  styled-block = (take (drop styled-block y) h)
  (map (lambda (line) (styled-line-sub line x w)) styled-block))
(def (styled-block-blit tgt (coord tx ty) src)
  prefix = (take tgt ty)
  tgt = (drop tgt ty)
  suffix = (drop tgt (length src))
  blitted = (forl
              tgt-line <- tgt
              src-line <- src
              (styled-line-blit tgt-line tx src-line))
  (append prefix blitted suffix))

(module+ test
  (define test-block-0 (styled-block-fill test-style-0 #\- 20 30))
  (define test-block-1-0 (styled-block-fill-blank 15 18))
  (define test-block-1-1 (styled-block-fill test-style-1 #\o 10 12))
  (define test-block-1 (styled-block-blit test-block-1-0 (coord 2 3)
                                          (styled-block-sub test-block-1-1 (rect (coord 0 0) 10 12))))
  (check-equal?
    (styled-block-blit test-block-0 (coord 4 9)
                       (styled-block-sub test-block-1 (rect (coord 1 2) 7 9)))
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
  ss-empty = (blank-string 0)
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
                                          (styled-block-sub test-block-3 (rect (coord 1 2) 6 8))))
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