#lang racket/base
(provide
  (struct-out coord)
  (struct-out size)
  (struct-out rect)
  (struct-out style)
  style-empty
  blank-string
  styled-string
  styled-block-size
  styled-block-fill
  styled-block-fill-blank
  styled-block-expand
  styled-block-append-horizontal
  styled-block-append-vertical
  styled-block-sub
  styled-block-blit
  styled-block->string
  screen-size
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
  "list.rkt"
  "maybe.rkt"
  "record.rkt"
  "string.rkt"
  "sugar.rkt"
  racket/function
  racket/list
  racket/match
  racket/port
  racket/string
  racket/system
  )

(module+ test
  (require
    "test.rkt"
    rackunit))

(record coord x y)
(record size w h)
(record rect loc sz)

(define (tput arg) (system* (find-executable-path "tput") arg))

(define (screen-size)
  (define (out->num thnk)
    (string->number (string-trim (with-output-to-string thnk))))
  (size
    (out->num (thunk (tput "cols")))
    (out->num (thunk (tput "lines")))))
(define (screen-clear) (system* (find-executable-path "clear")))
; \e[?47h
(define (screen-save) (tput "smcup"))
; \e[?47l
(define (screen-restore) (tput "rmcup"))
(define-syntax with-screen-fresh
  (syntax-rules ()
    ((_ body ...)
     (dynamic-wind
       (thunk (screen-save) (screen-clear))
       (thunk body ...)
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
       (thunk body ...)
       cursor-show))))

(define (stty . args)
  (apply (curry system* (find-executable-path "stty")) args))
(define (stty-state-current)
  (string-trim (with-output-to-string (thunk (stty "-g")))))
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
           (thunk (apply stty args))
           (thunk body ...)
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
  (sgrstr blank-codes (make-immutable-string len #\space)))
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
  (if (= count 0) (list)
    (list (sgrstr sgrc (make-immutable-string count char)))))
(define (styled-line-length styled-line)
  (sum (forl
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

(def (styled-block-size block)
  height = (length block)
  width = (if (= height 0) 0 (styled-line-length (car block)))
  (size width height))
(def (styled-block-fill sty char (size w h))
  sgrc = (style->sgrcodes sty)
  row = (styled-line-fill sgrc char w)
  (replicate h row))
(def (styled-block-fill-blank (size w h))
  row = (list (blank-string w))
  (replicate h row))
(def (styled-block-expand sty char block (size width height) down? right?)
  fill = (lambda (sz) (styled-block-fill sty char sz))
  (size bw bh) = (styled-block-size block)
  width = (max bw width)
  height = (max bh height)
  w-ext = (fill (size (- width bw) bh))
  h-ext = (fill (size width (- height bh)))
  (list bl br) = (if right? (list block w-ext) (list w-ext block))
  block = (map append bl br)
  (list bt bb) = (if down? (list block h-ext) (list h-ext block))
  (append bt bb))
(def (styled-block-append-horizontal sty char down? prefix suffix)
  (size pw ph) = (styled-block-size prefix)
  (size sw sh) = (styled-block-size suffix)
  prefix = (styled-block-expand sty char prefix (size pw sh) down? #t)
  suffix = (styled-block-expand sty char suffix (size sw ph) down? #t)
  (map append prefix suffix))
(def (styled-block-append-vertical sty char right? prefix suffix)
  (size pw ph) = (styled-block-size prefix)
  (size sw sh) = (styled-block-size suffix)
  prefix = (styled-block-expand sty char prefix (size sw ph) #t right?)
  suffix = (styled-block-expand sty char suffix (size pw sh) #t right?)
  (append prefix suffix))
(def (styled-block-sub styled-block (rect (coord x y) (size w h)))
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
  (define test-block-0 (styled-block-fill test-style-0 #\- (size 20 30)))
  (define test-block-1-0 (styled-block-fill-blank (size 15 18)))
  (define test-block-1-1 (styled-block-fill test-style-1 #\o (size 10 12)))
  (define test-block-1 (styled-block-blit test-block-1-0 (coord 2 3)
                                          (styled-block-sub test-block-1-1
                                                            (rect (coord 0 0) (size 10 12)))))
  (check-equal?
    (styled-block-size '())
    (size 0 0)
    )
  (check-equal?
    (styled-block-size '(()))
    (size 0 1)
    )
  (check-equal?
    (styled-block-size test-block-1)
    (size 15 18)
    )
  (check-equal?
    (styled-block-expand test-style-0 #\$ test-block-1-1 (size 12 15) #t #f)
    (list
      (list (styled-string test-style-0 "$$") (sgrstr test-sgrs-1 "oooooooooo"))
      (list (styled-string test-style-0 "$$") (sgrstr test-sgrs-1 "oooooooooo"))
      (list (styled-string test-style-0 "$$") (sgrstr test-sgrs-1 "oooooooooo"))
      (list (styled-string test-style-0 "$$") (sgrstr test-sgrs-1 "oooooooooo"))
      (list (styled-string test-style-0 "$$") (sgrstr test-sgrs-1 "oooooooooo"))
      (list (styled-string test-style-0 "$$") (sgrstr test-sgrs-1 "oooooooooo"))
      (list (styled-string test-style-0 "$$") (sgrstr test-sgrs-1 "oooooooooo"))
      (list (styled-string test-style-0 "$$") (sgrstr test-sgrs-1 "oooooooooo"))
      (list (styled-string test-style-0 "$$") (sgrstr test-sgrs-1 "oooooooooo"))
      (list (styled-string test-style-0 "$$") (sgrstr test-sgrs-1 "oooooooooo"))
      (list (styled-string test-style-0 "$$") (sgrstr test-sgrs-1 "oooooooooo"))
      (list (styled-string test-style-0 "$$") (sgrstr test-sgrs-1 "oooooooooo"))
      (list (styled-string test-style-0 "$$$$$$$$$$$$"))
      (list (styled-string test-style-0 "$$$$$$$$$$$$"))
      (list (styled-string test-style-0 "$$$$$$$$$$$$"))
      ))
  (check-equal?
    (styled-block-append-vertical test-style-0 #\@ #t test-block-1-0 test-block-1-1)
    (list
      (list (blank-string 15))
      (list (blank-string 15))
      (list (blank-string 15))
      (list (blank-string 15))
      (list (blank-string 15))
      (list (blank-string 15))
      (list (blank-string 15))
      (list (blank-string 15))
      (list (blank-string 15))
      (list (blank-string 15))
      (list (blank-string 15))
      (list (blank-string 15))
      (list (blank-string 15))
      (list (blank-string 15))
      (list (blank-string 15))
      (list (blank-string 15))
      (list (blank-string 15))
      (list (blank-string 15))
      (list (sgrstr test-sgrs-1 "oooooooooo") (sgrstr test-sgrs-0 "@@@@@"))
      (list (sgrstr test-sgrs-1 "oooooooooo") (sgrstr test-sgrs-0 "@@@@@"))
      (list (sgrstr test-sgrs-1 "oooooooooo") (sgrstr test-sgrs-0 "@@@@@"))
      (list (sgrstr test-sgrs-1 "oooooooooo") (sgrstr test-sgrs-0 "@@@@@"))
      (list (sgrstr test-sgrs-1 "oooooooooo") (sgrstr test-sgrs-0 "@@@@@"))
      (list (sgrstr test-sgrs-1 "oooooooooo") (sgrstr test-sgrs-0 "@@@@@"))
      (list (sgrstr test-sgrs-1 "oooooooooo") (sgrstr test-sgrs-0 "@@@@@"))
      (list (sgrstr test-sgrs-1 "oooooooooo") (sgrstr test-sgrs-0 "@@@@@"))
      (list (sgrstr test-sgrs-1 "oooooooooo") (sgrstr test-sgrs-0 "@@@@@"))
      (list (sgrstr test-sgrs-1 "oooooooooo") (sgrstr test-sgrs-0 "@@@@@"))
      (list (sgrstr test-sgrs-1 "oooooooooo") (sgrstr test-sgrs-0 "@@@@@"))
      (list (sgrstr test-sgrs-1 "oooooooooo") (sgrstr test-sgrs-0 "@@@@@"))
      ))
  (check-equal?
    (styled-block-append-horizontal test-style-0 #\% #f test-block-1-0 test-block-1-1)
    (list
      (list (blank-string 15) (sgrstr test-sgrs-0 "%%%%%%%%%%"))
      (list (blank-string 15) (sgrstr test-sgrs-0 "%%%%%%%%%%"))
      (list (blank-string 15) (sgrstr test-sgrs-0 "%%%%%%%%%%"))
      (list (blank-string 15) (sgrstr test-sgrs-0 "%%%%%%%%%%"))
      (list (blank-string 15) (sgrstr test-sgrs-0 "%%%%%%%%%%"))
      (list (blank-string 15) (sgrstr test-sgrs-0 "%%%%%%%%%%"))
      (list (blank-string 15) (sgrstr test-sgrs-1 "oooooooooo"))
      (list (blank-string 15) (sgrstr test-sgrs-1 "oooooooooo"))
      (list (blank-string 15) (sgrstr test-sgrs-1 "oooooooooo"))
      (list (blank-string 15) (sgrstr test-sgrs-1 "oooooooooo"))
      (list (blank-string 15) (sgrstr test-sgrs-1 "oooooooooo"))
      (list (blank-string 15) (sgrstr test-sgrs-1 "oooooooooo"))
      (list (blank-string 15) (sgrstr test-sgrs-1 "oooooooooo"))
      (list (blank-string 15) (sgrstr test-sgrs-1 "oooooooooo"))
      (list (blank-string 15) (sgrstr test-sgrs-1 "oooooooooo"))
      (list (blank-string 15) (sgrstr test-sgrs-1 "oooooooooo"))
      (list (blank-string 15) (sgrstr test-sgrs-1 "oooooooooo"))
      (list (blank-string 15) (sgrstr test-sgrs-1 "oooooooooo"))
      ))
  (check-equal?
    (styled-block-blit test-block-0 (coord 4 9)
                       (styled-block-sub test-block-1
                                         (rect (coord 1 2) (size 7 9))))
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
  str-eol = (string-append str-reset "\n")
  ss-empty = (blank-string 0)
  block = (forl
            sline <- sb
            (string-append*
              (forl
                (sgrstr codes-prev _) <- (cons ss-empty sline)
                (sgrstr codes str) <- sline
                delta = (sgrcodes-delta codes-prev codes)
                (string-append (sgrcodes->string delta) str))))
  (string-append str-reset (string-join block str-eol) str-reset))

(module+ test
  (define test-style-3 (style 'white 'blue #t #f #f #f))
  (define test-style-4 (style 'yellow 'green #f #f #f #f))
  (define test-block-2 (styled-block-fill test-style-3 #\~ (size 30 20)))
  (define test-block-3 (styled-block-fill test-style-4 #\, (size 10 12)))
  (define test-block-4 (styled-block-blit test-block-2 (coord 10 5)
                                          (styled-block-sub test-block-3
                                                            (rect (coord 1 2) (size 6 8)))))
  (visual-check-equal?
    identity
    (styled-block->string test-block-4)
    (string-append
      "\e[0m"
      "\e[27;25;24;1;44;37m~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\e[0m\n"
      "\e[27;25;24;1;44;37m~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\e[0m\n"
      "\e[27;25;24;1;44;37m~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\e[0m\n"
      "\e[27;25;24;1;44;37m~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\e[0m\n"
      "\e[27;25;24;1;44;37m~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\e[0m\n"
      "\e[27;25;24;1;44;37m~~~~~~~~~~\e[22;42;33m,,,,,,\e[1;44;37m~~~~~~~~~~~~~~\e[0m\n"
      "\e[27;25;24;1;44;37m~~~~~~~~~~\e[22;42;33m,,,,,,\e[1;44;37m~~~~~~~~~~~~~~\e[0m\n"
      "\e[27;25;24;1;44;37m~~~~~~~~~~\e[22;42;33m,,,,,,\e[1;44;37m~~~~~~~~~~~~~~\e[0m\n"
      "\e[27;25;24;1;44;37m~~~~~~~~~~\e[22;42;33m,,,,,,\e[1;44;37m~~~~~~~~~~~~~~\e[0m\n"
      "\e[27;25;24;1;44;37m~~~~~~~~~~\e[22;42;33m,,,,,,\e[1;44;37m~~~~~~~~~~~~~~\e[0m\n"
      "\e[27;25;24;1;44;37m~~~~~~~~~~\e[22;42;33m,,,,,,\e[1;44;37m~~~~~~~~~~~~~~\e[0m\n"
      "\e[27;25;24;1;44;37m~~~~~~~~~~\e[22;42;33m,,,,,,\e[1;44;37m~~~~~~~~~~~~~~\e[0m\n"
      "\e[27;25;24;1;44;37m~~~~~~~~~~\e[22;42;33m,,,,,,\e[1;44;37m~~~~~~~~~~~~~~\e[0m\n"
      "\e[27;25;24;1;44;37m~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\e[0m\n"
      "\e[27;25;24;1;44;37m~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\e[0m\n"
      "\e[27;25;24;1;44;37m~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\e[0m\n"
      "\e[27;25;24;1;44;37m~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\e[0m\n"
      "\e[27;25;24;1;44;37m~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\e[0m\n"
      "\e[27;25;24;1;44;37m~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\e[0m\n"
      "\e[27;25;24;1;44;37m~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\e[0m")
    ))
