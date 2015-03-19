#lang racket/base
(provide
  decorate-controller
  dispatch-events
  dispatch-react-loop
  event-keycount
  event-keypress
  event-terminate
  event-tick
  keycount->events
  keycount-controller
  keypress-event-source
  latency-default
  markout-dispatch-react-loop
  note-terminated
  note-view
  sleep-remaining
  sources->source
  terminal-event-source
  tick-event-source
  timer-new
  timer-now
  )

(require
  "dict.rkt"
  "generator.rkt"
  "markout.rkt"
  "maybe.rkt"
  "monad.rkt"
  "record.rkt"
  "sugar.rkt"
  "terminal.rkt"
  racket/function
  racket/list
  racket/match
  )

(module+ test
  (require rackunit))

(records base-event
  (event-terminate)
  (event-tick dt)
  (event-keypress char)
  (event-keycount char count))

(records base-note
  (note-terminated)
  (note-view view))

(define latency-default 0.1)

(define ((timer-new start))
  (lets
    next = (current-milliseconds)
    dt = (- next start)
    (list (timer-new next) dt)))
(define (timer-now) (timer-new (current-milliseconds)))
(define (sleep-remaining total timer)
  (lets
    (list _ overhead) = (timer)
    sleep-duration = (/ (max 0 (- (* total 1000) overhead)) 1000)
    (sleep sleep-duration)))

(define ((sources->source sources) dt)
  (append* (map (lambda (source) (source dt)) sources)))
(define (tick-event-source dt) (list (event-tick dt)))
(define (keypress-event-source dt) (map event-keypress (read-chars-ready)))
(define terminal-event-source
  (sources->source (list keypress-event-source tick-event-source)))

(define (dispatch-fold f ctrl xs)
  (forf
    (gen-susp notes ctrl) = (gen-susp '() ctrl)
    x <- xs
    (gen-susp new-notes ctrl) = (f ctrl x)
    (gen-susp(append notes new-notes) ctrl)))
(define (dispatch-events ctrl events)
  (dispatch-fold (lambda (ctrl event) (ctrl event)) ctrl events))
(define (dispatch-react-loop react ctrl source (latency latency-default))
  (def (loop react ctrl timer)
    (list timer dt) = (timer)
    (gen-susp notes ctrl) = (dispatch-events ctrl (source dt))
    (match (react notes)
      ((just react)
       (begin
         (sleep-remaining latency timer)
         (loop react ctrl timer)))
      ((nothing) (void))))
  (loop react ctrl (timer-now)))

(module+ test
  (def (tick-ctrl (event-tick dt)) (gen-susp (list (note-view dt)) tick-ctrl))
  (check-equal?
    (dispatch-events
      tick-ctrl ((sources->source
                   (list tick-event-source tick-event-source)) 12))
    (gen-susp (list (note-view 12) (note-view 12)) tick-ctrl)
    ))

(record model event-source command-sink)

(def (model-control-loop ctrl (model event-source command-sink))
  event = (event-source)
  (match (ctrl event)
    ((gen-result r) r)
    ((gen-susp command ctrl)
     (lets
       next-model = (command-sink command)
       (model-control-loop ctrl next-model)))))

(module+ test
  (lets
    ctrl =
    (gn yield (e0)
      e1 = (yield (void))
      e2 = (yield (void))
      (list e2 e1 e0))
    events = (map (lambda (ev) (thunk ev)) '(a b c))
    react = (fnr (react events)
      (lambda (command) (model (first events) (react (rest events)))))
    mdl = ((react events) (void))
    (check-equal?
      (model-control-loop ctrl mdl)
      '(c b a)
      )))

(define (decorate-controller dec ctrl)
  (define dctrl (dec ctrl))
  (fn (event)
    (gen-susp result ctrl) = (dctrl event)
    (gen-susp result (decorate-controller dec ctrl))))

(define keycount-controller
  ((lambda ()
     (define (digits->count digits)
       (if (empty? digits) 1 (string->number (list->string (reverse digits)))))
     (define (new digits)
       (fn (event)
        (list digits mevent) =
        (match event
          ((event-keypress char)
           (if (char-numeric? char)
             (list (list* char digits) (nothing))
             (list '() (just (event-keycount char (digits->count digits))))))
          (_ (list digits (just event))))
        (gen-susp mevent (new digits))))
     (new '()))))

(define ((keycount->events keymap) event)
  (match event
    ((event-keycount char count)
     (match (dict-get keymap char)
       ((just action) (action count))
       ((nothing) (list event))))
    (_ (list event))))

(module+ test
  (define test-keymap
    (hash
      #\v (lambda (count) (list (note-view count)))
      #\q (lambda (_) (list (event-terminate)))))
  (define key-ctrl
    (gen-compose (maybe-gen '() (fn->gen (keycount->events test-keymap)))
                 keycount-controller))
  (define (test-key-source dt)
    (list (event-keypress #\4) (event-keypress #\2) (event-keypress #\v)
          (event-keypress #\q)))
  (check-equal?
    (lets
      (gen-susp result _) = (dispatch-events key-ctrl (test-key-source 12))
      result)
    (list (note-view 42) (event-terminate))
    ))

(def (display-doc doc)
  (size width height) = (screen-size)
  ctx = (sizing-context-new-default)
  block = (doc->styled-block ctx style-empty width doc)
  doc-str = (styled-block->string block)
  _ = (screen-clear)
  (displayln doc-str))

(define ((markout-reactor doc) notes)
  (define (handle-note doc note)
    (match note
      ((note-terminated) (nothing))
      ((note-view next-doc) (just next-doc))
      (_ (just doc))))
  (begin/with-monad maybe-monad
    next-doc <- (monad-foldl maybe-monad handle-note doc notes)
    _ = (unless (eq? doc next-doc) (display-doc next-doc))
    (pure (markout-reactor next-doc))))

(define (markout-dispatch-react-loop doc-0 ctrl (latency latency-default))
  (with-cursor-hidden
    (with-stty-direct
      (with-screen-fresh
        (display-doc doc-0)
        (dispatch-react-loop (markout-reactor doc-0)
                             ctrl terminal-event-source latency)))))

(module+ main
  (define (doc-str str) (doc-atom style-empty str))
  (define (doc-append . docs) (vertical-list style-empty docs))
  (define ((ctrl doc) event)
    (def (note-doc-append doc-tail)
      new-doc = (doc-append doc doc-tail)
      (gen-susp (list (note-view new-doc)) (ctrl new-doc)))
    (match event
      ((event-terminate) (gen-susp (list (note-terminated)) (ctrl doc)))
      ((event-tick dt)
       (note-doc-append (doc-str (format "time-delta: ~ams" dt))))
      ((event-keycount char count)
       (note-doc-append (doc-str (format "keycount: ~v,~a" char count))))
      (_ (gen-susp '() (ctrl doc)))))
  (define keymap
    (hash
      #\q (fn (_) (list (event-terminate)))
      ))
  (lets
    sty = (style 'yellow 'blue #f #f #f #f)
    doc = (doc-preformatted (styled-block-fill sty #\x (size 10 20)))
    doc = (doc-append doc (doc-str "Press 'q' to quit this test."))
    ctrl = (gen-compose
             (decorate-controller (curry dispatch-events) (ctrl doc))
             (maybe-gen '() (fn->gen (keycount->events keymap))))
    ctrl = (gen-compose ctrl keycount-controller)
    (markout-dispatch-react-loop doc ctrl)
    ))
