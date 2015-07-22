#lang racket/base
(provide
  decorate-controller
  dispatch-events
  dispatch-notes
  event-keypress
  event-source-model
  event-terminate
  event-tick
  keypress-event-source
  latency-default
  markout-model-control-loop
  markout-view-model
  model-control-loop
  note-terminated
  note-view
  sleep-remaining
  sources->source
  terminal-event-model
  terminal-event-source
  tick-event-source
  timer-new
  timer-now
  )

(require
  "dict.rkt"
  "either.rkt"
  "generator.rkt"
  "markout.rkt"
  "maybe.rkt"
  "monad.rkt"
  "record.rkt"
  "sugar.rkt"
  "terminal.rkt"
  racket/dict
  racket/function
  racket/list
  racket/match
  )

(module+ test
  (require rackunit))

(records base-event
  (event-terminate)
  (event-tick dt)
  (event-keypress char))

(records base-note
  (note-terminated)
  (note-view view))

(define latency-default 0.1)

(define ((timer-new start))
  (lets
    next = (current-milliseconds)
    dt = (- next start)
    (gen-susp dt (timer-new next))))
(define (timer-now) (timer-new (current-milliseconds)))
(def (sleep-remaining total timer)
  (gen-susp overhead _) = (timer)
  sleep-duration = (/ (max 0 (- (* total 1000) overhead)) 1000)
  (sleep sleep-duration))

(define ((sources->source sources) dt)
  (append* (map (lambda (source) (source dt)) sources)))
(define (tick-event-source dt) (list (event-tick dt)))
(define (keypress-event-source dt) (map event-keypress (read-chars-ready)))
(define terminal-event-source
  (sources->source (list keypress-event-source tick-event-source)))

(define (keypress-thread chan)
  (define (loop)
    (channel-put chan (event-keypress (read-char)))
    (loop))
  (thread loop))

(define (tick-thread duration chan)
  (def (loop timer)
    _ = (sleep-remaining duration timer)
    (gen-susp dt timer) = (timer)
    _ = (channel-put chan (event-tick dt))
    (loop timer))
  (thread (thunk (loop (timer-now)))))

(define (start-terminal-event-threads latency)
  (define chan (make-channel))
  (define ts (list (keypress-thread chan) (tick-thread latency chan)))
  (list chan (thunk (map kill-thread ts))))

(define (model-control-loop ctrl model) (gen-coloop ctrl model))

(module+ test
  (lets
    ctrl =
    (gn yield (e0)
      e1 = (yield (void))
      e2 = (yield (void))
      (list e2 e1 e0))
    events = '(a b c)
    react = (gn yield (events)
      (letn loop (cons enext erest) = events
        command = (yield enext)
        (loop erest)))
    (check-equal?
      (gen-susp-v (left-x
        (model-control-loop ctrl (thunk (react events)))))
      '(c b a)
      )))

(define (dispatch-events ctrl events)
  (model-control-loop ctrl
    (gn yield () (forl event <- events
                       (yield event)))))

(module+ test
  (def (tick-ctrl (event-tick dt)) (gen-susp (note-view dt) tick-ctrl))
  (check-equal?
    (dispatch-events
      tick-ctrl ((sources->source
                   (list tick-event-source tick-event-source)) 12))
    (right (gen-susp (list (note-view 12) (note-view 12)) tick-ctrl))
    ))

(define (decorate-controller dec ctrl)
  (define dctrl (dec ctrl))
  (fn (event)
    (gen-susp result ctrl) = (dctrl event)
    (gen-susp result (decorate-controller dec ctrl))))

(def (display-doc doc)
  (size width height) = (screen-size)
  ctx = (sizing-context-new-default)
  block = (doc->styled-block ctx style-empty width doc)
  doc-str = (styled-block->string block)
  _ = (screen-clear)
  (displayln doc-str))

(define (display-doc-thread latency doc)
  (define chan (make-channel))
  (define fetch-chan (make-channel))
  (def (fetch-loop doc)
    evt = (sync chan (channel-put-evt fetch-chan doc))
    (if (channel-put-evt? evt)
      (fetch-loop (channel-get chan))
      (fetch-loop evt)))
  (define (display-loop timer)
    (display-doc (channel-get fetch-chan))
    (sleep-remaining latency timer)
    (display-loop (gen-susp-k (timer))))
  (define ts (list (thread (thunk (fetch-loop doc)))
                   (thread (thunk (display-loop (timer-now))))))
  (list chan (thunk (map kill-thread ts))))

(def (markout-view-model latency doc submodel)
  (list chan-display kill-threads) = (display-doc-thread latency doc)
  (gn yield (note)
    result = (letn loop (list submodel note) = (list submodel note)
      (match note
        ((note-view next-doc)
         (channel-put chan-display next-doc)
         (loop (list submodel (yield (nothing)))))
        (_ (match (submodel note)
             ((gen-susp v k) (loop (list k (yield v))))
             (r r)))))
    _ = (kill-threads)
    result))

(def (dispatch-notes yield model notes)
  (match (dispatch-events model notes)
    ((right (gen-susp mevents model))
     (lets
       events = (maybe-filter mevents)
       (if (empty? events) (right model)
         (forf
           emodel = (right model)
           event <- events
           #:break (left? emodel)
           (right model) = emodel
           notes = (yield event)
           (dispatch-notes yield model notes)))))
    ((left (gen-susp r _)) (left r))))

(def (event-source-model source submodel)
  (gn yield (notes)
    (letn loop (list submodel notes) = (list submodel notes)
      (match (dispatch-notes yield submodel notes)
        ((left result) result)
        ((right submodel)
         (loop (list submodel (yield (source)))))))))

(def (terminal-event-model latency submodel)
  (list chan-events kill-threads) = (start-terminal-event-threads latency)
  model = (event-source-model (thunk (channel-get chan-events)) submodel)
  (gn yield (notes)
    result = (gen-delegate yield model notes)
    _ = (kill-threads)
    result))

(def (markout-model latency doc)
  view = (markout-view-model latency doc (const-gen (nothing)))
  terminal = (terminal-event-model latency view)
  (thunk (terminal '())))

(define (markout-model-control-loop doc ctrl)
  (with-cursor-hidden
    (with-stty-direct
      (with-screen-fresh
        (model-control-loop ctrl (markout-model latency-default doc))))))

(module+ main
  (record event-keycount char count)
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
                  (lets
                    digits = (list* char digits)
                    (list digits (left (digits->count digits))))
                  (list '() (right (event-keycount char (digits->count digits))))))
               (_ (list digits (right event))))
             (gen-susp mevent (new digits))))
       (new '()))))
  (define ((keycount->events keymap) event)
    (match event
      ((event-keycount char count)
       (match (dict-get keymap char)
         ((just action) (action count))
         ((nothing) (list event))))
      (_ (list event))))

  (define (doc-str str) (doc-atom style-empty str))
  (define (doc-append . docs) (vertical-list style-empty docs))
  (define ((ctrl doc) event)
    (def (note-doc-append doc-tail)
      new-doc = (doc-append doc doc-tail)
      (gen-susp (list (note-view new-doc)) (ctrl new-doc)))
    (match event
      ((event-terminate) (gen-result 'quitting))
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
    ctrl = (gen-compose*
             (fn->gen (curry either-from '()))
             (either-gen
                (gen-compose*
                  (ctrl doc)
                  (fn->gen (lambda (events) (first events)))
                  (fn->gen (keycount->events keymap))))
             keycount-controller)
    (markout-model-control-loop doc ctrl)
    ))
