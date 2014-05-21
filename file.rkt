#lang racket/base
(provide
  to-file*
  display-to-file*
  write-to-file*
  )

(require racket/file)

(define ((to-file* file-op)
         content
         path
         #:mode (mode-flag 'binary)
         #:exists (exists-flag 'replace))
  (define-values (directory filename is-root) (split-path path))
  (when (path? directory) (make-directory* directory))
  (file-op content path #:mode mode-flag #:exists exists-flag))
(define display-to-file* (to-file* display-to-file))
(define write-to-file* (to-file* write-to-file))
