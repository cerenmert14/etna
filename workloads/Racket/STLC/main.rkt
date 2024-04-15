#lang racket/base

(require "src/impl.rkt")
(require "src/spec.rkt")
(require "Strategies/RackcheckBespoke.rkt")
(require rackcheck)
(require racket/cmdline)
(require rebellion/collection/association-list)

(define config (make-config #:tests 20000 #:deadline (+ (current-inexact-milliseconds) (* 240 1000))))

(define props
    (association-list  )
)

(module+ main
    (command-line
      #:program "rackcheck-bespoke"
      #:args info
      (check-property config (vector-ref (association-list-ref props (list-ref info 0)) 0)))
)