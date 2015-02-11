#lang racket/base
(require racket/unit
         "ts-bus.rkt"
         "tc-expr.rkt" "tc-pattern.rkt"
         "tc-rules.rkt"
         "tc-map.rkt"
         "tc-set.rkt"
         "tc-call.rkt"
         "tc-lookup.rkt"
         "tc-sigs.rkt"
         "tc-variant.rkt")
(provide tc-rules tc-expr)

(define-values/invoke-unit/infer (export tc-rules^ tc-expr^)
  (link
   tc-expr@ tc-pattern@ tc-variant@ tc-call@ tc-lookup@ tc-map@ tc-rules@ ts-bus@ tc-set@))
