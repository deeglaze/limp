#lang racket/base
(require racket/unit
         "tc-bu.rkt"
         "tc-expr.rkt" "tc-pattern.rkt"
         "tc-rules.rkt"
         "tc-map.rkt"
         "tc-set.rkt"
         "tc-sigs.rkt"
         "tc-variant.rkt")
(provide tc-rules tc-expr)

(define-values/invoke-unit/infer (export tc-rules^ tc-expr^)
  (link
   tc-expr@ tc-pattern@ tc-variant@ tc-map@ tc-rules@ tc-bu@ tc-set@))
