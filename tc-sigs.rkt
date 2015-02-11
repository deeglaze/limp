#lang racket/base
(require racket/unit)
(provide
 ;; kinds
 tc-pattern^ tc-rules^ ts-bus^ tc-expr^
 ;; forms
 tc-variant^ tc-call^ tc-lookup^
 ;; special forms
 tc-map^ tc-set^)

(define-signature tc-pattern^ (tc-pattern ts-pattern))
(define-signature tc-rules^ (tc-rules ts-rules
                             check-and-join-rules))
(define-signature tc-expr^ (tc-expr ts-expr))

(define-signature tc-variant^ (tc-variant ts-variant))
(define-signature tc-call^ (ts-call))
(define-signature tc-lookup^ (tc-lookup ts-lookup))
(define-signature tc-set^ (tc-set ts-set))
(define-signature tc-map^ (tc-map ts-map))
(define-signature ts-bus^ (ts-bus))
