#lang racket/base
(require racket/unit)
(provide tc-pattern^ tc-rules^ tc-expr^ tc-variant^ tc-map^ tc-set^ tc-bu^)

(define-signature tc-pattern^ (tc-pattern))
(define-signature tc-rules^ (tc-rules check-and-join-rules))
(define-signature tc-expr^ (tc-expr))

(define-signature tc-variant^ (tc-variant))
(define-signature tc-set^ (tc-set))
(define-signature tc-map^ (tc-map))
(define-signature tc-bu^ (tc-bu tc-bus))
