#lang racket/base
(require (for-syntax syntax/parse racket/base racket/syntax syntax/for-body)
         racket/set)
(provide (all-defined-out))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Common utils
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define ∅eq (seteq))
(define ∅ (set))
(define ⊥ (hash))

(define-syntax (for/union stx)
  (syntax-parse stx
    [(_  guards body ...)
     (define/with-syntax [(pre-body ...) (post-body ...)] (split-for-body stx #'(body ...)))
     #'(for/fold ([acc ∅]) guards
         pre-body ...
         (set-union acc (let () post-body ...)))]))

(define (hash-hash-add! h k k2 v)
  (hash-set! h k (hash-set! (hash-ref! h k make-hash) k2 v)))
