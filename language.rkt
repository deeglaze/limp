#lang racket/base
(require "common.rkt")
(provide (all-defined-out))

(struct Language (options ;; Map[symbol,any]
                  external-spaces ;; Map[Name,ED]
                  E<: ;; Set[(U Pair[Name,τ] Pair[τ, Name])]
                  user-spaces ;; Mutable-Map[Name,Type]
                  meta-table ;; if #:check-metavariables is given, names include a space check.
                  uspace-info) ;; Mutable-Map[Name,Vector[Bool, Bool, ℕ]]
        #:transparent)

(struct Reduction-relation (rules τ) #:transparent)
(struct Metafunction (name τ rules) #:transparent)

;; External descriptor
(struct ED (⊔ ⊑ ≡ μ touch quality pretty parse))

(define (flat-ED q p)
  (ED #'flat-⊔ #'flat-⊑ #'flat-≡ #'flat-card #'flat-touch q #'flat-pretty p))

(define Ltest
  (Language #hasheq()
            #hasheq()
            ∅
            (make-hasheq)
            #hash()
            (make-hasheq)))

(define current-language (make-parameter Ltest))

(define limp-externalize-default #t)
(define limp-default-mm 'delay)
(define limp-default-em 'identity)
(define limp-default-addr-space 'limp)
(define limp-default-lookup-mode 'delay)
