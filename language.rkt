#lang racket/base
(provide (all-defined-out))

(struct Language (options ;; Map[symbol,any]
                  external-spaces ;; Map[Name,ED]
                  user-spaces ;; Map[Name,Type]
                  meta-table ;; if #:check-metavariables is given, names include a space check.
                  uspace-info) ;; Map[Name,Vector[Bool, Bool, ℕ]]
        #:transparent)

(struct Reduction-relation (rules τ) #:transparent)
(struct Metafunction (name τ rules) #:transparent)

;; External descriptor
(struct ED (⊔ ⊑ ≡ μ touch quality pretty parse))

(define (flat-ED q p)
  (ED #'flat-⊔ #'flat-⊑ #'flat-≡ #'flat-card #'flat-touch q #'flat-pretty p))
