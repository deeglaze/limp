#lang racket/base
(require "common.rkt")
(provide (all-defined-out))

(struct User-Space (τ bounded? trust-construction?) #:prefab)

(struct Language
        (options                       ;; Map[symbol,any]
         external-spaces               ;; Map[Name,ED]
         user-spaces                   ;; Mutable-Map[Name,Type]
         ordered-us ;; List[Pair[Name,Type]]
         E<: ;; Set[(U Pair[Name,τ] Pair[τ, Name])]
         meta-table ;; if #:check-metavariables is given, names include a space check.
         uspace-info) ;; Mutable-Map[Name,Vector[Bool, Bool, ℕ]]
        #:prefab)

(struct Reduction-relation (rules τ) #:prefab)
(struct Metafunction (name τ rules) #:prefab)

(define (mkΞ metafunctions)
  (for/hash ([m (in-list metafunctions)])
    (values (Metafunction-name m)
            (Metafunction-τ m))))

;; External descriptor
(struct ED (⊔ ⊑ ≡ μ touch quality pretty parse))

(define (flat-ED q p)
  (ED #'flat-⊔ #'flat-⊑ #'flat-≡ #'flat-card #'flat-touch q #'flat-pretty p))

(define limp-externalize-default #t)
(define limp-default-mm 'delay)
(define limp-default-em 'identity)
(define limp-default-addr-space 'limp)
(define limp-default-lookup-mode 'delay)
(define defaults
  (hasheq 'mm limp-default-mm
          'em limp-default-em
          'addr-space limp-default-addr-space
          'lm limp-default-lookup-mode
          'externalize limp-externalize-default
          'check-casts #t))

(define L₀
  (Language defaults ⊥ (make-hash) '() ∅ ⊥ (make-hash)))
(define current-language (make-parameter L₀))
(define check-for-heapification? (make-parameter #f))

(define (get-option op #:use [u (current-language)])
  (define ops (cond
               [(Language? u) (Language-options u)]
               [(hash? u) u]
               [else ⊥]))
  (define res (hash-ref ops op unmapped))
  (if (unmapped? res)
      (hash-ref defaults op (λ () (error 'get-option "Unknown option ~a" op)))
      res))
