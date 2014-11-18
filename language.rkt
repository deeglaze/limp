#lang racket/base
(require "common.rkt")
(provide (all-defined-out))

;; A Trust-Tag is one of
;; - 'untrusted 
;; - 'bounded [only destructed]
;; - 'trusted [allowed to be constructed without heap-allocation]
(define (untrusted? x) (eq? x 'untrusted))

(struct User-Space (τ bounded? trust-construction?) #:prefab)

(struct Language (options ;; Map[symbol,any]
                  external-spaces ;; Map[Name,ED]
                  E<: ;; Set[(U Pair[Name,τ] Pair[τ, Name])]
                  user-spaces ;; Mutable-Map[Name,Type]
                  ordered-us ;; List[Pair[Name,Type]]
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

(define Ltest
  (Language #hasheq()
            #hasheq()
            ∅
            (make-hasheq)
            #hasheq()
            #hash()
            (make-hasheq)))

(define current-language (make-parameter Ltest))

(define limp-externalize-default #t)
(define limp-default-mm 'delay)
(define limp-default-em 'identity)
(define limp-default-addr-space 'limp)
(define limp-default-lookup-mode 'delay)
