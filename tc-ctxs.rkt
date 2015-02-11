#lang racket/base
(provide ctx-lookup ctx-extend-var ctx-extend-tvar ctx-extend-uvar
         ctx-drop-after ctx-var-in-dom?
         ctx-set-var ctx-set-evar
         unsafe-tvar-at
         ctx-unsolved? ctx-solved apply-ctx
         ctx-wf?
         empty-ctx)
(require racket/match "common.rkt" "types.rkt")

;; A Context Γ,Δ,Θ is one of (A is a type, and τ is a monotype)
;; - ·
;; - Γ,α
;; - Γ,x : A
;; - Γ,α̂
;; - Γ,α̂ = τ
;; - Γ,▸α̂

;; We represent these with a hash table, but enforce ordering by pairing with a ℕ.
;; We reclaim scope by chopping off entries above a given number.
(struct ctx-entry (n) #:transparent)
(struct tvar ctx-entry () #:transparent) ;; key: α
(struct xvar ctx-entry (A) #:transparent) ;; key: x
(struct uvar ctx-entry () #:transparent) ;; key α̂
(struct evar ctx-entry (τ) #:transparent) ;; key α̂
;; Markers are unnecessary since uvars and evars are keyed by the same name.
;;(struct marker ctx-entry () #:transparent) ;; key α̂

(define (ctx-lookup Γ x #:fail [on-fail void])
  (match (hash-ref Γ x #f)
    [(tvar _) (on-fail 'tvar)]
    [(xvar _ A) A]
    [(uvar _) x]
    [(evar _ τ) τ]
    [#f (on-fail 'unmapped)]))

(define empty-ctx hasheq)

(define (ctx-wf? Γ type-wf-before)
  (for/and ([(x entry) (in-hash Γ)])
    (match entry
      [(tvar n) #t] ;; ensured to not already be in domain
      [(xvar n A) (type-wf-before Γ n A)]
      [(uvar n) #t] ;; ensured to not already be in domain
      [(evar n τ) (type-wf-before Γ n τ)])))

(define (ctx-extend-var Γ x A)
  (when (hash-has-key? Γ x) (error 'ctx-extend-var "Cannot shadow variable in ctx: ~a" x))
  (hash-set Γ x (xvar (hash-count Γ) A)))

(define (ctx-extend-tvar Γ α)
  (when (hash-has-key? Γ α) (error 'ctx-extend-tvar "Cannot shadow type in ctx: ~a" α))
  (hash-set Γ α (tvar (hash-count Γ))))

(define (ctx-var-in-dom? Γ xαα̂ #:before [before +inf.0])
  (match (hash-ref Γ xαα̂ #f)
    [#f #f]
    [(ctx-entry n) (< n (limit 'ctx-var-in-dom? Γ before))]))

(define (limit who Γ before)
  (if (number? before)
      before
      (let ([bad
             (λ () (error who "Unbound limit ~a" before))])
        (ctx-entry-n (hash-ref Γ before bad)))))

(define (ctx-unsolved? Γ α̂) (uvar? (hash-ref Γ α̂ #f)))
(define (ctx-solved Γ α̂)
  (match (hash-ref Γ α̂ #f)
    [(evar _ τ) τ]
    [_ #f]))

(define (unsafe-tvar-at Γ x n) (hash-set Γ x (tvar n)))

(define (ctx-extend-uvar Γ α̂)
  (when (hash-has-key? Γ α̂) (error 'ctx-extend-uvar "Unsolved existential exists: ~a" α̂))
  (hash-set Γ α̂ (uvar (hash-count Γ))))

(define (ctx-set-var Γ x τ)
  (match (hash-ref Γ x (λ () (error 'ctx-set-evar "Variable not in scope: ~a" x)))
    [(xvar n A) (hash-set Γ x (xvar n τ))]
    [entry (error 'ctx-set-var "Expected a variable mapping for ~a, got ~a" x entry)]))

(define (ctx-set-evar Γ α̂ τ)
  (match (hash-ref Γ α̂ (λ () (error 'ctx-set-evar "Existential not in scope: ~a" α̂)))
    [(uvar n) (hash-set Γ α̂ (evar n τ))]
    [(evar _ τ) (error 'ctx-set-evar "Existential already solved: ~a [: ~a]" α̂ τ)]
    [entry (error 'ctx-set-evar "Expected an existential variable mapping for ~a, got ~a" α̂ entry)]))

;; Drop all entries after (and including) the number/entry `after`
(define (ctx-drop-after Γ after)
  (for/hash ([(x entry) (in-hash Γ)]
             #:when (< (ctx-entry-n entry)
                       (limit 'ctx-drop-after Γ after)))
    (values x entry)))

(define (apply-ctx Γ τ)
  (type-fold #:TFree (λ (self sy x) (or (ctx-solved Γ x) self)) τ))
