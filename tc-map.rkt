#lang racket/unit
(require racket/match
         "tc-common.rkt" "tc-sigs.rkt"
         "type-lattice.rkt" "tast.rkt" "types.rkt")
(import tc-expr^)
(export tc-map^)
(define (tc-map Γ Ξ e expected path tagged)
  (match e
    [(EExtend sy _ m tag k v)
     ;; we can restrict the type since we know eextend will produce a map
     (define-values (Δ tag* W TW τ)
       ((*reshape expected down-expr-construction up-expr-construction)
        generic-map Γ (or tag tagged path)))
     (define-values (err d r ext)
       (match τ
         [(TMap: _ d r ext) (values #f d r ext)]
         [(TUnion: _ (list (? TMap?) ...))
          (values (type-error "Ambiguous map type ~a" τ)
                  T⊤ T⊤ 'dc)]
         [_ (values (type-error "Expected a map type, got ~a" τ)
                    T⊤ T⊤ 'dc)]))
     (define-values (Γ₁ m*) (tc-expr Δ Ξ m τ (cons 'extend-map path) #f))
     (define-values (Γ₂ k*) (tc-expr Γ₁ Ξ k d (cons 'extend-key path) (explicit-tag tag* 0)))
     (define-values (Γ₃ v*) (tc-expr Γ₂ Ξ v r (cons 'extend-value path) (explicit-tag tag* 1)))
     (define mk-e0 (λ (ct) (EExtend sy ct m* (give-tag tag* path) k* v*)))
     (define-values (Γ₄ j) (type-join Γ₃ (πcc m*) (mk-TMap #f (πcc k*) (πcc v*) ext)))
     (values Γ₄
             (W mk-e0)
             (and (not err) (TW j))
             err)]
    [(EEmpty-Map sy _)
     (define mk-e0 (λ (ct) (EEmpty-Map sy ct)))
     (values Γ mk-e0 generic-map #f)]
    [(EMap-lookup sy _ m k)
     (define-values (Δ m*) (tc-expr Γ Ξ m generic-map (cons 'lookup-map path) #f))
     (define-values (Θ mτ) (type-meet Δ (πcc m*) generic-map))
     (match (resolve mτ)
       [(TMap: _ d r _) ;; XXX: shouldn't be heapified?
        (define-values (Γ* k*) (tc-expr Θ Ξ k d (cons 'lookup-key path) #f))
        (values Γ*
                (λ (ct) (EMap-lookup sy ct m* k*))
                r
                #f)]
       [τ
        (define-values (Γ* k*) (tc-expr Θ Ξ k T⊤ (cons 'lookup-key path) #f))
        (values Γ*
                (λ (ct) (EMap-lookup sy ct m* k*))
                #f
                (type-error "Expected a map type: ~a" τ))])]
    [(EMap-has-key sy _ m k) (error 'tc-expr "Todo: map-has-key?")]
    [(EMap-remove sy _ m k) (error 'tc-expr "Todo: map-remove")]))

(define (ts-map Γ Ξ e path tagged)
  (match e
    [(EExtend sy _ m tag k v)
     (define tag* (or tagged tag))
     (define-values (Γ₁ m*) (ts-expr Γ Ξ m (cons 'extend-map path) #f))
     (define-values (Γ₂ k*) (ts-expr Γ₁ Ξ k (cons 'extend-key path) (explicit-tag tag* 0)))
     (define-values (Γ₃ v*) (ts-expr Γ₂ Ξ v (cons 'extend-value path) (explicit-tag tag* 1)))
     (define mk-e0 (λ (ct) (EExtend sy ct m* (give-tag tag* path) k* v*)))
     (define-values (Γ₄ j) (type-join Γ₃ (πcc m*) (mk-TMap #f (πcc k*) (πcc v*) 'dc)))
     (values Γ₄
             mk-e0
             j
             #f)]
    [(EEmpty-Map sy _)
     (define mk-e0 (λ (ct) (EEmpty-Map sy ct)))
     (values Γ mk-e0 generic-map #f)]
    [(EMap-lookup sy _ m k)
     (define-values (Δ m*) (ts-expr Γ Ξ m (cons 'lookup-map path) #f))
     (define-values (Θ mτ) (type-meet Δ (πcc m*) generic-map))
     (match (resolve mτ)
       [(TMap: _ d r _) ;; XXX: shouldn't be heapified?
        (define-values (Γ* k*) (tc-expr Θ Ξ k d (cons 'lookup-key path) #f))
        (values Γ*
                (λ (ct) (EMap-lookup sy ct m* k*))
                r
                #f)]
       [τ
        (define-values (Γ* k*) (ts-expr Θ Ξ k (cons 'lookup-key path) #f))
        (values Γ*
                (λ (ct) (EMap-lookup sy ct m* k*))
                #f
                (type-error "Expected a map type: ~a" τ))])]
    [(EMap-has-key sy _ m k) (error 'ts-map "Todo: map-has-key?")]
    [(EMap-remove sy _ m k) (error 'ts-map "Todo: map-remove")]))
