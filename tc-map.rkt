#lang racket/unit
(require racket/match
         "tc-common.rkt" "tc-sigs.rkt"
         "type-lattice.rkt" "tast.rkt" "types.rkt")
(import tc-expr^)
(export tc-map^)
(define (tc-map Δ Γ Ξ e expected path tagged)
  (match e
    [(EExtend sy _ m tag k v)
     ;; we can restrict the type since we know eextend will produce a map
     (define-values (tag* W TW τ)
       ((*reshape expected down-expr-construction up-expr-construction)
        generic-map Δ Γ (or tag tagged path)))
     (define-values (err d r ext)
       (match τ
         [(TMap: _ d r ext) (values #f d r ext)]
         [(TUnion: _ (list (? TMap?) ...))
          (values (type-error "Ambiguous map type ~a" τ)
                  T⊤ T⊤ 'dc)]
         [_ (values (type-error "Expected a map type, got ~a" τ)
                    T⊤ T⊤ 'dc)]))
     (define m* (tc-expr Δ Γ Ξ m τ (cons 'extend-map path) #f))
     (define k* (tc-expr Δ Γ Ξ k d (cons 'extend-key path) (explicit-tag tag* 0)))
     (define v* (tc-expr Δ Γ Ξ v r (cons 'extend-value path) (explicit-tag tag* 1)))
     (define mk-e0 (λ (ct) (EExtend sy ct m* (give-tag tag* path) k* v*)))
     (values (W mk-e0)
             (and (not err)
                  (TW (type-join (πcc m*) (mk-TMap #f (πcc k*) (πcc v*) ext))))
             err)]
    [(EEmpty-Map sy _)
     (define mk-e0 (λ (ct) (EEmpty-Map sy ct)))
     (values mk-e0 generic-map #f)]
    [(EMap-lookup sy _ m k)
     (define m* (tc-expr Δ Γ Ξ m generic-map (cons 'lookup-map path) #f))
     (match (resolve (type-meet (πcc m*) generic-map))
       [(TMap: _ d r _) ;; XXX: shouldn't be heapified?
        (values (λ (ct) (EMap-lookup sy ct m* (tc-expr Δ Γ Ξ k d (cons 'lookup-key path) #f)))
                r
                #f)]
       [τ (values (λ (ct) (EMap-lookup sy ct m* (tc-expr Δ Γ Ξ k T⊤ (cons 'lookup-key path) #f)))
                  #f
                  (type-error "Expected a map type: ~a" τ))])]
    [(EMap-has-key sy _ m k) (error 'tc-expr "Todo: map-has-key?")]
    [(EMap-remove sy _ m k) (error 'tc-expr "Todo: map-remove")]))
