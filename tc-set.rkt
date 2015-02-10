#lang racket/unit
(require racket/match "tc-common.rkt" "tc-sigs.rkt" 
         "type-lattice.rkt" "tast.rkt" "types.rkt")
(import tc-expr^)
(export tc-set^)

(define (tc-set Δ Γ Ξ e expected tagged path)
  (match e
    [(ESet-add sy _ e tag es)
     ;; we can restrict the type since we know eset-add will produce a set
     (define-values (tag* W TW τ)
       ((*reshape expected down-expr-construction up-expr-construction)
        generic-set Δ Γ (or tag tagged path)))
     (define-values (err v ext)
       (match τ
         [(TSet: _ v ext) (values #f v ext)]
         [(TUnion: _ (list (? TSet?) ...))
          (values (type-error "Ambiguous set type ~a" τ)
                  T⊤ 'dc)]
         [_ (values (type-error "Expected base expression to be a set, got ~a" τ) T⊤ 'dc)]))
     (define e* (tc-expr Δ Γ Ξ e τ `((set-add . 0) . ,path) #f))
     (define es*
       (for/list ([e (in-list es)]
                  [i (in-naturals 1)])
         (tc-expr Δ Γ Ξ e v `((set-add . ,i) . ,path) (explicit-tag tag i))))
     (define mk-e (λ (ct) (ESet-add sy ct e* (give-tag tag path) es*)))
     (values (W mk-e)
             (and (not err)
                  (TW (for/fold ([τ (πcc e*)]) ([e (in-list es*)])
                        (type-join τ (mk-TSet #f (πcc e) 'dc)))))
             err)]
    [(EEmpty-Set sy _)
     (define mk-e0 (λ (ct) (EEmpty-Set sy ct)))
     (values mk-e0 generic-set #f)]

    [(ESet-union sy _ es)
     (define es* (for/list ([e (in-list es)]
                            [i (in-naturals)])
                   (tc-expr Δ Γ Ξ e expected `((union . ,i) . ,path) #f)))
     (define mke0
       (λ (ct) (ESet-union sy ct es*)))
     (values mke0
             (for/fold ([τ T⊥]) ([e (in-list es*)])
               (type-join τ (πcc e)))
             #f)]

    [(ESet-intersection sy _ e es)
     (match-define (cons e* es*)
                   (for/list ([e (in-list (cons e es))]
                              [i (in-naturals)])
                     (tc-expr Δ Γ Ξ e generic-set `((intersection . ,i) . ,path) #f)))
     (define mk-e (λ (ct) (ESet-intersection sy ct e* es*)))
     (values mk-e
             (for/fold ([τ (πcc e*)])
                 ([e (in-list es*)])
               (type-meet τ (πcc e)))
             #f)]

    [(ESet-subtract sy _ e es) (error 'tc-expr "Todo: set-subtract")]
    [(ESet-member sy _ e v) (error 'tc-expr "Todo: set-member?")]))
