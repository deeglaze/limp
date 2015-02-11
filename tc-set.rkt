#lang racket/unit
(require racket/match
         foracc "tc-common.rkt" "tc-sigs.rkt" 
         "subtype.rkt"
         "type-lattice.rkt" "tast.rkt" "types.rkt")
(import tc-expr^)
(export tc-set^)

(define (tc-set Γ Ξ e expected tagged path)
  (match e
    [(ESet-add sy _ e tag es)
     ;; we can restrict the type since we know eset-add will produce a set
     (define-values (tag* W TW τ)
       ((*reshape expected down-expr-construction up-expr-construction)
        generic-set Γ (or tag tagged path)))
     (define-values (err v ext)
       (match τ
         [(TSet: _ v ext) (values #f v ext)]
         [(TUnion: _ (list (? TSet?) ...))
          (values (type-error "Ambiguous set type ~a" τ)
                  T⊤ 'dc)]
         [_ (values (type-error "Expected base expression to be a set, got ~a" τ) T⊤ 'dc)]))
     (define-values (Δ e*) (tc-expr Γ Ξ e τ `((set-add . 0) . ,path) #f))
     (define-values (Θ rev-es*)
       (for/acc ([Δ Δ] [#:type list])
           ([e (in-list es)]
            [i (in-naturals 1)])
           (tc-expr Δ Ξ e v `((set-add . ,i) . ,path) (explicit-tag tag i))))
     (define es* (reverse rev-es*))
     (define mk-e (λ (ct) (ESet-add sy ct e* (give-tag tag path) es*)))
     (define-values (Γ* j)
       (for/fold ([Γ Θ] [τ (πcc e*)])
           ([e (in-list es*)])
         (type-join Γ τ (mk-TSet #f (πcc e) 'dc))))
     (values Γ*
             (W mk-e)
             (and (not err) (TW j))
             err)]
    [(EEmpty-Set sy _)
     (define mk-e0 (λ (ct) (EEmpty-Set sy ct)))
     (values Γ mk-e0 generic-set #f)]

    [(ESet-union sy _ es)
     (define-values (Δ rev-es*)
       (for/acc ([Γ Γ] [#:type list])
           ([e (in-list es)]
            [i (in-naturals)])
           (tc-expr Γ Ξ e expected `((union . ,i) . ,path) #f)))
     (define es* (reverse rev-es*))
     (define mke0
       (λ (ct) (ESet-union sy ct es*)))
     (define-values (Θ j)
       (for/fold ([Δ Δ] [τ T⊥]) ([e (in-list es*)])
         (type-join Δ τ (πcc e))))
     (values Θ mke0 j #f)]

    [(ESet-intersection sy _ e es)
     (define-values (Δ rev-es*)
       (for/acc ([Γ Γ] [#:type list])
           ([e (in-list (cons e es))]
            [i (in-naturals)])
          (tc-expr Γ Ξ e generic-set `((intersection . ,i) . ,path) #f)))
     (match-define (cons e* es*) (reverse rev-es*))
     (define mk-e (λ (ct) (ESet-intersection sy ct e* es*)))
     (define-values (Θ m)
       (for/fold ([Δ Δ] [τ (πcc e*)])
           ([e (in-list es*)])
         (type-meet Δ τ (πcc e))))
     (values Θ mk-e m #f)]

    [(ESet-subtract sy _ e es) (error 'tc-expr "Todo: set-subtract")]
    [(ESet-member sy _ e v) (error 'tc-expr "Todo: set-member?")]))

(define (ts-set Γ Ξ e tagged path)
  (match e
    [(ESet-add sy _ e tag es)
     (define-values (Δ e*) (ts-set Γ Ξ e (or tag tagged) `((set-add . 0) . ,path) #f))
     (define-values (Θ es*)
       (for/acc ([Δ Δ] [#:type list])
           ([e (in-list es)]
            [i (in-naturals 1)])
           (ts-expr Δ Ξ e `((set-add . ,i) . ,path) (explicit-tag tag i))))
     (define mk-e (λ (ct) (ESet-add sy ct e* (give-tag tag path) es*)))
     (define base (πcc e*))
     (cond
      [(TSet? (resolve base))
       (define-values (Γ* j)
         (for/fold ([Γ Θ] [τ base])
             ([e (in-list es*)])
           (type-join Γ τ (mk-TSet #f (πcc e) 'dc))))
       (values Γ* mk-e j #f)]
      [else (values Θ mk-e #f (type-error "Set addition expected set type, got ~a" base))])]
    [(EEmpty-Set sy _)
     (define mk-e0 (λ (ct) (EEmpty-Set sy ct)))
     (values Γ mk-e0 generic-set #f)]

    [(ESet-union sy _ es)
     (define-values (Δ es*)
       (for/acc ([Γ Γ] [#:type list])
           ([e (in-list es)]
            [i (in-naturals)])
           (ts-expr Γ Ξ e `((union . ,i) . ,path) #f)))
     (define mke0
       (λ (ct) (ESet-union sy ct es*)))
     (define-values (Θ j)
       (for/fold ([Δ Δ] [τ T⊥]) ([e (in-list es*)])
         (type-join Δ τ (πcc e))))
     (cond
      [(<:? Θ j generic-set) =>
       (λ (Γ) (values Γ mke0 j #f))]
      [else (values Θ mke0 #f (type-error "Union expected set type, got ~a" j))])]

    [(ESet-intersection sy _ e es)
     (match-define-values (Δ (cons e* es*))
       (for/acc ([Γ Γ] [#:type list])
           ([e (in-list (cons e es))]
            [i (in-naturals)])
          (ts-expr Γ Ξ e `((intersection . ,i) . ,path) #f)))
     (define mk-e (λ (ct) (ESet-intersection sy ct e* es*)))
     (define-values (Θ m)
       (for/fold ([Δ Δ] [τ (πcc e*)])
           ([e (in-list es*)])
         (type-meet Δ τ (πcc e))))
     (cond
      [(<:? Θ m generic-set) =>
       (λ (Γ) (values Γ mk-e m #f))]
      [else (values Θ mk-e #f (type-error "Intersection expected set type, got ~a" m))])]

    [(ESet-subtract sy _ e es) (error 'ts-set "Todo: set-subtract")]
    [(ESet-member sy _ e v) (error 'ts-set "Todo: set-member?")]))
