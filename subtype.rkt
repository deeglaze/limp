#lang racket/base
(provide <:? trace-<:? untrace-<:?)
(require racket/match
         racket/trace
         racket/set
         (only-in racket/bool implies)
         "tc-ctxs.rkt" "type-wf.rkt"
         "common.rkt" "language.rkt" "types.rkt")

;; The TAPL approach to equirecursive subtyping.
;; Uses language axioms for external subtyping.
(define (<:? Γ τ σ)
  (define L (current-language))
  ((<:?-aux (Language-E<: L)) ∅ Γ τ σ))

(define trace-aux #f)
(define (trace-<:?) (set! trace-aux #t) (trace <:?))
(define (untrace-<:?) (set! trace-aux #f) (untrace <:?))

;; A subtyping result is one of
;; - #f
;; - (<:-res Setof[Pair[Type,Type]] Ctx)
(struct <:-res (A Γ) #:transparent)

(define ((<:?-aux E<:) A Γ τ σ)
  (define (<:?-aux A Γ τ σ)
    (define (grow-A) (set-add A (cons τ σ)))
    (define-syntax seq
      (syntax-rules ()
        [(_ A Γ last) last]
        [(_ A Γ more0 . more)
         (match more0
           [#f #f]
           [(<:-res A* Γ*)
            (seq A* Γ* . more)])]))
    (cond
     [(or (equal? τ σ)
          (set-member? A (cons τ σ))
          (TError? τ)
          (TError? σ))
      (<:-res A Γ)]
     [else
      (match* (τ σ)
        [(_ (? T⊤?)) (<:-res A Γ)]
        [((? T⊥?) _) (<:-res A Γ)]
        [((? needs-resolve?) _)
         (<:?-aux (grow-A) Γ (resolve τ) σ)]
        [(_ (? needs-resolve?))
         (<:?-aux (grow-A) Γ τ (resolve σ))]
        ;; Polymorphism with type inference.
        ;; Dunfield, Krishnaswami <:∀L rule
        [((TΛ: _ α sτ oa) _)
         (define α̂ (gensym α))
         (match (<:?-aux A (ctx-extend-uvar Γ α̂)
                         (open-scope sτ (mk-TFree #f α̂)) σ)
           [#f #f]
           [(<:-res A* Δ) (<:-res A* (ctx-drop-after Γ α̂))])]
        ;; <:∀R rule
        [(_ (TΛ: _ α sσ oa))
         (define α* (gensym α))
         (match (<:?-aux A (ctx-extend-tvar Γ α*)
                         τ (open-scope sσ (mk-TFree #f α*)))
           [#f #f]
           [(<:-res A* Δ) (ctx-drop-after Δ α*)])]
        ;; <:InstantiateL
        [((and tf (TFree: _ α̂)) _)
         (and (ctx-unsolved? Γ α̂)
              (not (set-member? (free σ) α̂))
              (let ([Γ* (left-instantiate Γ tf σ)])
                (and Γ* (<:-res A Γ*))))]
        [(_ (and tf (TFree: _ α̂)))
         (and (ctx-unsolved? Γ α̂)
              (not (set-member? (free τ) α̂))
              (let ([Γ* (right-instantiate Γ τ tf)])
                (and Γ* (<:-res A Γ*))))]
        ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
        ;; Structural rules
        [((THeap: _ taddr0 tag0 τ) (THeap: _ taddr1 tag1 σ))
         (and (not (unmapped? (⋈flat tag0 tag1)))
              (seq A Γ
                   (<:?-aux A Γ taddr0 taddr1)
                   (<:?-aux A Γ τ σ)))]
        ;; No implicit casts from heap/non-heap
        [((TUnion: _ ts) _)
         (let solve-all ([A A] [Γ Γ] [ts ts])
           (match ts
             ['() (<:-res A Γ)]
             [(cons t ts)
              (match (<:?-aux A Γ t σ)
                [#f #f]
                [(<:-res A* Γ*) (solve-all A* Γ* ts)])]))]
        ;; XXX: this is probably not complete for type inference.
        [(_ (TUnion: _ σs))
         (for/or ([σ (in-list σs)])
           (<:?-aux A Γ τ σ))]
        [((TAddr: _ space0 mm0 em0) (TAddr: _ space1 mm1 em1))
         (and (not (or (unmapped? (⋈flat space0 space1))
                       (unmapped? (⋈flat mm0 mm1))
                       (unmapped? (⋈flat em0 em1))))
              (<:-res A Γ))]
        [((TVariant: _ n τs tr0) (TVariant: _ n σs tr1))
         #:when (implies (and tr0 tr1) (equal? tr0 tr1))
         (let each ([A (grow-A)] [Γ Γ] [τs τs] [σs σs])
           (match* (τs σs)
             [('() '()) (<:-res A Γ)]
             [((cons τ τs) (cons σ σs))
              (seq A Γ (<:?-aux A Γ τ σ) (each A Γ τs σs))]
             [(_ _) #f]))]
        [((TSet: _ τ lext) (TSet: _ σ rext))
         (and
          (or (equal? lext rext)
              (eq? lext 'dc)
              (eq? rext 'dc))
          (<:?-aux A Γ τ σ))]
        [((TMap: _ τk τv lext) (TMap: _ σk σv rext))
         (and (or (equal? lext rext)
                  (eq? lext 'dc)
                  (eq? rext 'dc))
          (seq A Γ
               (<:?-aux A Γ τk σk)
               (<:?-aux A Γ τv σv)))]
        [(_ (TExternal: _ name)) (and (set-member? E<: (cons τ name)) (<:-res A Γ))]
        [((TWeak: _ τ) (TWeak: _ σ)) (<:?-aux A Γ τ σ)]
        [(_ (TWeak: _ σ)) (<:?-aux A Γ τ σ)] ;; non-weak types can be upcast to weak types
        [((? permissive?) _) (<:-res A Γ)]
        [((THeap: _ taddr0 tag0 τ) _) #:when (not (check-for-heapification?))
         (<:?-aux A Γ τ σ)]
        [(_ (THeap: _ taddr1 tag1 σ)) #:when (not (check-for-heapification?))
         (<:?-aux A Γ τ σ)]
        [(_ _) #f])]))
  (match (<:?-aux A Γ τ σ)
    [#f #f]
    [(<:-res _ Δ) Δ]))

(define (left-instantiate Γ α̂τ σ)
  (match-define (TFree: sy α̂) α̂τ)
  (let rec ([Γ Γ] [σ σ])
    (match σ
      ;; InstLReach
      [(TFree: _ β̂) #:when (ctx-var-in-dom? Γ α̂ #:before β̂)
       ;; If α̂ before β̂ then set β̂ = α̂
       (ctx-set-evar Γ β̂ α̂τ)]
      [σ #:when (mono-type? σ)
         ;; InstLSolve
         (and (type-wf-before? Γ σ α̂)
              (ctx-set-evar Γ α̂ σ))]
      ;; InstLAIIR
      [(TΛ: sy β s on-app)
       (define β* (gensym β))
       (match (rec (ctx-extend-tvar Γ β*) (open-scope s (mk-TFree #f β*)))
         [#f #f]
         [Δ (ctx-drop-after Δ β*)])]
      ;; InstLArr
      [(TArrow: sy A₁ A₂)
       (define α̂₂ (gensym 'rng))
       (define α̂₁ (gensym 'dom))
       (define αv₁ (mk-TFree #f α̂₁))
       (define αv₂ (mk-TFree #f α̂₂))
       ;; Γ* := Γ[α̂₂,α̂₁,α̂ = α̂₁ → α̂₂]
       (define Γ* (ctx-set-evar
                   (ctx-extend-tvar
                    (ctx-extend-tvar Γ α̂₂)
                    α̂₁)
                   α̂ (mk-TArrow sy αv₁ αv₂)))
       (match (right-instantiate Γ* A₁ αv₁)
         [Θ (left-instantiate Θ αv₂ (apply-ctx Θ A₂))]
         [#f #f])]
      [_ #f])))

(define (right-instantiate Γ τ α̂σ)
  (match-define (TFree: sy α̂) α̂σ)
  (let rec ([Γ Γ] [τ τ])
    (match τ
      ;; InstRReach
      [(TFree: _ β̂) #:when (ctx-var-in-dom? Γ α̂ #:before β̂)
       ;; If α̂ before β̂ then set β̂ = α̂
       (ctx-set-evar Γ β̂ α̂σ)]
      [τ #:when (mono-type? τ)
         ;; InstRSolve
         (and (type-wf-before? Γ τ α̂)
              (ctx-set-evar Γ α̂ τ))]
      ;; InstRAIIL
      [(TΛ: sy β s on-app)
       (define β̂ (gensym β))       
       (match (rec (ctx-extend-uvar Γ β̂)
                   (open-scope s (mk-TFree #f β̂)))
         [#f #f]
         [Δ (ctx-drop-after Δ β̂)])]
      ;; InstRArr
      [(TArrow: sy A₁ A₂)
       (define α̂₂ (gensym 'rng))
       (define α̂₁ (gensym 'dom))
       (define αv₁ (mk-TFree #f α̂₁))
       (define αv₂ (mk-TFree #f α̂₂))
       ;; Γ* := Γ[α̂₂,α̂₁,α̂ = α̂₁ → α̂₂]
       (define Γ* (ctx-set-evar
                   (ctx-extend-tvar
                    (ctx-extend-tvar Γ α̂₂)
                    α̂₁)
                   α̂ (mk-TArrow sy αv₁ αv₂)))
       (match (left-instantiate Γ* αv₁ A₁)
         [Θ (right-instantiate Θ (apply-ctx Θ A₂) αv₂)]
         [#f #f])]
      [_ #f])))


