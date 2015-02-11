#lang racket/base
(provide castable cast-to)
(require racket/match racket/set
         (only-in racket/bool implies)
         "common.rkt"
         "subtype.rkt" "types.rkt")

(define (cast-to Γ from to)
  (cond
   [(<:? Γ from to) => (λ (Δ) (values Δ (Check to)))] ;; upcast -> check, not cast
   [(castable from to) => (λ (Δ) (values Δ (Cast to)))]
   [else (values Γ (type-error "Could not cast ~a to ~a" from to))]))

(struct cast-res (A Γ) #:transparent)

;; τ is castable to σ if τ <: σ, τ = ⊤,
;; or structural components of τ are castable to structural components of σ.
(define (castable Γ from to)
  (define (check A Γ from to)
    (define-syntax seq
      (syntax-rules ()
        [(_ A Γ last) last]
        [(_ A Γ e . more)
         (let-values ([(A Γ) e]) (seq A Γ . more))]))
    (cond
     [(or
       (<:? Γ from to) ;; upcast
       (<:? Γ to from)) => ;; strict downcast
      (λ (Δ) (cast-res A Δ))]
     [else
      ;; Structurally castable?
      (match* (from to)
        [((TΛ: _ _ (Scope f) oa) (TΛ: _ _ (Scope t) oa))
         (check A Γ f t)]
        [((TVariant: _ n tsf tr0) (TVariant: _ n tst tr1))
         #:when (implies (and tr0 tr1) (equal? tr0 tr1))
         (let all ([A A] [Γ Γ] [tsf tsf] [tst tst])
           (match* (tsf tst)
             [('() '()) (cast-res A Γ)]
             [((cons f tsf) (cons t tst))
              (seq A Γ
                   (check A Γ f t)
                   (all A Γ tsf tst))]
             [(_ _) #f]))]
        [((Tμ: _ _ (Scope f) tr n) (Tμ: _ _ (Scope t) tr n))
         (check A Γ f t)]
        [((TMap: _ df rf ext) (TMap: _ dt rt ext))
         (seq A Γ
              (check A Γ df dt)
              (check A Γ rf rt))]
        [((TSet: _ f ext) (TSet: _ t ext)) (check A Γ f t)]
        [((TUnion: _ tsf) _)
         (define-values (A* Δ)
           (let/ec break
             (for/fold ([A A] [Γ Γ])
                 ([tf (in-list tsf)])
               (match (check A Γ tf to)
                 [(cast-res A* Δ) (values A* Δ)]
                 [#f (break #f #f)]))))
         (and A* (cast-res A* Δ))]
        [(_ (TUnion: _ tst))
         ;; Don't save false paths
         (for/or ([tt (in-list tst)]) (check A Γ from tt))]
        ;; XXX: Will this possibly diverge?
        [((and (not (? Tμ?)) (? needs-resolve?)) _)
         (if (set-member? A (cons from to))
             (cast-res A Γ)
             (check (set-add A (cons from to))
                    Γ
                    (resolve from) to))]
        [(_ (and (not (? Tμ?)) (? needs-resolve?)))
         (if (set-member? A (cons from to))
             (cast-res A Γ)
             (check (set-add A (cons from to))
                    Γ
                    from (resolve to)))]
        [(_ _) #f])]))
  (match (check ∅ Γ from to)
    [#f #f]
    [(cast-res _ Δ) Δ]))
