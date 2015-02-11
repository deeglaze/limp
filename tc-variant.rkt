#lang racket/unit
(require racket/match racket/trace
         foracc
         (only-in racket/list remove-duplicates)
         "tc-common.rkt" "types.rkt" "tast.rkt"
         "tc-sigs.rkt"
         "types-ad-hoc.rkt")
(import tc-expr^)
(export tc-variant^)

(define (tc-variant Γ Ξ e expected path tagged)
  (match-define (EVariant sy _ name tag τs es) e)
  ;; Find all the n-named variants and find which makes sense.
  (define arity (length es))
  (define generic (generic-variant name arity))
  ;; We can restrict the type because we know evariant will produce a variant.
  (define reshape (*reshape expected down-expr-construction up-expr-construction))
  (trace reshape)
  (define-values (Δ tag* W TW eτ)
    (reshape generic Γ (or tag tagged path)))
  (define (bad Γ bad-ct)
    (define-values (Θ es*)
      (for/acc ([Γ Δ] [#:type list])
               ([e (in-list es)]
                [i (in-naturals)])
        (tc-expr Γ Ξ e T⊤ `((,name . ,i) . ,path) #f)))
    (values Δ
            (λ (ct) (EVariant sy ct name tag* τs es*))
            #f bad-ct))
  (cond
   [(T⊥? eτ)
    ;;           (displayln "Bad")
    (bad Γ (type-error "Expected a variant of arity ~a (~a), got ~a" arity expected generic))]
   [else
    (define vars (lang-variants-of-arity Δ eτ))
    (define-values (Θ rev-possible)
      (for*/acc ([Γ Δ] [lst '()])
                ([τ (in-list vars)])
        (define-values (Δ _ inst) (apply-annotation Γ τs τ))
        (if inst
            (values Δ (cons inst lst))
            (values Γ lst))))
    (define possible-σs (reverse rev-possible))
    (printf "Bound ~a, Generic ~a, Expect ~a, Vars ~a, possible ~a~%"
            eτ generic expected vars possible-σs)

    (define errors (box '()))
    (define (no-match err)
      ;; Check subexpressions, but on the whole this doesn't work.
      (bad Γ (Check
            (TError
             (cons (format "~a Expected ~a (context: ~a)"
                           err
                           expected Γ)
                   (remove-duplicates (unbox errors)))))))
    (cond
     [(null? vars) (no-match "No variant type matched.")]
     [(null? possible-σs) (no-match "No variant type instantiable.")]
     [else
      ;; If we expect a type, we have a cast or explicit check, then use those rather than
      ;; an inferred variant type.racket tests.rkt
      (define (do Γ orig σs tr)
        ;; expressions typecheck with a possible variant type?
        (define-values (Δ es*)
          (for/acc ([Γ Γ] [#:type list])
                   ([σ (in-list σs)]
                    [e (in-list es)]
                    [i (in-naturals)])
            (define-values (Δ e*)
              (tc-expr Γ Ξ e σ `((,name . ,i) . ,path) (explicit-tag tag* i)))
            (values Δ e*)))
        (define mk-e0
          (λ (ct)
             (EVariant sy
                       (if (eq? tr 'bounded)
                           (type-error "Constructed a variant marked as bounded: ~a (orig ~a)"
                                       name orig)
                           ct)
                       name (give-tag tag* path) τs es*)))
        (values Δ
                (W mk-e0)
                (TW (mk-TVariant #f name (map πcc es*) tr))))
      (define-values (Θ mk-e op-τ)
        (for*/fold ([Δ Δ]
                    [mk-e #f]
                    [op-τ #f])
            ([σ (in-list possible-σs)] #:break mk-e)
          (let/ec break
            ;; if σ is quantified, instantiate to make it expected type
            (match σ
              [(TVariant: _ _ σs tr) ;; We know |σs| = |es| by possible-σs def.
               (parameterize ([type-error-fn (λ (fmt . args)
                                                (set-box! errors
                                                          (cons (apply format fmt args)
                                                                (unbox errors)))
                                                (break Δ #f #f))])
                 (do Δ σ σs tr))]
              [_ (values Δ #f #f)]))))
      (if mk-e
          (values Θ mk-e op-τ #f)
          (no-match "All variant choices led to type error."))])]))

(define (ts-variant Γ Ξ e path tagged)
  (match-define (EVariant sy _ name tag τs es) e)
  (define-values (Δ es*)
    (for/acc ([Γ Γ] [#:type list])
             ([e (in-list es)]
              [i (in-naturals)])
      (ts-expr Γ Ξ e `((,name . ,i) . ,path) (explicit-tag tag i))))
  (values Δ
          (λ (ct) (EVariant sy ct name (or tagged tag path) τs es*))
          (mk-TVariant sy name (map πcc es*) 'dc)
          #f))

