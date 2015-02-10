#lang racket/unit
(require racket/match racket/trace
         (only-in racket/list remove-duplicates)
         "tc-common.rkt" "types.rkt" "tast.rkt"
         "tc-sigs.rkt"
         "types-ad-hoc.rkt")
(import tc-expr^)
(export tc-variant^)

(define (tc-variant Δ Γ Ξ e expected path tagged)
  (match-define (EVariant sy _ name tag τs es) e)
  ;; Find all the n-named variants and find which makes sense.
  (define arity (length es))
  (define generic (generic-variant name arity))
  ;; We can restrict the type because we know evariant will produce a variant.
  (define reshape (*reshape expected down-expr-construction up-expr-construction))
  (trace reshape)
  (define-values (tag* W TW eτ)
    (reshape generic Δ Γ (or tag tagged path)))
  (define (bad bad-ct)
    (values (λ (ct)
               (EVariant sy ct name tag* τs
                         (for/list ([e (in-list es)]
                                    [i (in-naturals)])
                           (tc-expr Δ Γ Ξ e T⊤ `((,name . ,i) . ,path) #f))))
            #f bad-ct))
  (cond
   [(T⊥? eτ)
                                        ;           (displayln "Bad")
    (bad (type-error "Expected a variant of arity ~a (~a), got ~a" arity expected generic))]
   [else
    (define vars (lang-variants-of-arity eτ))
    (define possible-σs
      (for*/list ([τ (in-list vars)]
                  [σ (in-value (let-values ([(_ inst) (apply-annotation τs τ)])
                                 inst))]
                  #:when σ)
        σ))
    (printf "Bound ~a, Generic ~a, Expect ~a, Vars ~a, possible ~a~%"
            eτ generic expected vars possible-σs)

    (define errors (box '()))
    (define (no-match err)
      ;; Check subexpressions, but on the whole this doesn't work.
      (bad (Check
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
      (define (do orig σs tr)
        ;; expressions typecheck with a possible variant type?
        (define es*
          (for/list ([σ (in-list σs)]
                     [e (in-list es)]
                     [i (in-naturals)])
            (tc-expr Δ Γ Ξ e σ `((,name . ,i) . ,path) (explicit-tag tag* i))))
        (define mk-e0
          (λ (ct)
             (EVariant sy
                       (if (eq? tr 'bounded)
                           (type-error "Constructed a variant marked as bounded: ~a (orig ~a)" name orig)
                           ct)
                       name (give-tag tag* path) τs es*)))
        (values (W mk-e0) (TW (mk-TVariant #f name (map πcc es*) tr))))
      (define-values (mk-e op-τ)
        (for*/fold ([mk-e #f]
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
                                                (break #f #f))])
                 (do σ σs tr))]
              [_ (values #f #f)]))))
      (if mk-e
          (values mk-e op-τ #f)
          (no-match "All variant choices led to type error."))])]))
