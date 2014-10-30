#lang racket/base
(require (for-syntax syntax/parse racket/syntax racket/base)
         racket/list racket/match racket/set
         racket/trace
         "common.rkt" "tast.rkt" "types.rkt")
(provide tc-expr
         tc-pattern
         tc-term)

;; TODO: syntax location tracking and reporting
(define (unbound-mf who f)
  (error tag "Unbound metafunction name ~a" f))
(define (unbound-pat-var who x)
  (error tag "Unbound pattern variable: ~a" x))

(define type-error-fn (make-parameter
                       (λ (fmt . args)
                          (error 'tc-expr (apply format args)))))
(define-syntax-rule (type-error f e ...)
  ((type-error-fn) f e ...))

(define (num-top-level-Λs τ)
  (let count ([τ τ] [i 0])
   (match τ
     [(TΛ _ (Scope σ)) (count σ (add1 i))]
     [_ i])))

(define (cast-to τ σ) (error 'cast-to "Todo"))

(define (coerce-check-expect L ct expect τ)
  (match ct
    [(Cast σ)
     (define σ* (cast-to τ σ))
     (unless (if expect (<:? L σ* expect) #t)
       (type-error "Expected ~a, got ~a" expect τ))
     (or expect σ*)]
    [(Check σ)
     (unless (<:? L τ σ)
       (type-error "Expect ~a to be a subtype of ~a" τ σ))
     (unless (if expect (<:? L τ expect) #t)
       (type-error "Expected ~a, got ~a" expect τ))
     (or expect σ)]))

;; Repeatedly instantiate σ's Λs with τs until τs is empty.
;; If τs not empty before σ is not a Λ, then invoke on-too-many.
(define (repeat-inst L σ τs
                     [on-too-many
                      (λ () (error 'repeat-inst
                                   "Instantiated type with too many variables: ~a (~a)" σ τs))])
  (let loop ([σ σ] [τs τs])
    (match τs
      [(cons τ τs)
       (match (resolve σ (Language-user-spaces L))
         [(TΛ: x s)
          (loop (open-scope s τ) τs)]
         [_ (on-too-many)])]
      [_ σ])))

(define (tc-bu L Γ Ξ bu)
  (define tc-expr* (tc-expr L Γ Ξ))
  (match bu
    [(Update k v)
     (define kτ (tc-expr* k))
     ;; We expect k to be a TAddr type, but which kind doesn't matter
     (unless (TAddr? kτ)
       (type-error "Expect store lookup key to have an address type, got ~a" kτ))
     ;; for effect
     (tc-expr* v)
     Γ]
    [(Where pat e)
     ;; We expect e and pat to have overlapping types,
     ;; but one's type doesn't drive the other's checking.
     (define eτ (tc-expr* e))
     (define-values (Γ* pτ) (tc-pattern L Γ Ξ pat))
     (define overlap? (type-overlap? eτ pτ))
     (unless overlap?
       (printf "Where clause has non-overlapping pattern and expression types: ~a" bu))
     Γ*]))

(define (tc-pattern L Γ Ξ pat expect-overlap)
  (match pat
    [(PAnd ct ps) ???]
    [(PName ct x) ???]
    [(PWild ct) ???]
    [(PVariant ct n ps) ???]
    [(PMap-with ct k v p) ???]
    [(PMap-with* ct k v p) ???]
    [(PSet-with ct v p) ???]
    [(PSet-with* ct v p) ???]
    [(PTerm ct t) ???]
    [(PIsExternal ct) ???]
    [(PIsAddr ct) ???]
    [(PIsType ct) ???]
    [_ (error 'tc-pattern "Unsupported pattern: ~a" pat)]))

(define (tc-bus L Γ Ξ bus)
  (let all ([Γ Γ] [bus bus])
    (match bus
      ['() Γ]
      [(cons bu bus)
       (define Γ* (tc-bu Γ Ξ bu))
       (all Γ* bus)])))

(define (check-and-join-rules L Γ Ξ rules expect-discr expected)
  (let check ([rules rules] [τ T⊥])
   (match rules
     ['() τ]
     [(cons (Rule _ lhs rhs bus) rules)
      (define-values (Γ* lhs-τ) (tc-pattern L Γ Ξ lhs expect-discr))
      (define Γ** (tc-bus L Γ* Ξ bus))
      (check rules (type-join τ ((tc-expr L Γ** Ξ) rhs expected)))])))

;; L : Language,
;; Γ : Variable names ↦ Type,
;; Ξ : metafunction names ↦ Type,
;; e : expr
;; Output is expression's type.
(define ((tc-expr L Γ Ξ) e [expected #f])
  (let tc-expr* ([e e] [expected expected])
    (define ct (Typed-ct e))
    (define (project-check pred form ty)
      (define σ
        (match ct
          [(Cast σ) σ]
          [(Check σ) σ]))
      (unless (pred σ)
        (type-error "Expect ~a to have ~a type, got ~a" form ty σ))
      σ)
    (define pre-τ
      (match e
        [(ECall _ mf τs es)
         (define mfτ (hash-ref Ξ mf (unbound-mf 'tc-expr mf)))
         ;; instantiate with all given types, error if too many
         (define inst (repeat-inst L mfτ τs))
         ;; also error if too few
         (when (TΛ? inst)
           (type-error
            "Metafunction type must be fully instantiated, but ~a left: ~a"
            (num-top-level-Λs inst) inst))
         ;; INVARIANT: the metafunction type is a function and the domain is monovariant
         (match-define (TArrow (TVariant: _ σs _ _) rng) inst)
         (for ([se (in-list es)]
               [σ (in-list σs)])
           (tc-expr* se σ))
         rng]

        [(EVariant _ n τs es)
         ;; Find all the n-named variants and find which makes sense.
         (define arity (length es))
         (define possible-σs (lang-variants-of-arity L n arity))
         (for/fold ([τ T⊥])
             ([σ (in-list possible-σs)])
           (define vσ (let/ec break (repeat-inst L σ τs (λ () (break #f)))))
           (match vσ
             [#f τ]
             [(TVariant: _ σs _ _) ;; We know |σs| = |es| by possible-σs def.
              ;; expressions typecheck with a possible variant type?
              (if (let/ec break
                    (parameterize ([type-error-fn (λ _ (break #f))])
                      (for ([σ (in-list σs)]
                            [e (in-list es)])
                        (tc-expr* e σ))))
                  ;; good, then it could be vσ too.
                  (type-join L τ vσ)
                  ;; well then it's not vσ.
                  τ)]))]

        [(ERef _ x) (hash-ref Γ x (unbound-pat-var 'tc-expr x))]
      
        [(EStore-lookup _ k _) ;; lookup mode does not factor into type.
         (define kτ (tc-expr* k))
         ;; We expect k to be a TAddr type, but which kind doesn't matter
         (unless (TAddr? kτ)
           (type-error "Expect store lookup key to have an address type, got ~a" kτ))
         T⊤]
      
        [(EAlloc _ tag)
         (project-check TAddr? "alloc" "address")]

        [(ELet _ bus body)
         ((tc-expr L (tc-bus L Γ Ξ bus) Ξ) body expected)]

        [(EMatch _ de rules)
         (define dτ (tc-expr* de))
         (check-and-join-rules Γ Ξ rules dτ expected)]

        [(EExtend _ m k v)
         (define mτ (tc-expr* m))
         (define kτ (tc-expr* k))
         (define vτ (tc-expr* v))
         (type-join L mτ (mk-TMap kτ vτ #f))]

        [(EEmpty-Map _) (project-check TMap? "empty-map" "map")]

        [(EEmpty-Set _) (project-check TSet? "empty-set" "set")]

        [(ESet-union _ es)
         (for/fold ([τ T⊥]) ([e (in-list es)])
           (type-join L τ (tc-expr* e expected)))]

        [(ESet-intersection _ e es)
         (error 'tc-expr "Todo: set-intersect")
         #;
         (for/fold ([τ (tc-expr e)])
             ([e (in-list es)])
           (type-meet L τ (tc-expr e)))]

        [(ESet-subtract _ e es) (error 'tc-expr "Todo: set-subtract")]
        [(ESet-member _ e v) (error 'tc-expr "Todo: set-member?")]
        [(EMap-lookup _ m k) (error 'tc-expr "Todo: map-lookup")]
        [(EMap-has-key _ m k) (error 'tc-expr "Todo: map-has-key?")]
        [(EMap-remove _ m k) (error 'tc-expr "Todo: map-remove")]
        [_ (error 'tc-expr "Unrecognized expression form: ~a" e)]))
    (coerce-check-expect L ct expect pre-τ)))
