#lang racket/base
(require (for-syntax syntax/parse racket/syntax racket/base)
         racket/list racket/match racket/set
         racket/trace
         "common.rkt" "language.rkt" "tast.rkt" "types.rkt")
(provide tc-expr
         tc-pattern
         tc-term)

;; TODO: syntax location tracking and reporting
(define ((unbound-mf who f))
  (error who "Unbound metafunction name ~a" f))
(define ((unbound-pat-var who x))
  (error who "Unbound pattern variable: ~a" x))

(define type-error-fn (make-parameter
                       (λ (fmt . args)
                          (error 'tc-expr (apply format fmt args)))))
(define-syntax-rule (type-error f e ...)
  ((type-error-fn) f e ...))

(define (num-top-level-Λs τ)
  (let count ([τ τ] [i 0])
   (match τ
     [(TΛ: _ _ (Scope σ)) (count σ (add1 i))]
     [_ i])))

(module+ test (require rackunit)
  ;; ∀pair = ΛXY. pair<X,Y>
  (define ∀pair
    (mk-TΛ #f 'x
     (abstract-free
      (mk-TΛ #f 'y
       (abstract-free
        (mk-TVariant #f 'pair (list (mk-TFree #f 'x #f) (mk-TFree #f 'y #f)) #f #f)
        'y))
      'x)))
  (check-equal? 2 (num-top-level-Λs ∀pair)))

(define (coerce-check-expect ct expect τ)
  (match ct
    [(Cast σ)
     (define σ* (cast-to τ σ))
     (unless (if expect (<:? σ* expect) #t)
       (type-error "Expected ~a, got ~a" expect τ))
     (or expect σ*)]
    [(Check σ)
     (unless (<:? τ σ)
       (type-error "Expect ~a to be a subtype of ~a" τ σ))
     (unless (if expect (<:? τ expect) #t)
       (type-error "Expected ~a, got ~a" expect τ))
     (or expect σ)]
    [_
     (unless (if expect (<:? τ expect) #t)
       (type-error "Expected ~a, got ~a" expect τ))
     (or expect τ)]))

(define (coerce-check-overlap ct expect-overlap τ)
  (define (chk σ*)
    (unless (if expect-overlap (type-overlap? σ* expect-overlap) #t)
      (type-error "Expected ~a to overlap with ~a" expect-overlap τ)))
  (match ct
    [(Cast σ)
     (define σ* (cast-to τ σ))
     (chk σ*)
     (or expect-overlap σ*)]
    [(Check σ)
     (unless (<:? τ σ)
       (type-error "Overlap check: Expect ~a to be a subtype of ~a" τ σ))
     (chk τ)
     σ]
    [_ (chk τ)
     τ]))

;; Repeatedly instantiate σ's Λs with τs until τs is empty.
;; If τs not empty before σ is not a Λ, then invoke on-too-many.
(define (repeat-inst σ τs
                     [on-too-many
                      (λ () (error 'repeat-inst
                                   "Instantiated type with too many variables: ~a (~a)" σ τs))])
  (let loop ([σ σ] [τs τs])
    (match τs
      [(cons τ τs)
       (match (resolve σ (Language-user-spaces (current-language)))
         [(TΛ: _ x s)
          (loop (open-scope s τ) τs)]
         [_ (on-too-many)])]
      [_ σ])))

(define (tc-bu Γ Ξ bu)
  (define tc-expr* (tc-expr Γ Ξ))
  (match bu
    [(Update _ k v)
     (define kτ (tc-expr* k))
     ;; We expect k to be a TAddr type, but which kind doesn't matter
     (unless (TAddr? kτ)
       (type-error "Expect store lookup key to have an address type, got ~a" kτ))
     ;; for effect
     (tc-expr* v)
     Γ]
    [(Where _ pat e)
     ;; We expect e and pat to have overlapping types,
     ;; but one's type doesn't drive the other's checking.
     (define eτ (tc-expr* e))
     (define-values (Γ* pτ) (tc-pattern Γ Ξ pat))
     (define overlap? (type-overlap? eτ pτ))
     (unless overlap?
       (type-error "Where clause has non-overlapping pattern and expression types: ~a" bu))
     Γ*]))

(define (type-overlap? τ τ-or-τs)
  (unless (Type? τ) (error 'type-overlap? "What? ~a" τ))
  (match τ-or-τs
    ['() #f]
    [(cons σ σs) (and (type-overlap? τ σ) (type-overlap? τ σs))]
    [σ (not (T⊥? (type-meet τ σ)))]))
(trace type-overlap?)

(module+ test
  (check-true (type-overlap?
               ;; ab = (U a<> b<>)
               ;; foo<ab> ⋈ (U foo<b> bar<⊤>)
               (mk-TVariant #f 'foo
                            (list (*TRUnion #f (list (mk-TVariant #f 'a '() #f #f)
                                                     (mk-TVariant #f 'b '() #f #f))))
                            #f #f)
               (*TRUnion #f (list (mk-TVariant #f 'foo (list (mk-TVariant #f 'b '() #f #f)) #f #f)
                                  (mk-TVariant #f 'bar (list T⊤) #f #f))))))

(define (tc-term Γ Ξ t expect-overlap)
  (error 'tc-term "todo"))

;; expect-overlap is a type or a list of types (no expectations should be T⊤)
(define (tc-pattern Γ Ξ pat expect-overlap)
  (define (tc Γ pat expect-overlap)
    (define ct (Typed-ct pat))
    (define-values (Γ* pre-τ)
      (match pat
        [(PAnd _ _ ps)
         (let tcp* ([Γ Γ] [ps ps] [expect expect-overlap])
           (match ps
             ['() (values Γ expect)]
             [(cons p ps)
              (define-values (Γ* τ) (tc Γ p expect))
              (tcp* Γ* ps (type-meet τ expect))]))]
        
        [(PName _ _ x)
         (match (hash-ref Γ x #f)
           [#f (define t (or expect-overlap T⊤))
               (values (hash-set Γ x t) t)]
           [τ (unless (type-overlap? τ expect-overlap)
                (type-error "Non-linear Name pattern has ~a: ~a (type: ~a, expected overlap ~a)"
                        "non-overlapping initial type and expected overlapping type"
                        pat τ expect-overlap))
              (values Γ τ)])]

        [(PVariant _ _ n ps)
         (define len (length ps))
         ;; If we just have a single variant we expect, do a better job localizing errors.
         (define-values (expects bound? tr-c)
           (match (type-meet (resolve expect-overlap)
                             (mk-TVariant #f n (make-list len T⊤) 'dc 'dc))
             [(TVariant: _ n* τs bound? tr-c)
              (cond
               [(eq? n n*)
                (cond
                 [(= (length τs) len)
                  (values τs bound? tr-c)]
                 [else (type-error "Variant type arity mismatch. Expected ~a, got ~a"
                                   expect-overlap pat)])]
               [else (type-error "Variant type of a different name. Expected ~a, got ~a"
                                 expect-overlap pat)])]
             ;; XXX: is this the right behavior?
             [ft (values (make-list len T⊤) #f #f)]))

         (let all ([Γ Γ] [ps ps] [exs expects] [τs-rev '()])
           (match* (ps exs)
             [('() '())
              (values Γ (mk-TVariant #f n (reverse τs-rev) bound? tr-c))]
             [((cons p ps) (cons ex exs))
              (define-values (Γ* τ) (tc Γ p ex))
              (all Γ* ps exs (cons τ τs-rev))]))]
        
        [(or (PMap-with _ _ k v p) (PMap-with* _ _ k v p))
         ;; Another localizing check
         (define-values (ext exk exv)
           (match (type-meet expect-overlap (mk-TMap #f T⊤ T⊤ 'dc))
             [(TMap: _ d r ext) (values ext d r)]
             ;; XXX: if not a map, then what?
             [_ (values limp-externalize-default T⊤ T⊤)]))
         (define-values (Γ* kτ) (tc Γ k exk))
         (define-values (Γ** vτ) (tc Γ* v exv))
         (define-values (Γ*** mτ) (tc Γ** p expect-overlap))
         (values Γ*** (type-join (mk-TMap kτ vτ ext) mτ))]
        
        [(or (PSet-with _ _ v p) (PSet-with* _ _ v p))
         ;; Another localizing check
         (define-values (ext exv)
           (match (type-meet expect-overlap (mk-TSet #f T⊤ 'dc))
             [(TSet: _ v ext) (values ext v)]
             [_ (values limp-externalize-default T⊤)]))
         (define-values (Γ* vτ) (tc Γ v exv))
         (define-values (Γ** sτ) (tc Γ* p expect-overlap))
         (values Γ** (type-join (mk-TSet vτ ext) sτ))]

        [(PTerm _ _ t) (tc-term Γ Ξ t expect-overlap)]
        [(or (? PWild?) (? PIsExternal?) (? PIsAddr?) (? PIsType?))
         (values Γ T⊤)]
        [_ (error 'tc-pattern "Unsupported pattern: ~a" pat)]))

    (values Γ* (coerce-check-overlap ct expect-overlap pre-τ)))
  (trace tc)
  (tc Γ pat expect-overlap))


(define (tc-bus Γ Ξ bus)
  (let all ([Γ Γ] [bus bus])
    (match bus
      ['() Γ]
      [(cons bu bus)
       (define Γ* (tc-bu Γ Ξ bu))
       (all Γ* bus)])))

(define (check-and-join-rules Γ Ξ rules expect-discr expected)
  (let check ([rules rules] [τ T⊥])
   (match rules
     ['() τ]
     [(cons (Rule _ _ lhs rhs bus) rules)
      (define-values (Γ* lhs-τ) (tc-pattern Γ Ξ lhs expect-discr))
      (define Γ** (tc-bus Γ* Ξ bus))
      (check rules (type-join τ ((tc-expr Γ** Ξ) rhs expected)))])))

;; Γ : Variable names ↦ Type,
;; Ξ : metafunction names ↦ Type,
;; e : expr
;; Output is expression's type.
(define ((tc-expr Γ Ξ) e [expected #f])
  (define (tc-expr* e expected)
    (define ct (Typed-ct e))
    (define stx (with-stx-stx e))
    (define (project-check pred form ty)
      (define σ
        (match ct
          [(Cast σ) σ]
          [(Check σ) σ]
          [_ (error 'project-check "Expected a type annotation ~a" form)]))
      (unless (pred σ)
        (type-error "Expect ~a to have ~a type, got ~a" form ty σ))
      σ)
    (define pre-τ
      (match e
        [(ECall _ _ mf _ τs es)
         (define mfτ (hash-ref Ξ mf (unbound-mf 'tc-expr mf)))
         ;; instantiate with all given types, error if too many
         (define inst (repeat-inst mfτ τs))
         ;; also error if too few
         (when (TΛ? inst)
           (type-error
            "Metafunction type must be fully instantiated, but ~a left: ~a"
            (num-top-level-Λs inst) inst))
         ;; INVARIANT: the metafunction type is a function and the domain is monovariant
         (match-define (TArrow: _ (TVariant: _ _ σs _ _) rng) inst)
         (for ([se (in-list es)]
               [σ (in-list σs)])
           (tc-expr* se σ))
         rng]

        [(EVariant _ _ n _ τs es)
         ;; Find all the n-named variants and find which makes sense.
         (define arity (length es))
         (define possible-σs (lang-variants-of-arity
                              (mk-TVariant #f n (make-list arity T⊤) 'dc 'dc)))
         (for/fold ([τ T⊥])
             ([σ (in-list possible-σs)])
           (define vσ (let/ec break (repeat-inst σ τs (λ () (break #f)))))
           (match vσ
             [#f τ]
             [(TVariant: _ _ σs _ _) ;; We know |σs| = |es| by possible-σs def.
              ;; expressions typecheck with a possible variant type?
              (if (let/ec break
                    (parameterize ([type-error-fn (λ _ (break #f))])
                      (for ([σ (in-list σs)]
                            [e (in-list es)])
                        (tc-expr* e σ))))
                  ;; good, then it could be vσ too.
                  (type-join τ vσ)
                  ;; well then it's not vσ.
                  τ)]))]

        [(ERef _ _ x) (hash-ref Γ x (unbound-pat-var 'tc-expr x))]
      
        [(EStore-lookup _ _ k _) ;; lookup mode does not factor into type.
         (define kτ (tc-expr* k #f))
         ;; We expect k to be a TAddr type, but which kind doesn't matter
         (unless (TAddr? kτ)
           (type-error "Expect store lookup key to have an address type, got ~a" kτ))
         T⊤]
      
        [(? EAlloc?) (project-check TAddr? "alloc" "address")]

        [(ELet _ _ bus body)
         ((tc-expr (tc-bus Γ Ξ bus) Ξ) body expected)]

        [(EMatch _ _ de rules)
         (define dτ (tc-expr* de #f))
         (check-and-join-rules Γ Ξ rules dτ expected)]

        [(EExtend _ _ m _ k v)
         (define mτ (tc-expr* m #f))
         (define kτ (tc-expr* k #f))
         (define vτ (tc-expr* v #f))
         (type-join mτ (mk-TMap kτ vτ #f))]

        [(EEmpty-Map _ _) (project-check TMap? "empty-map" "map")]

        [(EEmpty-Set _ _) (project-check TSet? "empty-set" "set")]

        [(ESet-union _ _ es)
         (for/fold ([τ T⊥]) ([e (in-list es)])
           (type-join τ (tc-expr* e expected)))]

        [(ESet-intersection _ _ e es)
         (for/fold ([τ (tc-expr e)])
             ([e (in-list es)])
           (type-meet τ (tc-expr e)))]

        [(ESet-subtract _ _ e es) (error 'tc-expr "Todo: set-subtract")]
        [(ESet-member _ _ e v) (error 'tc-expr "Todo: set-member?")]
        [(EMap-lookup _ _ m k) (error 'tc-expr "Todo: map-lookup")]
        [(EMap-has-key _ _ m k) (error 'tc-expr "Todo: map-has-key?")]
        [(EMap-remove _ _ m k) (error 'tc-expr "Todo: map-remove")]
        [_ (error 'tc-expr "Unrecognized expression form: ~a" e)]))
    (coerce-check-expect ct expected pre-τ))
  (trace tc-expr*)
  (tc-expr* e expected))
(trace tc-bus tc-pattern tc-term tc-expr)
