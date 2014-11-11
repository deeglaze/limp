#lang racket/base
(require (for-syntax syntax/parse racket/syntax racket/base)
         racket/list racket/match racket/set
         racket/trace
         "common.rkt" "language.rkt" "tast.rkt" "types.rkt")
(provide tc-expr
         tc-pattern
         tc-term)

;; TODO: syntax location tracking and reporting
(define ((unbound-mf sy who f))
  (raise-syntax-error sy "~a: Unbound metafunction name ~a" who f))
(define ((unbound-pat-var sy who x))
  (raise-syntax-error sy "~a: Unbound pattern variable: ~a" who x))

(define type-error-fn (make-parameter
                       (λ (fmt . args)
                          (TError (list (apply format fmt args))))))
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
     (cond
      [(if expect (<:? σ* expect) #t)
       (Cast (or expect σ*))]
      [else (type-error "Expected ~a, got ~a" expect τ)])]
    [(Check σ)
     (cond
      [(<:? τ σ)
       (cond
        [(if expect (<:? τ expect) #t)
         (Check (or expect σ))]
        [else
         (type-error "Expected ~a, got ~a" expect τ)])]
      [else (type-error "Expect ~a to be a subtype of ~a" τ σ)])]
    [_
     (cond
      [(if expect (<:? τ expect) #t) (Check (or expect τ))]
      [else (type-error "Expected ~a, got ~a" expect τ)])]))

(define (coerce-check-overlap ct expect-overlap τ)
  (define (chk σ*)
    (if
     (if expect-overlap (type-overlap? σ* expect-overlap) #t)
     #f
     (type-error "Expected ~a to overlap with ~a" expect-overlap τ)))
  (match ct
    [(Cast σ)
     (define σ* (cast-to τ σ))
     (or (chk σ*)
         (Cast (or expect-overlap σ*)))]
    [(Check σ)
     (cond
      [(<:? τ σ)
       (or (chk τ) (Check σ))]
      [else
       (type-error "Overlap check: Expect ~a to be a subtype of ~a" τ σ)])]
    [_ (or (chk τ)
           (Check τ))]))

;; Repeatedly instantiate σ's Λs with τs until τs is empty.
;; If τs not empty before σ is not a Λ, then invoke on-too-many.
(define (repeat-inst σ τs
                     [on-too-many
                      (λ () (type-error "Instantiated type with too many variables: ~a (~a)" σ τs))])
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
    [(Update sy k v)
     (define k* (tc-expr* k))
     ;; We expect k to be a TAddr type, but which kind doesn't matter
     (cond
      [(TAddr? (πcc k*))
       (values Γ (Update sy k* (tc-expr* v)))]
      [else
       (values Γ
               (Update sy
                       (replace-ct
                        (type-error "Expect store lookup key to have an address type, got ~a" (πcc k*))
                        k*)
                       (tc-expr* v)))])]
    [(Where sy pat e)
     ;; We expect e and pat to have overlapping types,
     ;; but one's type doesn't drive the other's checking.
     (define e* (tc-expr* e))
     (define-values (Γ* pat*) (tc-pattern Γ Ξ pat))
     (cond
      [(type-overlap? (πcc e*) (πcc pat*))
       (values Γ* (Where sy pat* e*))]
      [else
       (values Γ*
               (Where sy pat*
                      (replace-ct
                       (type-error "Where clause has non-overlapping ~a: ~a"
                                   "pattern and expression types" bu)
                       e*)))])]))

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
    (define (chk pre-τ) (coerce-check-overlap ct expect-overlap pre-τ))
    (match pat
      [(PAnd sy _ ps)
       (let tcp* ([Γ Γ] [ps ps] [rev-ps* '()] [expect expect-overlap])
         (match ps
           ['() (values Γ (PAnd sy (chk expect) (reverse rev-ps*)))]
           [(cons p ps)
            (define-values (Γ* p*) (tc Γ p expect))
            (define τ (πcc p*))
            (tcp* Γ* ps (cons p* rev-ps*) (type-meet τ expect))]))]
        
      [(PName sy _ x)
       (match (hash-ref Γ x #f)
         [#f (define t (or expect-overlap T⊤))
             (values (hash-set Γ x t) (PName sy (chk t) x))]
         [τ (values
             Γ
             (cond
              [(type-overlap? τ expect-overlap)
               (PName sy (Check τ) x)]
              [else
               (PName sy
                      (type-error "~a ~a: ~a (type: ~a, expected overlap ~a)"
                                  "Non-linear Name pattern has"
                                  "non-overlapping initial type and expected overlapping type"
                                  pat τ expect-overlap)
                      x)]))])]

      [(PVariant sy _ n ps)
       (define len (length ps))
       ;; If we just have a single variant we expect, do a better job localizing errors.
       (define-values (expects bound? tr-c)
         (match (type-meet (resolve expect-overlap) (generic-variant n len))
           [(TVariant: _ n* τs bound? tr-c)
            ;; Name and length match due to type-meet
            (values τs bound? tr-c)]
           ;; XXX: is this the right behavior?
           [_ (type-error "Given variant ~a with arity ~a, expected overlap with ~a"
                          n len expect-overlap)]))

       (let all ([Γ Γ] [ps ps] [exs expects] [τs-rev '()] [rev-ps* '()])
         (match* (ps exs)
           [('() '())
            (values Γ (PVariant sy
                                (chk (*TVariant #f n (reverse τs-rev) bound? tr-c))
                                n
                                (reverse rev-ps*)))]
           [((cons p ps) (cons ex exs))
            (define-values (Γ* p*) (tc Γ p ex))
            (all Γ* ps exs (cons (πcc p*) τs-rev) (cons p* rev-ps*))]))]
        
      [(or (and (PMap-with sy _ k v p) (app (λ _ PMap-with) ctor))
           (and (PMap-with* sy _ k v p) (app (λ _ PMap-with*) ctor)))
       ;; Another localizing check
       (define-values (ext exk exv)
         (match (type-meet expect-overlap (mk-TMap #f T⊤ T⊤ 'dc))
           [(TMap: _ d r ext) (values ext d r)]
           ;; XXX: if not a map, then what?
           [_ (values limp-externalize-default T⊤ T⊤)]))
       (define-values (Γ* k*) (tc Γ k exk))
       (define-values (Γ** v*) (tc Γ* v exv))
       (define-values (Γ*** p*) (tc Γ** p expect-overlap))
       (values Γ***
               (ctor sy
                     (chk (type-join (mk-TMap (πcc k*) (πcc v*) ext) (πcc p*)))
                     k* v* p*))]
        
      [(or (and (PSet-with sy _ v p) (app (λ _ PSet-with) ctor))
           (and (PSet-with* sy _ v p) (app (λ _ PSet-with*) ctor)))
       ;; Another localizing check
       (define-values (ext exv)
         (match (type-meet expect-overlap (mk-TSet #f T⊤ 'dc))
           [(TSet: _ v ext) (values ext v)]
           [_ (values limp-externalize-default T⊤)]))
       (define-values (Γ* v*) (tc Γ v exv))
       (define-values (Γ** p*) (tc Γ* p expect-overlap))
       (values Γ**
               (ctor sy (chk (type-join (mk-TSet (πcc v*) ext) (πcc p*))) v* p*))]

      [(PTerm sy _ t)
       (define t* (tc-term Γ Ξ t expect-overlap))
       (PTerm sy (Typed-ct t*) t*)]
      [(or (? PWild?) (? PIsExternal?) (? PIsAddr?) (? PIsType?))
       (values Γ (replace-ct (chk T⊤) pat))]
      [_ (error 'tc-pattern "Unsupported pattern: ~a" pat)]))
  (trace tc)
  (tc Γ pat expect-overlap))


(define (tc-bus Γ Ξ bus)
  (let all ([Γ Γ] [bus bus] [rev-bus* '()])
    (match bus
      ['() (values Γ (reverse rev-bus*))]
      [(cons bu bus)
       (define-values (Γ* bu*) (tc-bu Γ Ξ bu))
       (all Γ* bus (cons bu* rev-bus*))])))

(define (check-and-join-rules Γ Ξ rules expect-discr expected)
  (let check ([rules rules] [τ T⊥] [rev-rules* '()])
   (match rules
     ['() (values (reverse rev-rules*) τ)]
     [(cons (Rule sy name lhs rhs bus) rules)
      (define-values (Γ* lhs*) (tc-pattern Γ Ξ lhs expect-discr))
      (define-values (Γ** bus*) (tc-bus Γ* Ξ bus))
      (define rhs* ((tc-expr Γ** Ξ) rhs expected))
      (check rules (type-join τ (πcc rhs*))
             (cons (Rule sy name lhs* rhs* bus*) rev-rules*))])))

;; Γ : Variable names ↦ Type,
;; Ξ : metafunction names ↦ Type,
;; e : expr
;; Output is expression's type.
(define ((tc-expr Γ Ξ) e [expected #f])
  (define (tc-expr* e expected)
    (define ct (Typed-ct e))
    (define stx (with-stx-stx e))
    (define (chk pre-τ) (coerce-check-expect ct expected pre-τ))
    (define (project-check pred form ty)
      (define σ
        (match ct
          [(Cast σ) σ]
          [(Check σ) σ]
          [_ (error 'project-check "Expected a type annotation ~a" form)]))
      (if (pred σ)
          ct
          (type-error "Expect ~a to have ~a type, got ~a" form ty σ)))
    (match e
      [(ECall sy _ mf tag τs es)
       (define mfτ (hash-ref Ξ mf (unbound-mf sy 'tc-expr mf)))
       ;; instantiate with all given types, error if too many
       (define inst (repeat-inst mfτ τs))
       ;; also error if too few
       (define-values (dom-σs rng)
         (cond
          [(TΛ? inst)
           (values (make-list
                    (length es)
                    (type-error
                     "Metafunction type must be fully instantiated, but ~a left: ~a"
                     (num-top-level-Λs inst) inst))
                   T⊤)]
          [else
           ;; INVARIANT: the metafunction type is a function and the domain is monovariant
           (match-define (TArrow: _ (TVariant: _ _ σs _ _) rng) inst)
           (values σs rng)]))
       ;; Check arguments against instantiated domain types.
       (define es*
         (for/list ([se (in-list es)]
                    [σ (in-list dom-σs)])
           (tc-expr* se σ)))
       (ECall sy (chk rng) mf tag τs es*)]

      [(EVariant sy _ n tag τs es)
       ;; Find all the n-named variants and find which makes sense.
       (define arity (length es))
       (define possible-σs (lang-variants-of-arity (generic-variant n arity)))
       (define-values (τout ess*)
         (for/fold ([τ T⊥] [ess* '()])
             ([σ (in-list possible-σs)])
           (define vσ (let/ec break (repeat-inst σ τs (λ () (break #f)))))
           (match vσ
             [#f (values τ ess*)]
             [(TVariant: _ _ σs _ _) ;; We know |σs| = |es| by possible-σs def.
              ;; expressions typecheck with a possible variant type?
              (define es*-op
                (let/ec break
                  (parameterize ([type-error-fn (λ _ (break #f))])
                    (for/list ([σ (in-list σs)]
                               [e (in-list es)])
                      (tc-expr* e σ)))))
              (if es*-op
                  ;; good, then it could be vσ too.
                  (values (type-join τ vσ) (cons es*-op ess*))
                  ;; well then it's not vσ.
                  (values τ ess*))])))
       ;; Each expression gets the joined type of its position.
       (define e-τs (make-vector arity T⊥))
       (for ([es (in-list ess*)])
         (for ([e (in-list es)]
               [i (in-naturals)])
           (vector-set! e-τs (type-join (vector-ref e-τs i) (πcc e)))))
       (define es*
         (for/list ([e (in-list es)]
                    [i (in-naturals)])
           (tc-expr* e (vector-ref e-τs i))))
       (EVariant sy (if (pair? ess*)
                        (chk τout)
                        (type-error "No variant type matched"))
                 tag τs es*)]

      [(ERef sy _ x)
       (ERef sy (chk (hash-ref Γ x (unbound-pat-var sy 'tc-expr x))) x)]
      
      [(EStore-lookup sy _ k lm)
       (define k* (tc-expr* k #f))
       ;; We expect k to be a TAddr type, but which kind doesn't matter
       (EStore-lookup
        sy
        (if (TAddr? (πcc k*))
            (chk T⊤)
            (type-error "Expect store lookup key to have an address type, got ~a" (πcc k*)))
        k* lm)]
      
      [(EAlloc sy _ tag)
       (EAlloc sy (project-check TAddr? "alloc" "address") tag)]

      [(ELet sy _ bus body)
       (define-values (Γ* bus*) (tc-bus Γ Ξ bus))
       (define body* ((tc-expr Γ* Ξ) body expected))
       (ELet sy (chk (πcc body*)) bus* body*)]

      [(EMatch sy _ de rules)
       (define d* (tc-expr* de #f))
       (define-values (rules* τjoin)
         (check-and-join-rules Γ Ξ rules (πcc d*) expected))
       (EMatch sy (chk τjoin) d* rules*)]

      [(EExtend sy _ m tag k v)
       (define m* (tc-expr* m #f))
       (define k* (tc-expr* k #f))
       (define v* (tc-expr* v #f))
       (EExtend sy 
                (chk (type-join (πcc m*) (mk-TMap #f (πcc k*) (πcc v*) 'dc)))
                m* tag k* v*)]

      [(EEmpty-Map sy _) (EEmpty-Map sy (project-check TMap? "empty-map" "map"))]

      [(EEmpty-Set sy _) (EEmpty-Set sy (project-check TSet? "empty-set" "set"))]

      [(ESet-union sy _ es)
       (define es* (for/list ([e (in-list es)]) (tc-expr* e expected)))
       (ESet-union sy
                   (chk
                    (for/fold ([τ T⊥]) ([e (in-list es*)])
                      (type-join τ (πcc e))))
                   es*)]

      [(ESet-intersection sy _ e es)
       (define e* (tc-expr* e generic-set))
       (define es* (for/list ([e (in-list es)]) (tc-expr* e generic-set)))
       (ESet-intersection sy
                          (chk
                           (for/fold ([τ (πcc e*)])
                               ([e (in-list es*)])
                             (type-meet τ (πcc e))))
                          e* es*)]

      [(ESet-subtract sy _ e es) (error 'tc-expr "Todo: set-subtract")]
      [(ESet-member sy _ e v) (error 'tc-expr "Todo: set-member?")]
      [(EMap-lookup sy _ m k) (error 'tc-expr "Todo: map-lookup")]
      [(EMap-has-key sy _ m k) (error 'tc-expr "Todo: map-has-key?")]
      [(EMap-remove sy _ m k) (error 'tc-expr "Todo: map-remove")]
      [_ (error 'tc-expr "Unrecognized expression form: ~a" e)]))
  (tc-expr* e expected))
(trace tc-bus tc-pattern tc-term tc-expr)
