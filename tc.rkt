#lang racket/base
(require (for-syntax syntax/parse racket/syntax racket/base)
         (only-in racket/bool implies)
         racket/list racket/match 
         racket/pretty
         racket/set
         racket/string racket/trace
         "common.rkt" "language.rkt" "tast.rkt" "types.rkt")
(provide tc-expr
         tc-pattern
         tc-term
         tc-rules
         tc-language
         tc-metafunctions
         report-all-errors
         check-for-heapification?)

(define check-for-heapification? (make-parameter #f))

;; TODO: syntax location tracking and reporting
(define ((unbound-mf sy who f))
  (raise-syntax-error who (format "Unbound metafunction name ~a" f) sy))
(define ((unbound-pat-var sy who x))
  (raise-syntax-error who (format "Unbound pattern variable: ~a" x) sy))

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
        (mk-TVariant #f 'pair (list (mk-TFree #f 'x #f) (mk-TFree #f 'y #f)) 'untrusted)
        'y))
      'x)))
  (check-equal? 2 (num-top-level-Λs ∀pair)))

(define (retag-THeap τ expect theap-tag)
  (if (THeap? expect)
      (match expect
        [(THeap: sy taddr tag _)
         (mk-THeap sy taddr (or tag theap-tag) τ)]
        [_ τ])
      τ))

(define (coerce-check-expect ct expect τ theap-tag)
  (define (sub-t who τ ct)
    (define (bad)
      (type-error "(~a) Expected ~a, got ~a" who expect τ))
    (cond
     [expect
      (if (<:? τ expect)
          (or ct
              (Check (retag-THeap τ expect theap-tag)))
          (match τ
            ;; We have a one-off downcast that needs a dereference coercion
            [(THeap: sy taddr tag τ*)
             (cond
              [(<:? τ* expect)
               ;; The tag doesn't matter since it's being deref'd and not allocated.
               (Deref taddr (or ct (Check τ)))]
              (bad))]
            [_ (bad)]))]
     [else (or ct (Check τ))]))
  (match ct
    [(Cast σ) ;; XXX: what do we do with casts that must be heapified?
     (define ct* (cast-to τ σ))
     (sub-t 'A (πct ct*) ct*)]
    [(Check σ)
     (cond
      [(<:? τ σ) (sub-t 'B τ #f)]
      [else (type-error "Expect ~a to be a subtype of ~a" τ σ)])]
    [(? Trust?) ct]
    [_ (sub-t 'C τ #f)]))

(define (coerce-check-overlap ct expect-overlap τ)
  (define (chk ct)
    (unless (or (Cast? ct) (Check? ct)) (error 'chk "Fak ~a" ct))
    (define τ
      (if expect-overlap
          (type-meet (πct ct) expect-overlap)
          #f))
    (if τ
        (if (T⊥? τ)
            (type-error "Expected ~a to overlap with ~a" expect-overlap τ)
            (ct-replace-τ ct τ))
        ct))
  (match ct
    [(Cast σ) (chk (cast-to τ σ))]
    [(Check σ)
     (cond
      [(<:? τ σ) (chk (Check σ))]
      [else
       (type-error "Overlap check: Expect ~a to be a subtype of ~a" τ σ)])]
    [(? Trust?) ct]
    [_ (chk (Check τ))]))

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

(define (tc-bu Γ Ξ bu path)
  (define tc-expr* (tc-expr Γ Ξ))
  (match bu
    [(Update sy k v)
     (define k* (tc-expr* k #:path (cons 'update-key path)))
     ;; We expect k to be a TAddr type, but which kind doesn't matter
     (cond
      [(TAddr? (πcc k*))
       (values Γ (Update sy k* (tc-expr* v #:path (cons 'update-value path))))]
      [else
       (values Γ
               (Update sy
                       (replace-ct
                        (type-error "Expect store lookup key to have an address type, got ~a"
                                    (πcc k*))
                        k*)
                       (tc-expr* v #:path (cons 'update-value path))))])]
    [(Where sy pat e)
     ;; We expect e and pat to have overlapping types,
     ;; but one's type doesn't drive the other's checking.
     (define e* (tc-expr* e #:path (cons 'where-rhs path)))
     (define-values (Γ* pat*) (tc-pattern Γ Ξ pat (πcc e*)))
     (values Γ* (Where sy pat* e*))]))

(define (tc-term Γ Ξ t expect-overlap)
  (define ct (Typed-ct t))
  (define (chk pre-τ) (coerce-check-overlap ct expect-overlap pre-τ))
  (match t
    [(Variant sy _ n ts) (error 'tc-term "Check variant")]
    [(Map sy _ f) (error 'tc-term "Check map")]
    [(Set sy _ s) (error 'tc-term "Check set")]
    [(External sy _ v) (error 'tc-term "Check external")]
    [_ (error 'tc-term "Unsupported term ~a" t)]))

;; expect-overlap is a type or a list of types (no expectations should be T⊤)
(define (tc-pattern Γ Ξ pat expect-overlap)
  (define (tc Γ pat expect-overlap)
    (unless expect-overlap (error 'tc-pattern "Overlap is #f ~a" pat))
    (define ct (Typed-ct pat))
    (define (chk pre-τ) (coerce-check-overlap ct expect-overlap pre-τ))
    (match pat
      [(PAnd sy _ ps)
       (let tcp* ([Γ Γ] [ps ps] [rev-ps* '()] [expect expect-overlap])
         (match ps
           ['()
            (values Γ (PAnd sy (chk expect) (reverse rev-ps*)))]
           [(cons p ps)
            (define-values (Γ* p*) (tc Γ p expect))
            (define τ (πcc p*))
            (tcp* Γ* ps (cons p* rev-ps*) (type-meet τ expect))]))]
        
      [(PName sy _ x)
       (match (hash-ref Γ x #f)
         [#f (define t (or (πct ct) expect-overlap T⊤))
             (values (hash-set Γ x t) (PName sy (chk t) x))]
         [τ
          (define τ* (type-meet τ expect-overlap))
          (define ct*
            (if (T⊥? τ*)
                (type-error "~a ~a: ~a (type: ~a, expected overlap ~a)"
                                   "Non-linear Name pattern has"
                                   "non-overlapping initial type and expected overlapping type"
                                   pat τ expect-overlap)
                (Check τ*)))
          (values Γ (PName sy ct* x))])]

      [(PVariant sy _ n ps)
       (define len (length ps))
       ;; If we just have a single variant we expect, do a better job localizing errors.
       (define res (resolve expect-overlap))
       (define met (type-meet res (generic-variant n len)))
       (define-values (expects err hfy)
         (match met
           [(TVariant: _ n* τs tr)
            ;; Name and length match due to type-meet
            (values τs #f (λ (τs) (*TVariant #f n τs tr)))]
           [(THeap: sy taddr tag (TVariant: _ n* τs tr))
            ;; Name and length match due to type-meet
            (values τs #f (λ (τs) (mk-THeap sy taddr tag (*TVariant #f n τs tr))))]
           ;; XXX: is this the right behavior?
           [_ (values (make-list len T⊤)
                      (type-error "Given variant ~a with arity ~a, expected overlap with ~a {~a}"
                                  n len res met)
                      (λ (τs) (*TVariant #f n τs 'dc)))]))

       (let all ([Γ Γ] [ps ps] [exs expects] [τs-rev '()] [rev-ps* '()])
         (match* (ps exs)
           [('() '())
            (values Γ (PVariant sy
                                (or err
                                    (chk (hfy (reverse τs-rev))))
                                n
                                (reverse rev-ps*)))]
           [((cons p ps) (cons ex exs))
            (define-values (Γ* p*) (tc Γ p ex))
            (all Γ* ps exs (cons (πcc p*) τs-rev) (cons p* rev-ps*))]))]
        
      [(or (and (PMap-with sy _ k v p) (app (λ _ PMap-with) ctor))
           (and (PMap-with* sy _ k v p) (app (λ _ PMap-with*) ctor)))
       ;; Another localizing check
       (define-values (exk exv hfy)
         (match (resolve (type-meet expect-overlap generic-map))
           [(TMap: _ d r ext) (values d r (λ (d r) (mk-TMap #f d r ext)))]
           [(THeap: sy taddr tag (TMap: _ d r ext))
            (values d r (λ (d r) (mk-THeap sy taddr tag (mk-TMap #f d r ext))))]
           ;; XXX: if not a map, then what?
           [_ (values T⊤ T⊤ (λ (d r) (mk-TMap #f d r limp-externalize-default)))]))
       (define-values (Γ* k*) (tc Γ k exk))
       (define-values (Γ** v*) (tc Γ* v exv))
       (define-values (Γ*** p*) (tc Γ** p expect-overlap))
       (values Γ***
               (ctor sy
                     (chk (type-join (hfy (πcc k*) (πcc v*)) (πcc p*)))
                     k* v* p*))]
        
      [(or (and (PSet-with sy _ v p) (app (λ _ PSet-with) ctor))
           (and (PSet-with* sy _ v p) (app (λ _ PSet-with*) ctor)))
       ;; Another localizing check
       (define-values (exv hfy)
         (match (resolve (type-meet expect-overlap generic-set))
           [(TSet: _ v ext) (values v (λ (τ) (mk-TSet #f τ ext)))]
           [(THeap: sy taddr tag (TSet: _ v ext))
            (values v (λ (τ) (mk-THeap sy taddr tag (mk-TSet #f τ ext))))]           
           [_ (values T⊤ (λ (τ) (mk-TSet #f T⊤ limp-externalize-default)))]))
       (define-values (Γ* v*) (tc Γ v exv))
       (define-values (Γ** p*) (tc Γ* p expect-overlap))
       (values Γ**
               (ctor sy (chk (type-join (hfy (πcc v*)) (πcc p*)))
                     v* p*))]

      [(PDeref sy _ p)
       (define expect*
         (match (resolve (πct ct))
           [(or (? TAddr?)
                (TSUnion: _ (list (? TAddr?) ...))
                (TRUnion: _ (list (? TAddr?) ...)))
            (chk T⊤)]
           [(THeap: _ taddr tag τ)
            (Check τ)]
           [τ (type-error "Deref patterns must be unambiguously address types")]))
       (PDeref sy expect* (tc Γ p (πct expect*)))]

      [(PTerm sy _ t)
       (define t* (tc-term Γ Ξ t expect-overlap))
       (PTerm sy (Typed-ct t*) t*)]
      [(or (? PWild?) (? PIsExternal?) (? PIsAddr?) (? PIsType?))
       (values Γ (replace-ct (chk T⊤) pat))]
      [_ (error 'tc-pattern "Unsupported pattern: ~a" pat)]))
  (tc Γ pat expect-overlap))

(define (tc-bus Γ Ξ bus head path)
  (let all ([Γ Γ] [bus bus] [i 0] [rev-bus* '()])
    (match bus
      ['() (values Γ (reverse rev-bus*))]
      [(cons bu bus)
       (define-values (Γ* bu*) (tc-bu Γ Ξ bu `((,head . ,i) . ,path)))
       (all Γ* bus (add1 i) (cons bu* rev-bus*))])))

(define (check-and-join-rules Γ Ξ rules expect-discr expected head path)
  (let check ([rules rules] [τ T⊥] [i 0] [rev-rules* '()])
   (match rules
     ['() (values (reverse rev-rules*) τ)]
     [(cons rule rules)
      (define rule* (tc-rule Γ Ξ rule expect-discr expected (cons head i) path))
      (check rules
             (type-join τ (πcc (Rule-rhs rule*)))
             (add1 i)
             (cons rule* rev-rules*))])))

(define (tc-rule Γ Ξ rule expect-discr expected head path)
  (match-define (Rule sy name lhs rhs bus) rule)
  (define-values (Γ* lhs*) (tc-pattern Γ Ξ lhs expect-discr))
  (define path* (cons (or name head) path))
  (define-values (Γ** bus*) (tc-bus Γ* Ξ bus 'rule-bu path*))
  (define rhs* ((tc-expr Γ** Ξ) rhs expected #:path path*))
  (Rule sy name lhs* rhs* bus*))

(define (tc-rules Γ Ξ rules expect-discr expected head path)
  (for/list ([rule (in-list rules)]
             [i (in-naturals)])
    (tc-rule Γ Ξ rule expect-discr expected (cons head i) path)))

;; Rewriting for monomorphization means updating paths to be specific to the
;; given type. Thus we mark built tags with an implicit-tag construction.
;; NOTE: Any user-defined tag will be the same regardless of monomorphization!
(define (give-tag tag path)
  (if (implies tag (implicit-tag? tag))
      (implicit-tag path)
      tag))

(define (explicit-tag tag tail)
  (and tag (not (implicit-tag? tag)) (cons tail tail)))

;; Γ : Variable names ↦ Type,
;; Ξ : metafunction names ↦ Type,
;; e : expr
;; Output is a fully annotated expression
(define ((tc-expr Γ Ξ) e [expected #f] #:path [path '()])
  (define (tc-expr* e expected path #:tagged [tagged #f])
    (define ct (Typed-ct e))
    (cond
     [(Trust? ct) e]
     [else
      (define stx (with-stx-stx e))
      (define (chk pre-τ) (coerce-check-expect ct expected pre-τ (or tagged path)))
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
        [(ECall sy _ mf τs es)
         ;; We monomorphize as well as check the function.
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
             (match-define (TArrow: _ (TVariant: _ _ σs _) rng) inst)
             (values σs rng)]))
         ;; Check arguments against instantiated domain types.
         (define es*
           (for/list ([se (in-list es)]
                      [σ (in-list dom-σs)]
                      [i (in-naturals)])
             (tc-expr* se σ `((call ,mf . ,i) . ,path))))
         (define H (monomorphized))
         (define renamed
           (cond
            [(and H (andmap mono-type? dom-σs) (mono-type? rng))
             ;; We recheck whole mf body to get the instantiations.
             (define mf-mono (hash-ref! H mf make-hash))
             (define name* ((mono-namer) mf τs))
             (unless (hash-has-key? mf-mono name*)
               (hash-set! mf-mono name* 'gray) ;; don't diverge with self-calls
               (hash-set!
                mf-mono name*
                (Metafunction name* inst
                              (tc-rules #hash() Ξ
                                        ;; instantiate the mono-types in the mf body.
                                        (open-scopes-in-rules
                                         (Metafunction-rules (hash-ref (mf-defs) mf))
                                         (reverse τs)) ;; Outermost first.
                                        (TArrow-dom inst)
                                        rng
                                        `(def . ,name*)
                                        '()))))
             name*]
            [else #f]))
         (if renamed ;; monomorphized
             (ECall sy (chk rng) renamed '() es*)
             (ECall sy (chk rng) mf τs es*))]

        [(EVariant sy _ n tag τs es)
         ;; Find all the n-named variants and find which makes sense.
         (define arity (length es))
         (define generic (generic-variant n arity))
         ;; If we expect a type, we have a cast or explicit check, then use those rather than
         ;; an inferred variant type.
         (define (do σs tr)
           ;; expressions typecheck with a possible variant type?
           (define es*
             (for/list ([σ (in-list σs)]
                        [e (in-list es)]
                        [i (in-naturals)])
               (tc-expr* e σ `((,n . ,i) . ,path) #:tagged (explicit-tag tag i))))
           (EVariant sy
                     (if (eq? tr 'bounded)
                         (type-error "Constructed a variant marked as bounded: ~a" n)
                         (Check (mk-TVariant #f n (map πcc es*) tr)))
                     n (give-tag tag path) τs es*))
         (define (infer)
           (define possible-σs (lang-variants-of-arity generic))
           (define found
             (for*/first ([σ (in-list possible-σs)]
                          [es*-op
                           (in-value
                            (let/ec break
                              (match (repeat-inst σ τs (λ () (break #f)))
                                [(TVariant: _ _ σs tr) ;; We know |σs| = |es| by possible-σs def.
                                 (parameterize ([type-error-fn (λ _ (break #f))])
                                   (do σs tr))]
                                [_ #f])))]
                          #:when es*-op)
               es*-op))
           (or found
               ;; Check subexpressions, but on the whole this doesn't work.
               (EVariant sy
                         (type-error "No variant type matched")
                         n tag τs (for/list ([e (in-list es)]
                                             [i (in-naturals)])
                                    (tc-expr* e T⊤ `((,n . ,i) . ,path))))))
         ;; XXX: type-meet does unification!
         (if expected
             (match (resolve (type-meet expected generic))
               [(TVariant: _ _ σs tr) (do σs tr)]
               [_ 'bad])
             (match ct
               [(Check τ)
                (match (resolve (type-meet τ generic))
                  [(TVariant: _ _ σs tr) (do σs tr)]
                  [_ (infer)])]
               [_ (infer)]))]

        [(ERef sy _ x)
         (ERef sy (chk (hash-ref Γ x (unbound-pat-var sy 'tc-expr x))) x)]
      
        [(EStore-lookup sy _ k lm imp)
         ;; k has an expected type if this is an implicit lookup
         (define k* (tc-expr* k (and imp expected) (cons 'lookup path)))
         (define ct*
           (cond
            [imp
             (cond
              [(check-for-heapification?)
               (define kct (Typed-ct k*))
               (define kτ (πct kct))
               (if (and (Deref? kct) (THeap? kτ))
                   (Cast (THeap-τ kτ))
                   (type-error "Implicit lookup did not have a downcast from #:heapify: ~a" 
                               kct))]
              [else ;; Not checking for heapification, so ignore that this is a lookup form.
               (EStore-lookup sy (Typed-ct k*) k* lm imp)])]
            ;; Explicit lookup means we expect k to be a TAddr type,
            ;; but which kind doesn't matter
            [(TAddr? (resolve (πcc k*)))
             (chk T⊤)]
            [else
             (type-error "Expect store lookup key to have an address type, got ~a" (πcc k*))]))
         (EStore-lookup sy ct* k* lm imp)]
      
        [(EAlloc sy _ tag)
         (EAlloc sy (project-check TAddr? "alloc" "address") (give-tag tag path))]

        [(ELet sy _ bus body)
         (define-values (Γ* bus*) (tc-bus Γ Ξ bus 'let-bu path))
         (define body* ((tc-expr Γ* Ξ) body expected #:path (cons 'let-body path)))
         (ELet sy (chk (πcc body*)) bus* body*)]

        [(EMatch sy _ de rules)
         (define d* (tc-expr* de #f (cons 'match-disc path)))
         (define-values (rules* τjoin)
           (check-and-join-rules Γ Ξ rules (πcc d*) expected 'match-rule path))
         (EMatch sy (chk τjoin) d* rules*)]

        [(EExtend sy _ m tag k v)
         (define-values (d r ext)
           (match (resolve (type-meet expected generic-map))
             [(TMap: _ d r ext) (values d r ext)] ;; XXX: shouldn't be heapified?
             [_ (values #f #f 'dc)]))
         (define m* (tc-expr* m expected (cons 'extend-map path)))
         (define k* (tc-expr* k d (cons 'extend-key path) #:tagged (explicit-tag tag 0)))
         (define v* (tc-expr* v r (cons 'extend-value path) #:tagged (explicit-tag tag 1)))
         (EExtend sy (chk (type-join (πcc m*) (mk-TMap #f (πcc k*) (πcc v*) ext)))
                  m* (give-tag tag path) k* v*)]

        [(EEmpty-Map sy _) (EEmpty-Map sy (project-check TMap? "empty-map" "map"))]

        [(EEmpty-Set sy _) (EEmpty-Set sy (project-check TSet? "empty-set" "set"))]

        [(ESet-union sy _ es)
         (define es* (for/list ([e (in-list es)]
                                [i (in-naturals)])
                       (tc-expr* e expected `((union . ,i) . ,path))))
         (ESet-union sy
                     (chk
                      (for/fold ([τ T⊥]) ([e (in-list es*)])
                        (type-join τ (πcc e))))
                     es*)]

        [(ESet-add sy _ e tag es)
         (define e* (tc-expr* e generic-set `((set-add . 0) . ,path)))
         (define es*
           (for/list ([e (in-list es)]
                      [i (in-naturals 1)])
             (tc-expr* e #f `((set-add . ,i) . ,path) #:tagged (explicit-tag tag i))))
         (ESet-add sy
                   (chk
                    (for/fold ([τ (πcc e*)]) ([e (in-list es*)])
                      (type-join τ (mk-TSet #f (πcc e) 'dc))))
                   e*
                   (give-tag tag path)
                   es*)]

        [(ESet-intersection sy _ e es)
         (match-define (cons e* es*)
                       (for/list ([e (in-list (cons e es))]
                                  [i (in-naturals)])
                         (tc-expr* e generic-set `((intersection . ,i) . ,path))))
         (ESet-intersection sy
                            (chk
                             (for/fold ([τ (πcc e*)])
                                 ([e (in-list es*)])
                               (type-meet τ (πcc e))))
                            e* es*)]

        [(ESet-subtract sy _ e es) (error 'tc-expr "Todo: set-subtract")]
        [(ESet-member sy _ e v) (error 'tc-expr "Todo: set-member?")]
        [(EMap-lookup sy _ m k)
         (define m* (tc-expr* m generic-map (cons 'lookup-map path)))
         (match (resolve (type-meet (πcc m*) generic-map))
           [(TMap: _ d r _) ;; XXX: shouldn't be heapified?
            (EMap-lookup sy (chk r) m* (tc-expr* k d (cons 'lookup-key path)))]
           [τ (EMap-lookup sy (type-error "Expected a map type: ~a" τ)
                           m* (tc-expr* k T⊤ (cons 'lookup-key path)))])]
        [(EMap-has-key sy _ m k) (error 'tc-expr "Todo: map-has-key?")]
        [(EMap-remove sy _ m k) (error 'tc-expr "Todo: map-remove")]
        [_ (error 'tc-expr "Unrecognized expression form: ~a" e)])]))
  (tc-expr* e expected path))

;; Map a name to a map of types to metafunction definitions.
;; This separates all metafunctions out into their appropriate monomorphizations.
;; The naming scheme for the monomorphizations is based on ???
(define monomorphized (make-parameter #f))
(define mf-defs (make-parameter #f))
(define mono-namer (make-parameter #f))

(define (tc-language rules metafunctions state-τ
                     #:use-lang [lang (current-language)]
                     #:mono-naming [namer (λ (name type)
                                             (string->symbol (format "~a~a" name type)))])
  ;; To resolve mf name to type while typechecking.
  (define Ξ
    (for/hash ([mf (in-list metafunctions)])
      (match-define (Metafunction name τ _) mf)
      (values name τ)))
  ;; Get the checked, general forms of the metafunctions
  (define mfs* (tc-metafunctions metafunctions Ξ))
  (parameterize ([monomorphized (make-hash)]
                 [mf-defs (for/hash ([mf (in-list mfs*)])
                            (values (Metafunction-name mf) mf))]
                 [mono-namer namer])
    ;; with monomorphized set to a hash, tc-metafunctions will create the
    ;; monomorphized versions of the monomorphic instantiations in the
    ;; metafunction definitions themselves.
    (tc-metafunctions mfs* Ξ)
    ;; When checking the rules, all ecalls will additionally populate monomorphized
    (values (tc-rules #hash() Ξ rules state-τ state-τ 'root '())
            (append-map hash-values (hash-values (monomorphized))))))

;; Typecheck all metafunctions
(define (tc-metafunctions mfs Ξ)
  (for/list ([mf (in-list mfs)])
    (match-define (Metafunction name τ scoped-rules) mf)
    (match-define-values (names (TArrow: _ dom rng) rules) (open-type-and-rules τ scoped-rules))
    (define rules* (tc-rules #hash() Ξ rules dom rng `(def . ,name) '()))
    (Metafunction name τ (abstract-frees-in-rules rules* names))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Error reporting
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (raise-typecheck-error msg stxs)
  (define who (string->symbol "Type Checker"))
  (match stxs
    ['() (raise-syntax-error who msg)]
    [(list stx) (raise-syntax-error who msg (car stxs))]
    [stxs (raise-syntax-error who msg #f #f stxs)]))

(define error-list null)
(struct err (msg stx) #:prefab)

(define (report-rule-errors r)
  (match-define (Rule _ name lhs rhs bus) r)
  (report-pattern-errors lhs)
  (for-each report-bu-errors bus)
  (report-expression-errors rhs))

(define (err-chk typed)
  (define τ (πcc typed))
  (when (TError? τ)
    (set! error-list (cons (err (TError-msgs τ) (with-stx-stx typed)) error-list))))

(define (report-pattern-errors pat)
  (err-chk pat)
  (match pat
    [(or (PAnd _ _ ps) (PVariant _ _ _ ps)) (for-each report-pattern-errors ps)]
    [(or (PMap-with _ _ k v p)
         (PMap-with* _ _ k v p))
     (report-pattern-errors k)
     (report-pattern-errors v)
     (report-pattern-errors p)]
    [(or (PSet-with _ _ v p)
         (PSet-with* _ _ v p))
     (report-pattern-errors v)
     (report-pattern-errors p)]
    [(PTerm _ _ t) (report-term-errors t)]
    [_ (void)]))

(define (report-term-errors t)
  (err-chk t)
  (match t
    [(Variant _ _ _ ts) (for-each report-term-errors ts)]
    [(Map _ _ f) (for ([(k v) (in-hash f)])
                   (report-term-errors k)
                   (report-term-errors v))]
    [(Set _ _ s) (for ([t (in-set s)]) (report-term-errors t))]
    [_ (void)]))

(define (report-bu-errors bu)
  (match bu
    [(Update _ k v)
     (report-expression-errors k)
     (report-expression-errors v)]
    [(Where _ pat e)
     (report-pattern-errors pat)
     (report-expression-errors e)]))

(define (report-expression-errors e)
  (err-chk e)
  (match e
    [(or (ECall _ _ _ _ es)
         (EVariant _ _ _ _ _ es)
         (ESet-union _ _ es))
     (for-each report-expression-errors es)]
    [(EStore-lookup _ _ k _ _)
     (report-expression-errors k)]
    [(ELet _ _ bus body)
     (for-each report-bu-errors bus)
     (report-expression-errors body)]
    [(EMatch _ _ de rules)
     (report-expression-errors de)
     (for-each report-rule-errors rules)]
    [(EExtend _ _ m _ k v)
     (report-expression-errors m)
     (report-expression-errors k)
     (report-expression-errors v)]
    [(or (ESet-intersection _ _ e es)
         (ESet-subtract _ _ e es))
     (report-expression-errors e)
     (for-each report-expression-errors es)]
    [(or (ESet-member _ _ e0 e1)
         (EMap-lookup _ _ e0 e1)
         (EMap-has-key _ _ e0 e1)
         (EMap-remove _ _ e0 e1))
     (report-expression-errors e0)
     (report-expression-errors e1)]
    [_ (void)]))


(define (report-all-errors v)
  (set! error-list null)
  (let populate ([v v])
    (cond [(Rule? v) (report-rule-errors v)]
          [(Expression? v) (report-expression-errors v)]
          [(Pattern? v) (report-pattern-errors v)]
          [(BU? v) (report-bu-errors v)]
          [(list? v) (for-each populate v)]))
  (define stxs
    (for/list ([e (in-list (reverse error-list))])
      (with-handlers ([exn:fail:syntax?
                       (λ (e) ((error-display-handler) (exn-message e) e))])
        (raise-typecheck-error (string-join (err-msg e) "\n") (list (err-stx e))))
      (err-stx e)))
  (set! error-list null)
  (unless (null? stxs)
    (raise-typecheck-error (format "Summary: ~a errors encountered" (length stxs))
                           (filter values stxs))))
