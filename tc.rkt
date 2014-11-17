#lang racket/base
(require (for-syntax syntax/parse racket/syntax racket/base)
         (only-in racket/bool implies)
         racket/list racket/match racket/set
         racket/string racket/trace
         "common.rkt" "language.rkt" "tast.rkt" "types.rkt")
(provide tc-expr
         tc-pattern
         tc-term
         tc-rules
         report-all-errors)

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

(define (coerce-check-expect ct expect τ)
  (match ct
    [(Cast σ)
     (define ct* (cast-to τ σ))
     (cond
      [(implies expect (<:? (πct ct*) expect))
       ct*]
      [else (type-error "(A) Expected ~a, got ~a" expect τ)])]
    [(Check σ)
     (cond
      [(<:? τ σ)
       (cond
        [(implies expect (<:? τ expect))
         (Check τ)]
        [else
         (type-error "(B) Expected ~a, got ~a" expect τ)])]
      [else (type-error "Expect ~a to be a subtype of ~a" τ σ)])]
    [_
     (cond
      [(implies expect (<:? τ expect)) (Check τ)]
      [else (type-error "(C ~a) Expected ~a, got ~a" ct expect τ)])]))

(define (coerce-check-overlap ct expect-overlap τ)
  (define (chk ct)
    (unless (or (Cast? ct) (Check? ct)) (error 'chk "Fak ~a" ct))
    (if (implies expect-overlap (type-overlap? (πct ct) expect-overlap))
        #f
        (type-error "Expected ~a to overlap with ~a" expect-overlap τ)))
  (match ct
    [(Cast σ)
     (define ct (cast-to τ σ))
     (or (chk ct) ct)]
    [(Check σ)
     (cond
      [(<:? τ σ)
       (define ct (Check σ))
       (or (chk ct) ct)]
      [else
       (type-error "Overlap check: Expect ~a to be a subtype of ~a" τ σ)])]
    [_ (define ct (Check τ))
       (or (chk ct) ct)]))

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
     (define-values (Γ* pat*) (tc-pattern Γ Ξ pat (πcc e*)))
     (values Γ* (Where sy pat* e*))]))

(define (type-overlap? τ τ-or-τs)
  (match τ-or-τs
    ['() #f]
    [(cons σ σs) (and (type-overlap? τ σ) (type-overlap? τ σs))]
    [σ (not (T⊥? (type-meet τ σ)))]))

(module+ test
  (check-true (type-overlap?
               ;; ab = (U a<> b<>)
               ;; foo<ab> ⋈ (U foo<b> bar<⊤>)
               (mk-TVariant #f 'foo
                            (list (*TRUnion #f (list (mk-TVariant #f 'a '() 'untrusted)
                                                     (mk-TVariant #f 'b '() 'untrusted))))
                            'untrusted)
               (*TRUnion #f (list (mk-TVariant #f 'foo (list (mk-TVariant #f 'b '() 'untrusted))
                                               'untrusted)
                                  (mk-TVariant #f 'bar (list T⊤) 'untrusted))))))

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
       (define res (resolve expect-overlap))
       (define met (type-meet res (generic-variant n len)))
       (define-values (expects tr)
         (match met
           [(TVariant: _ n* τs tr)
            ;; Name and length match due to type-meet
            (values τs tr)]
           ;; XXX: is this the right behavior?
           [_ (values (make-list
                       len
                       (type-error "Given variant ~a with arity ~a, expected overlap with ~a"
                                   n len expect-overlap))
                      'dc)]))

       (let all ([Γ Γ] [ps ps] [exs expects] [τs-rev '()] [rev-ps* '()])
         (match* (ps exs)
           [('() '())
            (values Γ (PVariant sy
                                (chk (*TVariant #f n (reverse τs-rev) tr))
                                n
                                (reverse rev-ps*)))]
           [((cons p ps) (cons ex exs))
            (define-values (Γ* p*) (tc Γ p ex))
            (all Γ* ps exs (cons (πcc p*) τs-rev) (cons p* rev-ps*))]))]
        
      [(or (and (PMap-with sy _ k v p) (app (λ _ PMap-with) ctor))
           (and (PMap-with* sy _ k v p) (app (λ _ PMap-with*) ctor)))
       ;; Another localizing check
       (define-values (ext exk exv)
         (match (resolve (type-meet expect-overlap generic-map))
           [(TMap: _ d r ext) (values ext d r)]
           ;; XXX: if not a map, then what?
           [_ (values limp-externalize-default T⊤ T⊤)]))
       (define-values (Γ* k*) (tc Γ k exk))
       (define-values (Γ** v*) (tc Γ* v exv))
       (define-values (Γ*** p*) (tc Γ** p expect-overlap))
       (values Γ***
               (ctor sy
                     (chk (type-join
                           (mk-TMap #f (πcc k*) (πcc v*) ext)
                           (πcc p*)))
                     k* v* p*))]
        
      [(or (and (PSet-with sy _ v p) (app (λ _ PSet-with) ctor))
           (and (PSet-with* sy _ v p) (app (λ _ PSet-with*) ctor)))
       ;; Another localizing check
       (define-values (ext exv)
         (match (resolve (type-meet expect-overlap generic-set))
           [(TSet: _ v ext) (values ext v)]
           [_ (values limp-externalize-default T⊤)]))
       (define-values (Γ* v*) (tc Γ v exv))
       (define-values (Γ** p*) (tc Γ* p expect-overlap))
       (values Γ**
               (ctor sy (chk (type-join
                              (mk-TSet #f (πcc v*) ext)
                              (πcc p*)))
                     v* p*))]

      [(PTerm sy _ t)
       (define t* (tc-term Γ Ξ t expect-overlap))
       (PTerm sy (Typed-ct t*) t*)]
      [(or (? PWild?) (? PIsExternal?) (? PIsAddr?) (? PIsType?))
       (values Γ (replace-ct (chk T⊤) pat))]
      [_ (error 'tc-pattern "Unsupported pattern: ~a" pat)]))
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
     [(cons rule rules)
      (define rule* (tc-rule Γ Ξ rule expect-discr expected))
      (check rules
             (type-join τ (πcc (Rule-rhs rule*)))
             (cons rule* rev-rules*))])))

(define (tc-rule Γ Ξ rule expect-discr expected)
  (match-define (Rule sy name lhs rhs bus) rule)
  (define-values (Γ* lhs*) (tc-pattern Γ Ξ lhs expect-discr))
  (define-values (Γ** bus*) (tc-bus Γ* Ξ bus))
  (define rhs* ((tc-expr Γ** Ξ) rhs expected))
  (Rule sy name lhs* rhs* bus*))

(define (tc-rules Γ Ξ rules expect-discr expected)
  (for/list ([rule (in-list rules)])
    (tc-rule Γ Ξ rule expect-discr expected)))

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
      [(ECall sy _ mf τs es)
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
                    [σ (in-list dom-σs)])
           (tc-expr* se σ)))
       (ECall sy (chk rng) mf τs es*)]

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
                      [e (in-list es)])
             (tc-expr* e σ)))
         (EVariant sy
                   (Check (mk-TVariant #f n (map πcc es*) tr))
                   n tag τs es*))
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
             (EVariant sy (type-error "No variant type matched")
                       n tag τs (for/list ([e (in-list es)]) (tc-expr* e T⊤)))))
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
       (define-values (d r ext)
         (match (resolve (type-meet expected generic-map))
           [(TMap: _ d r ext) (values d r ext)]
           [_ (values #f #f 'dc)]))
       (define m* (tc-expr* m expected))
       (define k* (tc-expr* k d))
       (define v* (tc-expr* v r))
       ;; Can't use 'dc when we expect #t/#f since 'dc is higher in the lattice.
       (EExtend sy 
                (chk (type-join (πcc m*) (mk-TMap #f (πcc k*) (πcc v*) ext)))
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
      [(EMap-lookup sy _ m k)
       (define m* (tc-expr* m generic-map))
       (match (resolve (type-meet (πcc m*) generic-map))
         [(TMap: _ d r _)
          (EMap-lookup sy (chk r) m* (tc-expr* k d))]
         [τ (EMap-lookup sy (type-error "Expected a map type: ~a" τ)
                         m* (tc-expr* k T⊤))])]
      [(EMap-has-key sy _ m k) (error 'tc-expr "Todo: map-has-key?")]
      [(EMap-remove sy _ m k) (error 'tc-expr "Todo: map-remove")]
      [_ (error 'tc-expr "Unrecognized expression form: ~a" e)]))
  (tc-expr* e expected))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Error reporting
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (raise-typecheck-error msg stxs)
  (if (null? (cdr stxs))
      (raise-syntax-error (string->symbol "Type Checker") msg (car stxs))
      (raise-syntax-error (string->symbol "Type Checker") msg #f #f stxs)))

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
    [(EStore-lookup _ _ k _)
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
                           stxs)))
