#lang racket/base
(require (for-syntax syntax/parse racket/syntax racket/base)
         (only-in racket/bool implies)
         racket/list racket/match
         racket/pretty
         racket/set
         racket/string racket/trace
         (only-in "alloc-rules.rkt" normalize-taddr)
         "common.rkt" "language.rkt" "tast.rkt" "types.rkt")
(provide tc-expr
         tc-pattern
         tc-term
         tc-rules
         tc-language
         tc-metafunctions
         report-all-errors)

;; TODO: syntax location tracking and reporting
(define ((unbound-mf sy who f))
  (raise-syntax-error who (format "Unbound metafunction name ~a" f) sy))
(define ((unbound-pat-var sy who x))
  (raise-syntax-error who (format "Unbound pattern variable: ~a" x) sy))

(module+ test (require rackunit)
  ;; ∀pair = ΛXY. pair<X,Y>
  (define ∀pair
    (mk-TΛ #f 'x
     (abstract-free
      (mk-TΛ #f 'y
       (abstract-free
        (mk-TVariant #f 'pair (list (mk-TFree #f 'x) (mk-TFree #f 'y)) 'untrusted)
        'y))
      'x)))
  (check-equal? 2 (num-top-level-Λs ∀pair)))

(define (check-term ct expect τ)
  (define (sub-t who τ ct)
    (cond
     [expect
      (if (<:? τ expect)
          (or ct (Check (type-meet τ expect)))
          (type-error "(~a) Expected ~a, got ~a" who expect τ))]
     [else (or ct (Check τ))]))
  (match ct
    [(Cast σ)
     (define ct* (cast-to τ σ))
     (sub-t 'A (πct ct*) ct*)]
    [(Check σ)
     (cond
      [(<:? τ σ) (sub-t 'B τ #f)]
      [else (type-error "Expect ~a to be a subtype of ~a" τ σ)])]
    [_ (sub-t 'C τ #f)]))

(define (coerce-check-expect ct expect τ)
  (define (sub-t who τ ct)
    (cond
     [expect
      (if (<:? τ expect)
          (or ct (Check (type-meet τ expect)))
          (type-error "(~a) Expected ~a, got ~a" who expect τ))]
     [else (or ct (Check τ))]))
  (match ct
    [(Cast σ) ;; XXX: what do we do with casts that must be heapified?
     (define ct* (cast-to τ σ))
     (sub-t 'A (πct ct*) ct*)]
    [(Check σ)
     (cond
      [(<:? τ σ) (sub-t 'B τ #f)]
      [else (type-error "Expect ~a to be a subtype of ~a" τ σ)])]
    [_ (sub-t 'C τ #f)]))

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
  (define (chk pre-τ) (check-term ct expect-overlap pre-τ))
  (match t
    [(Variant sy _ n ts) (error 'tc-term "Check variant")]
    [(Map sy _ f) (error 'tc-term "Check map")]
    [(Set sy _ s) (error 'tc-term "Check set")]
    [(External sy _ v) (error 'tc-term "Check external")]
    [_ (error 'tc-term "Unsupported term ~a" t)]))

(define (heapify-with taddr τ)
  (mk-THeap #f taddr #f τ)) ;; mm/em/tag all will be supplied by the meet.
(define (heapify-generic τ) (heapify-with generic-TAddr τ))

;; Reshaping must first reconcile with user annotations before continuing onward.
(define (*reshape expected down-construction up-construction)
  (λ (shape-τ [tag #f])
     (define non-H (resolve (type-meet expected shape-τ)))
     (cond
      [(T⊥? non-H)
       (cond
        ;; Downcast
        [(THeap? shape-τ) ;; Expect τ, have Hσ, so Hσ → τ (if σ ⊓ τ ≠ ⊥)
         (match (resolve (type-meet (heapify-generic expected) shape-τ))
           [(THeap: sy taddr tag* τ)
            (values tag*
                    (down-construction sy taddr (or tag* tag))
                    values
                    τ)]
           [_ (values #f values values T⊥)])]
        ;; Upcast
        [else ;; Have τ, may
         (match (resolve (type-meet expected (heapify-generic shape-τ)))
           [(THeap: sy taddr tag* τ)
            (values tag*
                    (up-construction sy taddr (or tag* tag))
                    (λ (τ) (mk-THeap sy taddr tag* τ))
                    τ)]
           [_ (values #f values values T⊥)])])]
      [else (values #f values values non-H)])))

(define (tc-pattern Γ Ξ pat expect)
  (define (tc Γ pat expect)
    ;; Coerce to given shape, explicitly coercing heapification
    (define (do-check expect)
      (define reshape
        (*reshape expect
                  ;; All downcasts are explicit with PDeref forms
                  (λ _ values)
                  (λ (Tsy taddr tag)
                     (λ (mkp0) (λ (ct) (mkp0 (type-error "Patterns cannot reshape into a heapified type")))))))
      (define-values (delegated? Γ* mkp op-τ op-ct)
        (match pat
          [(PAnd sy _ ps)
           (let tcp* ([Γ Γ] [ps ps] [rev-ps* '()] [expect expect])
             (match ps
               ['()
                (values #t Γ (λ (ct) (PAnd sy ct (reverse rev-ps*))) expect #f)]
               [(cons p ps)
                (define-values (Γ* p*) (tc Γ p expect))
                (define τ (πcc p*))
                (tcp* Γ* ps (cons p* rev-ps*) (type-meet τ expect))]))]

          [(PName sy _ x)
           (define ex (hash-ref Γ x #f))
           (define-values (tag W TW τ*)
             (if ex
                 (reshape ex)
                 (values #f values values expect)))
           (define err
             (and (T⊥? τ*)
                  (type-error "~a ~a: ~a (type: ~a, expected overlap ~a)"
                              "Non-linear Name pattern has"
                              "non-overlapping initial type and expected overlapping type"
                              pat ex expect)))
           (define τout (TW τ*))
           (values #t
                   (hash-set Γ x τout)
                   (W (λ (ct) (PName sy ct x)))
                   (and (not err) τout)
                   err)]

          [(PVariant sy _ n ps)
           (define len (length ps))
           ;; If we just have a single variant we expect, do a better job localizing errors.
           (define-values (tag W TW τ) (reshape (generic-variant n len)))
           (define-values (expects err mk)
             (match τ
               [(TVariant: _ n* τs tr)
                ;; Name and length match due to type-meet
                (values τs #f (λ (τs) (*TVariant #f n τs tr)))]
               ;; XXX: is this the right behavior?
               [_ (values (make-list len T⊤)
                          (type-error "Given variant ~a with arity ~a, expected overlap with ~a {~a}"
                                      n len expect τ)
                          (λ (τs) (*TVariant #f n τs #f)))]))

           (let all ([Γ Γ] [ps ps] [exs expects] [τs-rev '()] [rev-ps* '()])
             (match* (ps exs)
               [('() '())
                (define mkp0 (λ (ct) (PVariant sy ct n (reverse rev-ps*))))
                (values #t Γ (W mkp0) (and (not err) (mk (reverse τs-rev))) err)]
               [((cons p ps) (cons ex exs))
                (define-values (Γ* p*) (tc Γ p ex))
                (all Γ* ps exs (cons (πcc p*) τs-rev) (cons p* rev-ps*))]))]

          [(or (and (PMap-with sy _ k v p) (app (λ _ PMap-with) ctor))
               (and (PMap-with* sy _ k v p) (app (λ _ PMap-with*) ctor)))
           (define-values (tag W TW τ) (reshape generic-map))
           (define-values (err exk exv mk)
             (match τ
               [(TMap: _ d r ext)
                (values #f d r (λ (d r) (mk-TMap #f d r ext)))]
               [_ (values (type-error "Map pattern expects a map type, got ~a" expect)
                          T⊤ T⊤ (λ (d r) (mk-TMap #f d r (get-option 'externalize))))]))
           (define-values (Γ* k*) (tc Γ k exk))
           (define-values (Γ** v*) (tc Γ* v exv))
           (define-values (Γ*** p*) (tc Γ** p expect))
           (define mkp0 (λ (ct) (ctor sy ct k* v* p*)))
           (values #t
                   Γ***
                   (W mkp0)
                   (and (not err) (type-join (mk (πcc k*) (πcc v*)) (πcc p*)))
                   err)]

          [(or (and (PSet-with sy _ v p) (app (λ _ PSet-with) ctor))
               (and (PSet-with* sy _ v p) (app (λ _ PSet-with*) ctor)))
           (define-values (tag* W TW τ) (reshape generic-set))
           (define-values (err exv mk)
             (match τ
               [(TSet: _ v ext)
                (values #f v (λ (τ) (mk-TSet #f τ ext)))]
               [_ (values (type-error "Set pattern expects a set type, got ~a" expect)
                          T⊤ (λ (τ) (mk-TSet #f T⊤ (get-option 'externalize))))]))
           (define-values (Γ* v*) (tc Γ v exv))
           (define-values (Γ** p*) (tc Γ* p expect))
           (define mkp0 (λ (ct) (ctor sy ct v* p*)))
           (values #t
                   Γ**
                   (W mkp0)
                   (and (not err) (type-join (mk (πcc v*)) (πcc p*)))
                   err)]

          [(PDeref sy _ p taddr imp)
           ;; If implicit, then the expected type should be heapified (when checking for heapification)
           ;; If explicit, then the expected type should be an address.
           (define-values (tag* W TW τ)
             (if imp
                 (if (check-for-heapification?)
                     (reshape (heapify-with taddr T⊤))
                     (values #f values values expect))
                 (reshape taddr)))
           (define err
             (and (T⊥? τ)
                  (type-error "~a deref expected ~a, got ~a"
                              (if imp "Implicit" "Explicit")
                              (if imp "a heapified type" "an address")
                              expect)))
           (define-values (Γ* p*) (tc Γ p (if (or err (not imp)) T⊤ τ)))
           (values #t
                   Γ*
                   (λ (ct) (PDeref sy ct p* taddr imp))
                   ;; If implicit, check type is heapified version of nested pattern's type
                   (and (not err) imp (TW (πcc p*)))
                   ;; If explicit, the type is still an address
                   (or err (and (not imp) (Check τ))))]

          [(PTerm sy _ t)
           (define t* (tc-term Γ Ξ t expect))
           (values #f Γ (λ (ct) (PTerm sy ct t*)) #f (Typed-ct t*))]
          [(or (? PWild?) (? PIsExternal?) (? PIsAddr?) (? PIsType?))
           (values #f Γ (λ (ct) (replace-ct ct pat)) (πcc pat) #f)]
          [_ (error 'tc-pattern "Unsupported pattern: ~a" pat)]))

      (define (chk τ)
        (if (<:? τ expect)
            (Check τ)
            (type-error "Expected ~a, got ~a" expect τ)))
      (values Γ*
              (cond
               [delegated? (mkp (chk (or op-τ (πct op-ct))))]
               [else
                ;; XXX: I don't think this preserves the `Cast`ness of a Term.
                (mkp (chk (or op-τ (πct op-ct))))])))

    (match (Typed-ct pat)
      [(Check cτ)
       (define (bad)
         (define-values (Γ* p*) (do-check T⊤))
         (define err (format "Annotation doesn't match expectation: ~a, given ~a" expect cτ))
         (values Γ*
                 (pattern-replace-ct
                  (if (TError? (πcc p*))
                      (Check (TError (cons err (TError-msgs (πcc p*)))))
                      (Check (TError (list err))))
                  p*)))
       (cond
        ;; Good to go.
        [(<:? cτ expect) (do-check cτ)]
        ;; Expect a heapified type?
        [else (match (type-meet expect (heapify-generic T⊤))
                [(THeap: sy taddr tag τ)
                 (if (<:? cτ τ)
                     (do-check (mk-THeap sy taddr tag cτ))
                     (bad))]
                ;; Annotation is heapified, but the expected type isn't
                [_ (match (type-meet cτ (heapify-generic T⊤))
                     [(? THeap?) (bad "Expected type isn't heapified: ~a, annotation: ~a" expect cτ)]
                     [_ (bad)])])])]
      ;; A cast means check against ⊤, then see if the synthesized type
      ;; can be casted to the given type. If so (optionally) insert the cast operation.
      [(Cast cτ)
       (define-values (Γ* p*) (do-check T⊤))
       (if (castable (πcc p*) cτ)
           (values Γ*
                   (if (get-option 'check-casts)
                       (let ([ct (Check cτ)])
                        (PAnd (with-stx-stx p*)
                              ct
                              (list p* (PIsType (with-stx-stx p*) ct))))
                       (pattern-replace-ct (Cast cτ) p*)))
           (values Γ*
                   (pattern-replace-ct
                    (type-error "Unable to cast ~a to ~a" (πcc p*) cτ)
                    p*)))]
      [_ (do-check expect)]))
  (tc Γ pat expect))

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

;; Hτ → τ
(define (((down-expr-construction sy taddr tag) constr) ct)
  (define e (constr ct))
  (EStore-lookup (with-stx-stx e) ct e (get-option 'lm) taddr))

;; τ → Hτ
(define (((up-expr-construction sy taddr tag) constr) ct)
  (define e (constr ct))
  (EHeapify (with-stx-stx e) ct e taddr tag))

;; Γ : Variable names ↦ Type,
;; Ξ : metafunction names ↦ Type,
;; e : expr
;; Output is a fully annotated expression
(define ((tc-expr Γ Ξ) e [expected T⊤] #:path [path '()])
  (define (tc-expr* e expected path #:tagged [tagged #f])
    (define (do-check expected)
      (define reshape (*reshape expected
                                down-expr-construction
                                up-expr-construction))

      (define stx (with-stx-stx e))
      #|
      There are a few general cases to consider during checking.
      (1) the expression expects a certain shape.
      - heapification must be dealt with within the expression.
      [EVariant, EExtend, EAdd, ERef]
      (2) the expression delegates expectations to inner expressions
      [EMatch, EIf, ELet,EStore-lookup w/ implicit]
      (3) the expression synthesizes a type without checking expectations.
      [ECall, EMap-lookup, ESet-union, EMap-has-key?, EEmpty-Map, EEmpty-Set,
      EStore-lookup w/o implicit]
      |#
    (define-values (mk-e op-τ op-ct)
      (match e
        #|Reshaping forms (count as delegated, though are self-represented)|#
        [(EVariant sy _ n tag τs es)
         ;; Find all the n-named variants and find which makes sense.
         (define arity (length es))
         (define generic (generic-variant n arity))
         (define-values (tag* W TW eτ) (reshape generic (or tag tagged path)))
         (define (bad bad-ct)
           (values (λ (ct)
                      (EVariant sy ct n tag* τs
                                (for/list ([e (in-list es)]
                                           [i (in-naturals)])
                                  (tc-expr* e T⊤ `((,n . ,i) . ,path)))))
                   #f bad-ct))
         (cond
          [(T⊥? eτ)
           (bad (type-error "Expected a variant of arity ~a, got ~a" arity expected))]
          [else
           (define vars (lang-variants-of-arity eτ))
           (define possible-σs
             (for*/list ([τ (in-list vars)]
                         [σ (in-value (apply-annotation τs τ))]
                         #:when σ)
               σ))

           (define errors (box '()))
           ;; If we expect a type, we have a cast or explicit check, then use those rather than
           ;; an inferred variant type.
           (define (do σs tr)
             ;; expressions typecheck with a possible variant type?
             (define es*
               (for/list ([σ (in-list σs)]
                          [e (in-list es)]
                          [i (in-naturals)])
                 (tc-expr* e σ `((,n . ,i) . ,path) #:tagged (explicit-tag tag* i))))
             (define mk-e0
               (λ (ct)
                  (EVariant sy
                            (if (eq? tr 'bounded)
                                (type-error "Constructed a variant marked as bounded: ~a" n)
                                ct)
                            n (give-tag tag* path) τs es*)))
             (values (W mk-e0) (TW (mk-TVariant #f n (map πcc es*) tr))))
           (define-values (mk-e op-τ)
             (for*/fold ([mk-e #f]
                         [op-τ #f])
                 ([σ (in-list possible-σs)] #:break mk-e)
               (let/ec break
                 (match σ
                   [(TVariant: _ _ σs tr) ;; We know |σs| = |es| by possible-σs def.
                    (parameterize ([type-error-fn (λ (fmt . args)
                                                     (set-box! errors
                                                               (cons (apply format fmt args)
                                                                     (unbox errors)))
                                                     (break #f #f))])
                      (do σs tr))]
                   [_ (values #f #f)]))))
           (if mk-e
               (values mk-e op-τ #f)
               ;; Check subexpressions, but on the whole this doesn't work.
               (bad (Check (TError (cons "No variant type matched"
                                         (remove-duplicates (unbox errors)))))))])]

        [(EStore-lookup sy _ k lm imp)
         ;; k has an expected type if this is an implicit lookup
         (define k* (tc-expr* k
                              (if imp
                                  ;; implicit, so are we checking for implicits?
                                  (if (check-for-heapification?)
                                      ;; Checking, so expect something heapified.
                                      (heapify-with imp expected)
                                      expected)
                                  ;; explicit, so need an address
                                  generic-TAddr)
                              (cons 'lookup path)))
         (define ct*
           (cond
            [imp
             (cond
              [(check-for-heapification?)
               (define kτ (πcc k*))
               (if (THeap? kτ)
                   (Cast (THeap-τ kτ))
                   (type-error "Implicit lookup did heapify: ~a" kτ))]
              [else ;; Not checking for heapification, so ignore that this is a lookup form.
               (Typed-ct k*)])]
            [else (Check T⊤)])) ;; XXX: right?
         (define mk-e (λ (ct) (EStore-lookup sy ct k* lm imp)))
         ;; Delegated if implicit
         (values mk-e #f ct*)]

        [(EExtend sy _ m tag k v)
         (define-values (tag* W TW τ)
           (reshape generic-map (or tag tagged path)))
         (define-values (err d r ext)
           (match τ
             [(TMap: _ d r ext) (values #f d r ext)]
             [(or (TRUnion: _ (list (? TMap?) ...))
                  (TSUnion: _ (list (? TMap?) ...)))
              (values (type-error "Ambiguous map type ~a" τ)
                      T⊤ T⊤ 'dc)]
             [_ (values (type-error "Expected a map type, got ~a" τ)
                        T⊤ T⊤ 'dc)]))
         (define m* (tc-expr* m τ (cons 'extend-map path)))
         (define k* (tc-expr* k d (cons 'extend-key path) #:tagged (explicit-tag tag* 0)))
         (define v* (tc-expr* v r (cons 'extend-value path) #:tagged (explicit-tag tag* 1)))
         (define mk-e0 (λ (ct) (EExtend sy ct m* (give-tag tag* path) k* v*)))
         (values (W mk-e0)
                 (and (not err)
                      (TW (type-join (πcc m*) (mk-TMap #f (πcc k*) (πcc v*) ext))))
                 err)]

        [(ESet-add sy _ e tag es)
         (define-values (tag* W TW τ)
           (reshape generic-set (or tag tagged path)))
         (define-values (err v ext)
           (match τ
             [(TSet: _ v ext) (values #f v ext)]
             [(or (TRUnion: _ (list (? TSet?) ...))
                  (TSUnion: _ (list (? TSet?) ...)))
              (values (type-error "Ambiguous set type ~a" τ)
                      T⊤ 'dc)]
             [_ (values (type-error "Expected base expression to be a set, got ~a" τ) T⊤ 'dc)]))
         (define e* (tc-expr* e τ `((set-add . 0) . ,path)))
         (define es*
           (for/list ([e (in-list es)]
                      [i (in-naturals 1)])
             (tc-expr* e v `((set-add . ,i) . ,path) #:tagged (explicit-tag tag i))))
         (define mk-e (λ (ct) (ESet-add sy ct e* (give-tag tag path) es*)))
         (values (W mk-e)
                 (and (not err)
                      (TW (for/fold ([τ (πcc e*)]) ([e (in-list es*)])
                            (type-join τ (mk-TSet #f (πcc e) 'dc)))))
                 err)]
        #|Delegating forms|#
        [(ELet sy _ bus body)
         (define-values (Γ* bus*) (tc-bus Γ Ξ bus 'let-bu path))
         (define body* ((tc-expr Γ* Ξ) body expected #:path (cons 'let-body path)))
         (define mk-e (λ (ct) (ELet sy ct bus* body*)))
         (values mk-e (πcc body*) #f)]

        [(EMatch sy _ de rules)
         (define d* (tc-expr* de T⊤ (cons 'match-disc path)))
         (define-values (rules* τjoin)
           (check-and-join-rules Γ Ξ rules (πcc d*) expected 'match-rule path))
         (define mk-e (λ (ct) (EMatch sy ct d* rules*)))
         (values mk-e τjoin #f)]

        #|Oblivious forms|#
        [(ERef sy _ x)
         (define-values (tag W TW τ)
           (reshape (hash-ref Γ x (unbound-pat-var sy 'tc-expr x))))
         (define mk-e0 (λ (ct) (ERef sy ct x)))
         (values (W mk-e0) (TW τ) #f)]

        [(ECall sy _ mf τs es)
         ;; We monomorphize as well as check the function.
         (define mfτ (hash-ref Ξ mf (unbound-mf sy 'tc-expr mf)))
         ;; instantiate with all given types, error if too many
         (define inst (apply-annotation τs mfτ))
         ;; also error if too few
         (define-values (dom-σs rng)
           (match inst
             [(TArrow: _ (TVariant: _ _ σs _) rng) (values σs rng)]
             [#f
              (values (make-list
                      (length es)
                      (type-error
                       "Metafunction type must be fully instantiated, but ~a left: ~a"
                       (num-top-level-Λs inst) inst))
                     T⊤)]
             [bad (error 'ecall "Unexpected metafunction type ~a" bad)]))
         ;; Check arguments against instantiated domain types.
         (define es*
           (for/list ([se (in-list es)]
                      [σ (in-list dom-σs)]
                      [i (in-naturals)])
             (tc-expr* se σ `((call ,mf . ,i) . ,path))))
         ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
         ;; Recheck MFs for monomorphivation
         (define H (monomorphized))
         (define renamed
           (cond
            [(and H (andmap mono-type? dom-σs) (mono-type? rng))
             ;; We recheck whole mf body to get the instantiations.
             (define mf-mono (hash-ref! H mf make-hash))
             (define name* ((mono-namer) mf τs))
             (unless (hash-has-key? mf-mono name*)
               (hash-set! mf-mono name* 'gray) ;; don't diverge with self-calls
               (define opened (open-scopes-in-rules
                               (Metafunction-rules (hash-ref (mf-defs) mf))
                               (reverse τs)))
               (hash-set!
                mf-mono name*
                (Metafunction name* inst
                              (tc-rules #hash() Ξ
                                        ;; instantiate the mono-types in the mf body.
                                        opened ;; Outermost first.
                                        (TArrow-dom inst)
                                        rng
                                        `(def . ,name*)
                                        '()))))
             name*]
            [else #f]))
         (define mk-e
           (if renamed ;; monomorphized
               (λ (ct) (ECall sy ct renamed '() es*))
               (λ (ct) (ECall sy ct mf τs es*))))
         ;; End monomorphization
         ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
         (values mk-e rng #f)]

        [(EAlloc sy _ tag)
         (define mk-e0 (λ (ct) (EAlloc sy ct (give-tag tag path))))
         (values mk-e0 generic-TAddr #f)]
        [(EEmpty-Map sy _)
         (define mk-e0 (λ (ct) (EEmpty-Map sy ct)))
         (values mk-e0 generic-map #f)]

        [(EEmpty-Set sy _)
         (define mk-e0 (λ (ct) (EEmpty-Set sy ct)))
         (values mk-e0 generic-set #f)]

        [(ESet-union sy _ es)
         (define es* (for/list ([e (in-list es)]
                                [i (in-naturals)])
                       (tc-expr* e expected `((union . ,i) . ,path))))
         (define mke0
           (λ (ct) (ESet-union sy ct es*)))
         (values mke0
                 (for/fold ([τ T⊥]) ([e (in-list es*)])
                   (type-join τ (πcc e)))
                 #f)]

        [(ESet-intersection sy _ e es)
         (match-define (cons e* es*)
                       (for/list ([e (in-list (cons e es))]
                                  [i (in-naturals)])
                         (tc-expr* e generic-set `((intersection . ,i) . ,path))))
         (define mk-e (λ (ct) (ESet-intersection sy ct e* es*)))
         (values mk-e
                 (for/fold ([τ (πcc e*)])
                     ([e (in-list es*)])
                   (type-meet τ (πcc e)))
                 #f)]

        [(ESet-subtract sy _ e es) (error 'tc-expr "Todo: set-subtract")]
        [(ESet-member sy _ e v) (error 'tc-expr "Todo: set-member?")]
        [(EMap-lookup sy _ m k)
         (define m* (tc-expr* m generic-map (cons 'lookup-map path)))
         (match (resolve (type-meet (πcc m*) generic-map))
           [(TMap: _ d r _) ;; XXX: shouldn't be heapified?
            (values (λ (ct) (EMap-lookup sy ct m* (tc-expr* k d (cons 'lookup-key path))))
                    r
                    #f)]
           [τ (values (λ (ct) (EMap-lookup sy ct m* (tc-expr* k T⊤ (cons 'lookup-key path))))
                      #f
                      (type-error "Expected a map type: ~a" τ))])]
        [(EMap-has-key sy _ m k) (error 'tc-expr "Todo: map-has-key?")]
        [(EMap-remove sy _ m k) (error 'tc-expr "Todo: map-remove")]
        [(EUnquote sy _ e) (values (λ (ct) (EUnquote sy ct e)) expected #f)]
        [_ (error 'tc-expr "Unrecognized expression form: ~a" e)]))

    (define (chk τ)
      (if (<:? τ expected)
          (Check τ)
          (type-error "Expected ~a, got ~a" expected τ)))
    (mk-e (chk (or op-τ (πct op-ct)))))
   
    (match (Typed-ct e)
      [(Check cτ)
       (define (bad who [err #f])
         (define e* (do-check T⊤))
         (define err*
           (or err
               (format "~a: Annotation doesn't match expectation: ~a, given ~a" who expected cτ)))
         (expr-replace-ct
          (if (TError? (πcc e*))
              (Check (TError (cons err* (TError-msgs (πcc e*)))))
              (Check (TError (list err*))))
          e*))
       (cond
        ;; Good to go.
        [(<:? cτ expected) (do-check cτ)]
        ;; Expect a heapified type?
        [else (match (type-meet expected (heapify-generic T⊤))
                [(THeap: sy taddr tag τ)
                 (if (<:? cτ τ)
                     (do-check (mk-THeap sy taddr (or tag tagged path) cτ))
                     (bad 'heap))]
                ;; Annotation is heapified, but the expected type isn't
                [_ (match (type-meet cτ (heapify-generic T⊤))
                     [(? THeap?)
                      (bad 'ann-heap
                           (format "Expected type isn't heapified: ~a, annotation: ~a"
                                   expected cτ))]
                     [_ (bad 'non-sub)])])])]
      ;; A cast means check against ⊤, then see if the synthesized type
      ;; can be casted to the given type. If so (optionally) insert the cast operation.
      [(Cast cτ)
       ;; If the expected type is heapified, but the cast isn't, we construct in.
       (define e* (do-check T⊤))
       (define reshape (*reshape (πcc e*)
                                 down-expr-construction
                                 up-expr-construction))
       (define-values (tag* W T σ) (reshape cτ))
       (define cτ* (T cτ))
       (define we* ((W (λ (ct) (expr-replace-ct ct e*))) (Typed-ct e*)))
       (if (castable (πcc e*) cτ*)
           (if (get-option 'check-casts)
               (let ([sy (with-stx-stx e*)]
                     [x (gensym 'cast)]
                     [ct (Check cτ)])
                 (EMatch sy ct we*
                         (list (Rule sy ct
                                     (PAnd sy ct (list (PIsType sy ct) (PName sy ct x)))
                                     (ERef sy ct x) '()))))
               (expr-replace-ct (Cast cτ) we*))
           (expr-replace-ct
            (type-error "Unable to cast ~a to ~a" (πcc e*) cτ*)
            e*))]
      [_ (do-check expected)]))
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
    [(or (PAnd _ _ (? list? ps)) (PVariant _ _ _ (? list? ps)))
     (for-each report-pattern-errors ps)]
    [(or (PMap-with _ _ k v p)
         (PMap-with* _ _ k v p))
     (report-pattern-errors k)
     (report-pattern-errors v)
     (report-pattern-errors p)]
    [(or (PSet-with _ _ v p)
         (PSet-with* _ _ v p))
     (report-pattern-errors v)
     (report-pattern-errors p)]
    [(PDeref _ _ p _ _) (report-pattern-errors p)]
    [(PTerm _ _ t) (report-term-errors t)]
    [_ (void)]))

(define (report-term-errors t)
  (err-chk t)
  (match t
    [(Variant _ _ _ (? list? ts)) (for-each report-term-errors ts)]
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
    [(or (ECall _ _ _ _ (? list? es))
         (EVariant _ _ _ _ _ (? list? es))
         (ESet-union _ _ (? list? es)))
     (for-each report-expression-errors es)]
    [(EStore-lookup _ _ k _ _)
     (report-expression-errors k)]
    [(ELet _ _ (? list? bus) body)
     (for-each report-bu-errors bus)
     (report-expression-errors body)]
    [(EMatch _ _ de (? list? rules))
     (report-expression-errors de)
     (for-each report-rule-errors rules)]
    [(EExtend _ _ m _ k v)
     (report-expression-errors m)
     (report-expression-errors k)
     (report-expression-errors v)]
    [(or (ESet-intersection _ _ e (? list? es))
         (ESet-subtract _ _ e (? list? es)))
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
