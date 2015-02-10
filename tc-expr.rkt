#lang racket/unit
(require (for-syntax syntax/parse racket/syntax racket/base)
         (only-in racket/bool implies)
         racket/list racket/match
         racket/pretty
         racket/set
         racket/string racket/trace
         (only-in "alloc-rules.rkt" normalize-taddr)
         "common.rkt" "language.rkt" "tast.rkt"
         "subtype.rkt"
         "types.rkt"
         "type-cast.rkt"
         "type-lattice.rkt"
         "tc-common.rkt"
         "tc-sigs.rkt")
(import tc-pattern^ tc-rules^ tc-bu^
        ;; expr forms
        tc-set^ tc-map^ tc-variant^)
(export tc-expr^)

;; Γ : Variable names ↦ Type,
;; Ξ : metafunction names ↦ Type,
;; e : expr
;; Output is a fully annotated expression
(define (tc-expr Δ Γ Ξ e expected path tagged)
  (define (tc-expr* e expected path)
    (define (do-check expected)
      (define in/out (*in/out expected
                              down-expr-construction
                              up-expr-construction))
;      (trace in/out reshape)

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
        [(? EVariant? e) (tc-variant Δ Γ Ξ e expected path tagged)]
        [(? Map-Expression? e) (tc-map Δ Γ Ξ e expected path tagged)]
        [(? Set-Expression? e) (tc-set Δ Γ Ξ e expected path tagged)]

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

        [(EHeapify sy _ e taddr tag)
         (cond
          [(check-for-heapification?)
           (define-values (tag* W TW τ)
             (in/out (heapify-with taddr T⊤) (or tag tagged path)))
           (define e* (tc-expr* e τ))
           (define mke (λ (ct) (EHeapify sy ct e* taddr tag)))
           (define eτ (πcc e*))
           (values (W mke)
                   (if (TError? eτ)
                       (Check T⊥)
                       (TW eτ))
                   #f)]
          [else
           (define e* (tc-expr* e expected))
           (define mke (λ (ct) (EHeapify sy ct e* taddr tag)))
           (values mke (πcc e*) #f)])]

        #|Delegating forms|#
        [(ELet sy _ bus body)
         (define-values (Γ* bus*) (tc-bus Δ Γ Ξ bus 'let-bu path))
         (define body* (tc-expr Δ Γ* Ξ body expected (cons 'let-body path) #f))
         (define mk-e (λ (ct) (ELet sy ct bus* body*)))
         (values mk-e (πcc body*) #f)]

        [(EMatch sy _ de rules)
         (define d* (tc-expr* de T⊤ (cons 'match-disc path)))
         (define-values (rules* τjoin)
           (check-and-join-rules Δ Γ Ξ rules (πcc d*) expected 'match-rule path))
         (define mk-e (λ (ct) (EMatch sy ct d* rules*)))
         (values mk-e τjoin #f)]

        [(EIf sy _ g t e)
         (define g* (tc-expr* g T⊤ (cons 'if-guard path)))
         (define t* (tc-expr* t expected (cons 'if-then path)))
         (define e* (tc-expr* e expected (cons 'if-else path)))
         (define mk-if (λ (ct) (EIf sy ct g* t* e*)))
         (values mk-if (type-join (πcc t*) (πcc e*)) #f)]

        #|Oblivious forms|#
        [(ERef sy _ x)
         (define xτ (hash-ref Γ x (unbound-pat-var sy 'tc-expr x)))
         (define-values (tag W TW τ) (in/out xτ))
         (define mk-e0 (λ (ct) (ERef sy ct x)))
         (cond [(T⊥? τ) ;;(uninhabitable? τ Γ)
                (values (W mk-e0) #f (type-error "Ref expected ~a, got ~a" expected xτ))]
               [else
                (values (W mk-e0) (TW τ) #f)])]

        [(ECall sy _ mf τs es)
         ;; We monomorphize as well as check the function.
         (define mfτ (hash-ref Ξ mf (unbound-mf sy 'tc-expr mf)))
         ;; instantiate with all given types, error if too many
         (define-values (τs* inst) (apply-annotation τs mfτ))
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
         ;; Recheck MFs for monomorphization
         (define H (monomorphized))
         (define renamed
           (cond
            [(and H (andmap mono-type? dom-σs) (mono-type? rng))
             ;; We recheck whole mf body to get the instantiations.
             (define mf-mono (hash-ref! H mf make-hash))
             (define name* ((mono-namer) mf τs*))
             (printf "Mono name ~a~%" name*)
             (unless (hash-has-key? mf-mono name*)
               (hash-set! mf-mono name* 'gray) ;; don't diverge with self-calls
               (define old-mf (hash-ref (mf-defs) mf))
               (unless (Metafunction? old-mf)
                 (error 'tc-metafunction "Not a metafunction: ~a" mf))
               (define opened (open-scopes-in-rules
                               (Metafunction-rules old-mf)
                               (reverse τs*)))
               (printf "Opened at ~a~%" τs*)
               (hash-set!
                mf-mono name*
                (Metafunction name* inst
                              (tc-rules ⊥eq #hash() Ξ
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
               (λ (ct) (ECall sy ct mf τs* es*))))
         ;; End monomorphization
         ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
         (values mk-e rng #f)]

        [(EAlloc sy _ tag)
         (define mk-e0 (λ (ct) (EAlloc sy ct (give-tag tag path))))
         (values mk-e0 generic-TAddr #f)]

        [(EUnquote sy _ e) (values (λ (ct) (EUnquote sy ct e)) expected #f)]
        [(EExternal sy ct v) (values (λ (ct) (EExternal sy ct v)) (πct ct) #f)]
        [_ (error 'tc-expr "Unrecognized expression form: ~a" e)]))

    (define (chk τ)
      (if (<:? τ expected)
          (Check τ)
          (begin ;(printf "FSCK: ~a ~a~%" expected τ)
           (type-error "chk: Expression expected ~a, got ~a" expected τ))))
    (mk-e (chk (or op-τ (πct op-ct)))))
   
    (match (Typed-ct e)
      [(Check cτ)
       (define (bad who [err #f])
         (define e* (do-check T⊤))
         (define err*
           (or err
               (format "~a: Expression annotation doesn't match expectation: ~a, given ~a" who expected cτ)))
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
       (define in/out (*in/out (πcc e*)
                                down-expr-construction
                                up-expr-construction))
       (define-values (tag* W T σ) (in/out cτ))
       (define cτ* (T cτ))
       (define we* ((W (λ (ct) (expr-replace-ct ct e*))) (Typed-ct e*)))
       (define eτ (πcc e*))
       (define (bad)
         (expr-replace-ct (type-error "Unable to cast ~a to ~a" (πcc e*) cτ*) e*))
       (cond [(T⊥? σ) ;;(uninhabitable? σ Γ)
              (bad)
              ]
             [(castable eτ cτ*)
              (if (get-option 'check-casts)
                  (let ([sy (with-stx-stx e*)]
                        [x (gensym 'cast)]
                        [ct (Check cτ)])
                    (EMatch sy ct we*
                            (list (Rule sy x ;; name of rule same as the generated binder
                                        (PIsType sy ct (PName sy ct x (PWild sy ct)))
                                        (ERef sy ct x) '()))))
                  (expr-replace-ct (Cast cτ) we*))]
             [else (bad)])]
      [_ (do-check expected)]))
;  (trace tc-expr*)
  (tc-expr* e expected path))
