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
         "tc-ctxs.rkt"
         "type-cast.rkt"
         "type-lattice.rkt"
         "tc-common.rkt"
         "tc-sigs.rkt")
(import tc-pattern^ tc-rules^ ts-bus^ tc-call^ tc-lookup^
        ;; expr forms
        tc-set^ tc-map^ tc-variant^)
(export tc-expr^)

;; Type-check expression
(define (tc-expr Γ Ξ e expected path tagged)
  (define in/out (*in/out expected
                          down-expr-construction
                          up-expr-construction))
  (define-values (Δ mk-e op-τ op-ct)
    (match e
      #|Reshaping forms (count as delegated, though are self-represented)|#
      [(? EVariant? e) (tc-variant Γ Ξ e expected path tagged)]
      [(? Map-Expression? e) (tc-map Γ Ξ e expected path tagged)]
      [(? Set-Expression? e) (tc-set Γ Ξ e expected path tagged)]

      [(? EStore-lookup?) (tc-lookup Γ Ξ e expected path tagged)]

      [(EHeapify sy _ e taddr tag)
       (cond
        [(check-for-heapification?)
         (define-values (Δ tag* W TW τ)
           (in/out (heapify-with taddr T⊤) Γ (or tag tagged path)))
         (define-values (Θ e*) (tc-expr Δ Ξ e τ (cons 'heapify path) #f))
         (define mke (λ (ct) (EHeapify sy ct e* taddr tag)))
         (define eτ (πcc e*))
         (values Θ (W mke)
                 (if (TError? eτ)
                     (Check T⊥)
                     (TW eτ))
                 #f)]
        [else
         (define-values (Δ e*) (tc-expr Γ Ξ e expected path tagged))
         (define mke (λ (ct) (EHeapify sy ct e* taddr tag)))
         (values Δ mke (πcc e*) #f)])]

      #|Delegating forms|#
      [(ELet sy _ bus body)
       (define-values (Γ* bus*) (ts-bus Γ Ξ bus 'let-bu path))
       (define-values (Δ body*) (tc-expr Γ* Ξ body expected (cons 'let-body path) #f))
       (define mk-e (λ (ct) (ELet sy ct bus* body*)))
       (values Δ mk-e (πcc body*) #f)]

      [(EMatch sy _ de rules)
       (define-values (Δ d*) (ts-expr Γ Ξ de (cons 'match-disc path) #f))
       (define-values (Θ rules*)
         (tc-rules Δ Ξ rules (πcc d*) expected 'match-rule path))
       (define mk-e (λ (ct) (EMatch sy ct d* rules*)))
       (values Θ mk-e expected #f)]

      [(EIf sy _ g t e)
       (define-values (Γ₁ g*) (ts-expr Γ Ξ g (cons 'if-guard path) #f))
       (define-values (Γ₂ t*) (tc-expr Γ₁ Ξ t expected (cons 'if-then path) #f))
       (define-values (Γ₃ e*) (tc-expr Γ₂ Ξ e expected (cons 'if-else path) #f))
       (define mk-if (λ (ct) (EIf sy ct g* t* e*)))
       (values Γ₃ mk-if (type-join (πcc t*) (πcc e*)) #f)]

      #|Oblivious forms|#
      [(ERef sy _ x)
       (define xτ (ctx-lookup Γ x #:fail (unbound-pat-var sy 'tc-expr x)))
       (define-values (Δ tag W TW τ) (in/out xτ Γ))
       (define mk-e0 (λ (ct) (ERef sy ct x)))
       (cond [(T⊥? τ) ;;(uninhabitable? τ Γ)
              (values Δ (W mk-e0) #f (type-error "Ref expected ~a, got ~a" expected xτ))]
             [else
              (values Δ (W mk-e0) (TW τ) #f)])]

      [(? ECall? e) (ts-call Γ Ξ e path tagged)]

      [(EAlloc sy _ tag)
       (define mk-e0 (λ (ct) (EAlloc sy ct (give-tag tag path))))
       (values Γ mk-e0 generic-TAddr #f)]

      [(EUnquote sy _ e) (values Γ (λ (ct) (EUnquote sy ct e)) expected #f)]
      [(EExternal sy ct v) (values Γ (λ (ct) (EExternal sy ct v)) (πct ct) #f)]
      [_ (error 'tc-expr "Unrecognized expression form: ~a" e)]))
  ;; Check versus expectation
  (values Δ (mk-e (if op-τ (Check op-τ) op-ct))))

;; Type-synthesize expression
(define (ts-expr Γ Ξ e path tagged)
  (define-values (Δ mk-e op-τ op-ct)
   (match e
     #|Reshaping forms (count as delegated, though are self-represented)|#
     [(? EVariant? e) (ts-variant Γ Ξ e path tagged)]
     [(? Map-Expression? e) (ts-map Γ Ξ e path tagged)]
     [(? Set-Expression? e) (ts-set Γ Ξ e path tagged)]

     [(? EStore-lookup?) (ts-lookup Γ Ξ e path tagged)]

     [(EHeapify sy _ e taddr tag)
      (cond
       [(check-for-heapification?)
        (define-values (Δ e*) (ts-expr Γ e (cons 'heapify path) #f))
        (define mke (λ (ct) (EHeapify sy ct e* taddr tag)))
        (define eτ (πcc e*))
        (values Δ mke
                (if (TError? eτ)
                    (Check T⊥)
                    eτ)
                #f)]
       [else
        (define-values (Δ e*) (ts-expr Γ Ξ e (cons 'heapify path) tagged))
        (define mke (λ (ct) (EHeapify sy ct e* taddr tag)))
        (values Δ mke (πcc e*) #f)])]

     #|Delegating forms|#
     [(ELet sy _ bus body)
      (define-values (Γ* bus*) (ts-bus Γ Ξ bus 'let-bu path))
      (define-values (Δ body*) (ts-expr Γ* Ξ body (cons 'let-body path) #f))
      (define mk-e (λ (ct) (ELet sy ct bus* body*)))
      (values Δ mk-e (πcc body*) #f)]

     [(EMatch sy _ de rules)
      (define-values (Δ d*) (ts-expr Γ Ξ de (cons 'match-disc path) tagged))
      (define-values (Θ rules* τjoin) (ts-rules Δ Ξ rules (πcc d*) 'match-rule path))
      (define mk-e (λ (ct) (EMatch sy ct d* rules*)))
      (values Θ mk-e τjoin #f)]

     [(EIf sy _ g t e)
      (define-values (Γ₁ g*) (ts-expr Γ g (cons 'if-guard path) #f))
      (define-values (Γ₂ t*) (ts-expr Γ₁ t (cons 'if-then path) #f))
      (define-values (Γ₃ e*) (ts-expr Γ₂ e (cons 'if-else path) #f))
      (define mk-if (λ (ct) (EIf sy ct g* t* e*)))
      (values Γ₃ mk-if (type-join (πcc t*) (πcc e*)) #f)]

     #|Oblivious forms|#
     [(ERef sy _ x)
      (define xτ (ctx-lookup Γ x #:fail (unbound-pat-var sy 'ts-expr x)))
      (define mk-e0 (λ (ct) (ERef sy ct x)))
      (values Γ mk-e0 xτ #f)]

     [(? ECall? e)
      (ts-call Γ Ξ e path tagged)]

     [(EAlloc sy _ tag)
      (define mk-e0 (λ (ct) (EAlloc sy ct (give-tag tag path))))
      (values Γ mk-e0 generic-TAddr #f)]

     [(EUnquote sy _ e) (values Γ (λ (ct) (EUnquote sy ct e)) T⊤ #f)]
     [(EExternal sy ct v) (values Γ (λ (ct) (EExternal sy ct v)) (πct ct) #f)]
     [_ (error 'ts-expr "Unrecognized expression form: ~a" e)]))
  (values Δ (mk-e (if op-τ (Check op-τ) op-ct))))

;; Γ : Variable names ↦ Type,
;; Ξ : metafunction names ↦ Type,
;; e : expr
;; Output is a fully annotated expression
#;
(define (tc-expr Γ Ξ e expected path tagged)
  (define (tc-expr* Γ e expected path)
    (define (do-check Γ expected)
      (define in/out (*in/out expected
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
    ;; Synthesized expression and environment.
    (values Δ (mk-e (if op-τ (Check op-τ) op-ct)))
    #;
    (define τ (or op-τ (πct op-ct)))
    #;
    (cond
     [(<:? Δ τ expected) => (λ (Θ) (values Θ (mk-e (Check τ))))]
     [else (values Δ (mk-e (type-error "chk: Expression expected ~a, got ~a" expected τ)))]))
   
    (match (Typed-ct e)
      [(Check cτ)
       (define (bad Γ who [fmt "~a: Expression annotation doesn't match expectation: ~a, given ~a"])
         (define-values (Δ e*) (do-check Γ T⊤))
         (define err* (format fmt who expected cτ))
         (values Δ
                 (expr-replace-ct
                  (if (TError? (πcc e*))
                      (Check (TError (cons err* (TError-msgs (πcc e*)))))
                      (Check (TError (list err*))))
                  e*)))
       ;; Synthesize a type first
       (define-values (Δ e*) (do-check Γ T⊤))
       (cond
        ;; Good to go.
        [(<:? Γ cτ expected) => (λ (Δ) (do-check Δ cτ))]
        ;; Expect a heapified type?
        [else (match/values (type-meet Γ expected (heapify-generic T⊤))
                [(Δ (THeap: sy taddr tag τ))
                 (cond
                  [(<:? Δ cτ τ) =>
                   (λ (Θ)
                      (do-check Θ (mk-THeap sy taddr (or tag tagged path) cτ)))]
                  [else (bad Δ 'heap)])]
                ;; Annotation is heapified, but the expected type isn't
                [(Δ _)
                 (match/values (type-meet Δ cτ (heapify-generic T⊤))
                   [(Θ (? THeap?))
                    (bad Θ 'ann-heap
                         "~a: Expected type isn't heapified: ~a, annotation: ~a")]
                   [(Θ _) (bad Θ 'non-sub)])])])]
      ;; A cast means check against ⊤, then see if the synthesized type
      ;; can be casted to the given type. If so (optionally) insert the cast operation.
      [(Cast cτ)
       ;; If the expected type is heapified, but the cast isn't, we construct in.
       (define-values (Δ e*) (do-check Γ T⊤))
       (define in/out (*in/out (πcc e*)
                                down-expr-construction
                                up-expr-construction))
       (define-values (Θ tag* W T σ) (in/out cτ Δ))
       (define cτ* (T cτ))
       (define we* ((W (λ (ct) (expr-replace-ct ct e*))) (Typed-ct e*)))
       (define eτ (πcc e*))
       (define (bad)
         (expr-replace-ct (type-error "Unable to cast ~a to ~a" (πcc e*) cτ*) e*))
       (cond [(T⊥? σ) ;;(uninhabitable? σ Γ)
              (values Θ (bad))]
             [(castable Θ eτ cτ*) =>
              (λ (Γ)
                 (values Γ
                         (if (get-option 'check-casts)
                             (let ([sy (with-stx-stx e*)]
                                   [x (gensym 'cast)]
                                   [ct (Check cτ)])
                               (EMatch sy ct we*
                                       (list (Rule sy x ;; name of rule same as the generated binder
                                                   (PIsType sy ct (PName sy ct x (PWild sy ct)))
                                                   (ERef sy ct x) '()))))
                             (expr-replace-ct (Cast cτ) we*))))]
             [else (values Θ (bad))])]
      [_ (do-check Γ expected)]))
  (trace tc-expr*)
  (tc-expr* Γ e expected path))
