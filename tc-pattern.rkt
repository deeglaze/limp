#lang racket/unit
(require racket/match foracc
         (only-in racket/list make-list)
         "language.rkt"
         "types.rkt" "tast.rkt"
         "subtype.rkt"
         "type-cast.rkt"
         "type-lattice.rkt"
         "tc-common.rkt" "tc-ctxs.rkt" "tc-sigs.rkt" "tc-term.rkt")
(import tc-expr^)
(export tc-pattern^)

;; All downcasts are explicit with PDeref forms
(define pat-down (λ _ values))
(define pat-up (λ (Tsy taddr tag)
                  (λ (mkp0)
                     (λ (ct)
                        (mkp0 (type-error "Patterns cannot reshape into a heapified type"))))))

(define (tc-pattern Γ pat expect)
  (define (tc Γ pat expect)
    ;; Coerce to given shape, explicitly coercing heapification
    (define (do-check Γ expect)
      (define preshape (*reshape expect pat-down pat-up))
      (define-values (Γ* mkp op-τ op-ct)
        (match pat
          ;; A name is a wildcard that binds the term to the given name in the output environment.
          ;; If the name exists in the environment, the type must 
          [(PName sy _ x p)
           (define ex (ctx-lookup Γ x #:fail (λ _ #f)))
           (define-values (Δ tag W TW τ*)
             (if ex
                 (preshape ex Γ)
                 (values Γ #f values values expect)))
           (define err
             (and ex
                  ;; expected type might be uninhabitable, which is fine.
                  ;; If there is a mismatch though, error
                  (let* ([ue (and expect (T⊥? expect) ;;(uninhabitable? expect Γ)
                                  )]
                         [ut (T⊥? τ*) ;;(uninhabitable? τ* Γ)
                          ]
                         [wtf (if ue (not ut) ut)])
                   ;(when wtf (printf "Okay wtf ~a, ~a, ~a, ~a, ~a~%" wtf expect τ* ue ut))
                    wtf)
                  (type-error "~a ~a: ~a (type: ~a, expected overlap ~a)"
                              "Non-linear Name pattern has"
                              "non-overlapping initial type and expected overlapping type"
                              pat ex expect)))
           ;; XXX: is (TW τ*) expected or is τout expected?
           (define-values (Γ* p*) (tc Δ p τ*))
           (define τout (TW (πcc p*)))
           (values (if (ctx-var-in-dom? Γ* x)
                       (ctx-set-var Γ* x τout)
                       (ctx-extend-var Γ* x τout)) ;; Refine x's type after pattern matching
                   (W (λ (ct) (PName sy ct x p*)))
                   (and (not err) τout)
                   err)]

          [(PVariant sy _ n ps)
           (define len (length ps))
           ;; If we just have a single variant we expect, do a better job localizing errors.
           (define-values (Δ tag W TW τ) (preshape (generic-variant n len) Γ))
           (define-values (expects err mk)
             (match τ
               [(TVariant: _ n* τs tr)
                ;; Name and length match due to type-meet
                (values τs #f (λ (τs) (mk-TVariant #f n τs tr)))] ;; *TVariant
               ;; XXX: is this the right behavior?
               [_ (values (make-list len T⊤)
                          (type-error "Given variant ~a with arity ~a, expected overlap with ~a {~a}"
                                      n len expect τ)
                          (λ (τs) (mk-TVariant #f n τs #f)))])) ;; *TVariant

           (let all ([Γ Δ] [ps ps] [exs expects] [τs-rev '()] [rev-ps* '()])
             (match* (ps exs)
               [('() '())
                (define mkp0 (λ (ct) (PVariant sy ct n (reverse rev-ps*))))
                (values Γ
                        (W mkp0)
                        (and (not err) (mk (reverse τs-rev))) err)]
               [((cons p ps) (cons ex exs))
                (define-values (Γ* p*) (tc Γ p ex))
                (all Γ* ps exs (cons (πcc p*) τs-rev) (cons p* rev-ps*))]
               [(_ _) (error 'blark)]))]

          [(or (and (PMap-with sy _ k v p) (app (λ _ PMap-with) ctor))
               (and (PMap-with* sy _ k v p) (app (λ _ PMap-with*) ctor)))
           (define-values (Δ tag W TW τ) (preshape generic-map Γ))
           (define-values (err exk exv mk)
             (match τ
               [(TMap: _ d r ext)
                (values #f d r (λ (d r) (mk-TMap #f d r ext)))]
               [_ (values (type-error "Map pattern expects a map type, got ~a" expect)
                          T⊤ T⊤ (λ (d r) (mk-TMap #f d r (get-option 'externalize))))]))
           (define-values (Γ* k*) (tc Δ k exk))
           (define-values (Γ** v*) (tc Γ* v exv))
           (define-values (Γ*** p*) (tc Γ** p expect))
           (define mkp0 (λ (ct) (ctor sy ct k* v* p*)))
           (define-values (Θ j)
             (if err
                 (values Γ*** #f)
                 (type-join Γ*** (mk (πcc k*) (πcc v*)) (πcc p*))))
           (values Θ (W mkp0) j err)]

          [(or (and (PSet-with sy _ v p) (app (λ _ PSet-with) ctor))
               (and (PSet-with* sy _ v p) (app (λ _ PSet-with*) ctor)))
           (define-values (Δ tag* W TW τ) (preshape generic-set Γ))
           (define-values (err exv mk)
             (match τ
               [(TSet: _ v ext)
                (values Δ #f v (λ (τ) (mk-TSet #f τ ext)))]
               [_ (values Δ (type-error "Set pattern expects a set type, got ~a" expect)
                          T⊤ (λ (τ) (mk-TSet #f T⊤ (get-option 'externalize))))]))
           (define-values (Γ* v*) (tc Δ v exv))
           (define-values (Γ** p*) (tc Γ* p expect))
           (define mkp0 (λ (ct) (ctor sy ct v* p*)))
           (define-values (Θ j)
             (if err
                 (values Γ** #f)
                 (type-join Γ** (mk (πcc v*)) (πcc p*))))
           (values Θ (W mkp0) j err)]

          [(PDeref sy _ p taddr imp)
           ;; If implicit, then the expected type should be heapified (when checking for heapification)
           ;; If explicit, then the expected type should be an address.
           (define-values (Δ tag* W TW τ)
             (if imp
                 (if (check-for-heapification?)
                     (preshape (heapify-with taddr T⊤) Γ)
                     (values #f values values expect))
                 (preshape taddr Γ)))
           (define err
             (and (T⊥? τ) ;;(uninhabitable? τ Γ)
                  (type-error "~a deref expected ~a, got ~a"
                              (if imp "Implicit" "Explicit")
                              (if imp "a heapified type" "an address")
                              expect)))
           (define-values (Γ* p*) (tc Δ p (if (or err (not imp)) T⊤ τ)))
           (values Γ*
                   (λ (ct) (PDeref sy ct p* taddr imp))
                   ;; If implicit, check type is heapified version of nested pattern's type
                   (and (not err) imp (TW (πcc p*)))
                   ;; If explicit, the type is still an address
                   (or err (and (not imp) (Check τ))))]

          [(PTerm sy _ t)
           (define-values (Δ t*) (tc-term Γ t expect))
           (values Δ (λ (ct) (PTerm sy ct t*)) #f (Typed-ct t*))]
          [(PIsType sy ct p)
           (define τ (πct ct))
           (define-values (Δ τ*) (type-meet Γ τ expect))
           (cond
            [(T⊥? τ*) ;;(uninhabitable? (type-meet τ expect) Γ)
             (define-values (Γ* p*) (tc Δ p T⊤))
             (values Γ* (λ (ct) (PIsType sy ct p*)) #f
                     (type-error "~a have no overlap. Given ~a, expected ~a"
                                 "Casted type and expected type"
                                 τ expect))]
            [else
             (define-values (Γ* p*) (tc Δ p τ*))
             (values Γ*
                     (λ (ct) (PIsType sy (Check τ*) p*))
                     τ*
                     #f)])]
          ;; A wildcard's type is whatever is expected.
          [(? PWild?) (values Γ (λ (ct) (replace-ct ct pat)) expect #f)]
          [_ (error 'tc-pattern "Unsupported pattern: ~a" pat)]))

      (define τ (or op-τ (πct op-ct)))
      (cond [(<:? Γ* τ expect) => (λ (Δ) (values Δ (mkp (Check τ))))]
            [else (values Γ* (mkp (type-error "Pattern expected ~a, got ~a" expect τ)))]))

    (match (Typed-ct pat)
      [(Check cτ)
       (define (bad Γ [fmt "Pattern annotation doesn't match expectation: ~a, given ~a"])
         (define-values (Γ* p*) (do-check Γ T⊤))
         (define err (type-error fmt expect cτ))
         (values Γ*
                 (pattern-replace-ct
                  (if (TError? (πcc p*))
                      (Check (TError (cons err (TError-msgs (πcc p*)))))
                      (Check (TError (list err))))
                  p*)))
       (cond
        ;; Good to go.
        [(<:? Γ cτ expect) => (λ (Δ) (do-check Δ cτ))]
        ;; Expect a heapified type?
        [else (match/values (type-meet Γ expect (heapify-generic T⊤))
                [(Δ (THeap: sy taddr tag τ))
                 (cond
                  [(<:? Δ cτ τ) =>
                   (λ (Θ)
                      (do-check Θ (mk-THeap sy taddr tag cτ)))]
                  [else (bad Δ)])]
                ;; Annotation is heapified, but the expected type isn't
                [(Δ _) (match/values (type-meet Δ cτ (heapify-generic T⊤))
                         [(Θ (? THeap?))
                          (bad Θ "Expected type isn't heapified: ~a, annotation: ~a")]
                         [(Θ _) (bad Θ)])])])]
      ;; A cast means check against ⊤, then see if the synthesized type
      ;; can be casted to the given type. If so (optionally) insert the cast operation.
      [(Cast cτ)
       (define-values (Δ m) (type-meet Γ expect cτ))
       (define-values (Γ* p*) (do-check Δ m))
       (define pτ (πcc p*))
       (cond
        [(castable Γ* pτ cτ) =>
         (λ (Θ)
            (values Θ
                    (if (get-option 'check-casts)
                        (PIsType (with-stx-stx p*) (Check cτ) p*)
                        (pattern-replace-ct (Cast cτ) p*))))]
        [else
         (values Γ*
                 (pattern-replace-ct
                  (type-error "Unable to cast ~a to ~a" (πcc p*) cτ)
                  p*))])]
      [_ (do-check Γ expect)]))
  (tc Γ pat expect))

(define (ts-pattern Γ pat)
  (define-values (Γ* mkp op-τ op-ct)
    (match pat
      ;; A name is a wildcard that binds the term to the given name in the output environment.
      ;; If the name exists in the environment, the type must 
      [(PName sy _ x p)
       (define ex (ctx-lookup Γ x #:fail (λ _ #f)))
       (define-values (Γ* p*)
         (if ex
             (tc-pattern Γ p ex)
             (ts-pattern Γ p)))
       (define τout (πcc p*))
       (values (if (ctx-var-in-dom? Γ* x)
                   (ctx-set-var Γ* x τout)
                   (ctx-extend-var Γ* x τout)) ;; Refine x's type after pattern matching
               (λ (ct) (PName sy ct x p*))
               τout
               #f)]

      [(PVariant sy _ n ps)
       (define-values (Δ ps*)
        (for/acc ([Γ Γ] [#:type list])
                 ([p (in-list ps)])
          (ts-pattern Γ p)))
       (values Δ
               (λ (ct) (PVariant sy ct n ps*))
               (mk-TVariant #f n (map πcc ps*) #f)
               #f)]

      [(or (and (PMap-with sy _ k v p) (app (λ _ PMap-with) ctor))
           (and (PMap-with* sy _ k v p) (app (λ _ PMap-with*) ctor)))
       (define-values (Γ₁ k*) (ts-pattern Γ k))
       (define-values (Γ₂ v*) (ts-pattern Γ₁ v))
       (define-values (Γ₃ p*) (ts-pattern Γ₂ p))
       (define expect (πcc p*))
       (define preshape (*reshape expect pat-down pat-up))
       (define-values (Δ tag W TW τ) (preshape generic-map Γ))
       (define-values (err exk exv mk)
         (match τ
           [(TMap: _ d r ext)
            (values #f d r (λ (d r) (mk-TMap #f d r ext)))]
           [_ (values (type-error "Map pattern expects a map type, got ~a" expect)
                      T⊤ T⊤ (λ (d r) (mk-TMap #f d r (get-option 'externalize))))]))

       (define mkp0 (λ (ct) (ctor sy ct k* v* p*)))
       (define-values (Θ j)
         (if err
             (values Γ₃ #f)
             (type-join Γ₃ (mk (πcc k*) (πcc v*)) (πcc p*))))
       (values Θ (W mkp0) j err)]

      [(or (and (PSet-with sy _ v p) (app (λ _ PSet-with) ctor))
           (and (PSet-with* sy _ v p) (app (λ _ PSet-with*) ctor)))
       (define-values (Γ₁ v*) (ts-pattern Γ v))
       (define-values (Γ₂ p*) (ts-pattern Γ₁ p))
       (define expect (πcc p))
       (define preshape (*reshape expect pat-down pat-up))
       (define-values (Δ tag* W TW τ) (preshape generic-set Γ₂))
       (define-values (err exv mk)
         (match τ
           [(TSet: _ v ext)
            (values Δ #f v (λ (τ) (mk-TSet #f τ ext)))]
           [_ (values Δ (type-error "Set pattern expects a set type, got ~a" expect)
                      T⊤ (λ (τ) (mk-TSet #f T⊤ (get-option 'externalize))))]))
       (define mkp0 (λ (ct) (ctor sy ct v* p*)))
       (define-values (Θ j)
         (if err
             (values Δ #f)
             (type-join Δ (mk (πcc v*)) (πcc p*))))
       (values Θ (W mkp0) j err)]

      [(PDeref sy _ p taddr imp)
       (define-values (Δ p*) (ts-pattern Γ p))
       (define expect (πcc p*))
       (define preshape
         (*reshape expect pat-down pat-up))
       ;; If implicit, then the expected type should be heapified (when checking for heapification)
       ;; If explicit, then the expected type should be an address.
       (define-values (Θ tag* W TW τ)
         (if imp
             (if (check-for-heapification?)
                 (preshape (heapify-with taddr T⊤) Δ)
                 (values #f values values expect))
             (preshape taddr Γ)))
       (define err
         (and (T⊥? τ) ;;(uninhabitable? τ Γ)
              (type-error "~a deref expected ~a, got ~a"
                          (if imp "Implicit" "Explicit")
                          (if imp "a heapified type" "an address")
                          expect)))
       (values Θ
               (λ (ct) (PDeref sy ct p* taddr imp))
               ;; If implicit, check type is heapified version of nested pattern's type
               (and (not err) imp (TW (πcc p*)))
               ;; If explicit, the type is still an address
               (or err (and (not imp) (Check τ))))]

      [(PTerm sy _ t)
       (define-values (Δ t*) (ts-term Γ t))
       (values Δ (λ (ct) (PTerm sy ct t*)) #f (Typed-ct t*))]
      [(PIsType sy ct p)
       (define τ (πct ct))
       (define-values (Γ* p*) (tc-pattern Γ p τ))
       (values Γ*
               (λ (ct) (PIsType sy (Check τ) p*))
               τ
               #f)]
      ;; A wildcard's type is whatever is expected.
      [(? PWild?) (values Γ (λ (ct) (replace-ct ct pat)) T⊤ #f)]
      [_ (error 'tc-pattern "Unsupported pattern: ~a" pat)]))
  (values Γ* (mkp (if op-τ (Check op-τ) op-ct))))
