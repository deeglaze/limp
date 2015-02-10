#lang racket/unit
(require racket/match
         (only-in racket/list make-list)
         "language.rkt"
         "types.rkt" "tast.rkt"
         "subtype.rkt"
         "type-cast.rkt"
         "type-lattice.rkt"
         "tc-common.rkt" "tc-sigs.rkt" "tc-term.rkt")
(import tc-expr^)
(export tc-pattern^)

(define (tc-pattern Δ Γ Ξ pat expect)
  (define (tc Δ Γ pat expect)
    ;; Coerce to given shape, explicitly coercing heapification
    (define (do-check expect)
      (define preshape
        (*reshape expect
                  ;; All downcasts are explicit with PDeref forms
                  (λ _ values)
                  (λ (Tsy taddr tag)
                     (λ (mkp0) (λ (ct) (mkp0 (type-error "Patterns cannot reshape into a heapified type")))))))
;      (trace preshape)
      (define-values (Γ* mkp op-τ op-ct)
        (match pat
          ;; A name is a wildcard that binds the term to the given name in the output environment.
          ;; If the name exists in the environment, the type must 
          [(PName sy _ x p)
           (define ex (hash-ref Γ x #f))
           (define-values (tag W TW τ*)
             (if ex
                 (preshape ex Δ Γ)
                 (values #f values values expect)))
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
           (define τsub (TW τ*))
           ;; XXX: is τ* expected or is τout expected?
           (define-values (Γ* p*) (tc Δ (hash-set Γ x τsub) p τ*))
           (define τout (TW (πcc p*)))
           (values (hash-set Γ* x τout) ;; Refine x's type after pattern matching
                   (W (λ (ct) (PName sy ct x p*)))
                   (and (not err) τout)
                   err)]

          [(PVariant sy _ n ps)
           (define len (length ps))
           ;; If we just have a single variant we expect, do a better job localizing errors.
           (define-values (tag W TW τ) (preshape (generic-variant n len) Δ Γ))
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

           (let all ([Γ Γ] [ps ps] [exs expects] [τs-rev '()] [rev-ps* '()])
             (match* (ps exs)
               [('() '())
                (define mkp0 (λ (ct) (PVariant sy ct n (reverse rev-ps*))))
                (values Γ
                        (W mkp0)
                        (and (not err) (mk (reverse τs-rev))) err)]
               [((cons p ps) (cons ex exs))
                (define-values (Γ* p*) (tc Δ Γ p ex))
                (all Γ* ps exs (cons (πcc p*) τs-rev) (cons p* rev-ps*))]
               [(_ _) (error 'blark)]))]

          [(or (and (PMap-with sy _ k v p) (app (λ _ PMap-with) ctor))
               (and (PMap-with* sy _ k v p) (app (λ _ PMap-with*) ctor)))
           (define-values (tag W TW τ) (preshape generic-map Δ Γ))
           (define-values (err exk exv mk)
             (match τ
               [(TMap: _ d r ext)
                (values #f d r (λ (d r) (mk-TMap #f d r ext)))]
               [_ (values (type-error "Map pattern expects a map type, got ~a" expect)
                          T⊤ T⊤ (λ (d r) (mk-TMap #f d r (get-option 'externalize))))]))
           (define-values (Γ* k*) (tc Δ Γ k exk))
           (define-values (Γ** v*) (tc Δ Γ* v exv))
           (define-values (Γ*** p*) (tc Δ Γ** p expect))
           (define mkp0 (λ (ct) (ctor sy ct k* v* p*)))
           (values Γ***
                   (W mkp0)
                   (and (not err) (type-join (mk (πcc k*) (πcc v*)) (πcc p*)))
                   err)]

          [(or (and (PSet-with sy _ v p) (app (λ _ PSet-with) ctor))
               (and (PSet-with* sy _ v p) (app (λ _ PSet-with*) ctor)))
           (define-values (tag* W TW τ) (preshape generic-set Δ Γ))
           (define-values (err exv mk)
             (match τ
               [(TSet: _ v ext)
                (values #f v (λ (τ) (mk-TSet #f τ ext)))]
               [_ (values (type-error "Set pattern expects a set type, got ~a" expect)
                          T⊤ (λ (τ) (mk-TSet #f T⊤ (get-option 'externalize))))]))
           (define-values (Γ* v*) (tc Δ Γ v exv))
           (define-values (Γ** p*) (tc Δ Γ* p expect))
           (define mkp0 (λ (ct) (ctor sy ct v* p*)))
           (values Γ**
                   (W mkp0)
                   (and (not err) (type-join (mk (πcc v*)) (πcc p*)))
                   err)]

          [(PDeref sy _ p taddr imp)
           ;; If implicit, then the expected type should be heapified (when checking for heapification)
           ;; If explicit, then the expected type should be an address.
           (define-values (tag* W TW τ)
             (if imp
                 (if (check-for-heapification?)
                     (preshape (heapify-with taddr T⊤) Δ Γ)
                     (values #f values values expect))
                 (preshape taddr Δ Γ)))
           (define err
             (and (T⊥? τ) ;;(uninhabitable? τ Γ)
                  (type-error "~a deref expected ~a, got ~a"
                              (if imp "Implicit" "Explicit")
                              (if imp "a heapified type" "an address")
                              expect)))
           (define-values (Γ* p*) (tc Δ Γ p (if (or err (not imp)) T⊤ τ)))
           (values Γ*
                   (λ (ct) (PDeref sy ct p* taddr imp))
                   ;; If implicit, check type is heapified version of nested pattern's type
                   (and (not err) imp (TW (πcc p*)))
                   ;; If explicit, the type is still an address
                   (or err (and (not imp) (Check τ))))]

          [(PTerm sy _ t)
           (define t* (tc-term Γ Ξ t expect))
           (values Γ (λ (ct) (PTerm sy ct t*)) #f (Typed-ct t*))]
          [(PIsType sy ct p)
           (define τ (πct ct))
           (define τ* (type-meet τ expect))
           (cond
            [(T⊥? τ*) ;;(uninhabitable? (type-meet τ expect) Γ)
             (define-values (Γ* p*) (tc Δ Γ p T⊤))
             (values Γ* (λ (ct) (PIsType sy ct p*)) #f
                     (type-error "~a have no overlap. Given ~a, expected ~a"
                                 "Casted type and expected type"
                                 τ expect))]
            [else
             (define-values (Γ* p*) (tc Δ Γ p τ*))
             (values Γ*
                     (λ (ct) (PIsType sy (Check τ*) p*))
                     τ*
                     #f)])]
          ;; A wildcard's type is whatever is expected.
          [(? PWild?) (values Γ (λ (ct) (replace-ct ct pat)) expect #f)]
          [_ (error 'tc-pattern "Unsupported pattern: ~a" pat)]))

      (define (chk τ)
        (if (<:? τ expect)
            (Check τ)
            (type-error "Pattern expected ~a, got ~a" expect τ)))
      (values Γ* (mkp (chk (or op-τ (πct op-ct))))))

    (match (Typed-ct pat)
      [(Check cτ)
       (define (bad)
         (define-values (Γ* p*) (do-check T⊤))
         (define err (type-error "Pattern annotation doesn't match expectation: ~a, given ~a" expect cτ))
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
       (define-values (Γ* p*) (do-check (type-meet expect cτ)))
       (define pτ (πcc p*))
       (if (castable pτ cτ)
           (values Γ*
                   (if (get-option 'check-casts)
                       (PIsType (with-stx-stx p*) (Check cτ) p*)
                       (pattern-replace-ct (Cast cτ) p*)))
           (values Γ*
                   (pattern-replace-ct
                    (type-error "Unable to cast ~a to ~a" (πcc p*) cτ)
                    p*)))]
      [_ (do-check expect)]))
  (tc Δ Γ pat expect))
