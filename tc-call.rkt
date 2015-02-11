#lang racket/unit
(require racket/match foracc
         (only-in racket/list make-list)
         "common.rkt" "language.rkt"
         "tc-common.rkt" "tc-sigs.rkt"
         "tc-ctxs.rkt"
         "type-lattice.rkt" "tast.rkt" "types.rkt")
(import tc-expr^ tc-rules^)
(export tc-call^)
(define (ts-call Γ Ξ e path tagged)
  (match-define (ECall sy _ mf τs es) e)
  ;; We monomorphize as well as check the function.
  (define mfτ (hash-ref Ξ mf (unbound-mf sy 'tc-expr mf)))
  ;; instantiate with all given types, error if too many
  (define-values (Δ τs* inst) (apply-annotation Γ τs mfτ))
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
  (define-values (Θ es*)
    (for/acc ([Δ Δ] [#:type list])
             ([se (in-list es)]
              [σ (in-list dom-σs)]
              [i (in-naturals)])
     (tc-expr Δ Ξ se σ `((call ,mf . ,i) . ,path) #f)))
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
        (define-values (Δ rules*)
          (tc-rules (empty-ctx) Ξ
                    ;; instantiate the mono-types in the mf body.
                    opened ;; Outermost first.
                    (TArrow-dom inst)
                    rng
                    `(def . ,name*)
                    '()))
        (hash-set! mf-mono name* (Metafunction name* inst rules*)))
      name*]
     [else #f]))
  (define mk-e
    (if renamed ;; monomorphized
        (λ (ct) (ECall sy ct renamed '() es*))
        (λ (ct) (ECall sy ct mf τs* es*))))
  ;; End monomorphization
  ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (values Θ mk-e rng #f))
