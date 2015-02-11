#lang racket/base
(provide monomorphized mf-defs mono-namer tc-context
         unbound-mf unbound-pat-var
         up-expr-construction down-expr-construction
         give-tag explicit-tag
         *reshape *in/out heapify-with heapify-generic
         apply-annotation)
(require racket/match foracc
         (only-in racket/bool implies)
         "language.rkt" "subtype.rkt" "type-lattice.rkt"
         "tc-ctxs.rkt"
         "types.rkt" "tast.rkt")
;; Map a name to a map of types to metafunction definitions.
;; This separates all metafunctions out into their appropriate monomorphizations.
;; The naming scheme for the monomorphizations is based on ???
(define monomorphized (make-parameter #f))
(define mf-defs (make-parameter #f))
(define mono-namer (make-parameter #f))

;; Delineate boundaries where typechecking is happening
(define tc-context (make-parameter '()))

(define ((unbound-mf sy who f))
  (raise-syntax-error who (format "Unbound metafunction name ~a" f) sy))
(define ((unbound-pat-var sy who x))
  (raise-syntax-error who (format "Unbound pattern variable: ~a" x) sy))

(define (heapify-with taddr τ) (mk-THeap #f taddr #f τ)) ;; mm/em/tag all will be supplied by the meet.
(define (heapify-generic τ) (heapify-with generic-TAddr τ))

;; Hτ → τ
(define (((down-expr-construction sy taddr tag) constr) ct)
  (define e (constr ct))
  (EStore-lookup (with-stx-stx e) ct e (get-option 'lm) taddr))

;; τ → Hτ
(define (((up-expr-construction sy taddr tag) constr) ct)
  (define e (constr ct))
  (EHeapify (with-stx-stx e) ct e taddr tag))

;; Rewriting for monomorphization means updating paths to be specific to the
;; given type. Thus we mark built tags with an implicit-tag construction.
;; NOTE: Any user-defined tag will be the same regardless of monomorphization!
(define (give-tag tag path)
  (if (implies tag (implicit-tag? tag))
      (implicit-tag path)
      tag))

(define (explicit-tag tag tail)
  (and tag (not (implicit-tag? tag)) (cons tail tail)))

;; Reshaping must first reconcile with user annotations before continuing onward.
(define (*reshape expected down-construction up-construction)
  (λ (shape-τ Γ [tag #f])
     (define-values (Δ m) (type-meet Γ expected shape-τ))
     (define shaped (resolve m))
     (cond
      [(T⊥? shaped) ;;(uninhabitable? shaped Γ)
;       (printf "Uninhabitable with expectation ~a~%" expected)
        (cond
         ;; Downcast
         [(THeap? shape-τ) ;; Expect τ, have Hσ, so Hσ → τ (if σ ⊓ τ ≠ ⊥)
          (define-values (Θ m) (type-meet Δ (heapify-generic expected) shape-τ))
          (match (resolve m)
            [(THeap: sy taddr tag* τ)
             (values Θ tag*
                     (down-construction sy taddr (or tag* tag))
                     values
                     τ)]
            [_ (values Γ #f values values T⊥)])]
         ;; Upcast
         [else ;; Have τ, may
          (define-values (Θ m) (type-meet Δ expected (heapify-generic shape-τ)))
          (match (resolve m)
            [(THeap: sy taddr tag* τ)
             (values Θ tag*
                     (up-construction sy taddr (or tag* tag))
                     (λ (τ) (mk-THeap sy taddr tag* τ))
                     τ)]
            [_ (values Δ #f values values shaped)])])]
      [else
       ;; Both are heapified, but we want to get at the appropriate structure underneath.
       (match shaped
         [(THeap: sy taddr tag* τ)
          (values Δ
                  tag*
                  values
                  (λ (τ) (mk-THeap sy taddr (or tag* tag) τ))
                  τ)]
         [non-H (values Δ #f values values non-H)])])))

(define (*in/out expected down-construction up-construction)
  (λ (shape-τ Γ [tag #f])
     (define (bad Γ) (values Γ #f values values T⊥))
     (cond
      [(<:? Γ shape-τ expected) =>
       (λ (Δ)
          (match shape-τ
            [(THeap: sy taddr tag* τ)
             (match-define-values
              (Θ (THeap: _ taddr* _ _))
              (type-meet Δ expected (heapify-generic (THeap-τ expected))))
             (define-values (Γ* taddr**) (type-meet Θ taddr taddr*))
             (if (T⊥? taddr**)
                 (bad Γ*)
                 (values Γ* tag*
                         values
                         (λ (τ) (mk-THeap sy taddr** (or tag* tag) (THeap-τ τ)))
                         shape-τ))]
            [_ (values Γ #f values values (resolve shape-τ))]))]
      ;; Downcast
      [(THeap? shape-τ)
       (match-define (THeap: sy taddr tag* τ) shape-τ)
       (cond
        [(<:? Γ τ expected) =>
         (λ (Δ)
            (values Δ tag*
                    (down-construction sy taddr (or tag* tag))
                    values
                    (resolve τ)))]
        [else (bad Γ)])]
      ;; Upcast
      [(THeap? expected)
       (match-define (THeap: sy taddr tag* τ) expected)
       (cond
        [(<:? Γ shape-τ τ) =>
         (λ (Δ)
            (values Δ tag*
                    (up-construction sy taddr (or tag* tag))
                    (λ (τ) (mk-THeap sy taddr tag* τ))
                    (resolve shape-τ)))]
        [else (bad Γ)])]
      [else (bad Γ)])))

;; Create unification variables for implicit types.
;; If over- or under-instantiated, return #f.
(define (apply-annotation Γ τs τ)
  (define-values (Δ τs*)
    (if (list? τs)
        (for/acc ([Γ Γ] [#:type list])
                 ([τ (in-list τs)])
          (cond [τ (values Γ τ)]
                [else
                 (define α̂ (gensym 'α))
                 (values (ctx-extend-uvar Γ α̂) (mk-TFree #f α̂))]))
        (for/acc ([Γ Γ] [#:type list])
                 ([dummy (in-range (num-top-level-Λs τ))])
          (define α̂ (gensym 'α))
          (values (ctx-extend-uvar Γ α̂) (mk-TFree #f α̂)))))
  (define possible-out (repeat-inst τ τs*))
  (cond
   [(or (not possible-out) (TΛ? (resolve possible-out)))
    (values Δ #f #f)] ;; should be fully instantiated
   [else
    (values Δ τs* possible-out)]))
