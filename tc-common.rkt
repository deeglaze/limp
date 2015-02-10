#lang racket/base
(provide monomorphized mf-defs mono-namer tc-context
         unbound-mf unbound-pat-var
         up-expr-construction down-expr-construction
         give-tag explicit-tag
         *reshape *in/out heapify-with heapify-generic)
(require racket/match
         (only-in racket/bool implies)
         "language.rkt" "subtype.rkt" "type-lattice.rkt"
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

(define (heapify-with taddr τ)
  (mk-THeap #f taddr #f τ)) ;; mm/em/tag all will be supplied by the meet.
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
  (λ (shape-τ Δ Γ [tag #f] #:require-<:? [no-meet? #f])
     (define shaped (resolve (type-meet expected shape-τ)))
     (cond
      [(T⊥? shaped) ;;(uninhabitable? shaped Γ)
;       (printf "Uninhabitable with expectation ~a~%" expected)
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
            [_ (values #f values values shaped)])])]
      [else
       ;; Both are heapified, but we want to get at the appropriate structure underneath.
       (match shaped
         [(THeap: sy taddr tag* τ)
          (values tag*
                  values
                  (λ (τ) (mk-THeap sy taddr (or tag* tag) τ))
                  τ)]
         [non-H (values #f values values non-H)])])))

(define (*in/out expected down-construction up-construction)
  (λ (shape-τ [tag #f] #:require-<:? [no-meet? #f])
     (define (bad) (values #f values values T⊥))
     (displayln "In/out start")
     (trace-<:?)
     (begin0
         (cond
          [(<:? shape-τ expected)
           (match shape-τ
             [(THeap: sy taddr tag* τ)
              (match-define (THeap: _ taddr* _ _)
                            (type-meet expected (heapify-generic (THeap-τ expected))))
              (define taddr** (type-meet taddr taddr*))
              (if (T⊥? taddr**)
                  (bad)
                  (values tag*
                          values
                          (λ (τ) (mk-THeap sy taddr** (or tag* tag) (THeap-τ τ)))
                          shape-τ))]
             [_ (values #f values values (resolve shape-τ))])]
          ;; Downcast
          [(THeap? shape-τ)
           (match-define (THeap: sy taddr tag* τ) shape-τ)
           (if (<:? τ expected)
               (values tag*
                       (down-construction sy taddr (or tag* tag))
                       values
                       (resolve τ))
               (bad))]
          ;; Upcast
          [(THeap? expected)
           (match-define (THeap: sy taddr tag* τ) expected)
           (if (<:? shape-τ τ)
               (values tag*
                       (up-construction sy taddr (or tag* tag))
                       (λ (τ) (mk-THeap sy taddr tag* τ))
                       (resolve shape-τ))
               (bad))]
          [else (bad)])
       (untrace-<:?)
       (displayln "In/out end"))))
