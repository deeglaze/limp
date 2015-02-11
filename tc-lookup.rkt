#lang racket/unit
(require racket/match
         "language.rkt"
         "tc-common.rkt" "tc-sigs.rkt"
         "type-lattice.rkt" "tast.rkt" "types.rkt")
(import tc-expr^)
(export tc-lookup^)

(define (tc-lookup Γ Ξ e expected path tagged)
  (match-define (EStore-lookup sy _ k lm imp) e)
  ;; k has an expected type if this is an implicit lookup
  (define-values (Δ k*)
    (tc-expr Γ Ξ k
             (if imp
                 ;; implicit, so are we checking for implicits?
                 (if (check-for-heapification?)
                     ;; Checking, so expect something heapified.
                     (heapify-with imp expected)
                     expected)
                 ;; explicit, so need an address
                 generic-TAddr)
             (cons 'lookup path) #f))
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
  (values Δ mk-e #f ct*))

(define (ts-lookup Γ Ξ e path tagged)
  (match-define (EStore-lookup sy _ k lm imp) e)
  ;; k has an expected type if this is an implicit lookup
  (define-values (Δ k*) (ts-expr Γ Ξ k (cons 'lookup path) #f))
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
  (values Δ mk-e #f ct*))
