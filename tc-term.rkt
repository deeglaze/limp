#lang racket/base
(provide tc-term ts-term)
(require racket/match
         "types.rkt" "tast.rkt" "subtype.rkt"
         "type-lattice.rkt" "type-cast.rkt" "tc-sigs.rkt")

(define (check-term Γ ct expect τ)
  (define (sub-t who τ ct)
    (cond
     [expect
      (cond [(<:? Γ τ expect) (λ (Δ) (values Δ (or ct (Check (type-meet τ expect)))))]
            [else (type-error "(~a) Expected ~a, got ~a" who expect τ)])]
     [else (values Γ (or ct (Check τ)))]))
  (match ct
    [(Cast σ)
     (define ct* (cast-to τ σ))
     (sub-t 'A (πct ct*) ct*)]
    [(Check σ)
     (cond
      [(<:? τ σ) (sub-t 'B τ #f)]
      [else (type-error "Expect ~a to be a subtype of ~a" τ σ)])]
    [_ (sub-t 'C τ #f)]))

(define (tc-term Γ t expect-overlap)
  (define ct (Typed-ct t))
  (define (chk pre-τ) (check-term Γ ct expect-overlap pre-τ))
  (match t
    [(Variant sy _ n ts) (error 'tc-term "Check variant")]
    [(Map sy _ f) (error 'tc-term "Check map")]
    [(Set sy _ s) (error 'tc-term "Check set")]
    [(External sy _ v) (error 'tc-term "Check external")]
    [_ (error 'tc-term "Unsupported term ~a" t)]))

(define (ts-term Γ t)
  (match t
    [(Variant sy _ n ts) (error 'ts-term "Synth variant")]
    [(Map sy _ f) (error 'ts-term "Synth map")]
    [(Set sy _ s) (error 'ts-term "Synth set")]
    [(External sy _ v) (error 'ts-term "Synth external")]
    [_ (error 'ts-term "Unsupported term ~a" t)]))
