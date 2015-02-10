#lang racket/unit
(require racket/match "types.rkt" "tast.rkt" "type-lattice.rkt" "tc-sigs.rkt")
(import tc-expr^ tc-pattern^ tc-bu^)
(export tc-rules^)

(define (check-and-join-rules Δ Γ Ξ rules expect-discr expected head path)
  (let check ([rules rules] [τ T⊥] [i 0] [rev-rules* '()])
   (match rules
     ['() (values (reverse rev-rules*) τ)]
     [(cons rule rules)
      (define rule* (tc-rule Δ Γ Ξ rule expect-discr expected (cons head i) path))
      (check rules
             (type-join τ (πcc (Rule-rhs rule*)))
             (add1 i)
             (cons rule* rev-rules*))]
     [_ (error 'cajr)])))

(define (tc-rule Δ Γ Ξ rule expect-discr expected head path)
  (match-define (Rule sy name lhs rhs bus) rule)
  (define-values (Γ* lhs*) (tc-pattern Δ Γ Ξ lhs expect-discr))
  (define path* (cons (or name head) path))
  (define-values (Γ** bus*) (tc-bus Δ Γ* Ξ bus 'rule-bu path*))
  (define rhs* (tc-expr Δ Γ** Ξ rhs expected path* #f))
  (Rule sy name lhs* rhs* bus*))

(define (tc-rules Δ Γ Ξ rules expect-discr expected head path)
  (for/list ([rule (in-list rules)]
             [i (in-naturals)])
;    (printf "Rule ~a: ~a~%" i expected)
    (tc-rule Δ Γ Ξ rule expect-discr expected (cons head i) path)))
