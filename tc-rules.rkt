#lang racket/unit
(require racket/match
         foracc
         "types.rkt" "tast.rkt" "type-lattice.rkt" "tc-ctxs.rkt" "tc-sigs.rkt")
(import tc-expr^ tc-pattern^ ts-bus^)
(export tc-rules^)

(define (check-and-join-rules Γ Ξ rules expect-discr expected head path)
  (let check ([Γ Γ] [rules rules] [τ T⊥] [i 0] [rev-rules* '()])
   (match rules
     ['() (values Γ (reverse rev-rules*) τ)]
     [(cons rule rules)
      (define-values (Δ rule*) (tc-rule Γ Ξ rule expect-discr expected (cons head i) path))
      (define-values (Θ j) (type-join Δ τ (πcc (Rule-rhs rule*))))
      (check Θ rules j (add1 i) (cons rule* rev-rules*))]
     [_ (error 'cajr)])))

(define (tc-rule Γ Ξ rule expect-discr expected head path)
  (match-define (Rule sy name lhs rhs bus) rule)
  (define-values (Γ* lhs*) (tc-pattern Γ lhs expect-discr))
  (define path* (cons (or name head) path))
  (define-values (Γ** bus*) (ts-bus Γ* Ξ bus 'rule-bu path*))
  (define-values (Δ rhs*) (tc-expr Γ** Ξ rhs expected path* #f))
  (values (ctx-drop-after Δ (hash-count Γ))
          (Rule sy name lhs* rhs* bus*)))

(define (ts-rule Γ Ξ rule head path)
  (match-define (Rule sy name lhs rhs bus) rule)
  (define-values (Γ* lhs*) (ts-pattern Γ Ξ lhs))
  (define path* (cons (or name head) path))
  (define-values (Γ** bus*) (ts-bus Γ* Ξ bus 'rule-bu path*))
  (define-values (Δ rhs*) (ts-expr Γ** Ξ rhs path* #f))
  (values (ctx-drop-after Δ (hash-count Γ))
          (Rule sy name lhs* rhs* bus*)))

(define (tc-rules Γ Ξ rules expect-discr expected head path)
  (for/acc ([Γ Γ] [#:type list]) ([rule (in-list rules)]
                                  [i (in-naturals)])
           ;;    (printf "Rule ~a: ~a~%" i expected)
           (tc-rule Γ Ξ rule expect-discr expected (cons head i) path)))

(define (ts-rules Γ Ξ rules head path)
  (for/acc ([Γ Γ] [#:type list]) ([rule (in-list rules)]
                                  [i (in-naturals)])
           (ts-rule Γ Ξ rule (cons head i) path)))
