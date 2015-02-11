#lang racket/unit
(require racket/match
         "types.rkt" "tast.rkt" "tc-sigs.rkt")
(import tc-pattern^ tc-expr^)
(export ts-bus^)

(define (ts-bu Γ Ξ bu path)
   (match bu
    [(Update sy k v)
     (define k* (ts-expr Γ Ξ k (cons 'update-key path) #f))
     ;; We expect k to be a TAddr type, but which kind doesn't matter
     (cond
      [(TAddr? (πcc k*))
       (define-values (Δ e*) (ts-expr Γ Ξ v (cons 'update-value path) #f))
       (values Δ (Update sy k* e*))]
      [else
       (define-values (Δ e*) (ts-expr Γ Ξ v (cons 'update-value path) #f))
       (values Δ
               (Update sy
                       (replace-ct
                        (type-error "Expect store lookup key to have an address type, got ~a"
                                    (πcc k*))
                        k*)
                       e*))])]
    [(Where sy pat e)
     ;; We expect e and pat to have overlapping types,
     ;; but one's type doesn't drive the other's checking.
     (define-values (Δ e*) (ts-expr Γ Ξ e (cons 'where-rhs path) #f))
     (define-values (Θ pat*) (tc-pattern Δ pat (πcc e*)))
     (values Θ (Where sy pat* e*))]
    [(When sy e)
     (define-values (Δ e*) (ts-expr Γ Ξ e (cons 'when-expr path) #f))
     (values Δ (When sy e*))]
    [(Unless sy e)
     (define-values (Δ e*) (ts-expr Γ Ξ e (cons 'unless-expr path) #f))
     (values Δ (Unless sy e*))]
    [_ (error 'ts-bu "Bad bu ~a" bu)]))

(define (ts-bus Γ Ξ bus head path)
  (let all ([Γ Γ] [bus bus] [i 0] [rev-bus* '()])
    (match bus
      ['() (values Γ (reverse rev-bus*))]
      [(cons bu bus)
       (define-values (Γ* bu*) (ts-bu Γ Ξ bu `((,head . ,i) . ,path)))
       (all Γ* bus (add1 i) (cons bu* rev-bus*))]
      [_ (error 'ts-bus)])))
