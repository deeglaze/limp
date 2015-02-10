#lang racket/unit
(require racket/match
         "types.rkt" "tast.rkt" "tc-sigs.rkt")
(import tc-pattern^ tc-expr^)
(export tc-bu^)

(define (tc-bu Δ Γ Ξ bu path)
   (match bu
    [(Update sy k v)
     (define k* (tc-expr Δ Γ Ξ k T⊤ (cons 'update-key path) #f))
     ;; We expect k to be a TAddr type, but which kind doesn't matter
     (cond
      [(TAddr? (πcc k*))
       (values Γ (Update sy k* (tc-expr Δ Γ Ξ v T⊤ (cons 'update-value path) #f)))]
      [else
       (values Γ
               (Update sy
                       (replace-ct
                        (type-error "Expect store lookup key to have an address type, got ~a"
                                    (πcc k*))
                        k*)
                       (tc-expr Δ Γ Ξ v T⊤ (cons 'update-value path) #f)))])]
    [(Where sy pat e)
     ;; We expect e and pat to have overlapping types,
     ;; but one's type doesn't drive the other's checking.
     (define e* (tc-expr Δ Γ Ξ e T⊤ (cons 'where-rhs path) #f))
     (define-values (Γ* pat*) (tc-pattern Δ Γ Ξ pat (πcc e*)))
     (values Γ* (Where sy pat* e*))]
    [(When sy e)
     (define e* (tc-expr Δ Γ Ξ e T⊤ (cons 'when-expr path) #f))
     (values Γ (When sy e*))]
    [(Unless sy e)
     (define e* (tc-expr Δ Γ Ξ e  T⊤ (cons 'unless-expr path) #f))
     (values Γ (Unless sy e*))]
    [_ (error 'tc-bu "Bad bu ~a" bu)]))

(define (tc-bus Δ Γ Ξ bus head path)
  (let all ([Γ Γ] [bus bus] [i 0] [rev-bus* '()])
    (match bus
      ['() (values Γ (reverse rev-bus*))]
      [(cons bu bus)
       (define-values (Γ* bu*) (tc-bu Δ Γ Ξ bu `((,head . ,i) . ,path)))
       (all Γ* bus (add1 i) (cons bu* rev-bus*))]
      [_ (error 'tc-bus)])))
