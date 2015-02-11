#lang racket/base
(provide type-wf-before?)
(require racket/match "types.rkt" "tc-ctxs.rkt")

(define (type-wf-before? Γ n τ)
  (match τ
    [(or (Tμ: _ x s _ _)
         (TΛ: _ x s _))
     (define x* (gensym x))
     (type-wf-before? (unsafe-tvar-at Γ x* n) (open-scope s (mk-TFree #f x*)))]
    ;; boilerplate
    [(or (? T⊤?) (? T⊥?) (? TAddr?) (? TExternal?) (? TName?) (? TError?))
     #t]
    [(TFree: _ x) (ctx-var-in-dom? Γ x #:before n)]

    [(or (TUnion: _ ts)
         (TVariant: _ _ ts _))
     (for/and ([t (in-list ts)]) (type-wf-before? Γ n t))]
    [(or (TCut: _ t u)
         (TMap: _ t u _)
         (THeap: _ t _ u)
         (TArrow: _ t u))
     (and (type-wf-before? Γ n t)
          (type-wf-before? Γ n u))]

    [(or (TSet: _ t _) (TWeak: _ t))
     (type-wf-before? Γ n t)]

    [_ (error 'type-wf-before? "Bad type ~a" τ)]))
