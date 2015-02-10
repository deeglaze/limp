#lang racket/base
(provide castable cast-to)
(require racket/match racket/set
         (only-in racket/bool implies)
         "common.rkt"
         "subtype.rkt" "types.rkt")

(define (cast-to from to)
  (cond
   [(<:? from to) (Check to)] ;; upcast -> check, not cast
   [(castable from to) (Cast to)]
   [else (type-error "Could not cast ~a to ~a" from to)]))

;; τ is castable to σ if τ <: σ, τ = ⊤,
;; or structural components of τ are castable to structural components of σ.
(define (castable from to)
  (define (check A from to)
    (if (or
         (<:? from to) ;; upcast
         (<:? to from)) ;; strict downcast
        A
        ;; Structurally castable?
        (match* (from to)
          [((TΛ: _ _ (Scope f) oa) (TΛ: _ _ (Scope t) oa))
           (check A f t)]
          [((TVariant: _ n tsf tr0) (TVariant: _ n tst tr1))
           #:when (implies (and tr0 tr1) (equal? tr0 tr1))
           (let all ([A A] [tsf tsf] [tst tst])
             (match* (tsf tst)
               [('() '()) A]
               [((cons f tsf) (cons t tst))
                (seq A (check A f t) (all A tsf tst))]
               [(_ _) #f]))]
          [((Tμ: _ _ (Scope f) tr n) (Tμ: _ _ (Scope t) tr n))
           (check A f t)]
          [((TMap: _ df rf ext) (TMap: _ dt rt ext))
           (seq (check A df dt)
                (check A rf rt))]
          [((TSet: _ f ext) (TSet: _ t ext)) (check A f t)]
          [((TUnion: _ tsf) _)
           (for/fold ([A A]) ([tf (in-list tsf)]
                              #:when A)
             (check A tf to))]
          [(_ (TUnion: _ tst))
           ;; Don't save false paths
           (for/or ([tt (in-list tst)]) (check A from tt))]
          ;; XXX: Will this possibly diverge?
          [((and (not (? Tμ?)) (? needs-resolve?)) _)
           (if (set-member? A (cons from to))
               A
               (check (set-add A (cons from to))
                      (resolve from) to))]
          [(_ (and (not (? Tμ?)) (? needs-resolve?)))
           (if (set-member? A (cons from to))
               A
               (check (set-add A (cons from to))
                      from (resolve to)))]
          [(_ _) #f])))
  (and (check ∅ from to) #t))
