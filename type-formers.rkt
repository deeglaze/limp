#lang racket/base
(provide sort-TUnion *TUnion)
(require racket/match
         (only-in racket/function curry)
         (only-in racket/list append-map)
         "subtype.rkt" "types.rkt" "tc-ctxs.rkt")


(define (flatten-unions-in-list ts)
  (append-map
   (λ (t)
      (match t
        [(TUnion: _ ts*)
         (flatten-unions-in-list ts*)]
        [_ (list t)]))
   ts))

;; Only incomparable types should be represented in a union.
;; When a type subsumes another, we remove the subsumed type.
(define (remove-subtypes Γ ts)
  (let rec ([Γ Γ] [ts ts] [rev-ts* '()])
   (match ts
     ['() (values Γ rev-ts*)]
     [(cons t ts)
      ;; If t is subtyped in the rest of the list, drop it.
      ;; If t was supertyped by a previous type, drop it.
      (cond [(or (for/or ([s (in-list ts)]) (<:? Γ t s))
                 (for/or ([s (in-list rev-ts*)]) (<:? Γ t s)))
             => (λ (Γ) (rec Γ ts rev-ts*))]
            [else (rec Γ ts (cons t rev-ts*))])])))

;; Canonicalize a list of types to forbid disequal but equivalent types.
(define (simplify-types Γ U ts)
  (sort-union Γ U ts remove-subtypes))

(define (sort-union Γ U ts [post values])
  (define-values (Δ ts*)
    (post Γ
          (remove-sorted-dups
           (sort (flatten-unions-in-list ts) < #:key Type-key))))
  (values Δ
          (match ts*
            [(list t) t]
            ['() T⊥]
            [ts (U ts)])))

(define (sort-TUnion sy ts)
  (define-values (Δ t) (sort-union (empty-ctx) (λ (ts) (mk-TUnion sy ts)) ts))
  t)

;; reverses, but it's still canonically sorted.
(define (remove-sorted-dups ts) ;; assumes #f not the first element of list.
  (let loop ([ts ts] [last #f] [new '()])
    (match ts
      ['() new]
      [(cons t ts)
       (if (equal? t last)
           (loop ts last new)
           (loop ts t (cons t new)))]
      [_ (error 'loop "Expected a list of types ~a" ts)])))
(define (*TUnion Γ sy ts)
  (unless (list? ts) (error '*TUnion "WAT"))
  (simplify-types Γ ((curry mk-TUnion) sy) ts))
