#lang racket/base
(provide lang-variants-of-arity)
(require racket/match
         racket/set
         racket/trace
         "language.rkt" "types.rkt" "type-formers.rkt" "type-lattice.rkt")

;; Find all instances of variants named n with given arity, and return
;; their type, additionally quantified by all the containing Λs.
(define (lang-variants-of-arity Γ overlap)
  (define us (Language-ordered-us (current-language)))
  (define seen (mutable-seteq))
  (define more-upper (free->x T⊤ overlap #:∪ (λ (self sy ts) (sort-TUnion sy ts))))
  (reverse
   (for/fold ([found '()])
       ([nu (in-list us)])
     (define τ (cdr nu))
     (define (collect τ TVs OAs Name-TVs found)
       (define (collect* τs found)
         (match τs
           ['() found]
           [(cons τ τs)
            (define found* (collect τ TVs OAs Name-TVs found))
            (collect* τs found*)]
           [_ (error 'collect* "Expected a list of types: ~a" τs)]))
       (cond
        [(set-member? seen τ) found]
        [else
         (set-add! seen τ)
         (match τ
           [(TVariant: _ n* ts tr)
            (define τ* (free->x Tpermissive τ))
            (cond
             ;; easy check first
             [(or (T⊤? more-upper)
                  (and (TVariant? more-upper)
                       (eq? (TVariant-name τ*) (TVariant-name more-upper))))
              (define-values (Δ m) (type-meet Γ τ* more-upper))
              (displayln "Maybe")
              (trace-type-meet!)
              (define found*
                ;; Tpermissive is like T⊥ orderwise, but doesn't constitute an error.
                (if (T⊥? m)
                    found
                    (begin #;(printf "Granted ~a, ~a~%" τ overlap)
                      (cons (quantify-frees τ TVs #:names Name-TVs #:OAs OAs) found))))
              (untrace-type-meet!)
              (collect* ts found*)]
             [else found])]
           [(TΛ: _ x s oa)
            (define x* (gensym x))
            (define TVs* (cons x* TVs))
            (collect (open-scope s (mk-TFree #f x*)) TVs* (cons oa OAs) (cons x Name-TVs) found)]
           [(TName: _ x)
            found]
           [(Tμ: _ x s tr n)
            (collect (open-scope s (mk-TFree #f (gensym x))) TVs OAs Name-TVs found)]
           [(? needs-resolve?) (collect (resolve τ) TVs OAs Name-TVs found)]
           [(TMap: _ d r _)
            (collect r TVs OAs Name-TVs (collect d TVs OAs Name-TVs found))]
           [(or (TSet: _ v _) (THeap: _ _ _ v)) (collect v TVs OAs Name-TVs found)]
           [(TUnion: _ ts) (collect* ts found)]
           [_ found])]))
     (collect τ '() '() '() found))))
(trace lang-variants-of-arity)
