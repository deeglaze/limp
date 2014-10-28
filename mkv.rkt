#lang racket/base
(require "types.rkt" "language.rkt" "common.rkt"
         graph)
#|
Transform a language into a skeleton mkV, with a feedback loop for improving the allocation rules.
|#

;; Unfolding and subtyping has difficult interactions that I don't have time to mess with
;; before graduating. 

(struct Space (x) #:transparent)
(struct Ref (x) #:transparent)
(define (recursive-nonrecursive user-spaces)
  (define G (unweighted-graph/adj
             (append
              (for/list ([(name ty) (in-hash user-spaces)])
                (cons (Space name) (map Ref (free ty))))
              ;; Close the loop
              (for/list ([name (in-hash-keys user-spaces)])
                (list (Ref name) (Space name))))))
  (for/fold ([h #hasheq()]) ([comp (in-list (scc G))])
    (define-values (spaces references) (partition Space? comp))
    (for/fold ([h h]) ([space (in-list spaces)])
      (hash-set h space
                (for/or ([r (in-list references)])
                  (eq? space (Ref-x r)))))))

(define (find-type-in-Γ ty Γ)
  (for/or ([(name ty*) (in-hash Γ)]
           #:when (type-contains? ty ty*))
    name))

;; Find all the variants and associate with those types the set of newly allocated positions.
(define (map-variants-to-rewritten-type ty space-recursion Γ h)
  (let build ([t ty])
   (match t
     [(Tμ: _ st _ _ _) (map-variants-to-rewritten-type (open-scope st -addrize))]
     [(TName: x taddr)
      (if (hash-ref space-recursion x #f)
          (match (hash-ref Γ x)
            ;; externalized -> inline
            [(and t (TMap: _ _ #t) (TSet: _ #t))
             (build t)]
            [_ taddr])
          t)]
     [(TVariant: name ts r c n)
      (cond [c t]
            [else
             (define ts* (for/list ([t (in-list ts)]
                                    [i (in-naturals)])
                           (define t* (build t))
                           (when (and (not (TAddr? t)) (TAddr? t*))
                             (hash-hash-add! h t i t*))
                           t*))
             (mk-TVariant name ts* r c n)])]
     ;; boilerplate
     [(or (? T⊤?) (? TAddr?) (? TBound?) (? TFree?)) t]
     [(TΛ: _ (Scope t)) (build t)]
     [(TSUnion: ts) (mk-TSUnion (map build ts))]
     [(TRUnion: ts) (mk-TRUnion (map build ts))]
     [(TCut: t u) (build (resolve t))]
     [(TMap: t-dom t-rng ext)
      (mk-TMap (build t-dom) (build t-rng) ext)]
     [(TSet: t ext) (mk-TSet (build t) ext)])))

(define (language->mkV L R alloc)
  (define space-recursion (recursive-nonrecursive (Language-user-spaces L)))
  ;; Assign allocation behavior to each variant in Γ
  (define ty-to-mkv (make-hash))
  (for ([(name ty) (in-hash (Language-user-spaces L))])
    (map-variants-to-rewritten-type ty space-recursion h))
  ;; Each rule could be the same on the left and different on the right.
  ;; We need to know the rule to generate the address? Sure, this comes from alloc.

;; FIXME: Pseudocode
  
  `(λ (ς σ μ ρ δ σΔ μΔ n ts)
      ;; and τ of requested variant, want rule requesting, and position requesting
      (match τ . ,(for/list ([(τ* positions) (in-hash ty-to-mkv)])
                    `[(== ,τ*)
                      (n . ,(for/list ([t (in-list ts)]
                                       [i (in-naturals)])
                              (if (set-member? positions i)
                                  (make-addr-at ς alloc)
                                  t)))])))
  )
