#lang racket/base
(require "common.rkt"
         "language.rkt"
         "tast.rkt"
         "types.rkt"
         graph
         racket/list
         racket/match
         racket/pretty
         racket/set
         racket/trace)
(provide language->mkV
         recursive-nonrecursive)
#|
Transform a language into a skeleton mkV, with a feedback loop for improving the allocation rules.
|#

;; Unfolding and subtyping has difficult interactions that I don't have time to mess with
;; before graduating. 

(struct Space (x) #:transparent)
(struct Ref (x) #:transparent)
(define (recursive-nonrecursive user-spaces)
  (define adj
    (append
     ;; Def to Ref
     (for/list ([(name ty) (in-hash user-spaces)])
       (cons (Space name) (set-map (names ty) Ref)))
     ;; Ref to Def
     (for/list ([name (in-hash-keys user-spaces)])
       (list (Ref name) (Space name)))))
  (define G (unweighted-graph/adj adj))

  ;; TODO: error on bad externalizations.
  ;; TODO: check that trust/boundedness is the same within an SCC
  (for/fold ([h #hasheq()]) ([comp (in-list (scc G))])
    (define-values (spaces references) (partition Space? comp))
    (for/fold ([h h]) ([space (in-list spaces)])
      (match-define (Space s) space)
      (hash-set h s
                (for/or ([r (in-list references)])
                  (eq? s (Ref-x r)))))))

#|
A map or set may not be externalized if there is a path from the map to itself
without an intervening variant constructor.
|#

;; Find all the variants and associate with those types the set of newly allocated positions.
(define ((map-variants-to-rewritten-type h space-recursion Γ) ty)
  (define (build t)
    (or (hash-ref h t #f)
        (let
          ([ty*
            (match t
              [(Tμ: _ _ st _ _ _) (build (open-scope st -addrize))]
              [(TName: _ x taddr)
               ;; TODO: associate trust with the space name, not just variants in the space.
               (if (hash-ref space-recursion x #f)
                   (match (hash-ref Γ x)
                     ;; externalized -> inline. Bad externals should have errored.
                     [(and t (or (TMap: _ _ _ #t) (TSet: _ _ #t)))
                      (build t)]
                     [_ (or taddr limp-default-Λ-addr)])
                   t)]
              [(TVariant: _ name ts tr tc)
               (cond [tc t]
                     [else (mk-TVariant #f name (map build ts) tr tc)])]
              ;; boilerplate
              [(or (? T⊤?) (? TAddr?) (? TBound?) (? TExternal?)) t]
              [(TΛ: _ _ (Scope t)) (build t)]
              [(TSUnion: _ ts) (*TSUnion #f (map build ts))]
              [(TRUnion: _ ts) (*TRUnion #f (map build ts))]
              [(TCut: _ t u)
               (match (resolve t #:addrize space-recursion)
                 [(TΛ: _ _ s)
                  (build (open-scope s -addrize))]
                 [(? TAddr? τ)
                  τ]
                 [τ (error 'map-variants-to-rewritten-type "Bad cut: ~a" τ)])]
              [(TMap: _ t-dom t-rng ext)
               (mk-TMap #f (build t-dom) (build t-rng) ext)]
              [(TSet: _ t ext) (mk-TSet #f (build t) ext)])])
          (hash-set! h t ty*)
          ty*)))
  (trace build)
  (build ty))

(define (populate-bu-rules tr vh eh path bu)
  (match bu
    [(Update _ k v)
     (populate-expr-rules tr vh eh `(update-key . ,path) k)
     (populate-expr-rules tr vh eh `(update-value . ,path) v)]
    [(Where _ pat e)
     (populate-expr-rules tr vh eh `(where-rhs . ,path) e)]))

(define (implicit-translation? tr typed)
  (define σ (πcc typed))
  (define τ (tr σ))
  (and (TAddr? τ) (TAddr-implicit? τ)))

(define (populate-expr-rules tr vh eh path e)
  (match e
    ;; For each e in es with an implicit TAddr type, introduce a new rule.
    [(ECall _ ct mf τs es)
     (for ([e (in-list es)]
           [i (in-naturals)])
       (populate-expr-rules tr vh eh `((call ,mf . ,i) . ,path) e))]

    [(EVariant _ ct n tag τs es)
     (define to-alloc
       (for/list ([e (in-list es)]
                  [i (in-naturals)]
                  #:when (implicit-translation? tr e))
         i))
     (for ([e (in-list es)]
           [i (in-naturals)])
       (populate-expr-rules tr vh eh `((,n . ,i) . ,path) e))
     (when (pair? to-alloc)
       (hash-set! vh (or tag path) to-alloc))]
    
    [(EExtend _ ct m tag k v)
     (populate-expr-rules tr vh eh `(extend-map . ,path) m)
     (populate-expr-rules tr vh eh `(extend-key . ,path) k)
     (populate-expr-rules tr vh eh `(extend-value . ,path) v)
     (define to-alloc
       (append (if (implicit-translation? tr k) '(key) '())
               (if (implicit-translation? tr v) '(value) '())))
     (when (pair? to-alloc)
       (hash-set! eh (or tag path) to-alloc))]

    [(EStore-lookup _ ct k lm) (populate-expr-rules tr vh eh `(lookup . path) k)]
    
    [(ELet _ ct bus body)
     (for ([bu (in-list bus)]
           [i (in-naturals)])
       (populate-bu-rules tr vh eh `((let-bu . ,i) . ,path) bu))
     (populate-expr-rules tr vh eh `(let-body . ,path) body)]
    [(EMatch _ ct de rules)
     (populate-expr-rules tr vh eh `(match-disc . ,path) de)
     (for ([rule (in-list rules)]
           [i (in-naturals)])
       (populate-rule-rules tr vh eh `((match-rule . ,i) . ,path) rule))]
    [(ESet-union _ ct es)
     (for ([e (in-list es)]
           [i (in-naturals)])
       (populate-expr-rules tr vh eh `((union . ,i) . ,path) e))]
    [(ESet-intersection _ ct e es)
     (for ([e (in-list (cons e es))]
           [i (in-naturals)])
       (populate-expr-rules tr vh eh `((intersection . ,i) . ,path) e))]
    [(ESet-subtract _ ct e es)
     (for ([e (in-list (cons e es))]
           [i (in-naturals)])
       (populate-expr-rules tr vh eh `((subtract . ,i) . ,path) e))]
    [(ESet-member _ ct e v)
     (populate-expr-rules tr vh eh `(member-set . ,path) e)
     (populate-expr-rules tr vh eh `(member-value . ,path) v)]
    [(EMap-lookup _ ct m k)
     (populate-expr-rules tr vh eh `(lookup-map . ,path) m)
     (populate-expr-rules tr vh eh `(lookup-key . ,path) k)]
    [(EMap-has-key _ ct m k)
     (populate-expr-rules tr vh eh `(has-key-map . ,path) m)
     (populate-expr-rules tr vh eh `(has-key-key . ,path) k)]
    [(EMap-remove _ ct m k)
     (populate-expr-rules tr vh eh `(map-remove-map . ,path) m)
     (populate-expr-rules tr vh eh `(map-remove-key . ,path) k)]

    [(or (? ERef?) (? EAlloc?) (? EEmpty-Map?) (? EEmpty-Set?)) (void)]
    [_ (error 'tc-expr "Unrecognized expression form: ~a" e)]))

(define (populate-rule-rules tr vh eh path rule)
  (match-define (Rule _ name lhs rhs bus) rule)
  (define path* `((Rule ,name) . ,path))
  (for ([bu (in-list bus)]
        [i (in-naturals)])
    (populate-bu-rules tr vh eh `((bu . ,i) . ,path*) bu))
  (populate-expr-rules tr vh eh `(rhs . ,path*) rhs))

(define (language->mkV R alloc)
  (define L (current-language))
  (define us (Language-user-spaces L))
  (define space-recursion (recursive-nonrecursive us))
  ;; Rewrite language user spaces to addrize the recursive references
  ;; Assign allocation behavior to each variant in Γ
    (define ty-to-mkv (make-hash))
    (printf "Sup~%")
    (define translate (map-variants-to-rewritten-type ty-to-mkv space-recursion us))
    (for ([(name ty) (in-hash us)])
      (translate ty))

    (define vtag->rule (make-hash))
    (define etag->rule (make-hash))
    (for ([rule (in-list R)]
          [i (in-naturals)])
      (populate-rule-rules translate vtag->rule etag->rule
                           (or (Rule-name rule) `(rule . ,i))
                           rule))

    (displayln "Variant rules:")
    (pretty-print vtag->rule)
    (displayln "~%Extension rules:")
    (pretty-print etag->rule)

    ;; Now when we encounter an ECall, EVariant or EExtend, we can look up
    ;; the translated type and see if any components are TAddr with a true implicit? field.
    ;; All implicit fields must be allocated and stored.
    ;; If we output this as a metafunction, then we have to extend the alloc function.
    ;; If we output this as a Racket function, then we don't,
    ;;  but we have to use the store updating functions.

    ;; 

    ;; Each rule could be the same on the left and different on the right.
    ;; We need to know the rule to generate the address? Sure, this comes from alloc.

    ;; FIXME: Pseudocode
  
    `(λ (ς σ μ ρ δ σΔ μΔ n tag ts)
        ;; and τ of requested variant, want rule requesting, and position requesting
        wut))
