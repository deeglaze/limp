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
         recursive-nonrecursive
         ;; for testing
         Space Ref
         )
#|
Transform a language into a skeleton mkV, with a feedback loop for improving the allocation rules.
|#

;; Unfolding and subtyping has difficult interactions that I don't have time to mess with
;; before graduating.

(struct Space (x) #:prefab)
(struct Ref (x) #:prefab)
(struct Container (τ) #:prefab)

(define (mk-scc-map sccs)
  (for*/hash ([scc (in-list sccs)]
              ;; Singleton SCCs aren't recursive.
              #:unless (and (pair? scc) (null? (cdr scc)))
              [node (in-list scc)])
    (values node scc)))

(define (bool->trust b) (if b 'trusted 'untrusted))

(define (type->edges t)
  (define (link-to t* trust)
    (match t*
      ;; If a name is due to be addrized anyway, don't count that as a route to recursion.
      [(TName: _ n #f)
       (if (untrusted? trust)
           (list (list (Container t) (Ref n)))
           '())]
      [_ '()]))
  (define (types->edges ts tr)
    (let mk-links ([ts ts] [edges '()])
       (match ts
         ['() edges]
         [(cons t* ts)
          (mk-links ts (append (link-to t* tr) (type->edges t*) edges))])))
  (match t
    ;; All name references should be edged in from the containers
    [(TName: _ n taddr) '()]
    [(or (? T⊤?) (? TAddr?) (? TBound?) (? TExternal?)) '()]
    [(TVariant: _ _ ts tr) (types->edges ts tr)]
    [(TMap: _ t-dom t-rng _)
     (types->edges (list t-dom t-rng) 'untrusted)]
    [(TSet: _ tv ext)
     (types->edges (list tv) 'untrusted)]
    ;; boilerplate
    [(or (Tμ: _ _ (Scope t) _ _)
         (TΛ: _ _ (Scope t)))
     (types->edges (list t) 'untrusted)]
    ;; Resimplify, since unification may have bumped some stuff up.
    [(or (TSUnion: _ ts)
         (TRUnion: _ ts))
     (types->edges ts 'untrusted)]
    ;; Don't resolve
    [(TCut: _ t u)
     (types->edges (list t u) 'untrusted)]
    [_ (error 'type->edges "Bad type ~a" t)]))

;; All containers are nodes (variants, maps, sets)
;; All spaces have definition nodes and reference nodes.
;; If a container can reach itself, then its immediate space references
;;  within the SCC are addrized unless not 'untrusted.
;; Produce a map from type to SCC
(define (recursive-nonrecursive user-spaces)
  (define adj
    (append
     ;; Def to Ref (transitive through containers)
#;
     (for/list ([(name ty) (in-hash user-spaces)])
       (cons (Space name) (set-map (names ty) Ref)))
     ;; Def to containers, and containers to refs
     (for/append ([(name ty) (in-hash user-spaces)])
       (define edges (type->edges ty))
       (cons (cons (Space name) (map first edges)) edges))
     ;; Ref to Def
     (for/list ([name (in-hash-keys user-spaces)])
       (list (Ref name) (Space name)))))
  (define G (unweighted-graph/adj adj))
  (define SCC (scc G))
  ;; TODO: error on bad externalizations.
  ;; TODO: check that trust/boundedness is the same within an SCC
  (mk-scc-map SCC))

#|
A map or set may not be externalized if there is a path from the map to itself
without an intervening variant constructor.
|#

;; Find all the variants and associate with those types the set of newly allocated positions.
(define (map-variants-to-rewritten-type h space-recursion Γ)
  (case-lambda
    [() h]
    [(ty)
     (define (build t)
       (define (alloc-immediate t*)
         (define SCC (hash-ref space-recursion (Container t) ∅))
         ;; if t* is in t's SCC, then we allocate it.
         (match t*
           [(TName: _ n taddr)
            #:when (and (set-member? SCC (Space n))
                        ;; Externalized maps/sets are unlinked.
                        (match (hash-ref Γ n)
                          [(or (TMap: _ _ _ #t) (TSet: _ _ #t)) #f]
                          [_ #t]))
            (or taddr limp-default-rec-addr)]
           [_ t*]))
       (or (hash-ref h t #f)
           (let
               ([ty*
                 (match t
                   [(Tμ: _ _ st _ _) (build (open-scope st -addrize))]
                   [(TName: _ x taddr) (or taddr t)]
                   [(? T⊤?) limp-default-⊤-addr] ;; All anys must be heap-allocated
                   [(TVariant: _ name ts tr)
                    (if (untrusted? tr)
                        (mk-TVariant #f name (map alloc-immediate ts) tr)
                        (mk-TVariant #f name (map build ts) tr))]
                   [(TMap: _ t-dom t-rng ext)
                    (mk-TMap #f (alloc-immediate t-dom) (alloc-immediate t-rng) ext)]
                   [(TSet: _ t ext)
                    (mk-TSet #f (alloc-immediate t) ext)]
                   ;; boilerplate
                   [(or (? TAddr?) (? TBound?) (? TExternal?)) t]
                   [(TΛ: _ _ (Scope t)) (build t)]
                   [(TSUnion: _ ts) (*TSUnion #f (map build ts))]
                   [(TRUnion: _ ts) (*TRUnion #f (map build ts))]
                   [(TCut: _ t u)
                    (match (resolve t #:addrize space-recursion)
                      [(TΛ: _ _ s)
                       (build (open-scope s -addrize))]
                      [(? TAddr? τ)
                       τ]
                      [τ (error 'map-variants-to-rewritten-type "Bad cut: ~a" τ)])])])
             (hash-set! h t ty*)
             ty*)))
    (build ty)]))

(define (populate-bu-rules tr vh eh path bu)
  (match bu
    [(Update _ k v)
     (populate-expr-rules tr vh eh `(update-key . ,path) k)
     (populate-expr-rules tr vh eh `(update-value . ,path) v)]
    [(Where _ pat e)
     (populate-expr-rules tr vh eh `(where-rhs . ,path) e)]))

(define (implicit-translation? τ)
  (or (and (TAddr? τ) (TAddr-implicit? τ))))

(define (populate-expr-rules tr vh eh path e)
  (match e
    ;; For each e in es with an implicit TAddr type, introduce a new rule.
    [(EVariant _ ct n tag τs es)
     (displayln e)
     (define to-alloc
       (match (tr (πct ct))
         [(TVariant: _ _ σs _)
          (for/list ([σ (in-list σs)]
                     [i (in-naturals)]
                     #:when (implicit-translation? σ))
            i)]
         [vτ (error 'populate-expr-rules "Variant has non-variant type ~a" vτ)]))
     (for ([e (in-list es)]
           [i (in-naturals)])
       (populate-expr-rules tr vh eh `((,n . ,i) . ,path) e))
     (when (pair? to-alloc)
       (hash-set! vh (or tag path) to-alloc))]
    
    [(EExtend _ ct m tag k v)
     (displayln e)
     (populate-expr-rules tr vh eh `(extend-map . ,path) m)
     (populate-expr-rules tr vh eh `(extend-key . ,path) k)
     (populate-expr-rules tr vh eh `(extend-value . ,path) v)
     (define τ (πct ct))
     (define τ* (tr τ))
     (define to-alloc
       (match τ*
         [(TMap: _ d r _)
          (append (if (implicit-translation? d) '(key) '())
                  (if (implicit-translation? r) '(value) '()))]
         [τ (error 'populate-expr-rules "EExtend has non-map type ~a" τ)]))
     (when (pair? to-alloc)
       (hash-set! eh (or tag path) to-alloc))]

    ;; Everything else is structural and builds up the tree path.
    [(ECall _ ct mf τs es)
     (for ([e (in-list es)]
           [i (in-naturals)])
       (populate-expr-rules tr vh eh `((call ,mf . ,i) . ,path) e))]

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
