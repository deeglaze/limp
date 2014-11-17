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

The primary difficulty in this type system is determining which positions of
collection constructions are "recursive," i.e., allow unbounded nesting.

If a type of container construction (EVariant, EAdd or EExtend),
through structural links and resolution reaches a supertype of itself,
then it is self-referential.
Inner positions that are self-referential types must then be heap-allocated.

Example:
 Types
 ------
 List = Λ X. (Nil) + (Cons X (List X))
 Kont = List[Frame]
 Frame = (ar Expr Env) + (fn Value)
 State = (ev Expr Env Kont) + ...

 Expression
 ----------
 e0, e1 : Expr, ρ: Env, κ: Kont ⊢ (ev e0 ρ (Cons (ar e1 ρ) κ))

 What must be heap allocated?
 The ev container is not self-referential, so we continue recursively.
 e0 and ρ are not container constructors, but references. Done.
 The Cons expressios is a container constructor.
 The type of the expression is (Cons (ar Expr Env) Kont).
 Kont resolves to (Nil) + (Cons Frame (List Frame)).
 (Cons Frame (List Frame)) is a supertype of (Cons (ar Expr Env) Kont).
 Therefore this constructor has a self-referential type.
 The (ar Expr Env) type is not self-referential and may be kept in place.
 The Kont type has (List Frame) reachable through resolution and structure, so
 it is self-referential and must be heap-allocated.

|#

;; Unfolding and subtyping has difficult interactions that I don't have time to mess with
;; before graduating.

(define (mk-scc-map sccs)
  (for*/hash ([scc (in-list sccs)]
              ;; Singleton SCCs aren't recursive.
              #:unless (and (pair? scc) (null? (cdr scc)))
              [node (in-list scc)])
    (values node scc)))

(define (bool->trust b) (if b 'trusted 'untrusted))

(define (type->edges t)
  (define seen (mutable-seteq))
  (let rec ([t t])
   (define (link-to t* trust)
     (match t*
       ;; If a name is due to be addrized anyway, don't count that as a route to recursion.
       [(TName: _ n taddr)
        (if (and (not taddr) (untrusted? trust))
            (list (list t t*))
            '())]
       ;; any taddr given -> unlinked
       [(or (TFree: _ _ taddr) (TBound: _ _ taddr))
        (if taddr '() (list (list t t*)))]
       [_ (list (list t t*))]))
   (define (types->edges ts [tr 'untrusted])
     (let mk-links ([ts ts] [edges '()])
       (match ts
         ['() edges]
         [(cons t* ts)
          (mk-links ts (append (link-to t* tr) (rec t*) edges))])))
   (cond
    [(set-member? seen t) '()]
    [else
     (set-add! seen t)
     (match t
       [(or (? T⊤?) (? TAddr?) (? TBound?) (? TExternal?) (? TFree?)) '()]
       [(TVariant: _ _ ts tr) (types->edges ts tr)]
       [(TMap: _ t-dom t-rng _)
        (types->edges (list t-dom t-rng))]
       [(TSet: _ tv ext)
        (types->edges (list tv))]
       [(Tμ: _ x st tr _)
        (types->edges (list (if (untrusted? tr)
                                (open-scope st t)
                                (open-scope st (mk-TFree #f (gensym x) 'trusted)))))]
       [(TΛ: _ x st) (types->edges (list (open-scope st (mk-TFree #f (gensym x) #f))))]
       ;; Resimplify, since unification may have bumped some stuff up.
       [(or (TSUnion: _ ts)
            (TRUnion: _ ts))
        (types->edges ts)]
       [(TCut: _ u s) (types->edges (list u s (resolve t)))]
       [(? TName?) (types->edges (list (resolve t)))]
       [_ (error 'type->edges "Bad type ~a" t)])])))

;; All containers are nodes (variants, maps, sets)
;; All spaces have definition nodes and reference nodes.
;; If a container can reach itself, then its immediate space references
;;  within the SCC are addrized unless not 'untrusted.
;; Produce a map from type to SCC
(define (recursive-nonrecursive all-types)
  (define adj
    (append
     (for/append ([ty (in-set all-types)])
       (type->edges ty))
     ;; Connect subtypes
     (for*/list ([ty0 (in-set all-types)]
                 [ty1 (in-set all-types)]
                 #:when (and (not (equal? ty0 ty1)) (<:? ty0 ty1)))
       (list ty0 ty1))))
  (define G (unweighted-graph/adj adj))
  (define SCC (scc G))
  (displayln "Graph")
  (pretty-print adj)
  (displayln "SCCs")
  (pretty-print SCC)
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
         (define SCC (hash-ref space-recursion t '()))
         ;; if t* is in t's SCC, then we allocate it.
         (match t*
           [(TName: _ n taddr)
            (or taddr
                (let ([τ (resolve t*)]
                      [U (mk-TRUnion #f SCC)])
                  (if (and (or (<:? t* U)
                               (<:? τ U))
                           (match τ
                             [(or (TMap: _ _ _ #t) (TSet: _ _ #t)) #f]
                             [_ #t]))
                      limp-default-rec-addr
                      t*)))]
           [_ (if (set-member? SCC t*)
                  limp-default-rec-addr
                  t*)]))
       (trace alloc-immediate)
       (or (hash-ref h t #f)
           (let
               ([ty*
                 (begin
                   ;; Temporary trusted self-reference
                   (hash-set! h t t)
                   (match t
                     [(Tμ: _ _ st _ _) (build (open-scope st -addrize))]
                     [(or (TName: _ _ taddr) (TExternal: _ _ taddr)) (or taddr t)]

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
                     [(or (? TAddr?) (? TBound?)) t]
                     [(TΛ: _ _ (Scope t)) (build t)]
                     [(TSUnion: _ ts) (*TSUnion #f (map build ts))]
                     [(TRUnion: _ ts) (*TRUnion #f (map build ts))]
                     [(TCut: _ t u)
                      (match (resolve
                              t
                              #:addrize
                              (λ (x) (for/or ([t (in-set (hash-ref space-recursion (hash-ref Γ x #f) ∅))]
                                              #:when (TName? t))
                                       (eq? x (TName-x t)))))
                        [(TΛ: _ _ s)
                         (build (open-scope s -addrize))]
                        [(? TAddr? τ)
                         τ]
                        [τ (error 'map-variants-to-rewritten-type "Bad cut: ~a" τ)])]))])
             (hash-set! h t ty*)
             ty*)))
     (trace build)
     (build ty)]))

(define (populate-bu-rules tr vh eh path bu)
  (match bu
    [(Update _ k v)
     (populate-expr-rules tr vh eh `(update-key . ,path) k)
     (populate-expr-rules tr vh eh `(update-value . ,path) v)]
    [(Where _ pat e)
     (populate-expr-rules tr vh eh `(where-rhs . ,path) e)]
    [_ (error 'populate-bu-rules "Bad bu ~a" bu)]))

(define ((populate-bu-types! add!) bu)
  (define E (populate-expr-types! add!))
  (match bu
    [(Update _ k v) (E k) (E v)]
    [(Where _ pat e)
     ((populate-pattern-types! add!) pat)
     (E e)]
    [_ (error 'populate-bu-types! "Bad bu ~a" bu)]))

(define (implicit-translation? τ)
  (and (TAddr? τ) (TAddr-implicit? τ)))

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
    [_ (error 'populate-expr-rules "Unrecognized expression form: ~a" e)]))

(define (populate-pattern-types! add!)
  (define (self pat)
    (add! (πcc pat))
    (match pat
      [(or (PAnd _ _ ps) (PVariant _ _ _ ps)) (for-each self ps)]
      [(or (PMap-with _ _ k v p) (PMap-with* _ _ k v p))
       (for-each self (list k v p))]
      [(or (PSet-with _ _ v p) (PSet-with* _ _ v p))
       (self v) (self p)]
      [(PTerm _ _ t) ((populate-term-types! add!) t)]
      [(or (? PWild?) (? PIsExternal?) (? PIsAddr?) (? PIsType?) (? PName?)) (void)]
      [_ (error 'populate-pattern-types! "Unsupported pattern: ~a" pat)]))
  self)

(define (populate-term-types! add!)
  (define (self t)
    (add! (πcc t))
    (match t
      [(Variant _ _ _ ts) (for-each self ts)]
      [(Map _ _ f) (hash-for-each f (λ (k v) (self k) (self v)))]
      [(Set _ _ s) (set-for-each s self)]
      [(? External?) (void)]
      [_ (error 'populate-term-types! "Unsupported term ~a" t)]))
  self)

(define (populate-expr-types! add!)
  (define (self e)
    (add! (πcc e))
    (match e
      ;; For each e in es with an implicit TAddr type, introduce a new rule.
      [(or (EVariant _ _ _ _ τs es)
           (ECall _ _ _ τs es))
       (for-each add! τs)
       (for-each self es)]

      [(EExtend _ _ m _ k v)
       (for-each self (list m k v))]

      [(EStore-lookup _ _ k _) (self k)]

      [(ELet _ _ bus body)
       (for-each (populate-bu-types! add!) bus)
       (self body)]
      [(EMatch _ _ de rules)
       (self de)
       (for-each (populate-rule-types! add!) rules)]
      [(ESet-union _ _ es) (for-each self es)]
      [(or (ESet-intersection _ _ e es)
           (ESet-subtract _ _ e es)) (self e) (for-each self es)]
      [(or (ESet-member _ _ e0 e1)
           (EMap-lookup _ _ e0 e1)
           (EMap-has-key _ _ e0 e1)
           (EMap-remove _ _ e0 e1))
       (self e0)
       (self e1)]

      [(or (? ERef?) (? EAlloc?) (? EEmpty-Map?) (? EEmpty-Set?)) (void)]
      [_ (error 'populate-rule-types! "Unrecognized expression form: ~a" e)]))
  self)

(define (populate-rule-rules tr vh eh path rule)
  (match rule
    [(Rule _ name lhs rhs bus)
     (define path* `((Rule ,name) . ,path))
     (for ([bu (in-list bus)]
           [i (in-naturals)])
       (populate-bu-rules tr vh eh `((bu . ,i) . ,path*) bu))
     (populate-expr-rules tr vh eh `(rhs . ,path*) rhs)]
    [_ (error 'populate-rule-rules "Bad rule ~a" rule)]))

(define ((populate-rule-types! add!) rule)
  (match rule
    [(Rule _ _ lhs rhs bus)
     ((populate-pattern-types! add!) lhs)
     (for-each (populate-bu-types! add!) bus)
     ((populate-expr-types! add!) rhs)]
    [_ (error 'populate-rule-types "Bad rule ~a" rule)]))

(define (language->mkV R alloc)
  (define L (current-language))
  (define us (Language-user-spaces L))

  (define all-types (mutable-set)) (define (add! τ) (set-add! all-types τ))
  (for ([t (in-hash-values us)]) (add! t))
  (for-each (populate-rule-types! add!) R)
  ;; Will be updated any time we translate new types.
  (define space-recursion (recursive-nonrecursive all-types))
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
