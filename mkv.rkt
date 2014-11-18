#lang racket/base
(require "common.rkt"
         "language.rkt"
         "tast.rkt"
         "types.rkt"
         racket/list
         racket/match
         racket/pretty
         racket/set
         racket/trace)
(provide language->mkV self-referential?)
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

#|
A map or set may not be externalized if there is a path from the map to itself
without an intervening variant constructor.
|#

;; Unfolding and subtyping has difficult interactions that I don't have time to mess with
;; before graduating.


(define self-referential (make-hash)) ;; memoize for speed.
(define (self-referential? t)
  (or (hash-ref self-referential t #f)
      (let ()
        (define seen (mutable-seteq))
        (define b
          (let rec ([t* t])
            (cond
             ;; Already went down this path and didn't find self-reference.
             [(set-member? seen t*) #f]
             ;; found a supertype that isn't the top level self -- self-referential.
             [(and (< 0 (set-count seen))
                   (<:? t t*)) #t]
             [else
              (set-add! seen t)
              (match t* ;; ⊤ is a supertype, so we took care of that.
                [(or (? TAddr?) (? TExternal?)) #f]
                [(TVariant: _ _ ts _) (ormap rec ts)] ;; XXX: should we check tr here or in constructor?
                [(TMap: _ t-dom t-rng _)
                 (or (rec t-dom) (rec t-rng))]
                [(TSet: _ tv _) (rec tv)]
                [(Tμ: _ x st tr _)
                 (rec (if (untrusted? tr)
                          (open-scope st t)
                          ;; ⊥ is not a supertype of anything but itself.
                          ;; Recursive positions are safe.
                          (open-scope st T⊥)))]
                [(TΛ: _ x st) #f] ;; XXX: Must be instantiated to be a problem?
                [(or (TSUnion: _ ts) (TRUnion: _ ts)) (ormap rec ts)]
                [(? needs-resolve?) (rec (resolve t))]
                [(or (? TBound?) (? TFree?))
                 (error 'self-referential? "We shouldn't see names here ~a" t*)]
                [_ (error 'type->edges "Bad type ~a" t)])])))
        (hash-set! self-referential t b)
        b)))

;; Can't resolve through a heap-allocation
(define (externalized? τ)
  (match τ
    [(and (? needs-resolve?) (not (TName: _ _ (not #f))))
     (externalized? (resolve τ))]
    [(or (TMap: _ _ _ #t) (TSet: _ _ #t)) #t]
    [_ #f]))

(define (populate-bu-rules vh eh path bu)
  (match bu
    [(Update _ k v)
     (populate-expr-rules vh eh `(update-key . ,path) k)
     (populate-expr-rules vh eh `(update-value . ,path) v)]
    [(Where _ pat e)
     (populate-expr-rules vh eh `(where-rhs . ,path) e)]
    [_ (error 'populate-bu-rules "Bad bu ~a" bu)]))

(define (implicit-translation? τ)
  (and (TAddr? τ) (TAddr-implicit? τ)))

(define (heap-allocate? σ)
  (or (and (TName? σ)
           (implicit-translation? (TName-taddr σ)))
      (and (self-referential? σ)
           (not (externalized? σ)))))

(define (populate-expr-rules vh eh path e)
  (match e
    ;; For each e in es with an implicit TAddr type, introduce a new rule.
    [(EVariant _ ct n tag τs es)
     (for ([e (in-list es)]
           [i (in-naturals)])
       (populate-expr-rules vh eh `((,n . ,i) . ,path) e))
     (define τ (resolve (πct ct)))
     (define to-alloc
       (match τ
         [(TVariant: _ _ σs tr)
          (if (and (untrusted? tr)
                   (self-referential? τ))
              (for/list ([σ (in-list σs)]
                         [i (in-naturals)]
                         #:when (heap-allocate? σ))
                i)
              '())]
         [vτ (error 'populate-expr-rules "Variant has non-variant type ~a" vτ)]))
     (when (pair? to-alloc)
       (hash-set! vh (or tag path) to-alloc))]

    [(EExtend _ ct m tag k v)
     (populate-expr-rules vh eh `(extend-map . ,path) m)
     (populate-expr-rules vh eh `(extend-key . ,path) k)
     (populate-expr-rules vh eh `(extend-value . ,path) v)
     (define τ (resolve (πct ct)))
     (define to-alloc
       (match τ
         [(TMap: _ d r _)
          (if (self-referential? τ)
              (append (if (heap-allocate? d) '(key) '())
                      (if (heap-allocate? r) '(value) '()))
              '())]
             [τ (error 'populate-expr-rules "EExtend has non-map type ~a" τ)]))
     (when (pair? to-alloc)
       (hash-set! eh (or tag path) to-alloc))]

    ;; TODO: add EAdd

    ;; Everything else is structural and builds up the tree path.
    [(ECall _ ct mf τs es)
     (for ([e (in-list es)]
           [i (in-naturals)])
       (populate-expr-rules vh eh `((call ,mf . ,i) . ,path) e))]

    [(EStore-lookup _ ct k lm) (populate-expr-rules vh eh `(lookup . path) k)]

    [(ELet _ ct bus body)
     (for ([bu (in-list bus)]
           [i (in-naturals)])
       (populate-bu-rules vh eh `((let-bu . ,i) . ,path) bu))
     (populate-expr-rules vh eh `(let-body . ,path) body)]
    [(EMatch _ ct de rules)
     (populate-expr-rules vh eh `(match-disc . ,path) de)
     (for ([rule (in-list rules)]
           [i (in-naturals)])
       (populate-rule-rules vh eh `(match-rule . ,i) path rule))]
    [(ESet-union _ ct es)
     (for ([e (in-list es)]
           [i (in-naturals)])
       (populate-expr-rules vh eh `((union . ,i) . ,path) e))]
    [(ESet-intersection _ ct e es)
     (for ([e (in-list (cons e es))]
           [i (in-naturals)])
       (populate-expr-rules vh eh `((intersection . ,i) . ,path) e))]
    [(ESet-subtract _ ct e es)
     (for ([e (in-list (cons e es))]
           [i (in-naturals)])
       (populate-expr-rules vh eh `((subtract . ,i) . ,path) e))]
    [(ESet-member _ ct e v)
     (populate-expr-rules vh eh `(member-set . ,path) e)
     (populate-expr-rules vh eh `(member-value . ,path) v)]
    [(EMap-lookup _ ct m k)
     (populate-expr-rules vh eh `(lookup-map . ,path) m)
     (populate-expr-rules vh eh `(lookup-key . ,path) k)]
    [(EMap-has-key _ ct m k)
     (populate-expr-rules vh eh `(has-key-map . ,path) m)
     (populate-expr-rules vh eh `(has-key-key . ,path) k)]
    [(EMap-remove _ ct m k)
     (populate-expr-rules vh eh `(map-remove-map . ,path) m)
     (populate-expr-rules vh eh `(map-remove-key . ,path) k)]

    [(or (? ERef?) (? EAlloc?) (? EEmpty-Map?) (? EEmpty-Set?)) (void)]
    [_ (error 'populate-expr-rules "Unrecognized expression form: ~a" e)]))

(define (populate-rule-rules vh eh nameless path rule)
  (match rule
    [(Rule _ name lhs rhs bus)
     (define path*
       (cons (if name `(Rule ,name) nameless) path))
     (for ([bu (in-list bus)]
           [i (in-naturals)])
       (populate-bu-rules vh eh `((bu . ,i) . ,path*) bu))
     (populate-expr-rules vh eh `(rhs . ,path*) rhs)]
    [_ (error 'populate-rule-rules "Bad rule ~a" rule)]))

(define (language->mkV R metafunctions alloc)
  (define L (current-language))
  (define us (Language-user-spaces L))

  (define vtag->rule (make-hash))
  (define etag->rule (make-hash))
  (hash-clear! self-referential)
  (for ([rule (in-list R)]
        [i (in-naturals)])
    (populate-rule-rules vtag->rule etag->rule
                         `(rule . ,i) '() rule))
  (for ([mf (in-list metafunctions)])
    (match-define (Metafunction name τ rules) mf)
    (define-values (names τ* rules*) (open-type-and-rules τ rules))
    (for ([rule (in-list rules*)]
          [i (in-naturals)])
      (populate-rule-rules vtag->rule etag->rule
                           `(rule . ,i) `(metafunction ,name)
                           rule)))

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
