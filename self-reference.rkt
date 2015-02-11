#lang racket/base
(require "types.rkt" "subtype.rkt" "tc-ctxs.rkt"
         racket/match
         racket/set
         racket/trace
         racket/pretty)
(provide reset-self-referential! self-referential? heap-allocate?)
#|
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

(define self-referential (make-hash)) ;; memoize for speed.
(define (reset-self-referential!) (hash-clear! self-referential))
(define self-dyn (make-parameter #f))
(define self-ref (make-parameter #f))
;; It's possible to call back into self-referential? during resolve, but we want to
;; compare against the top level self-referential? type.
(define (self-referential? t)
  (define prev (self-ref))
  (define self (or prev t))
  (when prev (printf "Self: ~a~%" prev))
  (parameterize ([self-ref self])
    (or (hash-ref self-referential t #f)
        (let* ([prev (self-dyn)]
               [self-seen (or prev (mutable-set))])
          (when prev (printf "Last seen ~a~%" prev))
          (parameterize ([self-dyn self-seen])        
            (define (sr-rec t*)
              (cond
               ;; Already went down this path and didn't find self-reference.
               [(set-member? self-seen t*) #f]
               ;; found a supertype that isn't the top level self -- self-referential.
               [(and (< 0 (set-count self-seen))
                     ;; don't self-loop when checking subtyping relationship.
                     (parameterize ([heapifying? #f])
                       (<:? (empty-ctx) self t*))) #t]
               [else
                (set-add! self-seen t*)
                (printf "~a ~a~%" self-seen t*)
                (match t* ;; ⊤ is a supertype, so we took care of that.
                  [(or (? TAddr?) (? TExternal?)) #f]
                  [(TVariant: _ _ ts _)
                   (printf "Variant Any?~%")
                   (ormap sr-rec ts)] ;; XXX: trust must be checked elsewhere
                  [(TMap: _ t-dom t-rng _)
                   (or (sr-rec t-dom) (sr-rec t-rng))]
                  [(TSet: _ tv _) (sr-rec tv)]
                  [(Tμ: _ x st tr _)
                   (sr-rec (if (untrusted? tr)
                               (open-scope st t*)
                               ;; ⊥ is not a supertype of anything but itself.
                               ;; Recursive positions are safe.
                               (open-scope st T⊥)))]
                  [(TΛ: _ x st _) #f] ;; XXX: Must be instantiated to be a problem?
                  [(TUnion: _ ts)
                   (printf "Union Any?~%")
                   (ormap sr-rec ts)]
                  [(? THeap?) #f] ;; Gets heapified and removes possible recursion here.
                  [(? needs-resolve?)
                   (printf "Calling resolve on ~a~%" t*)
                   (define t** (resolve t*))
                   (printf "Resolving. ~a, ~a~%" self-seen t**)
                   (sr-rec t**)]
                  ;; names are introduced by a μ, and trusted if the name is not a symbol
                  [(TFree: _ n) (symbol? n)]
                  [(TWeak: _ t) (sr-rec t)]
                  [(? T⊤?) #t]
                  [(or (? TBound?))
                   (error 'self-referential? "We shouldn't see names here ~a" t*)]
                  [_ (error 'self-referential? "Bad type ~a" t*)])]))
            (trace sr-rec)
            (define b (sr-rec t))
            (hash-set! self-referential t b)
            b)))))
(trace self-referential?)

;; Can't resolve through a heap-allocation
(define (externalized? τ)
  (match τ
    [(and (not (? THeap?)) (? needs-resolve?))
     (externalized? (resolve τ))]
    [(or (TMap: _ _ _ #t) (TSet: _ _ #t)) #t]
    [_ #f]))

(define (heap-allocate? σ)
  (or (THeap? σ)
      (parameterize ([self-dyn (or (self-dyn) (mutable-set))])
       (and (self-referential? σ)
            (not (externalized? σ))))))
