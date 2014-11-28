#lang racket/base
(require "common.rkt"
         "language.rkt"
         "self-reference.rkt"
         "tast.rkt"
         "types.rkt"
         racket/dict
         racket/set
         racket/match
         racket/pretty)
(provide language->rules report-rules heapify-language)

;; ROUNDTOIT
;; Unfolding and subtyping has difficult interactions that I don't have time to mess with
;; before graduating.

(define (populate-bu-rules vh eh sh bu)
  (match bu
    [(Update _ k v)
     (populate-expr-rules vh eh sh k)
     (populate-expr-rules vh eh sh v)]
    [(Where _ pat e)
     (populate-expr-rules vh eh sh e)]
    [_ (error 'populate-bu-rules "Bad bu ~a" bu)]))

(define (populate-expr-rules vh eh sh e)
  (define (self e) (populate-expr-rules vh eh sh e))
  (match e
    ;; For each e in es with an implicit TAddr type, introduce a new rule.
    [(EVariant _ ct n tag τs es)
     (for-each self es)
     (define τ (resolve (πct ct)))
     (define to-alloc
       (match τ
         [(TVariant: _ _ σs tr)
          (if (and (untrusted? tr)
                   (self-referential? τ))
              (for/set ([σ (in-list σs)]
                         [i (in-naturals)]
                         #:when (heap-allocate? σ))
                i)
              ∅)]
         [vτ (error 'populate-expr-rules "Variant has non-variant type ~a" vτ)]))
     (unless (set-empty? to-alloc)
       (hash-union! vh tag to-alloc))]

    [(EExtend _ ct m tag k v)
     (for-each self (list m k v))
     (define τ (resolve (πct ct)))
     (define to-alloc
       (match τ
         [(TMap: _ d r _)
          (if (self-referential? τ)
              (set-union (if (heap-allocate? d) (set 0) ∅)
                         (if (heap-allocate? r) (set 1) ∅))
              ∅)]
             [τ (error 'populate-expr-rules "EExtend has non-map type ~a" τ)]))
     (unless (set-empty? to-alloc)
       (hash-union! eh tag to-alloc))]

    [(ESet-add _ ct e tag es)
     (for-each self (cons e es))
     (define τ (resolve (πct ct)))
     (define to-alloc
       (match τ
         [(TSet: _ v _)
          (if (and (self-referential? τ) (heap-allocate? v))
              (for/set ([i (in-range (length es))]) i)
              ∅)]
         [τ (error 'populate-expr-rules "ESet-add has a non-set type ~a" τ)]))
     (unless (set-empty? to-alloc)
       (hash-union! sh tag to-alloc))]

    ;; Everything else structural
    [(EStore-lookup _ _ e _)
     (self e)]

    [(ELet _ _ bus body)
     (for ([bu (in-list bus)])
       (populate-bu-rules vh eh sh bu))
     (populate-expr-rules vh eh sh body)]
    [(EMatch _ ct de rules)
     (self de)
     (for ([rule (in-list rules)])
       (populate-rule-rules vh eh sh rule))]
    
    [(or (ECall _ _ _ _ es)
         (ESet-union _ _ es))
     (for ([e (in-list es)])
       (populate-expr-rules vh eh sh e))]

    [(or (ESet-subtract _ _ e es)
         (ESet-intersection _ _ e es))
     (for-each self (cons e es))]

    [(or (ESet-member _ _ e0 e1)
         (EMap-lookup _ _ e0 e1)
         (EMap-has-key _ _ e0 e1)
         (EMap-remove _ _ e0 e1))
     (self e0)
     (self e1)]

    [(or (? ERef?) (? EAlloc?) (? EEmpty-Map?) (? EEmpty-Set?)) (void)]
    [_ (error 'populate-expr-rules "Unrecognized expression form: ~a" e)]))

(define (populate-rule-rules vh eh sh rule)
  (match rule
    [(Rule _ name lhs rhs bus)
     (for ([bu (in-list bus)])
       (populate-bu-rules vh eh sh bu))
     (populate-expr-rules vh eh sh rhs)]
    [_ (error 'populate-rule-rules "Bad rule ~a" rule)]))

(define (language->rules R metafunctions)
  (define L (current-language))
  (define us (Language-user-spaces L))

  (define vtag->rule (make-hash))
  (define etag->rule (make-hash))
  (define stag->rule (make-hash))
  (reset-self-referential!)
  (for ([rule (in-list R)])
    (populate-rule-rules vtag->rule etag->rule stag->rule rule))
  (for ([mf (in-list metafunctions)])
    (match-define (Metafunction name τ rules) mf)
    (define-values (names τ* rules*) (open-type-and-rules τ rules))
    (for ([rule (in-list rules*)])
      (populate-rule-rules vtag->rule etag->rule stag->rule rule)))
  (values vtag->rule etag->rule stag->rule))

(define (report-rules vh eh sh)
  (displayln "Variant rules:")
  (pretty-print vh)
  (displayln "~%Extension rules:")
  (pretty-print eh)
  (displayln "~%Set-add rules:")
  (pretty-print sh))

(define (trusted? τ)
  (match τ
    [(or (TVariant: _ _ _ (not (? untrusted?)))
         (Tμ: _ _ _ (not (? untrusted?)) _))
     #t]
    [_ #f]))

(define (heapify-τ vtaddr etaddr staddr heapify-nonrec? τ)
  (define (heap-alloc sy t taddr)
    (match t
      [(? THeap?) t]
      [(? heap-allocate?) (mk-THeap sy taddr 'dc t)]
      [t (self t)]))
  (define (try-alloc? τ tr)
    (and (untrusted? tr)
         (or heapify-nonrec?
             (and (self-referential? τ)
                  (not (trusted? τ))))))
  (define (self τ)
    (match τ
      [(or (? TAddr?) (? TExternal?) (? TFree?) (? TName?) (? THeap?)) τ]
      [(TVariant: sy n ts tr)
       (if (try-alloc? τ tr)
           (mk-TVariant sy n (for/list ([t (in-list ts)])
                               (heap-alloc sy t vtaddr)) tr)
           (mk-TVariant sy n (map self ts) tr))]
      [(TMap: sy t-dom t-rng ext)
       (mk-TMap sy (heap-alloc sy t-dom etaddr) (heap-alloc sy t-rng etaddr) ext)]
      [(TSet: sy tv ext)
       (mk-TSet sy (heap-alloc sy tv staddr) ext)]
      [(Tμ: sy x st tr n)
       (define x* (if (try-alloc? τ tr)
                      (gensym x)
                      (cons 'trusted (gensym x))))
       (mk-Tμ sy x (abstract-free (self (open-scope st (mk-TFree sy x*))) x*) tr n)]
      ;; a quantified type is just all the known instantiations' heapifications.
      [(TΛ: sy x st)
       (mk-TΛ sy x ;; Add a name just so Cuts line up.
              (Scope
               (*TRUnion sy
                         (for/list ([t (in-set (hash-ref (or (instantiations) ⊥) τ ∅))])
                           (self (open-scope st t))))))]
      [(TSUnion: sy ts) (*TSUnion sy (map self ts))]
      [(TRUnion: sy ts) (*TRUnion sy (map self ts))]
      [(TCut: sy t u) (mk-TCut sy (self t) (self u))]
      [(? TBound?) 
       (error 'self-referential? "We shouldn't see deBruijn indices here ~a" τ)]
      [_ (error 'heapify-τ "Bad type ~a" τ)]))
  (self τ))

(define (heapify-language L heapify-nonrec?)
  (define us (Language-ordered-us L))
  (define vtaddr (mk-TAddr #f 'limp 'delay 'structural))
  (define etaddr (mk-TAddr #f 'limp 'delay 'structural))
  (define staddr (mk-TAddr #f 'limp 'delay 'structural))
  (define ordered
    (for/list ([(name ty) (in-dict us)])
      (cons name (heapify-τ vtaddr etaddr staddr
                            heapify-nonrec?
                            ty))))
  ;; We use self-referential checks for heapification, just like expression allocation rules.
  (struct-copy Language L
               [user-spaces (make-hash ordered)]
               [ordered-us ordered]))
