#lang racket/base
(require "common.rkt"
         "language.rkt"
         "self-reference.rkt"
         "tast.rkt"
         "type-formers.rkt"
         "types.rkt"
         racket/dict
         racket/set
         racket/match
         racket/pretty
         racket/trace)
(provide language->rules report-rules heapify-language
         heapify-rules
         normalize-taddr solidify-τ solidify-language)

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
    [(or (When _ e) (Unless _ e)) (populate-expr-rules vh eh sh e)]
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
    [(EStore-lookup _ _ e _ _)
     (self e)]

    [(ELet _ _ bus body)
     (for ([bu (in-list bus)])
       (populate-bu-rules vh eh sh bu))
     (populate-expr-rules vh eh sh body)]
    [(EMatch _ _ de rules)
     (self de)
     (for ([rule (in-list rules)])
       (populate-rule-rules vh eh sh rule))]

    [(EIf _ _ g th el)
     (self g)
     (self th)
     (self el)]
    
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

    [(or (? ERef?) (? EAlloc?) (? EEmpty-Map?) (? EEmpty-Set?) (? EExternal?)) (void)]
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
      [(? heap-allocate?) (mk-THeap sy taddr #f t)]
      [t (self t)]))
  (define (try-alloc? τ tr)
    (and (untrusted? tr)
         (or heapify-nonrec?
             (and (self-referential? τ)
                  (not (trusted? τ))))))
  (define (self τ)
    (match τ
      [(or (? TAddr?) (? TExternal?) (? TFree?) (? TName?) (? THeap?)) τ]
      [(? T⊤?) (mk-THeap #f limp-default-rec-addr #f τ)]
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
;       (printf "From heapify ~a~%" x*)
       (mk-Tμ sy x (abstract-free (self (open-scope st (mk-TFree sy x*))) x*) tr n)]
      ;; a quantified type will be heapified at application time
      [(TΛ: sy x st _) (mk-TΛ sy x st (λ (t)
                                         (printf "Applied and became ~a: heapifing ...~%" t)
                                         (define t* (self t))
                                         (printf "Done ~a~%" t*)
                                         t*))]
      [(TUnion: sy ts) (*TUnion sy (map self ts))]
      [(TCut: sy t u) (mk-TCut sy (self t) (self u))]
      [(TWeak: sy t) (mk-TWeak sy (self t))]
      [(TUnif _ t)
       (define τ* (self t))
       (set-TUnif-τ! τ τ*)
       τ*]
      [(? TBound?) 
       (error 'self-referential? "We shouldn't see deBruijn indices here ~a" τ)]
      [_ (error 'heapify-τ "Bad type ~a" τ)]))
  (parameterize ([heapifying? #t]) (self τ)))
;(trace heapify-τ)

(define (heapify-language L heapify-nonrec?)
  (define us (Language-ordered-us L))
  (define vtaddr limp-default-deref-addr)
  (define etaddr limp-default-deref-addr)
  (define staddr limp-default-deref-addr)
  (define ordered
    (for/list ([(name ty) (in-dict us)])
      (cons name (heapify-τ vtaddr etaddr staddr
                            heapify-nonrec?
                            ty))))
  ;; We use self-referential checks for heapification, just like expression allocation rules.
  (struct-copy Language L
               [user-spaces (make-hash ordered)]
               [ordered-us ordered]))

(define (heapify-ct vtaddr etaddr staddr heapify-nonrec?)
  (define hτ (λ (τ) (heapify-τ vtaddr etaddr staddr heapify-nonrec? τ)))
  (λ (ct) (and ct (ct-replace-τ ct (hτ (πct ct))))))
;; All explicit annotations should also be heapified

(define (heapify-expr vtaddr etaddr staddr heapify-nonrec?)
  (define hτ (λ (τ) (heapify-τ vtaddr etaddr staddr heapify-nonrec? τ)))
  (define hbus (heapify-bus vtaddr etaddr staddr heapify-nonrec?))
  (define hrules (heapify-rules vtaddr etaddr staddr heapify-nonrec?))
  (define hct (heapify-ct vtaddr etaddr staddr heapify-nonrec?))
  (define (hannot τs)
    (and (list? τs) (for/list ([τ (in-list τs)]) (and τ (hτ τ)))))
  (define (self e)
    (define ct (Typed-ct e))
    (define ct* (hct ct))
    (match e
      [(ECall sy _ mf τs es)
       (ECall sy ct* mf (hannot τs) (map self es))]
      [(EVariant sy _ n tag τs es)
       (EVariant sy ct* n tag (hannot τs) (map self es))]
      [(ERef sy _ x) (ERef sy ct* x)]
      [(EStore-lookup sy _ k lm imp) (EStore-lookup sy ct* (self k) lm imp)]
      [(EAlloc sy _ tag) (EAlloc sy ct* tag)]
      [(ELet sy _ bus body) (ELet sy ct* (hbus bus) (self body))]
      [(EMatch sy _ de rules) (EMatch sy ct* (self de) (hrules rules))]
      [(EExtend sy _ m tag k v) (EExtend sy ct* (self m) tag (self k) (self v))]
      [(EEmpty-Map sy _) (EEmpty-Map sy ct*)]
      [(EEmpty-Set sy _) (EEmpty-Set sy ct*)]
      [(ESet-union sy _ es) (ESet-union sy ct* (map self es))]
      [(ESet-add sy _ e tag es) (ESet-add sy ct* (self e) tag (map self es))]
      [(ESet-intersection sy _ e es) (ESet-intersection sy ct* (self e) (map self es))]
      [(ESet-subtract sy _ e es) (ESet-subtract sy ct* (self e) (map self es))]
      [(ESet-member sy _ e v) (ESet-member sy ct* (self e) (self v))]
      [(EMap-lookup sy _ m k) (EMap-lookup sy ct* (self m) (self k))]
      [(EMap-has-key sy _ m k) (EMap-has-key sy ct* (self m) (self k))]
      [(EMap-remove sy _ m k) (EMap-remove sy ct* (self m) (self k))]
      [(EHeapify sy _ e taddr tag) (EHeapify sy ct* (self e) taddr tag)]
      [(EUnquote sy _ e) (EUnquote sy ct* e)]
      [(EExternal sy _ v) (EExternal sy ct* v)]
      [_ (error 'heapify-expr "Unrecognized expression form: ~a" e)]))
  self)

(define (heapify-term vtaddr etaddr staddr heapify-nonrec?)
  (define hct (heapify-ct vtaddr etaddr staddr heapify-nonrec?))
  (define (self t)
    (define ct* (hct (Typed-ct t)))
    (match t
      [(Variant sy _ n ts) (Variant sy ct* n (map self ts))]
      [(Map sy _ f) (Map sy ct* (for/hash ([(k v) (in-hash f)])
                                  (values (self k) (self v))))]
      [(Set sy _ s) (Set sy ct* (for/set ([v (in-set s)])
                                  (self v)))]
      [(External sy _ v) (External sy ct* v)]
      [_ (error 'heapify-term "Unsupported term ~a" t)]))
  self)

(define (heapify-pattern vtaddr etaddr staddr heapify-nonrec?)
  (define ht (heapify-term vtaddr etaddr staddr heapify-nonrec?))
  (define hct (heapify-ct vtaddr etaddr staddr heapify-nonrec?))
  (define (self pat)
    (define ct* (hct (Typed-ct pat)))
    (match pat
      [(PName sy _ x p) (PName sy ct* x (self p))]
      [(PWild sy _) (PWild sy ct*)]
      [(PVariant sy _ n ps) (PVariant sy ct* n (map self ps))]
      [(PMap-with sy _ k v p) (PMap-with sy ct* (self k) (self v) (self p))]
      [(PMap-with* sy _ k v p) (PMap-with* sy ct* (self k) (self v) (self p))]
      [(PSet-with sy _ v p) (PSet-with sy ct* (self v) (self p))]
      [(PSet-with* sy _ v p) (PSet-with* sy ct* (self v) (self p))]
      [(PTerm sy _ t) (PTerm sy ct* (ht t))]
      [(PDeref sy _ p taddr imp) (PDeref sy ct* (self p) taddr imp)]
      [(PIsType sy _ p) (PIsType sy ct* (self p))]
      [_ (error 'heapify-pat "Unsupported pattern: ~a" pat)]))
  self)

(define ((heapify-bus vtaddr etaddr staddr heapify-nonrec?) bus)
  (map (heapify-bu vtaddr etaddr staddr heapify-nonrec?) bus))
(define (heapify-bu vtaddr etaddr staddr heapify-nonrec?)
  (define he (heapify-expr vtaddr etaddr staddr heapify-nonrec?))
  (λ (bu)
   (match bu
     [(Where sy pat e)
      (Where sy
             (heapify-pattern vtaddr etaddr staddr heapify-nonrec? pat)
             (he e))]
     [(Update sy k v) (Update sy (he k) (he v))])))

(define ((heapify-rules vtaddr etaddr staddr heapify-nonrec?) rules)
  (map (heapify-rule vtaddr etaddr staddr heapify-nonrec?) rules))
(define (heapify-rule vtaddr etaddr staddr heapify-nonrec?)
  (define hpat (heapify-pattern vtaddr etaddr staddr heapify-nonrec?))
  (define he (heapify-expr vtaddr etaddr staddr heapify-nonrec?))
  (define hbus (heapify-bus vtaddr etaddr staddr heapify-nonrec?))
  (match-lambda
   [(Rule sy name pat e bus) (Rule sy name (hpat pat) (he e) (hbus bus))]))

(define (normalize-taddr taddr)
  (match-define (TAddr: sy space mm em) taddr)
  (mk-TAddr sy
            (or space (get-option 'addr-space))
            (or mm (get-option 'mm))
            (or em (get-option 'em))))

;; Take off THeap annotations and just replace with the TAddr.
(define (solidify-τ τ)
  (match τ
    [(THeap: _ taddr _ _) (normalize-taddr taddr)]
    [(or (? TAddr?) (? TExternal?) (? TFree?) (? TName?) (? TBound?)) τ]
    [(TVariant: sy n ts tr) (mk-TVariant sy n (map solidify-τ ts) tr)]
    [(TMap: sy t-dom t-rng ext)
     (mk-TMap sy (solidify-τ t-dom) (solidify-τ t-rng) ext)]
    [(TSet: sy tv ext) (mk-TSet sy (solidify-τ tv) ext)]
    [(Tμ: sy x (Scope t) tr n)
     (mk-Tμ sy x (Scope (solidify-τ t)) tr n)]
    [(TΛ: sy x (Scope t) h)
     (mk-TΛ sy x (Scope (solidify-τ t)) h)]
    [(TUnion: sy ts) (*TUnion sy (map solidify-τ ts))]
    [(TWeak: sy t) (mk-TWeak sy (solidify-τ t))]
    [(TCut: sy t u) (mk-TCut sy (solidify-τ t) (solidify-τ u))]
    [(? T⊤?) T⊤]
    [_ (error 'solidify-τ "Bad type ~a" τ)]))
;(trace solidify-τ)

(define (solidify-language L)
  (define us (Language-ordered-us L))
  (define ordered
    (for/list ([(name ty) (in-dict us)])
;      (printf "Solidifying ~a, ~a~%" name ty)
      (cons name (solidify-τ ty))))
  (struct-copy Language L
               [user-spaces (make-hash ordered)]
               [ordered-us ordered]))
