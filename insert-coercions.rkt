#lang racket/base
(require racket/match
         "common.rkt"
         "language.rkt"
         "tast.rkt"
         "types.rkt")
(provide coerce-language)

(define (coerce-pattern pat)
  (define ct (Typed-ct pat))
  (match ct
    [(Deref taddr ct)
     (PDeref (with-stx-stx pat) ct
             (coerce-pattern (pattern-replace-ct ct pat)))]
    [_
     ;; Not immediately dereferencing, so continue structurally
     (match pat
       [(PAnd sy _ ps) (PAnd sy ct (map coerce-pattern ps))]
       [(PName sy _ x) (PName sy ct x)]
       [(PVariant sy _ n ps) (PVariant sy ct n (map coerce-pattern ps))]
        
       [(or (and (PMap-with sy _ k v p) (app (λ _ PMap-with) ctor))
            (and (PMap-with* sy _ k v p) (app (λ _ PMap-with*) ctor)))
        (ctor sy (coerce-pattern k) (coerce-pattern v) (coerce-pattern p))]
        
       [(or (and (PSet-with sy _ v p) (app (λ _ PSet-with) ctor))
            (and (PSet-with* sy _ v p) (app (λ _ PSet-with*) ctor)))
        (ctor sy (coerce-pattern v) (coerce-pattern p))]

       [(PDeref sy _ p) (PDeref sy ct (coerce-pattern p))]

       [(or (? PTerm?) (? PWild?) (? PIsExternal?) (? PIsAddr?) (? PIsType?))
        pat]
       [_ (error 'coerce-pattern "Unsupported pattern: ~a" pat)])]))

(define (do-deref e)
  (define ct (Typed-ct e))
  (match ct
    [(Deref taddr ct)
     (EStore-lookup (with-stx-stx e) ct (expr-replace-ct ct e)
                    (get-option 'lm))]
    [_ #f]))

(define (do-store e)
  (define ct (Typed-ct e))
  (match ct
    [(or (and (Cast (and (THeap: sy taddr tag τ) th)) (app (λ _ Cast) ctor))
         (and (Check (and (THeap: sy taddr tag τ) th)) (app (λ _ Check) ctor)))
     (define esy (with-stx-stx e))
     (define cτ (Check τ))
     (define ctaddr (Check taddr))
     (define x (gensym 'temp))
     (define a (gensym 'tempa))
     (ELet esy
           (Trust τ)
           (list (Where esy
                        (PName esy cτ x)
                        (coerce-expr (expr-replace-ct (Check τ) e)))
                 (Where esy
                        (PName esy ctaddr a)
                        (EAlloc esy ctaddr tag))
                 (Update esy (ERef esy ctaddr a) (ERef esy cτ x)))
           (ERef esy ctaddr a))]
    [_ #f]))


;; Any heapified expression needs a good tag for allocation.
(define (add-tag tag e)
  (define e* (or (do-deref e) e))
  (define ct (Typed-ct e*))
  (match (πct ct)
    [(THeap: sy taddr _ τ)
     (replace-ct (ct-replace-τ ct (mk-THeap sy taddr tag τ)) e*)]
    [_ e]))

(define (coerce-expr e)
  (define e* (do-deref e))
  (if e*
      (coerce-expr e*)
      (or (do-store e)
          ;; Structurally coerce
          (match e
            [(EVariant sy ct n tag τs es)
             (EVariant sy ct n tag τs
                       (for/list ([e (in-list es)]
                                  [i (in-naturals)])
                         (coerce-expr (add-tag (cons tag i) e))))]
            [(EExtend sy ct m tag k v)
             (EExtend sy ct (coerce-expr m) tag
                      (coerce-expr (add-tag (cons tag 0) k))
                      (coerce-expr (add-tag (cons tag 1) v)))]
            [(ESet-add sy ct e tag es)
             (ESet-add sy ct (coerce-expr e) tag
                       (for/list ([e (in-list es)]
                                  [i (in-naturals)])
                         (coerce-expr (add-tag (cons tag i) e))))]

            [(ECall sy ct mf τs es) (ECall sy ct mf τs (map coerce-expr es))]
            [(EStore-lookup sy ct k lm) (EStore-lookup sy ct (coerce-expr k) lm)]
            [(ELet sy ct bus body) (ELet sy ct (map coerce-bu bus) (coerce-expr body))]
            [(EMatch sy ct de rules) (EMatch sy ct (coerce-expr de) (map coerce-rule rules))]
            [(ESet-union sy ct es) (ESet-union sy ct (map coerce-rule es))]
            [(ESet-intersection sy ct e es) (ESet-intersection sy ct (coerce-expr e) (map coerce-expr es))]
            [(ESet-subtract sy ct e es) (ESet-subtract sy ct (coerce-expr e) (map coerce-expr es))]
            [(ESet-member sy ct e v) (ESet-member sy ct (coerce-expr e) (coerce-expr v))]
            [(EMap-lookup sy ct m k) (EMap-lookup sy ct (coerce-expr m) (coerce-expr k))]
            [(EMap-has-key sy ct m k) (EMap-has-key sy ct (coerce-expr m) (coerce-expr k))]
            [(EMap-remove sy ct m k) (EMap-remove sy ct (coerce-expr m) (coerce-expr k))]
            [(or (? ERef?) (? EEmpty-Map?) (? EEmpty-Set?) (? EAlloc?))
             e]
            [_ (error 'coerce-expr "Unrecognized expression form: ~a" e)]))))

(define (coerce-bu bu)
  (match bu
    [(Where sy p e) (Where sy (coerce-pattern p) (coerce-expr e))]
    [(Update sy k e) (Update sy (coerce-expr k) (coerce-expr e))]))

(define (coerce-rule r)
  (match r
    [(Rule sy name lhs rhs bus)
     (Rule sy name (coerce-pattern lhs) (coerce-expr rhs) (map coerce-bu bus))]
    [_ (error 'coerce-rule "Bad rule ~a" r)]))

(define (coerce-metafunction mf)
  (match-define (Metafunction name τ rules) mf)
  (Metafunction name τ (map coerce-rule rules)))

(define (coerce-language R metafunctions)
  (values (map coerce-rule R) (map coerce-metafunction metafunctions)))