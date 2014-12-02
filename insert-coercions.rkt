#lang racket/base
(require racket/match
         racket/trace
         (only-in "alloc-rules.rkt" solidify-τ normalize-taddr)
         "common.rkt"
         "language.rkt"
         "tast.rkt"
         "types.rkt")
(provide coerce-language)

(define (deheapify-ct ct)
  (ct-replace-τ ct (solidify-τ (πct ct))))
(trace deheapify-ct)

(define (coerce-pattern pat)
  (define ct (Typed-ct pat))
  (define ct* (deheapify-ct ct))
  (match ct
    [(Deref taddr ct)
     (PDeref (with-stx-stx pat) ct
             (coerce-pattern (pattern-replace-ct ct pat))
             #f)]
    [_
     ;; Not immediately dereferencing, so continue structurally
     (match pat
       ;; All implicit dereferences become explicit.
       [(PDeref sy _ p imp) (PDeref sy ct* (coerce-pattern p) #f)]
       [(PAnd sy _ ps) (PAnd sy ct* (map coerce-pattern ps))]
       [(PName sy _ x) (PName sy ct* x)]
       [(PVariant sy _ n ps) (PVariant sy ct* n (map coerce-pattern ps))]
        
       [(or (and (PMap-with sy _ k v p) (app (λ _ PMap-with) ctor))
            (and (PMap-with* sy _ k v p) (app (λ _ PMap-with*) ctor)))
        (ctor sy ct* (coerce-pattern k) (coerce-pattern v) (coerce-pattern p))]
        
       [(or (and (PSet-with sy _ v p) (app (λ _ PSet-with) ctor))
            (and (PSet-with* sy _ v p) (app (λ _ PSet-with*) ctor)))
        (ctor sy ct* (coerce-pattern v) (coerce-pattern p))]

       [(or (? PTerm?) (? PWild?) (? PIsExternal?) (? PIsAddr?) (? PIsType?))
        pat]
       [_ (error 'coerce-pattern "Unsupported pattern: ~a" pat)])]))

(define (do-deref e [lm #f])
  (define ct (Typed-ct e))
  (match ct
    ;; Unanticipated lookup (from unannotated semantics)
    [(Deref taddr ct)
     (EStore-lookup (with-stx-stx e)
                    (to-cast ct)
                    (expr-replace-ct (Check (normalize-taddr taddr)) e)
                    (or lm (get-option 'lm))
                    #f)]
    [_
     (match e
       ;; The expression anticipated a lookup
       [(EStore-lookup sy ct k lm #t)
        (define kct (Typed-ct k))
        (match-define (THeap: _ taddr _ τ) (πct kct))
        (define taddr* (normalize-taddr taddr))
        (EStore-lookup sy
                       (Check taddr*)
                       (coerce-expr (replace-ct (ct-replace-τ kct taddr*) k))
                       lm #f)]
       [_ #f])]))

(define (do-store e)
  (define ct (Typed-ct e))
  (match ct
    [(or (and (Cast (and (THeap: sy taddr tag τ) th)) (app (λ _ Cast) ctor))
         (and (Check (and (THeap: sy taddr tag τ) th)) (app (λ _ Check) ctor)))
     (define esy (with-stx-stx e))
     (define cτ (Check τ))
     (define ctaddr (Check (normalize-taddr taddr)))
     (define x (gensym 'temp))
     (define a (gensym 'tempa))
     (ELet esy
           ctaddr
           (list (Where esy
                        (PName esy cτ x)
                        (coerce-expr (expr-replace-ct (Check τ) e)))
                 (Where esy
                        (PName esy ctaddr a)
                        (EAlloc esy ctaddr tag))
                 (Update esy (ERef esy ctaddr a) (ERef esy cτ x)))
           (ERef esy ctaddr a))]
    [_ #f]))

(define (coerce-expr e)
  (define e* (do-deref e))
  (if e*
      (coerce-expr e*)
      (or (do-store e)
          (match e
            ;; 
            [(EStore-lookup sy ct k lm imp)
             (when imp (error 'coerce-expr "Must be done with do-deref ~a" e))
             (EStore-lookup sy (deheapify-ct ct) (coerce-expr k) lm #f)]
            ;; Structurally coerce
            [(EVariant sy ct n tag τs es)
             (EVariant sy (deheapify-ct ct) n tag τs (map coerce-expr es))]
            [(EExtend sy ct m tag k v)
             (EExtend sy (deheapify-ct ct) (coerce-expr m) tag
                      (coerce-expr k)
                      (coerce-expr v))]
            [(ESet-add sy ct e tag es)
             (ESet-add sy (deheapify-ct ct) (coerce-expr e) tag
                       (map coerce-expr es))]

            [(ECall sy ct mf τs es) (ECall sy (deheapify-ct ct) mf τs (map coerce-expr es))]
            [(ELet sy ct bus body) (ELet sy (deheapify-ct ct) (map coerce-bu bus) (coerce-expr body))]
            [(EMatch sy ct de rules) (EMatch sy (deheapify-ct ct) (coerce-expr de) (map coerce-rule rules))]
            [(ESet-union sy ct es) (ESet-union sy (deheapify-ct ct) (map coerce-rule es))]
            [(ESet-intersection sy ct e es) (ESet-intersection sy (deheapify-ct ct) (coerce-expr e) (map coerce-expr es))]
            [(ESet-subtract sy ct e es) (ESet-subtract sy (deheapify-ct ct) (coerce-expr e) (map coerce-expr es))]
            [(ESet-member sy ct e v) (ESet-member sy (deheapify-ct ct) (coerce-expr e) (coerce-expr v))]
            [(EMap-lookup sy ct m k) (EMap-lookup sy (deheapify-ct ct) (coerce-expr m) (coerce-expr k))]
            [(EMap-has-key sy ct m k) (EMap-has-key sy (deheapify-ct ct) (coerce-expr m) (coerce-expr k))]
            [(EMap-remove sy ct m k) (EMap-remove sy (deheapify-ct ct) (coerce-expr m) (coerce-expr k))]
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
