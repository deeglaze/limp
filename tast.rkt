#lang racket/base
(require racket/match racket/set "language.rkt" "common.rkt" "types.rkt")
#|
This module provides the structs that the Limp compiler uses to typecheck an input language
and semantics.
|#

(provide (all-defined-out))

(struct with-stx (stx) #:transparent)
(struct Typed with-stx (ct) #:transparent)
(define πcc (match-lambda
             [(Typed _ ct) (πct ct)]
             [_ #f]))

(define (replace-ct ct v)
  (cond [(Pattern? v) (pattern-replace-ct ct v)]
        [(Expression? v) (expr-replace-ct ct v)]
        [(Term? v) (term-replace-ct ct v)]
        [else (error 'replace-ct "Unsupported value: ~a" v)]))

(define pattern-print-verbosity (make-parameter 0))
(define term-print-verbosity (make-parameter 0))
(define expr-print-verbosity (make-parameter 0))

(define (ann-wrap ct sexp)
  (match ct
    [#f sexp]
    [(Check σ) `(#:ann ,(type->sexp σ) ,sexp)]
    [(Cast σ) `(#:cast ,(type->sexp σ) ,sexp)]
    [(Deref taddr ct) `(#:after-deref ,(type->sexp taddr) ,(ann-wrap ct sexp))]
    [_ `(error$ 'ann-wrap ,(format "Bad ct: ~a" ct))]))

;; Elaborated patterns
(define (pattern->sexp p)
  (define v (pattern-print-verbosity))
  (let rec ([p p])
    (define sexp
      (match p
        [(PName _ _ x p) (if (PWild? p) x `(#:name ,x ,(rec p)))]
        [(PWild _ _) '_]
        [(PVariant _ _ n (? list? ps)) `(,n . ,(map rec ps))]
        [(PMap-with _ _ k v p) `(#:map-with ,(rec k)
                                            ,(rec v)
                                            ,(rec p))]
        [(PMap-with* _ _ k v p) `(#:map-with* ,(rec k)
                                              ,(rec v)
                                              ,(rec p))]
        [(PSet-with _ _ v p) `(#:set-with ,(rec v)
                                          ,(rec p))]
        [(PSet-with* _ _ v p) `(#:set-with* ,(rec v)
                                            ,(rec p))]
        [(PDeref _ _ p taddr imp) `(#:deref ,(rec p)
                                            ,@(if taddr (list taddr) '())
                                            ,@(if imp '(#:implicit) '()))]
        [(PTerm _ _ t) `(#:term ,(term->sexp t))]
        ;; printer will handle τ
        [(PIsType _ ct p) `(#:is-type ,(πct ct) ,@(if (PWild? p) '() (list (rec p))))]
        [_ `(error$ ,(format "Unsupported pattern: ~a" (struct->vector p)))]))
    (case v
      [(0) sexp]
      [(1) (ann-wrap (Typed-ct p) sexp)]
      [else (parameterize ([type-print-verbosity (sub1 v)])
              (ann-wrap (Typed-ct p) sexp))])))

(define (pattern-replace-ct ct p)
   (match p
     [(PName sy _ x p) (PName sy ct x p)]
     [(PWild sy _) (PWild sy ct)]
     [(PVariant sy _ n ps) (PVariant sy ct n ps)]
     [(PMap-with sy _ k v p) (PMap-with sy ct k v p)]
     [(PMap-with* sy _ k v p) (PMap-with* sy ct k v p)]
     [(PSet-with sy _ v p) (PSet-with sy ct v p)]
     [(PSet-with* sy _ v p) (PSet-with* sy ct v p)]
     [(PTerm sy _ t) (PTerm sy ct t)]
     [(PIsType sy _ p) (PIsType sy ct p)]
     [_ (error 'pattern-replace-ct "Unsupported pattern: ~a" p)]))

(define (write-pattern pat port mode)
  (display (pattern->sexp pat) port))

(struct Pattern Typed () #:transparent
        #:methods gen:custom-write [(define write-proc write-pattern)])
(struct PName Pattern (x p) #:transparent)
(struct PWild Pattern () #:transparent)
(struct PVariant Pattern (n ps) #:transparent)
(struct PMap-with Pattern (k v p) #:transparent)
(struct PMap-with* Pattern (k v p) #:transparent)
(struct PSet-with Pattern (v p) #:transparent)
(struct PSet-with* Pattern (v p) #:transparent)
(struct PTerm Pattern (t) #:transparent)
;; Expect an address always, so deref and continue matching.
(struct PDeref Pattern (p taddr implicit?) #:transparent)
;; The info is in the type
(struct PIsType Pattern (p) #:transparent)
#|
pattern template:
 (match pat
    [(PName sy ct x p) ???]
    [(PWild sy ct) ???]
    [(PVariant sy ct n ps) ???]
    [(PMap-with sy ct k v p) ???]
    [(PMap-with* sy ct k v p) ???]
    [(PSet-with sy ct v p) ???]
    [(PSet-with* sy ct v p) ???]
    [(PTerm sy ct t) ???]
    [(PDeref sy ct p taddr imp?) ???]
    [(PIsType sy ct p) ???]
    [_ (error who "Unsupported pattern: ~a" pat)])
|#

(define (pattern-α-equal? pat0 pat1 ρ0 ρ1)
  (define (sequence-pattern-α-equal? ps0 ps1 ρ0 ρ1)
    (match* (ps0 ps1)
      [('() '()) (values ρ0 ρ1 #t)]
      [((cons p0 ps0) (cons p1 ps1))
       (define-values (ρ0* ρ1* r) (pattern-α-equal? p0 p1 ρ0 ρ1))
       (if r
           (sequence-pattern-α-equal? ps0 ps1 ρ0* ρ1*)
           (values ρ0 ρ1 #f))]
      [(_ _) (values ρ0 ρ1 #f)]))

  (match* (pat0 pat1)
    [((PName _ ct x0 p0) (PName _ ct x1 p1))
     (match (hash-ref ρ0 x0 #f)
       [#f (if (hash-has-key? ρ1 x1)
               (pattern-α-equal? ρ0 ρ1 p0 p1)
               ;; both unmapped. Freshen to same name.
               (let ([f (gensym)])
                 (pattern-α-equal? (hash-set ρ0 x0 f)
                                   (hash-set ρ1 x1 f)
                                   p0 p1)))]
       [x0* (match (hash-ref ρ1 x1 #f)
              [#f (pattern-α-equal? ρ0 ρ1 p0 p1)]
              [x1* (if (eq? x0* x1*)
                       (pattern-α-equal? ρ0 ρ1 p0 p1)
                       (values ρ0 ρ1 #f))])])]
    [((PVariant _ ct n ps0) (PVariant _ ct n ps1))
     (sequence-pattern-α-equal? ps0 ps1 ρ0 ρ1)]
    [((PMap-with _ ct k0 v0 p0) (PMap-with _ ct k1 v1 p1))
     (sequence-pattern-α-equal? (list k0 v0 p0) (list k1 v1 p1) ρ0 ρ1)]
    [((PMap-with* _ ct k0 v0 p0) (PMap-with* _ ct k1 v1 p1))
     (sequence-pattern-α-equal? (list k0 v0 p0) (list k1 v1 p1) ρ0 ρ1)]
    [((PSet-with _ ct v0 p0) (PSet-with _ ct v1 p1))
     (sequence-pattern-α-equal? (list v0 p0) (list v1 p1) ρ0 ρ1)]
    [((PSet-with* _ ct v0 p0) (PSet-with* _ ct v1 p1))
     (sequence-pattern-α-equal? (list v0 p0) (list v1 p1) ρ0 ρ1)]
    [((PTerm _ ct t0) (PTerm _ ct t1)) (values ρ0 ρ1 (term-α-equal? t0 t1))]
    [((PDeref _ ct p0 taddr imp) (PDeref _ ct p1 taddr imp)) (pattern-α-equal? p0 p1)]
    [((PWild _ ct) (PWild _ ct)) (values ρ0 ρ1 #t)]
    [((PIsType _ ct p0) (PIsType _ ct p1))
     (pattern-α-equal? ρ0 ρ1 p0 p1)]
    [(_ _) (values ρ0 ρ1 #f)]))

;; Elaborated Terms
(define (term->sexp t)
  ;; TODO: annotations based on verbosity.
  (match t
    [(Variant sy ct n ts) `(,n . ,(map term->sexp ts))]
    [(Map sy ct f) (for/fold ([t '#:empty-map])
                    ([(k v) (in-hash f)])
                  `(#:extend ,t ,(term->sexp k) ,(term->sexp v)))]
    [(Set sy ct s) (for/fold ([t '#:empty-set])
                    ([v (in-set s)])
                  `(#:add ,t ,(term->sexp v)))]
    [(External _ (Check (TExternal: _ name)) v) `(#:external ,name ,v)]
    [_ `(error$ ,(format "Unsupported term ~a" t))]))

(define (term-replace-ct ct t)
  (match t
    [(Variant sy _ n ts) (Variant sy ct n ts)]
    [(Map sy _ f) (Map sy ct f)]
    [(Set sy _ s) (Set sy ct s)]
    [(External sy _ v) (External sy ct v)]
    [_ (error 'term-replace-ct "Unsupported term ~a" t)]))

(define (term-α-equal? t0 t1)
  (match* (t0 t1)
    [((Variant _ ct n ts0) (Variant _ ct n ts1))
     (andmap term-α-equal? ts0 ts1)]
    [((Map _ ct f0) (Map _ ct f1))
     (define (msub m0 m1)
       (for/and ([(k0 v0) (in-hash f0)])
         (for/or ([(k1 v1) (in-hash f1)])
           (and (term-α-equal? k0 k1)
                (term-α-equal? v0 v1)))))
     (and (msub f0 f1) (msub f1 f0))]
    [((Set _ ct s0) (Set _ ct s1))
     (define (ssub s0 s1)
       (for/and ([t0 (in-set s0)])
         (for/or ([t1 (in-set s1)])
           (term-α-equal? t0 t1))))
     (and (ssub s0 s1) (ssub s1 s0))]
    ;; Externals must be `equal?`
    [((External _ ct v) (External _ ct v)) #t]
    [(_ _) #f]))

(define (write-term t port mode)
  (display (term->sexp t) port))

(struct Term Typed () #:transparent
        #:methods gen:custom-write [(define write-proc write-term)])
(struct Variant Term (n ts) #:transparent)
(struct Map Term (f) #:transparent)
(struct Set Term (s) #:transparent)
(struct External Term (v) #:transparent)

#|
term template
 (match t
    [(Variant sy ct n ts) ???]
    [(Map sy ct f) ???]
    [(Set sy ct s) ???]
    [(External sy ct v) ???]
    [_ (error who "Unsupported term ~a" t)])
|#

(define (expr->sexp e)
  (define (do-tag tag) 
    ;; only show implicit tags in verbosity > 1
    (if (and tag (or (> v 1) (not (implicit-tag? tag))))
        `(#:tag ,tag)
        '()))
  (define v (expr-print-verbosity))
  (let rec ([e e])
    (define sexp
      (match e
        [(ECall _ _ mf τs es) `(,mf . ,(map rec es))]
        [(EVariant _ _ n tag τs es) `(,n ,@(do-tag tag) . ,(map rec es))]
        [(ERef _ _ x) x]
        [(EStore-lookup _ _ k lm imp) `(#:lookup ,(rec k) ,(and lm (s->k lm)) ,@(if imp `(#:implicit ,imp) '()))]
        [(EAlloc _ (Check (TAddr: _ space mm em)) tag)
         `(#:alloc ,@(do-tag tag) ,space ,(and mm (s->k mm)) ,(and em (s->k em)))]
        [(ELet _ _ bus body) `(#:let ,(map bu->sexp bus) ,(rec body))]
        [(ELetrec _ _ mfs body) `(#:letrec ,(map mf->sexp mfs) ,(rec body))]
        [(EMatch _ _ de rules) `(#:match ,(rec de) . ,(map (rule->sexp #f) rules))]
        [(EIf _ _ g t e) `(#:if ,(rec g) ,(rec t) ,(rec e))]
        [(EExtend _ _ m tag k v)
         `(#:extend ,(rec m) ,@(do-tag tag) ,(rec k) ,(rec v))]
        [(EEmpty-Map _ _) '#:empty-map]
        [(EEmpty-Set _ _) '#:empty-set]
        [(ESet-union _ _ es) `(#:union . ,(map rec es))]
        [(ESet-add _ _ e tag es) `(#:set-add ,(rec e) ,@(do-tag tag) . ,(map rec es))]
        [(ESet-intersection _ _ e es) `(#:intersection ,(rec e) . ,(map rec es))]
        [(ESet-subtract _ _ e es) `(#:subtract ,(rec e) . ,(map rec es))]
        [(ESet-member _ _ e v) `(#:member? ,(rec e) ,(rec v))]
        [(EMap-lookup _ _ m k) `(#:map-lookup ,(rec m) ,(rec k))]
        [(EMap-has-key _ _ m k) `(#:has-key? ,(rec m) ,(rec k))]
        [(EMap-remove _ _ m k) `(#:map-remove ,(rec m) ,(rec k))]
        [(EHeapify _ _ e taddr tag) `(#:addrize ,(rec e) ,taddr ,@(do-tag tag))]
        [(EUnquote _ _ e) `(#:unquote ,e)]
        [(EExternal _ (Check t) e) `(#:external ,t ,e)]
        [_ `(error$ ,(format "Unrecognized expression form: ~a" e))]))
    (case v
      [(0) sexp]
      [(1) (ann-wrap (Typed-ct e) sexp)]
      [else (parameterize ([type-print-verbosity (sub1 v)])
              (ann-wrap (Typed-ct e) sexp))])))

(define (expr-replace-ct ct e)
  (match e
    [(ECall sy _ mf τs es) (ECall sy ct mf τs es)]
    [(EVariant sy _ n tag τs es) (EVariant sy ct n tag τs es)]
    [(ERef sy _ x) (ERef sy ct x)]
    [(EStore-lookup sy _ k lm imp) (EStore-lookup sy ct k lm imp)]
    [(EAlloc sy _ tag) (EAlloc sy ct tag)]
    [(ELet sy _ bus body) (ELet sy ct bus body)]
    [(ELetrec sy _ mfs body) (ELetrec sy ct mfs body)]
    [(EMatch sy _ de rules) (EMatch sy ct de rules)]
    [(EIf sy _ g t e) (EIf sy g t e)]
    [(EExtend sy _ m tag k v) (EExtend sy ct m tag k v)]
    [(EEmpty-Map sy _) (EEmpty-Map sy ct)]
    [(EEmpty-Set sy _) (EEmpty-Set sy ct)]
    [(ESet-union sy _ es) (ESet-union sy ct es)]
    [(ESet-add sy _ e tag es) (ESet-add sy ct e tag es)]
    [(ESet-intersection sy _ e es) (ESet-intersection sy ct e es)]
    [(ESet-subtract sy _ e es) (ESet-subtract sy ct e es)]
    [(ESet-member sy _ e v) (ESet-member sy ct e v)]
    [(EMap-lookup sy _ m k) (EMap-lookup sy ct m k)]
    [(EMap-has-key sy _ m k) (EMap-has-key sy ct m k)]
    [(EMap-remove sy _ m k) (EMap-remove sy ct m k)]
    [(EHeapify sy _ e taddr tag) (EHeapify sy ct e taddr tag)]
    [(EUnquote sy _ e) (EUnquote sy ct e)]
    [(EExternal sy _ v) (EExternal sy ct v)]
    [_ (error 'expr-replace-ct "Unrecognized expression form: ~a" e)]))

(define (write-expr e port mode)
  (display (expr->sexp e) port))

;; Expressions
(struct Expression Typed () #:transparent
        #:methods gen:custom-write [(define write-proc write-expr)])
(struct Map-Expression Expression () #:transparent)
(struct Set-Expression Expression () #:transparent)

(struct ECall Expression (mf τs es) #:transparent)
(struct EVariant Expression (n tag τs es) #:transparent)
(struct ERef Expression (x) #:transparent)
;; lm ::= 'resolve | 'delay | 'deref
;; An implicit store lookup is k pre-heapification, and the lookup post-
(struct EStore-lookup Expression (k lm op-implicit) #:transparent)
;; TODO: add a "ghost" store lookup that is identity concretely,
;;       but expects to need a deref in the transform.
;;       It exists to change the default deref behavior.
(struct EAlloc Expression (tag) #:transparent) ;; space mm em in type
(struct ELet Expression (bus body) #:transparent)
(struct ELetrec Expression (mfs body) #:transparent) ;; Local metafunctions
(struct EMatch Expression (discriminant rules) #:transparent)
(struct EIf Expression (g t e) #:transparent)
(struct EExternal Expression (v) #:transparent)

(struct EExtend Map-Expression (m tag k v) #:transparent)
(struct EEmpty-Map Map-Expression () #:transparent)
(struct EEmpty-Set Set-Expression () #:transparent)
(struct ESet-add Set-Expression (s tag v) #:transparent)
;; For heap-allocation annotations and algebraic eliminations
(struct EUnquote Expression (e) #:transparent)
(struct EHeapify Expression (e taddr tag) #:transparent)
;; utility expressions
(struct ESet-union Set-Expression (es) #:transparent)
(struct ESet-intersection Set-Expression (e es) #:transparent)
(struct ESet-subtract Set-Expression (e es) #:transparent)
(struct ESet-remove Set-Expression (e es) #:transparent)
(struct ESet-member Set-Expression (e v) #:transparent)
(struct EMap-lookup Map-Expression (m k) #:transparent)
(struct EMap-has-key Map-Expression (m k) #:transparent)
(struct EMap-remove Map-Expression (m k) #:transparent)
(struct implicit-tag (tag) #:prefab)
#|
expr template
 (match e
    [(ECall sy ct mf τs es) ???]
    [(EVariant sy ct n tag τs es) ???]
    [(ERef sy ct x) ???]
    [(EStore-lookup sy ct k lm imp) ???]
    [(EAlloc sy ct tag) ???]
    [(ELet sy ct bus body) ???]
    [(ELetrec sy ct mfs body) ???]
    [(EMatch sy ct de rules) ???]
    [(EIf sy ct g t e) ???]
    [(EExtend sy ct m tag k v) ???]
    [(EEmpty-Map sy ct) ???]
    [(EEmpty-Set sy ct) ???]
    [(ESet-union sy ct es) ???]
    [(ESet-add sy ct e tag es) ???]
    [(ESet-intersection sy ct e es) ???]
    [(ESet-subtract sy ct e es) ???]
    [(ESet-member sy ct e v) ???]
    [(EMap-lookup sy ct m k) ???]
    [(EMap-has-key sy ct m k) ???]
    [(EMap-remove sy ct m k) ???]
    [(EHeapify sy ct m taddr tag) ???]
    [(EUnquote sy ct e) ???]
    [(EExternal sy ct v) ???]
    [_ (error who "Unrecognized expression form: ~a" e)])
|#

(define (expr-α-equal? e0 e1 [ρ0 #hasheq()] [ρ1 #hasheq()])
  (define (equal*? es0 es1)
    (for/and ([e0 (in-list es0)]
              [e1 (in-list es1)])
      (expr-α-equal? e0 e1 ρ0 ρ1)))
  (match* (e0 e1)
    ;; ct, τs uses type equality after structural equality.
    ;; mf and tag must be `equal?`
    ;; es0 and es1 need recursion
    [((ECall _ ct mf τs es0)
      (ECall _ ct mf τs es1))
     (equal*? es0 es1)]
    [((EVariant _ ct n tag τs es0)
      (EVariant _ ct n tag τs es1)) ;; SAME NAME ONLY
     (equal*? es0 es1)]
    [((ERef _ ct x) (ERef _ ct y))
     (eq? (hash-ref ρ0 x x)
          (hash-ref ρ1 y y))]
    [((EStore-lookup _ ct k0 lm imp)
      (EStore-lookup _ ct k1 lm imp))
     (expr-α-equal? k0 k1 ρ0 ρ1)]
    [((EAlloc _ ct tag) (EAlloc _ ct tag)) #t]
    [((ELet _ ct bus0 body0) (ELet _ ct bus1 body1))
     (define-values (ρ0* ρ1* r) (bus-α-equal? bus0 bus1 ρ0 ρ1))
     (and r (expr-α-equal? body0 body1 ρ0* ρ1*))]
    [((ELetrec _ ct mfs0 body0) (ELetrec _ ct mfs1 body1))
     (and (mfs-α-equal? mfs0 mfs1 ρ0 ρ1)
          (expr-α-equal? body0 body1 ρ0 ρ1))]
    [((EMatch _ ct de0 rules0) (EMatch _ ct de1 rules1))
     (and (expr-α-equal? de0 de1 ρ0 ρ1)
          (for/and ([rule0 (in-list rules0)]
                    [rule1 (in-list rules1)])
            (rule-α-equal? rule0 rule1 ρ0 ρ1)))]
    [((EIf _ ct g0 t0 e0) (EIf _ ct g1 t1 e1))
     (and (expr-α-equal? g0 g1 ρ0 ρ1)
          (expr-α-equal? t0 t1 ρ0 ρ1)
          (expr-α-equal? e0 e1 ρ0 ρ1))]
    [((EExtend _ ct m0 tag k0 v0) (EExtend _ ct m1 tag k1 v1))
     (and (expr-α-equal? m0 m1 ρ0 ρ1)
          (expr-α-equal? k0 k1 ρ0 ρ1)
          (expr-α-equal? v0 v1 ρ0 ρ1))]
    [((EEmpty-Map _ ct) (EEmpty-Map _ ct)) #t]
    [((EEmpty-Set _ ct) (EEmpty-Set _ ct)) #t]
    [((ESet-union _ ct es0) (ESet-union _ ct es1))
     (equal*? es0 es1)]
    [((ESet-add _ ct e0 tag es0) (ESet-add _ ct e1 tag es1))
     (and (expr-α-equal? e0 e1 ρ0 ρ1)
          (equal*? es0 es1))]
    [((ESet-intersection _ ct e0 es0) (ESet-intersection _ ct e1 es1))
     (and (expr-α-equal? e0 e1 ρ0 ρ1)
          (equal*? es0 es1))]
    [((ESet-subtract _ ct e0 es0) (ESet-subtract _ ct e1 es1))
     (and (expr-α-equal? e0 e1 ρ0 ρ1)
          (equal*? es0 es1))]
    [((ESet-member _ ct e0 v0) (ESet-member _ ct e1 v1))
     (and (expr-α-equal? e0 e1 ρ0 ρ1)
          (expr-α-equal? v0 v1 ρ0 ρ1))]
    [((EMap-lookup _ ct m0 k0) (EMap-lookup _ ct m1 k1))
     (and (expr-α-equal? m0 m1 ρ0 ρ1)
          (expr-α-equal? k0 k1 ρ0 ρ1))]
    [((EMap-has-key _ ct m0 k0) (EMap-has-key _ ct m1 k1))
     (and (expr-α-equal? m0 m1 ρ0 ρ1)
          (expr-α-equal? k0 k1 ρ0 ρ1))]
    [((EMap-remove _ ct m0 k0) (EMap-remove _ ct m1 k1))
     (and (expr-α-equal? m0 m1 ρ0 ρ1)
          (expr-α-equal? k0 k1 ρ0 ρ1))]
    [((EHeapify _ ct e0 taddr tag) (EHeapify _ ct e1 taddr tag))
     (expr-α-equal? e0 e1 ρ0 ρ1)]
    [((EUnquote _ ct e) (EUnquote _ ct e)) #t]
    [((EExternal _ ct v) (EExternal _ ct v)) #t]
    [(_ _) #f]))

;; Binding updates
(define (bu->sexp bu)
  (match bu
    [(Update _ k v) `(#:update ,(expr->sexp k) ,(expr->sexp v))]
    [(Where _ pat e) `(#:where ,(pattern->sexp pat) ,(expr->sexp e))]
    [(When _ e) `(#:when ,(expr->sexp e))]
    [(Unless _ e) `(#:unless ,(expr->sexp e))]
    [_ `(error$ ,(format "Unrecognized bu form: ~a" bu))]))

(define (mf->sexp mf)
  (match mf
    [(Metafunction m τ rules)
     `(m : ,(type->sexp τ) . ,(map rule->sexp rules))]
    [_ `(error$ ,(format "Unrecognized mf form: ~a" mf))]))

(define (bu-α-equal? bu0 bu1 ρ0 ρ1)
  (match* (bu0 bu1)
    [((Update _ k0 v0) (Update _ k1 v1))
     (values ρ0 ρ1 (and (expr-α-equal? k0 k1 ρ0 ρ1)
                        (expr-α-equal? v0 v1 ρ0 ρ1)))]
    [((Where _ pat0 e0) (Where _ pat1 e1))
     (if (expr-α-equal? e0 e1 ρ0 ρ1)
         (pattern-α-equal? pat0 pat1 ρ0 ρ1)
         (values ρ0 ρ1 #f))]
    [((When _ e0) (When _ e1)) (expr-α-equal? e0 e1)]
    [((Unless _ e0) (Unless _ e1)) (expr-α-equal? e0 e1)]
    [(_ _) (values ρ0 ρ1 #f)]))

(define (bus-α-equal? bus0 bus1 ρ0 ρ1)
  (match* (bus0 bus1)
    [('() '()) (values ρ0 ρ1 #t)]
    [((cons bu0 bus0) (cons bu1 bus1))
     (define-values (ρ0* ρ1* r) (bu-α-equal? bu0 bu1 ρ0 ρ1))
     (cond
      [r (bus-α-equal? bus0 bus1 ρ0* ρ1*)]
      [else (values ρ0* ρ1* #f)])]
    [(_ _) (values ρ0 ρ1 #f)]))

(define (mf-α-equal? mf0 mf1 ρ0 ρ1)
  (match-define (Metafunction name0 τ0 rules0) mf0)
  (match-define (Metafunction name1 τ1 rules1) mf1)
  (and (eq? name0 name1)
       (equal? τ0 τ1)
       (for/and ([r0 (in-list rules0)]
                 [r1 (in-list rules1)])
         (rule-α-equal? r0 r1 ρ0 ρ1))))

(define (mfs-α-equal? mfs0 mfs1 ρ0 ρ1)
  (for/and ([mf0 (in-list mfs0)]
            [mf1 (in-list mfs1)])
    (mf-α-equal? mf0 mf1 ρ0 ρ1)))

(define (write-bu bu port mode)
  (display (bu->sexp bu) port))

(struct BU with-stx () #:transparent)
(struct Update BU (k v) #:transparent
        #:methods gen:custom-write [(define write-proc write-bu)])
(struct Where BU (pat e) #:transparent
        #:methods gen:custom-write [(define write-proc write-bu)])
(struct When BU (e) #:transparent
        #:methods gen:custom-write [(define write-proc write-bu)])
(struct Unless BU (e) #:transparent
        #:methods gen:custom-write [(define write-proc write-bu)])

(define (rule->sexp arrow?)
  (define head (if arrow? '(#:-->) '()))
  (match-lambda [(Rule _ name lhs rhs bus)
                 `(,@head ,@(if name `(#:name ,name) '())
                          ,(pattern->sexp lhs)
                          ,(expr->sexp rhs)
                          . ,(map bu->sexp bus))]
                [_ #f]))

(define (write-rule r port mode)
  (display ((rule->sexp #t) r) port))

(define (rule-α-equal? r0 r1 ρ0 ρ1)
  (match* (r0 r1)
    [((Rule _ name lhs0 rhs0 bus0)
      (Rule _ name lhs1 rhs1 bus1))
     (define-values (ρ0* ρ1* r) (pattern-α-equal? lhs0 lhs1 ρ0 ρ1))
     (cond
      [r (define-values (ρ0** ρ1** r*) (bus-α-equal? bus0 bus1 ρ0* ρ1*))
         (and r* (expr-α-equal? rhs0 rhs1 ρ0** ρ1**))]
      [else #f])]
    [(_ _) #f]))

(struct Rule with-stx (name lhs rhs bus) #:transparent
        #:methods gen:custom-write [(define write-proc write-rule)])

(define (abstract-frees-in-rules rules names)
  (for/fold ([scoped-rules (abstract-frees-in-rules-aux rules names)])
      ([? (in-list names)])
    (Scope scoped-rules)))

(define (open-scopes-in-rules scoped-rules substs)
  (let match-open ([sr scoped-rules] [substs* substs])
    (match* (sr substs*)
      [((Scope sr) (cons _ substs*))
       (match-open sr substs*)]
      [((not (? Scope?)) '())
       (open-scopes-in-rules-aux sr substs)]
      [(_ _)
       (error 'open-scopes-in-rules "Scope subst mismatch ~a, ~a" scoped-rules substs)])))

(define (abstract-frees-in-rules-aux rules names)
  (for/list ([rule (in-list rules)])
    (abstract-frees-in-rule rule names)))

(define (open-scopes-in-rules-aux rules substs)
  (for/list ([rule (in-list rules)])
    (open-scopes-in-rule rule substs)))

(define (abstract-frees-in-rule rule names)
  (match-define (Rule sy name lhs rhs bus) rule)
  (define lhs* (abstract-frees-in-pattern lhs names))
  (define rhs* (abstract-frees-in-expr rhs names))
  (define bus* (abstract-frees-in-bus bus names))
  (Rule sy name lhs* rhs* bus*))

(define (open-scopes-in-rule rule substs)
  (match-define (Rule sy name lhs rhs bus) rule)
  (define lhs* (open-scopes-in-pattern lhs substs))
  (define rhs* (open-scopes-in-expr rhs substs))
  (define bus* (open-scopes-in-bus bus substs))
  (Rule sy name lhs* rhs* bus*))

(define (abstract-frees-in-bus bus names)
  (for/list ([bu (in-list bus)]) (abstract-frees-in-bu bu names)))

(define (abstract-frees-in-mfs mfs names)
  (for/list ([mf (in-list mfs)]) (abstract-frees-in-mf mf names)))

(define (open-scopes-in-bus bus substs)
  (for/list ([bu (in-list bus)]) (open-scopes-in-bu bu substs)))

(define (open-scopes-in-mfs mfs substs)
  (for/list ([mf (in-list mfs)]) (open-scopes-in-mf mf substs)))

(define (abstract-frees-in-bu bu names)
  (match bu
    [(Update sy k v)
     (Update sy
             (abstract-frees-in-expr k names)
             (abstract-frees-in-expr v names))]
    [(Where sy pat e)
     (Where sy
            (abstract-frees-in-pattern pat names)
            (abstract-frees-in-expr e names))]
    [(When sy e) (When sy (abstract-frees-in-expr e names))]
    [(Unless sy e) (Unless sy (abstract-frees-in-expr e names))]))

(define (open-scopes-in-bu bu substs)
  (match bu
    [(Update sy k v)
     (Update sy
             (open-scopes-in-expr k substs)
             (open-scopes-in-expr v substs))]
    [(Where sy pat e)
     (Where sy
            (open-scopes-in-pattern pat substs)
            (open-scopes-in-expr e substs))]
    [(When sy e) (When sy (open-scopes-in-expr e substs))]
    [(Unless sy e) (Unless sy (open-scopes-in-expr e substs))]))

(define (abstract-frees-in-mf mf names)
  (match-define (Metafunction name τ rules) mf)
  (Metafunction name
                (abstract-frees τ names)
                (abstract-frees-in-rules rules names)))

(define (open-scopes-in-mf mf substs)
  (match-define (Metafunction name τ rules) mf)
  (Metafunction name (open-scopes τ substs) (open-scopes-in-rules rules substs)))

(define (abstract-frees-in-ct ct names)
  (match ct
    [(Cast τ) (Cast (abstract-frees τ names))]
    [(Check τ) (Check (abstract-frees τ names))]
    [_ ct]))

(define (open-scopes-in-ct ct substs)
  (match ct
    [(Cast τ) (Cast (open-scopes τ substs))]
    [(Check τ) (Check (open-scopes τ substs))]
    [_ ct]))

(define (peel-scopes s)
  (match s
    [(Scope st) (peel-scopes st)]
    [_ s]))

(define (abstract-frees-in-pattern pat names)
  (let self ([pat pat])
    (define ct* (abstract-frees-in-ct (Typed-ct pat) names))
    (match pat
      [(PName sy _ x p) (PName sy ct* x (self p))]
      [(PWild sy ct) (PWild sy ct*)]
      [(PVariant sy _ n ps) (PVariant sy ct* n (map self ps))]
      [(PMap-with sy _ k v p) (PMap-with sy ct* (self k) (self v) (self p))]
      [(PMap-with* sy _ k v p) (PMap-with* sy ct* (self k) (self v) (self p))]
      [(PSet-with sy _ v p) (PSet-with sy ct* (self v) (self p))]
      [(PSet-with* sy _ v p) (PSet-with* sy ct* (self v) (self p))]
      [(PTerm sy _ t) (PTerm sy ct* (abstract-frees-in-term t names))]
      [(PDeref sy _ p taddr imp) (PDeref sy ct* (self p) taddr imp)]
      [(PIsType sy _ p) (PIsType sy ct* (self p))]
      [_ (error 'abstract-frees-in-pattern "Unsupported pattern: ~a" pat)])))

(define (open-scopes-in-pattern pat substs)
  (let self ([pat pat])
    (define ct* (open-scopes-in-ct (Typed-ct pat) substs))
    (match pat
      [(PName sy _ x p) (PName sy ct* x (self p))]
      [(PWild sy ct) (PWild sy ct*)]
      [(PVariant sy _ n ps) (PVariant sy ct* n (map self ps))]
      [(PMap-with sy _ k v p) (PMap-with sy ct* (self k) (self v) (self p))]
      [(PMap-with* sy _ k v p) (PMap-with* sy ct* (self k) (self v) (self p))]
      [(PSet-with sy _ v p) (PSet-with sy ct* (self v) (self p))]
      [(PSet-with* sy _ v p) (PSet-with* sy ct* (self v) (self p))]
      [(PTerm sy _ t) (PTerm sy ct* (open-scopes-in-term t substs))]
      [(PDeref sy _ p taddr imp) (PDeref sy ct* (self p) taddr imp)]
      [(PIsType sy _ p) (PIsType sy ct* (self p))]
      [_ (error 'open-scopes-in-pattern "Unsupported pattern: ~a" pat)])))

(define (abstract-frees τ names)
  (for/fold ([abs-τ τ])
      ([name (in-list names)]
       [i (in-naturals)])
    (abstract-free-aux abs-τ i name #f)))

(define (abstract-freess τs names)
  (for/list ([τ (in-list τs)]) (and τ (abstract-frees τ names))))

(define (open-scopes τ substs)
  (for/fold ([open-τ τ])
      ([sub (in-list substs)]
       [i (in-naturals)])
    (open-scope-aux open-τ i sub)))

(define (open-scopess τs substs)
  (for/list ([τ (in-list τs)]) (and τ (open-scopes τ substs))))

(define (abstract-frees-in-expr e names)
  (let self ([e e])
    (define ct* (abstract-frees-in-ct (Typed-ct e) names))
    (match e
      [(ECall sy _ mf τs es)
       (ECall sy ct* mf
              (and τs (abstract-freess τs names))
              (map self es))]
      [(EVariant sy _ n tag τs es)
       (EVariant sy ct* n tag
                 (and τs (abstract-freess τs names)) (map self es))]
      [(ERef sy _ x) (ERef sy ct* x)]
      [(EStore-lookup sy _ k lm imp) (EStore-lookup sy ct* (self k) lm imp)]
      [(EAlloc sy _ tag) (EAlloc sy ct* tag)]
      [(ELet sy _ bus body) (ELet sy ct* (abstract-frees-in-bus bus names) (self body))]
      [(ELetrec sy _ mfs body) (ELetrec sy ct* (abstract-frees-in-mfs mfs names) (self body))]
      [(EMatch sy _ de rules) (EMatch sy ct* (self de) (abstract-frees-in-rules-aux rules names))]
      [(EIf sy _ g t e) (EIf sy ct* (self g) (self t) (self e))]
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
      [(EUnquote sy _ racke) (EUnquote sy ct* racke)]
      [(EExternal sy _ v) (EExternal sy ct* v)]
      [_ (error 'abstract-frees-in-expr "Unrecognized expression form: ~a" e)])))

(define (open-scopes-in-expr e substs)
  (let self ([e e])
    (define ct* (open-scopes-in-ct (Typed-ct e) substs))
    (match e
      [(ECall sy _ mf τs es)
       (ECall sy ct* mf
              (and τs (open-scopess τs substs))
              (map self es))]
      [(EVariant sy _ n tag τs es)
       (EVariant sy ct* n tag (and τs (open-scopess τs substs)) (map self es))]
      [(ERef sy _ x) (ERef sy ct* x)]
      [(EStore-lookup sy _ k lm imp) (EStore-lookup sy ct* (self k) lm imp)]
      [(EAlloc sy _ tag) (EAlloc sy ct* tag)]
      [(ELet sy _ bus body) (ELet sy ct* (open-scopes-in-bus bus substs) (self body))]
      [(ELetrec sy _ mfs body) (ELetrec sy ct* (open-scopes-in-mfs mfs substs) (self body))]
      [(EMatch sy _ de rules) (EMatch sy ct* (self de) (open-scopes-in-rules-aux rules substs))]
      [(EIf sy _ g t e) (EIf sy ct* (self g) (self t) (self e))]
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
      [(EUnquote sy _ racke) (EUnquote sy ct* racke)]
      [(EExternal sy _ v) (EExternal sy ct* v)]
      [_ (error 'open-scopes-in-expr "Unrecognized expression form: ~a" e)])))

(define (abstract-frees-in-term t names)
  (let self ([t t])
    (define ct* (abstract-frees-in-ct (Typed-ct t) names))
    (match t
      [(Variant sy _ n ts) (Variant sy ct* n (map self ts))]
      [(Map sy _ f) (Map sy ct* (for/hash ([(k v) (in-hash f)])
                                  (values (self k) (self v))))]
      [(Set sy _ s) (Set sy ct* (for/set ([v (in-set s)]) (self v)))]
      [(External sy _ v) (External sy ct* v)]
      [_ (error 'abstract-frees-in-term "Unsupported term ~a" t)])))

(define (open-scopes-in-term t substs)
  (let self ([t t])
    (define ct* (open-scopes-in-ct (Typed-ct t) substs))
    (match t
      [(Variant sy _ n ts) (Variant sy ct* n (map self ts))]
      [(Map sy _ f) (Map sy ct* (for/hash ([(k v) (in-hash f)])
                                  (values (self k) (self v))))]
      [(Set sy _ s) (Set sy ct* (for/set ([v (in-set s)]) (self v)))]
      [(External sy _ v) (External sy ct* v)]
      [_ (error 'abstract-frees-in-term "Unsupported term ~a" t)])))

(define (open-type-and-rules τ scoped-rules)
  (define (err)
    (error 'open-type-and-rules
             "Scope mismatch between type and rules ~a and ~a"
             τ scoped-rules))
  (let open ([τ τ] [names '()] [tvs '()])
   (match τ
     [(TΛ: _ name s oa)
      (define name* (fresh-name (support (Scope-t s)) name))
      (define tv (mk-TFree #f name*))
      (open (oa (open-scope s tv)) (cons name* names) (cons tv tvs))]
     [_ (values names τ (open-scopes-in-rules scoped-rules tvs))])))
