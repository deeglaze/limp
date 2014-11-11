#lang racket/base
(require racket/match racket/set "types.rkt")
#|
This module provides the structs that the Limp compiler uses to typecheck an input language
and semantics.
|#

(provide (all-defined-out))

(struct with-stx (stx) #:transparent)
;; Cast or Check annotations?
(struct Cast (t) #:transparent)
(struct Check (t) #:transparent)
(struct Typed with-stx (ct) #:transparent)
(define πcc (match-lambda
             [(Typed _ (or (Cast t) (Check t))) t]
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
    [_ `(error$ 'ann-wrap ,(format "Bad ct: ~a" ct))]))

;; Elaborated patterns
(define (pattern->sexp p)
  (define v (pattern-print-verbosity))
  (let rec ([p p])
    (define sexp
      (match p
        [(PAnd _ _ ps) `(and . ,(map rec ps))]
        [(PName _ _ x) x]
        [(PWild _ _) '_]
        [(PVariant _ _ n ps) `(,n . ,(map rec ps))]
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
        [(PTerm _ _ t) `(#:term ,(term->sexp t))]
        [(PIsExternal _ (Check (TExternal: _ name))) `(#:is-external ,name)]
        [(PIsAddr _ (Check (TAddr: _ space mm em _))) `(#:is-addr ,space ,mm ,em)]
        [(PIsType _ (Check τ)) `(#:is-type ,τ)] ;; printer will handle τ
        [_ `(error$ ,(format "Unsupported pattern: ~a" p))]))
    (case v
      [(0) sexp]
      [(1) (ann-wrap (Typed-ct p) sexp)]
      [else (parameterize ([type-print-verbosity 1])
              (ann-wrap (Typed-ct p) sexp))])))

(define (pattern-replace-ct ct p)
   (match p
     [(PAnd sy _ ps) (PAnd sy ct ps)]
     [(PName sy _ x) (PName sy ct x)]
     [(PWild sy _) (PWild sy ct)]
     [(PVariant sy _ n ps) (PVariant sy ct n ps)]
     [(PMap-with sy _ k v p) (PMap-with sy ct k v p)]
     [(PMap-with* sy _ k v p) (PMap-with* sy ct k v p)]
     [(PSet-with sy _ v p) (PSet-with sy ct v p)]
     [(PSet-with* sy _ v p) (PSet-with* sy ct v p)]
     [(PTerm sy _ t) (PTerm sy ct t)]
     [(PIsExternal sy _) (PIsExternal sy ct)]
     [(PIsAddr sy _) (PIsAddr sy ct)]
     [(PIsType sy _) (PIsType sy ct)]
     [_ (error 'pattern-replace-ct "Unsupported pattern: ~a" p)]))

(define (write-pattern pat port mode)
  (display (pattern->sexp pat) port))

(struct Pattern Typed () #:transparent
        #:methods gen:custom-write [(define write-proc write-pattern)])
(struct PAnd Pattern (ps) #:transparent)
(struct PName Pattern (x) #:transparent)
(struct PWild Pattern () #:transparent)
(struct PVariant Pattern (n ps) #:transparent)
(struct PMap-with Pattern (k v p) #:transparent)
(struct PMap-with* Pattern (k v p) #:transparent)
(struct PSet-with Pattern (v p) #:transparent)
(struct PSet-with* Pattern (v p) #:transparent)
(struct PTerm Pattern (t) #:transparent)
;; The info is in the type
(struct PIsExternal Pattern () #:transparent)
(struct PIsAddr Pattern () #:transparent)
(struct PIsType Pattern () #:transparent)
#|
Template:
 (match pat
    [(PAnd sy ct ps) ???]
    [(PName sy ct x) ???]
    [(PWild sy ct) ???]
    [(PVariant sy ct n ps) ???]
    [(PMap-with sy ct k v p) ???]
    [(PMap-with* sy ct k v p) ???]
    [(PSet-with sy ct v p) ???]
    [(PSet-with* sy ct v p) ???]
    [(PTerm sy ct t) ???]
    [(PIsExternal sy ct) ???]
    [(PIsAddr sy ct) ???]
    [(PIsType sy ct) ???]
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
    [((PAnd _ ct ps0) (PAnd _ ct ps1)) (sequence-pattern-α-equal? ps0 ps1 ρ0 ρ1)]
    [((PName _ ct x0) (PName _ ct x1))
     (match (hash-ref ρ0 x0 #f)
       [#f (if (hash-has-key? ρ1 x1)
               (values ρ0 ρ1 #f)
               ;; both unmapped. Freshen to same name.
               (let ([f (gensym)])
                 (values (hash-set ρ0 x0 f)
                         (hash-set ρ1 x1 f)
                         #t)))]
       [x0* (match (hash-ref ρ1 x1 #f)
              [#f (values ρ0 ρ1 #f)]
              [x1* (values ρ0 ρ1 (eq? x0* x1*))])])]
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
    [((PIsExternal _ ct) (PIsExternal _ ct)) (values ρ0 ρ1 #t)]
    [((PWild _ ct) (PWild _ ct)) (values ρ0 ρ1 #t)]
    [((PIsAddr _ ct) (PIsAddr _ ct)) (values ρ0 ρ1 #t)]
    [((PIsType _ ct) (PIsType _ ct)) (values ρ0 ρ1 #t)]
    [(_ _) (values ρ0 ρ1 #f)]))

;; Elaborated Terms
(define (term->sexp t)
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
template
 (match t
    [(Variant sy ct n ts) ???]
    [(Map sy ct f) ???]
    [(Set sy ct s) ???]
    [(External sy ct v) ???]
    [_ (error who "Unsupported term ~a" t)])
|#

(define (expr->sexp e)
  (define (do-tag tag) (if tag `(#:tag ,tag) '()))
  (define v (expr-print-verbosity))
  (let rec ([e e])
    (define sexp
      (match e
        [(ECall _ _ mf tag τs es) `(,mf ,@(do-tag tag) . ,(map rec es))]
        [(EVariant _ _ n tag τs es) `(,n ,@(do-tag tag) . ,(map rec es))]
        [(ERef _ _ x) x]
        [(EStore-lookup _ _ k lm) `(#:lookup ,(rec k) ,lm)]
        [(EAlloc _ (Check (TAddr: _ space mm em _)) tag) `(#:alloc ,@(do-tag tag) ,space ,mm ,em)]
        [(ELet _ _ bus body) `(#:let ,(map bu->sexp bus) ,(rec body))]
        [(EMatch _ _ de rules) `(#:match ,(rec de) . ,(map (rule->sexp #f) rules))]
        [(EExtend _ _ m tag k v)
         `(#:extend ,(rec m) ,@(do-tag tag) ,(rec k) ,(rec v))]
        [(EEmpty-Map _ _) '#:empty-map]
        [(EEmpty-Set _ _) '#:empty-set]
        [(ESet-union _ _ es) `(#:union . ,(map rec es))]
        [(ESet-intersection _ _ e es) `(#:intersection ,(rec e) . ,(map rec es))]
        [(ESet-subtract _ _ e es) `(#:subtract ,(rec e) . ,(map rec es))]
        [(ESet-member _ _ e v) `(#:member? ,(rec e) ,(rec v))]
        [(EMap-lookup _ _ m k) `(#:map-lookup ,(rec m) ,(rec k))]
        [(EMap-has-key _ _ m k) `(#:has-key? ,(rec m) ,(rec k))]
        [(EMap-remove _ _ m k) `(#:map-remove ,(rec m) ,(rec k))]
        [_ `(error$ ,(format "Unrecognized expression form: ~a" e))]))
    (case v
      [(0) sexp]
      [(1) (ann-wrap (Typed-ct e) sexp)]
      [else (parameterize ([type-print-verbosity 1])
              (ann-wrap (Typed-ct e) sexp))])))

(define (expr-replace-ct ct e)
  (match e
    [(ECall sy _ mf tag τs es) (ECall sy ct mf tag τs es)]
    [(EVariant sy _ n tag τs es) (EVariant sy ct n tag τs es)]
    [(ERef sy _ x) (ERef sy ct x)]
    [(EStore-lookup sy _ k lm) (EStore-lookup sy ct k lm)]
    [(EAlloc sy _ tag) (EAlloc sy ct tag)]
    [(ELet sy _ bus body) (ELet sy ct bus body)]
    [(EMatch sy _ de rules) (EMatch sy ct de rules)]
    [(EExtend sy _ m tag k v) (EExtend sy ct m tag k v)]
    [(EEmpty-Map sy _) (EEmpty-Map sy ct)]
    [(EEmpty-Set sy _) (EEmpty-Set sy ct)]
    [(ESet-union sy _ es) (ESet-union sy ct es)]
    [(ESet-intersection sy _ e es) (ESet-intersection sy ct e es)]
    [(ESet-subtract sy _ e es) (ESet-subtract sy ct e es)]
    [(ESet-member sy _ e v) (ESet-member sy ct e v)]
    [(EMap-lookup sy _ m k) (EMap-lookup sy ct m k)]
    [(EMap-has-key sy _ m k) (EMap-has-key sy ct m k)]
    [(EMap-remove sy _ m k) (EMap-remove sy ct m k)]
    [_ (error 'expr-replace-ct "Unrecognized expression form: ~a" e)]))

(define (write-expr e port mode)
  (display (expr->sexp e) port))

;; Expressions
(struct Expression Typed () #:transparent
        #:methods gen:custom-write [(define write-proc write-expr)])
(struct ECall Expression (mf tag τs es) #:transparent)
(struct EVariant Expression (n tag τs es) #:transparent)
(struct ERef Expression (x) #:transparent)
(struct EStore-lookup Expression (k lm) #:transparent) ;; lm ::= 'resolve | 'delay | 'deref
(struct EAlloc Expression (tag) #:transparent) ;; space mm em in type
(struct ELet Expression (bus body) #:transparent)
(struct EMatch Expression (discriminant rules) #:transparent)
(struct EExtend Expression (m tag k v) #:transparent)
(struct EEmpty-Map Expression () #:transparent)
(struct EEmpty-Set Expression () #:transparent)
(struct ESet-add Expression (s v) #:transparent)
;; Utility expressions
(struct ESet-union Expression (es) #:transparent)
(struct ESet-intersection Expression (e es) #:transparent)
(struct ESet-subtract Expression (e es) #:transparent)
(struct ESet-remove Expression (e es) #:transparent)
(struct ESet-member Expression (e v) #:transparent)
(struct EMap-lookup Expression (m k) #:transparent)
(struct EMap-has-key Expression (m k) #:transparent)
(struct EMap-remove Expression (m k) #:transparent)
#|
Template
 (match e
    [(ECall sy ct mf tag τs es) ???]
    [(EVariant sy ct n tag τs es) ???]
    [(ERef sy ct x) ???]
    [(EStore-lookup sy ct k lm) ???]
    [(EAlloc sy ct tag) ???]
    [(ELet sy ct bus body) ???]
    [(EMatch sy ct de rules) ???]
    [(EExtend sy ct m tag k v) ???]
    [(EEmpty-Map sy ct) ???]
    [(EEmpty-Set sy ct) ???]
    [(ESet-union sy ct es) ???]
    [(ESet-intersection sy ct e es) ???]
    [(ESet-subtract sy ct e es) ???]
    [(ESet-member sy ct e v) ???]
    [(EMap-lookup sy ct m k) ???]
    [(EMap-has-key sy ct m k) ???]
    [(EMap-remove sy ct m k) ???]
    [_ (error 'tc-expr "Unrecognized expression form: ~a" e)])
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
    [((ECall _ ct mf tag τs es0)
      (ECall _ ct mf tag τs es1))
     (equal*? es0 es1)]
    [((EVariant _ ct n tag τs es0)
      (EVariant _ ct n tag τs es1))
     (equal*? es0 es1)]
    [((ERef _ ct x) (ERef _ ct y))
     (eq? (hash-ref ρ0 x x)
          (hash-ref ρ1 y y))]
    [((EStore-lookup _ ct k0 lm)
      (EStore-lookup _ ct k1 lm))
     (expr-α-equal? k0 k1 ρ0 ρ1)]
    [((EAlloc _ ct tag) (EAlloc _ ct tag)) #t]
    [((ELet _ ct bus0 body0) (ELet _ ct bus1 body1))
     (define-values (ρ0* ρ1* r) (bus-α-equal? bus0 bus1 ρ0 ρ1))
     (and r (expr-α-equal? body0 body1 ρ0* ρ1*))]
    [((EMatch _ ct de0 rules0) (EMatch _ ct de1 rules1))
     (and (expr-α-equal? de0 de1 ρ0 ρ1)
          (for/and ([rule0 (in-list rules0)]
                    [rule1 (in-list rules1)])
            (rule-α-equal? rule0 rule1 ρ0 ρ1)))]
    [((EExtend _ ct m0 tag k0 v0) (EExtend _ ct m1 tag k1 v1))
     (and (expr-α-equal? m0 m1 ρ0 ρ1)
          (expr-α-equal? k0 k1 ρ0 ρ1)
          (expr-α-equal? v0 v1 ρ0 ρ1))]
    [((EEmpty-Map _ ct) (EEmpty-Map _ ct)) #t]
    [((EEmpty-Set _ ct) (EEmpty-Set _ ct)) #t]
    [((ESet-union _ ct es0) (ESet-union _ ct es1))
     (equal*? es0 es1)]
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
    [(_ _) #f]))

;; Binding updates
(define (bu->sexp bu)
  (match bu
    [(Update _ k v) `(#:update ,(expr->sexp k) ,(expr->sexp v))]
    [(Where _ pat e) `(#:where ,(pattern->sexp pat) ,(expr->sexp e))]
    [_ `(error$ ,(format "Unrecognized bu form: ~a" bu))]))

(define (bu-α-equal? bu0 bu1 ρ0 ρ1)
  (match* (bu0 bu1)
    [((Update _ k0 v0) (Update _ k1 v1))
     (values ρ0 ρ1 (and (expr-α-equal? k0 k1 ρ0 ρ1)
                        (expr-α-equal? v0 v1 ρ0 ρ1)))]
    [((Where _ pat0 e0) (Where _ pat1 e1))
     (if (expr-α-equal? e0 e1 ρ0 ρ1)
         (pattern-α-equal? pat0 pat1 ρ0 ρ1)
         (values ρ0 ρ1 #f))]
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

(define (write-bu bu port mode)
  (display (bu->sexp bu) port))

(struct Update with-stx (k v) #:transparent
        #:methods gen:custom-write [(define write-proc write-bu)])
(struct Where with-stx (pat e) #:transparent
        #:methods gen:custom-write [(define write-proc write-bu)])

(define (rule->sexp arrow?)
  (define head (if arrow? '(#:-->) '()))
  (match-lambda [(Rule _ name lhs rhs bus)
                 `(,@head ,@(if name `(#:name ,name) '())
                          ,(pattern->sexp lhs)
                          ,(expr->sexp rhs)
                          . ,(map bu->sexp bus))]))

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

