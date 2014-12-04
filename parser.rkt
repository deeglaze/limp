#lang racket/base
(require (for-syntax racket/base syntax/parse racket/syntax)
         (only-in racket/bool implies)
         racket/dict
         racket/list
         racket/match
         racket/pretty
         racket/set
         racket/syntax
         racket/trace
         syntax/parse
         syntax/srcloc
         "common.rkt"
         "language.rkt"
         "tast.rkt"
         "types.rkt")
(provide parse-language
         parse-reduction-relation
         parse-metafunction
         TopPreType ClosedTopPreType
         Rule-cls
         Expression-cls)


(module+ test (require rackunit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Fully annotated Limp code

(define (pretty-type t) (pretty-print (type->sexp t)))

;; Not actually writable.
#;#;
(struct Delay (a) #:transparent)
(struct TAbs (ts Es) #:transparent)

#|
Specialization analyses:
useless variable elimination
interprocedural unboxing (don't match and send unmatched value)
single address space
"concreteness" of a type for good map representation

|#

(define-splicing-syntax-class Unrolling
  #:attributes (trust n)
  (pattern (~seq (~or (~optional (~and trec #:bounded))
                      (~optional (~and tcon #:trust-construction))
                      (~optional (~seq #:unfold sn:nat))) ...)
           #:fail-when (and (attribute trec) (attribute tcon))
           "Cannot specify both #:bounded and #:trust-construction"
           #:attr trust (cond
                         [(syntax? (attribute trec)) 'bounded]
                         [(syntax? (attribute tcon)) 'trusted]
                         [else 'untrusted])
           #:fail-unless (implies (attribute sn) (untrusted? (attribute trust)))
           "Cannot specify both #:unfold and either #:bounded or #:trust-construction"
           #:attr n (if (attribute sn) (syntax-e #'sn) 0)))

(define-splicing-syntax-class (EM-Modes ops space? tag?)
  #:attributes (em mm tag space)
  (pattern (~seq (~or 
                  (~optional (~seq #:tag tag-s:expr))
                  (~optional (~seq #:space space-s:id))
                  (~optional mm*:Match-Mode)
                  (~optional em*:Equality-Mode)) ...)
           #:fail-when (and (attribute space-s) (not space?))
           "Unexpected #:space annotation"
           #:fail-when (and (attribute tag-s) (not tag?))
           "Unexpected #:tag annotation"
           #:attr mm (or (attribute mm*.mm)
                         (get-option 'mm #:use ops))
           #:attr em (or (attribute em*.em)
                         (get-option 'em #:use ops))
           #:attr tag (and (attribute tag-s) (syntax-e #'tag-s))
           #:attr space (or (and (attribute space-s) (syntax-e #'space-s))
                            (get-option 'addr-space #:use ops))))

(define (->ref x Unames Enames meta-table taddr)
  (let* ([sym (syntax-e x)]
         [sym (hash-ref meta-table sym sym)])
    (define τ
      (cond
       [(set-member? Unames sym)
        (mk-TName x sym)]
       [(set-member? Enames sym)
        (mk-TExternal x sym)]
       [else
        (mk-TFree x sym)]))
    (if taddr
        (*THeap '->ref x taddr #f τ) ;; No tag in types.
        τ)))

(define-splicing-syntax-class (formal-splicing options)
  #:attributes (id x taddr)
  (pattern (~seq id:id (~or (~and #:trusted trusted)
                           (~var modes (EM-Modes options #t #f))))
           #:fail-unless (or (syntax? (attribute trusted))
                             (or (attribute modes.mm)
                                 (attribute modes.em)
                                 (attribute modes.space)))
           "Must specify #:trusted or at least one of mm, em, #:space"
           #:attr x (syntax-e #'id)
           #:attr taddr (if (syntax? (attribute trusted))
                            'trusted
                            (if (syntax? (attribute trusted))
                                'trusted
                                (mk-TAddr #'modes
                                          (attribute modes.space)
                                          (attribute modes.mm) 
                                          (attribute modes.em))))))

(define-syntax-class (formal options)
  #:attributes (id x taddr)
  (pattern [(~var f (formal-splicing options))]
           #:attr id (attribute f.id)
           #:attr x (attribute f.x)
           #:attr taddr (attribute f.taddr))
  (pattern id:id
           #:attr x (syntax-e #'id)
           #:attr taddr limp-default-Λ-addr))

(define-syntax-class (formals options)
  #:attributes (ids xs taddrs)
  (pattern (~var f (formal options))
           #:attr ids (list (attribute f.id))
           #:attr xs (list (attribute f.x))
           #:attr taddrs (list (attribute f.taddr)))
  (pattern ((~var fs (formal options)) ...)
           #:attr ids (attribute fs.id)
           #:attr xs (attribute fs.x)
           #:attr taddrs (attribute fs.taddr)))

(define-splicing-syntax-class Externalize
  #:attributes (ext)
  (pattern (~optional (~or (~and ex #:externalize)
                           (~and nx #:do-not-externalize)))
           #:attr ext (cond
                       [(syntax? (attribute ex)) #t]
                       [(syntax? (attribute nx)) #f]
                       [else 'dc])))

(define-syntax-class (PreType options trust Unames Enames meta-table)
  #:attributes (t)
  #:local-conventions ([#rx"^t" (PreType options trust Unames Enames meta-table)])
  (pattern ((~or #:Λ #:∀ #:all) (~var f (formals options)) tbody)
           #:attr t (quantify-frees (attribute tbody.t)
                                    (reverse (attribute f.xs))
                                    #:stxs (attribute f.ids)
                                    #:taddrs (attribute f.taddrs)))
  (pattern (~and sy
                 (#:μ x:id (~var ty:expr) u:Unrolling
                      (~parse (~var tbody (PreType options
                                                   (attribute u.trust)
                                                   Unames Enames meta-table))
                              #'ty)))
           #:do [(define fv (free (attribute tbody.t)))
                 (define recursive? (set-member? fv (syntax-e #'x)))
                 (unless recursive?
                   (log-info (format "Recursive type ~a recursively bound variable: ~a (at ~a)"
                                     "does not refer to"
                                     (syntax-e #'x) (source-location-source #'sy))))]
           #:attr t (if recursive?
                        (mk-Tμ #'sy (syntax-e #'x)
                               (abstract-free (attribute tbody.t) (syntax-e #'x))
                               (attribute u.trust)
                               (attribute u.n))
                        (attribute tbody.t)))
  (pattern (~and sy (#:inst tf ta ...+))
           #:attr t (let all ([t (attribute tf.t)] [ts (attribute ta.t)])
                      (match ts
                        ['() t]
                        [(cons s ts) (all (mk-TCut #'sy t s) ts)])))
  (pattern (~and sy ((~or #:∪ #:union #:U) ts ...))
           #:attr t (*TRUnion #'sy (attribute ts.t)))
  ;; TODO: make abstraction annotations parse errors outside of define-language
  (pattern (~and sy ((~or #:map #:↦) td tr :Externalize))
           #:attr t (mk-TMap #'sy (attribute td.t) (attribute tr.t)
                             (attribute ext)))
  (pattern (~and sy ((~or #:set #:℘) ts :Externalize))
           #:attr t (mk-TSet #'sy (attribute ts.t) (attribute ext)))
  (pattern (~and sy (n:id ts ...))
           #:attr t (mk-TVariant #'sy
                                 (syntax-e #'n)
                                 (attribute ts.t)
                                 trust))
  (pattern (~and sy (#:addr (~var modes (EM-Modes options #t #f))))
           #:attr t (mk-TAddr #'sy
                              (attribute modes.space)
                              (attribute modes.mm)
                              (attribute modes.em)))
  (pattern x:id #:attr t
           (->ref #'x Unames Enames meta-table #f))
  (pattern [#:ref (~var f (formal-splicing options))]
           #:attr t (->ref (attribute f.id) Unames Enames meta-table
                           (attribute f.taddr)))
  (pattern (~or #:⊤ #:top #:any) #:attr t T⊤)
  (pattern 3d #:when (Type? (syntax-e #'3d)) #:attr t (syntax-e #'3d)))

(define-syntax-class (TopPreType options Unames Enames meta-table)
  #:attributes (t)
  (pattern (~var ty (PreType options 'untrusted Unames Enames meta-table))
           #:attr t (attribute ty.t)))

(define-syntax-class ClosedTopPreType
  #:attributes (t)
  (pattern (~var ty (PreType #hash() 'untrusted ∅ ∅ #hasheq())) #:attr t (attribute ty.t)))

(define-syntax-class Lookup-Mode
  #:attributes (lm)
  (pattern #:delay #:attr lm 'delay)
  (pattern #:deref #:attr lm 'deref)
  (pattern #:resolve #:attr lm 'resolve))

(define-syntax-class Match-Mode
  #:attributes (mm)
  (pattern #:delay #:attr mm 'delay)
  (pattern #:deref #:attr mm 'deref)
  (pattern #:resolve #:attr mm 'resolve)
  (pattern #:expose #:attr mm 'expose))

(define-syntax-class Equality-Mode
  #:attributes (em)
  (pattern #:structural #:attr em 'structural)
  (pattern #:identity #:attr em 'identity))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pattern syntax directives may only use literals if the language allows it.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-for-syntax (reserved-for-limp stx)
  (raise-syntax-error #f "This identifier is for use within the Limp language" stx))
(define-syntax map-with reserved-for-limp)
(define-syntax map-with* reserved-for-limp)
(define-syntax set-with reserved-for-limp)
(define-syntax set-with* reserved-for-limp)
(define-syntax addr reserved-for-limp)
(define-syntax name reserved-for-limp)
(define-syntax term reserved-for-limp)
(define-syntax external reserved-for-limp)
(define-syntax has-type reserved-for-limp)
(define-syntax-class (inc-pat L)
  (pattern _ #:when (hash-ref (Language-options L) 'include-pattern-namespace #f)))

(define-syntax-class (pand L)
  (pattern #:and)
  (pattern (~and (~literal and) (~var _ (inc-pat L)))))
(define-syntax-class (pmapwith L)
  (pattern #:map-with)
  (pattern (~and (~literal map-with) (~var _ (inc-pat L)))))
(define-syntax-class (pmapwith* L)
  (pattern #:map-with*)
  (pattern (~and (~literal map-with*) (~var _ (inc-pat L)))))
(define-syntax-class (psetwith L)
  (pattern #:set-with)
  (pattern (~and (~literal set-with) (~var _ (inc-pat L)))))
(define-syntax-class (psetwith* L)
  (pattern #:set-with*)
  (pattern (~and (~literal set-with*) (~var _ (inc-pat L)))))
(define-syntax-class (pterm L)
  (pattern #:term)
  (pattern (~and (~literal term) (~var _ (inc-pat L)))))
(define-syntax-class (paddr L)
  (pattern #:addr)
  (pattern (~and (~literal addr) (~var _ (inc-pat L)))))
(define-syntax-class (pexternal L)
  (pattern #:external)
  (pattern (~and (~literal external) (~var _ (inc-pat L)))))
(define-syntax-class (pname L)
  (pattern #:name)
  (pattern (~and (~literal name) (~var _ (inc-pat L)))))
(define-syntax-class (phastype L)
  (pattern #:has-type)
  (pattern (~and (~literal has-type) (~var _ (inc-pat L)))))
(define-syntax-class (pderef L)
  (pattern #:deref)
  (pattern (~and (~literal deref) (~var _ (inc-pat L)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pattern syntax
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-syntax-class Wild (pattern (~or (~datum _) #:wild)))
(define-syntax-class (Pattern-cls L ct)
  #:attributes (pat)
  #:local-conventions ([#rx"^p" (Pattern-cls L #f)])
  (pattern (~and sy :Wild)
           #:attr pat (PWild #'sy ct))
  (pattern (~and sy ((~var _ (pand L)) p ...))
           #:attr pat (PAnd #'sy ct (attribute p.pat)))
  (pattern (~and sy ((~var _ (pmapwith L)) pk pv pm))
           #:attr pat (PMap-with #'sy ct
                                    (attribute pk.pat)
                                    (attribute pv.pat)
                                    (attribute pm.pat)))
  (pattern (~and sy ((~var _ (pmapwith* L)) pk pv pm))
           #:attr pat (PMap-with* #'sy ct
                                     (attribute pk.pat)
                                     (attribute pv.pat)
                                     (attribute pm.pat)))
  (pattern (~and sy ((~var _ (psetwith L)) pv ps))
           #:attr pat (PSet-with #'sy ct
                                    (attribute pv.pat)
                                    (attribute ps.pat)))
  (pattern (~and sy ((~var _ (psetwith* L)) pv ps))
           #:attr pat (PSet-with* #'sy ct
                                    (attribute pv.pat)
                                    (attribute ps.pat)))
  (pattern (~and sy ((~var _ (pname L)) x:id))
           #:attr pat (PName #'sy ct (syntax-e #'x)))
  (pattern (~and sy ((~var _ (paddr L)) name:id
                     (~var modes (EM-Modes (Language-options L) #f #f))))
           #:attr pat (PIsAddr #'sy
                               ;; FIXME: actually check that ct and the given taddr are the same
                               ;; since a mismatch is an error.
                               (or ct
                                   (Cast
                                    (mk-TAddr #'modes (syntax-e #'name)
                                              (attribute modes.mm)
                                              (attribute modes.em))))))
  (pattern (~and sy ((~var _ (pexternal L)) name:id))
           #:when (hash-has-key? (Language-external-spaces L) (syntax-e #'name))
           #:attr pat (PIsExternal #'sy
                                   (or ct ;; FIXME: same as above
                                       (Cast
                                        (mk-TExternal #'name (syntax-e #'name) #f)))))
  (pattern (~and sy (n:id p ...))
           #:attr pat (PVariant #'sy ct (syntax-e #'n) (attribute p.pat)))
  (pattern (~and sy ((~var _ (pterm L)) (~var t (Term-cls L #f))))
           #:attr pat (PTerm #'sy ct (attribute t.tm)))
  (pattern (~and sy ((~var _ (phastype L)) (~var t (Type-cls #t L))))
           #:when (mono-type? (attribute t.t))
           #:attr pat (PIsType #'sy (or ct ;; FIXME: same as above
                                        (Cast (attribute t.t)))))
  (pattern (~and sy ((~var _ (pderef L))
                     (~or 
                      (~once (~var modes (EM-Modes (Language-options L) #f #f)))
                      (~optional (~or (~and #:explicit explicit)
                                      (~and #:implicit implicit)))
                      (~once p)) ...))
           #:attr pat (PDeref #'sy ct (attribute p.pat)
                              (if (or (syntax? (attribute explicit))
                                      (syntax? (attribute implicit)))
                                  (mk-TAddr #'modes
                                            (attribute modes.space)
                                            (attribute modes.mm)
                                            (attribute modes.em))
                                  generic-TAddr)
                              (syntax? (attribute implicit))))
  (pattern x:id #:attr pat (PName #'x ct (syntax-e #'x)))
  ;; Annotate/cast
  (pattern (#:ann (~var t (Type-cls #t L)) (~var pata (Pattern-cls L (Check (attribute t.t)))))
           #:attr pat (attribute pata.pat))
  (pattern (#:cast (~var t (Type-cls #t L)) (~var patc (Pattern-cls L (Cast (attribute t.t)))))
           #:attr pat (attribute patc.pat)))

(define-syntax-class (Type-cls allow-raw? L)
  #:attributes (t)
  (pattern (~var pt (TopPreType (Language-options L)
                                (hash-key-set (Language-user-spaces L))
                                (hash-key-set (Language-external-spaces L))
                                (Language-meta-table L)))
           #:do [(define t-op
                   (parameterize ([current-language L])
                     (check-productive-and-classify-unions (attribute pt.t) allow-raw?)))]
           #:when t-op
           #:attr t t-op))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Limp Terms
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax-class (Term-cls L ct)
  #:attributes (tm)
  #:local-conventions ([#rx"^t" (Term-cls L #f)])
  (pattern (~and sy (#:set t ...))
           ;; XXX: set?
           #:attr tm (Set #'sy ct (apply set (attribute t.tm))))
  (pattern (~and sy (#:map (~seq tk tv) ...))
           #:attr tm (Map #'sy ct (for/hash ([k (in-list (attribute tk.tm))]
                                             [v (in-list (attribute tv.tm))])
                                    (values k v))))
  (pattern (~and sy (n:id t ...))
           #:attr tm (Variant #'sy ct (syntax-e #'n) (attribute t.tm)))
  (pattern (~and sy (#:external name:id v))
           #:attr tm (External #'sy (syntax-e #'name) #'v))
  ;; Annotate/cast
  (pattern (#:ann (~var aty (Type-cls #t L)) (~var ta (Term-cls L (Check (attribute aty.t)))))
           #:attr tm (attribute ta.tm))
  (pattern (#:cast (~var cty (Type-cls #t L)) (~var tc (Term-cls L (Cast (attribute cty.t)))))
           #:attr tm (attribute tc.tm))
  ;; Those didn't work. What about the external spaces?
  (pattern v
           #:do [(define ext
                   (for/or ([(name ed) (in-hash
                                        (Language-external-spaces L))]
                            #:when (let ([p (ED-parse ed)])
                                     (and p (p #'v))))
                     name))]
           #:when ext
           #:attr tm (External #'v ext #'v)))

(define-syntax-class (Expression-cls L ct)
  #:attributes (e)
  #:local-conventions ([#rx"^e" (Expression-cls L #f)]
                       [#rx"^r" (Rule-cls #f L)])
  (pattern (~and sy (#:call f:id (~optional (~seq #:inst [(~var ts (Type-cls #t L)) ...]))
                            es ...))
           #:attr e (ECall #'sy ct
                           (syntax-e #'f)
                           (or (attribute ts.t) '())
                           (attribute es.e)))
  (pattern (~and sy (#:lookup ek (~optional mode:Lookup-Mode)
                              (~optional (~seq (~and #:implicit implicit)
                                               (~var modes (EM-Modes (Language-options L) #t #f))))))
           #:attr e (EStore-lookup #'sy ct
                                   (attribute ek.e)
                                   (or (attribute mode.lm) (get-option 'lm #:use L))
                                   (and (syntax? (attribute implicit))
                                        (mk-TAddr #'modes
                                                  (attribute modes.space)
                                                  (attribute modes.mm)
                                                  (attribute modes.em)))))
  (pattern (~and sy (#:alloc (~var ops (EM-Modes (Language-options L) #t #t))))
           #:attr e (EAlloc #'sy
                            (or ct ;; FIXME: same as above
                                (Check (mk-TAddr #'ops
                                                 (attribute ops.space)
                                                 (attribute ops.mm)
                                                 (attribute ops.em))))
                            (attribute ops.tag)))
  (pattern (~and sy (#:let [(~var bus (Binding-updates-cls L))] ebody))
           #:attr e (ELet #'sy
                          (or ct
                              (Typed-ct (attribute ebody.e)))
                          (attribute bus.bus)
                          (attribute ebody.e)))
  (pattern (~and sy (#:match edisc rules ...))
           #:attr e (EMatch #'sy ct (attribute edisc.e)
                            (attribute rules.rule)))
  (pattern (~and sy (#:extend em (~optional (~seq #:tag tag:expr)) ek ev))
           #:attr e (EExtend #'sy ct (attribute em.e)
                             (let ([t (attribute tag)]) (and t (syntax->datum t)))
                             (attribute ek.e)
                             (attribute ev.e)))
  (pattern (~and sy #:empty-map) #:attr e (EEmpty-Map #'sy (TMap T⊥ T⊥ #f)))
  (pattern (~and sy #:empty-set) #:attr e (EEmpty-Set #'sy (TSet T⊥ #f)))
  (pattern (~and sy (#:add es ev))
           #:attr e (ESet-add #'sy ct (attribute es.e) (attribute ev.e)))
  (pattern (~and sy (n:id (~or (~optional (~seq #:tag tag:expr)) es) ...))
           #:attr e (EVariant #'sy
                              ct
                              (syntax-e #'n)
                              (let ([t (attribute tag)]) (and t (syntax->datum t)))
                              '() ;; TODO: Type instantiations
                              (attribute es.e)))
  ;; TODO: use some binding environment? Check afterwards?
  (pattern x:id #:attr e (ERef #'x ct (syntax-e #'x)))

  ;; Extra builtins
  (pattern (~and sy (#:union es ...))
           #:attr e (ESet-union #'sy ct (attribute es.e)))
  (pattern (~and sy (#:intersection e0 es ...))
           #:attr e (ESet-intersection #'sy ct (attribute e0.e) (attribute es.e)))
  (pattern (~and sy (#:subtract e0 es ...))
           #:attr e (ESet-subtract #'sy ct (attribute e0.e) (attribute es.e)))
  (pattern (~and sy (#:remove e0 ev))
           #:attr e (ESet-remove #'sy ct (attribute e0.e) (attribute ev.e)))
  (pattern (~and sy (#:member? es ev))
           #:attr e (ESet-member #'sy ct (attribute es.e) (attribute ev.e)))
  (pattern (~and sy (#:map-lookup em ek)) #:attr e (EMap-lookup #'sy ct (attribute em.e) (attribute ek.e)))
  (pattern (~and sy (#:has-key? em ek))
           #:attr e (EMap-has-key #'sy ct (attribute em.e) (attribute ek.e)))
  (pattern (~and sy (#:map-remove em ek))
           #:attr e (EMap-remove #'sy ct (attribute em.e) (attribute ek.e)))
  ;; Annotate/cast
  (pattern (#:ann (~var t (Type-cls #t L)) (~var ea (Expression-cls L (Check (attribute t.t)))))
           #:attr e (attribute ea.e))
  (pattern (#:cast (~var t (Type-cls #t L)) (~var ec (Expression-cls L (Cast (attribute t.t)))))
           #:attr e (attribute ec.e)))

(define-syntax-class (Binding-update-cls L)
  #:attributes (bu)
  #:local-conventions ([#rx"^e" (Expression-cls L #f)])
  (pattern (~and sy [#:where (~var p (Pattern-cls L #f)) e])
           #:attr bu (Where #'sy (attribute p.pat) (attribute e.e)))
  (pattern (~and sy [#:update ek ev])
           #:attr bu (Update #'sy (attribute ek.e) (attribute ev.e))))

(define-splicing-syntax-class (Binding-updates-cls L)
  #:attributes (bus)
  (pattern (~seq) #:attr bus '())
  (pattern (~seq (~var bu (Binding-update-cls L)) (~var bs (Binding-updates-cls L)))
           #:attr bus (cons (attribute bu.bu) (attribute bs.bus))))

(define-syntax-class (Rule-cls arrow? L)
  #:attributes (rule)
  (pattern (~and sy [(~optional (~and #:--> arrow))
                     (~optional (~seq #:name name:id))
                     (~var p (Pattern-cls L #f))
                     (~var e (Expression-cls L #f))
                     (~var bus (Binding-updates-cls L))])
           #:fail-unless (if arrow? (attribute arrow) #t)
           "Expected rule form to start with #:-->"
           #:fail-when (if arrow? #f (attribute arrow))
           "Unexpected #:--> in [pat rhs] form"
           
           #:attr rule (Rule #'sy (and (attribute name) (syntax-e #'name))
                             (attribute p.pat)
                             (attribute e.e)
                             (attribute bus.bus))))

#|
TODO:
Check that only metavariables or space names are used in space definitions.
Replace all space metavariables for the canonical space name
Form a type binding environment to perform the check-productive-and-classify-unions operation.
Turn all free non-metavariables into external space names if they are bound.
|#

(define-syntax-class User-shape
  (pattern [(~optional (:id ...)) :id . _]))
(define-syntax-class External-shape
  (pattern [(~optional (:id ...)) #:external :id . _]))
(define-syntax-class External-cls
  #:attributes ((metas 1) name desc)
  #:description "Specify an external value space"
  (pattern
   [(~optional (metas:id ...) #:defaults ([(metas 1) '()]))
    #:external name:id
    ;; run time
    (~or
     (~optional (~and #:flat flat)) ;; mutually exclusive with the following
     (~optional (~seq #:join join:expr))
     (~optional (~seq #:lesseq lesseq:expr))
     (~optional (~seq #:equiv equiv:expr))
     (~optional (~seq #:cardinality card:expr))
     (~optional (~seq #:touch touch:expr))
     (~optional (~seq #:pretty pretty:expr))
     ;; parse time
     (~optional (~seq #:parse to-eval:expr))
     ;; Qualities
     (~optional (~or (~and #:discrete (~bind [quality 'discrete]))
                     (~and #:concrete (~bind [quality 'concrete]))
                     (~and #:abstract (~bind [quality 'abstract])))
                #:defaults ([quality 'abstract]))) ...]
   #:fail-when (and (attribute flat)
                    (or (attribute join)
                        (attribute lesseq)
                        (attribute equiv)
                        (attribute card)
                        (attribute touch)
                        (attribute pretty)))
   ;; Ensure external space of the right form
   (format
    "#:flat cannot be specified with any of ~a. Violating external spaces: ~a"
    "#:join, #:lesseq, #:equiv, #:cardinality, #:touch, or #:pretty"
    (syntax-e #'name))
   #:do [(define parse (and (attribute to-eval) (eval-syntax #'to-eval)))]
   #:attr desc (if (attribute flat)
                   (flat-ED (attribute quality))
                   (ED (attribute join)
                       (attribute lesseq)
                       (attribute equiv)
                       (attribute card)
                       (attribute touch)
                       (attribute quality)
                       (attribute pretty)
                       parse))))

(define-syntax-class User-names-cls
  #:attributes ((metas 1) name info)
  #:description "Specify a user-defined value space"
  (pattern [(~optional (metas:id ...) #:defaults ([(metas 1) '()]))
            name:id 
            (~or (~seq #:full :expr) (~seq :expr ...))
            u:Unrolling]
           #:do [(define dup (check-duplicate-identifier (attribute metas)))]
           #:fail-when dup
           (format "Space has duplicate metavariable identifiers (~a): ~a" (syntax-e #'name) dup)
           #:attr info (vector (attribute u.trust)
                               (attribute u.n))))

(define-syntax-class (User-cls options Unames Enames meta-table space-info ext)
  #:attributes ((metas 1) name ty)
  #:description "Specify a user-defined value space"
  (pattern
   (~and
    ;; get the trust info first
    [(~optional (:id ...)) :id (~or (~seq #:full :expr) (~seq :expr ... ))
     (~optional (~datum ....)) u:Unrolling]
    ;; use trust withing type parsing.
    [(~optional (metas:id ...) #:defaults ([(metas 1) '()]))
     name:id
     (~or (~seq #:full (~commit (~var fty (PreType options
                                                   (attribute u.trust)
                                                   Unames Enames
                                                   meta-table))))
          (~commit (~seq (~var sty (PreType options
                                            (attribute u.trust)
                                            Unames Enames
                                            meta-table)) ...)))
     (~optional (~and (~datum ....) extend))
     ;; shape only
     :Unrolling])
   #:fail-when (and (attribute fty.t) (attribute u))
   "Cannot specify full type and use #:bounded, #:trust-construction, or #:unfold"
   #:fail-unless (implies (attribute extend) 
                          (hash-has-key? (Language-user-spaces ext) (syntax-e #'name)))
   "Can't extend a space that didn't originally exist."
   #:do [(define pre-ty (*TRUnion #'(sty ...)
                                  (if (attribute extend)
                                      (cons
                                       (hash-ref (Language-user-spaces ext) (syntax-e #'name))
                                       (attribute sty.t))
                                      (attribute sty.t))))]
   #:fail-unless (set-empty? (free pre-ty))
   (format "Space's type contains free variables: ~a (~a)"
           (syntax-e #'name) (free pre-ty))
   #:attr ty pre-ty))

(define-splicing-syntax-class (Lang-options-cls lang)
  #:attributes (options op-lang)
  (pattern (~seq (~or (~optional (~and #:pun-space-names pun-space))
                      (~optional (~and #:require-metavariables require-meta))
                      (~optional (~and #:check-metavariables check-meta))
                      (~optional (~and #:include-pattern-namespace pattern-namespace))
                      (~optional (~and #:default-externalize ext))
                      (~optional (~and #:default-no-externalize next))
                      (~optional (~seq #:default-match-mode mm:Match-Mode))
                      (~optional (~seq #:default-equality-mode em:Equality-Mode))
                      (~optional (~seq #:default-lookup-mode lm:Lookup-Mode))
                      (~optional (~seq #:default-addr-space space:id))
                      ) ...)
           #:fail-when (and (syntax? (attribute ext)) (syntax? (attribute next)))
           "Must choose at most one of #:default-externalize #:default-no-externalize"
           #:do [(define base-ops
                   (if lang
                       (Language-options lang)
                       (hash)))
                 (define (do-op h . kvs)
                   (let rec ([h h] [kvs kvs])
                     (match kvs
                       ['() h]
                       [(list-rest k v kvs)
                        (rec (if (if (eq? k 'externalize) (boolean? v) v)
                                 (hash-set h k v) h)
                             kvs)]
                       [_ (error 'Lang-options-cls "internal error, odd kvs list: ~a" kvs)])))
                 (define ops
                   (do-op base-ops
                          'pun-space-names (syntax? (attribute pun-space))
                          'require-metavariables (syntax? (attribute require-meta))
                          'check-metavariables (syntax? (attribute check-meta))
                          'mm (attribute mm.mm)
                          'em (attribute em.em)
                          'lm (attribute lm.lm)
                          'externalize (cond
                                        [(syntax? (attribute ext)) #t]
                                        [(syntax? (attribute next)) #f]
                                        [else 'unset])
                          'addr-space (and (attribute space) (syntax-e #'space))
                          'include-pattern-namespace (syntax? (attribute pattern-namespace))))
                 (define L
                   (match lang
                     [(Language _ ES US oUS E<: meta-table u-info)
                      (Language ops ES US oUS E<: meta-table u-info)]
                     [_ #f]))]
           #:attr options ops
           #:attr op-lang L))

(define-syntax-class Language-externals/user-ids
  #:attributes (external-spaces
                meta-table uspace-info
                (enames 1) (edescs 1) (emetas 2) (unames 1) (umetas 2))
  (pattern ((~or ext:External-cls usr:User-names-cls) ...)
           #:attr external-spaces
           (for/hash ([Ext (in-list (attribute ext.name))]
                      [desc (in-list (attribute ext.desc))])
             (values (syntax-e Ext) desc))
           #:attr (enames 1) (attribute ext.name)
           #:attr (edescs 1) (attribute ext.desc)
           #:attr (emetas 2) (attribute ext.metas)
           #:attr (unames 1) (attribute usr.name)
           #:attr (umetas 2) (attribute usr.metas)
           ;; Ensure spaces unique
           #:do [(define all-space-names
                   (append (attribute enames) (attribute unames)))
                 (define space-name-dups
                   (check-duplicate-identifier all-space-names))]
           #:fail-when space-name-dups
           (format "Duplicate space name: ~a" space-name-dups)
           ;; Ensure metas unique
           #:do [(define all-metas
                   (append (append* (attribute emetas)) (append* (attribute umetas))))
                 (define all-duplicate (check-duplicate-identifier all-metas))]
           #:fail-when all-duplicate
           (format "Duplicate metavariable across spaces: ~a" all-duplicate)
           ;; Ensure metas and spaces don't overlap
           #:do [(define dup-meta-space (check-duplicate-identifier
                                         (append all-space-names all-metas)))]
           #:fail-when dup-meta-space
           (format "Metavariable conflicts with space name: ~a" dup-meta-space)
           ;; Point all metavariables to their space
           #:attr meta-table
           (for/fold ([h
                       ;; Point external metas to their space name
                       (for/fold ([h #hasheq()])
                           ([Ext (in-list (attribute enames))]
                            [metas (in-list (attribute emetas))])
                         (define ext-sym (syntax-e Ext))
                         (for/fold ([h h]) ([m (in-list metas)])
                           (hash-set h (syntax-e m) ext-sym)))])
               ;; Point user metas to their space name
               ([uname (in-list (attribute unames))]
                [metas (in-list (attribute umetas))])
             (define name-sym (syntax-e uname))
             (for/fold ([h h]) ([m (in-list metas)])
               (hash-set h (syntax-e m) name-sym)))
           #:attr uspace-info
           (let ([h (make-hasheq)])
             (for ([name (in-list (attribute unames))]
                   [info (in-list (attribute usr.info))])
               (hash-set! h (syntax-e name) info))
             h)))

(define (contains-externalized? ts)
  (for/or ([t (in-list ts)])
    (match (resolve t)
      [(or (TMap: _ _ _ ext) (TSet: _ _ ext)) ext]
      [_ #f])))

(define (any-union-contains-externalized? ty)
  (define seen (mutable-seteq))
  (let check ([ty ty])
    (if (set-member? seen ty)
        #f
        (begin
          (set-add! seen ty)
          (match ty
            [(or (Tμ: _ _ (Scope t) _ _) (TΛ: _ _ (Scope t)) (TSet: _ t _))
             (check t)]
            [(or (? T⊤?) (? TAddr?) (? TExternal?) (? TName?) (? TBound?) (? TFree?)) #f]
            [(or (TSUnion: sy ts) (TRUnion: sy ts))
             (if (contains-externalized? ts)
                 (or sy #t)
                 (ormap check ts))]
            [(TVariant: _ name ts _) (ormap check ts)]
            [(TCut: _ t* u) (check (resolve ty))]
            [(TMap: _ t-dom t-rng _)
             (or (check t-dom)
                 (check t-rng))])))))

;; TODO: sanity check that maps/sets that are "externalized" can't
;; be self-referential without an intermediate variant construction.
;; Possibly add trust tag, but ensure all types in mutual reference have
;; the same level of trust.
(define (check-externalized stx alst)
  (void))

(define (sset-map f s) (for/set ([u (in-set s)]) (f u)))

(define (parse-language stx [extending #f])
  (syntax-parse stx
    [((~optional (~seq #:extending extb:id))
      (~do (define lang (and (syntax? (attribute extb)) (syntax-local-value #'extb))))
      (~fail #:unless (implies (syntax? (attribute extb)) (Language? lang))
             (format "Value bound to ~a is not a Language value. Given ~a"
                     (syntax-e #'extb) lang))
      (~fail #:when (and extending lang)
             "Cannot explicitly give a base language ot parse-language and an #:extending form.")
      (~do (define ext (or extending lang)))
      (~var ops (Lang-options-cls ext))
      . rest)
     (syntax-parse #'rest
       [gather:Language-externals/user-ids
        ;; TODO: override/extend user classes in (or extending lang)
        (syntax-parse #'rest
          [((~or (~var usr (User-cls (attribute ops.options)
                                     (sset-map syntax-e (attribute gather.unames))
                                     (sset-map syntax-e (attribute gather.enames))
                                     (attribute gather.meta-table)
                                     (attribute gather.uspace-info)
                                     ext))
                 :External-shape) ...)
           (define local-dict
             (for/list ([space (in-list (attribute usr.name))]
                        [ty (in-list (attribute usr.ty))])
             (cons (syntax-e space) ty)))
           (define pre-Γ
             (if ext
                 (let ([h (make-hasheq pre-Γ)]
                       [eh (Language-user-spaces ext)])
                   (append
                    (for/list ([(name ty) (in-dict (Language-ordered-us ext))])
                      (cons name (hash-ref h name ty)))
                    (for/list ([pair (in-list local-dict)]
                               ;; not already pulled in as a rewrite?
                               #:unless (hash-has-key? eh (car pair)))
                      pair)))
                 local-dict))
           (check-externalized stx pre-Γ)
           ;; TODO: make sure unioned types aren't vaguely shaped,
           ;; make sure recursion (named or anonymous) is guarded.
           (define categorized-and-guarded
                   pre-Γ)
           (Language
            (attribute ops.options) ;; extended already
            (attribute gather.external-spaces) ;; TODO: extend ext
            (make-hasheq categorized-and-guarded)
            categorized-and-guarded
            ∅ ;; TODO: syntax for E<:
            (attribute gather.meta-table) ;; TODO: extend ext, check no cross-talk
            (attribute gather.uspace-info))])])])) ;; TODO: extend ext

(define (parse-reduction-relation stx [L (current-language)])
  (syntax-parse stx
    [((~var r (Rule-cls #t L)) ...) (attribute r.rule)]))

(define (parse-metafunction stx [L (current-language)])
  (syntax-parse stx
    [(name:id (~datum :)
              (~do (define options (Language-options L))
                   (define unames (hash-key-set (Language-user-spaces L)))
                   (define enames (hash-key-set (Language-external-spaces L)))
                   (define meta-table (Language-meta-table L)))
              (~and
               (~seq arrty ...)
               (~seq
                (~optional (~seq (~or #:Λ #:∀ #:all) (ta:id ...)))
                (~var formals (TopPreType options unames enames meta-table))
                ... (~or (~datum ->) (~datum →))
                (~var ret (TopPreType options unames enames meta-table))))
              (~var r (Rule-cls #f L)) ...)
     (define type-names (rev-map syntax-e (attribute ta)))
     ;; TODO: check that rules' patterns match (name args ...) for the type of name.
     (Metafunction (syntax-e #'name)
                   (quantify-frees
                    (mk-TArrow #'(arrty ...)
                     (mk-TVariant #'(formals ...) (syntax-e #'name) (attribute formals.t) 'untrusted)
                     (attribute ret.t))
                    type-names)
                   ;; There will be as many scopes on the rules as type quants
                   ;; in the mf type.
                   (abstract-frees-in-rules (attribute r.rule) type-names))]))
