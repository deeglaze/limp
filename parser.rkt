#lang racket/base
(require (for-syntax racket/base syntax/parse racket/syntax)
         syntax/parse racket/syntax racket/match racket/set racket/list
         syntax/srcloc
         "common.rkt"
         "language.rkt"
         "tast.rkt"
         "types.rkt"
         racket/pretty)
(provide parse-language
         parse-reduction-relation
         Rule-cls)


(module+ test (require rackunit))
(define limp-default-mm 'delay)
(define limp-default-em 'identity)
(define limp-default-addr-space 'limp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Fully annotated Limp code

(define (type-join t0 t1)
  (if (equal? t0 t1)
      t0
      (match* (t0 t1)
        [((TMap: d0 r0 ext) (TMap: d1 r1 ext))
         (mk-TMap (type-join d0 d1) (type-join r0 r1) ext)]
        [((TSet: s0 ext) (TSet: s1 ext))
         (mk-TSet (type-join s0 s1) ext)]
        [(_ _)
         (define ts (simplify-types (list t0 t1)))
         (if (vaguely-shaped? ts)
             T⊤
             (mk-TSUnion ts))])))

(define (type->sexp t)
  (match t
      [(TFree: x _) x]
      [(or (and (Tμ: x st _ _ _) (app (λ _ 'μ) head))
           (and (TΛ: x st) (app (λ _ 'Λ) head)))
       `(,head ,x ,(type->sexp (open-scope-hygienically st x)))]
      [(TVariant: name ts _ _)
       (cons name (map type->sexp ts))]
      [(or (and (TSUnion: ts) (app (λ _ '∪) head))
           (and (TRUnion: ts) (app (λ _ 'raw∪) head))
           (app (match-lambda [(TMap: d r _) (list '↦ d r)]
                              [(TSet: t _) (list '℘ t)]) (cons head ts)))
       `(,head . ,(map type->sexp ts))]
      [(TCut: t u)
       (list (type->sexp t) (type->sexp u))]
      [(? T⊤?) '⊤]
      [(TAddr: name mm em) `(Addr ,name ,mm ,em)]
      [(TExternal: name) name]
      [_ (error 'type->sexp "Bad type ~a" t)]))
(define (pretty-type t) (pretty-print (type->sexp t)))

(define (free->external t ES)
  (let/ec break
   (let rename ([t t])
     (match t
       [(TFree: x _)
        (if (hash-has-key? ES x)
            (mk-TExternal x)
            (break #f))]
       ;; boilerplate
       [(Tμ: x (Scope t) r c n) (mk-Tμ x (Scope (rename t)) r c n)]
       [(TΛ: x (Scope t)) (mk-TΛ x (Scope (rename t)))]
       [(or (? T⊤?) (? TAddr?) (? TBound?)) t]
       [(TSUnion: ts) (mk-TSUnion (map rename ts))]
       [(TRUnion: ts) (mk-TRUnion (map rename ts))]
       [(TVariant: name ts r c) (mk-TVariant name (map rename ts) r c)]
       [(TCut: t u) (mk-TCut (rename t) (rename u))]
       [(TMap: t-dom t-rng ext) (mk-TMap (rename t-dom) (rename t-rng) ext)]
       [(TSet: t ext) (mk-TSet (rename t) ext)]))))


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
  #:attributes (bounded? trust? n)
  (pattern (~seq (~or (~optional (~and trec #:bounded))
                      (~optional (~and tcon #:trust-construction))
                      (~optional (~seq #:unfold sn:nat))) ...)
           #:attr bounded? (syntax? (attribute trec))
           #:attr trust? (syntax? (attribute tcon))
           #:fail-when (and (attribute sn)
                            (or (attribute bounded?) (attribute trust?)))
           "Cannot specify both #:unfold and either #:bounded or #:trust-construction"
           #:attr n (if (attribute sn) (syntax-e #'sn) 0)))

(define-splicing-syntax-class (EM-Modes space? tag?)
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
           #:attr mm (attribute mm*.mm)
           #:attr em (attribute em*.em)
           #:attr tag (and (attribute tag-s) (syntax-e #'tag-s))
           #:attr space (and (attribute space-s) (syntax-e #'space-s))))

(define-splicing-syntax-class (EM-Modes-default ops space? tag?)
  #:attributes (em mm space tag)
  (pattern (~var modes (EM-Modes space? tag?))
           #:attr em (or (attribute modes.em)
                         (hash-ref ops 'equality-mode #f)
                         limp-default-em)
           #:attr mm (or (attribute modes.mm)
                         (hash-ref ops 'match-mode #f)
                         limp-default-mm)
           #:attr space (or (attribute modes.space)
                            (hash-ref ops 'addr-space #f)
                            limp-default-addr-space)
           #:attr tag (attribute modes.tag)))

(define-syntax-class (PreType bounded? trust?)
  #:attributes (t)
  #:local-conventions ([#rx"^t" (PreType bounded? trust?)])
  (pattern (#:Λ x:id tbody)
           #:attr t (mk-TΛ (syntax-e #'x) (abstract-free (attribute tbody.t) (syntax-e #'x))))
  (pattern (~and stx
                 (#:μ x:id (~var ty:expr) u:Unrolling
                      (~parse (~var tbody (PreType (attribute u.bounded?)
                                                   (attribute u.trust?)))
                              #'ty)))
           #:do [(define fv (free (attribute tbody.t)))
                 (define recursive? (set-member? fv (syntax-e #'x)))
                 (unless recursive?
                   (log-info (format "Recursive type ~a recursively bound variable: ~a (at ~a)"
                                     "does not refer to"
                                     (syntax-e #'x) (source-location-source #'stx))))]
           #:attr t (if recursive?
                        (mk-Tμ (syntax-e #'x)
                               (abstract-free (attribute tbody.t) (syntax-e #'x))
                               (attribute u.bounded?)
                               (attribute u.trust?)
                               (attribute u.n))
                        (attribute tbody.t)))
  (pattern (#:inst tf ta)
           #:attr t (mk-TCut (attribute tf.t) (attribute ta.t)))
  (pattern ((~or #:∪ #:union #:U) ts ...)
           #:attr t (*TRUnion (attribute ts.t)))
  ;; TODO: make abstraction annotations parse errors outside of define-language
  (pattern ((~or #:map #:↦) td tr (~optional (~and ext #:externalize)))
           #:attr t (mk-TMap (attribute td.t) (attribute tr.t) (syntax? (attribute ext))))
  (pattern ((~or #:set #:℘) ts (~optional (~and ext #:externalize)))
           #:attr t (mk-TSet (attribute ts.t) (syntax? (attribute ext))))
  (pattern (n:id ts ...)
           #:attr t (mk-TVariant (syntax-e #'n)
                                 (attribute ts.t)
                                 bounded?
                                 trust?))
  (pattern x:id #:attr t (mk-TFree (syntax-e #'x) #f))
  (pattern [#:ref x:id (~var modes (EM-Modes #t #f))]
           #:fail-unless (and (attribute modes.mm)
                              (attribute modes.em)
                              (attribute modes.space))
           "Must specify both match-mode and equality-mode"
           #:attr t (mk-TFree (syntax-e #'x)
                              (TAddr (attribute modes.space)
                                     (attribute modes.mm) 
                                     (attribute modes.em))))
  (pattern (~or #:⊤ #:top #:any) #:attr t T⊤))

(define-syntax-class TopPreType
  #:attributes (t)
  (pattern (~var ty (PreType #f #f))
           #:attr t (attribute ty.t)))

(module+ test
  (test-true "Pretype success"
             (syntax-parse #'(#:μ List (#:Λ y (#:∪ (mt) (cons y (#:inst List y)))))
               [:TopPreType #t]
               [_ #f])))

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
  (pattern _ #:when (hash-ref (Language-options) 'include-pattern-namespace #f)))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pattern syntax
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-syntax-class Wild (pattern (~or (~datum _) #:wild)))
(define-syntax-class (Pattern-cls L)
  #:attributes (pat)
  #:local-conventions ([#rx"^p" (Pattern-cls L)])
  (pattern (~or :Wild
                [:Wild (~optional (~var ct (Compulsary-type-op L)))])
           #:when (or (attribute ct.t)
                      ;; FIXME: shouldn't be in language?
                      (hash-ref (Language-options L) 'compulsary #f))
           #:attr pat (PWild (or (attribute ct.t) T⊤)))
  (pattern ((~var _ (pand L)) p ...)
           #:attr pat (PAnd #f (attribute p.pat)))
  (pattern ((~var _ (pmapwith L)) pk pv pm)
           #:attr pat (PMap-with #f
                                    (attribute pk.pat)
                                    (attribute pv.pat)
                                    (attribute pm.pat)))
  (pattern ((~var _ (pmapwith* L)) pk pv pm)
           #:attr pat (PMap-with* #f
                                     (attribute pk.pat)
                                     (attribute pv.pat)
                                     (attribute pm.pat)))
  (pattern ((~var _ (psetwith L)) pv ps)
           #:attr pat (PSet-with #f
                                    (attribute pv.pat)
                                    (attribute ps.pat)))
  (pattern ((~var _ (psetwith* L)) pv ps)
           #:attr pat (PSet-with* #f
                                    (attribute pv.pat)
                                    (attribute ps.pat)))
  (pattern ((~var _ (pname L)) x:id (~var ct (Compulsary-type-op L)))
           #:attr pat (PName (attribute ct.t) (syntax-e #'x)))
  (pattern ((~var _ (paddr L)) name:id
            (~var modes (EM-Modes-default (Language-options L) #f #f)))
           #:attr pat (PIsAddr (TAddr (syntax-e #'name (attribute modes.mm) (attribute modes.em)))))
  (pattern ((~var _ (pexternal L)) name:id)
           #:when (hash-has-key? (Language-external-spaces) (syntax-e #'name))
           #:attr pat (PIsExternal (mk-TExternal (syntax-e #'name))))
  (pattern (n:id p ...)
           #:attr pat (PVariant #f (syntax-e #'n) (attribute p.pat)))
  (pattern ((~var _ (pterm L)) (~var t (Term-cls L)))
           #:attr pat (PTerm #f (attribute t.tm)))
  (pattern ((~var _ (phastype L)) (~var t (Type-cls #t L)))
           #:when (mono-type? (attribute t.t))
           #:attr pat (PIsType (attribute t.t))))

(define-syntax-class (Type-cls allow-raw? L)
  #:attributes (t)
  (pattern pt:TopPreType
           #:do [(define t-op (check-productive-and-classify-unions (attribute pt.t) allow-raw?))
                 (define t-ext (and t-op (free->external t-op
                                                         (Language-external-spaces L))))]
           #:when (and t-ext)
           #:attr t t-ext))
(define-splicing-syntax-class (Compulsary-type-op L)
  #:attributes (t)
  (pattern (~var ty (Type-cls #t (Language-external-spaces L)))
           #:attr t (Check (attribute ty.t)))
  (pattern (~seq #:cast (~var ty (Type-cls #t (Language-external-spaces L))))
           #:attr t (Cast (attribute ty.t)))
  (pattern (~seq)
           #:when (hash-ref (Language-options L) 'compulsary #f)
           #:attr t #f))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Limp Terms
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax-class (Term-cls L)
  #:attributes (tm)
  #:local-conventions ([#rx"^t" (Term-cls L)])
  (pattern (#:set t ...) #:attr tm (Set #f (apply set (attribute t.tm))))
  (pattern (#:map (~seq tk tv) ...)
           #:attr tm (Map #f (for/hash ([k (in-list (attribute tk.tm))]
                                            [v (in-list (attribute tv.tm))])
                                   (values k v))))
  (pattern (n:id t ...)
           #:attr tm (Variant #f (syntax-e #'n) (attribute t.tm)))
  (pattern (#:external name:id v)
           #:attr tm (External (syntax-e #'name) #'v))
  ;; Those didn't work. What about the external spaces?
  (pattern v
           #:do [(define ext
                   (for/or ([(name ed) (in-hash
                                        (Language-external-spaces L))]
                            #:when (let ([p (ED-parse ed)])
                                     (and p (p #'v))))
                     name))]
           #:when ext
           #:attr tm (External ext #'v)))

(define-syntax-class (Expression-cls L)
  #:attributes (e)
  #:local-conventions ([#rx"^e" (Expression-cls L)]
                       [#rx"^r" (Rule-cls #f L)])
  (pattern (#:call f:id es ...)
           ;; TODO: check f bound here?
           #:attr e (ECall #f (syntax-e #'f) (attribute es.e)))
  (pattern (#:lookup ek (~var ct (Compulsary-type-op L)))
           #:attr e (EStore-lookup (or (attribute ct.t) T⊤) (attribute ek.e)))
  (pattern (#:alloc (~var ops (EM-Modes-default (Language-options L) #t #t)))
           #:attr e (EAlloc (TAddr (attribute ops.space) (attribute ops.mm) (attribute ops.em))
                            (attribute ops.tag)))
  (pattern (#:let [(~var bus (Binding-updates-cls L))] ebody)
           #:attr e (ELet (Typed-ct (attribute ebody.e))
                          (attribute bus.bus)
                          (attribute ebody.e)))
  (pattern (#:match edisc rules ...)
           #:attr e (EMatch #f (attribute edisc.e)
                            (attribute rules.rule)))
  (pattern (#:extend em ek ev)
           #:attr e (EExtend #f (attribute em.e) (attribute ek.e) (attribute ev.e)))
  (pattern #:empty-map #:attr e (EEmpty-Map (TMap T⊥ T⊥ #f)))
  (pattern [#:empty-map (~describe
                         "Map type"
                         (~and (~var ct (Compulsary-type-op L))
                               (~fail #:unless
                                      (match (attribute ct.t)
                                        [(or (Check (? TMap?)) (Cast (? TMap?)))
                                         #t]
                                        [_ #f]))))]
           #:attr e (EEmpty-Map (attribute ct.t)))
  (pattern #:empty-set #:attr e (EEmpty-Set (TSet T⊥ #f)))
  (pattern [#:empty-set (~describe
                         "Set type"
                         (~and (~var ct (Compulsary-type-op L))
                               (~fail #:unless
                                      (match (attribute ct.t)
                                        [(or (Check (? TSet?)) (Cast (? TSet?)))
                                         #t]
                                        [_ #f]))))]
           #:attr e (EEmpty-Set (attribute ct.t)))
  (pattern (#:add es ev)
           #:attr e (ESet-add #f (attribute es.e) (attribute ev.e)))
  (pattern (n:id es ...)
           #:attr e (EVariant (mk-TVariant (syntax-e #'n)
                                           (map Typed-ct (attribute es.e)))
                              (attribute es.e)))
  ;; TODO: use some binding environment? Check afterwards?
  (pattern x:id #:attr e (ERef #f (syntax-e #'x)))

  ;; Extra builtins
  (pattern (#:union es ...) #:attr e (ESet-union #f (attribute es.e)))
  (pattern (#:intersection e0 es ...) #:attr e (ESet-intersection #f (attribute e0.e) (attribute es.e)))
  (pattern (#:subtract e0 es ...) #:attr e (ESet-subtract #f (attribute e0.e) (attribute es.e)))
  (pattern (#:remove e0 ev) #:attr e (ESet-remove #f (attribute e0.e) (attribute ev.e)))
  (pattern (#:member? es ev) #:attr e (ESet-member #f (attribute es.e) (attribute ev.e)))
  (pattern (#:map-lookup em ek) #:attr e (EMap-lookup #f (attribute em.e) (attribute ek.e)))
  (pattern (#:has-key? em ek) #:attr e (EMap-has-key #f (attribute em.e) (attribute ek.e)))
  (pattern (#:map-remove em ek) #:attr e (EMap-remove #f (attribute em.e) (attribute ek.e))))

(define-syntax-class (Binding-update-cls L)
  #:attributes (bu)
  #:local-conventions ([#rx"^e" (Expression-cls L)])
  (pattern [#:where (~var p (Pattern-cls L)) e]
           #:attr bu (Where (attribute p.pat) (attribute e.e)))
  (pattern [#:update ek ev]
           #:attr bu (Update (attribute ek.e) (attribute ev.e))))

(define-splicing-syntax-class (Binding-updates-cls L)
  #:attributes (bus)
  (pattern (~seq) #:attr bus '())
  (pattern (~seq (~var bu (Binding-update-cls L)) (~var bs (Binding-updates-cls L)))
           #:attr bus (cons (attribute bu.bu) (attribute bs.bus))))

(define-syntax-class (Rule-cls arrow? L)
  #:attributes (rule)
  (pattern [(~and #:rule (~fail #:unless arrow?))
            (~optional (~seq #:name name:id))
            (~var p (Pattern-cls L))
            (~var e (Expression-cls L))
            (~var bus (Binding-updates-cls L))]
           #:attr rule (Rule (and (attribute name) (syntax-e #'name))
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
           #:attr info (vector (attribute u.bounded?)
                               (attribute u.trust?)
                               (attribute u.n))))

(define-syntax-class (User-cls options ES meta-table space-info)
  #:attributes ((metas 1) name ty)
  #:description "Specify a user-defined value space"
  (pattern [(~optional (metas:id ...) #:defaults ([(metas 1) '()]))
            name:id
            (~or (~seq #:full (~commit fty:TopPreType))
                 (~commit (~seq sty:TopPreType ...)))
            ;; shape only
            u:Unrolling]
           #:fail-when (and (attribute fty.t) (attribute u))
           "Cannot specify full type and use #:bounded, #:trust-construction, or #:unfold"
           #:do [(define pre-ty (close-type-with
                                 (if (attribute fty.t)
                                     (attribute fty.t)
                                     (*TRUnion (attribute sty.t)))
                                 ES
                                 meta-table
                                 space-info
                                 '()))]
           #:fail-unless pre-ty
           (format "Space's type contains free variables: ~a" (syntax-e #'name)) ;; TODO: give free variables
           #:attr ty pre-ty))

(define-splicing-syntax-class Lang-options-cls
  #:attributes (options)
  (pattern (~seq (~or (~optional (~and #:pun-space-names pun-space))
                      (~optional (~and #:require-metavariables require-meta))
                      (~optional (~and #:check-metavariables check-meta))
                      (~optional (~and #:include-pattern-namespace pattern-namespace))
                      (~optional (~seq #:default-match-mode mm:Match-Mode))
                      (~optional (~seq #:default-equality-mode em:Equality-Mode))
                      (~optional (~seq #:default-addr-space space:id))) ...)
           #:attr options
           (hash 'pun-space-names (syntax? (attribute pun-space))
                 'require-metavariables (syntax? (attribute require-meta))
                 'check-metavariables (syntax? (attribute check-meta))
                 'match-mode (attribute mm.mm)
                 'equality-mode (attribute em.em)
                 'addr-space (and (attribute space) (syntax-e #'space))
                 'include-pattern-namespace (syntax? (attribute pattern-namespace)))))

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
           (for/hash ([name (in-list (attribute unames))]
                      [info (in-list (attribute usr.info))])
             (values (syntax-e name) info))))

(define (contains-externalized? ts Γ)
  (for/or ([t (in-list ts)])
    (match (resolve t Γ)
      [(or (TMap: _ _ ext) (TSet: _ ext)) ext]
      [_ #f])))

(define (any-union-contains-externalized? ty Γ)
  (let check ([ty ty])
   (match ty
     [(or (Tμ: _ (Scope t) _ _ _) (TΛ: _ (Scope t)) (TSet: t _))
      (check t)]
     [(or (? T⊤?) (? TAddr?) (? TExternal?) (? TName?) (? TBound?) (? TFree?)) #f]
     [(or (TSUnion: ts) (TRUnion: ts))
      (or (contains-externalized? ts Γ)
          (ormap check ts))]
     [(TVariant: name ts r c) (ormap check ts)]
     [(TCut: t* u) (check (resolve ty))]
     [(TMap: t-dom t-rng _)
      (or (check t-dom)
          (check t-rng))])))

;; Check that all occurrences of #:externalize are not in a union.
(define (check-externalized stx Γ)
  (for ([ty (in-hash-values Γ)])
    (when (any-union-contains-externalized? ty Γ)
      (raise-syntax-error #f (format "Cannot have externalized type in a union: ~a" ty) stx))))

(define (parse-language stx)
  (syntax-parse stx
    [(ops:Lang-options-cls . rest)
     (syntax-parse #'rest
       [gather:Language-externals/user-ids
        (define rename-table
          (for/fold ([h (attribute gather.meta-table)])
              ([name (in-sequences
                      (in-list (attribute gather.enames))
                      (in-list (attribute gather.unames)))])
            (define symbol (syntax-e name))
            (hash-set h symbol symbol)))
        (syntax-parse #'rest
          [((~or (~var usr (User-cls (attribute ops.options)
                                     (attribute gather.external-spaces)
                                     rename-table
                                     (attribute gather.uspace-info)))
                 :External-shape) ...)
           (define pre-Γ
             (for/hash ([space (in-list (attribute usr.name))]
                        [ty (in-list (attribute usr.ty))])
               (values (syntax-e space) ty)))
           (check-externalized stx pre-Γ)
           #;
           (define level-names
             (produce-unfold-names pre-Γ (attribute gather.uspace-info)))
           #;
           (define unfolded
             (for/hash ([(n ty) (in-hash pre-Γ)])
               (values n (perform-unfolds level-names ty))))
           ;; TODO
           (define categorized-and-guarded
                   pre-Γ)
           (Language
            (attribute ops.options)
            (attribute gather.external-spaces)
            categorized-and-guarded
            (attribute gather.meta-table)
            (attribute gather.uspace-info))])])]))

(define (parse-reduction-relation stx L)
  (syntax-parse stx
    [((~var r (Rule-cls #t L)) ...) (attribute r.rule)]))

(define (parse-metafunction stx L)
  (syntax-parse stx
    [(name:id (~datum :)
              (~optional (~seq (~or #:∀ #:all) (ta:id ...)))
              formals:TopPreType ... (~datum ->) ret:TopPreType
              (~var r (Rule-cls #f L)) ...)
     ;; TODO: check that rules' patterns match (name args ...) for the type of name.
     (Metafunction (syntax-e #'name)
                   (close-type-with
                    (TArrow (TVariant (syntax-e #'name) (attribute formals.t) #f #f)
                            (attribute ret.t))
                    (Language-external-spaces L)
                    (Language-meta-table L)
                    (Language-uspace-info L)
                    ;; forall variables
                    (if (attribute ta)
                        (map syntax-e (attribute ta))
                        '()))
                   (attribute r))]))

(module+ test
  (parse-language
   #'([Expr (app Expr Expr) x (lam x Expr)]
      [(x) #:external Name #:parse identifier?])))
#|
 (Language '#hash((pun-space-names . #f) (require-metavariables . #f) (check-metavariables . #f) (match-mode . #f) (equality-mode . #f) (addr-space . #f) (include-pattern-namespace . #f))
           '#hash((Name . #<ED>))
           (hash 'Expr
                 (TRUnion 12 #f #f #f 'unset
                          (list (TVariant 10 #f #f #f 'unset 'lam
                                          (list #0=(TExternal 8 #f #f #f 'unset 'Name)
                                                #1=(TName 9 #f #f #f 'unset 'Expr #f)) #f #f)
                                #0#
                                (TVariant 11 #f #f #f 'unset 'app (list #1# #1#) #f #f))))
           '#hasheq((x . Name))
           '#hash((Expr . #(#f #f 0))))
|#
