#lang racket/base
(require (for-syntax syntax/parse racket/syntax racket/base)
         (only-in racket/bool implies)
         (only-in racket/function const)
         racket/list racket/match racket/set (only-in racket/function curry)
         racket/trace racket/pretty
         (only-in unstable/sequence in-pairs)
         "common.rkt" "language.rkt")
(provide (all-defined-out))

(define instantiations (make-parameter #f))
(define heapifying? (make-parameter #f))

;; Cast or Check annotations?
(struct Cast (t) #:transparent)
(struct Check (t) #:transparent)
(struct Deref (taddr ct) #:transparent)
(define πct (match-lambda
             [(or (Cast t) (Check t)) t]
             [(Deref _ ct) (πct ct)]
             [_ #f]))
(define (ct-replace-τ ct τ)
  (match ct
    [(Cast _) (Cast τ)]
    [(Check _) (Check τ)]
    ;; If replacing a Deref, it's for inserting coercions,
    ;; so we remove the deref at this point.
    [(? Deref?) (error 'ct-replace-τ "Uh oh. Deref of THeap? ~a" ct)]))

(define (to-cast ct)
  (match ct
    [(Check σ) (if (T⊤? σ) ct (Cast σ))]
    [(? Cast?) ct]
    [(? Deref?) (error 'to-cast "Impossible? ~a" ct)]))

(define type-error-fn (make-parameter
                       (λ (fmt . args)
                          (Check (TError (list (apply format fmt args)))))))
(define-syntax-rule (type-error f e ...)
  ((type-error-fn) f e ...))

(define type-print-verbosity (make-parameter 0))

(define (as-named τ)
  (and (< (type-print-verbosity) 2)
       (let ()
         (define us (Language-ordered-us (current-language)))
         (define clean
           (if (= (type-print-verbosity) 1)
               (λ (name) `(fold$ ,name))
               values))
         (for/first ([(name σ) (in-pairs us)] #:when (equal? τ σ))
           (clean name)))))

(define (type->sexp t)
  (define v (type-print-verbosity))
  (let rec ([t t])
    (define (ref head x)
      (if (> v 1)
          `(,head ,x)
          x))
    (or (as-named t)
        (match t
          [(TName: _ x) (ref 'name$ x)]
          [(TFree: _ x) (ref 'ref$ x)]
          [(TExternal: _ x) (ref 'ext$ x)]
          [(or (and (Tμ: _ x st _ _) (app (λ _ '#:μ) head))
               (and (TΛ: _ x st _) (app (λ _ '#:Λ) head)))
           `(,head ,x ,(rec (open-scope-hygienically st x)))]
          [(TVariant: _ name ts tr)
           (define base `(ty$ ,name . ,(map rec ts)))
           (if (> v 0)
               (append base
                       (case tr
                         [(bounded) '(#:bounded)]
                         [(trusted) '(#:trust-construction)]
                         [(untrusted) (if (> v 1) '(#:untrusted) '())]
                         [else (if (> v 1) '(#:any) '())]))
               base)]
          [(? T⊥?) '⊥]
          [(TUnion: _ ts)
           `(#:∪ . ,(map rec ts))]
          [(TMap: _ d r ext) `(↦ ,(rec d) ,(rec r) ,ext)]
          [(TSet: _ s ext) `(℘ ,(rec s) ,ext)]
          [(TCut: _ s u)
           `(#:inst ,(rec s) ,(rec u))]
          [(? T⊤?) '⊤]
          [(TAddr: _ name mm em) `(Addr ,name ,(and mm (s->k mm)) ,(and em (s->k em)))]
          [(TArrow: _ dom rng) `(#:-> ,(rec dom) ,(rec rng))]
          [(TBound: _ i) `(deb$ ,i)]
          ;; Non-types
          [(TUnif _ τ) `(Unif$ ,(rec τ))]
          [(TError msgs) `(Error . ,msgs)]
          [(THeap: _ taddr tag τ)
           (if (> v 1)
               `(#:heapify ,(if (symbol? taddr) taddr (rec taddr))
                           ,tag
                           ,(rec τ))
               (rec τ))]
          [#f '_] ;; Missing type
          [_ `(Unknown$ ,(struct->vector t))]))))


(define (write-type t port mode)
  (display (type->sexp t) port))

(struct Kind () #:transparent)
(struct Star Kind () #:transparent)
(struct K→ Kind (From To) #:transparent)

;; Type representations are structurally unique by an intern key.
;; Various properties are memoized: support, free vars, quality and monomorphic?
(struct Type (key support free quality mono? stx) #:mutable #:transparent
        #:methods gen:equal+hash
        [(define (equal-proc t0 t1 rec) (eqv? (Type-key t0) (Type-key t1)))
         (define (hash-proc t rec) (rec (Type-key t)))
         (define (hash2-proc t rec) (rec (Type-key t)))]
        #:property prop:custom-print-quotable 'never
        #:methods gen:custom-write
        [(define write-proc write-type)])
(define intern-table (make-hash))
(define-syntax (define-type stx)
  (syntax-parse stx
    [(_ name fields)
     (define/with-syntax mk-name (format-id #'name "mk-~a" #'name))
     (define/with-syntax name: (format-id #'name "~a:" #'name))
     #`(begin #,(syntax/loc stx (struct name Type fields #:transparent))
              #,(syntax/loc stx
                  (define (mk-name syn . fields)
                    (hash-ref! intern-table (list 'name . fields)
                               (λ () (name (hash-count intern-table) #f #f #f 'unset syn . fields)))))
              #,(syntax/loc stx
                 (define-match-expander name:
                   (syntax-rules () [(_ syn . fields) (name _ _ _ _ _ syn . fields)]))))]))
(struct base-T⊤ Type () #:transparent)
  (define T⊤ (base-T⊤ 0 ∅eq ∅eq 'abstract #t #f))
  (hash-set! intern-table '(T⊤) T⊤)
  (define (T⊤? x) (eq? T⊤ x))
(define-type TUnion (ts))
  (define T⊥ (TUnion 1 ∅eq ∅eq 'concrete #t #f '()))
  (hash-set! intern-table '(T⊥) T⊥)
  (define (T⊥? x) (eq? T⊥ x))
(struct permissive ()) (define Tpermissive (permissive))
(define-type TVariant (name ts trust)) ;; trust is a Trust-Tag
(define-type TExternal (name))
(define-type Tμ (x st tr n)) ;; name for printing
(define-type TΛ (x #;kind st on-app
                 ))
(define-type TCut (t u))
(define-type TName (x)) ;; top level interaction and letrec-like binding
(define-type TMap (t-dom t-rng ext))
(define-type TSet (t ext))
(define -tbool (mk-TExternal #'boolean 'boolean))
;; the final boolean is if the type is meant to kill unions and force heap allocation.
(define-type TAddr (space mm em))
;; First order function
(define-type TArrow (dom rng))
;; Locally nameless stuff. References have their address target post-abstraction.
(struct Scope (t) #:transparent)
(define-type TFree (x))
(define-type TBound (i))
(define-type TWeak (τ))
;; Marked to be heap-allocated when transformed.
(define-type THeap (taddr tag τ))
;; Unification variable
(struct TUnif ([tag #:mutable] [τ #:mutable]) #:transparent ;; use tag to make it appear non-transparent for equality.
        #:methods gen:custom-write [(define write-proc write-type)])
;; Error placeholder
(struct TError (msgs) #:transparent
        #:methods gen:custom-write [(define write-proc write-type)])

(define generic-TAddr (mk-TAddr #f #f #f #f))

(define (*THeap who sy taddr tag τ)
  (when (THeap? τ) (error '*THeap "~a: bad construction ~a" who (list sy taddr tag τ)))
  (mk-THeap sy taddr tag τ))

(define (*TVariant sy n tσ tr)
  (if (for/or ([σ (in-list tσ)]) (T⊥? σ))
      T⊥
      (mk-TVariant sy n tσ tr)))

;; A Trust-Tag is one of
;; - 'untrusted 
;; - 'bounded [only destructed]
;; - 'trusted [allowed to be constructed without heap-allocation]
;; trusted ⊏ bounded ⊏ untrusted
;; A special "undefined" (#f) that jumps up or down depending on join/meet is also allowed
(define (untrusted? x) (eq? x 'untrusted))

;; #f is bottom
(define (⊔trust b0 b1) (cond [(not b0) b1]
                         [(not b1) b0]
                         [(eq? b0 'trusted) b1]
                         [(eq? b1 'trusted) b0]
                         [(eq? b0 'bounded) b1]
                         [(eq? b1 'bounded) b0]
                         [else 'untrusted]))

;; #f is top
(define (⊓trust b0 b1)
  (cond [(not b0) b1]
        [(not b1) b0]
        [(eq? b0 'untrusted) b1]
        [(eq? b1 'untrusted) b0]
        [(eq? b0 'bounded) b1]
        [(eq? b1 'bounded) b0]
        [else 'trusted]))

(define (⊔b e0 e1)
  (cond [(eq? e0 'dc) e1]
        [(eq? e1 'dc) e0]
        [else (or e0 e1)]))

(define (⊓b e0 e1)
  (cond [(eq? e0 'dc) e1]
        [(eq? e1 'dc) e0]
        [else (and e0 e1)]))

(define (⋈flat f0 f1)
  ;; Debugging assertion
  (when (or (eq? f0 'dc) (eq? f1 'dc))
    (error '⋈flat "'dc not bottom for flat non-boolean elements: ~a, ~a" f0 f1))
  (cond
   [(and f0 f1) (if (equal? f0 f1)
                    f0
                    unmapped)]
   [else (or f0 f1)]))

(define generic-set (mk-TSet #f T⊤ 'dc))
(define generic-map (mk-TMap #f T⊤ T⊤ 'dc))
(define (generic-variant n arity)
  (mk-TVariant #f n (make-list arity T⊤) #f))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Binding/naming operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (open-scope s t)
  (match-define (Scope t*) s)
  (open-scope-aux t* 0 t))

(define (combine-taddr t0 t1 on-fail)
  (match* (t0 t1)
    [((TAddr: _ space0 mm0 em0) (TAddr: _ space1 mm1 em1))
     (define space (⋈flat space0 space1))
     (define mm (⋈flat mm0 mm1))
     (define em (⋈flat em0 em1))
     (if (or (unmapped? space) (unmapped? mm) (unmapped? em))
         (on-fail t0 t1)
         (mk-TAddr #f space mm em))]))

;; If we substituted in a heap allocation under a heap allocation,
;; duplicate the type with different allocation tags if they are indeed different.
(define (combine-THeap sy taddr tag σ)
  (match σ
    [(THeap: _ taddr* tag* τ*)
     (*THeap #f sy tag
             (combine-taddr taddr taddr*
                            (λ _ 
                               (TError sy
                                       (list (format "~a in heapified type: ~a ~a"
                                                     "Could not combine addresses"
                                                     taddr taddr*)))))
             τ*)]
    [τ* (*THeap 'combine0 sy taddr tag τ*)]))

(define (open-scope-aux t* i t)
  (let open ([t* t*] [i i])
    (define (open* t*) (open t* i))
    (match t*
      [(TBound: _ i*) (if (= i i*) t t*)]
      [(Tμ: sy x (Scope t) tr n) (mk-Tμ sy x (Scope (open t (add1 i))) tr n)]
      [(TΛ: sy x (Scope t) on-app) (mk-TΛ sy x (Scope (open t (add1 i))) on-app)]
      ;; boilerplate
      [(or (? T⊤?) (? TAddr?) (? TFree?) (? TExternal?) (? TName?) (? TUnif?) (? TError?)) t*]
      [(? T⊥?) T⊥] ;; don't make another ⊥
      [(TUnion: sy ts) (mk-TUnion sy (map open* ts))]
      [(TVariant: sy name ts tr) (mk-TVariant sy name (map open* ts) tr)]
      [(TCut: sy t u) (mk-TCut sy (open* t) (open* u))]
      [(TMap: sy t-dom t-rng ext) (mk-TMap sy (open* t-dom) (open* t-rng) ext)]
      [(TSet: sy t ext) (mk-TSet sy (open* t) ext)]
      [(TWeak: sy τ) (mk-TWeak sy (open* τ))]
      [(THeap: sy taddr tag τ) (combine-THeap sy taddr tag (open* τ))]
      ;; second-class citizens
      [(TArrow: sy d r) (mk-TArrow sy (open* d) (open* r))]
      [(TUnif _ τ) (open* τ)]
      [_ (error 'open-scope "Bad type ~a" t*)])))

;; predictable name generation over gensym.
(define (fresh-name supp base)
  (cond
   [(set-member? supp base)
    (define base-str (symbol->string base))
    (let bump ([i 0])
      (define numbered
        (string->symbol (string-append base-str (number->string i))))
      (if (set-member? supp numbered)
          (bump (add1 i))
          numbered))]
   [else base]))

(define ((name-conflict-res name on-conflict) f x t rec)
  (cond [(equal? x name)
         (when on-conflict (on-conflict))
         (f (fresh-name (set-add (support t) x) x) (rec t))]
        [else (f x (rec t))]))

;; for correct printing, sometimes clobbering old names
(define (open-scope-hygienically s name [on-conflict #f])
  (match-define (Scope t*) s)
  (define conflict-res (name-conflict-res name on-conflict))
  (let open ([t* t*] [i 0])
    (define (open* t*) (open t* i))
    (define (rec t) (Scope (open t (add1 i))))
    (match t*
      [(TBound: sy i*) (if (= i i*) (mk-TFree sy name) t*)]
      [(Tμ: sy x (Scope t) tr n) (conflict-res (λ (x s) (mk-Tμ sy x s tr n)) x t rec)]
      [(TΛ: sy x (Scope t) on-app) (conflict-res (λ (x s) (mk-TΛ sy x s on-app)) x t rec)]
      ;; boilerplate
      [(or (? T⊤?) (? TAddr?) (? TFree?) (? TExternal?) (? TName?)) t*]
      [(? T⊥?) T⊥] ;; don't make another ⊥
      [(TUnion: sy ts) (mk-TUnion sy (map open* ts))]
      [(TVariant: sy name ts tr) (mk-TVariant sy name (map open* ts) tr)]
      [(TCut: sy t u) (mk-TCut sy (open* t) (open* u))]
      [(TMap: sy t-dom t-rng ext) (mk-TMap sy (open* t-dom) (open* t-rng) ext)]
      [(TSet: sy t ext) (mk-TSet sy (open* t) ext)]
      [(TWeak: sy τ) (mk-TWeak sy (open* τ))]
      ;; second-class citizens
      [(TArrow: sy d r) (mk-TArrow sy (open* d) (open* r))]
      [(TUnif _ τ) (open* τ)]
      [(THeap: sy taddr tag τ) (*THeap 'open-scope-hygienically sy taddr tag (open* τ))]
      [(? permissive?) t*]
      [_ (error 'open "Bad type ~a" t*)])))
 
(define (subst-name t name s)
  (define conflict-res (name-conflict-res name #f))
  (let subst ([t t])
    (match t
      [(TName: _ x)
       (if (equal? x name)
           s
           t)]
      [(Tμ: sy x (Scope t) tr n) (conflict-res (λ (x s) (mk-Tμ sy x s tr n)) x t subst)]
      [(TΛ: sy x (Scope t) on-app) (conflict-res (λ (x s) (mk-TΛ sy x s on-app)) x t subst)]
      ;; boilerplate
      [(or (? T⊤?) (? TAddr?) (? TFree?) (? TExternal?) (? TBound?)) t]
      [(? T⊥?) T⊥] ;; don't make another ⊥
      [(TUnion: sy ts) (mk-TUnion sy (map subst ts))]
      [(TVariant: sy name ts tr) (mk-TVariant sy name (map subst ts) tr)]
      [(TCut: sy t u) (mk-TCut sy (subst t) (subst u))]
      [(TMap: sy t-dom t-rng ext) (mk-TMap sy (subst t-dom) (subst t-rng) ext)]
      [(TSet: sy t ext) (mk-TSet sy (subst t) ext)]
      [(TWeak: sy t) (mk-TWeak sy (subst t))]
      [(THeap: sy taddr tag τ) (combine-THeap sy taddr tag (subst τ))]
      [(? permissive?) t]
      [_ (error 'subst-name "Bad type ~a" t)])))

(define (abstract-free-aux t i name taddr*)
  (let abs ([t t] [i i])
    (define (abs* t) (abs t i))
    (match t
      [(TFree: sy x)
       (if (equal? x name)
           (mk-TBound sy i
                      #;
                      (cond
                       [(eq? taddr 'trusted) #f] ;; 'trusted has behavior of #f when closed.
                       [taddr]                   ;; return self
                       ;; override typing if there isn't already one.
                       [else (and (not (eq? taddr* 'trusted)) taddr*)]))
           t)]
      [(Tμ: sy x (Scope t) tr n) (mk-Tμ sy x (Scope (abs t (add1 i))) tr n)]
      [(TΛ: sy x (Scope t) on-app) (mk-TΛ sy x (Scope (abs t (add1 i))) on-app)]
      ;; boilerplate
      [(or (? T⊤?) (? TAddr?) (? TBound?) (? TName?) (? TUnif?) (? TError?) (? TExternal?)) t]
      [(? T⊥?) T⊥] ;; don't make another ⊥
      [(TUnion: sy ts) (mk-TUnion sy (map abs* ts))]
      [(TCut: sy t u) (mk-TCut sy (abs* t) (abs* u))]
      [(TVariant: sy name ts tr) (mk-TVariant sy name (map abs* ts) tr)]
      [(TMap: sy t-dom t-rng ext) (mk-TMap sy (abs* t-dom) (abs* t-rng) ext)]
      [(TSet: sy t ext) (mk-TSet sy (abs* t) ext)]
      [(TWeak: sy t) (mk-TWeak sy (abs* t))]
      [(TArrow: sy d r) (mk-TArrow sy (abs* d) (abs* r))]
      [(THeap: sy taddr tag τ) (*THeap 'abstract-free sy taddr tag (abs* τ))]
      [(? permissive?) t]
      [_ (error 'abstract-free "Bad type ~a" t)])))

(define (abstract-free t name [taddr* #f])
  (Scope (abstract-free-aux t 0 name taddr*)))

(define (uninhabitable? t Γ)
  (define us (Language-user-spaces (current-language)))
  (define (rec t guarded? A)
    (define (rec* t) (rec t guarded? A))
    (or (set-member? A t)
        (match t
          [(TUnif _ τ) (rec τ guarded? (set-add A t))]
          [(Tμ: _ x s _ _)
           (rec (open-scope s (mk-TFree #f x)) #f A)]
          [(TΛ: _ _ s _) (rec* (open-scope s T⊤))]
          [(TName: _ x)
           (rec (hash-ref us x)
                guarded?
                (set-add A t))]
          [(? TFree?) (or (not guarded?) ;; guarded recursive type variable
                          ;; the variable exists in the environment
                          (for/or ([τ (in-hash-values Γ)])
                            (equal? t τ)))]
          [(? TError?) #t]
          [(or (? T⊤?) (? TAddr?) (? TBound?) (? TExternal?)) #f]
          ;; Resimplify, since unification may have bumped some stuff up.
          [(TUnion: _ ts) (andmap rec* ts)]
          [(TCut: _ l r)
           (let open ([l l] [A A] [k (λ (A Λs) (rec (open-scope Λs r) guarded? A))])
             (match l
               [(TName: _ x)
                (or (set-member? A l)
                    (open (hash-ref us x) (set-add A l) k))]
               [(TCut: _ ll rr)
                (open ll (λ (A Λs) (k A (open (open-scope Λs rr)))))]
               [(TΛ: _ _ s _) (k A s)]
               [t (error 'uninhabitable? "Couldn't resolve ~a" t)]))]
          [(TVariant: sy name ts tr) (for/or ([t (in-list ts)]) (rec t #t A))] ;; *TVariant
          [(? TMap?) #f]
          [(? TSet?) #f]
          [(or (THeap: _ _ _ τ) (TWeak: _ τ)) (rec* τ)]
          [(TArrow: sy dom rng) #f]
          [_ (error 'uninhabitable? "Bad type ~a" t)])))
  (rec t #f ∅eq))

;; Remove mutable unification variables.
(define (freeze t [∪ mk-TUnion])
  (let rec ([t t])
    (match t
      [(TUnif _ τ) (rec τ)]
      ;; boilerplate
      [(Tμ: sy x (Scope t) tr n) (mk-Tμ sy x (Scope (rec t)) tr n)]
      [(TΛ: sy x (Scope t) on-app) (mk-TΛ sy x (Scope (rec t)) on-app)]
      [(or (? T⊤?) (? TAddr?) (? TBound?) (? TName?) (? TFree?) (? TError?) (? TExternal?)) t]
      ;; Resimplify, since unification may have bumped some stuff up.
      [(TUnion: sy ts) (∪ sy (map rec ts))]
      [(TCut: sy t u) (mk-TCut sy (rec t) (rec u))]
      [(TVariant: sy name ts tr) (*TVariant sy name (map rec ts) tr)] ;; *TVariant
      [(TMap: sy t-dom t-rng ext) (mk-TMap sy (rec t-dom) (rec t-rng) ext)]
      [(TSet: sy t ext) (mk-TSet sy (rec t) ext)]
      [(TWeak: sy t) (mk-TWeak sy (rec t))]
      [(THeap: sy taddr tag τ) (*THeap 'rec sy taddr tag (rec τ))]
      [(TArrow: sy dom rng) (mk-TArrow sy (rec dom) (rec rng))]
      [(? permissive?) t]
      [_ (error 'freeze "Bad type ~a" t)])))

;; Change free variables to ⊤
(define (free->x x t #:pred [pred (const #t)] #:∪ [∪ mk-TUnion])
  (let self ([t t])
    (match t
      [(? TFree?) (if (pred t)
                      x
                      t)]
      ;; boilerplate
      [(Tμ: sy x (Scope t) tr n) (mk-Tμ sy x (Scope (self t)) tr n)]
      [(TΛ: sy x (Scope t) on-app) (mk-TΛ sy x (Scope (self t)) on-app)]
      [(or (? T⊤?) (? TAddr?) (? TBound?) (? TName?) (? TFree?) (? TError?) (? TExternal?)) t]
      ;; Resimplify, since unification may have bumped some stuff up.
      [(TUnion: sy ts) (∪ sy (map self ts))]
      [(TCut: sy t u) (mk-TCut sy (self t) (self u))]
      ;; XXX: This must be mk-TVariant and not *TVariant in order to not conflate (foo X) with (bar X)
      [(TVariant: sy name ts tr) (mk-TVariant sy name (map self ts) tr)]
      [(TMap: sy t-dom t-rng ext) (mk-TMap sy (self t-dom) (self t-rng) ext)]
      [(TSet: sy t ext) (mk-TSet sy (self t) ext)]
      [(TWeak: sy t) (mk-TSet sy (self t))]
      [(THeap: sy taddr tag τ) (mk-THeap sy taddr tag (self τ))]
      [(TArrow: sy dom rng) (mk-TArrow sy (self dom) (self rng))]
      [_ (error 'free->x "Bad type ~a" t)])))

(define ff (cons #f #f))
(define vf (cons values #f))
;; Abstract inside-out. Give cosmetic names for better readability and equality checking.
(define (quantify-frees t names #:names [name-names #f] #:OAs [OAs #f] #:stxs [stxs #f] #:taddrs [taddrs #f])
  (let rec ([t t] [names names] [OAs OAs] [nnames (or name-names names)] [stxs stxs] [taddrs taddrs])
   (match names
     ['() t]
     [(cons name names*)
      (match-define (cons name-name name-names*) nnames)
      (match-define (cons stx0 stxs*) (or stxs ff))
      (match-define (cons taddr taddrs*) (or taddrs ff))
      (match-define (cons oa OAs*) (or OAs vf))
      (rec (mk-TΛ stx0 name-name (abstract-free t name taddr) oa)
           names* OAs* name-names* stxs* taddrs*)]
     [_ (error 'quantify-frees "Expected a list of names ~a" names)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Type operations (memoizes results in type-rep)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (support t)
  (or (Type-support t)
      (let ([t* (match t
                  [(or (TUnion: _ ts)  (TVariant: _ _ ts _)
                       (app (match-lambda [(or (TMap: _ d r _) (TCut: _ d r)) (list d r)] [_ '()]) ts)
                       (app (match-lambda [(TSet: _ s _) (list s)] [_ '()]) ts)
                       (app (match-lambda [(or (THeap: _ _ _ τ) (TWeak: _ τ)) (list τ)] [_ '()]) ts))
                   (for/union ([t (in-list ts)]) (support t))]
                  [(or (TFree: _ x) (TName: _ x)) (seteq x)]
                  [(or (Tμ: _ x (Scope t) _ _) (TΛ: _ x (Scope t) _))
                   (set-add (support t) x)]
                  [_ ∅eq])])
        (set-Type-support! t t*)
        t*)))

(define (free t)
  (or (Type-free t)
      (let ([t* (match t
                  [(or (TUnion: _ ts) (TVariant: _ _ ts _))
                   (for/unioneq ([t (in-list ts)]) (free t))]
                  [(or (TMap: _ d r _) (TCut: _ d r))
                   (set-union (free d) (free r))]
                  ;; TName and TExternal are bound by language
                  [(or (TFree: _ x)) (seteq x)]
                  [(or (Tμ: _ _ (Scope t) _ _)
                       (TΛ: _ _ (Scope t) _)
                       (TSet: _ t _)
                       (THeap: _ _ _ t)
                       (TWeak: _ t))
                   (free t)]
                  [_ ∅eq])])
        (set-Type-free! t t*)
        t*)))

;; Which space names are mentioned?
(define (names-mentioned t)
  (match t
    [(or (TUnion: _ ts) (TVariant: _ _ ts _))
     (for/unioneq ([t (in-list ts)]) (names-mentioned t))]
    [(or (TMap: _ d r _) (TCut: _ d r))
     (set-union (names-mentioned d) (names-mentioned r))]
    [(TName: _ x) (seteq x)]
    [(or (Tμ: _ _ (Scope t) _ _)
         (TΛ: _ _ (Scope t) _)
         (TSet: _ t _)
         (THeap: _ _ _ t)
         (TWeak: _ t))
     (names-mentioned t)]
    [_ ∅eq]))

(define (mono-type? t)
  (define (coind A t)
    (define m (Type-mono? t))
    (cond
     [(eq? m 'unset)
      (define res
        (cond
         [(set-member? A t) A]
         [else
          (define A* (set-add A t))
          (match t
            [(TUnion: _ ts)
             (andmap ((curry coind) A*) ts)]
            [(TMap: _ d r _)
             (and (coind A* d) (coind A* r))]
            [(TVariant: _ _ ts _)
             (let all ([A A*] [ts ts])
               (match ts
                 ['() A]
                 [(cons t ts)
                  (define A* (coind A t))
                  (and A* (all A* ts))]))]
            [(or (Tμ: _ _ (Scope t) _ _)  (TSet: _ t _))
             (coind A* t)]
            [(or (? TΛ?) (? TFree?)) #f]
            [(? needs-resolve?)
             (coind A* (resolve t))]
            [(or (THeap: _ _ _ τ) (TWeak: _ τ)) (coind A* τ)]
            [_ A*])]))
      (set-Type-mono?! t (not (not res)))
      res]
     [else (and m A)]))
  (coind ∅ t))

(define (type-contains? ty inner)
  (let search ([ty ty])
    (or (eq? ty inner)
        (match ty
          [(or (TΛ: _ _ (Scope t) _) (Tμ: _ _ (Scope t) _ _)) (search t)]
          ;; boilerplate
          [(or (? T⊤?) (? TAddr?) (? TBound?) (? TName?) (? TFree?)) #f]
          [(or (TUnion: _ ts) (TVariant: _ _ ts _)) (ormap search ts)]
          [(TCut: _ t u) (or (search t) (search u)
                           (search (resolve ty)))]
          [(TMap: _ t-dom t-rng _)
           (or (search t-dom) (search t-rng))]
          [(TSet: _ t _) (search t)]
          [_ (error 'type-contains? "Bad type ~a" ty)]))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Other type operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (needs-resolve? τ)
  (or (TName? τ) (Tμ? τ) (TCut? τ) (TUnif? τ)
      (and (THeap? τ) (needs-resolve? (THeap-τ τ)))))

(define limp-default-Λ-addr
  (mk-TAddr #f
            limp-default-addr-space
            limp-default-mm
            limp-default-em))
(define limp-default-deref-addr
  (mk-TAddr #f
            limp-default-addr-space
            'delay
            'identity))
(define limp-default-rec-addr limp-default-Λ-addr)
(define limp-default-⊤-addr limp-default-Λ-addr)

;; resolve : Type Map[Name,Type] -> Maybe[Type]
(define (resolve t #:addrize [rec-spaces (const #f)])
  (define Γ (Language-user-spaces (current-language)))
  (define Γcount (hash-count Γ))
  (define orig t)
  (let reset ([t t])
    (let fuel ([t t] [i (add1 Γcount)])
      (if (< 0 i)
          (match t
            [(TName: sy x)
             (match (rec-spaces x)
               [#f
                (match (hash-ref Γ x #f) ;; FIXME: paired names with types
                  [#f
                   (error 'resolve "Missing extra context for ~a [~a, ~a]" x
                          (struct->vector orig) Γ)]
                  [τ (fuel τ (sub1 i))])]
               [#t limp-default-Λ-addr]
               [bad (error 'resolve "Unexpected rec ~a" bad)])]
            [(Tμ: sy x st tr n)
             ;; INVARIANT: the only μs at this point are trusted.
             (when (untrusted? tr) (error 'resolve "Unfolds should be resolved first: ~a" t))
             (fuel (open-scope st t) (sub1 i))]
            [(TCut: _ t* u)
             (match (reset t*)
               [(and (TΛ: _ _ st on-app) lam)
                (define u* (reset u))
                ;; Record the type instantiations for later transformations.
                (define inst (instantiations))
                (when (and inst (not (permissive? u*)) (mono-type? u*))
                  (hash-add! inst lam u*))
                (define applied (open-scope st u))
                (reset (if (heapifying?) (on-app applied) applied))]
               [_ (error 'resolve "Expected a type abstraction at ~a: got ~a" t t*)])]
            [(TUnif _ τ) (reset τ)]
            [(THeap: sy taddr tag τ) (*THeap 'resolve sy taddr tag (reset τ))]
            [_ t])
          (error 'resolve "Circular reference: ~a" orig)))))
;(trace resolve)

(define-syntax seq
  (syntax-rules ()
    [(_ A last) last]
    [(_ A more0 . more)
     (let* ([A more0])
       (and A
            (seq A . more)))]))
 
;; If both are set, then they must be the same.
;; If not, we use the default
(define (mode-comb m0 m1)
  (if (implies (and m0 m1) (eq? m0 m1))
      (or m0 m1)
      'default))

;; Repeatedly instantiate σ's Λs with τs until τs is empty.
;; If τs not empty before σ is not a Λ, then invoke on-too-many.
(define (repeat-inst σ τs
                     [on-too-many
                      (λ _ #f)])
  (let loop ([σ σ] [τs τs])
    (match τs
      [(cons τ τs)
       (match (resolve σ)
         [(TΛ: _ x s oa)
          (loop (oa (open-scope s τ)) τs)]
         [_ (on-too-many)])]
      [_ σ])))

(define (num-top-level-Λs τ)
  (let count ([τ τ] [i 0])
   (match (resolve τ)
     [(TΛ: _ _ (Scope σ) _) (count σ (add1 i))]
     [_ i])))

;; Create unification variables for implicit types.
;; If over- or under-instantiated, return #f.
(define (apply-annotation τs τ)
  (define τs*
    (if (list? τs)
        (for/list ([τ (in-list τs)])
          (or τ (TUnif (gensym) T⊤)))
        (build-list (num-top-level-Λs τ) (λ _ (TUnif (gensym) T⊤)))))
  (define possible-out (repeat-inst τ τs*))
  (cond
   [(or (not possible-out) (TΛ? (resolve possible-out)))
    (values #f #f)] ;; should be fully instantiated
   [else
    (values (map freeze τs*) (freeze possible-out))]))

;; If we have (n τ ...) ≤ (n σ ...) and one unfolds more than the other, what do we do?
;; It's possible to introduce type errors because one unfolding won't be a subtype of the other.
;; Each non-identity subtype use must then have an implicit rewrite to fit into the target.
(define (produce-unfold-names Γ uspace-info) (error 'todo))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Type well-formedness operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; no-free? : Type -> Boolean
;; #t iff the type has no free variables
(define (no-free? t)
  (match t
    [(or (? T⊤?) (? TAddr?) (? TBound?) (? TExternal?) (? TName?) (? TError?)) #t]
    [(? TFree?) #f]
    [(or (Tμ: _ _ (Scope t) _ _) (TΛ: _ _ (Scope t) _) (TSet: _ t _))
     (no-free? t)]
    ;; boilerplate
    [(or (TUnion: _ ts)  (TVariant: _ _ ts _))
     (andmap no-free? ts)]
    [(or (TMap: _ t0 t1 _) (TCut: _ t0 t1))
     (and (no-free? t0) (no-free? t1))]
    [_ (error 'no-free? "Bad type: ~a" t)]))
