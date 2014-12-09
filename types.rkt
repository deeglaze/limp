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
               (and (TΛ: _ x st) (app (λ _ '#:Λ) head)))
           `(,head ,x ,(rec (open-scope-hygienically st x)))]
          [(TVariant: _ name ts tr)
           (define base `(ty$ ,name . ,(map rec ts)))
           (if (> v 0)
               (append base
                       (case tr
                         [(bounded) '(#:bounded)]
                         [(trusted) '(#:trust-construction)]
                         [else (if (> v 1)
                                   '(#:untrusted)
                                   '())]))
               base)]
          [(? T⊥?) '⊥]
          [(or (and (TSUnion: _ ts) (app (λ _ '#:∪) head))
               (and (TRUnion: _ ts) (app (λ _ '#:r∪) head)))
           `(,head . ,(map rec ts))]
          [(TMap: _ d r ext) `(↦ ,(rec d) ,(rec r) ,ext)]
          [(TSet: _ s ext) `(℘ ,(rec s) ,ext)]
          [(TCut: _ s u)
           `(#:inst ,(rec s) ,(rec u))]
          [(? T⊤?) '⊤]
          [(TAddr: _ name mm em) `(Addr ,name ,(and mm (s->k mm)) ,(and em (s->k em)))]
          [(TArrow: _ dom rng) `(#:-> ,(rec dom) ,(rec rng))]
          [(TBound: _ i) `(deb$ ,i)]
          ;; Non-types
          [(TUnif τ) `(Unif$ ,(rec τ))]
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
(define-type TSUnion (ts))
  (define T⊥ (TSUnion 1 ∅eq ∅eq 'concrete #t #f '()))
  (hash-set! intern-table '(T⊥) T⊥)
  (define (T⊥? x) (eq? T⊥ x))
(define-type TRUnion (ts))
(define-type TVariant (name ts trust)) ;; trust is a Trust-Tag
(define-type TExternal (name))
(define-type Tμ (x st tr n)) ;; name for printing
(define-type TΛ (x st))
(define-type TCut (t u))
(define-type TName (x)) ;; top level interaction and letrec-like binding
(define-type TMap (t-dom t-rng ext))
(define-type TSet (t ext))
;; the final boolean is if the type is meant to kill unions and force heap allocation.
(define-type TAddr (space mm em))
;; First order function
(define-type TArrow (dom rng))
;; Locally nameless stuff. References have their address target post-abstraction.
(struct Scope (t) #:transparent)
(define-type TFree (x))
(define-type TBound (i))
;; Marked to be heap-allocated when transformed.
(define-type THeap (taddr tag τ))
;; Unification variable
(struct TUnif ([τ #:mutable])
        #:methods gen:custom-write [(define write-proc write-type)])
;; Error placeholder
(struct TError (msgs) #:transparent
        #:methods gen:custom-write [(define write-proc write-type)])

(define generic-TAddr (mk-TAddr #f #f #f #f))

(define (*THeap who sy taddr tag τ)
  (when (THeap? τ) (error '*THeap "~a: bad construction ~a" who (list sy taddr tag τ)))
  (mk-THeap sy taddr tag τ))

;; Canonicalize ⊥s
(define (*TVariant sy name ts tr)
  (if (ormap T⊥? ts)
      T⊥
      (mk-TVariant sy name ts tr)))

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

;; If we substituted in a heap allocation under a heap allocation,
;; duplicate the type with different allocation tags if they are indeed different.
(define (combine-THeap sy taddr tag σ)
  (match σ
    [(THeap: _ taddr* tag* τ*)
     (type-join (*THeap 'combine0 sy tag taddr τ*)
                (*THeap 'combine1 sy tag taddr* τ*))]
    [τ* (*THeap 'combine0 sy taddr tag τ*)]))

(define (open-scope-aux t* i t)
  (let open ([t* t*] [i i])
    (define (open* t*) (open t* i))
    (match t*
      [(TBound: _ i*) (if (= i i*) t t*)]
      [(Tμ: sy x (Scope t) tr n) (mk-Tμ sy x (Scope (open t (add1 i))) tr n)]
      [(TΛ: sy x (Scope t)) (mk-TΛ sy x (Scope (open t (add1 i))))]
      ;; boilerplate
      [(or (? T⊤?) (? TAddr?) (? TFree?) (? TExternal?) (? TName?) (? TUnif?) (? TError?)) t*]
      [(TSUnion: sy ts) (mk-TSUnion sy (map open* ts))]
      [(TRUnion: sy ts) (mk-TRUnion sy (map open* ts))]
      [(TVariant: sy name ts tr) (mk-TVariant sy name (map open* ts) tr)]
      [(TCut: sy t u) (mk-TCut sy (open* t) (open* u))]
      [(TMap: sy t-dom t-rng ext) (mk-TMap sy (open* t-dom) (open* t-rng) ext)]
      [(TSet: sy t ext) (mk-TSet sy (open* t) ext)]
      [(THeap: sy taddr tag τ) (combine-THeap sy taddr tag (open* τ))]
      ;; second-class citizens
      [(TArrow: sy d r) (mk-TArrow sy (open* d) (open* r))]
      [(TUnif τ) (open* τ)]
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

(define ((name-conflict-res name on-conflict) f sy x t rec)
  (cond [(equal? x name)
         (when on-conflict (on-conflict))
         (f sy (fresh-name (set-add (support t) x) x) (rec t))]
        [else (f sy x (rec t))]))

;; for correct printing, sometimes clobbering old names
(define (open-scope-hygienically s name [on-conflict #f])
  (match-define (Scope t*) s)
  (define conflict-res (name-conflict-res name on-conflict))
  (let open ([t* t*] [i 0])
    (define (open* t*) (open t* i))
    (define (rec t) (Scope (open t (add1 i))))
    (match t*
      [(TBound: sy i*) (if (= i i*) (mk-TFree sy name) t*)]
      [(Tμ: sy x (Scope t) tr n) (conflict-res (λ (x s) (mk-Tμ x s tr n)) x t rec)]
      [(TΛ: sy x (Scope t)) (conflict-res mk-TΛ sy x t rec)]
      ;; boilerplate
      [(or (? T⊤?) (? TAddr?) (? TFree?) (? TExternal?) (? TName?)) t*]
      [(TSUnion: sy ts) (mk-TSUnion sy (map open* ts))]
      [(TRUnion: sy ts) (mk-TRUnion sy (map open* ts))]
      [(TVariant: sy name ts tr) (mk-TVariant sy name (map open* ts) tr)]
      [(TCut: sy t u) (mk-TCut sy (open* t) (open* u))]
      [(TMap: sy t-dom t-rng ext) (mk-TMap sy (open* t-dom) (open* t-rng) ext)]
      [(TSet: sy t ext) (mk-TSet sy (open* t) ext)]
      ;; second-class citizens
      [(TArrow: sy d r) (mk-TArrow sy (open* d) (open* r))]
      [(TUnif τ) (open* τ)]
      [(THeap: sy taddr tag τ) (*THeap 'open-scope-hygienically sy taddr tag (open* τ))]
      [_ (error 'open "Bad type ~a" t*)])))
 
(define (subst-name t name s)
  (define conflict-res (name-conflict-res name #f))
  (let subst ([t t])
    (match t
      [(TName: _ x)
       (if (equal? x name)
           s
           t)]
      [(Tμ: sy x (Scope t) tr n) (conflict-res (λ (x s) (mk-Tμ x s tr n)) sy t subst)]
      [(TΛ: sy x (Scope t)) (conflict-res mk-TΛ sy x t subst)]
      ;; boilerplate
      [(or (? T⊤?) (? TAddr?) (? TFree?) (? TExternal?) (? TBound?)) t]
      [(TSUnion: sy ts) (mk-TSUnion sy (map subst ts))]
      [(TRUnion: sy ts) (mk-TRUnion sy (map subst ts))]
      [(TVariant: sy name ts tr) (mk-TVariant sy name (map subst ts) tr)]
      [(TCut: sy t u) (mk-TCut sy (subst t) (subst u))]
      [(TMap: sy t-dom t-rng ext) (mk-TMap sy (subst t-dom) (subst t-rng) ext)]
      [(TSet: sy t ext) (mk-TSet sy (subst t) ext)]
      [(THeap: sy taddr tag τ) (combine-THeap sy taddr tag (subst τ))]
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
      [(TΛ: sy x (Scope t)) (mk-TΛ sy x (Scope (abs t (add1 i))))]
      ;; boilerplate
      [(or (? T⊤?) (? TAddr?) (? TBound?) (? TName?) (? TUnif?) (? TError?)) t]
      [(TSUnion: sy ts) (mk-TSUnion sy (map abs* ts))]
      [(TRUnion: sy ts) (mk-TRUnion sy (map abs* ts))]
      [(TCut: sy t u) (mk-TCut sy (abs* t) (abs* u))]
      [(TVariant: sy name ts tr) (mk-TVariant sy name (map abs* ts) tr)]
      [(TMap: sy t-dom t-rng ext) (mk-TMap sy (abs* t-dom) (abs* t-rng) ext)]
      [(TSet: sy t ext) (mk-TSet sy (abs* t) ext)]
      [(TArrow: sy d r) (mk-TArrow sy (abs* d) (abs* r))]
      [(THeap: sy taddr tag τ) (*THeap 'abstract-free sy taddr tag (abs* τ))]
      [_ (error 'abstract-free "Bad type ~a" t)])))

(define (abstract-free t name [taddr* #f])
  (Scope (abstract-free-aux t 0 name taddr*)))

;; Remove mutable unification variables.
(define (freeze t)
  (match t
    [(TUnif τ) (freeze τ)]
    ;; boilerplate
    [(Tμ: sy x (Scope t) tr n) (mk-Tμ sy x (Scope (freeze t)) tr n)]
    [(TΛ: sy x (Scope t)) (mk-TΛ sy x (Scope (freeze t)))]
    [(or (? T⊤?) (? TAddr?) (? TBound?) (? TName?) (? TFree?) (? TError?) (? TExternal?)) t]
    ;; Resimplify, since unification may have bumped some stuff up.
    [(TSUnion: sy ts) (*TSUnion sy (map freeze ts))]
    [(TRUnion: sy ts) (*TRUnion sy (map freeze ts))]
    [(TCut: sy t u) (mk-TCut sy (freeze t) (freeze u))]
    [(TVariant: sy name ts tr) (*TVariant sy name (map freeze ts) tr)]
    [(TMap: sy t-dom t-rng ext) (mk-TMap sy (freeze t-dom) (freeze t-rng) ext)]
    [(TSet: sy t ext) (mk-TSet sy (freeze t) ext)]
    [(THeap: sy taddr tag τ) (*THeap 'freeze sy taddr tag (freeze τ))]
    [(TArrow: sy dom rng) (mk-TArrow sy (freeze dom) (freeze rng))]
    [_ (error 'freeze "Bad type ~a" t)]))

;; Remove heapification annotations
(define (unannotate t)
  (match t
    [(THeap: _ _ _ τ) (unannotate τ)]
    ;; boilerplate
    [(Tμ: sy x (Scope t) tr n) (mk-Tμ sy x (Scope (unannotate t)) tr n)]
    [(TΛ: sy x (Scope t)) (mk-TΛ sy x (Scope (unannotate t)))]
    [(or (? T⊤?) (? TAddr?) (? TBound?) (? TName?) (? TFree?) (? TError?) (? TExternal?)) t]
    ;; Resimplify, since unification may have bumped some stuff up.
    [(TSUnion: sy ts) (*TSUnion sy (map unannotate ts))]
    [(TRUnion: sy ts) (*TRUnion sy (map unannotate ts))]
    [(TCut: sy t u) (mk-TCut sy (unannotate t) (unannotate u))]
    [(TVariant: sy name ts tr) (*TVariant sy name (map unannotate ts) tr)]
    [(TMap: sy t-dom t-rng ext) (mk-TMap sy (unannotate t-dom) (unannotate t-rng) ext)]
    [(TSet: sy t ext) (mk-TSet sy (unannotate t) ext)]
    [(TArrow: sy dom rng) (mk-TArrow sy (unannotate dom) (unannotate rng))]
    [_ (error 'unannotate "Bad type ~a" t)]))

;; Change free variables to ⊤
(define (free->x x t)
  (let self ([t t])
    (match t
      [(? TFree?) x]
      ;; boilerplate
      [(Tμ: sy x (Scope t) tr n) (mk-Tμ sy x (Scope (self t)) tr n)]
      [(TΛ: sy x (Scope t)) (mk-TΛ sy x (Scope (self t)))]
      [(or (? T⊤?) (? TAddr?) (? TBound?) (? TName?) (? TFree?) (? TError?) (? TExternal?)) t]
      ;; Resimplify, since unification may have bumped some stuff up.
      [(TSUnion: sy ts) (*TSUnion sy (map self ts))]
      [(TRUnion: sy ts) (*TRUnion sy (map self ts))]
      [(TCut: sy t u) (mk-TCut sy (self t) (self u))]
      [(TVariant: sy name ts tr) (*TVariant sy name (map self ts) tr)]
      [(TMap: sy t-dom t-rng ext) (mk-TMap sy (self t-dom) (self t-rng) ext)]
      [(TSet: sy t ext) (mk-TSet sy (self t) ext)]
      [(THeap: sy taddr tag τ) (mk-THeap sy taddr tag (self τ))]
      [(TArrow: sy dom rng) (mk-TArrow sy (self dom) (self rng))]
      [_ (error 'free->x "Bad type ~a" t)])))

(define ff (cons #f #f))
;; Abstract inside-out. Give cosmetic names for better readability and equality checking.
(define (quantify-frees t names #:names [name-names #f] #:stxs [stxs #f] #:taddrs [taddrs #f])
  (let rec ([t t] [names names] [nnames (or name-names names)] [stxs stxs] [taddrs taddrs])
   (match names
     ['() t]
     [(cons name names*)
      (match-define (cons name-name name-names*) nnames)
      (match-define (cons stx0 stxs*) (or stxs ff))
      (match-define (cons taddr taddrs*) (or taddrs ff))
      (rec (mk-TΛ stx0 name-name (abstract-free t name taddr)) names* name-names* stxs* taddrs*)]
     [_ (error 'quantify-frees "Expected a list of names ~a" names)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Type operations (memoizes results in type-rep)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (support t)
  (or (Type-support t)
      (let ([t* (match t
                  [(or (TSUnion: _ ts) (TRUnion: _ ts) (TVariant: _ _ ts _)
                       (app (match-lambda [(or (TMap: _ d r _) (TCut: _ d r)) (list d r)] [_ '()]) ts)
                       (app (match-lambda [(TSet: _ s _) (list s)] [_ '()]) ts)
                       (app (match-lambda [(THeap: _ _ _ τ) (list τ)] [_ '()]) ts))
                   (for/union ([t (in-list ts)]) (support t))]
                  [(or (TFree: _ x) (TName: _ x)) (seteq x)]
                  [(or (Tμ: _ x (Scope t) _ _) (TΛ: _ x (Scope t)))
                   (set-add (support t) x)]
                  [_ ∅eq])])
        (set-Type-support! t t*)
        t*)))

(define (free t)
  (or (Type-free t)
      (let ([t* (match t
                  [(or (TSUnion: _ ts) (TRUnion: _ ts) (TVariant: _ _ ts _))
                   (for/unioneq ([t (in-list ts)]) (free t))]
                  [(or (TMap: _ d r _) (TCut: _ d r))
                   (set-union (free d) (free r))]
                  ;; TName and TExternal are bound by language
                  [(or (TFree: _ x)) (seteq x)]
                  [(or (Tμ: _ _ (Scope t) _ _)
                       (TΛ: _ _ (Scope t))
                       (TSet: _ t _)
                       (THeap: _ _ _ t))
                   (free t)]
                  [_ ∅eq])])
        (set-Type-free! t t*)
        t*)))

;; Which space names are mentioned?
(define (names t)
  (match t
    [(or (TSUnion: _ ts) (TRUnion: _ ts) (TVariant: _ _ ts _))
     (for/unioneq ([t (in-list ts)]) (names t))]
    [(or (TMap: _ d r _) (TCut: _ d r))
     (set-union (names d) (names r))]
    [(TName: _ x) (seteq x)]
    [(or (Tμ: _ _ (Scope t) _ _)
         (TΛ: _ _ (Scope t))
         (TSet: _ t _)
         (THeap: _ _ _ t))
     (names t)]
    [_ ∅eq]))

(define (mono-type? t)
  (define m (Type-mono? t))
  (cond
   [(eq? m 'unset)
    (define b
      (let coind ([A ∅eq] [t t])
        (define m (Type-mono? t))
        (cond
         [(eq? m 'unset)
          (match t
            [(or (TSUnion: _ ts) (TRUnion: _ ts))
             (andmap ((curry coind) A) ts)]
            [(TMap: _ d r _)
             (and (coind A d) (coind A r))]
            [(TVariant: _ _ ts _)
             (let all ([A A] [ts ts])
               (match ts
                 ['() A]
                 [(cons t ts)
                  (define A* (coind A t))
                  (and A* (all A* ts))]))]
            [(or (Tμ: _ _ (Scope t) _ _)  (TSet: _ t _))
             (coind A t)]
            [(or (? TΛ?) (? TFree?)) #f]
            [(? needs-resolve?)
             (if (set-member? A t) ;; already looked up name and haven't failed yet.
                 A
                 (coind (set-add A t) (resolve t)))]
            [(THeap: _ _ _ τ) (coind A τ)]
            [_ A])]
         [else (and m A)])))
    (set-Type-mono?! t b)
    b]
   [else m]))

(define (type-contains? ty inner)
  (let search ([ty ty])
    (or (eq? ty inner)
        (match ty
          [(or (TΛ: _ _ (Scope t)) (Tμ: _ _ (Scope t) _ _)) (search t)]
          ;; boilerplate
          [(or (? T⊤?) (? TAddr?) (? TBound?) (? TName?) (? TFree?)) #f]
          [(or (TSUnion: _ ts) (TRUnion: _ ts) (TVariant: _ _ ts _)) (ormap search ts)]
          [(TCut: _ t u) (or (search t) (search u)
                           (search (resolve ty)))]
          [(TMap: _ t-dom t-rng _)
           (or (search t-dom) (search t-rng))]
          [(TSet: _ t _) (search t)]
          [_ (error 'type-contains? "Bad type ~a" ty)]))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Other type operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (flatten-unions-in-list ts)
  (append-map
   (λ (t)
      (match t
        [(or (TRUnion: _ ts*) (TSUnion: _ ts*))
         (flatten-unions-in-list ts*)]
        [_ (list t)]))
   ts))

;; Only incomparable types should be represented in a union.
;; When a type subsumes another, we remove the subsumed type.
(define (remove-subtypes ts)
  (let rec ([ts ts] [rev-ts* '()])
   (match ts
     ['() rev-ts*]
     [(cons t ts)
      ;; If t is subtyped in the rest of the list, drop it.
      ;; If t was supertyped by a previous type, drop it.
      (cond [(or (for/or ([s (in-list ts)]) (<:? t s))
                 (for/or ([s (in-list rev-ts*)]) (<:? t s)))
             (rec ts rev-ts*)]
            [else (rec ts (cons t rev-ts*))])])))

;; Canonicalize a list of types to forbid disequal but equivalent types.
(define (simplify-types U ts)
  (match (remove-subtypes
          (remove-sorted-dups
           (sort (flatten-unions-in-list ts) < #:key Type-key)))
    [(list t) t]
    ['() T⊥]
    [ts (U ts)]))

;; reverses, but it's still canonically sorted.
(define (remove-sorted-dups ts) ;; assumes #f not the first element of list.
  (let loop ([ts ts] [last #f] [new '()])
    (match ts
      ['() new]
      [(cons t ts)
       (if (equal? t last)
           (loop ts last new)
           (loop ts t (cons t new)))]
      [_ (error 'loop "Expected a list of types ~a" ts)])))
(define (*TSUnion sy ts) 
  (unless (list? ts) (error '*TSUnion "WAT"))
  (simplify-types ((curry mk-TSUnion) sy) ts))
(define (*TRUnion sy ts)
  (unless (list? ts) (error '*TRUnion "WAT"))
  (simplify-types ((curry mk-TRUnion) sy) ts))

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
(define (resolve t [extra-Γ #f] #:addrize [rec-spaces (const #f)])
  (define Γ (Language-user-spaces (current-language)))
  (define Γcount (+ (hash-count Γ) (if extra-Γ (hash-count extra-Γ) 0)))
  (define orig t)
  (let reset ([t t])
    (let fuel ([t t] [i (add1 Γcount)])
      (if (< 0 i)
          (match t
            [(TName: sy x)
             (match (rec-spaces x)
               [#f
                (match (hash-ref Γ x #f)
                  [#f
                   (unless extra-Γ
                     (error 'resolve "Missing extra context for ~a" x))
                   (mk-TName sy (hash-ref extra-Γ x))]
                  [τ (fuel τ (sub1 i))])]
               [#t limp-default-Λ-addr]
               [bad (error 'resolve "Unexpected rec ~a" bad)])]
            [(Tμ: sy x st tr n)
             ;; INVARIANT: the only μs at this point are trusted.
             (when (untrusted? tr) (error 'resolve "Unfolds should be resolved first: ~a" t))
             (fuel (open-scope st t) (sub1 i))]
            [(TCut: _ t* u)
             (match (reset t*)
               [(and (TΛ: _ _ st) lam)
                ;; Record the type instantiations for later transformations.
                (define u* (reset u))
                (define inst (instantiations))
                (when (and inst (mono-type? u*)) (hash-add! inst lam u*))
                (reset (open-scope st u))]
               [_ (error 'resolve "Expected a type abstraction at ~a: got ~a" t t*)])]
            [(TUnif τ) (reset τ)]
            [(THeap: sy taddr tag τ) (*THeap 'resolve sy taddr tag (reset τ))]
            [_ t])
          (error 'resolve "Circular reference: ~a" orig)))))

(define-syntax seq
  (syntax-rules ()
    [(_ A last) last]
    [(_ A more0 . more)
     (let* ([A more0])
       (and A
            (seq A . more)))]))

;; The TAPL approach to equirecursive subtyping.
;; Uses language axioms for external subtyping.
(define (<:? τ σ [ρ #f])
  (define L (current-language))
  ((<:?-aux (Language-E<: L) ρ) ∅ τ σ))
(define ((<:?-aux E<: ρ) A τ σ)
  (define (<:?-aux A τ σ)
    (define (grow-A) (set-add A (cons τ σ)))
    (cond
     [(or (equal? τ σ)
          (set-member? A (cons τ σ))
          (TError? τ)
          (TError? σ)) A]
     [else
      (match* (τ σ)
        [(_ (? T⊤?)) A]
        [((? T⊥?) _) A]
        [((TVariant: _ n τs tr0) (TVariant: _ n σs tr1))
         #:when (implies (and tr0 tr1) (equal? tr0 tr1))
         (let each ([A (grow-A)] [τs τs] [σs σs])
           (match* (τs σs)
             [('() '()) A]
             [((cons τ τs) (cons σ σs))
              (seq A (<:?-aux A τ σ) (each A τs σs))]
             [(_ _) #f]))]
        [((TSet: _ τ lext) (TSet: _ σ rext))
         (and
          (or (equal? lext rext)
              (eq? lext 'dc)
              (eq? rext 'dc))
          (<:?-aux A τ σ))]
        [((TMap: _ τk τv lext) (TMap: _ σk σv rext))
         (and (or (equal? lext rext)
                  (eq? lext 'dc)
                  (eq? rext 'dc))
          (seq A
               (<:?-aux A τk σk)
               (<:?-aux A τv σv)))]
        [((TΛ: _ _ sτ) (TΛ: _ _ sσ))
         (define name (mk-TFree #f (gensym 'dummy)))
         (<:?-aux A (open-scope sτ name) (open-scope sσ name))]
        [(_ (TExternal: _ name)) (and (set-member? E<: (cons τ name)) A)]
        [((? needs-resolve?) _)
         (<:?-aux (grow-A) (resolve τ ρ) σ)]
        [(_ (? needs-resolve?))
         (<:?-aux (grow-A) τ (resolve σ ρ))]
        [((THeap: _ taddr0 tag0 τ) (THeap: _ taddr1 tag1 σ))
         (and (not (unmapped? (⋈flat tag0 tag1)))
              (seq A
                   (<:?-aux A taddr0 taddr1)
                   (<:?-aux A τ σ)))]
        ;; No implicit casts from heap/non-heap
        [((or (TRUnion: _ ts) (TSUnion: _ ts)) _)
         (and (for/and ([t (in-list ts)])
                (<:?-aux A t σ))
              A)]
        [(_ (or (TRUnion: _ σs) (TSUnion: _ σs)))
         (and (for/or ([σ (in-list σs)])
                (<:?-aux A τ σ))
              A)]
        [((TAddr: _ space0 mm0 em0) (TAddr: _ space1 mm1 em1))
         (and (not (or (unmapped? (⋈flat space0 space1))
                       (unmapped? (⋈flat mm0 mm1))
                       (unmapped? (⋈flat em0 em1))))
              A)]
        [(_ _) #f])]))
  (<:?-aux A τ σ))

;; If both are set, then they must be the same.
;; If not, we use the default
(define (mode-comb m0 m1)
  (if (implies (and m0 m1) (eq? m0 m1))
      (or m0 m1)
      'default))

(define (type-join-aux us)
  (define (⊔ τ σ ρ)
    (define (join-named x σ)
      (match (hash-ref ρ x #f)
        [#f (define x* (gensym x))
            (hash-set! us x* T⊥)
            (define τσ (⊔ (hash-ref us x) σ (hash-set ρ x x*)))
            (hash-set! us x* τσ)
            τσ]
        [y (⊔ (mk-TName #f y) σ ρ)]))
    (define (unify τ σ)
      (cond
       [(type-contains? σ τ)
        (TError (list "Cyclic unification"))]
       [else
        (define out (⊔ (TUnif-τ τ) σ ρ))
        (set-TUnif-τ! τ out)
        τ]))
    (cond
     [(and (TError? τ) (TError? σ))
      (TError (append (TError-msgs τ) (TError-msgs σ)))]
     ;; If comparable, choose the larger type without allocating new type structure.
     [(<:? τ σ ρ) σ]
     [(<:? σ τ ρ) τ]
     [else
      (match* (τ σ)
        [((TVariant: _ n τs tr0) (TVariant: _ n σs tr1))
         #:when (and (= (length τs) (length σs))
                     (implies (and tr0 tr1) (equal? tr0 tr1)))
         (mk-TVariant #f n (for/list ([τ (in-list τs)]
                                      [σ (in-list σs)])
                             (⊔ τ σ ρ))
                      (⊔trust tr1 tr0))]
        ;; Make Λs agree on a name and abstract the result.
        [((TΛ: _ x st) (TΛ: _ _ ss))
         (define fresh (gensym 'joinΛ))
         (define tv (mk-TFree #f fresh))
         (mk-TΛ #f x
                (abstract-free (⊔ (open-scope st tv)
                                  (open-scope ss tv)
                                  ρ)
                               fresh))]
        ;; If not an abstraction, unify.
        [((TΛ: _ x st) _) (⊔ (open-scope st (TUnif T⊥)) σ ρ)]
        [(_ (TΛ: _ x ss)) (⊔ τ (open-scope ss (TUnif T⊥)) ρ)]
        [((? TUnif?) _) (unify τ σ)]
        [(_ (? TUnif?)) (unify σ τ)]
        ;; distribute unions
        [((or (TRUnion: _ ts) (TSUnion: _ ts)) _)
         (*TRUnion #f (for/list ([t (in-list ts)])
                        (⊔ t σ ρ)))]
        [(_ (or (TRUnion: _ ts) (TSUnion: _ ts)))
         (*TRUnion #f (for/list ([t (in-list ts)])
                        (⊔ τ t ρ)))]
        ;; map and set are structural
        [((TMap: _ fd fr fext) (TMap: _ td tr text))
         (mk-TMap #f
                  (⊔ fd td ρ)
                  (⊔ fr tr ρ)
                  (⊔b fext text))]
        [((TSet: _ t fext) (TSet: _ s text))
         (mk-TSet (⊔ t s ρ) (⊔b fext text))]
        ;; The join of two recursive types requires them agreeing on their variable.
        [((Tμ: _ x sτ ftr fn) (Tμ: _ _ sσ ttr tn))
         (define fresh (gensym 'joinμ))
         (define tv (mk-TFree #f fresh))
         (mk-Tμ #f x
                (abstract-free (⊔ (open-scope sτ tv) (open-scope sσ tv) ρ) fresh)
                (⊔trust ftr ttr)
                (min fn tn))]
        ;; Named types are like recursive types, but trickier to get the name agreement right.
        [((TName: _ x) _) (join-named x σ)]
        [(_ (TName: _ x)) (join-named x τ)]
        [((? TCut?) _) (⊔ (resolve τ ρ) σ ρ)]
        [(_ (? TCut?)) (⊔ τ (resolve σ ρ) ρ)]
        ;; Maintain invariant that heap allocation annotations are only one deep.
        [((THeap: _ taddr0 tag0 τ) (THeap: _ taddr1 tag1 σ))
         (define (both)
           (mk-TRUnion #f (list (*THeap 'join-theap0 #f taddr0 tag0 τ)
                                (*THeap 'join-theap1 #f taddr1 tag1 σ))))
         (match (⊔ taddr0 taddr1 ρ)
           [(? TRUnion?) (both)]
           [(? TAddr? ta)
            (define tag (⋈flat tag0 tag1))
            (if (unmapped? tag)
                (both)
                (*THeap 'join-theap #f ta tag (⊔ τ σ ρ)))]
           [bad (error 'type-join "Non-TAddr join? ~a ~a => ~a" taddr0 taddr1 bad)])]
        [((TAddr: _ space0 mm0 em0) (TAddr: _ space1 mm1 em1))
         (define space (⋈flat space0 space1))
         (define mm (⋈flat mm0 mm1))
         (define em (⋈flat em0 em1))
         (if (or (unmapped? space) (unmapped? mm) (unmapped? em))
             (*TRUnion #f (list τ σ))
             (mk-TAddr #f space mm em))]
        [(_ _) (*TRUnion #f (list τ σ))])]))
  ⊔)
(define (type-join τ σ)  
  (freeze ((type-join-aux (Language-user-spaces (current-language))) τ σ #hasheq())))

(define (type-join* τs [ρ #hasheq()] #:no-freeze? [no-freeze? #f])
  (define tj (type-join-aux (Language-user-spaces (current-language))))
  (define (rec τs acc)
    (match τs
      ['() (if no-freeze? acc (freeze acc))]
      [(cons τ τs*) (rec τs* (tj τ acc ρ))]))
  (rec τs T⊥))

;; Doesn't freeze afterwards
(define (type-meet-aux us)
  (define (⊓ τ σ ρ)
    (define (meet-named x σ)
      (match (hash-ref ρ x #f)
        [#f (define x* (gensym x))
            (hash-set! us x* T⊥)
            (define τσ (⊓ (hash-ref us x) σ (hash-set ρ x x*)))
            (hash-set! us x* τσ)
            τσ]
        [y
         (⊓ (mk-TName #f y) σ ρ)]))
    (define (unify τ σ)
      (define out (⊓ (TUnif-τ τ) σ ρ))
      (set-TUnif-τ! τ out)
      τ)
   (cond
    [(and (TError? τ) (TError? σ))
     (TError (append (TError-msgs τ) (TError-msgs σ)))]
    [(<:? τ σ ρ) τ]
    [(<:? σ τ ρ) σ]
    [else
     (match* (τ σ)
       [((TVariant: _ n τs tr0) (TVariant: _ n σs tr1))
        #:when (and (= (length τs) (length σs))
                    (let ([r  (implies (and tr0 tr1) (equal? tr0 tr1))])
                      (printf "Trust ~a ~a ~a~%" tr0 tr1 r)
                      r))
        (*TVariant #f n (for/list ([τ (in-list τs)]
                                   [σ (in-list σs)])
                            (⊓ τ σ ρ))
                     (⊓trust tr1 tr0))]
       ;; Make Λs agree on a name and abstract the result.
       [((TΛ: _ x st) (TΛ: _ _ ss))
        (define fresh (gensym 'joinΛ))
        (define tv (mk-TFree #f fresh))
        (mk-TΛ #f x
               (abstract-free (⊓ (open-scope st tv)
                                 (open-scope ss tv)
                                 ρ)
                              fresh))]
       ;; If not both abstractions, start at ⊤ and narrow.
       [((TΛ: _ _ st) _) (⊓ (open-scope st (TUnif T⊤)) σ ρ)]
       [(_ (TΛ: _ _ ss)) (⊓ τ (open-scope ss (TUnif T⊤)) ρ)]
       [((? TUnif?) _) (unify τ σ)]
       [(_ (? TUnif?)) (unify σ τ)]
       ;; distribute unions
       [((or (TRUnion: _ ts) (TSUnion: _ ts)) _)
        (type-join* (for/list ([t (in-list ts)])
                       (⊓ t σ ρ))
                    ρ #:no-freeze? #t)]
       [(_ (or (TRUnion: _ ts) (TSUnion: _ ts)))
        (type-join* (for/list ([t (in-list ts)])
                      (⊓ τ t ρ))
                    ρ #:no-freeze? #t)]
       ;; map and set are structural
       [((TMap: _ fd fr fext) (TMap: _ td tr text))
        (mk-TMap #f (⊓ fd td ρ)
                 (⊓ fr tr ρ)
                 (⊓b fext text))]
       [((TSet: _ t fext) (TSet: _ s text))
        (mk-TSet #f (⊓ t s ρ) (⊓b fext text))]
       ;; The join of two recursive types requires them agreeing on their variable.
       [((Tμ: _ x sτ ftr fn) (Tμ: _ _ sσ ttr tn))
        (define fresh (gensym 'joinμ))
        (define tv (mk-TFree #f fresh))
        (mk-Tμ #f x
               (abstract-free
                (⊓
                 (open-scope sτ tv)
                 (open-scope sσ tv)
                 ρ)
                fresh)
               (⊓trust ftr ttr)
               (min fn tn))]
       ;; Named types are like recursive types, but trickier to get the name agreement right.
       [((TName: _ x) _) (meet-named x σ)]
       [(_ (TName: _ x)) (meet-named x τ)]
       [((? TCut?) _) (⊓ (resolve τ ρ) σ ρ)]
       [(_ (? TCut?)) (⊓ τ (resolve σ ρ) ρ)]
       [((THeap: _ taddr0 tag0 τ) (THeap: _ taddr1 tag1 σ))
         (match (⊓ taddr0 taddr1 ρ)
           [(? TAddr? ta)
            (define inner (⊓ τ σ ρ))
            (define tag (⋈flat tag0 tag1))
            (if (or (T⊥? inner) (unmapped? tag))
                T⊥ ;; XXX: don't heap-allocate bottom?
                (*THeap 'meet-theap #f ta tag inner))]
           [(? T⊥?) T⊥]
           [bad (error 'type-meet "Non-TAddr meet? ~a ~a => ~a" taddr0 taddr1 bad)])]
       [((TAddr: _ space0 mm0 em0) (TAddr: _ space1 mm1 em1))
         (define space (⋈flat space0 space1))
         (define mm (⋈flat mm0 mm1))
         (define em (⋈flat em0 em1))
         (if (or (unmapped? space) (unmapped? mm) (unmapped? em))
             T⊥
             (mk-TAddr #f space mm em))]
       [(_ _)
        (unless (and τ σ) (error 'type-meet "Bad type ~a ~a" τ σ))
        T⊥])]))
  ⊓)

(define (type-meet τ σ)
  (define res (freeze ((type-meet-aux (Language-user-spaces (current-language))) τ σ #hasheq())))
  (when (T⊥? res)
    (printf "Meet ⊥: ~a, ~a~%" τ σ))
  res)

(define (type-meet* τs [ρ #hasheq()] #:no-freeze? [no-freeze? #f])
  (define tm (type-meet-aux (Language-user-spaces (current-language))))
  (let rec ([τs τs] [acc T⊤])
   (match τs
     ['() (if no-freeze? acc (freeze acc))]
     [(cons τ τs)
      (rec τs (tm τ acc ρ))])))

;; τ is castable to σ if τ <: σ, τ = ⊤,
;; or structural components of τ are castable to structural components of σ.
(define (castable from to)
  (define (check A from to)
    (if (or
         (<:? from to) ;; upcast
         (<:? to from)) ;; strict downcast
        A
        ;; Structurally castable?
        (match* (from to)
          [((TΛ: _ _ (Scope f)) (TΛ: _ _ (Scope t)))
           (check A f t)]
          [((TVariant: _ n tsf tr0) (TVariant: _ n tst tr1))
           #:when (implies (and tr0 tr1) (equal? tr0 tr1))
           (let all ([A A] [tsf tsf] [tst tst])
             (match* (tsf tst)
               [('() '()) A]
               [((cons f tsf) (cons t tst))
                (seq A (check A f t) (all A tsf tst))]
               [(_ _) #f]))]
          [((Tμ: _ _ (Scope f) tr n) (Tμ: _ _ (Scope t) tr n))
           (check A f t)]
          [((TMap: _ df rf ext) (TMap: _ dt rt ext))
           (seq (check A df dt)
                (check A rf rt))]
          [((TSet: _ f ext) (TSet: _ t ext)) (check A f t)]
          [((TSUnion: _ tsf) _)
           (for/fold ([A A]) ([tf (in-list tsf)]
                              #:when A)
             (check A tf to))]
          [(_ (TSUnion: _ tst))
           ;; Don't save false paths
           (for/or ([tt (in-list tst)]) (check A from tt))]
          ;; XXX: Will this possibly diverge?
          [((and (not (? Tμ?)) (? needs-resolve?)) _)
           (if (set-member? A (cons from to))
               A
               (check (set-add A (cons from to))
                      (resolve from) to))]
          [(_ (and (not (? Tμ?)) (? needs-resolve?)))
           (if (set-member? A (cons from to))
               A
               (check (set-add A (cons from to))
                      from (resolve to)))]
          [(_ _) #f])))
  (and (check ∅ from to) #t))

(define (cast-to from to)
  (cond
   [(<:? from to) (Check to)] ;; upcast -> check, not cast
   [(castable from to) (Cast to)]
   [else (type-error "Could not cast ~a to ~a" from to)]))

;; Find all instances of variants named n with given arity, and return
;; their type, additionally quantified by all the containing Λs.
(define (lang-variants-of-arity upper-bound)
  (define us (Language-ordered-us (current-language)))
  (define seen (mutable-seteq))
  (define more-upper (free->x T⊤ upper-bound))
  (reverse
   (for/fold ([found '()])
       ([nu (in-list us)])
     (define τ (cdr nu))
     (define (collect τ TVs Name-TVs found)
       (define (collect* τs found)
         (match τs
           ['() found]
           [(cons τ τs)
            (define found* (collect τ TVs Name-TVs found))
            (collect* τs found*)]
           [_ (error 'collect* "Expected a list of types: ~a" τs)]))
       (cond
        [(set-member? seen τ) found]
        [else
         (set-add! seen τ)
         (match τ
           [(TVariant: _ n* ts tr)
            (define found*
              (if (<:? (free->x T⊥ τ) more-upper) 
                  (cons (quantify-frees τ TVs #:names Name-TVs) found)
                  found))
            (collect* ts found*)]
           [(TΛ: _ x s)
            (define x* (gensym x))
            (define TVs* (cons x* TVs))
            (collect (open-scope s (mk-TFree #f x*)) TVs* (cons x Name-TVs) found)]
           [(TName: _ x)
            found]
           [(Tμ: _ x s tr n)
            (collect (open-scope s (mk-TFree #f (gensym x))) TVs Name-TVs found)]
           [(? needs-resolve?) (collect (resolve τ) TVs Name-TVs found)]
           [(TMap: _ d r _)
            (collect r TVs Name-TVs (collect d TVs Name-TVs found))]
           [(or (TSet: _ v _) (THeap: _ _ _ v)) (collect v TVs Name-TVs found)]
           [(or (TRUnion: _ ts) (TSUnion: _ ts)) (collect* ts found)]
           [_ found])]))
     (reverse (collect τ '() '() found)))))

;; Repeatedly instantiate σ's Λs with τs until τs is empty.
;; If τs not empty before σ is not a Λ, then invoke on-too-many.
(define (repeat-inst σ τs
                     [on-too-many
                      (λ _ #f)])
  (let loop ([σ σ] [τs τs])
    (match τs
      [(cons τ τs)
       (match (resolve σ)
         [(TΛ: _ x s)
          (loop (open-scope s τ) τs)]
         [_ (on-too-many)])]
      [_ σ])))

(define (num-top-level-Λs τ)
  (let count ([τ τ] [i 0])
   (match (resolve τ)
     [(TΛ: _ _ (Scope σ)) (count σ (add1 i))]
     [_ i])))

;; Create unification variables for implicit types.
;; If over- or under-instantiated, return #f.
(define (apply-annotation τs τ)
  (define τs*
    (if (list? τs)
        (for/list ([τ (in-list τs)])
          (or τ (TUnif T⊤)))
        (build-list (num-top-level-Λs τ) (λ _ (TUnif T⊤)))))
  (define possible-out (repeat-inst τ τs*))
  (and (not (TΛ? (resolve possible-out))) ;; should be fully instantiated
       (freeze possible-out)))

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
    [(or (Tμ: _ _ (Scope t) _ _) (TΛ: _ _ (Scope t)) (TSet: _ t _))
     (no-free? t)]
    ;; boilerplate
    [(or (TSUnion: _ ts) (TRUnion: _ ts) (TVariant: _ _ ts _))
     (andmap no-free? ts)]
    [(or (TMap: _ t0 t1 _) (TCut: _ t0 t1))
     (and (no-free? t0) (no-free? t1))]
    [_ (error 'no-free? "Bad type: ~a" t)]))

;; check-path-productive : Type Type (any -> ⊥) -> (void)
;; (void) iff endpoint unreachable from t. Otherwise break invoked with #f.
(define (check-path-productive t endpoint break)
  (let search ([t t])
    (when (eq? t endpoint) (break #f))
    (match t
      [(or (TΛ: _ _ (Scope t)) (Tμ: _ _ (Scope t) _ _)) (search t)]
      [(or (TSUnion: _ ts) (TRUnion: _ ts)) (for-each search ts)]
      [_ (void)])))

;; vaguely-shaped? : Listof[Type] -> Boolean
;; #f iff all types are not vaguely shaped.
;; Shape vagueries are
;; - free names
;; - same name/arity variants
;; - more than one map or set
(define (vaguely-shaped? ts)
  (define name-arities (mutable-set))
  (let/ec break
   (for/fold ([map? #f] [set? #f])
       ([t (in-list ts)])
     (match t
       [(? TMap?)
        (when map? (break #t))
        (values #t set?)]
       [(? TSet?)
        (when set? (break #t))
        (values map? #t)]
       [(? TFree?) (break #t)]
       [(TVariant: _ name ts _)
        (define n-arity (cons name (length ts)))
        (cond
         [(set-member? name-arities n-arity) (break #t)]
         [else (set-add! name-arities n-arity)
               (values map? set?)])]
       [_ (values map? set?)]))
   #f))

;; Unroll all types and mark where the unrolling was

;; check-productive-and-classify-unions : Type Boolean -> (U #f Type)
;; Simplifies unions and classifies them as raw or shapely.
;; If ar? is #f, then the result is #f if any raw unions are detected.
;; If the type has an unguarded recursive type variable, then the result is #f.
(define (check-productive-and-classify-unions t ar?)
  (let/ec break
    (let loop ([t t] [unrolled ∅eq])
      (define (loop* t) (loop t unrolled))
      (match t
        [(TΛ: sy x st) ;; XXX: TFree taddr should be #f or...?
         (mk-TΛ sy x (abstract-free (loop (open-scope st (mk-TFree #f x)) unrolled) x))]
        [(Tμ: sy x st tr n)
         (cond
          [(set-member? unrolled t)
           ;; It's been unfolded once. We won't unfold more than that.
           (loop (open-scope st (mk-TFree sy x)) unrolled)]
          [else
           (define opened (open-scope st t))
           (check-path-productive opened t break) ;; uses pointer equality
           (mk-Tμ sy x (abstract-free (loop opened (set-add unrolled t)) x) tr n)])]
        [(TName: sy x)
         (cond
          [(set-member? unrolled x) t]
          [else (loop (hash-ref (Language-user-spaces (current-language))
                                x (λ () (error 'check-path-productive "Unbound name ~a" x)))
                      (set-add unrolled x))])]
        [(or (TSUnion: sy ts) (TRUnion: sy ts))
         (define ts* (map loop* ts))
         (define ts** (flatten-unions-in-list ts*))
         (cond
          [(vaguely-shaped? ts**)
           (unless ar? (break #f))
           (*TRUnion sy ts**)]
          [else
           (*TSUnion sy ts**)])]
        [(TVariant: sy n ts tr)
         (*TVariant sy n (map loop* ts) tr)]
        [(TMap: sy t-dom t-rng ext)
         (mk-TMap sy (loop* t-dom) (loop* t-rng) ext)]
        [(TSet: sy t ext)
         (mk-TSet sy (loop* t) ext)]
        [_ t]))))
