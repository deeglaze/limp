#lang racket/base
(require (for-syntax syntax/parse racket/syntax racket/base)
         racket/list racket/match racket/set
         racket/trace
         "common.rkt")
(provide (all-defined-out))

(struct addrize ()) (define -addrize (addrize))

;; Type representations
;; We'll want something like rep-utils later to intern types and check equality faster?
(struct Type (key support free quality mono?) #:mutable #:transparent
        #:methods gen:equal+hash
        [(define (equal-proc t0 t1 rec) (eqv? (Type-key t0) (Type-key t1)))
         (define (hash-proc t rec) (rec (Type-key t)))
         (define (hash2-proc t rec) (rec (Type-key t)))])
(define intern-table (make-hash))
(define-syntax (define-type stx)
  (syntax-parse stx
    [(_ name fields)
     (define/with-syntax mk-name (format-id #'name "mk-~a" #'name))
     (define/with-syntax name: (format-id #'name "~a:" #'name))
     #`(begin #,(syntax/loc stx (struct name Type fields #:transparent))
              #,(syntax/loc stx
                  (define (mk-name . fields)
                    (hash-ref! intern-table (list 'name . fields)
                               (λ () (name (hash-count intern-table) #f #f #f 'unset . fields)))))
              #,(syntax/loc stx
                 (define-match-expander name:
                   (syntax-rules () [(_ . fields) (name _ _ _ _ _ . fields)]))))]))
(struct base-T⊤ Type () #:transparent)
  (define T⊤ (base-T⊤ 0 ∅eq ∅eq 'abstract #t))
  (hash-set! intern-table '(T⊤) T⊤)
  (define (T⊤? x) (eq? T⊤ x))
(define-type TSUnion (ts))
  (define T⊥ (TSUnion 1 ∅eq ∅eq 'concrete #t '()))
  (hash-set! intern-table '(T⊥) T⊥)
(define-type TRUnion (ts))
(define-type TVariant (name ts trust-rec trust-con))
(define-type TExternal (name))
(define-type Tμ (x st r c n)) ;; name for printing
(define-type TΛ (x st))
(define-type TCut (t u))
(define-type TFree (x taddr))
(define-type TBound (i taddr))
(define-type TName (x taddr)) ;; top level interaction and letrec-like binding
(define-type TMap (t-dom t-rng ext))
(define-type TSet (t ext))
(define-type TAddr (space mm em))
;; First order function
(define-type TArrow (dom rng))
;; Locally nameless stuff
(struct Scope (t) #:transparent)

#||#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Binding/naming operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (open-scope s t)
  (match-define (Scope t*) s)
  (let open ([t* t*] [i 0])
    (define (open* t*) (open t* i))
    (match t*
      [(TBound: i* taddr)
       (if (= i i*)
           (if (eq? t -addrize)
               taddr
               t)
           t*)]
      [(Tμ: x (Scope t) r c n) (mk-Tμ x (Scope (open t (add1 i))) r c n)]
      [(TΛ: x (Scope t)) (mk-TΛ x (Scope (open t (add1 i))))]
      ;; boilerplate
      [(or (? T⊤?) (? TAddr?) (? TFree?) (? TExternal?) (? TName?)) t*]
      [(TSUnion: ts) (*TSUnion (map open* ts))]
      [(TRUnion: ts) (*TRUnion (map open* ts))]
      [(TVariant: name ts r c) (mk-TVariant name (map open* ts) r c)]
      [(TCut: t u) (mk-TCut (open* t) (open* u))]
      [(TMap: t-odm t-rng ext) (mk-TMap (open* t-dom) (open* t-rng) ext)]
      [(TSet: t ext) (mk-TSet (open* t) ext)])))

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
  (define (conflict-res f x t) (name-conflict-res name on-conflict))
  (let open ([t* t*] [i 0])
    (define (open* t*) (open t* i))
    (define (rec t) (Scope (open t (add1 i))))
    (match t*
      [(TBound: i* taddr) (if (= i i*) (mk-TFree name taddr) t*)]
      [(Tμ: x (Scope t) r c n) (conflict-res (λ (x s) (mk-Tμ x s r c n)) x t rec)]
      [(TΛ: x (Scope t)) (conflict-res mk-TΛ x t rec)]
      ;; boilerplate
      [(or (? T⊤?) (? TAddr?) (? TFree?) (? TExternal?) (? TName?)) t*]
      [(TSUnion: ts) (mk-TSUnion (map open* ts))]
      [(TRUnion: ts) (mk-TRUnion (map open* ts))]
      [(TVariant: name ts r c) (mk-TVariant name (map open* ts) r c)]
      [(TCut: t u) (mk-TCut (open* t) (open* u))]
      [(TMap: t-dom t-rng ext) (mk-TMap (open* t-dom) (open* t-rng) ext)]
      [(TSet: t ext) (mk-TSet (open* t) ext)])))

(define (subst-name t name s)
  (define (conflict-res f x t) (name-conflict-res name #f))
  (let subst ([t t])
    (match t
      [(TName: x _) (if (equal? x name) s t)]
      [(Tμ: x (Scope t) r c n) (conflict-res (λ (x s) (mk-Tμ x s r c n)) x t subst)]
      [(TΛ: x (Scope t)) (conflict-res mk-TΛ x t subst)]
      ;; boilerplate
      [(or (? T⊤?) (? TAddr?) (? TFree?) (? TExternal?) (? TBound?)) t]
      [(TSUnion: ts) (*TSUnion (map subst ts))]
      [(TRUnion: ts) (*TRUnion (map subst ts))]
      [(TVariant: name ts r c) (mk-TVariant name (map subst ts) r c)]
      [(TCut: t u) (mk-TCut (subst t) (subst u))]
      [(TMap: t-dom t-rng ext) (mk-TMap (subst t-dom) (subst t-rng) ext)]
      [(TSet: t ext) (mk-TSet (subst t) ext)])))

(define (abstract-free t name)
  (Scope
   (let abs ([t t] [i 0])
     (define (abs* t) (abs t i))
     (match t
       [(TFree: x taddr) (if (equal? x name) (mk-TBound i taddr) t)]
       [(Tμ: x (Scope t) r c n) (mk-Tμ x (Scope (abs t (add1 i))) r c n)]
       [(TΛ: x (Scope t)) (mk-TΛ x (Scope (abs t (add1 i))))]
       ;; boilerplate
       [(or (? T⊤?) (? TAddr?) (? TBound?) (? TName?)) t]
       [(TSUnion: ts) (mk-TSUnion (map abs* ts))]
       [(TRUnion: ts) (mk-TRUnion (map abs* ts))]
       [(TCut: t u) (mk-TCut (abs* t) (abs* u))]
       [(TVariant: name ts r c) (mk-TVariant name (map abs* ts) r c)]
       [(TMap: t-dom t-rng ext) (mk-TMap (abs* t-dom) (abs* t-rng) ext)]
       [(TSet: t ext) (mk-TSet (abs* t) ext)]))))
;; Abstract inside-out.
(define (quantify-frees t names)
  (match names
    ['() t]
    [(cons name names)
     (abstract-frees (mk-TΛ (abstract-free t name)) names)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Type operations (memoizes results in type-rep)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (support t)
  (or (Type-support t)
      (let ([t* (match t
                  [(or (TSUnion: ts) (TRUnion: ts) (TVariant: _ ts _ _)
                       (app (match-lambda [(or (TMap: d r _) (TCut: d r)) (list d r)]) ts)
                       (app (match-lambda [(TSet: s _) (list s)]) ts))
                   (for/union ([t (in-list ts)]) (support t))]
                  [(or (TFree: x _) (TName: x _)) (seteq x)]
                  [(or (Tμ: x (Scope t) _ _ _) (TΛ: x (Scope t)))
                   (set-add (support t) x)]
                  [_ ∅eq])])
        (set-Type-support! t t*)
        t*)))

(define (free t)
  (or (Type-free t)
      (let ([t* (match t
                  [(or (TSUnion: ts) (TRUnion: ts) (TVariant: _ ts _ _))
                   (for/union ([t (in-list ts)]) (free t))]
                  [(or (TMap: d r _) (TCut: d r))
                   (set-union (free d) (free r))]
                  [(or (TFree: x _) (TName: x _)) (seteq x)]
                  [(or (Tμ: _ (Scope t) _ _ _)
                       (TΛ: _ (Scope t))
                       (TSet: t _))
                   (free t)]
                  [_ ∅eq])])
        (set-Type-free! t t*)
        t*)))

(define (mono-type? t)
  (define m (Type-mono? t))
  (cond
   [(eq? m 'unset)
    (define b
      (match t
        [(or (TSUnion: ts) (TRUnion: ts) (TVariant: _ ts _ _)
             (app (match-lambda [(or (TMap: d r _) (TCut: d r)) (list d r)]) ts))
         (andmap mono-type? ts)]
        [(or (Tμ: _ (Scope t) _ _ _)  (TSet: t _))
         (mono-type? t)]
        [(? TΛ?) #f]
        [(TName: x _) (error 'mono-type? "Todo: interaction with top level type defs")]
        [_ #t]))
    (set-Type-mono?! t b)
    b]
   [else m]))

(define (type-contains? ty inner)
  (let search ([ty ty])
    (or (equal? ty inner)
        (match ty
          [(or (TΛ: _ (Scope t)) (Tμ: _ (Scope t) _ _ _)) (search t)]
          ;; boilerplate
          [(or (? T⊤?) (? TAddr?) (? TBound?) (? TName?) (? TFree?)) #f]
          [(or (TSUnion: ts) (TRUnion: ts) (TVariant: _ ts _ _)) (ormap search ts)]
          [(TCut: t u) (or (search t) (search u) (search (resolve ty)))]
          [(TMap: t-dom t-rng _)
           (or (search t-dom) (search t-rng))]
          [(TSet: t _) (search t)]))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Other type operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (flatten-unions-in-list ts)
  (append-map
   (λ (t)
      (match t
        [(or (TRUnion: ts*) (TSUnion: ts*))
         (flatten-unions-in-list ts*)]
        [_ (list t)]))
   ts))

(define (simplify-types ts)
  (match (remove-sorted-dups (sort (flatten-unions-in-list ts) < #:key Type-key))
    [(list t) t]
    ['() T⊥]
    [ts ts]))

;; reverses, but it's still canonically sorted.
(define (remove-sorted-dups ts) ;; assumes #f not the first element of list.
  (let loop ([ts ts] [last #f] [new '()])
    (match ts
      ['() new]
      [(cons t ts)
       (if (equal? t last)
           (loop ts last new)
           (loop ts t (cons t new)))])))
(define (*TSUnion ts) (mk-TSUnion (simplify-types ts)))
(define (*TRUnion ts) (mk-TRUnion (simplify-types ts)))

(define (needs-resolve? τ)
  (or (TName? τ) (Tμ? τ) (TCut? τ)))

;; resolve : Type Map[Name,Type] -> Maybe[Type]
(define (resolve t Γ)
  (let fuel ([t t] [i (hash-count Γ)])
    (and (< 0 i)
         (match t
           [(TName: x _) (fuel (hash-ref Γ x) (sub1 i))]
           [(Tμ: x st r c n)
            ;; INVARIANT: the only μs at this point are trusted.
            (unless (or r c) (error 'resolve "Unfolds should be resolved first: ~a" t))
            (open-scope st t)]
           [(TCut: t* u)
            (match (resolve t*)
              [(TΛ: _ st) (resolve (open-scope st u))]
              [_ (error 'resolve "Expected a type abstraction at ~a: got ~a" t t*)])]
           [_ t]))))

(define (<:? L τ σ)
  ((<:?-aux (Language-user-spaces L) #f) ∅ τ σ))
(define ((<:?-aux Γ E<:) A τ σ) ;; TODO: use axiom rules
  (let <:?-aux ([A A] [τ τ] [σ σ])
       (define-syntax seq-<:
         (syntax-rules ()
           [(_ A last) last]
           [(_ A τ σ more0 . more)
            (let ([A (<:?-aux A τ σ)])
              (seq-<: A more0 . more))]))
       (define (grow-A) (set-add A (cons τ σ)))
       (cond
        [(equal? τ σ) A]
        [(set-member? A (cons τ σ)) A]
        [else
         (match* (τ σ)
           [(_ (? T⊤?)) #t]
           [((? T⊥?) _) #t]
           [((or (TRUnion: ts) (TSUnion: ts)) _)
            (let each ([A (grow-A)] [ts ts])
              (match ts
                ['() #t]
                [(cons t ts)
                 (seq-<: A
                         t σ
                         (each A* ts))]))]
           [(_ (or (TRUnion: σs) (TSUnion: σs)))
            (let some ([A (grow-A)] [σs σs])
              (match σs
                ['() #f]
                [(cons σ σs)
                 (define A* (<:?-aux A τ σ))
                 (or A* (some A* σs))]))]
           [((TΛ: _ sτ) (TΛ: _ sσ))
            (define name (mk-TFree (gensym 'dummy) #f))
            (<:?-aux A (open-scope sτ name) (open-scope sσ name))]
           [((TSet: τ ext) (TSet: σ ext)) (<:?-aux A τ σ)]
           [((TMap: τk τv ext) (TMap: σk σv ext))
            (seq-<: A
                    τk σk
                    (<:?-aux A σv σv))]
           ;; XXX: for now, trust does not have subtyping.
           [((TVariant: n τs tr tc) (TVariant: n σs tr tc))
            (let each ([A (grow-A)] [τs τs] [σs σs])
              (match* (τs σs)
                [('() '()) A]
                [((cons τ τs) (cons σ σs))
                 (seq-<: A τ σ (each A τs σs))]
                [(_ _) #f]))]
           [((? needs-resolve?) _) (<:?-aux (grow-A) (resolve τ Γ) σ)]
           [(_ (? needs-resolve?)) (<:?-aux (grow-A) τ (resolve σ Γ))]
           [(_ _) #f])])))

(define (type-join L τ σ)
  (cond [(<:? L τ σ) σ]
        [(<:? L σ τ) τ]
        [else
         (match* (τ σ)
           [((TVariant: n τs tr tc) (TVariant: n σs tr tc)) ???]
           [((TΛ: x (Scope t)) (TΛ: _ (Scope s))) ???]
           ;; boilerplate
           ;;[(or (? T⊤?) (? TAddr?) (? TBound?) (? TName?)) t]
           [((TSUnion: ts) _) ???]
           [(TRUnion: ts) ???]
           [(TMap: t-dom t-rng ext) ???]
           [((TSet: t ext) (TSet: s ext)) ???]
           ;; FIXME: ???
           [(Tμ: x (Scope t) r c n) ???]
           [(TCut: t u) ???]
           [(_ _) (*TRUnion (list τ σ))])]) (error 'type-join "Todo"))

(define (type-meet L τ σ)
  (cond [(<:? L τ σ) τ]
        [(<:? L σ τ) σ]
        [else
         (match* (τ σ)
           [(_ _) (error 'type-meet "Todo")])]))

(define (castable L from to)
  (define us (Language-user-spaces L))
  (let check ([from from] [to to])
    (or (<:? L from to) ;; upcast
        (T⊤? from)
        (match* (from to)
          [((TΛ: _ (Scope f)) (TΛ: _ (Scope t)))
           (check f t)]
          [((TVariant: n tsf tr tc) (TVariant: n tst tr tc))
           (let all ([tsf tsf] [tst tst])
             (match* (tsf tst)
               [('() '()) #t]
               [((cons f tsf) (cons t tst))
                (and (check f t) (all tsf tst))]
               [(_ _) #f]))]
          [((Tμ: _ (Scope f) r c n) (Tμ: _ (Scope t) r c n))
           (check f t)]
          [((TMap: df rf) (TMap: dt rt))
           (and (check df dt)
                (check rf rt))]
          [((TSet: f) (TSet: t)) (check f t)]
          [((TSUnion: tsf) _) (error 'castable "Todo: unions")]
          [(_ (TSUnion: tst)) (error 'castable "Todo: unions")]
          [((and (not (? Tμ?)) (? needs-resolve?)) _)
           (check (resolve from us) to)]
          [(_ (and (not (? Tμ?)) (? needs-resolve?)))
           (check from (resolve to us))]
          [(_ _) #f]))))

;; Find all instances of variants named n with given arity, and return
;; their type, additionally quantified by all the containing Λs.
(define (lang-variants-of-arity L n arity)
  (define us (Language-user-spaces L))
  (for/fold ([found '()])
      ([τ (in-hash-values us)])
    (let collect ([τ τ] [TVs '()] [found fould] [μs ∅eq] [names ∅eq])
      (define (collect* τs found)
        (match τs
          ['() found]
          [(cons τ τs)
           (define found* (collect τ TVs found μs names))
           (collect* τs found*)]))
      (match τ
        [(TVariant: n* ts tr tc)
         (define found*
           (if (and (eq? n n*)
                    (= arity (length ts)))
               (cons (quantify-frees TVs τ) found)
               found))
         (collect* ts found*)]
        [(TΛ: x s)
         (define x* (gensym x))
         (define TVs* (cons x* TVs))
         (collect (open-scope s (mk-TFree x* #f)) TVs* found μs names)]
        [(TName: x _)
         (if (set-member? names x)
             found
             (collect (hash-ref us x) TVs found μs (set-add names x)))]
        [(Tμ: x s)
         (if (set-member? μs τ)
             found
             (collect (open-scope s τ) TVs found (set-add μs τ) names))]
        [(? TCut?) (collect (resolve τ us) TVs found μs names)]
        [(TMap: d r _)
         (collect r TVs
                  (collect d TVs found μs names)
                  μs names)]
        [(TSet: v) (collect v TVs found μs names)]
        [(or (TRUnion: ts) (TSUnion: ts)) (collect* ts found)]
        [_ found]))))

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
    [(or (? T⊤?) (? TAddr?) (? TBound?) (? TExternal?) (? TName?)) #t]
    [(? TFree?) #f]
    [(or (Tμ: _ (Scope t) _ _ _) (TΛ: _ (Scope t)) (TSet: t _))
     (no-free? t)]
    ;; boilerplate
    [(or (TSUnion: ts) (TRUnion: ts) (TVariant: _ ts _ _))
     (andmap no-free? ts)]
    [(or (TMap: t0 t1 _) (TCut: t0 t1))
     (and (no-free? t0) (no-free? t1))]))

(define (close-type-with t ES meta-names space-info forall)
  (let/ec break
    (let close ([t (for/fold ([t t]) ([ta (in-list forall)])
                     (TΛ ta (abstract-free t ta)))])
      (match t
        [(TFree: x taddr)
         (cond
          [(hash-has-key? ES x) (mk-TExternal x)]
          [(hash-has-key? meta-names x)
           (define S (hash-ref meta-names x))
           (if (hash-has-key? ES S)
               (mk-TExternal S)
               (mk-TName S taddr))]
          [else (break #f)])]
        ;; boilerplate
        [(or (? T⊤?) (? TAddr?) (? TBound?) (? TExternal?)) t]
        [(Tμ: x (Scope t) r c n) (mk-Tμ x (Scope (close t)) r c n)]
        [(TΛ: x (Scope t)) (mk-TΛ x (Scope (close t)))]
        [(TSUnion: ts) (mk-TSUnion (map close ts))]
        [(TRUnion: ts) (mk-TRUnion (map close ts))]
        [(TVariant: n ts r c) (mk-TVariant n (map close ts) r c)]
        [(TMap: d r ex) (mk-TMap (close d) (close r) ex)]
        [(TSet: s ex) (mk-TSet (close s) ex)]
        [(TCut: t u) (mk-TCut (close t) (close u))]
        [(? TName?) (error 'close-type-with "Already closed ~a" t)]))))

;; check-path-productive : Type Type (any -> ⊥) -> (void)
;; (void) iff endpoint unreachable from t. Otherwise break invoked with #f.
(define (check-path-productive t endpoint break)
  (let search ([t t])
    (when (eq? t endpoint) (break #f))
    (match t
      [(or (TΛ: _ (Scope t)) (Tμ: _ (Scope t) _ _ _)) (search t)]
      [(or (TSUnion: ts) (TRUnion: ts)) (for-each search ts)]
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
       [(TVariant: name ts _ _)
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
(define (check-productive-and-classify-unions t ar? Γ)
  (let/ec break
    (let loop ([t t] [unrolled ∅eq])
      (define (loop* t) (loop t unrolled))
      (match t
        [(TΛ: x st) ;; XXX: TFree taddr should be #f or...?
         (mk-TΛ (abstract-free (loop (open-scope st (TFree x #f)) unrolled) x))]
        [(Tμ: x st r c n)
         (cond
          [(set-member? unrolled t)
           ;; It's been unfolded once. We won't unfold more than that.
           (loop (open-scope st (TFree x #f)) unrolled)]
          [else
           (define opened (open-scope st t))
           (check-path-productive opened t break) ;; uses pointer equality
           (mk-Tμ x (abstract-free (loop opened (set-add unrolled t)) x) r c n)])]
        [(TName: x _)
         (cond
          [(set-member? unrolled x) t]
          [else (loop (hash-ref Γ x (λ () (error 'check-path-productive "Unbound name ~a" x)))
                      (set-add unrolled x))])]
        [(or (TSUnion: ts) (TRUnion: ts))
         (define ts* (map loop* ts))
         (define ts** (flatten-unions-in-list ts*))
         (cond
          [(vaguely-shaped? ts**)
           (unless ar? (break #f))
           (*TRUnion ts**)]
          [else (*TSUnion ts**)])]
        [(TVariant: n ts r c)
         (mk-TVariant n (map loop* ts) r c)]
        [(TMap: t-dom t-rng ext)
         (mk-TMap (loop* t-dom) (loop* t-rng) ext)]
        [(TSet: t ext)
         (mk-TSet (loop* t) ext)]
        [_ t]))))
