#lang typed/racket/base
(require (for-syntax racket/base)
         racket/match racket/list racket/set)
(require/typed racket/pretty [pretty-print (-> Any Void)]
               [pretty-write (-> Any Void)])
(require/typed racket/port [with-output-to-string (-> (-> Any) String)])

(define-syntax (??? stx) #'(error 'todo))

(: set-smap : (All (A B) (-> (Setof A) (-> A B) (Setof B))))
(define (set-smap S f)
  (for/fold ([b : (Setof B) (set)]) ([x (in-set S)]) (set-add b (f x))))

(: hash-set-many : (All (A B) (-> (HashTable A B) (Listof A) (Listof B) (HashTable A B))))
(define (hash-set-many ρ xs ys)
  (for/fold ([ρ : (HashTable A B) ρ])
      ([x (in-list xs)]
       [y (in-list ys)])
    (hash-set ρ x y)))

(: map-union : (All (A B) (-> (Setof B) (Listof A) (-> A (Setof B)) (Setof B))))
(define (map-union base lst f)
  (for/fold ([S : (Setof B) base]) ([x (in-list lst)])
    (set-union S (f x))))

(: rassoc : (All (A) (-> (-> A A A) A (Listof A) A)))
(define (rassoc bin ⊥ lst)
  (match lst
    [(cons x y)
     (if (null? y)
         x
         (bin x (rassoc bin ⊥ y)))]
    ['() ⊥]))

;; Raw implementation first to play with.

(define-type Module Symbol)
(define-type Label Symbol)

;; Expressions
(struct app ([e : Expr] [es : (Listof Expr)]) #:transparent)
(struct ref ([x : Symbol]) #:transparent)
(struct lam ([xs : (Listof Symbol)] [e : Expr]) #:transparent)
;; Construct S, run e, attach S to e's result with +/- labels.
(struct smon ([+ : Symbol] [- : Symbol] [S : SContract] [e : Expr]) #:transparent)
 ;; ηe --> η, T --> Tv, attach Tv to η, run e.
(struct tmon ([ηe : Expr] [T : Expr]) #:transparent)
(struct ife ([g : Expr] [t : Expr] [e : Expr]) #:transparent)
(struct letrece ([cs : (Listof (List Symbol Expr))] [e : Expr]) #:transparent)
(struct begine ([es : (Pairof Expr (Listof Expr))]) #:transparent)
(struct primop ([which : Symbol]) #:transparent) ;; 'cons | 'new-timeline | 'pair? | 'car | 'cdr | 'null?
(define-type Expr (U app ref lam smon tmon ife letrece begine primop Datum
                     bind kl · ∩ ∪ ¬ ε ⊤ ⊥))
(define-type Datum (U Symbol String Number '() (Pair Datum Datum) #t #f Void))

(: *letrece : (-> (Listof (List Symbol Expr)) Expr Expr))
(define (*letrece cs e) (if (null? cs) e (letrece cs e)))

#|
Expr template:
  (match e
    [(app e es) ???]
    [(ref x) ???]
    [(lam xs e) ???]
    [(smon + - S e) ???]
    [(tmon ηe T) ???]
    [(ife g t e) ???]
    [(letrece cs e) ???]
    [(begine es) ???]
    [(primop which) ???]
    [(? datum?) ???]
    [(∩ T0 T1) ???]
    [(∪ T0 T1) ???]
    [(· T0 T1) ???]
    [(¬ T) ???]
    [(kl T) ???]
    [(bind e) ???]
    [(ε) ???]
    [(⊤) ???]
    [(⊥) ???]
    [_ (error who "Bad expression ~a" e)])
|#
(: first* (All (A B) (-> (List A B) A)))
(define (first* lst) (car lst))
(: second* (All (A B) (-> (List A B) B)))
(define (second* lst) (cadr lst))

;; Expression's support
(: supp : (-> Expr (Setof Symbol)))
(define (supp e)
  (match e
    [(app e es) ((inst map-union Expr Symbol) (supp e) es supp)]
    [(ref x) (seteq x)]
    [(lam xs e) (set-union (supp e) (apply seteq xs))]
    [(smon + - S e) (set-union (Ssupp S) (supp e))]
    [(tmon ηe T) (set-union (supp ηe) (supp T))]
    [(ife g t e) (set-union (supp g) (supp t) (supp e))]
    [(letrece cs e) (set-union (supp e)
                               (apply seteq ((inst map Symbol (List Symbol Expr))
                                             (inst first* Symbol Expr)
                                             cs)))]
    [(? primop?) (seteq)]

    [(bind e) (supp e)]
    [(or (? ε?) (? ⊥?) (? ⊤?)) (seteq)]
    [(or (kl T) (¬ T)) (supp T)]
    [(or (· T T*) (∪ T T*) (∩ T T*)) (set-union (supp T) (supp T*))]
    [_ (error 'supp "Bad expression ~a" e)]))

;; Free variables
(: fv : (-> Expr (Setof Symbol)))
(define (fv e)
  (match e
    [(app e es) (map-union (fv e) es fv)]
    [(ref x) (seteq x)]
    [(lam xs e) (set-subtract (fv e) (apply seteq xs))]
    [(smon + - S e) (set-union (Sfv S) (fv e))]
    [(tmon ηe T) (set-union (fv ηe) (fv T))]
    [(ife g t e) (set-union (fv g) (fv t) (fv e))]
    [(letrece cs e) (set-subtract (map-union (fv e) cs (compose fv (inst second* Symbol Expr)))
                                  (apply seteq (map (inst first* Symbol Expr) cs)))]
    [(begine es) (map-union ((inst seteq Symbol)) es fv)]
    [(primop which) (seteq)]
    [(? datum?) (seteq)]

    [(bind e) (fv e)]
    [(or (? ε?) (? ⊥?) (? ⊤?)) (seteq)]
    [(or (kl T) (¬ T)) (fv T)]
    [(or (· T T*) (∪ T T*) (∩ T T*)) (set-union (fv T) (fv T*))]
    [_ (error 'fv "Bad expression ~a" e)]))

;; another expression is quoted data

; Values
(struct Clo ([xs : (Listof Symbol)] [e : Expr] [ρ : Env]) #:transparent)
(struct Clo/blessed ([ℓ- : Module] [ℓ+ : Module] [Svs- : (Listof SContractv)] [Sv+ : SContractv]
                     [ℓ : Label] [η : timeline] [clv : Procedure-Value]) #:transparent)
(struct timeline ([nonce : Any]) #:transparent)
(struct boxv ([a : Any]) #:transparent)
(struct weak ([v : Value]) #:transparent)
(struct weakly ([v : Value]) #:transparent)
;; cons is another value
(struct undefined () #:transparent) (define -undefined (undefined))
(define-predicate datum? Datum)
#;
(define (datum? x)
  (or (boolean? x)
      (number? x)
      (string? x)
      (symbol? x)
      (null? x)
      (and (pair? x) (datum? (car x)) (datum? (cdr x)))
      (void? x)))
(define-type Value (U Procedure-Value timeline boxv weak undefined
                      #t #f Number String Symbol '() (Pairof Value Value) Void
                      call ret ;; event objects
                      TCon-Value))
(define-type Procedure-Value (U Clo Clo/blessed weakly primop))
(define-type Non-Wrap-TCon-Value (U ⊤ ⊥ ε klv ·v ∪v ∩v ¬v weakly primop bindv))
(define-type TCon-Value (U Clo Clo/blessed Non-Wrap-TCon-Value))
(define-predicate non-wrap-tcon-value? Non-Wrap-TCon-Value)
(define-predicate tcon-value? TCon-Value)

(: rng : (All (A B) (-> (HashTable A B) (Setof B))))
(define (rng h) (for/fold ([b : (Setof B) (seteq)]) ([a (in-hash-values h)]) (set-add b a)))

(: weaken-addr : (-> Any (Setof Any) Any))
(define (weaken-addr a live)
  (if (set-member? live a) a -undefined))

(: weaken-env : (All (A) (-> (HashTable A Any) (Setof Any) (HashTable A Any))))
(define (weaken-env ρ live)
  (for/fold ([ρ* : (HashTable A Any) (hash)])
      ([(x a) (in-hash ρ)])
    (hash-set ρ* x (weaken-addr a live))))

(: weaken-proc : (-> Procedure-Value (Setof Any) Procedure-Value))
(define (weaken-proc fn live)
  (match fn
    [(Clo xs e ρ) (Clo xs e (weaken-env ρ live))]
    [(? Clo/blessed? fn) (weaken-blessed fn live)]
    [v v]))

(: weaken-blessed : (-> Clo/blessed (Setof Any) Clo/blessed))
(define (weaken-blessed fn live)
  (match fn
    [(Clo/blessed ℓ- ℓ+ Svs- Sv+ ℓ η clv)
     (Clo/blessed ℓ- ℓ+
                  (map (λ ([s : SContractv]) (weaken-scon s live)) Svs-)
                  (weaken-scon Sv+ live)
                  ℓ
                  (weaken-timeline η live)
                  (weaken-proc clv live))]))

(: weaken-timeline : (-> timeline (Setof Any) timeline))
(define (weaken-timeline t live)
  (match t [(timeline a) (timeline (weaken-addr a live))]))

(: weaken : (-> Value (Setof Any) Value))
(define (weaken v live)
  (let rec ([v v])
    (match v
      [(boxv a) (boxv (weaken-addr a live))]
      [(cons A D) (cons (rec A) (rec D))]
      [(? timeline? v) (weaken-timeline v live)]
      [(? Clo? v) (weaken-proc v live)]
      [(? Clo/blessed? v) (weaken-proc v live)]
      [(call ℓ fn args) (call ℓ (weaken-blessed fn live) (map rec args))]
      [(ret ℓ fn v) (ret ℓ (weaken-blessed fn live) (rec v))]

      [(kl Tv) (kl (rec Tv))]
      [(¬ Tv) (¬ (rec Tv))]
      [(bindv Tv) (bindv (weaken-proc Tv live))]
      [(∪ Tv0 Tv1) (∪ (rec Tv0) (rec Tv1))]
      [(∩ Tv0 Tv1) (∩ (rec Tv0) (rec Tv1))]
      [(· Tv0 Tv1) (· (rec Tv0) (rec Tv1))]

      ;; includes (weak _) and (WClo _ _ _)
      [v v])))

(: weaken-scon : (-> SContractv (Setof Any) SContractv))
(define (weaken-scon Sv live)
  (let rec : SContractv ([Sv : SContractv Sv])
       (cond [(-->/blessed? Sv)
              (match-define (-->/blessed Svs- Sv+ ℓ η) Sv)
              (-->/blessed (map rec Svs-) (rec Sv+) ℓ (cast (weaken η live) timeline))]
             [(cons/blessed? Sv)
              (match-define (cons/blessed Av Dv) Sv)
              (cons/blessed (rec Av) (rec Dv))]
             [(any/c? Sv) Sv]
             [else (weaken-proc Sv live)])))

;; value -> (values Strongly-touched Weakly-touched)
(: touch : (-> Value (Setof Any)))
(define (touch v)
  (match v
   [(Clo _ _ ρ) (rng ρ)]
   [(timeline a) (seteq a)]
   [(boxv a) (seteq a)]
   [(Clo/blessed _ _ Svs- Sv+ _ η clv)
    (map-union
     (set-union (touch η) (touch clv) (scon-touch Sv+))
     Svs-
     scon-touch)]
   [(cons A D) (set-union (touch A) (touch D))]

   [(call _ fn args)
    (map-union (touch fn) args touch)]
   [(ret _ fn  v) (set-union (touch fn) (touch v))]

   [(or (kl Tv) (¬ Tv) (bindv Tv)) (touch Tv)]
   [(or (∪ Tv0 Tv1) (∩ Tv0 Tv1) (· Tv0 Tv1))
    (set-union (touch Tv0) (touch Tv1))]
   ;; includes (weak _) and (WClo _ _ _)
   [_ (seteq)]))

(: scon-touch : (-> SContractv (Setof Any)))
(define/match (scon-touch Sv)
  [((-->/blessed Svs- Sv+ _ η))
   (map-union (set-union (scon-touch Sv+) (touch η))
              Svs-
              scon-touch)]
  [((cons/blessed Av Dv))
   (set-union (scon-touch Av) (scon-touch Dv))]
  [((? any/c?)) (seteq)]
  [(v) (touch (cast v Value))])

(: frame-touch : (-> Frame (Setof Any)))
(define/match (frame-touch φ)
  [((evk _ vs ρ)) (map-union (rng ρ) vs touch)]
  [((or (sk _ _ _ ρ)
        (ifk _ _ ρ)
        (lrk _ _ _ ρ)
        (mkd _ ρ)
        (mkt _ ρ)
        (kbin₀ _ _ ρ)
        (begink _ ρ)))
   (rng (cast ρ Env))]

  [((ch*k Svs- fn vs args))
   (map-union
    (map-union
     (map-union (touch fn) Svs- scon-touch)
     args
     touch)
    vs
    touch)]
  [((or (chret fn) (sret fn) (blret fn))) (touch fn)]
  [((chDk _ _ Dv v)) (set-union (scon-touch Dv) (touch v))]
  [((or (wrapk _ _ Sv) (mkcons Sv))) (scon-touch (cast Sv SContractv))]

  [((blcall fn vs ev))
   (map-union
    (set-union (touch fn) (touch ev))
    vs
    touch)]

  [((or (tbin₁ _ Tv) (seqk Tv) (kbin₁ _ Tv) (consk Tv))) (touch Tv)]
  [((or (seq2k T ev η _) (tbin₀ _ T ev η _)))
   (set-union (touch (cast T Value)) (touch (cast ev Value)) (touch (cast η Value)))]

  [((or (negk _ _ _ _ ρ Svs-)
        (timelinek Svs- _ _ ρ)))
   ((inst map-union SContractv Any) (rng (cast ρ Env)) (cast Svs- (Listof SContractv)) scon-touch)]
  [((arrk Svs Sv _))
   ((inst map-union SContractv Any) (scon-touch Sv) Svs scon-touch)]
  [(_) (seteq)])

(: kont-touch : (-> Kont (Setof Any)))
(define (kont-touch κ)
  (: both : (-> Frame Kont (Setof Any)))
  (define (both φ κ) (set-union (frame-touch φ) (kont-touch κ)))
  (match κ
    [(scons φ κ) (both φ κ)]
    [(econs φ κ) (both φ κ)]
    [(tcons φ κ) (both φ κ)]
    [(acons φ κ) (both φ κ)]
    [(bcons φ κ) (both φ κ)]
    [(ccons φ κ) (both φ κ)]
    [(pcons φ κ) (both φ κ)]
    [(lcons φ κ) (both φ κ)]
    [(vcons φ κ) (both φ κ)]
    [(hcons φ κ) (both φ κ)]
    ['() (seteq)]))

;; ℘[Addr] Map[Addr,Value] -> (values Strongly-reachable Only-weakly-reachable)
(: reachable : (-> (Setof Any) Store (Setof Any)))
(define (reachable root σ)
  (: seen : (HashTable Any #t))
  (define seen (make-hasheq '()))
  (let rec : (Setof Any) ([todo : (Setof Any) root])
    (cond [(set-empty? todo)
           (for/fold ([S : (Setof Any) (set)]) ([a (in-hash-keys seen)]) (set-add S a))]
          [else
           (define a (set-first todo))
           (define todo* (set-rest todo))
           (cond
            [(hash-has-key? seen a) (rec todo*)]
            [else
             (hash-set! seen a #t)
             (rec (set-union todo* (touch (hash-ref σ a))))])])))

(: state-touch : (-> State (values (Setof Any) Store)))
(define (state-touch ς)
  (match ς
    [(ev _ ρ σ κ)
     (values (set-union (rng ρ) (kont-touch κ)) σ)]
    [(co κ v σ)
     (values (set-union (kont-touch κ) (touch v)) σ)]
    [(ap fn args σ κ)
     (values
      (map-union
       (set-union (touch fn) (kont-touch κ))
       args
       touch)
      σ)]
    [(check ℓ+ ℓ- S v σ κ)
     (values (set-union (scon-touch S) (touch v) (kont-touch κ)) σ)]
    [(ev-syn _ ρ σ κ)
     (values (set-union (kont-touch κ) (rng ρ)) σ)]
    [(send T ev _ η σ κ)
     (values (set-union (touch T) (touch ev) (touch η) (kont-touch κ)) σ)]
    [(check-app Svs- fn vs* vs σ κ)
     (values
      (map-union
       (map-union
        (map-union (set-union (touch fn) (kont-touch κ))
                   Svs-
                   scon-touch)
        vs*
        touch)
       vs
       touch)
      σ)]))

(: state-replace-σ : (-> State Store State))
(define (state-replace-σ ς σ)
  (match ς
    [(ev e ρ _ κ) (ev e ρ σ κ)]
    [(co κ v _) (co κ v σ)]
    [(ap fn args _ κ) (ap fn args σ κ)]
    [(check ℓ+ ℓ- S v _ κ) (check ℓ+ ℓ- S v σ κ)]
    [(ev-syn S ρ _ κ) (ev-syn S ρ σ κ)]
    [(send T ev ℓ η _ κ) (send T ev ℓ η σ κ)]
    [(check-app Svs- fn vs* vs _ κ)
     (check-app Svs- fn vs* vs σ κ)]))

(: Γ : (-> State State))
(define (Γ ς)
  (define-values (root σ) (state-touch ς))
  (define R (reachable root σ))
  (define σ*
    (for/fold ([σ* : Store (hash)])
        ([(a v) (in-hash σ)]
         #:when (set-member? R a))
      (hash-set σ* a (weaken v R))))
  (state-replace-σ ς σ*))

(: value-equal? : (-> Value Value Store Boolean))
(define (value-equal? v0 v1 σ)
  (define A (make-hasheq '()))
  (let rec ([v0 v0] [v1 v1])
    (match* (v0 v1)
      [((boxv v0*) (boxv v1*))
       (define p (cons v0 v1))
       (or (hash-has-key? A p)
           (begin (hash-set! A p #t)
                  (rec (hash-ref σ v0*) (hash-ref σ v1*))))]
      [((cons v0A v0D) (cons v1A v1D))
       (and (rec v0A v1A)
            (rec v0D v1D))]
      [(_ _) (equal? v0 v1)])))

;; Structural contract syntax
(struct --> ([Ss- : (Listof SContract)] [S+ : SContract] [ℓ : Label] [e : Expr]) #:transparent)
(struct cons/c ([A : SContract] [D : SContract]) #:transparent)
(struct any/c () #:transparent) (define -any/c (any/c))
(define-type SContract (U --> cons/c any/c Expr))

;; Evaluated structural contracts
(struct -->/blessed ([Svs- : (Listof SContractv)] [Sv+ : SContractv] [ℓ : Label] [η : timeline]) #:transparent)
(struct cons/blessed ([Av : SContractv] [Dv : SContractv]) #:transparent)
(define-type SContractv (U -->/blessed cons/blessed any/c Procedure-Value))

(: Ssupp : (-> SContract (Setof Symbol)))
(define (Ssupp S)
  (match S
    [(--> Ss- S+ _ e)
     (for/fold ([S* (set-union (Ssupp S+) (supp e))])
         ([S- (in-list Ss-)])
       (set-union S* (Ssupp S-)))]
    [(cons/c A D) (set-union (Ssupp A) (Ssupp D))]
    [(? any/c?) (seteq)]
    [_ (error 'Ssupp "Bad structural contract ~a" S)]))

(: Sfv : (-> SContract (Setof Symbol)))
(define (Sfv S)
  (match S
    [(--> Ss- S+ _ e)
     (for/fold ([S* : (Setof Symbol) (set-union (Sfv S+) (fv e))])
         ([S- : SContract (in-list Ss-)])
       (set-union S* (Sfv S-)))]
    [(cons/c A D) (set-union (Sfv A) (Sfv D))]
    [(? any/c?) ((inst seteq Symbol))]
    [e (fv (cast e Expr))]))

;; Temporal contract syntax
(struct bind ([e : Expr]) #:transparent) ;; Take an event and produce a tcon
(struct kl ([T : Expr]) #:transparent)
(struct · ([T₀ : Expr] [T₁ : Expr]) #:transparent)
(struct ∪ ([T₀ : Expr] [T₁ : Expr]) #:transparent)
(struct ∩ ([T₀ : Expr] [T₁ : Expr]) #:transparent)
(struct ¬ ([T : Expr]) #:transparent)

(struct klv ([T : TCon-Value]) #:transparent)
(struct ·v ([T₀ : TCon-Value] [T₁ : TCon-Value]) #:transparent)
(struct ∪v ([T₀ : TCon-Value] [T₁ : TCon-Value]) #:transparent)
(struct ∩v ([T₀ : TCon-Value] [T₁ : TCon-Value]) #:transparent)
(struct ¬v ([T : TCon-Value]) #:transparent)

(struct ε () #:transparent)
(struct ⊥ () #:transparent)
(struct ⊤ () #:transparent)
;; A value is any of the above except bind, which evaluates bindv.
(struct bindv ([v : Procedure-Value]) #:transparent)

(define -⊤ (⊤))
(define -⊥ (⊥))
(define -ε (ε))
(define -ev-any (let ([x (gensym 'x)]) (lam (list x) #t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; WOOHOO CODE DUPLICATION!!!
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Nullable? decision procedure.
(: ν? : (-> Expr Boolean))
(define/match (ν? T)
  [((∪ T₀ T₁)) (or (ν? T₀) (ν? T₁))]
  [((or (∩ T₀ T₁) (· T₀ T₁))) (and (ν? T₀) (ν? T₁))]
  [((or (? ε?) (? kl?) (? ¬?) (? ⊤?))) #t]
  [(_) #f] ;; ⊥, bind, expression
  )

;; (ν!? T) ⇒ ⟦T⟧ = {ε}
;; Incomplete since μ? is incomplete.
(: ν!? : (-> Expr Boolean))
(define/match (ν!? T)
  [((? ε?)) #t]
  [((kl T)) (ν!? T)] ;; ε* = ε.
  [((¬ T)) (μ? T)] ;; ¬ adds {ε}, but can't get anything else out of T.
  [((or (∪ T₀ T₁) (· T₀ T₁))) (and (ν!? T₀) (ν!? T₁))]
  [((∩ T₀ T₁)) (or (ν!? T₀) (ν!? T₁))]
  [(_) #f]) ;; ⊥ ⊤ bind pred

;; (μ? T) ⇒ ⟦T⟧ = ∅
;; Incomplete decision due to undecidability of infeasibility of matching.
(: μ?  : (-> Expr Boolean))
(define/match (μ? T)
  [((∪ T₀ T₁)) (and (μ? T₀) (μ? T₁))]
  [((∩ T₀ T₁)) (or (μ? T₀) (μ? T₁))]
  ;; denotation of · contains partial traces of T₀ regardless of T₁.
  ;; If T₀ is denotationally {ε}, then we can say the sequence is ⊥ if T₁ is.
  [((· T₀ T₁)) (or (μ? T₀) (and (ν!? T₀) (μ? T₁)))]
  [((? ⊥?)) #t]
  [(_) #f]) ;; (or (? ε?) (? kl?) (? ¬?) (? ⊤?) (? bind?) (? bindv?) expr)

;; Theorem: DNE does not hold. However, ¬^4 = ¬^2.
;; We are /adding/ one ¬, so if at 3, going to 4 is going to 2.
(: mk¬ : (-> Expr Expr))
(define/match (mk¬ T)
  [((¬ (¬ (¬ T)))) (¬ (¬ T))]
  [(T) (¬ T)])

(: mk· : (-> Expr Expr Expr))
(define (mk· T₀ T₁)
  (cond [(μ? T₀) -⊥]
        [(ν!? T₀) T₁]
        [else (· T₀ T₁)]))

(: mk∪ : (-> Expr Expr Expr))
(define (mk∪ T₀ T₁)
  (cond [(equal? T₀ T₁) T₀]
        [(μ? T₀) T₁]
        [(μ? T₁) T₀]
        [else (∪ T₀ T₁)]))

(: mk∩ : (-> Expr Expr Expr))
(define (mk∩ T₀ T₁)
  (cond [(equal? T₀ T₁) T₀]
        [(⊤? T₀) T₁]
        [(⊤? T₁) T₀]
        [else (∩ T₀ T₁)]))

(: mkkl : (-> Expr Expr))
(define (mkkl T)
  (cond [(ν!? T) -ε]
        [(or (kl? T) (⊤? T)) T]
        [else (kl T)]))

;;;;;;;;;;;;;;
;; Value forms

(: ν?v : (-> Value Boolean))
(define/match (ν?v T)
  [((∪v T₀ T₁)) (or (ν?v T₀) (ν?v T₁))]
  [((or (∩v T₀ T₁) (·v T₀ T₁))) (and (ν?v T₀) (ν?v T₁))]
  [((or (? ε?) (? klv?) (? ¬v?) (? ⊤?))) #t]
  [(_) #f] ;; ⊥, bind, expression
  )

;; (ν!? T) ⇒ ⟦T⟧ = {ε}
;; Incomplete since μ? is incomplete.
(: ν!?v : (-> Value Boolean))
(define/match (ν!?v T)
  [((? ε?)) #t]
  [((klv T)) (ν!?v T)] ;; ε* = ε.
  [((¬v T)) (μ?v T)] ;; ¬ adds {ε}, but can't get anything else out of T.
  [((or (∪v T₀ T₁) (·v T₀ T₁))) (and (ν!?v T₀) (ν!?v T₁))]
  [((∩v T₀ T₁)) (or (ν!?v T₀) (ν!?v T₁))]
  [(_) #f]) ;; ⊥ ⊤ bind pred

(: whyν!?v : (-> Value Any))
(define/match (whyν!?v T)
  [((? ε?)) 'ε]
  [((klv T)) `(kl ,(whyν!?v T))] ;; ε* = ε.
  [((¬v T)) `(¬νμ ,(whyμ?v T))] ;; ¬ adds {ε}, but can't get anything else out of T.
  [((∪v T₀ T₁)) `(∪ν ,(whyν!?v T₀) ,(whyν!?v T₁))]
  [((·v T₀ T₁))
   `(·ν ,(whyν!?v T₀) ,(whyν!?v T₁))]
  [((∩v T₀ T₁))
   (if (ν!?v T₀)
       `(∩left ,(whyν!?v T₀) ,T₁)
       `(∩right ,T₀ ,(whyν!?v T₁)))]
  [(_) (error 'whyν!?v "Should never be here ~a" T)])

;; (μ? T) ⇒ ⟦T⟧ = ∅
;; Incomplete decision due to undecidability of infeasibility of matching.
(: μ?v  : (-> Value Boolean))
(define/match (μ?v T)
  [((∪v T₀ T₁)) (and (μ?v T₀) (μ?v T₁))]
  [((∩v T₀ T₁)) (or (μ?v T₀) (μ?v T₁))]
  ;; denotation of · contains partial traces of T₀ regardless of T₁.
  ;; If T₀ is denotationally {ε}, then we can say the sequence is ⊥ if T₁ is.
  [((·v T₀ T₁)) (or (μ?v T₀) (and (ν!?v T₀) (μ?v T₁)))]
  [((? ⊥?)) #t]
  [(_) #f]) ;; (or (? ε?) (? kl?) (? ¬?) (? ⊤?) (? bind?) (? bindv?) expr)

(: whyμ?v : (-> Value Any))
(define/match (whyμ?v T)
  [((∪v T₀ T₁)) `(∪μ ,T₀ ,T₁)]
  [((∩v T₀ T₁)) (if (μ?v T₀)
                    `(∩left ,(whyμ?v T₀) ,T₁)
                    `(∩right ,T₀ ,(whyμ?v T₁)))]
  ;; denotation of · contains partial traces of T₀ regardless of T₁.
  ;; If T₀ is denotationally {ε}, then we can say the sequence is ⊥ if T₁ is.
  [((·v T₀ T₁)) (if (μ?v T₀)
                    `(·left ,(whyμ?v T₀) ,T₁)
                    `(·right ,(whyν!?v T₀)
                             ,(whyμ?v T₁)))]
  [((? ⊥?)) '⊥]
  [(_) (error 'whyμ?v "Should never be here ~a" T)])

;; Theorem: DNE does not hold. However, ¬^4 = ¬^2.
;; We are /adding/ one ¬, so if at 3, going to 4 is going to 2.
(: mk¬v : (-> TCon-Value TCon-Value))
(define/match (mk¬v T)
  [((¬v (¬v (¬v T)))) (¬v (¬v T))]
  [((? ⊥?)) -⊤] ;; ⟦¬ ⊥⟧ = ⟦⊤⟧ since no prefixes to exclude
  [((? ⊤?)) -ε] ;; ⟦¬ ⊤⟧ = {ε} since all non-empty prefixes excluded
  [(T) (¬v T)])

(: mk·v : (-> TCon-Value TCon-Value TCon-Value))
(define (mk·v T₀ T₁)
  (cond [(μ?v T₀) -⊥] ;; Can't sequence anything past failure.
        [(ν!?v T₀) T₁] ;; If T₀ is denotationally ε, then the sequence is just T₁.
        [else (·v T₀ T₁)]))

(: mk∪v : (-> TCon-Value TCon-Value TCon-Value))
(define (mk∪v T₀ T₁)
  (cond [(equal? T₀ T₁) T₀]
        [(μ?v T₀) T₁]
        [(μ?v T₁) T₀]
        [else (∪v T₀ T₁)]))

(: mk∩v : (-> TCon-Value TCon-Value TCon-Value))
(define (mk∩v T₀ T₁)
  (cond [(equal? T₀ T₁) T₀]
        [(⊤? T₀) T₁]
        [(⊤? T₁) T₀]
        [else (∩v T₀ T₁)]))

(: mkklv : (-> TCon-Value TCon-Value))
(define (mkklv T)
  (cond [(ν!?v T) -ε]
        [(or (klv? T) (⊤? T)) T]
        [else (klv T)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Frames
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type Env (HashTable Symbol Any))

;; Evaluation Frames
(struct evk ([es : (Listof Expr)] [vs : (Listof Value)] [ρ : Env]) #:transparent)
(struct ifk ([t : Expr] [e : Expr] [ρ : Env]) #:transparent)
(struct lrk ([x : Symbol] [cs : (Listof (List Symbol Expr))] [body : Expr] [ρ : Env]) #:transparent)

;; Delimiting frames
(struct sk ([+ : Symbol] [- : Symbol] [e : Expr] [ρ : Env]) #:transparent) ;; attaching structural monitor
(struct mkflat () #:transparent) (define -mkflat (mkflat)) ;; to make the typechecker happy

;; Checking frames
(struct ch*k ([Svs- : (Listof SContractv)] [fn : Clo/blessed]
              [vs : (Listof Value)]
              [args : (Listof Value)]) #:transparent)
(struct chret ([fn : Clo/blessed]) #:transparent)
(struct chDk ([ℓ+ : Module] [ℓ- : Module] [D : SContractv] [v : Value]) #:transparent)
(struct consk ([Av : Value]) #:transparent)

(struct checking () #:transparent) (define -checking (checking))

(struct flatk ([v-checked : Value] [flat-fn : Procedure-Value] [ℓ-blame : Module]) #:transparent)
(struct wrapk ([ℓ+ : Module] [ℓ- : Module] [Sv : SContractv]) #:transparent)


;; Messaging frames
(struct sret ([fn : Clo/blessed]) #:transparent)
(struct blret ([ev : ret]) #:transparent)
(struct blcall ([fn : Clo/blessed]
                [vs* : (Listof Value)]
                [ev : call]) #:transparent)

;; Deriving frames
(struct tbin₀ ([C : (-> TCon-Value TCon-Value TCon-Value)]
               [T : TCon-Value]
               [ev : (U call ret)]
               [η : timeline]
               [ℓ- : Module]) #:transparent)
(struct tbin₁ ([C : (-> TCon-Value TCon-Value TCon-Value)] [T : TCon-Value]) #:transparent)
(struct seq2k ([T : TCon-Value]
               [ev : (U call ret)]
               [η : timeline]
               [ℓ- : Module]) #:transparent) ;; evaling (· T₀ T₁) and (ν? T₀)
;; If (· T₀ T₁) and ¬(ν? T₀), then (· ∂_E(T₀) T₁)
;; If (kl T) then (· ∂_E(T) (kl T))
(struct seqk ([T : TCon-Value]) #:transparent)
(struct tunitary ([C : (-> TCon-Value TCon-Value)]) #:transparent)
(define negt (tunitary (λ (T) (if (ν?v T) -⊥ (mk¬v T)))))

;; Making structural contract frames
(struct negk ([Ss- : (Listof SContract)] [S+ : SContract] [ℓ : Label] [e : Expr] [ρ : Env] [Svs- : (Listof SContractv)]) #:transparent) ;; left of ->
(struct mkd ([D : SContract] [ρ : Env]) #:transparent)
(struct mkcons ([A : SContractv]) #:transparent)
(struct timelinek ([rev-Ss- : (Listof SContractv)] [ℓ : Label] [e : Expr] [ρ : Env]) #:transparent)
;; Final frame, so in co, not cos
(struct arrk ([vs : (Listof SContractv)] [v : SContractv] [ℓ : Label]) #:transparent)

;; SCon-Frames are delimited by an sk in the Kont.
(define-type SCon-Frame (U negk mkd mkcons timelinek))

;; Making temporal contract frames
(struct mkt ([T : Expr] [ρ : Env]) #:transparent)
(struct firstT ([v : timeline]) #:transparent)
(struct kunitary ([C : (-> TCon-Value TCon-Value)]) #:transparent)
(struct kbin₀ ([C : (-> TCon-Value TCon-Value TCon-Value)] [T : Expr] [ρ : Env]) #:transparent)
(struct kbin₁ ([C : (-> TCon-Value TCon-Value TCon-Value)] [Tv : TCon-Value]) #:transparent)
(struct clo-to-bind () #:transparent) (define -clo-to-bind (clo-to-bind))
(struct begink ([es : (Listof Expr)] [ρ : Env]) #:transparent)
(define kkl (kunitary mkklv))
(define kneg (kunitary mk¬v))

;; Computed temporal contracts
(struct pred-to-T () #:transparent) (define -pred-to-T (pred-to-T))
(struct mk-tcon () #:transparent) (define -mk-tcon (mk-tcon))

(define-type Deriv-Frame (U tunitary tbin₀ tbin₁ seq2k seqk))
(define-type Check-Frame (U chDk consk))
(define-type Ev-Frame (U evk ifk lrk begink wrapk chret
                         clo-to-bind kunitary mkt firstT kbin₀ kbin₁ ;; making tcons
                         ))

(define-type Frame (U arrk mkflat
                      sk
                      blcall blret
                      mk-tcon pred-to-T
                      flatk
                      sret ch*k checking
                      SCon-Frame Ev-Frame Deriv-Frame Check-Frame))
;; Events
(struct call ([ℓ : Label] [fn : Clo/blessed] [args : (Listof Value)]) #:transparent)
(struct ret ([ℓ : Label] [fn : Clo/blessed] [v : Value]) #:transparent)

(define-type Store (HashTable Any Value))

;; Continuations aren't lists - they bounce back and forth.
(struct scons ([φ : SCon-Frame]
               [κ : SKont]) #:transparent)
(struct econs ([φ : Ev-Frame]
               [κ : EKont]) #:transparent)
(struct tcons ([φ : Deriv-Frame]
               [κ : TKont]) #:transparent)
(struct ccons ([φ : Check-Frame]
               [κ : CKont]) #:transparent)
;; Delimiter continuations
(struct acons ([φ : (U arrk mkflat)] [κ : SKont]) #:transparent) ;; ev-syn -> ev
(struct bcons ([φ : sk] [κ : EKont]) #:transparent) ;; ev -> ev-syn
(struct pcons ([φ : (U mk-tcon pred-to-T)] [κ : TKont]) #:transparent) ;; send -> ev
(struct lcons ([φ : (U blret blcall)] [κ : EKont]) #:transparent) ;; check -> send
(struct vcons ([φ : flatk] [κ : CKont]) #:transparent) ;; check -> ev
(struct hcons ([φ : (U sret ch*k checking)] [κ : EKont]) #:transparent) ;; check -> ev

(define-type SKont (U bcons ;; EKont delimiter
                      scons)) ;; in the middle of construction
(define-type EKont (U Null ;; Done
                      econs ;; in the middle of evalution
                      pcons ;; TKont delimiter
                      acons ;; SKont delimiter
                      vcons)) ;; CKont delimiter
(define-type TKont (U lcons ;; EKont delimiter
                      tcons))
(define-type CKont (U hcons ;; delimiter
                      ccons))
;; sk is the special delimiter
(define-type Kont (U SKont EKont TKont CKont))

(: step-coc : (-> coc State))
(define (step-coc ς)
  (match-define (coc κ* v σ) ς)
  (match κ*
    [(ccons φ κ)
     (match φ
      ;; send the return message with the wrapped return value
      [(chDk ℓ+ ℓ- SDv D) (check ℓ+ ℓ- SDv D σ (ccons (consk v) κ))]
      )]
    [(hcons φ κ)
     (match φ
       [(ch*k Svs- fn vs-to-check vs-checked)
        (check-app Svs- fn vs-to-check (cons v vs-checked) σ κ)]
       [(sret fn)
        (match-define (Clo/blessed ℓ- ℓ+ _ _ ℓ η _) fn)
       (define ev (ret ℓ fn v))
       (define Tv (hash-ref σ η (λ () -⊤)))
       (if (tcon-value? Tv)
           (send Tv ev ℓ+ η σ (lcons (blret ev) κ))
           (error 'step-co "Somehow a timeline mapped to a non-tcon ~a" ς))]
       [(? checking?) (co κ v σ)])]))

(: mk-ensure-tcon : (-> State Value (-> (-> TCon-Value State) State)))
(define (mk-ensure-tcon ς v)
  (λ (f)
     (cond
      [(or (Clo? v) (Clo/blessed? v)) (f (weakly v))]
      [(non-wrap-tcon-value? v) (f v)]
      [else (stuck ς "Expected a temporal contract value")])))

(: step-cod : (-> cod State))
(define (step-cod ς)
  (match-define (cod κ* v σ) ς)
  (define ensure-tcon (mk-ensure-tcon ς v))
  (match κ*
    [(lcons φ κ)
     (match φ
      [(blcall (and (Clo/blessed ℓ- ℓ+ _ Sv+ ℓ η clv) fn) vs* ev)
       ;; Temporal contract has been derived against call message.
       ;; If it's blatantly bad, then blame.
       (define orig (hash-ref σ η (λ () -⊤)))
#;
       (printf "Event ~a at ~a: ~a~%"
               (prettyfy pretty-value ev)
               (prettyfy pretty-value orig)
               (prettyfy pretty-value v))
       (if (μ?v v)
           (tblame ℓ- `((original ,orig)
                        (justification ,(whyμ?v v))) ev)
           ;; call the function with the cleaned values, to check the positive contract afterwards.
           (ap clv vs* (hash-set σ η v) (econs (chret fn) κ)))]
      [(blret ev)
       (match-define (ret _ (Clo/blessed _ ℓ+ _ _ _ η _) rv) ev)
       (define orig (hash-ref σ η (λ () -⊤)))
#;
       (printf "Event ~a at ~a: ~a~%"
               (prettyfy pretty-value ev)
               (prettyfy pretty-value orig)
               (prettyfy pretty-value v))
       ;; Temporal contract has been derived against return message.
       ;; If it's blatantly bad, then blame.
       (if (μ?v v)
           (tblame ℓ+ `((original ,orig)
                        (justification (whyμ?v v))) ev)
           (co κ rv (hash-set σ η v)))])]
    [(tcons φ κ)
     (match φ ;; Derivatives of temporal contracts
       [(tunitary C) (ensure-tcon (λ (v) (cod κ (C v) σ)))]
       ;; Computing ∂_ev(· T₀ T₁), got v = ∂_ev(T₀), and we know ¬ν(T₀)
       [(seqk T₁) (ensure-tcon (λ (v) (cod κ (mk·v v T₁) σ)))]
       ;; Computing ∂_ev(· T₀ T₁), got v = ∂_ev(T₀), and we know ν(T₀), so also compute ∂_ev(T₁)
       [(seq2k T₁ ev η ℓ-)
        ;; v is ∂_ev(T₀) and we need to compute ∂_ev(T₁) to union with v·T₁.
        (ensure-tcon (λ (v) (send T₁ ev ℓ- η σ (tcons (tbin₁ mk∪v (mk·v v T₁)) κ))))]
       [(tbin₀ C Tv ev η ℓ-) (ensure-tcon (λ (v) (send Tv ev ℓ- η σ (tcons (tbin₁ C v) κ))))]
       [(tbin₁ C Tv) (ensure-tcon (λ (v) (cod κ (C Tv v) σ)))])]
    [_ (error 'step-cod "Bad TKont ~a" κ*)]))

;; States
;; Evaluation states
(struct ev ([e : Expr] [ρ : Env] [σ : Store] [κ : EKont]) #:transparent)
(struct ap ([fn : Procedure-Value] [vs : (Listof Value)] [σ : Store] [κ : EKont]) #:transparent)
(struct co ([κ : EKont] [v : Value] [σ : Store]) #:transparent)
;; Structural contract states
(struct ev-syn ([Ssyn : SContract] [ρ : Env] [σ : Store] [κ : SKont]) #:transparent)
(struct cos ([κ : SKont] [v : SContractv] [σ : Store]) #:transparent)
;; Deriving states
(struct cod ([κ : TKont] [v : TCon-Value] [σ : Store]) #:transparent)
(struct send ([T : TCon-Value] [ev : (U call ret)]
              [ℓ : Module]
              [η : timeline] [σ : Store] [κ : TKont]) #:transparent)
;; Checking states
(struct coc ([κ : CKont] [v : Value] [σ : Store]) #:transparent)
(struct check ([ℓ+ : Module] [ℓ- : Module] [S : SContractv] [v : Value] [σ : Store] [κ : CKont]) #:transparent)
(struct check-app ([Svs- : (Listof SContractv)]
                   [fn : Clo/blessed]
                   [vs-to-check : (Listof Value)]
                   [vs-checked : (Listof Value)]
                   [σ : Store] [κ : EKont]) #:transparent)

(define-type State (U ev co check check-app ap ev-syn send cos cod coc
                      stuck blame tblame ans))

;; Final states
(struct ans ([v : Value] [σ : Store]) #:transparent)
(struct stuck ([state : State] [msg : String]) #:transparent)
(struct blame ([ℓ : Module] [S : SContractv] [v : Value]) #:transparent)
(struct tblame ([ℓ : Label] [T : Any] [ev : (U call ret)]) #:transparent)

(: alloc : (-> State (U Symbol String) Any))
(define (alloc ς tag) (gensym tag))

(define prim-symbols
  (make-immutable-hash (list (cons '_ -ev-any)
                             (cons '⊤ -⊤)
                             (cons '... -⊤)
                             (cons '⊥ -⊥)
                             (cons 'ε -ε))))
(define nullary-prims '(new-timeline))
(define unary-prims ;; predicates and projections
  '(pair? car cdr null?
    not
    box? make-box unbox
    display
    call? call-label call-fn call-args
    ret? ret-fn ret-label ret-value
    boolean? number? real?))
(define binary-prims '(cons equal? set-box! <=))
(define prims (append nullary-prims unary-prims binary-prims))
(: unary-primop? : (-> Any Boolean : #:+ primop))
(define (unary-primop? v)
  (and (primop? v)
       (memq (primop-which v) unary-prims)
       #t))

(define-predicate procedure-value? Procedure-Value)

(: unweaken : (-> (Listof Value) (Listof Value)))
(define (unweaken vs)
  (map (λ ([v : Value]) (if (weak? v) (weak-v v) v)) vs))

(: ev-δ : (-> State Symbol (Listof Value) Store EKont State))
(define (ev-δ ς which args σ κ)
  (define (arity num) (format "Primitive expected ~a args, got ~a" num (length args)))
  (: bad : (-> String stuck))
  (define (bad msg) (stuck ς msg))
  (: arity-mismatch : (-> Number (U #f stuck)))
  (define (arity-mismatch num)
    (if (= num (length args))
        #f
        (bad (arity num))))
  (define (bad-preds preds)
    (format "Primitive expected arguments to match ~a, got ~a" preds args))
  (: go : (-> Value State))
  (define (go v) (co κ v σ))
  (define args* (unweaken args))
  (: f-project : (All (A) (-> (-> Any Boolean : A) (-> A Value) State)))
  (define (f-project pred proj)
    (if (and (pair? args*) (null? (cdr args*)))
        (let* ([v (car (cast args* (Pairof Any Any)))])
          (cond [(pred v) (go (proj v))]
                [(undefined? v) (go -undefined)]
                [else (bad (bad-preds (list pred)))]))
        (bad (arity 1))))
  (match which
    ['cons (or (arity-mismatch 2) (go (cons (first args*) (second args*))))]
    ['not (or (arity-mismatch 1) (go (not (first args*))))]
    ['display
     (display "Display: ") (for-each display args*) (newline)
     (go (void))]
    ['pair? (or (arity-mismatch 1)
                (go (pair? (first args*))))]
    ['car (if (and (pair? args*) (null? (cdr args*)) (pair? (car args*)))
              (go (car (car args*)))
              (bad (bad-preds (list pair?))))]
    ['cdr (if (and (pair? args*) (null? (cdr args*)) (pair? (car args*)))
              (go (cdr (car args*)))
              (bad (bad-preds (list pair?))))]
    ['null? (or (arity-mismatch 1)
                (go (null? (first args*))))]
    ['new-timeline (or (arity-mismatch 0)
                       (go (timeline (alloc ς 'new-timeline))))]

    ['call? (or (arity-mismatch 1)
                (go (call? (first args*))))]
    ['call-label (f-project call? call-ℓ)]
    ['call-fn (f-project call? call-fn)]
    ['call-args (f-project call? call-args)]

    ['ret? (or (arity-mismatch 1)
               (go (ret? (first args*))))]
    ['ret-fn (f-project ret? ret-fn)]
    ['ret-label (f-project ret? ret-ℓ)]
    ['ret-value (f-project ret? ret-v)]

    ['boolean? (or (arity-mismatch 1) (go (boolean? (first args*))))]
    ['number? (or (arity-mismatch 1) (go (number? (first args*))))]
    ['real? (or (arity-mismatch 1) (go (real? (first args*))))]

    ['box? (or (arity-mismatch 1) (go (boxv? (first args*))))]
    ['make-box (or (arity-mismatch 1)
                   (let ([a (alloc ς 'make-box)])
                     (co κ (boxv a) (hash-set σ a (first args*)))))]
    ['unbox (or (arity-mismatch 1)
                (match (first args*)
                  [(boxv a) (go (hash-ref σ a))]
                  [(? undefined?) (go -undefined)]
                  [f (bad (format "unbox expects a box, got ~a" f))]))]
    ['set-box! (match args*
                 [(list b v)
                  (match b
                    [(? undefined?) (co κ (void) σ)]
                    [(boxv a) (co κ (void) (hash-set σ a v))]
                    [_ (bad (format "set-box! expects a box as the first argument, got ~a" b))])]
                 [_ (bad (arity 2))])]

    ['<= (if (pair? args*)
             (let ([d (cdr args*)])
               (if (pair? d)
                   (let ([dd (cdr d)])
                     (if (null? dd)
                         (let ([a (car args*)]
                               [ad (car d)])
                           (if (and (real? a) (real? ad))
                               (go (<= a ad))
                               (bad (bad-preds (list real? real?)))))
                         (bad (arity 2))))
                   (bad (arity 2))))
             (bad (arity 2)))]

    ['equal? (or (arity-mismatch 2)
                 (let* ([v0 (first args*)]
                        [v1 (second args*)]
                        [ans (and (not (or (undefined? v0) (undefined? v1)))
                                  (value-equal? v0 v1 σ))])
#;
                   (printf "Checking equality of ~a, ~a: ~a~%"
                           (prettyfy pretty-value v0)
                           (prettyfy pretty-value v1)
                           ans)                   
                   ;; Like NaN, undefined is not equal to itself
                   (go ans)))]))

(: restrict-to-fv : (-> Expr Env Env))
(define (restrict-to-fv e ρ)
  (define dom (fv e))
  (for/hash : Env ([(x a) (in-hash ρ)]
                  #:when (set-member? dom x))
    (values x a)))

(: step-ev : (-> ev State))
(define/match (step-ev ς)
  [((ev e ρ σ κ))
   (match e
     [(app e0 es) (ev e0 ρ σ (econs (evk es '() ρ) κ))]
     [(lam xs e) (co κ (Clo xs e (restrict-to-fv e ρ)) σ)]
     [(ref x)
      (define a/undefined (hash-ref ρ x))
      (if (undefined? a/undefined)
          (co κ a/undefined σ)
          (co κ (hash-ref σ a/undefined) σ))]
     [(smon + - Ssyn e) (ev-syn Ssyn ρ σ (bcons (sk + - e ρ) κ))]
     [(tmon ηe T) (ev ηe ρ σ (econs (mkt T ρ) κ))]
     [(ife gu th el) (ev gu ρ σ (econs (ifk th el ρ) κ))]

     [(letrece cs body)
      (match cs
        ;; (letrec () e) = e
        ['() (ev body ρ σ κ)]
        ;; Initialize boxes, evaluate first clause.
        [(cons (list x e) cs*)
         (define-values (σ* ρ*)
           (for/fold ([σ* : Store σ] [ρ* : Env ρ]) ([xe (in-list cs)])
               (match-define (list x e) xe)
               (define a (alloc ς x))
               (values (hash-set σ* a -undefined)
                       (hash-set ρ* x a))))
         (ev e ρ* σ* (econs (lrk x cs* body ρ*) κ))])
      ]
     [(begine (cons e es)) (ev e ρ σ (econs (begink es ρ) κ))]
     [(or (? primop?) (? datum?)) (co κ (cast e Value) σ)] ;; e is its own value

     ;; atomic contracts that are their own value
     [(or (? ⊤?) (? ⊥?) (? ε?))
      (co κ (cast e TCon-Value) σ)]
     [(bind e) (ev e ρ σ (econs -clo-to-bind κ))]
     [(kl T) (ev T ρ σ (econs kkl κ))]
     [(¬ T) (ev T ρ σ (econs kneg κ))]
     [(· T₀ T₁) (ev T₀ ρ σ (econs (kbin₀ mk·v T₁ ρ) κ))]
     [(∪ T₀ T₁) (ev T₀ ρ σ (econs (kbin₀ mk∪v T₁ ρ) κ))]
     [(∩ T₀ T₁) (ev T₀ ρ σ (econs (kbin₀ mk∩v T₁ ρ) κ))]
     [_ (error 'step-ev "Bad expression ~a" e)])])

(: singleton-lst? : (-> (Listof Any) Boolean))
(define (singleton-lst? xs) (and (pair? xs) (null? (cdr xs))))

(: unary? : (-> Value Boolean))
(define (unary? v)
  (cond [(Clo? v) (singleton-lst? (Clo-xs v))]
        [(Clo/blessed? v) (singleton-lst? (Clo/blessed-Svs- v))]
        ;; primops can't produce temporal contracts, so reject.
        [else #f]))

(: step-co : (-> co State))
(define (step-co ς)
  (match-define (co κ* v σ) ς)
  (define ensure-tcon (mk-ensure-tcon ς v))
  (match κ*
   ['() (ans v σ)]
   [(acons φ κ) ;; co --> cos
    (match φ
      [(arrk Svs- Sv+ ℓ)
       (if (timeline? v)
           ;; arrk is always on top of an SCon-Frame
           (cos κ (-->/blessed (reverse Svs-) Sv+ ℓ v) σ)
           (stuck ς "--> contract requires a timeline."))]
      [(? mkflat?)
       (if (procedure-value? v)
           (cos κ v σ)
           (stuck ς "Non-procedure cannot be a structural contract"))])]
   [(pcons φ κ) ;; co -> cod
    (match φ
      [(mk-tcon) (ensure-tcon (λ (v) (cod κ v σ)))]
      [(pred-to-T) (cod κ (if v -ε -⊥) σ)])]
   [(vcons (flatk v-checked fn ℓ-) κ) ;; co -> check
    (if v
        (coc κ v-checked σ)
        (blame ℓ- fn (format "Flat contract failed on ~a" v-checked)))]
   [(econs φ κ)
    (match φ
      ;; Evaluating
      [(evk '() vs ρ)
       (match-define (cons v0 vs*) (reverse (cons v vs)))
       (if (procedure-value? v0)
           (ap v0 vs* σ κ)
           (stuck ς "Expected a procedure value in applied position"))]

      [(evk (cons e0 es) vs ρ)
       (ev e0 ρ σ (econs (evk es (cons v vs) ρ) κ))]

      [(ifk th el ρ) (ev (if v th el) ρ σ κ)]

      [(lrk x cs body ρ)
       (define σ* (hash-set σ (hash-ref ρ x) v))
       (match cs
         ['() (ev body ρ σ* κ)]
         [(cons (list y e*) cs*)
          (ev e* ρ σ* (econs (lrk y cs* body ρ) κ))])]

      ;; Constructing temporal contracts
      [(clo-to-bind)
       (define (bad) (stuck ς "Bind expects a unary function"))
       (cond [(or (Clo? v) (Clo/blessed? v))
              (if (unary? v)
                  (co κ (bindv (weakly v)) σ)
                  (bad))]
             [(weakly? v)
              (if (unary? (weakly-v v))
                  (co κ (bindv v) σ)
                  (bad))]
             [else (bad)])]
      [(mkt T ρ)
       (if (timeline? v)
           (ev T ρ σ (econs (firstT v) κ))
           (stuck ς "tmon expects a timeline object"))]
      [(firstT η) (ensure-tcon (λ (v)
#;
                                  (printf "Initial ~a: ~a~%"
                                          (prettyfy pretty-value η)
                                          (prettyfy pretty-value v))
                                  (co κ (void) (hash-set σ η v))))]
      [(kunitary C) (ensure-tcon (λ (v) (co κ (C v) σ)))]
      [(kbin₀ C T ρ) (ensure-tcon (λ (v) (ev T ρ σ (econs (kbin₁ C v) κ))))]
      [(kbin₁ C Tv) (ensure-tcon (λ (v) (co κ (C Tv v) σ)))]

      ;; Run in context of a temporal contract
      [(begink es ρ)
       (match es
         ['() (co κ v σ)]
         [(cons e es) (ev e ρ σ (econs (begink es ρ) κ))])]

      ;; Messaging
      [(chret (and (Clo/blessed ℓ- ℓ+ _ Sv+ _ η _) fn))
       ;; check return value first, then send message to timeline.
       (check ℓ+ ℓ- Sv+ v σ (hcons (sret fn) κ))] ;; blame or do call

      ;; Constructing the whole smon contract requires checking upfront.
      [(wrapk ℓ+ ℓ- Sv)
       (check ℓ+ ℓ- Sv v σ (hcons -checking κ))]
      [(consk Av) (co κ (cons Av v) σ)]

      [_ (error 'step-co "Bad frame ~a" φ)])]
   [_ (error 'step-co "Bad EKont ~a" κ*)]))

(: step-cos : (-> cos State))
(define (step-cos ς)
  (match-define (cos κ* Sv σ) ς)
  (match κ*
    [(bcons (sk + - e ρ) κ) ;; κ is an EKont
     (ev e ρ σ (econs (wrapk + - Sv) κ))]
    [(scons φ κ)
     (match φ
       ;; Constructing structural contracts
       [(timelinek Svs ℓ e ρ)
        (ev e ρ σ (acons (arrk Svs Sv ℓ) κ))]

       [(negk '() S+ ℓ e ρ Svs-)
        (ev-syn S+ ρ σ (scons (timelinek (cons Sv Svs-) ℓ e ρ) κ))]

       [(negk (cons S- Ss-) S+ ℓ e ρ Svs-)
        (ev-syn S- ρ σ (scons (negk Ss- S+ ℓ e ρ (cons Sv Svs-)) κ))]
       [(mkd D ρ) (ev-syn D ρ σ (scons (mkcons Sv) κ))]
       [(mkcons A) (cos κ (cons/blessed A Sv) σ)]
       [_ (error 'step-cos "Bad frame ~a" φ)])]))

(: step-ap : (-> ap State))
(define/match (step-ap ς)
  [((ap fn vs σ κ))
   (: app : (-> (Listof Symbol) Expr Env (Listof Value) State))
   (define (app xs e ρ vs)
     (let bind ([xs xs] [vs vs] [ρ ρ] [σ σ])
       (match* (xs vs)
         [('() '()) (ev e ρ σ κ)]
         [((cons x xs) (cons v vs))
          (define a (alloc ς x))
          (bind xs vs (hash-set ρ x a) (hash-set σ a v))]
         [(_ _) (stuck ς "Arity mismatch for function application")])))
   (: wrap : (-> Value (Listof Value) State))
   (define (wrap fn vs)
     (match fn
       [(Clo xs e ρ) (app xs e ρ vs)]
       [(Clo/blessed ℓ- ℓ+ Svs- Sv+ ℓ η clv)
        (check-app Svs- fn vs '() σ κ)]
       [(primop which) (ev-δ ς which vs σ κ)]))
   (match fn
     [(weakly clv) (wrap clv (map weak vs))]
     [clv (wrap clv vs)])])

(: step-ev-syn (-> ev-syn State))
(define/match (step-ev-syn ς)
  [((ev-syn S ρ σ κ))
   (match S
     [(--> '() S+ ℓ e) (ev-syn S+ ρ σ (scons (timelinek '() ℓ e ρ) κ))]
     [(--> (cons S- Ss-) S+ ℓ e)
      (ev-syn S- ρ σ (scons (negk Ss- S+ ℓ e ρ '()) κ))]

     [(cons/c A D)
      (ev-syn A ρ σ (scons (mkd D ρ) κ))]

     ;; only unary functions are contracts
     [(and (or (? unary-primop?)
               (? any/c?))
           Sv)
      (cos κ Sv σ)]

     ;; Must delimit κ to show that e is evaluated in an SKont context
     [e (ev (cast e Expr) ρ σ (acons -mkflat κ))])])

;; Derivatives!
(: step-send : (-> send State))
(define/match (step-send ς)
  [((send T ev ℓ- η σ κ))
   (match T
     [(or (? ε?) #;(? ev-none?) (? ⊥?)
          )
      (cod κ -⊥ σ)]
     [(? ⊤?) (cod κ -⊤ σ)] ;; ??

     [(bindv v) (ap v (list ev) σ (pcons -mk-tcon κ))]
     [(klv T*) (send T* ev ℓ- η σ (tcons (seqk T) κ))]
     [(¬v T*) (send T* ev ℓ- η σ (tcons negt κ))]
     [(·v T₀ T₁) (send T₀ ev ℓ- η σ (tcons (if (ν?v T₀) (seq2k T₁ ev η ℓ-) (seqk T₁)) κ))]
     [(∪v T₀ T₁) (send T₀ ev ℓ- η σ (tcons (tbin₀ mk∪v T₁ ev η ℓ-) κ))]
     [(∩v T₀ T₁) (send T₀ ev ℓ- η σ (tcons (tbin₀ mk∩v T₁ ev η ℓ-) κ))]
     [(? procedure-value? v) (ap v (list ev) σ (pcons -pred-to-T κ))]
     [_ (error 'step-send "Unhandled temporal contract ~a" T)])])

(: step-check-app : (-> check-app State))
(define/match (step-check-app ς)
  [((check-app Svs- fn vs-to-check vs-checked σ κ))
   (match* (Svs- vs-to-check)
     [('() '())
      (match-define (Clo/blessed ℓ- ℓ+ _ Sv+ ℓ η clv) fn)
      (define args-checked (reverse vs-checked))
      (define ev (call ℓ fn args-checked))
      (define Tv (hash-ref σ η (λ () -⊤)))
      (if (tcon-value? Tv)
          (send Tv ev ℓ- η σ (lcons (blcall fn args-checked ev) κ))
          (error 'step-check-app "Somehow timeline maps to non-tcon-value ~a" ς))]
     [((cons Sv- Svs-*) (cons v1 vs-to-check*))
      (match-define (Clo/blessed ℓ- ℓ+ _ _ _ _ _) fn)
      (check ℓ- ℓ+ Sv- v1 σ (hcons (ch*k Svs-* fn vs-to-check* vs-checked) κ))]
     [(_ _) (stuck ς "Arity mismatch for blessed application")])])

(: step-check : (-> check State))
(define/match (step-check ς)
  [((check ℓ+ ℓ- S v σ κ))
   (cond [(-->/blessed? S)
          (match-define (-->/blessed Svs- Sv+ ℓ η) S)
          (match v
            [(or (Clo args _ _) (Clo/blessed _ _ args _ _ _ _))
             #:when (= (length (cast args (Listof Any))) (length Svs-))
             (coc κ (Clo/blessed ℓ- ℓ+ Svs- Sv+ ℓ η v) σ)]
            [_  (blame ℓ S v)])]
         [(cons/blessed? S)
          (match-define (cons/blessed Av Dv) S)
          (match v
            [(cons A D)
             (check ℓ+ ℓ- Av A σ (ccons (chDk ℓ+ ℓ- Dv D) κ))]
            [_ (blame ℓ+ S v)])]
         [(any/c? S) (coc κ v σ)]
         [else (ap S (list v) σ (vcons (flatk v S ℓ-) κ))])])

(: step : (-> State State))
(define (step ς)
  (cond [(ev? ς) (step-ev ς)]
        [(co? ς) (step-co ς)]
        [(ap? ς) (step-ap ς)]
        [(check? ς) (step-check ς)]
        [(ev-syn? ς) (step-ev-syn ς)]
        [(cos? ς) (step-cos ς)]
        [(cod? ς) (step-cod ς)]
        [(coc? ς) (step-coc ς)]
        [(check-app? ς) (step-check-app ς)]
        [(send? ς) (step-send ς)]
        [else (error 'step "Unknown state ~a" ς)]))

(: run : (-> State State))
(define (run ς)
  (if (or (ans? ς) (blame? ς) (tblame? ς) (stuck? ς))
      ς
      (run (step ς))))
#|
(: symbol-append-number : (-> Symbol Exact-Nonnegative-Integer Symbol))
(define (symbol-append-number s n)
  (string->symbol (string-append (symbol->string s) (number->string n))))

(: fresh : (->* (Symbol (Setof Symbol)) (Exact-Nonnegative-Integer) Symbol))
(define (fresh base not-in [tail 0])
  (if (set-member? not-in base)
      (fresh (symbol-append-number base tail) not-in (add1 tail))
      base))
|#

(define-type Renaming (HashTable Symbol Symbol))
(: parse : (->* (Any) [Renaming] Expr))
(define (parse sexp [ρ ((inst hasheq Symbol Symbol))])
  (define (p* sexp) (parse sexp ρ))
  (: is-app : (->* () ((Listof Any)) Expr))
  (define (is-app [sexp (cast sexp (Listof Any))])
    (app (p* (first sexp)) (map p* (rest sexp))))
  (: if-builtin : (-> Symbol (-> Expr) Expr))
  (define (if-builtin name f)
    (if (hash-has-key? ρ name) (is-app) (f)))
  (: defn-ctx : (-> (Listof Any) Renaming Expr))
  (define (defn-ctx sexps ρ)
    (unless (pair? sexps) (error 'defn-ctx "Expected at least one expression"))
    (define ρ*
      (for/fold ([ρ* : Renaming ρ]) ([s (in-list sexps)])
        (match s
          [`(define ,(? symbol? name) ,rhs)
           (if (hash-has-key? ρ* 'define)
               ρ*
               (hash-set ρ* name (gensym name)))]
          [`(define (,(? symbol? name) ,(? symbol? args) ...) ,rhs ...)
           (if (hash-has-key? ρ* 'define)
               ρ*
               (hash-set ρ* name (gensym name)))]
          [`(define . ,rest)
           (if (hash-has-key? ρ* 'define)
               ρ*
               (error 'defn-ctx "Ill-formed define form"))]
          [_ ρ*])))
    (: loop : (-> (Listof Any)
                  (Listof (List Symbol Expr))
                  (Listof Expr)
                  Boolean Expr))
    (define (loop ss rev-clauses since-last-define redefined?)
      (define (finish e)
        (*letrece (reverse rev-clauses)
                  (begine (cast (append (reverse since-last-define)
                                        (list (parse e ρ*)))
                                (Pairof Expr (Listof Expr))))))
      (match ss
        [(list (and e `(define ,x ,r)))
         (if redefined?
             (finish e)
             (error 'defn-ctx "Expected last form to be an expression, not a definition: ~a" e))]
        [(list e) (finish e)]
        [(cons s ss)
         (define (expr)
           (loop ss
                 rev-clauses
                 (cons (parse s ρ*) since-last-define)
                 redefined?))
         (match s
           [`(define ,x ,r)
            (cond
             [redefined? (expr)]
             [else
              (: name : Symbol)
              (: rhs : Expr)
              (define-values (name rhs)
                (cond
                 [(symbol? x) (values (hash-ref ρ* x) (parse r ρ*))]
                 [else
                  (match-define (cons name formals) x)
                  (define name* (cast name Symbol))
                  (define formals* (cast formals (Listof Symbol)))
                  (: xs* : (Listof Symbol))
                  (define xs* ((inst map Symbol Symbol)
                               gensym
                               formals*))
                  (define ρ** (hash-set-many ρ* formals* xs*))
                  (values (hash-ref ρ* name*) (lam xs* (parse r ρ**)))]))
              (loop ss
                    (cons (list name rhs)
                          (append (map (λ ([e : Expr]) (list (gensym 'dummy) e)) since-last-define)
                                  rev-clauses))
                    '()
                    (eq? name 'define))])]
           [_ (expr)])]))
    (loop sexps '() '() (hash-has-key? ρ 'define)))
  (match sexp
    ;; other symbols
    [(? symbol? x)
     (define x* (hash-ref ρ x (λ () x)))
     (if (memq x* prims)
         (primop x*)
         (hash-ref prim-symbols x* (λ () (ref x*))))]
    [`(,(and head (or 'λ 'lambda)) (,(? symbol? xs) ...) ,body ...)
     (if-builtin head
                 (λ ()
                    (define xs0 (cast xs (Listof Symbol)))
                    (define xs* ((inst map Symbol Symbol) gensym
                                 xs0))
                    (define ρ* (hash-set-many ρ xs0 xs*))
                    (lam xs* (defn-ctx body ρ*))))]
    [`(letrec ([,(? symbol? xs) ,es] ...) ,body ...)
     (if-builtin 'letrec
                 (λ ()
                    (define xs0 (cast xs (Listof Symbol)))
                    (define xs* ((inst map Symbol Symbol) gensym xs0))
                    (define ρ* (hash-set-many ρ xs0 xs*))
                    (*letrece (for/list ([x (in-list xs*)] [e (in-list es)])
                                (list x (parse e ρ*)))
                              (defn-ctx body ρ*))))]
    [`(smon ',(? symbol? +) ',(? symbol? -) ,S ,e)
     (if-builtin 'smon
                 (λ () (smon + - (parse-scon S ρ) (p* e))))]
    [`(tmon ,ηe ,T)
     (if-builtin 'tmon
                 (λ () (tmon (p* ηe) (p* T))))]
    [`(if ,g ,t ,e)
     (if-builtin 'if
                 (λ () (ife (p* g) (p* t) (p* e))))]
    [`(begin ,e ,es ...)
     (if-builtin 'begin (λ () (begine (cons (p* e) (map p* es)))))]

    ;; temporal contracts are expressions too, since bind produces tcons
    [`(* ,T) (if-builtin '* (λ () (kl (p* T))))]
    [`(∪ ,T ...) (if-builtin '∪ (λ () (rassoc mk∪ -⊥ (map p* T))))]
    [`(∩ ,T ...) (if-builtin '∩ (λ () (rassoc mk∩ -⊤ (map p* T))))]
    [`(· ,T ...) (if-builtin '· (λ () (rassoc mk· -ε (map p* T))))]
    [`(¬ ,T) (if-builtin '¬ (λ () (mk¬ (p* T))))]
    [`(bind ,e) (if-builtin 'bind (λ () (bind (p* e))))]

    ;; macros
    [`(let ([,(? symbol? xs) ,es] ...) ,body ...)
     (if-builtin 'let
                 (λ () (p* `((λ ,xs . ,body) . ,es))))]
    [`(or ,e ...)
     (if-builtin 'or (λ ()
                        (let rec : Expr ([es : (Listof Any) e])
                             (match es
                               ['() #f]
                               [(list e) (p* e)]
                               [(cons e rest)
                                ;; (let ([t e]) (if t t (or . rest)))
                                (define t (gensym 'tmp))
                                (app (lam (list t)
                                          (ife (ref t) (ref t) (rec rest)))
                                     (list (p* e)))]))))]
    [`(and ,e ...)
     (if-builtin 'and (λ ()
                         (let rec : Expr ([es : (Listof Any) e])
                              (match es
                                ['() #t]
                                [(list e) (p* e)]
                                [(cons e rest) (ife (p* e) (rec rest) #f)]))))]
    [`(cond [,gs ,rhss ...] ... [else ,last ...])
     (if-builtin 'cond
                 (λ ()
                    (let rec : Expr
                         ([gs : (Listof Any) gs]
                          [rhss : (Listof (Listof Any)) (cast rhss (Listof (Listof Any)))])
                         (match* (gs rhss)
                           [('() '())
                            (defn-ctx last ρ)]
                           [((cons g gs) (cons rhs rhss))
                            (ife (p* g)
                                 (defn-ctx rhs ρ)
                                 (rec gs rhss))]))))]

    ;; back to expressions

    [`(quote ,(? datum? d)) (if-builtin 'quote (λ () d))]
    ;; fall-through application
    [`(,e . ,es) (is-app)]
    [(? datum? sexp) sexp]
    [_ (error 'parse "Bad expression ~a" sexp)]))

(: parse-scon : (-> Any Renaming SContract))
(define (parse-scon S ρ)
  (define (parse-scon* S) (parse-scon S ρ))
  (match S
    [`(-> ,S- ... ,S+ : ',(? symbol? ℓ) @ ,e)
     (if (hash-has-key? ρ '->)
         (parse S ρ)
         (--> (map parse-scon* S-)
              (parse-scon* S+)
              ℓ
              (parse e ρ)))]
    [`(cons/c ,A ,D)
     (if (hash-has-key? ρ 'cons/c)
         (parse S ρ)
         (cons/c (parse-scon* A) (parse-scon* D)))]
    [(and (or 'any 'any/c) S)
     (if (hash-has-key? ρ S)
         (ref (hash-ref ρ S))
         -any/c)]
    [e (parse e ρ)]))

(: unparse : (-> Expr Any))
(define (unparse e)
  (match e
    [(app e es) (cons (unparse e) (map unparse es))]
    [(ref x) x]
    [(lam xs e) `(λ ,xs ,(unparse e))]
    [(smon + - S e) `(smon ,+ ,- ,(unparse-scon S) ,(unparse e))]
    [(tmon ηe T) `(tmon ,(unparse ηe) ,(unparse T))]
    [(ife g t e) `(if ,(unparse g) ,(unparse t) ,(unparse e))]
    [(letrece cs e) `(letrec ,(map (λ ([c : (List Symbol Expr)])
                                      (list (car c) (unparse (cadr c))))
                                   cs)
                       ,(unparse e))]
    [(begine es) `(begin . ,(map unparse es))]
    [(primop which) which]
    [(? datum?) e]
    
    [(? ∩? T) `(∩ . ,(map unparse (flatten-pair ∩? ∩-T₀ ∩-T₁ T)))]
    [(? ∪? T) `(∪ . ,(map unparse (flatten-pair ∪? ∪-T₀ ∪-T₁ T)))]
    [(? ·? T) `(· . ,(map unparse (flatten-pair ·? ·-T₀ ·-T₁ T)))]
    [(¬ T) `(¬ ,(unparse T))]
    [(kl T) `(* ,(unparse T))]
    [(bind e) `(bind ,(unparse e))]
    [(ε) 'ε]
    [(⊤) '...]
    [(⊥) '⊥]

    [_ (error 'unparse "Bad expression ~a" e)]))

(: unparse-scon : (-> SContract Any))
(define (unparse-scon S)
  (match S
    [(--> Ss- S+ ℓ e)
     `(--> ,(map unparse-scon Ss-) ,(unparse-scon S+) ,ℓ ,(unparse e))]
    [(cons/c A D) `(cons/c ,(unparse-scon A) ,(unparse-scon D))]
    [(? any/c?) `any/c]
    [_ (error 'unparse-scon "Bad structural contract ~a" S)]))

(: prettyfy : (All (A) (-> (-> A Any) A String)))
(define (prettyfy f v) (with-output-to-string (λ () (pretty-write (f v)))))

(: pretty-env : (-> Env Any))
(define (pretty-env ρ)
  (for/list : (Listof Any) ([(x a) (in-hash ρ)])
    (list x '↦ a)))

(: flatten-pair : (All (A B) (-> (-> Any Boolean : A)
                               (-> A B)
                               (-> A B)
                               B
                               (Listof B))))
(define (flatten-pair p π₀ π₁ v)
  (let rec : (Listof B) ([v : B v])
       (cond [(p v) (append (rec (π₀ v)) (rec (π₁ v)))]
             [else (list v)])))

(: pretty-value : (-> Value Any))
(define (pretty-value v)
  (match v
   [(Clo xs e ρ)
    (if (= 0 (hash-count ρ))
        `(top-fun ,(unparse (lam xs e)))
        `(closure ,(unparse (lam xs e)) ,(pretty-env ρ)))]
   [(timeline a) `(timeline ,a)]
   [(boxv a) `(box @ ,a)]
   [(Clo/blessed ℓ- ℓ+ Svs- Sv+ ℓ η clv)
    `(blessed (- ,ℓ-) (+ ,ℓ+)
              ,(pretty-sconv (-->/blessed Svs- Sv+ ℓ η))
              ,(pretty-value clv))]
   [(cons A D) (cons (pretty-value A) (pretty-value D))]

   [(call ℓ fn args) `(call ,ℓ ,(pretty-value fn) ,(map pretty-value args))]
   [(ret ℓ fn v) `(ret ,ℓ ,(pretty-value fn) ,(pretty-value v))]

   [(klv Tv) `(* ,(pretty-value Tv))]
   [(¬v Tv) `(¬ ,(pretty-value Tv))]
   [(bindv Tv) `(bind ,(pretty-value Tv))]
   [(? ∪v? Tv)
    `(∪ . ,(map pretty-value (flatten-pair ∪v? ∪v-T₀ ∪v-T₁ Tv)))]
   [(? ∩v? Tv)
    `(∩ . ,(map pretty-value (flatten-pair ∩v? ∩v-T₀ ∩v-T₁ Tv)))]
   [(? ·v? Tv)
    `(· . ,(map pretty-value (flatten-pair ·v? ·v-T₀ ·v-T₁ Tv)))]

   [(primop which) which]
   [(weak v) `(weak ,(pretty-value v))]
   [(weakly v) `(weakly ,(pretty-value v))]

   [(⊤) '...]
   [(⊥) '⊥]
   [(ε) 'ε]

   [_ v]))

(: pretty-sconv : (-> SContractv Any))
(define/match (pretty-sconv Sv)
  [((-->/blessed Svs- Sv+ ℓ η))
   `(-->/blessed ,(map pretty-sconv Svs-) ,(pretty-sconv Sv+) ,ℓ ,(pretty-value η))]
  [((cons/blessed Av Dv)) `(cons/c ,(pretty-sconv Av) ,(pretty-sconv Dv))]
  [((? any/c?)) 'any/c]
  [(v) (pretty-value (cast v Value))])

(define ex-common
  '((define narf (make-box #f))
    (define (insert cmp)
      (λ (a lst)
         (set-box! narf cmp)
         (cond [(null? lst) (cons a '())]
               [else
                (define l0 (car lst))
                (if (cmp a l0)
                    (cons a lst)
                    (cons l0 ((insert cmp) a (cdr lst))))])))
    (define (foldl f b lst)
      (if (pair? lst)
          (foldl f (f (car lst) b) (cdr lst))
          b))
    (define (sort cmp lst)
      (foldl (insert cmp) '() lst))
    (define (listof f)
      (λ (lst)
         (if (pair? lst)
             (and (f (car lst)) ((listof f) (cdr lst)))
             (null? lst))))
    (define η (new-timeline))
    (define csort
      (smon 'user 'context
            (->
             (-> real? real? boolean? : 'cmp @ η)
             (listof real?)
             any
             : 'sort @ η)
            sort))
    (define lst (cons 1 (cons 2 (cons 3 (cons 4 '())))))
    (define call-sort
      (λ (ev) (and (call? ev) (equal? 'sort (call-label ev)))))
    (define ret-sort
      (λ (ev) (and (ret? ev) (equal? 'sort (ret-label ev)))))
    (define not-ret-sort (λ (ev) (not (ret-sort ev))))
    (csort (λ (x y) (<= x y)) lst)))

(define example
  `(let ()
     ,@ex-common
     (begin
       (tmon η
            (∩ (¬ (· ...
                     ;; (call 'sort _)
                     call-sort
                     ;; (* (! (ret 'sort _)))
                     (* not-ret-sort)
                     ;; (call 'sort)
                     call-sort))

               (¬ (· ...
                     (bind
                      (λ (ev)
                         (if (call-sort ev)
                             (·  ...
                                 ret-sort
                                 ...
                                 (λ (ev*) (and (call? ev*) (equal? (car (call-args ev))
                                                                   (call-fn ev*)))))
                             ⊥)))))))
       (csort (λ (x y) (<= x y)) lst))))
(define ex-bad
  `(let ()
     ,@ex-common
     (tmon η
           (∩ (¬ (· (* (λ (ev) (not (call-sort ev))))
                    call-sort
                    (* not-ret-sort)
                    call-sort))
              (¬ (· (* (λ (ev) (not (call-sort ev))))
                    (bind
                     (λ (ev)
                        (if (call-sort ev)
                            (· (* not-ret-sort)
                               ret-sort
                               (* (λ (ev*) (not (and (call? ev*)
                                                     (equal? (car (call-args ev))
                                                             (call-fn ev*))))))
                               (λ (ev*) (and (call? ev*)
                                             (equal? (car (call-args ev))
                                                     (call-fn ev*)))))
                            ⊥)))))))
     (csort (λ (x y) (<= x y)) lst)
     ((unbox narf) 0 1)))

(define expr (parse example))
(unless (set-empty? (fv expr))
  (error 'example "Free variables in program ~a" (fv expr)))

(run (ev expr (hash) (hash) '()))
