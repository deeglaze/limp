#lang racket/base
(require (for-syntax racket/base) racket/match racket/list racket/set)

(define-syntax (??? stx) #'(error 'todo))

(define (set-smap S f)
  (for/set ([x (in-set S)]) (f x)))

(define (map-union base lst f)
  (for/fold ([S base]) ([x (in-list lst)]) (set-union S (f x))))

;; Raw implementation first to play with.

;; Expressions
(struct app (e es) #:transparent)
(struct ref (x) #:transparent)
(struct lam (xs e) #:transparent)
(struct smon (+ - S e) #:transparent) ;; Construct S, run e, attach S to e's result with +/- labels.
(struct tmon (ηe T e) #:transparent) ;; ηe --> η, T --> Tv, attach Tv to η, run e.
(struct ife (g t e) #:transparent)
(struct letrece (cs e) #:transparent)
(struct primop (which) #:transparent) ;; 'cons | 'new-timeline | 'pair? | 'car | 'cdr | 'null?

#|
Expr template:
  (match e
    [(app e es) ???]
    [(ref x) ???]
    [(lam xs e) ???]
    [(smon + - S e) ???]
    [(tmon ηe T e) ???]
    [(ife g t e) ???]
    [(letrece cs e) ???]
    [(primop which) ???]
    [_ (error who "Bad expression ~a" e)])
|#
(define ∅eq (seteq))

;; Expression's support
(define (supp e)
  (match e
    [(app e es) (map-union (supp e) es supp)]
    [(ref x) (seteq x)]
    [(lam xs e) (set-union (supp e) (apply seteq xs))]
    [(smon + - S e) (set-union (Ssupp S) (supp e))]
    [(tmon ηe T e) (set-union (supp ηe) (Tsupp T) (supp e))]
    [(ife g t e) (set-union (supp g) (supp t) (supp e))]
    [(letrece cs e) (set-union (supp e) (apply seteq (map first cs)))]
    [(? primop?) ∅eq]
    [_ (error 'supp "Bad expression ~a" e)]))

;; Free variables
(define (fv e)
  (match e
    [(app e es) (map-union (fv e) es fv)]
    [(ref x) (seteq x)]
    [(lam xs e) (set-subtract (fv e) (apply seteq xs))]
    [(smon + - S e) (set-union (Sfv S) (fv e))]
    [(tmon ηe T e) (set-union (fv ηe) (Tfv T) (fv e))]
    [(ife g t e) (set-union (fv g) (fv t) (fv e))]
    [(letrece cs e) (set-subtract (map-union (fv e) cs (compose fv second))
                                  (apply seteq (map first cs)))]
    [(primop which) ∅eq]
    [_ (error 'fv "Bad expression ~a" e)]))

;; another expression is quoted data

; Values
(struct Clo (xs e ρ) #:transparent)
(struct Clo/blessed (ℓ- ℓ+ Svs- Sv+ ℓ η clv) #:transparent)
(struct WClo (xs e ρ) #:transparent)
(struct timeline (nonce) #:transparent)
(struct boxv (a) #:transparent)
(struct weak (v) #:transparent)
;; cons is another value
(struct undefined () #:transparent) (define -undefined (undefined))
(define (datum? x)
  (or (boolean? x)
      (number? x)
      (string? x)
      (symbol? x)
      (null? x)
      (pair? x)
      (void? x)))

(define (rng h) (for/seteq ([a (in-hash-values h)]) a))

(define (SW* baseS baseW lst f)
  (for/fold ([S baseS]
             [W baseW])
      ([x (in-list lst)])
    (define-values (SS SW) (f x))
    (values (set-union S SS) (set-union W SW))))

(define-syntax (∪2* stx)
  (syntax-case stx ()
    [(_ e ...)
     (with-syntax ([(S ...) (generate-temporaries #'(e ...))]
                   [(W ...) (generate-temporaries #'(e ...))])
       #'(let-values ([(S W) e] ...)
           (values (set-union S ...) (set-union W ...))))]))

;; value -> (values Strongly-touched Weakly-touched)
(define/match (touch v)
  [((Clo _ _ ρ)) (values (rng ρ) ∅eq)]
  [((WClo _ _ ρ)) (values ∅eq (rng ρ))]
  [((timeline a)) (values (seteq a) ∅eq)]
  [((boxv a)) (values (seteq a) ∅eq)]
  [((weak v))
   (define-values (S W) (touch v))
   (values ∅eq (set-union S W))]
  [((Clo/blessed _ _ Svs- Sv+ _ η clv))
   (define-values (S* W*)
     (∪2* (touch η) (touch clv) (scon-touch Sv+)))
   (SW* S* W* Svs- scon-touch)]
  [((cons A D)) (∪2* (touch A) (touch D))]

  [((call _ fn args))
   (define-values (S* W*) (touch fn))
   (SW* S* W* args touch)]
  [((ret _ fn  v)) (∪2* (touch fn) (touch v))]

  [((or (kl Tv) (¬ Tv) (bindv Tv) (ev-predv Tv))) (touch Tv)]
  [((or (∪ Tv0 Tv1) (∩ Tv0 Tv1) (· Tv0 Tv1)))
   (∪2* (touch Tv0) (touch Tv1))]
  
  [(_) ∅eq])

(define/match (scon-touch Sv)
  [((-->/blessed Svs- Sv+ _ η))
   (define-values (S* W*) (∪2* (scon-touch Sv+) (touch η)))
   (SW* S* W* Svs- scon-touch)]
  [((cons/blessed Av Dv))
   (∪2* (scon-touch Av) (scon-touch Dv))]
  [(v) (touch v)])

(define/match (frame-touch φ)
  [((evk _ vs ρ)) (SW* (rng ρ) ∅eq vs touch)]
  [((or (sk _ _ _ ρ)
        (ifk _ _ ρ)
        (lrk _ _ _ ρ)
        (mkd _ ρ)
        (mkt _ _ ρ)
        (kbin₀ _ _ ρ)
        (begink _ ρ)))
   (values (rng ρ) ∅eq)]

  [((ch*k _ Svs- _ Sv+ vs _ η clv args))
   (define-values (S* W*) (∪2* (touch η) (touch clv) (scon-touch Sv+)))
   (define-values (S** W**) (SW* S* W* Svs- scon-touch))
   (SW* S** W** args touch)]
  [((chk _ _ Sv+ clv _ η))
   (∪2* (touch clv) (touch η) (scon-touch Sv+))]
  [((chDk _ _ Dv v)) (∪2* (scon-touch Dv) (touch v))]
  [((or (wrapk _ _ Sv) (mkcons Sv))) (scon-touch Sv)]

  [((or (sret _ v0 _ v1)
        (blret _ v0 v1)))
   (∪2* (touch v0) (touch v1))]
  [((blcall _ _ Sv+ clv vs* _ η))
   (define-values (S* W*) (∪2* (touch η) (touch clv) (scon-touch Sv+)))
   (SW* S* W* vs* touch)]

  [((or (tbin₀ _ Tv) (seqk Tv) (kbin₁ _ Tv))) (touch Tv)]
  [((seq2k T ev η _))
   (∪2* (touch T) (touch ev) (touch η))]

  [((or (negk _ _ _ _ ρ Svs-)
        (timelinek Svs- _ _ ρ)))
   (SW* (rng ρ) ∅eq Svs- scon-touch)]
  [((arrk vs v _))
   (define-values (S* W*) (touch v))
   (SW* S* W* vs touch)]
  [(_) ∅eq])

(define/match (kont-touch κ)
  [((cons φ κ)) (∪2* (frame-touch φ) (kont-touch κ))]
  [('()) (values ∅eq ∅eq)])

;; ℘[Addr] Map[Addr,Value] -> (values Strongly-reachable Only-weakly-reachable)
(define (reachable Sroot Wroot σ)
  (define seenS (mutable-seteq))
  (define onlyW (mutable-seteq))
  (set-union! onlyW (set-subtract Wroot Sroot))
  (let rec ([todo Sroot])
    (cond [(set-empty? todo) (values seenS onlyW)]
          [else
           (define a (set-first todo))
           (define todo* (set-rest todo))
           (cond
            [(set-member? seenS a) (rec todo*)]
            [else
             (set-remove! onlyW a)
             (set-add! seenS a)
             (define-values (S W) (touch a))
             (set-union! onlyW (set-subtract W seenS))
             (rec (set-union todo* S))])])))

(define (state-touch ς)
  (match ς
    [(ev _ ρ _ κ)
     (define-values (S W) (kont-touch κ))
     (values (set-union (rng ρ) S) W)]
    [(co κ v _)
     (∪2* (kont-touch κ) (touch v))]
    [(ap fn args _ κ)
     (define-values (S* W*) (∪2* (touch fn) (kont-touch κ)))
     (SW* S* W* args touch)]
    [(check ℓ+ ℓ- S v _ κ)
     (∪2* (scon-touch S) (touch v) (kont-touch κ))]
    [(ev-syn S ρ _ κ)
     (∪2* (scon-touch S) (kont-touch κ) (values (rng ρ) ∅eq))]
    [(send T ev η _ κ)
     (∪2* (touch T) (touch ev) (touch η) (kont-touch κ))]
    [(check-app _ Svs- _ Sv+ vs* _ η clv vs _ κ)
     (define-values (S* W*)
       (∪2* (touch η) (touch clv) (kont-touch κ) (scon-touch Sv+)))
     (define-values (S** W**)
       (SW* S* W* Svs- scon-touch))
     (define-values (S*** W***)
       (SW* S** W** vs* touch))
     (SW* S*** W*** vs touch)]))

(define (state-replace-σ ς σ)
  (match ς
    [(ev e ρ _ κ) (ev e ρ σ κ)]
    [(co κ v _) (co κ v σ)]
    [(ap fn args _ κ) (ap fn args σ κ)]
    [(check ℓ+ ℓ- S v _ κ) (check ℓ+ ℓ- S v σ κ)]
    [(ev-syn S ρ _ κ) (ev-syn S ρ σ κ)]
    [(send T ev η _ κ) (send T ev η σ κ)]
    [(check-app ℓ- Svs- ℓ+ Sv+ vs* ℓ η clv vs _ κ)
     (check-app ℓ- Svs- ℓ+ Sv+ vs* ℓ η clv vs σ κ)]))

(define (Γ ς)
  (define-values (root σ) (state-touch ς))
  (define R (reachable root σ))
  (define σ*
    (for/hash ([(a v) (in-hash σ)]
               #:when (set-member? a rS))
      (values a (weaken v rW))))
  (state-replace-σ ς σ*))

(define (value-equal? v0 v1 σ)
  (define A (mutable-seteq))
  (let rec ([v0 v0] [v1 v1])
    (match* (v0 v1)
      [((boxv v0*) (boxv v1*))
       (define p (cons v0 v1))
       (or (set-member? A p)
           (begin (set-add! A p)
                  (rec (hash-ref σ v0*) (hash-ref σ v1*))))]
      [((cons v0A v0D) (cons v1A v1D))
       (and (rec v0A v1A)
            (rec v0D v1D))]
      [(_ _) (equal? v0 v1)])))

;; Structural contract syntax
(struct --> (Ss- S+ ℓ e) #:transparent)
(struct cons/c (A D) #:transparent)
;; Evaluated structural contracts
(struct -->/blessed (Svs- Sv+ ℓ η) #:transparent)
(struct cons/blessed (Av Dv) #:transparent)

(define (Ssupp S)
  (match S
    [(--> Ss- S+ _ e)
     (for/fold ([S* (set-union (Ssupp S+) (supp e))])
         ([S- (in-list Ss-)])
       (set-union S* (Ssupp S-)))]
    [(cons/c A D) (set-union (Ssupp A) (Ssupp D))]
    [_ (error 'Ssupp "Bad structural contract ~a" S)]))

(define (Sfv S)
  (match S
    [(--> Ss- S+ _ e)
     (for/fold ([S* (set-union (Sfv S+) (fv e))])
         ([S- (in-list Ss-)])
       (set-union S* (Sfv S-)))]
    [(cons/c A D) (set-union (Sfv A) (Sfv D))]
    [_ (error 'Sfv "Bad structural contract ~a" S)]))

;; Temporal contract syntax
(struct ev-pred (e) #:transparent)
(struct ev-any () #:transparent)
;;(struct ev-none () #:transparent)
(struct bind (e) #:transparent) ;; Take an event and produce a tcon
(struct kl (T) #:transparent)
(struct · (T₀ T₁) #:transparent)
(struct ∪ (T₀ T₁) #:transparent)
(struct ∩ (T₀ T₁) #:transparent)
(struct ¬ (T) #:transparent)
(struct ε () #:transparent)
(struct ⊥ () #:transparent)
(struct ⊤ () #:transparent)
;; A value is any of the above except ev-pred and bind, which evaluate to ev-predv and bindv resp.
(struct ev-predv (v) #:transparent)
(struct bindv (v) #:transparent)

;; Temporal contract's support
(define (Tsupp T)
  (match T
    [(or (ev-pred e) (bind e)) (supp e)]
    [(or (? ε?) (? ⊥?) (? ⊤?) (? ev-any?)) ∅eq]
    [(or (kl T) (¬ T)) (Tsupp T)]
    [(or (· T T*) (∪ T T*) (∩ T T*)) (set-union (Tsupp T) (Tsupp T*))]
    [_ (error 'Tsupp "Bad temporal contract ~a" T)]))

;; Temporal contract's free variables
(define (Tfv T)
  (match T
    [(or (ev-pred e) (bind e)) (fv e)]
    [(or (? ε?) (? ⊥?) (? ⊤?) (? ev-any?)) ∅eq]
    [(or (kl T) (¬ T)) (Tfv T)]
    [(or (· T T*) (∪ T T*) (∩ T T*)) (set-union (Tfv T) (Tfv T*))]
    [_ (error 'Tfv "Bad temporal contract ~a" T)]))

(define -⊤ (⊤))
(define -⊥ (⊥))
(define -ε (ε))
(define -ev-any (ev-any))

;; Nullable? decision procedure.
(define/match (ν? T)
  [((or (? ev-pred?) (? ev-predv?) (? ev-any?) #;(? ev-none?) (? bind?) (? bindv?)
        )) #f]
  [((∪ T₀ T₁)) (or (ν? T₀) (ν? T₁))]
  [((or (∩ T₀ T₁) (· T₀ T₁))) (and (ν? T₀) (ν? T₁))]
  [((or (? ε?) (? kl?) (? ¬?) (? ⊤?))) #t]
  [((? ⊥?)) #f])

;; (ν!? T) ⇒ ⟦T⟧ = {ε}
;; Incomplete since μ? is incomplete.
(define/match (ν!? T)
  [((? ε?)) #t]
  [((kl T)) (ν!? T)] ;; ε* = ε.
  [((¬ T)) (μ? T)] ;; ¬ adds {ε}, but can't get anything else out of T.
  [((or (∪ T₀ T₁) (· T₀ T₁))) (and (ν!? T₀) (ν!? T₁))]
  [((∩ T₀ T₁)) (or (ν!? T₀) (ν!? T₁))]
  [((or (? ⊥?) (? ⊤?) (? ev-pred?) (? ev-predv?) (? ev-any?) #;(? ev-none?)
        (? bind?) (? bindv?))) #f])

;; (μ? T) ⇒ ⟦T⟧ = ∅
;; Incomplete decision due to undecidability of infeasibility of matching.
(define/match (μ? T)
  [((∪ T₀ T₁)) (and (μ? T₀) (μ? T₁))]
  [((∩ T₀ T₁)) (or (μ? T₀) (μ? T₁))]
  ;; denotation of · contains partial traces of T₀ regardless of T₁.
  ;; If T₀ is denotationally {ε}, then we can say the sequence is ⊥ if T₁ is.
  [((· T₀ T₁)) (or (μ? T₀) (and (ν!? T₀) (μ? T₁)))]
  [((or (? ε?) (? kl?) (? ¬?) (? ⊤?)
        (? ev-pred?) (? ev-predv?) (? ev-any?) #;(? ev-none?) (? bind?) (? bindv?)))
   #f]
  [((? ⊥?)) #t])

;; Theorem: DNE does not hold. However, ¬^4 = ¬^2.
;; We are /adding/ one ¬, so if at 3, going to 4 is going to 2.
(define/match (mk¬ T)
  [((¬ (¬ (¬ T)))) (¬ (¬ T))]
  [(T) (¬ T)])

(define (mk· T₀ T₁)
  (cond [(or (⊥? T₀) (⊤? T₀))
         T₀]
        [(ν!? T₀) T₁]
        [(μ? T₀) -⊥]
        [else (· T₀ T₁)]))

(define (mk∪ T₀ T₁)
  (cond [(equal? T₀ T₁) T₀]
        [(μ? T₀) T₁]
        [(μ? T₁) T₀]
        [else (∪ T₀ T₁)]))

(define (mk∩ T₀ T₁)
  (cond [(equal? T₀ T₁) T₀]
        [(⊤? T₀) T₁]
        [(⊤? T₁) T₀]
        [else (∩ T₀ T₁)]))

(define (mkkl T)
  (cond [(ν!? T) -ε]
        [(or (kl? T) (⊤? T)) T]
        [else (kl T)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Frames
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Evaluation Frames
(struct evk (es vs ρ) #:transparent)
(struct sk (+ - e ρ) #:transparent) ;; attaching structural monitor
(struct ifk (t e ρ) #:transparent)
(struct lrk (x cs body ρ) #:transparent)

;; Checking frames
(struct ch*k (ℓ- Svs- ℓ+ Sv+ vs ℓ η clv args) #:transparent)
(struct chk (ℓ+ ℓ- Sv+ clv ℓ η) #:transparent)
(struct chDk (ℓ+ ℓ- D v) #:transparent)
(struct wrapk (ℓ+ ℓ- Sv) #:transparent)

;; Messaging frames
(struct sret (ℓ+ clv ℓ η) #:transparent)
(struct blret (ℓ+ η rv) #:transparent)
(struct blcall (ℓ- ℓ+ Sv+ clv vs* ℓ η) #:transparent)

;; Deriving frames
(struct tbin₀ (C T) #:transparent)
(struct seq2k (T ev η ℓ) #:transparent) ;; evaling (· T₀ T₁) and (ν? T₀)
;; If (· T₀ T₁) and ¬(ν? T₀), then (· ∂_E(T₀) T₁)
;; If (kl T) then (· ∂_E(T) (kl T))
(struct seqk (T) #:transparent)


;; Making structural contract frames
(struct negk (Ss- S+ ℓ e ρ Svs-) #:transparent) ;; left of ->
(struct mkd (D ρ) #:transparent)
(struct mkcons (A) #:transparent)
(struct timelinek (rev-Ss- ℓ e ρ) #:transparent)
(struct arrk (vs v ℓ) #:transparent)

;; Making temporal contract frames
(struct mkt (T e ρ) #:transparent)
(struct kunitary (C) #:transparent)
(struct kbin₀ (C T ρ) #:transparent)
(struct kbin₁ (C Tv) #:transparent)
(struct pred-to-T () #:transparent) (define -pred-to-T (pred-to-T))
(struct begink (e ρ) #:transparent)
(define kevpred (kunitary ev-predv))
(define kbind (kunitary bindv))
(define kkl (kunitary kl))
(define kneg (kunitary ¬))
(define negt (kunitary (λ (T) (if (ν? T) -⊥ (¬ T)))))

;; Events
(struct call (ℓ fn args) #:transparent)
(struct ret (ℓ fn v) #:transparent)

;; States
(struct ev (e ρ σ κ) #:transparent)
(struct co (κ v σ) #:transparent)
(struct check (ℓ+ ℓ- S v σ κ) #:transparent)
(struct check-app (ℓ- Svs- ℓ+ Sv+ vs* ℓ η clv vs σ κ) #:transparent)
(struct ap (fn vs σ κ) #:transparent)
(struct ev-syn (Ssyn ρ σ κ) #:transparent)
(struct send (T ev η σ κ) #:transparent)

;; Final states
(struct ans (v σ) #:transparent)
(struct stuck (state msg) #:transparent)
(struct blame (ℓ S v) #:transparent)
(struct tblame (ℓ T ev) #:transparent)

(define (alloc ς tag)
  (gensym tag))

(define nullary-prims '(new-timeline))
(define unary-prims ;; predicates and projections
  '(pair? car cdr null?
    box? make-box unbox
    call? call-label call-fn call-args
    ret? ret-fn ret-label ret-value))
(define binary-prims '(cons equal? set-box!))
(define prims (append nullary-prims unary-prims binary-prims))
(define (unary-primop? v)
  (match v [(primop which) #:when (memq which unary-prims) #t] [_ #f]))

(define (ev-δ ς which args σ κ)
  (define (bad num)
    (stuck ς (format "Primitive expected ~a args, got ~a" num (length args))))
  (define (arity-mismatch num)
    (if (= num (length args)) #f (bad num)))
  (define (go v) (co κ v σ))
  (match which
    ['cons (or (arity-mismatch 2)
               ;; already consed
               (go args))]
    ['pair? (or (arity-mismatch 1)
                (go (pair? (first args))))]
    ['car (or (arity-mismatch 1)
              (go (car (first args))))]
    ['cdr (or (arity-mismatch 1)
              (go (cdr (first args))))]
    ['null? (or (arity-mismatch 1)
                (go (null? (first args))))]
    ['new-timeline (or (arity-mismatch 0)
                       (go (timeline (alloc ς 'new-timeline))))]

    ['call? (or (arity-mismatch 1)
                (go (call? (first args))))]
    ['call-label (or (arity-mismatch 1)
                     (go (call-ℓ (first args))))]
    ['call-fn (or (arity-mismatch 1)
                  (go (call-fn (first args))))]
    ['call-args (or (arity-mismatch 1)
                    (go (call-args (first args))))]

    ['ret? (or (arity-mismatch 1) (go (ret? (first args))))]
    ['ret-fn (or (arity-mismatch 1) (go (ret-fn (first args))))]
    ['ret-label (or (arity-mismatch 1) (go (ret-ℓ (first args))))]
    ['ret-value (or (arity-mismatch 1) (go (ret-v (first args))))]

    ['box? (or (arity-mismatch 1) (go (boxv? (first args))))]
    ['make-box (or (arity-mismatch 1)
                   (let ([a (alloc ς 'make-box)])
                     (co κ (boxv a) (hash-set σ a (first args)))))]
    ['unbox (or (arity-mismatch 1)
                (match (first args)
                  [(boxv a) (go (hash-ref σ a))]
                  [f (stuck ς "unbox expects a box, got ~a" f)]))]
    ['set-box! (match args
                 [(list b v)
                  (match b
                    [(boxv a) (co κ (void) (hash-set σ a v))]
                    [_ (stuck ς "set-box! expects a box as the first argument, got ~a" b)])]
                 [_ (bad 2)])]

    ['equal? (or (arity-mismatch 2)
                 (go (value-equal? (first args) (secord args) σ)))]))

(define (restrict-to-fv e ρ)
  (define dom (fv e))
  (for/hash ([(x a) (in-hash ρ)]
             #:when (set-member? dom x))
    (values x a)))

(define/match (step-ev ς)
  [((ev e ρ σ κ))
   (match e
     [(app e0 es) (ev e0 ρ σ (cons (ev es '() ρ) κ))]
     [(lam xs e) (co κ (Clo xs e (restrict-to-fv e ρ)) σ)]
     [(ref x) (co κ (hash-ref σ (hash-ref ρ x)) σ)]
     [(smon + - Ssyn e) (ev-syn Ssyn ρ σ (cons (sk + - e ρ) κ))]
     [(tmon ηe T e) (ev ηe ρ σ (cons (mkt T e ρ) κ))]
     [(ife gu th el) (ev gu ρ σ (cons (ifk th el ρ) κ))]
     [(letrece cs body)
      (match cs
        ;; (letrec () e) = e
        ['() (ev body ρ σ κ)]
        ;; Initialize boxes, evaluate first clause.
        [(cons (cons x e) cs*)
         (define-values (σ* ρ*)
           (for/fold ([σ* σ] [ρ* ρ]) ([xe (in-list cs)])
               (match-define (cons x e) xe)
               (define a (alloc ς x))
               (values (hash-set σ* a -undefined)
                       (hash-set ρ* x a))))
         (ev e ρ* σ* (cons (lrk x cs* body ρ*) κ))])]
     [(or (? primop?) (? datum?)) (co κ e σ)] ;; e is its own value

     ;; atomic contracts that are their own value
     [(or (? ⊤?) (? ⊥?) (? ε?) (? ev-any?) #;(? ev-none?)
          )
      (co κ T σ)]
     [(ev-pred e) (ev e ρ σ (cons kevpred κ))]
     [(bind e) (ev e ρ σ (cons kbind κ))]
     [(kl T) (ev T ρ σ (cons kkl κ))]
     [(¬ T) (ev T ρ σ (cons kneg κ))]
     [(· T₀ T₁) (ev T₀ σ σ (cons (kbin₀ mk· T₁ ρ) κ))]
     [(∪ T₀ T₁) (ev T₀ σ σ (cons (kbin₀ mk∪ T₁ ρ) κ))]
     [(∩ T₀ T₁) (ev T₀ σ σ (cons (kbin₀ mk∩ T₁ ρ) κ))]
     [_ (error 'step-ev "Bad expression ~a" e)])])

(define/match (step-co ς)
  [((co '() v σ)) (ans v σ)]
  [((co (cons φ κ) v σ))
   (match φ
     ;; Evaluating
     [(evk '() vs ρ)
      (match-define (cons v0 vs*) (reverse (cons v vs)))
      (ap v0 vs* σ κ)]

     [(evk (cons e0 es) vs ρ)
      (ev e0 ρ σ (cons (evk es (cons v vs) ρ) κ))]

     [(ifk th el ρ) (ev (if v th el) ρ σ κ)]

     [(lrk x cs body ρ)
      (define σ* (hash-set σ (hash-ref ρ x) v))
      (match cs
        ['() (ev body ρ σ* κ)]
        [(cons (cons y e*) cs*)
         (ev e* ρ σ* (cons (lrk y cs* body ρ) κ))])]

     [(sk + - e ρ) ;; v is a structural contract
      (ev e ρ σ (cons (wrapk + - v) κ))]

     ;; Constructing temporal contracts
     [(mkt T e ρ) (ev T ρ σ (cons (begink e ρ) κ))]
     [(kunitary C) (co κ (C v) σ)]
     [(kbin₀ C T ρ) (ev T ρ σ (cons (kbin₁ C v) κ))]
     [(kbin₁ C Tv) (co κ (C Tv v) σ)]

     ;; Derivatives of temporal contracts
     [(pred-to-T) (co κ (if v -ε -⊥) σ)]
     [(seqk T₁) (co κ (mk· v T₁) σ)]
     [(seq2k T₁ ev η ℓ) 
      ;; v is ∂_ev(T₀)
      (error 'todo)
      (send T₁ ev η ℓ σ (cons (tbin₀ mk∪ v) κ))]
     [(tbin₀ C Tv) (co κ (C Tv v) σ)]

     ;; Constructing structural contracts
     [(timelinek vs ℓ e ρ)
      (ev e ρ σ (cons (arrk vs v ℓ) κ))]
     [(arrk vs- v+ ℓ) ;; v is a timeline
      (if (timeline? v)
          (co κ (-->/blessed (reverse vs-) v+ ℓ v) σ)
          (stuck ς "--> contract requires a timeline."))]
     [(negk '() S+ ℓ e ρ Svs-) (ev-syn S+ ρ σ (cons (timelinek Svs- ℓ e ρ) κ))]
     [(negk (cons S- Ss-) S+ ℓ e ρ Svs-)
      (ev-syn S- ρ σ (cons (negk Ss- S+ ℓ e ρ (cons v Svs-)) κ))]
     [(mkd D ρ) (ev-syn D ρ σ (cons (mkcons v) κ))]
     [(mkcons A) (co κ (cons/blessed A v) σ)]

     ;; Messaging
     [(chk ℓ+ ℓ- Sv+ clv ℓ η) ;; check return value first, then send message to timeline.
      (check ℓ+ ℓ- Sv+ v (hash-set σ η v) (cons (sret ℓ+ clv ℓ η) κ))]
     ;; blame or do call
     [(blcall ℓ- ℓ+ Sv+ clv vs* ℓ η)
      ;; Temporal contract has been derived against call message.
      ;; If it's blatantly bad, then blame.
      (if (μ? v)
          (tblame ℓ- (hash-ref σ η -⊤))
          (ap clv vs* σ (cons (chk ℓ+ ℓ- Sv+ clv ℓ η) κ)))]
     ;; blame or continue with return
     [(blret ℓ+ η rv)
      ;; Temporal contract has been derived against return message.
      ;; If it's blatantly bad, then blame.
      (if (μ? v)
          (tblame ℓ+ (hash-ref σ η -⊤))
          (co κ rv (hash-set σ η v)))]
     ;; send the return message with the wrapped return value
     [(sret ℓ+ clv ℓ η)
      (send (hash-ref σ η -⊤) (ret ℓ clv v) η ℓ σ (cons (blret ℓ+ η v) κ))]

     ;; Checking
     [(wrapk ℓ+ ℓ- Sv)
      (check ℓ+ ℓ- Sv v σ κ)]
     [(chDk ℓ+ ℓ- D v) (check ℓ+ ℓ- D v σ κ)]
     [(ch*k ℓ- Svs- ℓ+ Sv+ vs* ℓ η clv vs)
      (check-app ℓ- Svs- ℓ+ Sv+ vs* ℓ η clv vs σ κ)]     

     [_ (error 'step-co "Bad frame ~a" φ)])])

(define/match (step-ap ς)
  [((ap fn vs σ κ))
   (define (app xs e ρ vs)
     (let bind ([xs xs] [vs vs] [ρ ρ] [σ σ])
       (match* (xs vs)
         [('() '()) (ev e ρ σ κ)]
         [((cons x xs) (cons v vs))
          (define a (alloc ς x))
          (bind xs vs (hash-set ρ x a) (hash-set σ a v))]
         [(_ _) (stuck ς "Arity mismatch for function application")])))
   (match fn
     [(Clo xs e ρ) (app xs e ρ vs)]
     [(WClo xs e ρ) (app xs e ρ (map weak vs))]
     [(Clo/blessed ℓ- ℓ+ Svs- Sv+ ℓ η clv)
      (check-app ℓ- Svs- ℓ+ Sv+ vs '() ℓ η clv σ κ)]
     [(primop which) (ev-δ ς which vs σ κ)])])

(define/match (step-ev-syn ς)
  [((ev-syn S ρ σ κ))
   (match S
     [(--> '() S+ ℓ e) (ev-syn S+ ρ σ (cons (timelinek '() ℓ e ρ) κ))]
     [(--> (cons S- Ss-) S+ ℓ e)
      (ev-syn S- ρ σ (cons (negk Ss- S+ ℓ e ρ '()) κ))]

     [(cons/c A D)
      (ev-syn A ρ σ (cons (mkd D ρ) κ))]

     ;; only unary functions are contracts
     [(or (? unary-primop?)
          (Clo (list _) _ _)
          (Clo/blessed _ _ (list _) _ _ _ _))
      (co κ S σ)]

     [_ (stuck ς "Bad structural contract")])])

;; Derivatives!
(define/match (step-send ς)
  [((send T ev η σ κ))
   (match T
     [(or (? ε?) #;(? ev-none?)
          )
      (co κ -⊥ σ)]
     [(ev-predv v) (ap v ev σ (cons -pred-to-T κ))]
     [(bindv v) (ap v ev σ κ)]
     [(kl T*) (send T* ev η σ (cons (seqk T) κ))]
     [(¬ T*) (send T* ev η σ (cons negt κ))]
     [(· T₀ T₁) (send T₀ ev η σ (cons (if (ν? T₀) (seq2k T₁ ev η) (seqk T₁)) κ))]
     [(∪ T₀ T₁) (send T₀ ev η σ (cons (tbin₀ mk∪ T₁) κ))]
     [(∩ T₀ T₁) (send T₀ ev η σ (cons (tbin₀ mk∩ T₁) κ))])])

(define/match (step-check-app ς)
  [((check-app ℓ- Svs- ℓ+ Sv+ vs* ℓ η clv vs σ κ))
   (match* (Svs- vs)
     [('() '())
      (send (hash-ref σ η -⊤) (call ℓ clv vs*) η σ (cons (blcall ℓ- ℓ+ Sv+ clv vs* ℓ η) κ))]
     [((cons Sv- Svs-*) (cons v1 vs**))
      (check ℓ- ℓ+ Sv- v1 σ (cons (ch*k ℓ- Svs-* ℓ+ Sv+ vs** ℓ η clv vs*) κ))]
     [(_ _) (stuck ς "Arity mismatch for blessed application")])])

(define/match (step-check ς)
  [((check ℓ+ ℓ- S v σ κ))
   (match S
     [(-->/blessed Svs- Sv+ ℓ η)
      (match v
        [(or (Clo args _ _) (Clo/blessed _ _ args _ _ _ _))
         #:when (= (length args) (length Svs-))
         (co κ (Clo/blessed ℓ- ℓ+ Svs- Sv+ ℓ η v) σ)]
        [_  (blame ℓ S v)])]
     [(cons/blessed Av Dv)
      (match v
        [(cons A D)
         (check ℓ+ ℓ- A v σ (cons (chDk ℓ+ ℓ- Dv D) κ))]
        [_ (blame ℓ+ S v)])]
     [_ (error 'step-check "Bad structural contract ~a" S)])])

(define (step ς)
  (cond [(ev? ς) (step-ev ς)]
        [(co? ς) (step-co ς)]
        [(ap? ς) (step-ap ς)]
        [(check? ς) (step-check ς)]
        [(ev-syn? ς) (step-ev-syn ς)]
        [(check-app? ς) (step-check-app ς)]
        [(send? ς) (step-send ς)]))

(define (run ς)
  (if (or (ans? ς) (blame? ς) (tblame? ς) (stuck? ς))
      ς
      (run (step ς))))

(define (parse sexp [ρ (hasheq)])
  (define (p* sexp) (parse sexp ρ))
    (define (is-app [sexp sexp])
      (app (p* (first sexp)) (map p* (rest sexp))))
    (define (if-builtin name f)
      (if (hash-has-key? ρ name) (is-app) (f)))
    (define (defn-ctx sexps ρ)
      (unless (pair? sexps) (error 'defn-ctx "Expected at least one expression"))
      (define ρ*
        (for/fold ([ρ* ρ]) ([s (in-list sexps)])
          (match s
            [`(define ,(? symbol? name) ,rhs)
             (if (hash-has-key? ρ* 'define)
                 ρ*
                 (hash-set ρ* name (gensym name)))]
            [`(define (,(? symbol? name) ,(? symbol? args) ...) . ,rhs)
             (if (hash-has-key? ρ* 'define)
                 ρ*
                 (λ () (hash-set ρ* name (gensym name))))]
            [`(define . ,rest)
             (if (hash-has-key? ρ* 'define)
                 ρ*
                 (error 'defn-ctx "Ill-formed define form"))]
            [_ ρ*])))
      (let loop ([ss sexps] [rev-clauses '()] [redefined? (hash-has-key? ρ 'define)])
        (match ss
          [(list (and e `(define ,x ,r)))
           (if redefined?
               (letrece (reverse rev-clauses) (parse e ρ*))
               (error 'defn-ctx "Expected last form to be an expression, not a definition: ~a" e))]
          [(list e) (letrece (reverse rev-clauses) (parse e ρ*))]
          [(cons s ss)
           (define (expr)
             (loop ss
                   (cons (cons (gensym 'dummy) (parse s ρ*)) rev-clauses)
                   redefined?))
           (match s
             [`(define ,x ,r)
              (cond
               [redefined? (expr)]
               [else
                (define-values (name rhs)
                  (cond
                   [(symbol? x) (values x (parse r ρ*))]
                   [else
                    (match-define (cons name formals) x)
                    (define xs* (map gensym formals))
                    (define ρ** (apply hash-set* ρ* (map list formals xs*)))
                    (values name (lam xs* (parse r ρ**)))]))
                (loop ss
                      (cons (cons name rhs) rev-clauses)
                      (eq? name 'define))])]
             [_ (expr)])])))
    (match sexp
      [(? symbol? x)
       (define x* (hash-ref ρ x x))
       (if (memq x* prims)
           (primop x*)
           (ref x*))]
      [`(,(and head (or 'λ 'lambda)) (,(? symbol? xs) ...) . ,body)
       (if-builtin head
                   (λ ()
                      (define xs* (map gensym xs))
                      (define ρ* (apply hash-set* ρ (append-map list xs xs*)))
                      (lam xs* (defn-ctx body ρ*))))]
      [`(letrec ,([,(? symbol? xs) ,es] ...) . ,body)
       (if-builtin 'letrec
                   (λ ()
                      (define xs* (map gensym xs))
                      (define ρ* (apply hash-set* ρ (append-map list xs xs*)))
                      (letrece (for/list ([x (in-list xs*)] [e (in-list es)])
                                 (cons x (parse e ρ*)))
                               (defn-ctx body ρ*))))]
      [`(smon ',(? symbol? +) ',(? symbol? -) ,S ,e)
       (if-builtin 'smon
                   (λ () (smon + - (parse-scon S ρ) (p* e))))]
      [`(tmon ηe T e)
       (if-builtin 'tmon
                   (λ () (tmon (p* ηe) (parse-tcon T ρ) (p* e))))]
      [`(if ,g ,t ,e)
       (if-builtin 'if
                   (λ () (ife (p* g) (p* t) (p* e))))]

      ;; macros
      [`(let ([,(? symbol? xs) ,es] ...) . ,body)
       (if-builtin 'let
                   (λ () (p* `((λ ,xs . ,body) . ,es))))]
      [`(or ,e ...)
       (if-builtin 'or (λ ()
                          (let rec ([es e])
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
                           (let rec ([es e])
                             (match es
                               ['() #t]
                               [(list e) (p* e)]
                               [(cons e rest) (ife (p* e) (rec rest) #f)]))))]

      ;; fall-through application
      [`(,e . ,es) (is-app)]
      [_ (error 'parse "Bad expression ~a" sexp)]))

(define (parse-scon S ρ)
  (define (parse-scon* S) (parse-scon S ρ))
  (match S
    [`(-> ,S- ... ,S+ : ',(? symbol? ℓ) @ ,e)
     (--> (map parse-scon* S-)
          (parse-scon* S+)
          ℓ
          (parse e ρ))]
    [`(cons/c ,A ,D)
     (cons/c (parse-scon* A) (parse-scon* D))]
    [e (parse e ρ)]))

(define (rassoc bin ⊥ lst)
  (match lst
    [(cons x y)
     (if (null? y)
         x
         (bin x (rassoc bin ⊥ y)))]
    ['() ⊥]))

(define (parse-tcon T ρ)
  (define (p* T) (parse-tcon T ρ))
  (define (if-builtin name f)
    (if (hash-has-key? ρ name) (ev-pred (parse T ρ)) (f)))
  (match T
    [`(* ,T) (if-builtin '* (λ () (kl (p* T))))]
    [`(∪ ,T ...) (if-builtin '∪ (λ () (rassoc mk∪ -⊥ (map p* T))))]
    [`(∩ ,T ...) (if-builtin '∩ (λ () (rassoc mk∩ -⊤ (map p* T))))]
    [`(· ,T ...) (if-builtin '· (λ () (rassoc mk· -ε (map p* T))))]
    [`(¬ ,T) (if-builtin '¬ (λ () (mk¬ (p* T))))]
    [`_ (if-builtin '_ (λ () -ev-any))]
    [`⊤ (if-builtin '⊤ (λ () -⊤))]
    [`... (if-builtin '... (λ () -⊤))]
    [`⊥ (if-builtin '⊥ (λ () -⊥))]
    [`ε (if-builtin '⊥ (λ () -ε))]
    [`(bind ,e) (if-builtin 'bind (λ () (bind (parse e ρ))))]
    [_ (error 'parse-tcon "Bad temporal contract ~a" T)]))

(define example
  '(let ()
     (define narf (make-box #f))
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
       (if (null? lst)
           b
           (foldl f (f (car lst) b) (cdr lst))))
     (define (sort cmp lst)
       (foldl (insert cmp) '() lst))
     (define (listof f)
       (λ (lst)
          (or (null? lst)
              (and (f (car lst)) ((listof f) (cdr lst))))))
     (define η (new-timeline))
     (define csort 
       (smon 'user 'context
             (->
              (-> number? number? boolean? : 'cmp @ η)
              (listof number?)
              any
              : 'sort @ η)
             sort))
     (define lst (list 1 2 3 4))
     (tmon η
      (∩ (¬ (· ...
               (λ (ev) (and (call? ev) (equal? 'sort (call-label ev))))
               (star (λ (ev) (or (not (ret? ev))
                                 (not (equal? 'sort (ret-label ev))))))
               (λ (ev) (and (call? ev) (equal? 'sort (call-label ev))))))
           
           (¬ (· ...
                 (bind
                  (λ (ev)
                     (if (and (call? ev)
                              (equal? 'sort (call-label ev)))
                         (· ...))
                     (call (label sort) (? cmp) _)
                     (·  ...
                         (ret (label sort) _)
                         ...
                         (call ($ cmp) _ _))))))))
     (csort (λ (x y) (<= x y)) lst)))

(run (ev (parse example) (hash) (hash) '()))
