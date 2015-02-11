#lang racket/base
(provide type-join type-meet trace-type-meet! untrace-type-meet!)
(require racket/match racket/set racket/trace
         foracc
         (only-in racket/bool implies)
         "tc-ctxs.rkt"
         "common.rkt" "language.rkt" "subtype.rkt" "types.rkt" "type-formers.rkt")

(struct join-res (seen Γ τ) #:transparent)

(define (type-join-aux us)
  (define (⊔ ⊔seen ρ Γ τ σ)
    (define (⊔* τ σ) (⊔ ⊔seen ρ Γ τ σ))
    (define (resolve-join r τ)
      (⊔ (set-add ⊔seen (cons r τ)) ρ Γ (resolve r) τ))
    (cond
     [(and (TError? τ) (TError? σ))
      (join-res ⊔seen
                (TError (append (TError-msgs τ) (TError-msgs σ)))
                Γ)]
     [(set-member? ⊔seen (cons τ σ)) (join-res ⊔seen Γ T⊤)]   
     ;; If comparable, choose the larger type without allocating new type structure.
     [(<:? Γ τ σ) => (λ (Δ) (join-res ⊔seen Δ σ))]
     [(<:? Γ σ τ) => (λ (Δ) (join-res ⊔seen Δ τ))]
     [else
      (match* (τ σ)
        [((TVariant: _ n τs tr0) (TVariant: _ n σs tr1))
         #:when (and (= (length τs) (length σs))
                     (implies (and tr0 tr1) (equal? tr0 tr1)))
         (define-values (Δ j)
           (for/acc ([Γ Γ] [#:type list])
                    ([τ (in-list τs)]
                     [σ (in-list σs)])
                    (match-define (join-res seen Δ j) (⊔ ⊔seen ρ Γ τ σ))
                    (values Δ j)))
         (join-res ⊔seen Δ (mk-TVariant #f n j (⊔trust tr1 tr0)))]
        ;; Make Λs agree on a name and abstract the result.
        [((TΛ: _ x st oa) (TΛ: _ _ ss oa))
         (define fresh (gensym 'joinΛ))
         (define tv (mk-TFree #f fresh))
         (match-define (join-res seen Δ j) (⊔* (open-scope st tv)
                                             (open-scope ss tv)))
         (join-res seen Δ (mk-TΛ #f x (abstract-free j fresh) oa))]
        ;; If not an abstraction, unify.
        [((TΛ: _ x st oa) _) (⊔* (oa (open-scope st (TUnif (gensym) T⊥))) σ)]
        [(_ (TΛ: _ x ss oa)) (⊔* τ (oa (open-scope ss (TUnif (gensym) T⊥))))]
        ;; distribute unions
        [((TUnion: _ ts) _)
         (define-values (Δ τs)
           (for/acc ([Γ Γ] [#:type list])
               ([t (in-list ts)])
             (match-define (join-res _ Δ tσ) (⊔ ⊔seen ρ Γ t σ))
             (values Δ tσ)))
         (define-values (Θ U) (*TUnion Δ #f τs))
         (join-res ⊔seen Θ U)]
        [(_ (TUnion: _ ts))
         (define-values (Δ τs)
           (for/acc ([Γ Γ] [#:type list τs])
               ([t (in-list ts)])
             (match-define (join-res _ Δ τt) (⊔ ⊔seen ρ Γ τ t))
             (values Δ τt)))
         (define-values (Θ U) (*TUnion Δ #f τs))
         (join-res ⊔seen Θ U)]
        ;; map and set are structural
        [((TMap: _ fd fr fext) (TMap: _ td tr text))
         (match-define (join-res dseen Δ jd) (⊔* fd td))
         (match-define (join-res rseen Θ jr) (⊔ dseen ρ Δ fr tr))
         (join-res rseen Θ (mk-TMap #f jd jr (⊔b fext text)))]
        [((TSet: _ t fext) (TSet: _ s text))
         (match-define (join-res seen Δ j) (⊔* t s))
         (join-res seen Δ (mk-TSet j (⊔b fext text)))]
        ;; The join of two recursive types requires them agreeing on their variable.
        [((Tμ: _ x sτ ftr fn) (Tμ: _ _ sσ ttr tn))
         (define fresh (gensym 'joinμ))
         (define tv (mk-TFree #f fresh))
         (match-define (join-res seen Δ j) (⊔* (open-scope sτ tv) (open-scope sσ tv)))
         (join-res seen
                   Δ
                   (mk-Tμ #f x
                          (abstract-free j fresh)
                          (⊔trust ftr ttr)
                          (min fn tn)))]
        ;; Named types are like recursive types, but trickier to get the name agreement right.
        [((TName: _ x) _) #:when (hash-has-key? ρ x)
        (⊔* (hash-ref ρ x) σ)]
       [(_ (TName: _ x)) #:when (hash-has-key? ρ x)
        (⊔* τ (hash-ref ρ x))]
       [((TName: _ x) (TName: _ y))
        (define fresh (gensym 'join-name))
        (define tv (mk-TFree #f fresh))
        (match-define (join-res seen Δ m)
                      (⊔ ⊔seen (hash-set (hash-set ρ x tv) y tv) Γ
                               (hash-ref us x) (hash-ref us y)))
        ;; Promote the free type variable to a type name (it can be anywhere now)
        (for ([(x τ) (in-hash (hash-copy us))])
          (hash-set! us x (free->x (mk-TName #f fresh) τ
                                   #:pred (λ (x) (eq? x fresh)))))
        (join-res seen Δ m)]
        [((? needs-resolve?) _) (resolve-join τ σ)]
        [(_ (? needs-resolve?)) (resolve-join σ τ)]
        ;; Maintain invariant that heap allocation annotations are only one deep.
        [((THeap: _ taddr0 tag0 τ) (THeap: _ taddr1 tag1 σ))
         (match-define (join-res seen Δ j) (⊔* taddr0 taddr1))
         (define (both)
           (join-res
            seen
            Δ
            (mk-TUnion #f (list (*THeap 'join-theap0 #f taddr0 tag0 τ)
                                (*THeap 'join-theap1 #f taddr1 tag1 σ)))))
         (match j
           [(? TUnion?) (both)]
           [(? TAddr? ta)
            (define tag (⋈flat tag0 tag1))
            (cond
             [(unmapped? tag) (both)]
             [else
              (match-define (join-res seen* Δ j) (⊔* τ σ))
              (join-res seen* Δ (*THeap 'join-theap #f ta tag j))])]
           [bad (error 'type-join "Non-TAddr join? ~a ~a => ~a" taddr0 taddr1 bad)])]
        [((? TAddr? τ) (? TAddr? σ))
         (define-values (Δ U) (*TUnion Γ #f (list τ σ)))
         (join-res ⊔seen Δ (combine-taddr τ σ (λ (τ σ) U)))]
        [((TWeak: _ τ) (TWeak: _ σ))
         (match-define (join-res seen Δ j) (⊔* τ σ))
         (join-res seen Δ (mk-TWeak #f j))]
        ;; Upcast to TWeak
        [(_ (TWeak: _ σ))
         (match-define (join-res seen Δ j) (⊔* τ σ))
         (join-res seen Δ (mk-TWeak #f j))]
        [((TWeak: _ τ) _)
         (match-define (join-res seen Δ j) (⊔* τ σ))
         (join-res seen Δ (mk-TWeak #f j))]
        [(_ _)
         (define-values (Δ U) (*TUnion Γ #f (list τ σ)))
         (join-res ⊔seen Δ U)])]))
  ⊔)

;; type-join: Type Type -> Type
;; Form the least-upper-bound of two types.
(define (type-join Γ τ σ)
  (match-define (join-res _ Δ τσ)
                ((type-join-aux (Language-user-spaces (current-language)))
                 (set) ⊥eq Γ τ σ))
  (values Δ τσ))

(define (type-join* Γ τs #:seen [⊔seen (set)])
  (define tj (type-join-aux (Language-user-spaces (current-language))))
  (define (rec ⊔seen Γ τs acc)
    (match τs
      ['() (values Γ acc)]
      [(cons τ τs*)
       (match-define (join-res seen Δ j) (tj ⊔seen ⊥eq Γ τ acc))
       (rec seen Δ τs* j)]))
  (rec ⊔seen Γ τs T⊥))

;(trace type-join*)

(struct meet-res (⊓seen Γ τ) #:transparent)

(define (type-meet-aux us E<: ⊔seen)
  (define (⊓ ⊓seen ρ Γ τ σ)
    (define (⊓* τ σ) (⊓ ⊓seen ρ Γ τ σ))
    (define (resolve-meet r τ)
      (define pair (cons r τ))
      (⊓ (set-add ⊓seen pair) ρ Γ (resolve r) τ))
   (cond
    [(and (TError? τ) (TError? σ))
     (meet-res ⊓seen Γ (TError (append (TError-msgs τ) (TError-msgs σ))))]
    ;; XXX: Can't use <:? to short-cut since it doesn't fill in unknowns!
    [(equal? (apply-ctx Γ τ) (apply-ctx Γ σ)) (meet-res ⊓seen Γ τ)]
    [(set-member? ⊓seen (cons τ σ)) (meet-res ⊓seen Γ T⊥)]
    [else
     (match* (τ σ)
       [((? T⊤?) _) (meet-res ⊓seen Γ σ)]
       [(_ (? T⊤?)) (meet-res ⊓seen Γ τ)]
       [((? T⊥?) _) (meet-res ⊓seen Γ T⊥)]
       [(_ (? T⊥?)) (meet-res ⊓seen Γ T⊥)]
       [((TVariant: _ n τs tr0) (TVariant: _ n σs tr1))
        #:when (and (= (length τs) (length σs))
                    (implies (and tr0 tr1) (equal? tr0 tr1)))
        (define-values (Δ m)
          (for/acc ([Γ Γ] [#:type list])
                   ([τ (in-list τs)]
                    [σ (in-list σs)])
                   (match-define (meet-res seen Δ m) (⊓ ⊓seen ρ Γ τ σ))
                   (values Δ m)))
        (meet-res ⊓seen Δ (mk-TVariant #f n m (⊓trust tr1 tr0)))]
       ;; Make Λs agree on a name and abstract the result.
       [((TΛ: _ x st oa) (TΛ: _ _ ss oa))
        (define fresh (gensym 'joinΛ))
        (define tv (mk-TFree #f fresh))
        (match-define (meet-res seen Δ m) (⊓* (open-scope st tv)
                                            (open-scope ss tv)))
        (meet-res seen Δ (mk-TΛ #f x (abstract-free m fresh) oa))]
       ;; If not both abstractions, start at ⊤ and narrow.
       ;; FIXME
       [((TΛ: _ _ st oa) _) (⊓* (oa (open-scope st (TUnif (gensym) T⊤))) σ)]
       [(_ (TΛ: _ _ ss oa)) (⊓* τ (oa (open-scope ss (TUnif (gensym) T⊤))))]
        ;; distribute unions
       [((TUnion: _ ts) _)
        (define-values (Δ ms)
          (for/fold ([Γ Γ] [ms '()])
              ([t (in-list ts)])
            (match-define (meet-res _ Δ m) (⊓ ⊓seen ρ Γ t σ))
            (values Δ (cons m ms))))
        (define-values (Θ j) (type-join* Δ ms #:seen ⊔seen))
        (meet-res ⊓seen Θ j)]
       [(_ (TUnion: _ ts))
        (define-values (Δ ms)
          (for/fold ([Γ Γ] [ms '()])
              ([t (in-list ts)])
            (match-define (meet-res _ Δ m) (⊓ ⊓seen ρ Γ τ t))
            (values Δ (cons m ms))))
        (define-values (Θ m) (type-join* Δ ms #:seen ⊔seen))
        (meet-res ⊓seen Θ m)]
       ;; map and set are structural
       [((TMap: _ fd fr fext) (TMap: _ td tr text))
        (match-define (meet-res dseen Δ dm) (⊓* fd td))
        (match-define (meet-res rseen Θ rm) (⊓ dseen ρ Δ fr tr))
        (meet-res rseen Θ (mk-TMap #f dm rm (⊓b fext text)))]
       [((TSet: _ t fext) (TSet: _ s text))
        (match-define (meet-res seen Δ m) (⊓* t s))
        (meet-res seen Δ (mk-TSet #f m (⊓b fext text)))]
       ;; The join of two recursive types requires them agreeing on their variable.
       [((Tμ: _ x sτ ftr fn) (Tμ: _ _ sσ ttr tn))
        (define fresh (gensym 'joinμ))
        (define tv (mk-TFree #f fresh))
        (match-define (meet-res seen Δ m) (⊓* (open-scope sτ tv)
                                            (open-scope sσ tv)))
        (meet-res seen Δ
                  (mk-Tμ #f x
                         (abstract-free m fresh)
                         (⊓trust ftr ttr)
                         (min fn tn)))]
       [((TName: _ x) _) #:when (hash-has-key? ρ x)
        (⊓* (hash-ref ρ x) σ)]
       [(_ (TName: _ x)) #:when (hash-has-key? ρ x)
        (⊓* τ (hash-ref ρ x))]
       [((TName: _ x) (TName: _ y))
        (define fresh (gensym 'join-name))
        (define tv (mk-TFree #f fresh))
        (match-define (meet-res seen Δ m)
                      (⊓ ⊓seen (hash-set (hash-set ρ x tv) y tv) Γ
                               (hash-ref us x) (hash-ref us y)))
        ;; Promote the free type variable to a type name (it can be anywhere now)
        (for ([(x τ) (in-hash (hash-copy us))])
          (hash-set! us x (free->x (mk-TName #f fresh) τ
                                   #:pred (λ (x) (eq? x fresh)))))
        (meet-res seen Δ m)]
       
       [((? needs-resolve?) _) (resolve-meet τ σ)]
       [(_ (? needs-resolve?)) (resolve-meet σ τ)]
       [((THeap: _ taddr0 tag0 τ) (THeap: _ taddr1 tag1 σ))
        (match-define (meet-res seen Δ tm) (⊓* taddr0 taddr1))
         (match tm
           [(? TAddr? ta)
            (match-define (meet-res seen* Θ inner) (⊓ seen ρ Δ τ σ))
            (define tag (⋈flat tag0 tag1))
            (meet-res 
             seen*
             Θ
             (if (or (T⊥? inner) (unmapped? tag))
                 T⊥ ;; XXX: don't heap-allocate bottom?
                 (*THeap 'meet-theap #f ta tag inner)))]
           [(? T⊥?) (meet-res seen Δ T⊥)]
           [bad (error 'type-meet "Non-TAddr meet? ~a ~a => ~a" taddr0 taddr1 bad)])]
       [((TAddr: _ space0 mm0 em0) (TAddr: _ space1 mm1 em1))
         (define space (⋈flat space0 space1))
         (define mm (⋈flat mm0 mm1))
         (define em (⋈flat em0 em1))
         (meet-res
          ⊓seen
          Γ
          (if (or (unmapped? space) (unmapped? mm) (unmapped? em))
              T⊥
              (mk-TAddr #f space mm em)))]
       [((TExternal: _ τname) (TExternal: _ σname))
        (meet-res
         ⊓seen
         Γ
         (cond [(set-member? E<: (cons τ σname)) τ]
               [(set-member? E<: (cons σ τname)) σ]
               [else T⊥]))]
       [(_ (TExternal: _ name))
        (meet-res ⊓seen Γ (if (set-member? E<: (cons τ name))
                              τ
                              T⊥))]
       [((TExternal: _ name) _)
        (meet-res ⊓seen Γ (if (set-member? E<: (cons σ name))
                              σ
                              T⊥))]
       [((TWeak: _ τ) (TWeak: _ σ))
        (match-define (meet-res seen Δ m) (⊓* τ σ))
        (meet-res seen Δ (mk-TWeak #f m))]
       ;; XXX: Downcast out of weak?
       [(_ (? permissive?)) (meet-res ⊓seen Γ τ)]
       [((? permissive?) _) (meet-res ⊓seen Γ σ)]
       [(_ _)
        (unless (and τ σ) (error 'type-meet "Bad type ~a ~a" τ σ))
        (meet-res ⊓seen Γ T⊥)])]))
;  (trace ⊓)
  ⊓)

(define (type-meet Γ τ σ)
  (define L (current-language))
  (match-define (meet-res _ Δ m)
                ((type-meet-aux
                  (Language-user-spaces L)
                  (Language-E<: L)
                  (set))
                 (set) ⊥eq Γ τ σ))
#;
  (when (T⊥? res)
    (printf "Meet ⊥: ~a, ~a~%" τ σ))
  (values Δ m))
(define (trace-type-meet!) (trace type-meet))
(define (untrace-type-meet!) (untrace type-meet))
