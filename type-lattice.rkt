#lang racket/base
(provide type-join type-meet trace-type-meet! untrace-type-meet!)
(require racket/match racket/set racket/trace
         (only-in racket/bool implies)
         "common.rkt" "language.rkt" "subtype.rkt" "types.rkt" "type-formers.rkt")

(struct join-res (τ seen) #:transparent)

(define (type-join-aux us)
  (define (⊔ τ σ ρ ⊔seen)
    (define (resolve-join r τ)
      (⊔ (resolve r) τ ρ (set-add ⊔seen (cons r τ))))
    (define (unify τ σ)
      (cond
       [(type-contains? σ τ)
        (join-res (TError (list "Cyclic unification")) ⊔seen)]
       [else
        (match-define (join-res out seen) (⊔ (TUnif-τ τ) σ ρ ⊔seen))
        (set-TUnif-τ! τ out)
        (set-TUnif-tag! τ (gensym)) ;; updated
        (join-res τ seen)]))
    (cond
     [(and (TError? τ) (TError? σ))
      (join-res (TError (append (TError-msgs τ) (TError-msgs σ)))
                ⊔seen)]
     [(set-member? ⊔seen (cons τ σ)) (join-res T⊤ ⊔seen)]   
     ;; If comparable, choose the larger type without allocating new type structure.
     [(<:? τ σ) (join-res σ ⊔seen)]
     [(<:? σ τ) (join-res τ ⊔seen)]
     [else
      (match* (τ σ)
        [((TVariant: _ n τs tr0) (TVariant: _ n σs tr1))
         #:when (and (= (length τs) (length σs))
                     (implies (and tr0 tr1) (equal? tr0 tr1)))
         (let each ([τs τs] [σs σs]
                    ;;[⊔seen ⊔seen]
                    [rev-join '()])
           (match* (τs σs)
             [('() '())
              (join-res (mk-TVariant #f n (reverse rev-join)
                                     (⊔trust tr1 tr0))
                        ⊔seen)]
             [((cons τ τs) (cons σ σs))
              (match-define (join-res j seen) (⊔ τ σ ρ ⊔seen))
              (each τs σs
                    ;;seen
                    (cons j rev-join))]))]
        ;; Make Λs agree on a name and abstract the result.
        [((TΛ: _ x st oa) (TΛ: _ _ ss oa))
         (define fresh (gensym 'joinΛ))
         (define tv (mk-TFree #f fresh))
         (match-define (join-res j seen) (⊔ (open-scope st tv)
                                            (open-scope ss tv) ρ
                                            ⊔seen))
         (join-res (mk-TΛ #f x (abstract-free j fresh) oa) seen)]
        ;; If not an abstraction, unify.
        [((TΛ: _ x st oa) _) (⊔ (oa (open-scope st (TUnif (gensym) T⊥))) σ ρ ⊔seen)]
        [(_ (TΛ: _ x ss oa)) (⊔ τ (oa (open-scope ss (TUnif (gensym) T⊥))) ρ ⊔seen)]
        [((? TUnif?) _) (unify τ σ)]
        [(_ (? TUnif?)) (unify σ τ)]
        ;; distribute unions
        [((TUnion: _ ts) _)
         (join-res (*TUnion #f (for/list ([t (in-list ts)])
                                 (join-res-τ (⊔ t σ ρ ⊔seen))))
                   ⊔seen)]
        [(_ (TUnion: _ ts))
         (join-res (*TUnion #f (for/list ([t (in-list ts)])
                                 (join-res-τ (⊔ τ t ρ ⊔seen))))
                   ⊔seen)]
        ;; map and set are structural
        [((TMap: _ fd fr fext) (TMap: _ td tr text))
         (match-define (join-res jd dseen) (⊔ fd td ρ ⊔seen))
         (match-define (join-res jr rseen) (⊔ fr tr ρ dseen))
         (join-res (mk-TMap #f jd jr (⊔b fext text)) rseen)]
        [((TSet: _ t fext) (TSet: _ s text))
         (match-define (join-res j seen) (⊔ t s ρ ⊔seen))
         (join-res (mk-TSet j (⊔b fext text)) seen)]
        ;; The join of two recursive types requires them agreeing on their variable.
        [((Tμ: _ x sτ ftr fn) (Tμ: _ _ sσ ttr tn))
         (define fresh (gensym 'joinμ))
         (define tv (mk-TFree #f fresh))
         (match-define (join-res j seen) (⊔ (open-scope sτ tv) (open-scope sσ tv) ρ ⊔seen))
         (join-res (mk-Tμ #f x
                          (abstract-free j fresh)
                          (⊔trust ftr ttr)
                          (min fn tn))
                   seen)]
        ;; Named types are like recursive types, but trickier to get the name agreement right.
        [((TName: _ x) _) #:when (hash-has-key? ρ x)
        (⊔ (hash-ref ρ x) σ ρ ⊔seen)]
       [(_ (TName: _ x)) #:when (hash-has-key? ρ x)
        (⊔ τ (hash-ref ρ x) ρ ⊔seen)]
       [((TName: _ x) (TName: _ y))
        (define fresh (gensym 'join-name))
        (define tv (mk-TFree #f fresh))
        (match-define (join-res m seen) (⊔ (hash-ref us x) (hash-ref us y)
                                           (hash-set (hash-set ρ x tv) y tv)
                                           ⊔seen))
        ;; Promote the free type variable to a type name (it can be anywhere now)
        (for ([(x τ) (in-hash (hash-copy us))])
          (hash-set! us x (free->x (mk-TName #f fresh) τ
                                   #:pred (match-lambda [(TFree: _ x) (eq? x fresh)]))))
        (join-res m seen)]
        [((? needs-resolve?) _) (resolve-join τ σ)]
        [(_ (? needs-resolve?)) (resolve-join σ τ)]
        ;; Maintain invariant that heap allocation annotations are only one deep.
        [((THeap: _ taddr0 tag0 τ) (THeap: _ taddr1 tag1 σ))
         (match-define (join-res j seen) (⊔ taddr0 taddr1 ρ ⊔seen))
         (define (both)
           (join-res
            (mk-TUnion #f (list (*THeap 'join-theap0 #f taddr0 tag0 τ)
                                (*THeap 'join-theap1 #f taddr1 tag1 σ)))
            seen))
         (match j
           [(? TUnion?) (both)]
           [(? TAddr? ta)
            (define tag (⋈flat tag0 tag1))
            (cond
             [(unmapped? tag)
              (both)]
             [else
              (match-define (join-res j seen*) (⊔ τ σ ρ seen))
              (join-res (*THeap 'join-theap #f ta tag j) seen*)])]
           [bad (error 'type-join "Non-TAddr join? ~a ~a => ~a" taddr0 taddr1 bad)])]
        [((? TAddr? τ) (? TAddr? σ))
         (join-res (combine-taddr τ σ (λ (τ σ) (*TUnion #f (list τ σ))))
                   ⊔seen)]
        [((TWeak: _ τ) (TWeak: _ σ))
         (match-define (join-res j seen) (⊔ τ σ ⊔seen))
         (join-res (mk-TWeak #f j) seen)]
        ;; Upcast to TWeak
        [(_ (TWeak: _ σ))
         (match-define (join-res j seen) (⊔ τ σ ⊔seen))
         (join-res (mk-TWeak #f j) seen)]
        [((TWeak: _ τ) _)
         (match-define (join-res j seen) (⊔ τ σ ⊔seen))
         (join-res (mk-TWeak #f j) seen)]
        [(_ _) (join-res (*TUnion #f (list τ σ)) ⊔seen)])]))
  ⊔)

;; type-join: Type Type -> Type
;; Form the least-upper-bound of two types.
(define (type-join τ σ)  
  (freeze (join-res-τ
           ((type-join-aux (Language-user-spaces (current-language)))
            τ σ ⊥eq (set)))
          *TUnion))

(define (type-join* τs #:seen [⊔seen (set)] #:no-freeze? [no-freeze? #f])
  (define tj (type-join-aux (Language-user-spaces (current-language))))
  (define (rec τs acc ⊔seen)
    (match τs
      ['() (if no-freeze? acc (freeze acc *TUnion))]
      [(cons τ τs*)
       (match-define (join-res j seen) (tj τ acc ⊥eq ⊔seen))
       (rec τs* j seen)]))
  (rec τs T⊥ ⊔seen))

;(trace type-join*)

(struct meet-res (τ ⊓seen) #:transparent)
;; Doesn't freeze afterwards
(define (type-meet-aux us E<: ⊔seen)
  (define (⊓ τ σ ρ ⊓seen)
    (define (resolve-meet r τ)
      (define pair (cons r τ))
      (⊓ (resolve r) τ ρ (set-add ⊓seen pair)))
;    (trace meet-named)
    (define (unify τ σ)
      (match-define (meet-res out seen) (⊓ (TUnif-τ τ) σ ρ ⊓seen))
      (set-TUnif-τ! τ out)
      (meet-res τ seen))
   (cond
    [(and (TError? τ) (TError? σ))
     (meet-res (TError (append (TError-msgs τ) (TError-msgs σ))) ⊓seen)]
    ;; XXX: Can't use <:? to short-cut since it doesn't fill in unknowns!
    [(equal? (freeze τ *TUnion) (freeze σ *TUnion)) (meet-res τ ⊓seen)]
    [(set-member? ⊓seen (cons τ σ)) (meet-res T⊥ ⊓seen)]
    [else
     (match* (τ σ)
       [((? T⊤?) _) (meet-res σ ⊓seen)]
       [(_ (? T⊤?)) (meet-res τ ⊓seen)]
       [((? T⊥?) _) (meet-res T⊥ ⊓seen)]
       [(_ (? T⊥?)) (meet-res T⊥ ⊓seen)]
       [((TVariant: _ n τs tr0) (TVariant: _ n σs tr1))
        #:when (and (= (length τs) (length σs))
                    (implies (and tr0 tr1) (equal? tr0 tr1)))
        (let each ([τs τs] [σs σs]
                   ;;[⊓seen ⊓seen]
                   [rev-met '()])
          (match* (τs σs)
            [('() '())
             (meet-res (mk-TVariant #f n (reverse rev-met) (⊓trust tr1 tr0)) ⊓seen)]
            [((cons τ τs) (cons σ σs))
             (match-define (meet-res m seen) (⊓ τ σ ρ ⊓seen))
             (each τs σs
                   ;;seen
                   (cons m rev-met))]))]
       ;; Make Λs agree on a name and abstract the result.
       [((TΛ: _ x st oa) (TΛ: _ _ ss oa))
        (define fresh (gensym 'joinΛ))
        (define tv (mk-TFree #f fresh))
        (match-define (meet-res m seen) (⊓ (open-scope st tv)
                                            (open-scope ss tv) ρ
                                            ⊓seen))
        (meet-res (mk-TΛ #f x (abstract-free m fresh) oa) seen)]
       ;; If not both abstractions, start at ⊤ and narrow.
       [((TΛ: _ _ st oa) _) (⊓ (oa (open-scope st (TUnif (gensym) T⊤))) σ ρ ⊓seen)]
       [(_ (TΛ: _ _ ss oa)) (⊓ τ (oa (open-scope ss (TUnif (gensym) T⊤))) ρ ⊓seen)]
       [((? TUnif?) _) (unify τ σ)]
       [(_ (? TUnif?)) (unify σ τ)]
       ;; distribute unions
       [((TUnion: _ ts) _)
        (meet-res
         (type-join* (for/list ([t (in-list ts)])
                       (meet-res-τ (⊓ t σ ρ ⊓seen)))
                     #:seen ⊔seen
                     #:no-freeze? #t)
         ⊓seen)]
       [(_ (TUnion: _ ts))
        (meet-res
         (type-join* (for/list ([t (in-list ts)])
                       (meet-res-τ (⊓ τ t ρ ⊓seen)))
                     #:seen ⊔seen
                     #:no-freeze? #t)
         ⊓seen)]
       ;; map and set are structural
       [((TMap: _ fd fr fext) (TMap: _ td tr text))
        (match-define (meet-res dm dseen) (⊓ fd td ρ ⊓seen))
        (match-define (meet-res rm rseen) (⊓ fr tr ρ dseen))
        (meet-res (mk-TMap #f dm rm (⊓b fext text)) rseen)]
       [((TSet: _ t fext) (TSet: _ s text))
        (match-define (meet-res m seen) (⊓ t s ρ ⊓seen))
        (meet-res (mk-TSet #f m (⊓b fext text)) seen)]
       ;; The join of two recursive types requires them agreeing on their variable.
       [((Tμ: _ x sτ ftr fn) (Tμ: _ _ sσ ttr tn))
        (define fresh (gensym 'joinμ))
        (define tv (mk-TFree #f fresh))
        (match-define (meet-res m seen) (⊓
                                          (open-scope sτ tv)
                                          (open-scope sσ tv)
                                          ⊓seen))
        (meet-res
         (mk-Tμ #f x
                (abstract-free m fresh)
                (⊓trust ftr ttr)
                (min fn tn))
         seen)]
       [((TName: _ x) _) #:when (hash-has-key? ρ x)
        (⊓ (hash-ref ρ x) σ ρ ⊓seen)]
       [(_ (TName: _ x)) #:when (hash-has-key? ρ x)
        (⊓ τ (hash-ref ρ x) ρ ⊓seen)]
       [((TName: _ x) (TName: _ y))
        (define fresh (gensym 'join-name))
        (define tv (mk-TFree #f fresh))
        (match-define (meet-res m seen) (⊓ (hash-ref us x) (hash-ref us y)
                                           (hash-set (hash-set ρ x tv) y tv)
                                           ⊓seen))
        ;; Promote the free type variable to a type name (it can be anywhere now)
        (for ([(x τ) (in-hash (hash-copy us))])
          (hash-set! us x (free->x (mk-TName #f fresh) τ
                                   #:pred (match-lambda [(TFree: _ x) (eq? x fresh)]))))
        (meet-res m seen)]
       
       [((? needs-resolve?) _) (resolve-meet τ σ)]
       [(_ (? needs-resolve?)) (resolve-meet σ τ)]
       [((THeap: _ taddr0 tag0 τ) (THeap: _ taddr1 tag1 σ))
        (match-define (meet-res tm seen) (⊓ taddr0 taddr1 ρ ⊓seen))
         (match tm
           [(? TAddr? ta)
            (match-define (meet-res inner seen*) (⊓ τ σ ρ seen))
            (define tag (⋈flat tag0 tag1))
            (meet-res 
             (if (or (T⊥? inner) (unmapped? tag))
                 T⊥ ;; XXX: don't heap-allocate bottom?
                 (*THeap 'meet-theap #f ta tag inner))
             seen*)]
           [(? T⊥?) (meet-res T⊥ seen)]
           [bad (error 'type-meet "Non-TAddr meet? ~a ~a => ~a" taddr0 taddr1 bad)])]
       [((TAddr: _ space0 mm0 em0) (TAddr: _ space1 mm1 em1))
         (define space (⋈flat space0 space1))
         (define mm (⋈flat mm0 mm1))
         (define em (⋈flat em0 em1))
         (meet-res
          (if (or (unmapped? space) (unmapped? mm) (unmapped? em))
              T⊥
              (mk-TAddr #f space mm em))
          ⊓seen)]
       [((TExternal: _ τname) (TExternal: _ σname))
        (meet-res
         (cond [(set-member? E<: (cons τ σname)) τ]
               [(set-member? E<: (cons σ τname)) σ]
               [else T⊥])
         ⊓seen)]
       [(_ (TExternal: _ name))
        (meet-res (if (set-member? E<: (cons τ name))
                      τ
                      T⊥)
                  ⊓seen)]
       [((TExternal: _ name) _)
        (meet-res (if (set-member? E<: (cons σ name))
                      σ
                      T⊥)
                  ⊓seen)]
       [((TWeak: _ τ) (TWeak: _ σ))
        (match-define (meet-res m seen) (⊓ τ σ ⊓seen))
        (meet-res (mk-TWeak #f m) seen)]
       ;; XXX: Downcast out of weak?
       [(_ (? permissive?)) (meet-res τ ⊓seen)]
       [((? permissive?) _) (meet-res σ ⊓seen)]
       [(_ _)
        (unless (and τ σ) (error 'type-meet "Bad type ~a ~a" τ σ))
        (meet-res T⊥ ⊓seen)])]))
;  (trace ⊓)
  ⊓)

(define (type-meet τ σ)
  (define L (current-language))
  (define res (freeze (meet-res-τ
                       ((type-meet-aux
                         (Language-user-spaces L)
                         (Language-E<: L)
                         (set))
                        τ σ ⊥eq (set)))
                      *TUnion))
#;
  (when (T⊥? res)
    (printf "Meet ⊥: ~a, ~a~%" τ σ))
  res)
(define (trace-type-meet!) (trace type-meet))
(define (untrace-type-meet!) (untrace type-meet))
