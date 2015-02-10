#lang racket/base
(provide <:? trace-<:? untrace-<:?)
(require racket/match
         racket/trace
         racket/set
         (only-in racket/bool implies)
         "common.rkt" "language.rkt" "types.rkt")

;; The TAPL approach to equirecursive subtyping.
;; Uses language axioms for external subtyping.
(define (<:? τ σ)
  (define L (current-language))
  ((<:?-aux (Language-E<: L)) ∅ τ σ))

(define trace-aux #f)
(define (trace-<:?) (set! trace-aux #t) (trace <:?))
(define (untrace-<:?) (set! trace-aux #f) (untrace <:?))

(define ((<:?-aux E<:) A τ σ)
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
        [((? needs-resolve?) _)
         (<:?-aux (grow-A) (resolve τ) σ)]
        [(_ (? needs-resolve?))
         (<:?-aux (grow-A) τ (resolve σ))]
        [((THeap: _ taddr0 tag0 τ) (THeap: _ taddr1 tag1 σ))
         (and (not (unmapped? (⋈flat tag0 tag1)))
              (seq A
                   (<:?-aux A taddr0 taddr1)
                   (<:?-aux A τ σ)))]
        ;; No implicit casts from heap/non-heap
        [((TUnion: _ ts) _)
         (and (for/and ([t (in-list ts)])
                (<:?-aux A t σ))
              A)]
        [(_ (TUnion: _ σs))
         (and (for/or ([σ (in-list σs)])
                (<:?-aux A τ σ))
              A)]
        [((TAddr: _ space0 mm0 em0) (TAddr: _ space1 mm1 em1))
         (and (not (or (unmapped? (⋈flat space0 space1))
                       (unmapped? (⋈flat mm0 mm1))
                       (unmapped? (⋈flat em0 em1))))
              A)]
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
        [((TΛ: _ _ sτ oa) (TΛ: _ _ sσ oa))
         (define name (mk-TFree #f (gensym 'dummy)))
         (<:?-aux A (open-scope sτ name) (open-scope sσ name))]
        [(_ (TExternal: _ name)) (and (set-member? E<: (cons τ name)) A)]
        [((TWeak: _ τ) (TWeak: _ σ)) (<:?-aux A τ σ)]
        [(_ (TWeak: _ σ)) (<:?-aux A τ σ)] ;; non-weak types can be upcast to weak types
        [((? permissive?) _) A]
        [((THeap: _ taddr0 tag0 τ) _) #:when (not (check-for-heapification?))
         (<:?-aux A τ σ)]
        [(_ (THeap: _ taddr1 tag1 σ)) #:when (not (check-for-heapification?))
         (<:?-aux A τ σ)]
        [(_ _) #f])]))
  (when trace-aux (trace <:?-aux))
  ;;(trace <:?-aux)
  (<:?-aux A τ σ))
