#lang racket/base
(require "common.rkt"
         "language.rkt"
         "self-reference.rkt"
         "tast.rkt"
         "types.rkt"
         racket/dict
         racket/set
         racket/match
         racket/pretty)
(provide heapify-language)

;; ROUNDTOIT
;; Unfolding and subtyping has difficult interactions that I don't have time to mess with
;; before graduating.

(define (trusted? τ)
  (match τ
    [(or (TVariant: _ _ _ (not (? untrusted?)))
         (Tμ: _ _ _ (not (? untrusted?)) _))
     #t]
    [_ #f]))

(define (heapify-τ vtaddr etaddr staddr heapify-nonrec? τ)
  (define (heap-alloc sy t taddr)
    (match t
      [(? THeap?) t]
      [(? heap-allocate?) (mk-THeap sy taddr 'dc t)]
      [t (self t)]))
  (define (try-alloc? τ tr)
    (and (untrusted? tr)
         (or heapify-nonrec?
             (and (self-referential? τ)
                  (not (trusted? τ))))))
  (define (self τ)
    (match τ
      [(or (? TAddr?) (? TExternal?) (? TFree?) (? TName?) (? THeap?)) τ]
      [(TVariant: sy n ts tr)
       (if (try-alloc? τ tr)
           (mk-TVariant sy n (for/list ([t (in-list ts)])
                               (heap-alloc sy t vtaddr)) tr)
           (mk-TVariant sy n (map self ts) tr))]
      [(TMap: sy t-dom t-rng ext)
       (mk-TMap sy (heap-alloc sy t-dom etaddr) (heap-alloc sy t-rng etaddr) ext)]
      [(TSet: sy tv ext)
       (mk-TSet sy (heap-alloc sy tv staddr) ext)]
      [(Tμ: sy x st tr n)
       (define x* (if (try-alloc? τ tr)
                      (gensym x)
                      (cons 'trusted (gensym x))))
       (mk-Tμ sy x (abstract-free (self (open-scope st (mk-TFree sy x*))) x*) tr n)]
      ;; a quantified type is just all the known instantiations' heapifications.
      [(TΛ: sy x st)
       (mk-TΛ sy x ;; Add a name just so Cuts line up.
              (Scope
               (*TRUnion sy
                         (for/list ([t (in-set (hash-ref (or (instantiations) ⊥) τ ∅))])
                           (self (open-scope st t))))))]
      [(TSUnion: sy ts) (*TSUnion sy (map self ts))]
      [(TRUnion: sy ts) (*TRUnion sy (map self ts))]
      [(TCut: sy t u) (mk-TCut sy (self t) (self u))]
      [(? TBound?) 
       (error 'self-referential? "We shouldn't see deBruijn indices here ~a" τ)]
      [_ (error 'heapify-τ "Bad type ~a" τ)]))
  (self τ))

(define (heapify-language L heapify-nonrec?)
  (define us (Language-ordered-us L))
  (define vtaddr (mk-TAddr #f 'limp 'delay 'structural))
  (define etaddr (mk-TAddr #f 'limp 'delay 'structural))
  (define staddr (mk-TAddr #f 'limp 'delay 'structural))
  (define ordered
    (for/list ([(name ty) (in-dict us)])
      (cons name (heapify-τ vtaddr etaddr staddr
                            heapify-nonrec?
                            ty))))
  ;; We use self-referential checks for heapification, just like expression allocation rules.
  (struct-copy Language L
               [user-spaces (make-hash ordered)]
               [ordered-us ordered]))
