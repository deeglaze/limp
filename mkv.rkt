#lang racket/base
(require "alloc-rules.rkt"
         "common.rkt"
         "language.rkt"
         "self-reference.rkt"
         "tast.rkt"
         "types.rkt"
         racket/set
         racket/match
         racket/pretty
         racket/trace)
(provide language->mkV)
#|
Transform a language into a skeleton mkV, with a feedback loop for improving the allocation rules.

The primary difficulty in this type system is determining which positions of
collection constructions are "recursive," i.e., allow unbounded nesting.

|#

#|
A map or set may not be externalized if there is a path from the map to itself
without an intervening variant constructor.
|#

(define (language->mkV R metafunctions alloc)
  (define-values (vtag->rule etag->rule stag->rule)
    (language->rules R metafunctions))

  ;; Now when we encounter an ECall, EVariant or EExtend, we can look up
  ;; the translated type and see if any components are TAddr with a true implicit? field.
  ;; All implicit fields must be allocated and stored.
  ;; If we output this as a metafunction, then we have to extend the alloc function.
  ;; If we output this as a Racket function, then we don't,
  ;;  but we have to use the store updating functions.

  ;;

  ;; Each rule could be the same on the left and different on the right.
  ;; We need to know the rule to generate the address? Sure, this comes from alloc.

  (values
   ;; mkV
   `(λ (ς σ μ ρ δ σΔ μΔ n tag ts)
       (case tag
         ,(for/list ([(tag positions) (in-hash vtag->rule)])
            (define addrs
              (for/hash ([i (in-set positions)])
                (values i (alloc tag i))))
            `[(,tag)
              (define ts*
                ,(for/fold ([ts* 'ts])
                     ([i (in-set positions)])
                   `(list-update ,ts* ,i (QAddr ,(hash-ref addrs i) 'delay 'structural))))
              (define σΔ*
                ,(for/fold ([σΔ* 'σΔ])
                     ([i (in-set positions)])
                   `(hash-update ,σΔ* ,(hash-ref addrs i) (list-ref ts ,i))))
              (define μΔ*
                ,(for/fold ([μΔ* 'μΔ])
                     ([i (in-set positions)])
                   `(μbump ,μΔ* ,(hash-ref addrs i))))
              (values (Variant n ts*) ⊥ σΔ* μΔ*)])))
   ;; TODO: finish mkExt
   `(λ (ς σ μ ρ δ σΔ μΔ f tag k v)
       (case tag
         ,(for/list ([(tag positions) (in-hash etag->rule)])
            `[(,tag)
              (define f* ???)
              (values (Map f*) ⊥ σΔ* μΔ*)])))
   ;; TODO: mkAdd
   ))
