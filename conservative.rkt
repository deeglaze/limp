#lang racket/base
(require racket/match
         racket/set
         "alloc-rules.rkt"
         "common.rkt"
         "language.rkt"
         "tast.rkt"
         "tc.rkt"
         "types.rkt"
         "self-reference.rkt")
(provide (all-defined-out))

#|

How do we transform the semantics to use as many exposed addresses as possible
when we know which positions /should/ be heap allocated?

INVARIANT: at this point, all expressions have tags, the semantics is monomorphized,
and we have a map from tags to immediate subexpressions that must be heap-allocated.

Example (CEK):

 ([#:--> (ev (app e0 e1) ρ κ)
        (ev e0 ρ (Cons #:tag appL (ar e1 ρ) κ))]
 [#:--> (ev (lam y e) ρ κ)
        (co κ (Clo y e ρ))]
 [#:--> #:name var-lookup
        (ev (#:and (#:has-type Name) x) ρ κ)
        (co κ (#:map-lookup ρ x))]

 [#:--> (co (Cons (ar e ρ) κ) v)
        (ev e ρ (Cons #:tag appR (fn v) κ))]
 [#:--> (co (Cons (fn (Clo z e ρ)) κ) v)
        (ap z e ρ v κ)]

 [#:--> #:name fun-app
        (ap w e ρ v κ)
        (ev e (#:extend ρ #:tag ext w v) κ)])

To heap-allocate: appL.1, appR.1, and ext.value

The state type must change to accomodate the rewritten types.

The first stab at the rules, heap-allocating but using implicit addressing everywhere:

 ([#:--> (ev (app e0 e1) ρ κ)
         (ev e0 ρ (Cons #:tag appL (ar e1 ρ) a))
         [#:where a (#:alloc #:delay #:structural)]
         [#:update a κ]]
  [#:--> (ev (lam y e) ρ κ)
         (co κ (Clo y e ρ))]
  [#:--> #:name var-lookup
         (ev (#:and (#:has-type Name) x) ρ κ)
         (co κ (#:map-lookup ρ x))]

  [#:--> (co (Cons (ar e ρ) κ) v)
         (ev e ρ (Cons #:tag appR (fn v) a))
         [#:where a (#:alloc #:delay #:structural)]
         [#:update a κ]]
  [#:--> (co (Cons (fn (Clo z e ρ)) κ) v)
         (ap z e ρ v κ)]

  [#:--> #:name fun-app
         (ap w e ρ v κ)
         (ev e (#:extend ρ #:tag ext w a) κ)
         [#:where a (#:alloc #:delay #:structural)]
         [#:update a v]])

This doesn't typecheck. We have to change some types. Which types do we change?

Let's do a forward flow analysis to see where we need to do lookups.
The abstract values are types.
Every expression's type starts at ⊥.

Every variable gets joined with the type that it is put in.

Rule 1:
The state type is
lhs: (ev (app e0:⊥ e1:⊥) ρ:⊥ κ:⊥)
->
rhs: state type is (ev e0!(app ⊥ ⊥) ⊥ (Cons (ar ⊥ ⊥) (#:addr #:delay #:structural)))

Rule 2:
the state type is
lhs: (ev (U (app ⊥ ⊥) (lam y:⊥ e:⊥)) ρ:⊥ κ:(Cons (ar ⊥ ⊥) (#:addr #:delay #:structural)))
rhs: (U
      (ev e!(U (app ⊥ ⊥) (lam ⊥ ⊥)) ⊥ (Cons (ar ⊥ ⊥) (#:addr #:delay #:structural)))
      (co (Cons (ar ⊥ ⊥) (#:addr #:delay #:structural)) (Clo ⊥ ⊥ ⊥)))

Rule 3:
the state type is
lhs: (U
      (ev (U (app ⊥ ⊥) (lam ⊥ ⊥) x:Name) ρ:⊥ κ:(Cons (ar ⊥ ⊥) (#:addr #:delay #:structural)))
      (co (Cons (ar ⊥ ⊥) (#:addr #:delay #:structural)) (Clo ⊥ ⊥ ⊥)))
rhs: (U
      (ev x!(U (app ⊥ ⊥) (lam ⊥ ⊥) x:Name) ρ!(map ⊥ ⊥) (Cons (ar ⊥ ⊥) (#:addr #:delay #:structural)))
      (co (Cons (ar ⊥ ⊥) (#:addr #:delay #:structural)) (Clo ⊥ ⊥ ⊥)))

Rule 4:
lhs: (U
      (ev (U (app ⊥ ⊥) (lam ⊥ ⊥) Name) (map ⊥ ⊥) (Cons (ar ⊥ ⊥) (#:addr #:delay #:structural)))
      (co (Cons (ar e:⊥ ρ:⊥) κ:(#:addr #:delay #:structural)) v:(Clo ⊥ ⊥ ⊥)))
rhs: (U
      (ev (U (app ⊥ ⊥) (lam ⊥ ⊥) Name) (map ⊥ ⊥) (Cons (U (ar ⊥ ⊥) (fn (Clo ⊥ ⊥ ⊥))) (#:addr #:delay #:structural)))
      (co (Cons (ar e:⊥ ρ:⊥) κ:(#:addr #:delay #:structural)) (Clo ⊥ ⊥ ⊥)))

Rule 5:
lhs: (U
      (ev (U (app ⊥ ⊥) (lam ⊥ ⊥) Name) (map ⊥ ⊥) (Cons (U (ar ⊥ ⊥) (fn (Clo ⊥ ⊥ ⊥))) (#:addr #:delay #:structural)))
      (co (Cons (U (ar ⊥ ⊥) (fn v:(Clo z:⊥ e:⊥ ρ:⊥)) (#:addr #:delay #:structural)) (Clo ⊥ ⊥ ⊥)))
|#

;; Rewrite semantics to introduce allocations and updates.
;; This is not well-typed. We need the THeap types to be infectious.
(define (add-AU vh eh sh vtaddr etaddr staddr)
  (define vh-ct (Check vtaddr))
  (define eh-ct (Check etaddr))
  (define sh-ct (Check staddr))

  (define (add-AU-rules rules) (map add-AU-rule rules))
  (define (add-AU-rule rule)
    (match-define (Rule sy name lhs rhs bus) rule)
    (Rule sy name lhs (add-AU-expr rhs) (add-AU-bus bus)))

  (define (add-AU-bus bus) (map add-AU-bu bus))

  (define (add-AU-bu bu)
    (match bu
      [(Update sy k e) (Update sy (add-AU-expr k) (add-AU-expr e))]
      [(Where sy p e) (Where sy p (add-AU-expr e))]))

  (define (heap-alloc e ct tag)
    (define x (gensym 'temp))
    (define a (gensym 'tempa))
    ;; We heap allocate e, so we transform it into
    ;; (let ([#:where $x e] [#:where $a (alloc)] [#:update $a $x]) $a)
    ;; where $ means a fresh identifier.

    ;; All implicitly allocated expressions are now given the THeap type.
    ;; We use this type to propagate heap allocations and dereferences.
    (define-values (ct* eτ)
      (match (πcc e)
        [(THeap: sy taddr eτ)
         (values (Check taddr) (mk-THeap sy taddr eτ))]
        [τ (values ct (mk-THeap #f (πct ct) τ))]))
    (define xct (Check eτ))
    (define sy (with-stx-stx e))
    (ELet sy (Trust eτ)
          (list (Where sy (PName sy xct x) (add-AU-expr e))
                (Where sy
                       (PName sy ct* a)
                       (EAlloc sy ct* tag))
                (Update sy (ERef sy ct* a) (ERef sy xct x)))
          (ERef sy ct* a)))
  
  (define (heap-alloc-list es indices ct tag)
    (let build ([es es] [indices (sort (set->list indices) <)] [i 0] [rev-es* '()])
      (match indices
        ['() (rev-append rev-es* (map add-AU-expr es))]
        [(cons ind inds)
         (unless (pair? es)
           (error 'heap-alloc-list "More indices than exprs ~a at ~a" indices tag))
         (define-values (e* inds*)
           (if (= i ind)
               (values (heap-alloc (car es) ct (cons tag i)) inds)
               (values (add-AU-expr (car es)) indices)))
         (build (cdr es) inds* (add1 i) (cons e* rev-es*))])))

  (define (add-AU-expr e)
    (match e
      [(EVariant sy ct n tag τs es)
       (define indices (hash-ref vh tag ∅))
       (define es* (heap-alloc-list es indices vh-ct tag))
       ;(define ct* (Check (mk-TVariant #f n (map πcc es*) #f))) ;; trust doesn't matter now.
       (EVariant sy #f n tag τs es*)]
      [(EExtend sy _ m tag k v)
       (define indices (hash-ref eh tag ∅))
       (match-define (list k* v*) (heap-alloc-list (list k v) indices eh-ct tag))
       ;(define ct* (Check (mk-TMap #f (πcc k*) (πcc v*) #f))) ;; externalization doesn't matter now.
       (EExtend sy #f (add-AU-expr m) tag k* v*)]
      [(ESet-add sy _ e tag es)
       (define indices (hash-ref sh tag ∅))
       (define es* (heap-alloc-list es indices sh-ct tag))
       (ESet-add sy #f (add-AU-expr e) tag es*)]

      ;; TODO: get translate metafunction output types for this.
      [(ECall sy _ mf τs es) (ECall sy #f mf τs (map add-AU-expr es))]
      ;; boilerplate
      [(or (? EEmpty-Map?) (? EEmpty-Set?) (? EAlloc?) (? ERef?)) e]
      [(EStore-lookup sy ct k lm) (EStore-lookup sy ct (add-AU-expr k) lm)]
      [(ELet sy _ bus body)
       (define body* (add-AU-expr body))
       ;(define ct* (Check (πcc body*)))
       (ELet sy #f (add-AU-bus bus) body*)]
      [(EMatch sy _ de rules)
       (define rules* (add-AU-rules rules))
       ;(define ct* (Check (type-join* (map (compose πcc Rule-rhs) rules*))))
       (EMatch sy #f (add-AU-expr de) rules*)]
      [(ESet-union sy _ es) (ESet-union sy #f (map add-AU-expr es))]
      [(ESet-intersection sy _ e es) (ESet-intersection sy #f (add-AU-expr e) (map add-AU-expr es))]
      [(ESet-subtract sy _ e es) (ESet-subtract sy #f (add-AU-expr e) (map add-AU-expr es))]
      [(ESet-member sy _ e v) (ESet-member sy #f (add-AU-expr e) (add-AU-expr v))]
      [(EMap-lookup sy _ m k) (EMap-lookup sy #f (add-AU-expr m) (add-AU-expr k))]
      [(EMap-has-key sy _ m k) (EMap-has-key sy #f (add-AU-expr m) (add-AU-expr k))]
      [(EMap-remove sy _ m k) (EMap-remove sy #f (add-AU-expr m) (add-AU-expr k))]
      [_ (error 'add-AU-expr "Unrecognized expression form: ~a" e)]))

  add-AU-rules)

(define (language->add-AU R metafunctions)
  (define-values (vh eh sh) (language->rules R metafunctions))
  (report-rules vh eh sh)
  (define vtaddr (mk-TAddr #f 'limp 'delay 'structural))
  (define etaddr (mk-TAddr #f 'limp 'delay 'structural))
  (define staddr (mk-TAddr #f 'limp 'delay 'structural))
  (define add-AU-rules (add-AU vh eh sh vtaddr etaddr staddr))
  (values (add-AU-rules R)
          (for/list ([mf (in-list metafunctions)])
            (match-define (Metafunction name τ rules) mf)
            (Metafunction name τ (add-AU-rules rules)))))

;; Get the new "State" type, and clear ou
(define (join-rhs-clear-lhs R metafunctions)
  (parameterize ([ignore-checks? #t])
    (define Sτ (type-join* (map (compose πcc Rule-rhs) R)))
    (printf "New state type ~a~%" Sτ)
    (tc-language R metafunctions Sτ)))

(define (iterate R metafunctions [i 0])
  (printf "Itr ~a~%" i)
  (define-values (R* metafunctions*) (join-rhs-clear-lhs R metafunctions))
  (if (and (equal? R R*) (equal? metafunctions metafunctions*))
      (values R* metafunctions*)
      (iterate R* metafunctions* (add1 i))))
