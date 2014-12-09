#lang racket/base
(require racket/list
         racket/match
         racket/pretty
         racket/sandbox
         racket/set
         rackunit
         syntax/parse
         "alloc-rules.rkt"
         "common.rkt"
         "insert-coercions.rkt"
         "language.rkt"
         "mkv.rkt"
         "parser.rkt"
         "self-reference.rkt"
         "tast.rkt"
         "tc.rkt"
         "types.rkt")

;; If there are any time or space leaks, kill the tests.
(with-limits 40 1024
 (define (parse-type stx [unames ∅] [enames ∅] [meta-table #hasheq()] #:use-lang? [use-lang? #f])
   (define-values (unames* enames* meta-table*)
     (if use-lang?
         (match-let ([(Language _ ES US _ _ MT _) (current-language)])
           (values (hash-key-set US) (hash-key-set ES) MT))
         (values unames enames meta-table)))
   (syntax-parse stx
     [(~var t (TopPreType #hash() unames* enames* meta-table*)) (attribute t.t)]))
 (define (parse-expr stx)
   (syntax-parse stx
     [(~var e (Expression-cls (current-language) #f)) (attribute e.e)]))

(type-print-verbosity 2)
(pattern-print-verbosity 3)
(expr-print-verbosity 3)

 ;; (foo a (List a))
 (define foo-a-list-a
   (mk-TVariant #f 'foo (list (mk-TFree #f 'a) 
                              (mk-TCut #f
                                       (mk-TName #f 'List)
                                       (mk-TFree #f 'a)))
                'untrusted))

 (check-equal? foo-a-list-a
               (parse-type #'(foo a (#:inst List a)) (set 'List)))

 ;; (foo x y)
 (define foo-x-y
   (mk-TVariant #f 'foo (list (mk-TFree #f 'x) (mk-TFree #f 'y)) 'untrusted))

 (check-equal? foo-x-y (parse-type #'(foo x y)))

 ;; (foo ⊤ ⊤)
 (define foo-tt (mk-TVariant #f 'foo (list T⊤ T⊤) 'untrusted))
 (check-equal? foo-tt (parse-type #'(foo #:⊤ #:⊤)))

 (define list-a
   (mk-TΛ #f 'a (abstract-free (*TRUnion #f
                                         (list (mk-TVariant #f 'blah (list) 'untrusted)
                                               foo-a-list-a))
                               'a
                               limp-default-Λ-addr)))
 (check-equal? (parse-type #`(#:Λ a (#:∪ (blah) #,foo-a-list-a)))
        list-a
        "Unquoting")

 (check-equal? (type-join foo-tt
                          (parse-type #'(#:Λ (x y) (foo x y))))
               foo-tt)

 (define us-test
   ;; List = Λ a (U (blah) (foo a (List a))
   (list
     (cons 'List list-a)
     ;; Blah = (U ⊤ (foo ⊤ ⊤))
     ;; This foo will (should) be forgotten
     (cons 'Blor (*TRUnion #f (list T⊤ foo-tt)))
     ;; Cord = Λ x Λ y (U (bar ⊤) (foo x y))
     (cons 'Cord (quantify-frees (parse-type #`(#:∪ (bar #:⊤) #,foo-x-y)) '(y x)))))

 (check-equal? (type-meet foo-tt foo-x-y) foo-x-y)
 (check-equal? (type-join foo-tt foo-x-y) foo-tt)

 (check-true
  (T⊤? (*TRUnion #f (list T⊤ foo-tt)))
  "Simplify union with ⊤")

 ;; Fails because simplification doesn't heed language
 (parameterize ([current-language
                 (Language #hash() #hash() (make-hash us-test) us-test ∅ #hash() (make-hash))])
   (check-equal?
    (apply set (lang-variants-of-arity (mk-TVariant #f 'foo (list T⊤ T⊤) #f)))
    (set (quantify-frees foo-x-y '(y x))
         (quantify-frees foo-a-list-a '(a)))
    "Simplified")

   (define xτ (parse-type #'(#:inst Cord (bloo) (blah)) (set 'List 'Blor 'Cord)))
   (define Γ (hasheq 'x xτ))
   (check expr-α-equal?
          ((tc-expr Γ #hasheq())
           (parse-expr #'(#:match x [(foo y z) z])))
          (parse-expr #'(#:ann (blah) (#:match (#:ann (#:inst Cord (bloo) (blah)) x)
                                               [(#:ann (foo (bloo) (blah))
                                                       (foo (#:ann (bloo) y)
                                                            (#:ann (blah) z)))
                                                (#:ann (blah) z)])))))

(define CEK-lang (parse-language
                  #'([Expr (app Expr Expr) x (lam x Expr) #:bounded]
                     [(x) #:external Name #:parse identifier?]
                     [Value (Clo x Expr Env)]
                     [(ρ) Env (#:map Name Value #:externalize)]
                     [List (#:Λ X (#:U (Nil) (Cons X (#:inst List X))))]
                     [(φ) Frame (ar Expr Env) (fn Value)]
                     [(κ) Kont (#:inst List Frame)]
                     [State (ev Expr Env Kont)
                            (co Kont Value)
                            (ap x Expr Env Value Kont)])))

(define CEK-Rstx
  #'([#:--> (ev (app e0 e1) ρ κ)
            (ev e0 ρ (Cons (ar e1 ρ) κ))]
     [#:--> (ev (lam y e) ρ κ)
            (co κ (Clo y e ρ))]
     [#:--> #:name var-lookup
            (ev (#:and (#:has-type Name) x) ρ κ)
            (#:ann State (co κ (#:cast Value (#:map-lookup ρ x))))]

     [#:--> (co (Cons (ar e ρ) (#:deref κ #:implicit)) v)
            (ev e ρ (Cons (fn v) κ))]
     [#:--> (co (Cons (fn (Clo z e ρ)) κ) v)
            (ap z e ρ v κ)]

     [#:--> #:name fun-app
            (ap w e ρ v κ)
            (ev e (#:extend ρ w v) κ)]))

;; typecheck without heap allocation.
(parameterize ([instantiations (make-hash)])
  (parameterize ([current-language CEK-lang])
    (define CEK0 (parse-reduction-relation CEK-Rstx))
    (define Sτ0 (resolve (parse-type #'State #:use-lang? #t)))
    (define-values (CEK*0 metafunctions*0)
      (tc-language CEK0 '() Sτ0))         ;  (pretty-print CEK*)
    (report-all-errors CEK*0)

    ;; typecheck with heap allocation
    (parameterize ([current-language (heapify-language CEK-lang #f)])
      (pretty-print (Language-user-spaces (current-language)))
      (define CEK ((heapify-rules
                    limp-default-deref-addr
                    limp-default-deref-addr
                    limp-default-deref-addr
                    #f)
                   (parse-reduction-relation CEK-Rstx)))
      (define Sτ (resolve (parse-type #'State #:use-lang? #t)))
      (parameterize ([instantiations (make-hash)])
        (define-values (CEK* metafunctions*)
          (parameterize ([check-for-heapification? #t])
            (tc-language CEK '() Sτ)))  ;  (pretty-print CEK*)

        (pretty-print CEK*)
        (displayln "Reporting for heapification")
        (report-all-errors CEK*)
        (define-values (CEK2 metafunctions2)
          (coerce-language CEK* metafunctions*))
        (report-all-errors CEK2)
        (displayln "Transformed")
        (pretty-print (solidify-language (current-language)))
        (pretty-print CEK2)))))

(parameterize ([current-language
                (parse-language
                 #'([Expr (app Expr Expr) x (lam x Expr)]
                    [(x) #:external Name]))])
  (define e
    ((tc-expr (hasheq 'x limp-default-deref-addr)
              #hasheq())
     (parse-expr #'(#:match x [(#:deref (#:cast Expr (app e0 e1)) #:explicit #:delay #:identity) e1]))))
  (report-all-errors e)
  (displayln "Little test")
  (pretty-print e))

(parameterize ([current-language
                (parse-language
                 #'([Expr (app Expr Exprs) x (lam xs Expr) #:bounded]
                    [Exprs (#:inst TList Expr)]
                    [(x) #:external Name #:parse identifier?]
                    [(xs) Names (#:inst TList Name)]
                    [Value (Clo xs Expr Env)]
                    [Values (#:inst TList Value)]
                    [(ρ) Env (#:map Name Value #:externalize)]
                    [TList (#:Λ [X #:trusted] (#:U (Nil) (TCons X (#:inst TList X))))
                           #:trust-construction]
                    [List (#:Λ X (#:U (Nil) (Cons X (#:inst List X))))]
                    [(φ) Frame (ev Exprs Values Env) (fn Value)]
                    [(κ) Kont (#:inst List Frame)]
                    [State (ev Expr Env Kont)
                           (co Kont Value)
                           (ap xs Expr Env Values Kont)]))])

  (check-true
   (self-referential? (resolve (parse-type #'(#:inst TList Value) #:use-lang? #t)))
   "TList[Value] is recursive")

 (define CESK
   (parse-reduction-relation #'([#:--> (ev (app e0 es) ρ κ)
                                       (ev e0 ρ (Cons (ev es (Nil) ρ) κ))]
                                [#:--> (ev (lam ys e) ρ κ)
                                       (co κ (Clo ys e ρ))]
                                [#:--> #:name var-lookup
                                       (ev (#:and (#:has-type Name) x) ρ κ)
                                       (co κ (#:map-lookup ρ x))]

                                [#:--> (co (Cons (ev (TCons e es) vs ρ) κ) v)
                                       (ev e ρ (Cons (ev es (TCons v vs) ρ) κ))]
                                [#:--> (co (Cons (ev (Nil) vs ρ) κ) v)
                                       (ap zs e ρ vs* κ)
                                       [#:where (TCons (Clo zs e ρ) vs*)
                                                (#:call reverse #:inst [Value] vs)]]

                                [#:--> #:name fun-app
                                       (ap ws e ρ vs κ)
                                       (ev e (#:call extend* #:inst [Name Value] ρ ws vs) κ)])))

 (define match-thru
   ((tc-expr (hasheq 'x (parse-type #'Value #:use-lang? #t)) #hasheq())
     (parse-expr #'(#:match x [(Clo xs e (#:map-with y (Clo ys e* ρ) ρ*)) e*]))))
 (report-all-errors match-thru)

 (define Sτ (resolve (parse-type #'State #:use-lang? #t)))
 (define metafunctions
   (list
    (parse-metafunction
     #'(reverse : #:∀ (A) (#:inst TList A) → (#:inst TList A)
                [(reverse xs) (#:call rev-app #:inst [A] xs (Nil))]))
    (parse-metafunction
     #'(rev-app : #:∀ (A) (#:inst TList A) (#:inst TList A) → (#:inst TList A)
                [(rev-app (Nil) acc) acc]
                [(rev-app (TCons x xs) acc)
                 (#:call rev-app #:inst [A] xs (TCons x acc))]))
    (parse-metafunction
     #'(extend* : #:∀ (A B) (#:map A B) (#:inst TList A) (#:inst TList B) → (#:map A B)
                [(extend* ρ (Nil) (Nil)) ρ]
                [(extend* ρ (TCons a as) (TCons b bs))
                 (#:call extend* #:inst [A B] (#:extend ρ a b) as bs)]))))

 (displayln "Last one")

 
 (define-values (CESK* metafunctions*)
   (tc-language CESK metafunctions Sτ))
 (pretty-print metafunctions*)
 (pretty-print CESK*)

 (report-all-errors
  (append (append-map (compose peel-scopes Metafunction-rules) metafunctions*)
          CESK*))

 (language->mkV CESK* metafunctions* void)))
