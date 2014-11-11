#lang racket/base
(require rackunit racket/set syntax/parse racket/sandbox
         racket/pretty
         "common.rkt" "language.rkt" "parser.rkt" "tast.rkt" "tc.rkt" "types.rkt")

(with-limits 10 1024
 (define (parse-type stx [unames ∅] [enames ∅] [meta-table #hasheq()])
   (syntax-parse stx
     [(~var t (TopPreType unames enames meta-table)) (attribute t.t)]))
 (define (parse-expr stx)
   (syntax-parse stx
     [(~var e (Expression-cls (current-language) #f)) (attribute e.e)]))

 ;; (foo a (List a))
 (define foo-a-list-a
   (mk-TVariant #f 'foo (list (mk-TFree #f 'a #f) 
                              (mk-TCut #f
                                       (mk-TName #f 'List #f)
                                       (mk-TFree #f 'a #f))) #f #f))

 (check-equal? foo-a-list-a
               (parse-type #'(foo a (#:inst List a)) (set 'List)))

 ;; (foo x y)
 (define foo-x-y
   (mk-TVariant #f 'foo (list (mk-TFree #f 'x #f) (mk-TFree #f 'y #f)) #f #f))

 (check-equal? foo-x-y (parse-type #'(foo x y)))

 ;; (foo ⊤ ⊤)
 (define foo-tt (mk-TVariant #f 'foo (list T⊤ T⊤) #f #f))
 (check-equal? foo-tt (parse-type #'(foo #:⊤ #:⊤)))

 (define list-a
   (mk-TΛ #f 'a (abstract-free (*TRUnion #f
                                         (list (mk-TVariant #f 'blah (list) #f #f)
                                               foo-a-list-a))
                               'a)))
 (check-equal? (parse-type #`(#:Λ a (#:∪ (blah) #,foo-a-list-a)))
               list-a
               "Unquoting")

 (check-equal? (type-join foo-tt
                          (parse-type #'(#:Λ (x y) (foo x y))))
               foo-tt)

 (define us-test
   ;; List = Λ a (U (blah) (foo a (List a))
   (make-hash
    (list
     (cons 'List list-a)
     ;; Blah = (U ⊤ (foo ⊤ ⊤))
     ;; This foo will (should) be forgotten
     (cons 'Blor (*TRUnion #f (list T⊤ foo-tt)))
     ;; Cord = Λ x Λ y (U (bar ⊤) (foo x y))
     (cons 'Cord (quantify-frees (parse-type #`(#:∪ (bar #:⊤) #,foo-x-y)) '(y x))))))

 (check-equal? (type-meet foo-tt foo-x-y) foo-x-y)
 (check-equal? (type-join foo-tt foo-x-y) foo-tt)

 (check-true
  (T⊤? (*TRUnion #f (list T⊤ foo-tt)))
  "Simplify union with ⊤")

(pattern-print-verbosity 2)
(expr-print-verbosity 2)

 ;; Fails because simplification doesn't heed language
 (parameterize ([current-language
                 (Language #hash() #hash() ∅ us-test #hash() (make-hash))])
   (check-equal?
    (apply set (lang-variants-of-arity (mk-TVariant #f 'foo (list T⊤ T⊤) 'dc 'dc)))
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

(parameterize ([current-language
                (parse-language
                 #'([Expr (app Expr Expr) x (lam x Expr)]
                    [(x) #:external Name #:parse identifier?]
                    [Value (Clo x Expr Env)]
                    [(ρ) Env (#:map Name Value)]
                    [List (#:Λ X (#:U (Nil) (Cons X (#:inst List X))))]
                    [(φ) Frame (ar Expr Env) (fn Value)]
                    [(κ) Kont (#:inst List Frame)]
                    [State (ev Expr Env Kont)
                           (co Kont Value)
                           (ap x Expr Env Value Kont)]))])
  (define R
    (parse-reduction-relation #'([#:--> (ev (app e0 e1) ρ κ)
                                        (ev e0 ρ (Cons (ar e1 ρ) κ))]
                                 [#:--> (ev (lam x e) ρ κ)
                                        (co κ (Clo x e ρ))]
                                 [#:--> #:name var-lookup
                                        (ev (#:cast Name x) ρ κ)
                                        (co κ (#:lookup (#:map-lookup ρ x)))]

                                 [#:--> (co (Cons (ar e ρ) κ) v)
                                        (ev e ρ (Cons (fn v) κ))]
                                 [#:--> (co (Cons (fn (Clo x e ρ)) κ) v)
                                        (ap x e ρ v κ)]

                                 [#:--> (ap x e ρ v κ)
                                        (ev e (#:extend ρ x a) κ)
                                        [#:where a (#:alloc)]
                                        [#:update a v]])))
  (pretty-print R)
  (void)))
