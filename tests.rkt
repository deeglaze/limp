#lang racket/base
(require racket/match
         racket/pretty
         racket/sandbox
         racket/set
         rackunit
         syntax/parse
         "common.rkt"
         "language.rkt"
         "mkv.rkt"
         "parser.rkt"
         "tast.rkt"
         "tc.rkt"
         "types.rkt")

(with-limits 10 1024
 (define (parse-type stx [unames ∅] [enames ∅] [meta-table #hasheq()] #:use-lang? [use-lang? #f])
   (define-values (unames* enames* meta-table*)
     (if use-lang?
         (match-let ([(Language _ ES _ US _ MT _) (current-language)])
           (values (hash-key-set US) (hash-key-set ES) MT))
         (values unames enames meta-table)))
   (syntax-parse stx
     [(~var t (TopPreType unames* enames* meta-table*)) (attribute t.t)]))
 (define (parse-expr stx)
   (syntax-parse stx
     [(~var e (Expression-cls (current-language) #f)) (attribute e.e)]))

 ;; (foo a (List a))
 (define foo-a-list-a
   (mk-TVariant #f 'foo (list (mk-TFree #f 'a #f) 
                              (mk-TCut #f
                                       (mk-TName #f 'List #f)
                                       (mk-TFree #f 'a #f)))
                'untrusted))

 (check-equal? foo-a-list-a
               (parse-type #'(foo a (#:inst List a)) (set 'List)))

 ;; (foo x y)
 (define foo-x-y
   (mk-TVariant #f 'foo (list (mk-TFree #f 'x #f) (mk-TFree #f 'y #f)) 'untrusted))

 (check-equal? foo-x-y (parse-type #'(foo x y)))

 ;; (foo ⊤ ⊤)
 (define foo-tt (mk-TVariant #f 'foo (list T⊤ T⊤) 'untrusted))
 (check-equal? foo-tt (parse-type #'(foo #:⊤ #:⊤)))

(type-print-verbosity 2)
(pattern-print-verbosity 2)
(expr-print-verbosity 2)

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
                 (Language #hash() #hash() ∅ (make-hash us-test) us-test  #hash() (make-hash))])
   (check-equal?
    (apply set (lang-variants-of-arity (mk-TVariant #f 'foo (list T⊤ T⊤) 'dc)))
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
                 #'([Expr (app Expr Expr) x (lam x Expr) #:bounded]
                    [(x) #:external Name #:parse identifier?]
                    [Value (Clo x Expr Env)]
                    [(ρ) Env (#:map Name Value #:externalize)]
                    [List (#:Λ X (#:U (Nil) (Cons X (#:inst List X))))]
                    [(φ) Frame (ar Expr Env) (fn Value)]
                    [(κ) Kont (#:inst List Frame)]
                    [State (ev Expr Env Kont)
                           (co Kont Value)
                           (ap x Expr Env Value Kont)]))])
  (define R
    (parse-reduction-relation #'([#:--> (ev (app e0 e1) ρ κ)
                                        (ev e0 ρ (Cons (ar e1 ρ) κ))]
                                 [#:--> (ev (lam y e) ρ κ)
                                        (co κ (Clo y e ρ))]
                                 [#:--> #:name var-lookup
                                        (ev (#:and (#:has-type Name) x) ρ κ)
                                        (co κ (#:map-lookup ρ x))]

                                 [#:--> (co (Cons (ar e ρ) κ) v)
                                        (ev e ρ (Cons (fn v) κ))]
                                 [#:--> (co (Cons (fn (Clo z e ρ)) κ) v)
                                        (ap z e ρ v κ)]

                                 [#:--> #:name fun-app
                                        (ap w e ρ v κ)
                                        (ev e (#:extend ρ w v) κ)])))
  (check-true
   (set-member?
    (hash-ref (recursive-nonrecursive
               (Language-user-spaces
                (current-language)))
              (Space 'List)
              ∅)
    (Ref 'List))
   "List is recursive")

  (define Sτ (resolve (parse-type #'State #:use-lang? #t)))
  (define R** (tc-rules #hash() #hash() R Sτ Sτ))
  (pretty-print R**)

  (report-all-errors R**)

  (language->mkV R** void)))
