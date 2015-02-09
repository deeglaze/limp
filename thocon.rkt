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
         (only-in "tc.rkt" tc-expr)
         "tc-toplevel.rkt"
         "types.rkt")


(define (recognize-label stx)
  (syntax-case stx (quote)
    [(quote x) (identifier? #'x) #t]
    [_ #f]))

;(type-print-verbosity 3)

(with-limits 120 2048
 (parameterize ([current-language
                 (heapify-language
                  (parse-language
                   #'(;; Syntax
                      [(e) Expr (app Expr Exprs)
                       x
                       (lam xs Expr)
                       (smon ℓ ℓ Ssyn e)
                       (tmon e Tsyn)
                       (begine Expr Exprs)
                       (letrece LClauses Expr)
                       (ife Expr Expr Expr)
                       TCon-syntax
                       (primop Primop)
                       Datum
                       #:bounded]
                      [(cs) LClauses (NLC) (LC x Expr cs)]
                      [(Tsyn) TCon-syntax (bind Expr) (tpred Expr) (¬ Tsyn) (kl Tsyn) (· Tsyn Tsyn)
                       (∪ Tsyn Tsyn) (∩ Tsyn Tsyn) (⊥) (⊤) (ε)]

                      [(S) SCon (predv fnv) (-->/blessed Ss S ℓ η) (cons/c S S) (any/c)]
                      [(Ss) SCons (#:inst TList SCon)]
                      [(Ssyn) SCon-syntax (flat Expr) (--> Ssyns Ssyn ℓ Expr) (any/c)
                       (cons/c Ssyn Ssyn)]
                      [(Ssyns) SCon-syntaxes (#:inst TList Ssyn)]
                      [(es) Exprs (#:inst TList Expr)]
                      [(xs) Names (#:inst TList Name)]

                      ;; Values
                      [(T) TCon
                       (bindv (#:weak fnv)) (tpredv (#:weak fnv)) ;; HOASy way to do it.
                       (¬v T) (klv T)
                       (·v T T) (∪v T T) (∩v T T)
                       (⊥) (⊤) (ε) #:trust-construction]
                      [(fnv) Proc-Value (primop Primop) (Clo xs Expr Env) Blessed]
                      [Blessed (Clo/blessed ℓ ℓ (#:inst TList SCon) S ℓ η fnv)]
                      [event (call fnv Values) (ret fnv Value)]
                      [(v) Value
                       fnv T η
                       event
                       (LR-cell (#:addr #:expose #:identity)) ;; letrec without CESK
                       ;; automatically weak-boxes the arguments.
                       Primop Datum (cons Value Value)]
                      [(η) Timeline (timeline (#:addr #:expose #:identity))]
                      [(vs) Values (#:inst TList Value)]

                      ;; Components
                      [(ρ) Env (#:map Name Value #:externalize)]
                      [TList (#:Λ [X #:trusted] (#:U (Nil) (TCons X (#:inst TList X))))
                             #:trust-construction]
                      [List (#:Λ X (#:U (Nil) (Cons X (#:inst List X))))]
                    
                      ;; Frames
                      [(φ) Frame AFrame BFrame CFrame DFrame EFrame
                       HFrame LFrame PFrame SFrame VFrame]
                   
                      [(aφ) AFrame (arrk Ss S ℓ) (mkflat)]
                      [(bφ) BFrame (sk ℓ ℓ e ρ)]
                      [(cφ) CFrame (chDk ℓ ℓ S v) (consk v)]
                      [(dφ) DFrame (negt)
                       (∪₀ T event η ℓ) (∩₀ T event η ℓ)
                       (∪₁ T) (∩₁ T)
                       (seq2k T event η ℓ) (seqk T)]
                      [(eφ) EFrame (evk es vs ρ) (ifk e e ρ) (lrk x cs e ρ) (begink es ρ)
                       (wrapk ℓ ℓ S) (chret Blessed) (clo-to-bind) (clo-to-pred) (klk) (¬k)
                       (mkt Tsyn ρ) (firstT η)
                       (m·₀ Tsyn ρ) (m∩₀ Tsyn ρ) (m∪₀ Tsyn ρ)
                       (m·₁ T) (m∪₁ T) (m∩₁ T)]
                      [(hφ) HFrame (Checking) (sret Blessed) (ch*k Ss Blessed vs vs)]
                      [(lφ) LFrame (blret event) (blcall Blessed vs event)]
                      [(pφ) PFrame (mk-tcon) (pred-to-T)]
                      [(sφ) SFrame (negk Ssyns Ssyn ℓ e ρ Ss)
                       (mkd Ssyn ρ) (mkcons S) (timelinek Ss ℓ e ρ)]
                      [(vφ) VFrame (flatk v (predv fnv) ℓ)]

                      ;; Continuations
                      [(eκ) EKont (Halt) (ECons eφ eκ) (PCons pφ tκ) (VCons vφ cκ) (ACons aφ sκ)]
                      [(cκ) CKont (CCons cφ cκ) (HCons hφ eκ)]
                      [(tκ) TKont (τCons dφ tκ) (LCons lφ eκ)]
                      [(sκ) SKont (SCons sφ sκ) (BCons bφ eκ)]
                    
                      ;; States
                      [State (ans v)
                             (blame ℓ S v)
                             (tblame ℓ T event)
                           
                             (ev e ρ eκ)
                             (ev-syn Ssyn ρ sκ)
                             (coe eκ v)
                             (cod tκ T)
                             (coc cκ v)
                             (cos sκ S)
                             (send T event ℓ η tκ)
                             (check ℓ ℓ S v cκ)
                             (check-app (#:inst TList S) vs Blessed vs eκ)
                             (ap fnv vs eκ)]
                      ;; Externals
                      [(ℓ) #:external Label #:syntax recognize-label]
                      [(x) #:external Name #:syntax identifier?]
                      [(cons) #:external Cons-name #:syntax
                       (λ (stx) (and (identifier? stx) (free-identifier=? stx #'cons)))]
                      [#:external Datum
                                  #:syntax
                                  (λ (s)
                                     (with-handlers ([values (λ _ #f)])
                                       (define ev
                                         (parameterize
                                             ([sandbox-eval-limits (list 1 1)])
                                           (make-evaluator 'racket/base)))
                                       (define x
                                         (call-in-sandbox-context ev
                                                                  (λ () (eval-syntax s))))
                                       (or (symbol? x)
                                           (boolean? x)
                                           (number? x)
                                           (string? x)
                                           (null? x)
                                           (void? x))))]
                      [#:external Real #:syntax (λ (s) (real? (syntax-e #'s)))]
                      #:subtype* (boolean Real) Datum
                      [#:external Primop #:syntax
                                  (λ (s) (memv (syntax-e s) '(cons car cdr pair? null?
                                                                   not box? make-box unbox
                                                                   call? call-label call-fn call-args
                                                                   ret? ret-fn ret-label ret-value
                                                                   boolean? real? equal? set-box! <=
                                                                   add1 sub1 zero?
                                                                   new-timeline)))]
                      [#:external Real? #:syntax (λ (s) (eq? 'real? (syntax-e #'s)))]
                      #:subtype Real? Primop
                      #;[#:external Flat-Racket #:syntax (λ (s) #t)]
                      ))
                  #f)])

   (define CESK
     (parse-reduction-relation
      #'(
         [#:--> (ev e ρ κ)
                (#:match e
                         [(app e0 es)
                          (ev e0 ρ (ECons (evk es (Nil) ρ) κ))]
                         [(lam ys e*)
                          (coe κ (Clo ys e* ρ))]
                         [#:name var-lookup
                                 (#:has-type Name x)
                                 (coe κ (#:match (#:map-lookup ρ x)
                                                [(LR-cell a) (#:cast Value (#:lookup a #:delay))]
                                                [v v]))]
                         [(smon ℓ+ ℓ- S e*)
                          (ev-syn S ρ (BCons (sk ℓ+ ℓ- e* ρ) κ))]
                         [(tmon ηe Tsyn)
                          (ev ηe ρ (ECons (mkt Tsyn ρ) κ))]
                         [(ife g th el)
                          (ev g ρ (ECons (ifk th el ρ) κ))]
                         [(letrece (NLC) e*)
                          (ev e* ρ κ)]
                         [(letrece (#:name cs (LC x e* cs*)) body)
                          (ev e* ρ* (ECons (lrk x cs* body ρ*) κ))
                          [#:where ρ* (#:call clause-alloc ρ cs)]]
                         [(begine e0 es)
                          (ev e0 ρ (ECons (begink es ρ) κ))]
                         [(#:has-type Value v)
                          (coe κ v)]
                         [(bind e*)
                          (ev e* ρ (ECons (clo-to-bind) κ))]
                         [(tpred e*)
                          (ev e* ρ (ECons (clo-to-pred) κ))]
                         [(kl T)
                          (ev T ρ (ECons (klk) κ))]
                         [(¬ T)
                          (ev T ρ (ECons (¬k) κ))]
                         [(· T0 T1)
                          (ev T0 ρ (ECons (m·₀ T1 ρ) κ))]
                         [(∪ T0 T1)
                          (ev T0 ρ (ECons (m∪₀ T1 ρ) κ))]
                         [(∩ T0 T1)
                          (ev T0 ρ (ECons (m∩₀ T1 ρ) κ))])]

         [#:--> (coe (Halt) v) (ans v)]

         [#:--> (coe (ACons φ κ) v)
                (#:match φ
                         [(mkflat)
                          (cos κ (predv pred))
                          [#:where (#:has-type fnv pred) v]]
                         [(arrk Svs Sv ℓ)
                          (cos κ (-->/blessed (#:call reverse #:inst [S] Svs) Sv ℓ η))
                          [#:where (#:has-type Timeline η) v]])]

         [#:--> (coe (PCons φ κ) v)
                (#:match φ
                         [(mk-tcon)
                          (cod κ (#:cast TCon v))]
                         [(pred-to-T)
                          (cod κ (#:if v (ε) (⊥)))])]

         [#:--> (coe (VCons (flatk vc Sp ℓ-) κ) v)
                (#:if v
                      (coc κ vc)
                      (blame ℓ- Sp vc))]

         [#:--> (coe (ECons φ κ) v)
                (#:match φ
                         [(evk (TCons e es) vs ρ)
                          (ev e ρ (ECons (evk es (TCons v vs) ρ) κ))]
                         [(evk (Nil) vs ρ)
                          (ap fn vs* κ)
                          [#:where (TCons (#:has-type fnv fn) vs*)
                                   (#:call reverse #:inst [Value] vs)]]
                         [(ifk t e ρ)
                          (ev (#:if v t e) ρ κ)]
                         [(lrk x cs body ρ)
                          (#:match cs
                                   [(NLC) (ev body ρ κ)
                                    [#:where (LR-cell a) (#:map-lookup ρ x)]
                                    [#:update a v]]
                                   [(LC y e cs*) (ev e ρ (ECons (lrk y cs body ρ) κ))])]
                         [(clo-to-bind) (coe κ (bindv (#:cast fnv v)))]
                         [(clo-to-pred) (coe κ (tpredv (#:cast fnv v)))]
                         [(mkt T ρ)
                          (ev T ρ (ECons (firstT (#:cast Timeline v)) κ))]
                         [(firstT (timeline a))
                          (coe κ (#:external Datum (void)))
                          [#:update a v]]

                         [(m·₀ T ρ)
                          (ev T ρ (ECons (m·₁ (#:cast TCon v)) κ))]
                         [(m∪₀ T ρ)
                          (ev T ρ (ECons (m∪₁ (#:cast TCon v)) κ))]
                         [(m∩₀ T ρ)
                          (ev T ρ (ECons (m∩₁ (#:cast TCon v)) κ))]
                         [(m·₁ T)
                          (coe κ (·v T (#:cast TCon v)))]
                         [(m∪₁ T)
                          (coe κ (∪v T (#:cast TCon v)))]
                         [(m∩₁ T)
                          (coe κ (∩v T (#:cast TCon v)))]
                         [(begink es ρ)
                          (#:match es
                                   [(Nil) (coe κ v)]
                                   [(TCons e es*) (ev e ρ (ECons (begink es* ρ) κ))])]
                         [(chret (#:name fn (Clo/blessed ℓ- ℓ+ _ Sv+ _ η _)))
                          (check ℓ+ ℓ- Sv+ v (HCons (sret fn) κ))]
                         [(wrapk ℓ+ ℓ- Sv)
                          (check ℓ+ ℓ- Sv v (HCons (Checking) κ))])]

        
         [#:--> (cos (BCons (sk ℓ+ ℓ- e ρ) κ) Sv)
                (ev e ρ (ECons (wrapk ℓ+ ℓ- Sv) κ))]

         [#:--> (cos (SCons φ κ) Sv)
                (#:match φ
                         [(timelinek Svs ℓ e ρ)
                          (ev e ρ (ACons (arrk Svs Sv ℓ) κ))]
                         [(negk Ssyns S+ ℓ e ρ Svs-)
                          (#:match Ssyns
                                   [(Nil) (ev-syn S+ ρ (SCons (timelinek (TCons Sv Svs-) ℓ e ρ) κ))]
                                   [(TCons Ssyn Ssyns*)
                                    (ev-syn Ssyn ρ (SCons (negk Ssyns* S+ ℓ e ρ (TCons Sv Svs-)) κ))])]
                         [(mkd D ρ)
                          (ev-syn D ρ (SCons (mkcons Sv) κ))]
                         [(mkcons A)
                          (cos κ (cons/c A Sv))])]


         [#:--> (ev-syn S ρ κ)
                (#:match S
                         [(--> Ss- S+ ℓ e)
                          (#:match Ss-
                                   [(Nil) (ev-syn S+ ρ (SCons (timelinek (Nil) ℓ e ρ) κ))]
                                   [(TCons S- Ss-*)
                                    (ev-syn S- ρ (SCons (negk Ss-* S+ ℓ e ρ (Nil)) κ))])]
                         [(cons/c A D)
                          (ev-syn A ρ (SCons (mkd D ρ) κ))]
                         [(any/c) (cos κ (any/c))]
                         [(flat e) (ev e ρ (ACons (mkflat) κ))])]

         [#:--> (send T ev ℓ η κ)
                (#:match T
                         [(ε) (cod κ (⊥))]
                         [(⊥) (cod κ (⊥))]
                         [(⊤) (cod κ (⊤))]
                         [(bindv v) (ap v (TCons ev (Nil)) (PCons (mk-tcon) κ))]
                         [(klv T*) (send T* ev ℓ η (τCons (seqk T) κ))]
                         [(¬v T*) (send T* ev ℓ η (τCons (negt) κ))]
                         [(·v T₀ T₁) (send T₀ ev ℓ η (τCons φ κ))
                          [#:where φ (#:if (#:call ν?v T₀)
                                           (seq2k T₁ ev η ℓ)
                                           (seqk T₁))]]
                         [(∪v T₀ T₁) (send T₀ ev ℓ η (τCons (∪₀ T₁ ev η ℓ) κ))]
                         [(∩v T₀ T₁) (send T₀ ev ℓ η (τCons (∩₀ T₁ ev η ℓ) κ))]
                         [(tpredv v) (ap v (TCons ev (Nil)) (PCons (pred-to-T) κ))])]

         [#:--> (check-app (Nil)
                           (Nil)
                           (#:name fn (Clo/blessed ℓ- ℓ+ _ sv+ ℓ η clv)) vs-checked κ)
                (send (#:cast TCon (#:lookup a)) ev ℓ- η (LCons (blcall fn args-checked ev) κ))
                [#:where (timeline a) η]
                [#:where args-checked (#:call reverse #:inst [Value] vs-checked)]
                [#:where ev (call fn args-checked)]]
         [#:--> (check-app (TCons Sv- Svs-) (TCons v0 vs-to-check)
                           (#:name fn (Clo/blessed ℓ- ℓ+ _ _ _ _ _)) vs-checked κ)
                (check ℓ- ℓ+ Sv- v0 (HCons (ch*k Svs- fn vs-to-check vs-checked) κ))]

         [#:--> (check ℓ+ ℓ- S v κ)
                (#:match S
                         [(-->/blessed Svs- Sv+ ℓ η)
                          (#:match v
                                   [(#:name v* (Clo args _ _))
                                    (coc κ (Clo/blessed ℓ- ℓ+ Svs- Sv+ ℓ η v*))
                                    [#:when (#:call eq-len args Svs-)]]
                                   [(#:name v* (Clo/blessed _ _ args _ _ _ _))
                                    (coc κ (Clo/blessed ℓ- ℓ+ Svs- Sv+ ℓ η v*))
                                    [#:when (#:call eq-len args Svs-)]])]
                         [(cons/c A D)
                          (#:match v
                                   [(cons Av Dv) (check ℓ+ ℓ- A Av (CCons (chDk ℓ+ ℓ- D Dv) κ))]
                                   [_ (blame ℓ+ S v)])]
                         [(any/c) (coc κ v)]
                         [(#:name Sp (predv fn)) (ap fn (TCons v (Nil)) (VCons (flatk v Sp ℓ-) κ))])]

         [#:--> (coc (CCons φ κ) v)
                (#:match φ
                         [(chDk ℓ+ ℓ- D Dv)
                          (check ℓ+ ℓ- D Dv (CCons (consk v) κ))]
                         [(consk Av) (coc κ (cons Av v))])]
         [#:--> (coc (HCons φ κ) v)
                (#:match φ
                         [(ch*k Svs- fn vs-to-check vs-checked)
                          (check-app Svs- vs-to-check fn (TCons v vs-checked) κ)]
                         [(sret (#:name fn (Clo/blessed ℓ- ℓ+ _ _ ℓ η _)))
                          (send (#:cast TCon (#:lookup a)) event ℓ+ η (LCons (blret event) κ))
                          [#:where (timeline a) η]
                          [#:where event (ret fn v)]]
                         [(Checking) (coe κ v)])]

         [#:--> (cod (LCons φ κ) v)
                (#:match φ
                         [(blcall (#:name fn (Clo/blessed ℓ- ℓ+ _ Sv+ ℓ (timeline a) clv)) vs ev)
                          (#:if (#:call μ?v v)
                                (tblame ℓ- (#:cast TCon (#:lookup a)) ev)
                                (#:let ([#:update a v])
                                       (ap clv vs (ECons (chret fn) κ))))]
                         [(blret (#:name ev (ret (Clo/blessed _ ℓ+ _ _ _ (timeline a) _) rv)))
                          (#:if (#:call μ?v v)
                                (tblame ℓ+ (#:cast TCon (#:lookup a)) ev)
                                (#:let ([#:update a v])
                                       (coe κ rv)))])]
         [#:--> (cod (τCons φ κ) v)
                (#:match φ
                         [(negt) (cod κ (#:if (#:call ν?v v*)
                                              (⊥)
                                              (#:call mk¬v v*)))]
                         [(seqk T₁) (cod κ (#:call mk·v v* T₁))]
                         [(seq2k T₁ ev η ℓ-)
                          (send T₁ ev ℓ- η (τCons (∪₁ (#:call mk·v v* T₁)) κ))]
                         [(∪₀ T ev η ℓ-) (send T ev ℓ- η (τCons (∪₁ v*) κ))]
                         [(∩₀ T ev η ℓ-) (send T ev ℓ- η (τCons (∩₁ v*) κ))]
                         [(∪₁ T) (cod κ (#:call mk∪v T v*))]
                         [(∩₁ T) (cod κ (#:call mk∩v T v*))])
                [#:where v* (#:cast TCon v)]]
        
         [#:--> #:name fun-app
                (ap (Clo ws e ρ) vs κ)
                (ev e (#:call extend* #:inst [Name Value] ρ ws vs) κ)]
         [#:--> #:name prim-app
                (ap (primop p) vs κ)
                (coe κ (#:call δ p vs))]
         [#:--> #:name wrap-app
                (ap (#:name fn (Clo/blessed _ _ Svs- _ _ _ _)) vs κ)
                (check-app Svs- vs fn (Nil) κ)])))

   (define match-thru
     ((tc-expr (hasheq 'x (parse-type #'Value #:use-lang? #t)) #hasheq())
      (parse-expr #'(#:match x [(Clo xs e (#:map-with y (Clo ys e* ρ) ρ*)) e*]))))
   (report-all-errors match-thru)


   (define Sτ (resolve (parse-type #'State #:use-lang? #t)))
   (define metafunctions
     (map parse-metafunction
          (list
           #'(reverse : (#:∀ (A) (#:inst TList A) → (#:inst TList A))
                      [(reverse xs) (#:call rev-app #:inst [A] xs (Nil))])
           #'(rev-app : (#:∀ (A) (#:inst TList A) (#:inst TList A) → (#:inst TList A))
                      [(rev-app (Nil) acc) acc]
                      [(rev-app (TCons x xs) acc)
                       (#:call rev-app #:inst [A] xs (TCons #:inst [A] x acc))])
           #'(extend* : (#:∀ (A B) (#:map A B) (#:inst TList A) (#:inst TList B) → (#:map A B))
                      [(extend* ρ (Nil) (Nil)) ρ]
                      [(extend* ρ (TCons a as) (TCons b bs))
                       (#:call extend* #:inst [A B] (#:extend ρ a b) as bs)])
           #'(δ : (Primop Values → Value)
                [(δ (#:external Real?) (TCons v (Nil)))
                 (#:match v
                          [(#:has-type Real _) #t]
                          [_ #f])])
           #'(mk¬v : (TCon → TCon)
                   [(mk¬v (¬v (¬v (¬v T))))
                    (¬v (¬v T))]
                   [(mk¬v (⊥)) (⊤)]
                   [(mk¬v (⊤)) (ε)]
                   [(mk¬v T) (¬v T)])
           #'(mk∪v : (TCon TCon → TCon)
                 [(mk∪v T T) T]
                 [(mk∪v T₀ T₁) T₁ [#:when (#:call μ?v T₀)]]
                 [(mk∪v T₀ T₁) T₀ [#:when (#:call μ?v T₁)]]
                 [(mk∪v T₀ T₁) (∪v T₀ T₁)])
           #'(mk∩v : (TCon TCon → TCon)
                 [(mk∩v T T) T]
                 [(mk∩v (⊤) T₁) T₁]
                 [(mk∩v T₀ (⊤)) T₀]
                 [(mk∩v T₀ T₁) (∩v T₀ T₁)])
           #'(mk·v : (TCon TCon → TCon)
                   [(mk·v T₀ T₁)
                    (#:if (#:call μ?v T₀)
                          (⊥)
                          (#:if (#:call ν!?v T₀)
                                T₁
                                (·v T₀ T₁)))])
           #'(ν?v : (TCon → #:boolean)
                  [(ν?v (∪v T₀ T₁)) (#:if (#:call ν?v T₀)
                                          (#:external boolean #t)
                                          (#:call ν?v T₁))]
                  [(ν?v (∩v T₀ T₁)) (#:if (#:call ν?v T₀)
                                          (#:call ν?v T₁)
                                          (#:external boolean #f))]
                  [(ν?v (·v T₀ T₁)) (#:if (#:call ν?v T₀)
                                          (#:call ν?v T₁)
                                          (#:external boolean #f))]
                  [(ν?v (¬v _)) (#:external boolean #t)]
                  [(ν?v (ε)) (#:external boolean #t)]
                  [(ν?v (klv _)) (#:external boolean #t)]
                  [(ν?v _) (#:external boolean #f)])
           #'(ν!?v : (TCon → #:boolean)
                   [(ν!?v (ε)) (#:external boolean #t)]
                   [(ν!?v (klv T)) (#:call ν!?v T)]
                   [(ν!?v (¬v T)) (#:call μ?v T)]
                   [(ν!?v (∪v T₀ T₁)) (#:if (#:call ν!?v T₀)
                                            (#:call ν!?v T₁)
                                            (#:external boolean #f))]
                   [(ν!?v (·v T₀ T₁)) (#:if (#:call ν!?v T₀)
                                            (#:call ν!?v T₁)
                                            (#:external boolean #f))]
                   [(ν!?v (∩v T₀ T₁)) (#:if (#:call ν!?v T₀)
                                            (#:external boolean #t)
                                            (#:call ν!?v T₁))]
                   [(ν!?v _) (#:external boolean #f)])
           #'(μ?v : (TCon → #:boolean)
                  [(μ?v (⊥)) (#:external boolean #t)]
                  [(μ?v (∪v T₀ T₁)) (#:if (#:call μ?v T₀)
                                          (#:call μ?v T₁)
                                          (#:external boolean #f))]
                  [(μ?v (∩v T₀ T₁)) (#:if (#:call μ?v T₀)
                                          (#:external boolean #t)
                                          (#:call μ?v T₁))]
                  [(μ?v (·v T₀ T₁)) (#:if (#:call μ?v T₀)
                                          (#:external boolean #t)
                                          (#:if (#:call ν!?v T₀)
                                                (#:call μ?v T₁)
                                                (#:external boolean #f)))]
                  [(μ?v _) (#:external boolean #f)])
           #'(clause-alloc : (Env LClauses → Env)
                           [(clause-alloc ρ (NLC)) ρ]
                           [(clause-alloc ρ (LC x _ cs))
                            (#:call clause-alloc (#:extend ρ x (LR-cell (#:alloc #:expose #:identity))) cs)])
           #'(eq-len : ((#:inst TList #:⊤) (#:inst TList #:⊤) → #:boolean)
                     [(eq-len (Nil) (Nil)) (#:external boolean #t)]
                     [(eq-len (TCons _ l) (TCons _ r)) (#:call eq-len l r)]
                     [(eq-len _ _) (#:external boolean #f)]))))

   (define-values (CESK* metafunctions*)
     (tc-language CESK metafunctions Sτ))
   (define-values (aCESK* ametafunctions*)
     (coerce-language CESK* metafunctions*))
   (pretty-print aCESK*)
   (pretty-print ametafunctions*)

   (report-all-errors
    (append (append-map (λ (mf)
                           (if (Metafunction? mf)
                               (peel-scopes (Metafunction-rules mf))
                               (begin
                                 (printf "Bad mf ~a~%" mf)
                                 '()))) metafunctions*)
            CESK*))

   (language->mkV CESK* metafunctions* void))
 )
