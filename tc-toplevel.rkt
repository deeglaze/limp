#lang racket/base
(require (for-syntax syntax/parse racket/syntax racket/base)
         (only-in racket/bool implies)
         racket/list racket/match
         racket/pretty
         racket/set
         racket/string racket/trace
         "common.rkt" "language.rkt" "tast.rkt" "types.rkt"
         "tc-common.rkt" "tc.rkt")
(provide tc-language
         tc-metafunctions
         report-all-errors)

(define (tc-language rules metafunctions state-τ
                     #:use-lang [lang (current-language)]
                     #:mono-naming [namer (λ (name type)
                                             (string->symbol (format "~a~a" name type)))])
  ;; To resolve mf name to type while typechecking.
  (define Ξ
    (for/hash ([mf (in-list metafunctions)])
      (match-define (Metafunction name τ _) mf)
      (values name τ)))
  ;; Get the checked, general forms of the metafunctions
  (define mfs* (tc-metafunctions metafunctions Ξ))
  (displayln "Check 1 done")
  (define mfs** (tc-metafunctions mfs* Ξ))
  (displayln "Check 2 done")
  ;; Populate types of metafunction calls
  (define rules* (tc-rules ⊥eq #hash() Ξ rules state-τ state-τ 'root '()))
  (report-all-errors (append (metafunction-errors mfs*)
                             (metafunction-errors mfs**)
                             rules*))
  (displayln "Check 1/2 reports done")
  ;; Rewrite (and recheck for good measure) all metafunctions and rules
  ;; to use the monomorphized versions
  (parameterize ([monomorphized (make-hash)]
                 [mf-defs (for/hash ([mf (in-list mfs*)])
                            (values (Metafunction-name mf) mf))]
                 [mono-namer namer])
    ;; with monomorphized set to a hash, tc-metafunctions will create the
    ;; monomorphized versions of the monomorphic instantiations in the
    ;; metafunction definitions themselves.
    (report-all-errors (tc-metafunctions mfs* Ξ))
    (displayln "Check 2 done")
    ;; When checking the rules, all ecalls will additionally populate monomorphized
    (define rules* (tc-rules ⊥eq #hash() Ξ rules state-τ state-τ 'root '()))
    (displayln "Check 3 done")
    (values rules*
            (append-map hash-values (hash-values (monomorphized))))))

;; Typecheck all metafunctions
(define (tc-metafunctions mfs Ξ)
  (for/list ([mf (in-list mfs)])
    (match-define (Metafunction name τ scoped-rules) mf)
    (match-define-values (names (TArrow: _ dom rng) rules) (open-type-and-rules τ scoped-rules))
    (displayln (format "Checking ~a" mf))
    (define rules* (tc-rules ⊥eq #hash() Ξ rules dom rng `(def . ,name) '()))
    (report-all-errors rules*)
    (displayln "Checked")
    (Metafunction name τ (abstract-frees-in-rules rules* names))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Error reporting
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (raise-typecheck-error msg stxs)
  (define who (string->symbol "Type Checker"))
  (match stxs
    ['() (raise-syntax-error who msg)]
    [(list stx) (raise-syntax-error who msg (car stxs))]
    [stxs (raise-syntax-error who msg #f #f stxs)]))

(define error-list null)
(struct err (msg stx) #:prefab)

(define (report-rule-errors r)
  (match-define (Rule _ name lhs rhs bus) r)
  (report-pattern-errors lhs)
  (for-each report-bu-errors bus)
  (report-expression-errors rhs))

(define (metafunction-errors mfs)
  (append-map (λ (mf)
                 (if (Metafunction? mf)
                     (peel-scopes (Metafunction-rules mf))
                     (begin
                       (printf "Bad mf ~a~%" mf)
                       '())))
              mfs))

(define (err-chk typed)
  (define τ (πcc typed))
  (when (TError? τ)
    (set! error-list (cons (err (TError-msgs τ) (with-stx-stx typed)) error-list))))

(define (report-pattern-errors pat)
  (err-chk pat)
  (match pat
    [(PVariant _ _ _ (? list? ps))
     (for-each report-pattern-errors ps)]
    [(or (PMap-with _ _ k v p)
         (PMap-with* _ _ k v p))
     (report-pattern-errors k)
     (report-pattern-errors v)
     (report-pattern-errors p)]
    [(or (PSet-with _ _ v p)
         (PSet-with* _ _ v p))
     (report-pattern-errors v)
     (report-pattern-errors p)]
    [(or (PDeref _ _ p _ _)
         (PName _ _ _ p)
         (PIsType _ _ p))
     (report-pattern-errors p)]
    [(PTerm _ _ t) (report-term-errors t)]
    [_ (void)]))

(define (report-term-errors t)
  (err-chk t)
  (match t
    [(Variant _ _ _ (? list? ts)) (for-each report-term-errors ts)]
    [(Map _ _ f) (for ([(k v) (in-hash f)])
                   (report-term-errors k)
                   (report-term-errors v))]
    [(Set _ _ s) (for ([t (in-set s)]) (report-term-errors t))]
    [_ (void)]))

(define (report-bu-errors bu)
  (match bu
    [(Update _ k v)
     (report-expression-errors k)
     (report-expression-errors v)]
    [(Where _ pat e)
     (report-pattern-errors pat)
     (report-expression-errors e)]
    [(or (When _ e) (Unless _ e)) (report-expression-errors e)]
    [_ (error 'rbe)]))

(define (report-expression-errors e)
  (err-chk e)
  (match e
    [(or (ECall _ _ _ _ (? list? es))
         (EVariant _ _ _ _ _ (? list? es))
         (ESet-union _ _ (? list? es)))
     (for-each report-expression-errors es)]
    [(EStore-lookup _ _ k _ _)
     (report-expression-errors k)]
    [(ELet _ _ (? list? bus) body)
     (for-each report-bu-errors bus)
     (report-expression-errors body)]
    [(EMatch _ _ de (? list? rules))
     (report-expression-errors de)
     (for-each report-rule-errors rules)]
    [(EIf _ _ g t e)
     (report-expression-errors g)
     (report-expression-errors t)
     (report-expression-errors e)]
    [(EExtend _ _ m _ k v)
     (report-expression-errors m)
     (report-expression-errors k)
     (report-expression-errors v)]
    [(or (ESet-intersection _ _ e (? list? es))
         (ESet-subtract _ _ e (? list? es)))
     (report-expression-errors e)
     (for-each report-expression-errors es)]
    [(or (ESet-member _ _ e0 e1)
         (EMap-lookup _ _ e0 e1)
         (EMap-has-key _ _ e0 e1)
         (EMap-remove _ _ e0 e1))
     (report-expression-errors e0)
     (report-expression-errors e1)]
    [_ (void)]))


(define (report-all-errors v)
  (set! error-list null)
  (let populate ([v v])
    (cond [(Rule? v) (report-rule-errors v)]
          [(Expression? v) (report-expression-errors v)]
          [(Pattern? v) (report-pattern-errors v)]
          [(BU? v) (report-bu-errors v)]
          [(list? v) (for-each populate v)]))
  (define stxs
    (for/list ([e (in-list (reverse error-list))])
      (with-handlers ([exn:fail:syntax?
                       (λ (e) ((error-display-handler) (exn-message e) e))])
        (raise-typecheck-error (string-join (err-msg e) "\n\n") (list (err-stx e))))
      (err-stx e)))
  (set! error-list null)
  (unless (null? stxs)
    (raise-typecheck-error (format "Summary: ~a errors encountered" (length stxs))
                           (filter values stxs))))
