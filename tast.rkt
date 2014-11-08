#lang racket/base
#|
This module provides the structs that the Limp compiler uses to typecheck an input language
and semantics.
|#

(provide (all-defined-out))

(struct with-stx (stx) #:transparent)
;; Cast or Check annotations?
(struct Cast (t) #:transparent)
(struct Check (t) #:transparent)
(struct Typed with-stx (ct) #:transparent)

;; Elaborated patterns
(struct Pattern Typed () #:transparent)
(struct PAnd Pattern (ps) #:transparent)
(struct PName Pattern (x) #:transparent)
(struct PWild Pattern () #:transparent)
(struct PVariant Pattern (n ps) #:transparent)
(struct PMap-with Pattern (k v p) #:transparent)
(struct PMap-with* Pattern (k v p) #:transparent)
(struct PSet-with Pattern (v p) #:transparent)
(struct PSet-with* Pattern (v p) #:transparent)
(struct PTerm Pattern (t) #:transparent)
;; The info is in the type
(struct PIsExternal Pattern () #:transparent)
(struct PIsAddr Pattern () #:transparent)
(struct PIsType Pattern () #:transparent)
#|
Template:
 (match pat
    [(PAnd ct ps) ???]
    [(PName ct x) ???]
    [(PWild ct) ???]
    [(PVariant ct n ps) ???]
    [(PMap-with ct k v p) ???]
    [(PMap-with* ct k v p) ???]
    [(PSet-with ct v p) ???]
    [(PSet-with* ct v p) ???]
    [(PTerm ct t) ???]
    [(PIsExternal ct) ???]
    [(PIsAddr ct) ???]
    [(PIsType ct) ???]
    [_ (error who "Unsupported pattern: ~a" pat)])
|#

;; Elaborated Terms
(struct Term Typed () #:transparent)
(struct Variant Term (n ts) #:transparent)
(struct Map Term (f) #:transparent)
(struct Set Term (s) #:transparent)
(struct External Term (v) #:transparent)

;; Expressions
(struct Expression Typed () #:transparent)
(struct ECall Expression (mf tag τs es) #:transparent)
(struct EVariant Expression (n tag τs es) #:transparent)
(struct ERef Expression (x) #:transparent)
(struct EStore-lookup Expression (k lm) #:transparent) ;; lm ::= 'resolve | 'delay | 'deref
(struct EAlloc Expression (tag) #:transparent) ;; space mm em in type
(struct ELet Expression (bus body) #:transparent)
(struct EMatch Expression (discriminant rules) #:transparent)
(struct EExtend Expression (m tag k v) #:transparent)
(struct EEmpty-Map Expression () #:transparent)
(struct EEmpty-Set Expression () #:transparent)
(struct ESet-add Expression (s v) #:transparent)
;; Utility expressions
(struct ESet-union Expression (es) #:transparent)
(struct ESet-intersection Expression (e es) #:transparent)
(struct ESet-subtract Expression (e es) #:transparent)
(struct ESet-remove Expression (e es) #:transparent)
(struct ESet-member Expression (e v) #:transparent)
(struct EMap-lookup Expression (m k) #:transparent)
(struct EMap-has-key Expression (m k) #:transparent)
(struct EMap-remove Expression (m k) #:transparent)
#|
Template
(match e
    [(ECall ct mf tag es) ???]
    [(EVariant ct n tag es) ???]
    [(ERef ct x) ???]
    [(EStore-lookup ct k lm) ???]
    [(EAlloc ct tag) ???]
    [(ELet ct bus body) ???]
    [(EMatch ct de rules) ???]
    [(EExtend ct m tag k v) ???]
    [(EEmpty-Map ct) ???]
    [(EEmpty-Set ct) ???]
    [(ESet-union ct es) ???]
    [(ESet-intersection ct e es) ???]
    [(ESet-subtract ct e es) ???]
    [(ESet-member ct e v) ???]
    [(EMap-lookup ct m k) ???]
    [(EMap-has-key ct m k) ???]
    [(EMap-remove ct m k) ???]
    [_ (error 'tc-expr "Unrecognized expression form: ~a" e)])
|#

;; Binding updates
(struct Update with-stx (k v) #:transparent)
(struct Where with-stx (pat e) #:transparent)

(struct Rule with-stx (name lhs rhs bus) #:transparent)
