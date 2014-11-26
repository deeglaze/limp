#lang racket/base
(require (for-syntax syntax/parse racket/base racket/syntax syntax/for-body)
         racket/set racket/match
         racket/trace)
(provide (all-defined-out))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Common utils
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define ∅eq (seteq))
(define ∅ (set))
(define ⊥ (hash))
(struct -unmapped ())
(define unmapped (-unmapped))
(define (unmapped? x) (eq? x unmapped))

(define-syntax (define-for/do stx)
  (syntax-parse stx
    [(_  name folder base f)
     #'(...
        (define-syntax (name syn)
          (syntax-parse syn
            [(_ guards body ...)
             (define/with-syntax [(pre-body ...) (post-body ...)]
               (split-for-body syn #'(body ...)))
             (syntax/loc syn
               (folder ([acc base]) guards
                       pre-body ...
                       (f (let () post-body ...) acc)))])))]))

(define-for/do for/union for/fold ∅ set-union)
(define-for/do for/unioneq for/fold ∅eq set-union)

(define-for/do for/append for/fold '() append)

(define (hash-union! h k s) (hash-set! h k (set-union (hash-ref h k ∅) s)))
(define (hash-add! h k v) (set-add! (hash-ref! h k mutable-set) v))

(define (hash-key-set h) (for/set ([k (in-hash-keys h)]) k))

(define (rev-map f l)
  (let rec ([l l] [acc '()])
    (match l
      ['() acc]
      [(cons x l) (rec l (cons (f x) acc))])))

(define (rev-append r l)
  (match r
    ['() l]
    [(cons r rs) (rev-append rs (cons r l))]))

;; symbol->keyword
(define (s->k s) (string->keyword (symbol->string s)))
