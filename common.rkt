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
                       (f acc (let () post-body ...))))])))]))

(define-for/do for/union for/fold ∅ set-union)
(define-for/do for/unioneq for/fold ∅eq set-union)

(define (hash-hash-add! h k k2 v)
  (hash-set! h k (hash-set! (hash-ref! h k make-hash) k2 v)))

(define (hash-key-set h) (for/set ([k (in-hash-keys h)]) k))

(define (rev-map f l)
  (let rec ([l l] [acc '()])
    (match l
      ['() acc]
      [(cons x l) (rec l (cons (f x) acc))])))

;; symbol->keyword
(define (s->k s) (string->keyword (symbol->string s)))
