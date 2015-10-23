#lang racket/base

(require
  redex/reduction-semantics)
(module+ test
  (require rackunit))

(define-language ttL
  (e t ::= x (λ (x : t) e) (e e) (Π (x : t) t) (Type i))
  (x   ::= variable-not-otherwise-mentioned)
  (i j ::= natural)
  #:binding-forms
  (λ (x : t) e #:refers-to x)
  (Π (x : t) e #:refers-to x))

(define-extended-language httL
  e t ::= ....
          (Σ (x : t) t) (pair e e) (fst e) (snd e)
          (x : t | P) (in e) (out e)
          ({P} (x : t) {Q}) d
          1 ()
          bool true false
          nat natural (eq? e e)
  (P Q ::= ⊤ ⊥ (not P) (and P Q) (or P Q) (P ⇒ Q) (∀ (x : t) P) (∃ (x : t) Q) (= t t e e))
  (c   ::= (deref e : t) (set! e e : t) (fix f (y : t) : t = d in (eval f e))) (if e E E)
  (d   ::= (do E ... (return e)))
  (E   ::=  (x ← e) (x <= c) (x : A = e))
  (f y ::= variable-not-otherwise-mentioned)
  #:binding-forms
  ({P} (x : t) {Q #:refers-to x})
  (fix f (y : t_0) : t_1 #:refers-to (shadow f y) = d #:refers-to (shadow f y) in (eval f e) #:refers-to (shadow f y)))

;; -------------------
;; Okay, the rest of the system depends on heaps existing, which depend on a bunch of crap...
(define-term ∈ (λ (A : (Type 0))))

(define-extended-language tt-reduceL ttL
  (C ::= hole (λ (x : C) e) (λ (x : e) C) (C e) (e C) (Π (x : C) e) (Π (x : e) C))
  ;; Can redex handle the nondeterminism?!
  #;(C ::= hole (λ (x : C) e) (λ (x : v) C) (C e) (v C) (Π (x : C) e) (Π (x : v) C))
  #;(v ::= (Type i) (λ (x : v) v) (Π (x : v) v) c)
  #;(c ::= x (c v)))

(define-metafunction tt-reduceL
  [(subst e x_0 e_0)
   ,(substitute tt-reduceL (term e) (term x_0) (term e_0))])

(define tt-reduceR
  (reduction-relation tt-reduceL
    (==> (fst (pair e_0 e_1)) e_0)
    (==> (snd (pair e_0 e_1)) e_1)
    (==> (out (in e)) e)
    (==> (if true e_0 e_1) e_0)
    (==> (if false e_0 e_1) e_1)
    (==> (eq? natural_0 natural_0) true)
    (==> (eq? natural_!_0 natural_!_0) false)
    (==> ((λ (x : t) e_0) e_1) (subst e_0 x e_1))
    with
    [(--> (in-hole C e_0) (in-hole C e_1))
     (==> e_0 e_1)]))

(define-metafunction tt-reduceL
  [(reduce e) ,(car (apply-reduction-relation* tt-reduceR (term e)))])

(module+ test
  (require racket/function)
  (check (curry alpha-equivalent? tt-reduceL)
    (term (reduce ((λ (x : (Type 0)) x) z)))
    (term z)))

(define-judgment-form tt-reduceL
  #:mode (convert I I)
  #:contract (convert e e)

  [(side-condition ,(< (term i) (term j)))
   ---------------------------
   (convert (Type i) (Type j))]

  [(where e_3 (reduce e_0))
   (where e_3 (reduce e_1))
   --------------
   (convert e_0 e_1)])

(define-extended-language tt-typingL tt-reduceL
  (Γ ::= ∅ (Γ x : t)))

(define-judgment-form tt-typingL
  #:mode (valid I)
  #:contract (valid Γ)

  [--------------------
   (valid ∅)]

  [(type-infer Γ t (Type i))
   --------------------
   (valid (Γ x : t))])

(define-metafunction tt-typingL
  Γ-ref : Γ x -> t or #f
  [(Γ-ref ∅ x) #f]
  [(Γ-ref (Γ x : t) x) t]
  [(Γ-ref (Γ x_0 : t_0) x) (Γ-ref Γ x)])

(define-judgment-form tt-typingL
  #:mode (type-infer I I O)
  #:contract (type-infer Γ e t)

  [(where t (Γ-ref Γ x))
   (valid Γ)
   -----------------------
   (type-infer Γ x t)]

  [(valid Γ)
   (where j ,(add1 (term i)))
   -------------------------------
   (type-infer Γ (Type i) (Type j))]

  [(type-infer (Γ x : t_0) e t)
   -------------------------------------------
   (type-infer Γ (λ (x : t_0) e) (Π (x : t_0) t))]

  [(type-infer Γ t_0 (Type i))
   (type-check (Γ x : t_0) t (Type i))
   -------------------------------------
   (type-infer Γ (Π (x : t_0) t) (Type i))]

  [(type-infer Γ e_0 (Π (x : t_1) t))
   (type-check Γ e_1 t_1)
   --------------------------
   (type-infer Γ (e_0 e_1) (subst t x e_1))])

(define-judgment-form tt-typingL
  #:mode (type-check I I I)
  #:contract (type-check Γ e t)

  [(type-infer Γ e t_1)
   (convert t_1 t)
   -----------------
   (type-check Γ e t)])

(define-metafunction tt-typingL
  Γ-build : (x : t) ... -> Γ
  [(Γ-build) ∅]
  [(Γ-build (x_r : t_r) ...  (x : t))
   ((Γ-build (x_r : t_r) ...) x : t)])

(module+ test
  (check-true
    (judgment-holds (type-infer ∅ (Type 0) (Type 1))))
  (check-true
    (judgment-holds (type-check ∅ (Type 0) (Type 1))))
  (check-false
    (judgment-holds (type-check ∅ (Π (x : (Type 0)) (Type 0)) (Type 0))))
  (check-true
    (judgment-holds (type-check ∅ (Π (x : (Type 0)) (Type 0)) (Type 1))))
  (check-false
    (judgment-holds (type-check ∅ (Π (x : (Type 0)) x) (Type 0))))


  (define Γp (term (Γ-build
                      (Nat : (Type 0))
                      (z : Nat)
                      (s : (Π (x : Nat) Nat)))))
  (check-true
    (judgment-holds (type-check ,Γp z Nat)))
  (check-true
    (judgment-holds (type-check ,Γp (s (s z)) Nat))))
