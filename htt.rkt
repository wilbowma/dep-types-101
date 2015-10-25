#lang racket/base

(require
  redex/reduction-semantics
  "imp-itt.rkt")

;; HTT require a bunch of auxillary definitions, that can be defined via inductive types.

(define-term -> (λ (X : Prop) (λ (Y : Prop) (Π (x : X) (Π (y : Y) Prop)))))
(define-metafunction
  [(Π* (x : t) (x_r : t_r) ... t)
   (Π (x : t) (Π* (x_r : t_r) ... t))])
(define-term Δ
  (Δ-build
    (Bool : (Type 0)
      ((true : Bool)
       (false : Bool)))
    (Nat : (Type 0)
      ((z : Nat)
       (s : (Π (n : Nat) Nat))))
    (⊤ : Prop (I : ⊤))
    (⊥ : Prop ())
    (And : (-> Prop (-> Prop Prop))
      ((conj : (Π* (A : Prop) (B : Prop) (a : A) (b : B) (apply And A B)))))
    (Or : (-> Prop (-> Prop Prop))
      ((inl : (Π* (A : Prop) (B : Prop) (a : A) (apply Or A B)))
       (inr : (Π* (A : Prop) (B : Prop) (b : B) (apply Or A B)))))
    (Σ : ())
    (= : (Π* (A : (Type 0)) (B : (Type 0)) (a : A) (-> B Prop))
      ((refl : (Π (A : (Type 0) (a : A) (apply = A A a a))))))
    )) ...
(define-term Not (λ (x : Prop) False))
