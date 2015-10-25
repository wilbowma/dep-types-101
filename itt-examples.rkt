#lang racket/base

(require
  redex/reduction-semantics
  "itt.rkt")
(module+ test
  (require rackunit))


(module+ test
  (define-term Δ
    (Δ-build
      (Nat : (Type 0)
        ((z : Nat)
         (s : (Π (n : Nat) Nat))))
      (Bool : (Type 0)
        (true : Bool)
        (false : Bool))))
  (check-true
    (judgment-holds (type-check Δ ∅ true Bool)))
  (define-term not
    (λ (x : Bool)
       (apply (induction Bool (Type 0)) ;; Apply the induction principle for Bool
              (λ (x : Bool) Bool) ;; Motive
              false ;; true case
              true  ;; false case
              x))) ;; discriminant
  (check-true
    (judgment-holds (type-check Δ ∅ not (Π (x : Bool) Bool))))
  (require racket/function)
  (check (curry alpha-equivalent? ittL)
    (term (reduce Δ (not true)))
    (term false))
  (define-term pred
    (λ (x : Nat)
       (apply (induction Nat (Type 0)) ;; Apply the induction principle for Nat
              (λ (x : Nat) Nat) ;; Motive
              z ;; z case

              ;; inductive case
              ;; note that to define pred, we ignore the induction hypothesis
              (λ (n : Nat) (λ (IH : Nat) n))
              x)))
  (check-true
    (judgment-holds (type-check Δ ∅ pred (Π (x : Nat) Nat))))
  (check (curry alpha-equivalent? ittL)
    (term (reduce Δ (pred z)))
    (term z))
  (check (curry alpha-equivalent? ittL)
    (term (reduce Δ (pred (s z))))
    (term z))
  (check (curry alpha-equivalent? ittL)
    (term (reduce Δ (pred (s (s z)))))
    (term (s z))))
