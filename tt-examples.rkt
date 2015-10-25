#lang racket

(require
  redex/reduction-semantics
  "tt.rkt")
(module+ test
  (require rackunit))

(module+ test
  (require racket/function)
  (check (curry alpha-equivalent? tt-reduceL)
    (term (reduce ((λ (x : (Type 0)) x) z)))
    (term z))
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
