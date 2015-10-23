#lang racket/base

(require
  redex/reduction-semantics)
(module+ test
  (require rackunit))

(define-language ittL
  (e t ::= x (λ (x : t) e) (e e) (Π (x : t) t) (Type i) (induction x (Type i)))
  (x   ::= variable-not-otherwise-mentioned)
  (i j ::= natural)
  (Δ   ::= ∅ (Δ (x : t ((c : t) ...))))
  #:binding-forms
  (λ (x : t) e #:refers-to x)
  (Π (x : t) e #:refers-to x))

(define-metafunction ttL
  Δ-ref-type : Δ x -> t or #f
  [(Δ-ref-type ∅ x) #f]
  [(Δ-ref-type (Δ (x : t any)) x) t]
  [(Δ-ref-type (Δ (x_0 : t_0 any)) x) (Δ-ref-type Δ x)])

(define-metafunction ttL
  Δ-ref-constructor-map : Δ x -> ((x : t) ...) or #f
  ;; NB: Depends on clause order
  [(Δ-ref-constructor-map ∅ x_D) #f]
  [(Δ-ref-constructor-map (Δ (x_D : t_D any)) x_D)
   any]
  [(Δ-ref-constructor-map (Δ (x_1 : t_1 any)) x_D)
   (Δ-ref-constructor-map Δ x_D)])

(define-metafunction ttL
  Δ-ref-constructors : Δ x -> (x ...) or #f
  [(Δ-ref-constructors Δ x_D)
   (x ...)
   (where ((x : t) ...) (Δ-ref-constructor-map Δ x_D))])

(define-metafunction ttL
  Δ-ref-constructor-type : Δ x x -> t or #f
  [(Δ-ref-constructor-type Δ x_D x)
   t
   (where ((x_1 : t_1) ... (x : t) (x_2 : t_2) ...)
          (Δ-ref-constructor-map Δ x_D))]
  [(Δ-ref-constructor-type Δ x_D x) #f])

(define-metafunction ttL
  Δ-key-by-constructor : Δ x -> x
  [(Δ-key-by-constructor (Δ (x : t ((x_0 : t_0) ... (x_c : t_c) (x_1 : t_1) ...))) x_c)
   x]
  [(Δ-key-by-constructor (Δ (x_1 : t_1 any)) x)
   (Δ-key-by-constructor Δ x)])

(define-extended-language itt-reduceL ittL
  (C ::= hole (λ (x : C) e) (λ (x : e) C) (C e) (e C) (Π (x : C) e) (Π (x : e) C))
  ;; Can redex handle the nondeterminism?!
  #;(C ::= hole (λ (x : C) e) (λ (x : v) C) (C e) (v C) (Π (x : C) e) (Π (x : v) C))
  #;(v ::= (Type i)  (λ (x : v) v) (Π (x : v) v) c)
  #;(c ::= x (induction x (Type i)) (c v)))

(define-metafunction tt-reduceL
  [(subst e x_0 e_0)
   ,(substitute tt-reduceL (term e) (term x_0) (term e_0))])

(define tt-reduceR
  (reduction-relation tt-reduceL
    (==> ((λ (x : t) e_0) e_1)
         (subst e_0 x e_1))
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
