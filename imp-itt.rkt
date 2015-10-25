#lang racket/base

(require
  redex/reduction-semantics)

(provide (all-defined-out))

;; ITT with an impredicative universe Prop
(define-language imp-ittL
  (U   ::= Prop (Type i))
  (e t ::= x (λ (x : t) e) (e e) (Π (x : t) t) U (induction x U))
  (x   ::= variable-not-otherwise-mentioned)
  (i j ::= natural)
  (Δ   ::= ∅ (Δ (x : t ((c : t) ...))))
  #:binding-forms
  (λ (x : t) e #:refers-to x)
  (Π (x : t) e #:refers-to x))

;;; --------------------------------------------------------------------------------------------------
;;; This section defines a variety of functions for working with inductive definitions. They are
;;; largely uninteresting.

;; Returns the type of the inductively defined type x
(define-metafunction ttL
  Δ-ref-type : Δ x -> t or #f
  [(Δ-ref-type ∅ x) #f]
  [(Δ-ref-type (Δ (x : t any)) x) t]
  [(Δ-ref-type (Δ (x_0 : t_0 any)) x) (Δ-ref-type Δ x)])

;; Returns the constructor map for the inductively defined type x_D in the signature Δ
(define-metafunction ttL
  Δ-ref-constructor-map : Δ x -> ((x : t) ...) or #f
  ;; NB: Depends on clause order
  [(Δ-ref-constructor-map ∅ x_D) #f]
  [(Δ-ref-constructor-map (Δ (x_D : t_D any)) x_D)
   any]
  [(Δ-ref-constructor-map (Δ (x_1 : t_1 any)) x_D)
   (Δ-ref-constructor-map Δ x_D)])

;; Get the list of constructors for the inducitvely defined type x_D
(define-metafunction ttL
  Δ-ref-constructors : Δ x -> (x ...) or #f
  [(Δ-ref-constructors Δ x_D)
   (x ...)
   (where ((x : t) ...) (Δ-ref-constructor-map Δ x_D))])

;; Returns the type of the constructor x for the inductively defined type x_D
(define-metafunction ttL
  Δ-ref-constructor-type : Δ x x -> t or #f
  [(Δ-ref-constructor-type Δ x_D x)
   t
   (where ((x_1 : t_1) ... (x : t) (x_2 : t_2) ...)
          (Δ-ref-constructor-map Δ x_D))]
  [(Δ-ref-constructor-type Δ x_D x) #f])

;; Returns the inductively defined type for which x is a constructor.
(define-metafunction ttL
  Δ-key-by-constructor : Δ x -> x
  [(Δ-key-by-constructor (Δ (x : t ((x_0 : t_0) ... (x_c : t_c) (x_1 : t_1) ...))) x_c)
   x]
  [(Δ-key-by-constructor (Δ (x_1 : t_1 any)) x)
   (Δ-key-by-constructor Δ x)])

(define-metafunction ttL
  sequence-index-of : any (any ...) -> natural
  [(sequence-index-of any_0 (any_0 any ...))
   0]
  [(sequence-index-of any_0 (any_1 any ...))
   ,(add1 (term (sequence-index-of any_0 (any ...))))])

;; Get the index of the constructor x_ci in the list of constructors for x_D
(define-metafunction ttL
  Σ-constructor-index : Σ x x -> natural
  [(Σ-constructor-index Σ x_D x_ci)
   (sequence-index-of x_ci (Σ-ref-constructors Σ x_D))])

(define-extended-language imp-itt-ctxtL imp-ittL
  ;; Telescope.
  (Ξ Φ ::= hole (Π (x : t) Ξ))
  ;; Apply context
  (Θ   ::= hole (Θ e))
  (U   ::= (Type i)))

;; Return the parameters of x_D as a telescope Ξ
(define-metafunction imp-itt-ctxtL
  Δ-ref-parameter-Ξ : Δ x -> Ξ
  [(Δ-ref-parameter-Ξ (Δ (x_D : (in-hole Ξ U) any)) x_D)
   Ξ]
  [(Δ-ref-parameter-Ξ (Δ (x_1 : t_1 any)) x_D)
   (Δ-ref-parameter-Ξ Δ x_D)])

(define-metafunction imp-itt-ctxtL
  Ξ-apply : Ξ t -> t
  [(Ξ-apply hole t) t]
  [(Ξ-apply (Π (x : t) Ξ) t_0) (Ξ-apply Ξ (t_0 x))])

;; Compose multiple telescopes into a single telescope:
(define-metafunction imp-itt-ctxtL
  Ξ-compose : Ξ Ξ ... -> Ξ
  [(Ξ-compose Ξ) Ξ]
  [(Ξ-compose Ξ_0 Ξ_1 Ξ_rest ...)
   (Ξ-compose (in-hole Ξ_0 Ξ_1) Ξ_rest ...)])

;; Compute the number of arguments in a Ξ
(define-metafunction imp-itt-ctxtL
  Ξ-length : Ξ -> natural
  [(Ξ-length hole) 0]
  [(Ξ-length (Π (x : t) Ξ)) ,(add1 (term (Ξ-length Ξ)))])

;; Compute the number of applications in a Θ
(define-metafunction imp-itt-ctxtL
  Θ-length : Θ -> natural
  [(Θ-length hole) 0]
  [(Θ-length (Θ e)) ,(add1 (term (Θ-length Θ)))])

;; Reference an expression in Θ by index; index 0 corresponds to the the expression applied to a hole.
(define-metafunction imp-itt-ctxtL
  Θ-ref : Θ natural -> e or #f
  [(Θ-ref hole natural) #f]
  [(Θ-ref (in-hole Θ (hole e)) 0) e]
  [(Θ-ref (in-hole Θ (hole e)) natural) (Θ-ref Θ ,(sub1 (term natural)))])

;;; ------------------------------------------------------------------------
;;; Computing the types of eliminators

;; Returns the telescope of the arguments for the constructor x_ci of the inductively defined type x_D
(define-metafunction imp-itt-ctxtL
  Δ-constructor-telescope : Δ x x -> Ξ
  [(Δ-constructor-telescope Δ x_D x_ci)
   Ξ
   (where (in-hole Ξ (in-hole Θ x_D))
     (Δ-ref-constructor-type Δ x_D x_ci))])

;; Returns the parameter arguments as an apply context of the constructor x_ci of the inductively
;; defined type x_D
(define-metafunction imp-itt-ctxtL
  Δ-constructor-parameters : Δ x x -> Θ
  [(Δ-constructor-parameters Δ x_D x_ci)
   Θ
   (where (in-hole Ξ (in-hole Θ x_D))
     (Δ-ref-constructor-type Δ x_D x_ci))])

;; Inner loop for Δ-constructor-noninductive-telescope
(define-metafunction imp-itt-ctxtL
  noninductive-loop : x Φ -> Φ
  [(noninductive-loop x_D hole) hole]
  [(noninductive-loop x_D (Π (x : (in-hole Φ (in-hole Θ x_D))) Φ_1))
   (noninductive-loop x_D Φ_1)]
  [(noninductive-loop x_D (Π (x : t) Φ_1))
   (Π (x : t) (noninductive-loop x_D Φ_1))])

;; Returns the noninductive arguments to the constructor x_ci of the inductively defined type x_D
(define-metafunction imp-itt-ctxtL
  Δ-constructor-noninductive-telescope : Δ x x -> Ξ
  [(Δ-constructor-noninductive-telescope Δ x_D x_ci)
   (noninductive-loop x_D (Δ-constructor-telescope Δ x_D x_ci))])

;; Inner loop for Δ-constructor-inductive-telescope
;; NB: Depends on clause order
(define-metafunction imp-itt-ctxtL
  inductive-loop : x Φ -> Φ
  [(inductive-loop x_D hole) hole]
  [(inductive-loop x_D (Π (x : (in-hole Φ (in-hole Θ x_D))) Φ_1))
   (Π (x : (in-hole Φ (in-hole Θ x_D))) (inductive-loop x_D Φ_1))]
  [(inductive-loop x_D (Π (x : t) Φ_1))
   (inductive-loop x_D Φ_1)])

;; Returns the inductive arguments to the constructor x_ci of the inducitvely defined type x_D
(define-metafunction imp-itt-ctxtL
  Δ-constructor-inductive-telescope : Δ x x -> Ξ
  [(Δ-constructor-inductive-telescope Δ x_D x_ci)
   (inductive-loop x_D (Δ-constructor-telescope Δ x_D x_ci))])

;; Returns the inductive hypotheses required for eliminating the inductively defined type x_D with
;; motive t_P, where the telescope Φ are the inductive arguments to a constructor for x_D
(define-metafunction imp-itt-ctxtL
  hypotheses-loop : x t Φ -> Φ
  [(hypotheses-loop x_D t_P hole) hole]
  [(hypotheses-loop x_D t_P (name any_0 (Π (x : (in-hole Φ (in-hole Θ x_D))) Φ_1)))
   (Π (x_h : (in-hole Φ ((in-hole Θ t_P) (Ξ-apply Φ x))))
      (hypotheses-loop x_D t_P Φ_1))
   (where x_h ,(variable-not-in (term (x_D t_P any_0)) 'x-ih))])

;; Returns the inductive hypotheses required for the elimination method of constructor x_ci for
;; inductive type x_D, when eliminating with motive t_P.
(define-metafunction imp-itt-ctxtL
  Δ-constructor-inductive-hypotheses : Δ x x t -> Ξ
  [(Δ-constructor-inductive-hypotheses Δ x_D x_ci t_P)
   (hypotheses-loop x_D t_P (Δ-constructor-inductive-telescope Δ x_D x_ci))])

(define-metafunction imp-itt-ctxtL
  Δ-constructor-method-telescope : Δ x x t -> Ξ
  [(Δ-constructor-method-telescope Δ x_D x_ci t_P)
   (Π (x_mi : (in-hole Ξ_a (in-hole Ξ_h ((in-hole Θ_p t_P) (Ξ-apply Ξ_a x_ci)))))
      hole)
   (where Θ_p (Δ-constructor-parameters Δ x_D x_ci))
   (where Ξ_a (Δ-constructor-telescope Δ x_D x_ci))
   (where Ξ_h (Δ-constructor-inductive-hypotheses Δ x_D x_ci t_P))
   (where x_mi ,(variable-not-in (term (t_P Δ)) 'x-mi))])

;; fold Ξ-compose over map Δ-constructor-method-telescope over the list of constructors
(define-metafunction imp-itt-ctxtL
  method-loop : Δ x t (x ...) -> Ξ
  [(method-loop Δ x_D t_P ()) hole]
  [(method-loop Δ x_D t_P (x_0 x_rest ...))
   (Ξ-compose (Δ-constructor-method-telescope Δ x_D x_0 t_P) (method-loop Δ x_D t_P (x_rest ...)))])

;; Returns the telescope of all methods required to eliminate the type x_D with motive t_P
(define-metafunction imp-itt-ctxtL
  Δ-methods-telescope : Δ x t -> Ξ
  [(Δ-methods-telescope Δ x_D t_P)
   (method-loop Δ x_D t_P (Δ-ref-constructors Δ x_D))])


;;; -------------------------------------------------------------------------------------------------
;;; Interesting definitions resume


;; Computes the type of the eliminator for the inductively defined type x_D with a motive whose result
;; is in universe U.
;;
;; The type of (elim x_D U) is something like:
;;  (∀ (P : (∀ a -> ... -> (D a ...) -> U))
;;     (method_ci ...) -> ... ->
;;     (a -> ... -> (D a ...) ->
;;       (P a ... (D a ...))))
;;
;; x_D   is an inductively defined type
;; U     is the sort the motive
;; x_P   is the name of the motive
;; Ξ_P*D is the telescope of the parameters of x_D and
;;       the witness of type x_D (applied to the parameters)
;; Ξ_m   is the telescope of the methods for x_D
(define-metafunction imp-itt-ctxtL
  Δ-elim-type : Δ x U -> t
  [(Δ-elim-type Δ x_D U)
   (Π (x_P : (in-hole Ξ_P*D U))
      ;; The methods Ξ_m for each constructor of type x_D
      (in-hole Ξ_m
        ;; And finally, the parameters and discriminant
        (in-hole Ξ_P*D
          ;; The result is (P a ... (x_D a ...)), i.e., the motive
          ;; applied to the paramters and discriminant
          (Ξ-apply Ξ_P*D x_P))))
   ;; Get the parameters of x_D
   (where Ξ (Δ-ref-parameter-Ξ Δ x_D))
   ;; A fresh name to bind the discriminant
   (where x ,(variable-not-in (term (Δ Γ x_D Ξ)) 'x-D))
   ;; The telescope (∀ a -> ... -> (D a ...) hole), i.e.,
   ;; of the parameters and the inductive type applied to the
   ;; parameters
   (where Ξ_P*D (in-hole Ξ (Π (x : (Ξ-apply Ξ x_D)) hole)))
   ;; A fresh name for the motive
   (where x_P ,(variable-not-in (term (Δ Γ x_D Ξ Ξ_P*D x)) 'x-P))
   ;; The types of the methods for this inductive.
   (where Ξ_m (Δ-methods-telescope Δ x_D x_P))])

;; Generate recursive applications of the eliminator for each inductive argument of type x_D.
;; In more detaill, given motive t_P, parameters Θ_p, methods Θ_m, and arguments Θ_i to constructor
;; x_ci for x_D, for each inductively smaller term t_i of type (in-hole Θ_p x_D) inside Θ_i,
;; generate: (elim x_D U t_P  Θ_m ... Θ_p ... t_i)
(define-metafunction imp-itt-ctxtL
  Δ-inductive-elim : Δ x U t Θ Θ Θ -> Θ
  [(Δ-inductive-elim Δ x_D U t_P Θ_p Θ_m (in-hole Θ_i (hole (name t_i (in-hole Θ_r x_ci)))))
   ((Δ-inductive-elim Δ x_D U t_P Θ_p Θ_m Θ_i)
    (in-hole ((in-hole Θ_p Θ_m) t_i) ((elim x_D U) t_P)))
   (side-condition (memq (term x_ci) (term (Δ-ref-constructors Δ x_D))))]
  [(Δ-inductive-elim Δ x_D U t_P Θ_p Θ_m Θ_nr) hole])

(define-extended-language imp-itt-reduceL imp-itt-ctxtL
  (C ::= hole (λ (x : C) e) (λ (x : e) C) (C e) (e C) (Π (x : C) e) (Π (x : e) C))
  ;; Can redex handle the nondeterminism?!
  #;(C ::= hole (λ (x : C) e) (λ (x : v) C) (C e) (v C) (Π (x : C) e) (Π (x : v) C))
  #;(v ::= (Type i)  (λ (x : v) v) (Π (x : v) v) c)
  #;(c ::= x (induction x (Type i)) (c v)))

(define-metafunction imp-itt-reduceL
  [(subst e x_0 e_0)
   ,(substitute imp-itt-reduceL (term e) (term x_0) (term e_0))])

(define imp-itt-reduceR
  (reduction-relation imp-itt-reduceL
    (--> (Δ (in-hole C ((λ (x : t) e_0) e_1)))
         (Δ (in-hole C (subst e_0 x e_1))))
    (--> (Δ (in-hole C (in-hole Θ ((elim x_D U) v_P))))
         (Δ (in-hole C (in-hole Θ_r (in-hole Θv_i v_mi))))
         #|
          | The elim form must appear applied like so:
          | (elim x_D U v_P m_0 ... m_i m_j ... m_n p ... (c_i a ...))
          |
          | Where:
          |   x_D       is the inductive being eliminated
          |   U         is the universe of the result of the motive
          |   v_P       is the motive
          |   m_{0..n}  are the methods
          |   p ...     are the parameters of x_D
          |   c_i       is a constructor of x_d
          |   a ...     are the arguments to c_i
          | Unfortunately, Θ contexts turn all this inside out:
          |#
          ;; Split Θ into its components: the paramters Θ_p for x_D, the methods Θ_m for x_D, and
          ;; the discriminant: the constructor x_ci applied to its argument Θ_i
         (where (in-hole (Θ_p (in-hole Θ_i x_ci)) Θ_m) Θ)
         ;; Check that Θ_p actually matches the parameters of x_D, to ensure it doesn't capture other
         ;; arguments.
         (side-condition (equal? (term (Θ-length Θ_p)) (term (Ξ-length (Σ-ref-parameter-Ξ Σ x_D)))))
         ;; Ensure x_ci is actually a constructor for x_D
         (where (x_c* ...) (Σ-ref-constructors Σ x_D))
         (side-condition (memq (term x_ci) (term (x_c* ...))))
         ;; There should be a number of methods equal to the number of constructors; to ensure C
         ;; doesn't capture methods and Θ_m doesn't capture other arguments
         (side-condition (equal? (length (term (x_c* ...)))  (term (Θ-length Θ_m))))
         ;; Find the method for constructor x_ci, relying on the order of the arguments.
         (where v_mi (Θ-ref Θ_m (Σ-constructor-index Σ x_D x_ci)))
         ;; Generate the inductive recursion
         (where Θ_r (Σ-inductive-elim Σ x_D U v_P Θ_p Θ_m Θ_i))
         -->elim)))

(define-metafunction tt-reduceL
  [(reduce Δ e) ,(car (apply-reduction-relation* tt-reduceR (term e)))])

(define-judgment-form tt-reduceL
  #:mode (convert I I I)
  #:contract (convert Δ e e)

  [-------------------------
   (convert Δ Prop (Type 0))]

  [(side-condition ,(< (term i) (term j)))
   ---------------------------
   (convert Δ (Type i) (Type j))]

  [(where e_3 (reduce Δ e_0))
   (where e_3 (reduce Δ e_1))
   --------------
   (convert Δ e_0 e_1)])

(define-extended-language tt-typingL tt-reduceL
  (Γ ::= ∅ (Γ x : t)))

(define-metafunction tt-typingL
  nonpositive : x t -> #t or #f
  [(nonpositive x (in-hole Θ x))
   #t]
  [(nonpositive x (Π (x_0 : (in-hole Θ x)) t))
   #f]
  [(nonpositive x (Π (x_0 : t_0) t))
   ,(and (term (positive x t_0)) (term (nonpositive x t)))]
  [(nonpositive x t) #t])

(define-metafunction tt-typingL
  positive : x t -> #t or #f
  [(positive x (in-hole Θ x))
   #f]
  [(positive x (Π (x_0 : (in-hole Θ x)) t))
   (positive x t)]
  [(positive x (Π (x_0 : t_0) t))
   ,(and (term (nonpositive x t_0)) (term (positive x t)))]
  [(positive x t) #t])

(define-metafunction tt-typingL
  positive* : x (t ...) -> #t or #f
  [(positive* x_D ()) #t]
  [(positive* x_D (t_c t_rest ...))
   ;; Replace the result of the constructor with (Type 0), to avoid the result being considered a
   ;; nonpositive position.
   ,(and (term (positive x_D (in-hole Ξ (Type 0)))) (term (positive* x_D (t_rest ...))))
   (where (in-hole Ξ (in-hole Θ x_D)) t_c)])

(define-judgment-form tt-typingL
  #:mode (valid I I)
  #:contract (valid Δ Γ)

  [-------------------- "Valid-Empty"
   (valid ∅ ∅)]

  [(type-infer Δ Γ t (Type i))
   (valid Δ Γ)
   -------------------- "Valid-Var"
   (valid Δ (Γ x : t))]

  [(valid Δ ∅)
   (type-infer Δ ∅ t_D U_D)
   (type-infer Δ (∅ x_D : t_D) t_c U_c) ...
   ;; Ensure each constructor for x_D actually returns an x_D
   (side-condition ,(map (curry equal? (term x_D)) (term (x_D* ...))))
   ;; Ensure strict positivity
   (side-condition (positive* x_D (t_c ...)))
   ----------------- "Valid-Inductive"
   (valid (Δ (x_D : t_D
               ;; Checks that a constructor for x actually produces an x, i.e., that
               ;; the constructor is well-formed.
               ((x_c : (name t_c (in-hole Ξ (in-hole Θ x_D*)))) ...))) ∅)])

(define-metafunction tt-typingL
  Γ-ref : Γ x -> t or #f
  [(Γ-ref ∅ x) #f]
  [(Γ-ref (Γ x : t) x) t]
  [(Γ-ref (Γ x_0 : t_0) x) (Γ-ref Γ x)])

(define-judgment-form tt-typingL
  #:mode (type-infer I I I O)
  #:contract (type-infer Δ Γ e t)

  [(where t (Γ-ref Γ x))
   (valid Δ Γ)
   ---------------------
   (type-infer Δ Γ x t)]

  [(valid Δ Γ)
   (where j ,(add1 (term i)))
   -----------------------------------
   (type-infer Δ Γ (Type i) (Type j))]

  [(valid Δ Γ)
   -------------------------------
   (type-infer Δ Γ (Prop) (Type 0))]

  [(type-infer Δ (Γ x : t_0) e t)
   -------------------------------------------------
   (type-infer Δ Γ (λ (x : t_0) e) (Π (x : t_0) t))]

  [(type-infer Δ Γ t_0 (Type i))
   (type-check Δ (Γ x : t_0) t (Type i))
   ------------------------------------------
   (type-infer Δ Γ (Π (x : t_0) t) (Type i))]

  [(type-check Δ (Γ x : t_0) t Prop)
   ------------------------------------------
   (type-infer Δ Γ (Π (x : t_0) t) Prop)]

  [(type-infer Δ Γ e_0 (Π (x : t_1) t))
   (type-check Δ Γ e_1 t_1)
   -------------------------------------------
   (type-infer Δ Γ (e_0 e_1) (subst t x e_1))]

  [(where t (Δ-elim-type Δ x_D U))
   (type-infer Δ Γ t U_e)
   --------------------------------
   (type-infer Δ Γ (elim x_D U) t)])

(define-judgment-form tt-typingL
  #:mode (type-check I I I I)
  #:contract (type-check Δ Γ e t)

  [(type-infer Δ Γ e t_1)
   (convert Δ t_1 t)
   ---------------------
   (type-check Δ Γ e t)])

;;; --------------------------------------------------------------------------------------------------
;;; Auxillary defs. Not necessary for the type theory, but helpful for examples
(define-metafunction imp-itt-typingL
  Γ-build : (x : t) ... -> Γ
  [(Γ-build) ∅]
  [(Γ-build (x_r : t_r) ...  (x : t))
   ((Γ-build (x_r : t_r) ...) x : t)])

(define-metafunction imp-itt-typingL
  Δ-build : (x : t ((x : t) ...)) ... -> Δ
  [(Δ-build) ∅]
  [(Δ-build any_0 ... any)
   ((Δ-build any_0 ...) any)])

(define-metafunction imp-itt-typingL
  apply : e ... -> e
  [(apply e e_0 e_r ...)
   (apply (e e_0) e_r ...)]
  [(apply e) e])
