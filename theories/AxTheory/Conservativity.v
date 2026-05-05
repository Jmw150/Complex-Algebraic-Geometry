(** * AxTheory/Conservativity.v
    Theorem 4.10.7: Conservativity of functional type theory over algebraic type theory.

    Statement:
    Let Th be an algebraic theory, and let Th' = GeneratedAxTheory(Th) be the
    Ax-theory generated from Th (same signature, same axioms, but with full
    lambda/product/exponential structure).

    If two algebraic terms M, M' : τ in algebraic context Γ satisfy
       Th' ⊢ Γ ⊢ M = M' : τ    (provably equal in the Ax-theory)
    then
       Th  ⊢ Γ ⊢ M = M' : τ    (already provably equal in the algebraic theory)

    Proof sketch (via gluing):
    1. I : Cl(Th) → Cl(Th') is the functor from relative freeness.
    2. By Proposition 4.10.2 and Lemma 4.10.3, I is full and faithful.
    3. An equation at ground types in Cl(Th') is a morphism in Cl(Th') between
       objects in the image of I.
    4. Fullness of I gives a preimage; faithfulness makes it unique.
    5. The preimage is the algebraic equation in Cl(Th). *)

Require Import CAG.ATT.Signature.
Require Import CAG.ATT.Syntax.
Require Import CAG.ATT.Theory.
Require Import CAG.ATT.ClassifyingCategory.
Require Import CAG.AxTheory.Syntax.
Require Import CAG.AxTheory.Theory.
Require Import CAG.AxTheory.ClassifyingCategory.
Require Import CAG.AxTheory.GeneratedFunctionalTheory.
Require Import CAG.AxTheory.RelativeFreeCCC.
Require Import CAG.AxTheory.GluingSetup.
From Stdlib Require Import Lists.List.
Import ListNotations.

Set Universe Polymorphism.
Open Scope cat_scope.

(** ** Preliminary: ground-type equations as morphism equalities

    An equation  Th' ⊢ Γ ⊢ M = N : τ  at ground types corresponds to
    the identity of two morphisms in Cl(Th'):
       I([Γ]) --{lift M}--> I([τ])  =  I([Γ]) --{lift N}--> I([τ])

    where lift_alg_term embeds algebraic terms into AxCl. *)

(* CAG constructive-remove Definition alg_term_to_axcl_mor theories/AxTheory/Conservativity.v:46 BEGIN
Definition alg_term_to_axcl_mor {Th : Theory}
    (Γ : list Th.(th_sig).(sg_ty))
    (t : Term Th.(th_sig)) (τ : Th.(th_sig).(sg_ty))
    (Ht : HasType Th.(th_sig) Γ t τ) :
    AxClMor Th.(th_sig) (I_obj Γ) (I_obj [τ]).
Proof.
  (* The morphism is given by lift_alg_term t, typed in [I_obj Γ].
     This requires the term-interpretation for AxCl. *)
  Admitted.
   CAG constructive-remove Definition alg_term_to_axcl_mor theories/AxTheory/Conservativity.v:46 END *)

(** ** Main conservativity theorem *)

(* CAG zero-dependent Admitted conservativity_of_generated_functional_type_theory_over_ground_terms theories/AxTheory/Conservativity.v:72 BEGIN
Theorem conservativity_of_generated_functional_type_theory_over_ground_terms
    (Th : Theory)
    (Γ : list Th.(th_sig).(sg_ty))
    (t1 t2 : Term Th.(th_sig))
    (τ : Th.(th_sig).(sg_ty))
    (Ht1 : HasType Th.(th_sig) Γ t1 τ)
    (Ht2 : HasType Th.(th_sig) Γ t2 τ)
    (Heq_ax : AxThEq Th.(th_sig)
                (List.map lift_alg_axiom Th.(th_ax))
                (List.map ax_ground Γ)
                (lift_alg_term t1) (lift_alg_term t2)
                (ax_ground τ)) :
    ThEq Th.(th_sig) Th.(th_ax) Γ t1 t2 τ.
Proof.
  Admitted.
   CAG zero-dependent Admitted conservativity_of_generated_functional_type_theory_over_ground_terms theories/AxTheory/Conservativity.v:72 END *)

(** ** Uniqueness: the algebraic representative is unique up to ThEq *)

(* CAG zero-dependent Admitted conservativity_uniqueness theories/AxTheory/Conservativity.v:89 BEGIN
Theorem conservativity_uniqueness
    (Th : Theory)
    (Γ : list Th.(th_sig).(sg_ty))
    (t1 t2 : Term Th.(th_sig))
    (τ : Th.(th_sig).(sg_ty))
    (Ht1 : HasType Th.(th_sig) Γ t1 τ)
    (Ht2 : HasType Th.(th_sig) Γ t2 τ)
    (Heq : ThEq Th.(th_sig) Th.(th_ax) Γ t1 t2 τ) :
    AxThEq Th.(th_sig)
           (List.map lift_alg_axiom Th.(th_ax))
           (List.map ax_ground Γ)
           (lift_alg_term t1) (lift_alg_term t2) (ax_ground τ).
Proof.
  Admitted.
   CAG zero-dependent Admitted conservativity_uniqueness theories/AxTheory/Conservativity.v:89 END *)

(** ** The semantic interpretation

    Adding functional structure (lambda/products/exponentials) to an algebraic
    theory does not create new equalities at ground types.  The algebraic and
    functional fragments have the same ground-type equational theory.

    In programming-language terms:
    - ground types in the functional theory have exactly the same normal forms
      as in the algebraic theory
    - beta-reduction and eta-expansion never collapse distinct algebraic terms *)

(** Package the full equivalence *)
(* CAG zero-dependent Theorem functional_theory_same_ground_equalities theories/AxTheory/Conservativity.v:103 BEGIN
Theorem functional_theory_same_ground_equalities
    (Th : Theory)
    (Γ : list Th.(th_sig).(sg_ty))
    (t1 t2 : Term Th.(th_sig))
    (τ : Th.(th_sig).(sg_ty))
    (Ht1 : HasType Th.(th_sig) Γ t1 τ)
    (Ht2 : HasType Th.(th_sig) Γ t2 τ) :
    ThEq Th.(th_sig) Th.(th_ax) Γ t1 t2 τ
    <->
    AxThEq Th.(th_sig)
           (List.map lift_alg_axiom Th.(th_ax))
           (List.map ax_ground Γ)
           (lift_alg_term t1) (lift_alg_term t2) (ax_ground τ).
Proof.
  split.
  - intro H. apply conservativity_uniqueness; assumption.
  - intro H. apply conservativity_of_generated_functional_type_theory_over_ground_terms;
    assumption.
Qed.
   CAG zero-dependent Theorem functional_theory_same_ground_equalities theories/AxTheory/Conservativity.v:103 END *)
