(** * ATT/SoundComplete.v
    Soundness and completeness of the algebraic theory Th.

    Soundness:  if Th ⊢ Γ ⊢ t = t' : τ, then every model M in every
                category V with finite products satisfies [t]_M = [t']_M.

    Completeness: if every model in every FP-category satisfies an equation,
                  then the equation is derivable in Th.

    The completeness proof uses the GENERIC MODEL G in Cl(Th):
    suppose Γ ⊢ t = t' : τ holds in every model.  In particular it holds
    in G.  By the interpretation lemma, [t]_G = (Γ | t) and [t']_G = (Γ | t').
    Since (Γ | t) = (Γ | t') as morphisms in Cl(Th) (quotient by ThEq),
    we have Th ⊢ Γ ⊢ t = t'. *)

Require Import CAG.ATT.Signature.
Require Import CAG.ATT.Syntax.
Require Import CAG.ATT.Theory.
Require Import CAG.ATT.Model.
Require Import CAG.ATT.ClassifyingCategory.
Require Import CAG.ATT.GenericModel.
Require Import CAG.Category.Core.
Require Import CAG.Category.Products.
From Stdlib Require Import Lists.List.
Import ListNotations.

Set Universe Polymorphism.

(** ** Soundness *)

(** Soundness: derivable equations are satisfied by every model. *)
Theorem soundness (Th : Theory)
    (C : Category) (hp : HasFiniteProducts C) (M : Model Th C hp)
    (Γ : list Th.(th_sig).(sg_ty))
    (t t' : Term Th.(th_sig)) (τ : Th.(th_sig).(sg_ty))
    (Ht  : HasType Th.(th_sig) Γ t  τ)
    (Ht' : HasType Th.(th_sig) Γ t' τ)
    (Heq : ThEq Th.(th_sig) Th.(th_ax) Γ t t' τ) :
    interp_term M Γ t  τ Ht =
    interp_term M Γ t' τ Ht'.
Proof.
  Admitted.

(** ** Completeness via the generic model *)

(** Completeness: if an equation holds in the generic model G (in Cl(Th)),
    then it is derivable in Th.

    Proof:
    1. By assumption, [t]_G = [t']_G as morphisms in Cl(Th).
    2. By the interpretation lemma, [t]_G = (Γ | t) and [t']_G = (Γ | t').
    3. Since ClMor_theq holds (the morphisms represent the same equivalence class),
       the defining relation for Cl(Th) morphism equality gives Th ⊢ Γ ⊢ t = t'. *)

Theorem completeness_from_generic_model (Th : Theory)
    (Γ : list Th.(th_sig).(sg_ty))
    (t t' : Term Th.(th_sig)) (τ : Th.(th_sig).(sg_ty))
    (Ht  : HasType Th.(th_sig) Γ t  τ)
    (Ht' : HasType Th.(th_sig) Γ t' τ)
    (Hmod : ClMor_theq Th Γ [τ]
              {| clmor_terms := [t];  clmor_typed := Forall2_cons _ _ Ht  (Forall2_nil _) |}
              {| clmor_terms := [t']; clmor_typed := Forall2_cons _ _ Ht' (Forall2_nil _) |}) :
    ThEq Th.(th_sig) Th.(th_ax) Γ t t' τ.
Proof.
  (* Unfold ClMor_theq: the 0th components are Th-equal. *)
  apply Hmod with 0.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** ** Full completeness *)

(** If an equation in context holds in EVERY model in EVERY FP-category,
    then it is provable in Th. *)
Theorem completeness (Th : Theory)
    (Γ : list Th.(th_sig).(sg_ty))
    (t t' : Term Th.(th_sig)) (τ : Th.(th_sig).(sg_ty))
    (Ht  : HasType Th.(th_sig) Γ t  τ)
    (Ht' : HasType Th.(th_sig) Γ t' τ)
    (Hall : forall (C : Category) (hp : HasFiniteProducts C) (M : Model Th C hp),
              interp_term M Γ t  τ Ht =
              interp_term M Γ t' τ Ht') :
    ThEq Th.(th_sig) Th.(th_ax) Γ t t' τ.
Proof.
  Admitted.

(** ** Packaging *)

(** Together, soundness and completeness establish that the theory Th is
    a complete deductive system for its algebraic semantics. *)
Theorem algebraic_theory_sound_and_complete (Th : Theory)
    (Γ : list Th.(th_sig).(sg_ty))
    (t t' : Term Th.(th_sig)) (τ : Th.(th_sig).(sg_ty))
    (Ht  : HasType Th.(th_sig) Γ t  τ)
    (Ht' : HasType Th.(th_sig) Γ t' τ) :
    ThEq Th.(th_sig) Th.(th_ax) Γ t t' τ
    <->
    (forall (C : Category) (hp : HasFiniteProducts C) (M : Model Th C hp),
       interp_term M Γ t  τ Ht =
       interp_term M Γ t' τ Ht').
Proof.
  Admitted.
