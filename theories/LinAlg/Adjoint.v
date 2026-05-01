(** * LinAlg/Adjoint.v
    The adjoint representation: bridge from Lie algebras to linear maps.

    Given a Lie algebra [la : LieAlgebraF fld L] and an element x ∈ L,
    the map ad_x = (y ↦ [x, y]) : L → L is linear (right-bilinearity of
    bracket). This module packages it as a [LinearMapF].

    It also provides the bridge needed to define the Killing form
    K(x, y) = trace(ad_x ∘ ad_y) for concrete Lie algebras whose
    carrier is a known finite-dim vector space. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.LinAlg.LinearMap.
From Stdlib Require Import List.
Import ListNotations.

(* ================================================================== *)
(** * 1. ad x is a linear endomorphism of L                           *)
(* ================================================================== *)

(** Given x : L, the map ad_x : L → L (y ↦ [x, y]) is linear. *)
Definition lie_ad {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (x : L) : EndF (laF_vs la).
Proof.
  refine {| lm_fn := fun y => laF_bracket la x y; |}.
  - intros u v. apply la.(laF_bracket_add_r).
  - intros a v. apply la.(laF_bracket_scale_r).
Defined.

(** Composition of adjoint maps. *)
Definition lie_ad_comp {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (x y : L) : EndF (laF_vs la) :=
  lm_comp (lie_ad la x) (lie_ad la y).

(** Adjoint at zero is the zero endomorphism. *)
Lemma lie_ad_zero {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    forall y, lm_fn (lie_ad la (la_zero la)) y = la_zero la.
Proof.
  intro y. unfold lie_ad. simpl. apply laF_bracket_zero_l.
Qed.

(** Adjoint of negation: ad(-x) y = -ad(x) y. *)
Lemma lie_ad_neg_eq {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (x y : L) :
    lm_fn (lie_ad la (la_neg la x)) y = la_neg la (lm_fn (lie_ad la x) y).
Proof.
  unfold lie_ad. simpl. apply laF_bracket_neg_l.
Qed.

(** Adjoint of scalar: ad(c·x) y = c · ad(x) y. *)
Lemma lie_ad_scale_eq {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (c : F) (x y : L) :
    lm_fn (lie_ad la (la_scale la c x)) y = la_scale la c (lm_fn (lie_ad la x) y).
Proof.
  unfold lie_ad. simpl. apply la.(laF_bracket_scale_l).
Qed.

(** Adjoint of sum: ad(x + y) z = ad(x) z + ad(y) z. *)
Lemma lie_ad_add_eq {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (x y z : L) :
    lm_fn (lie_ad la (la_add la x y)) z =
    la_add la (lm_fn (lie_ad la x) z) (lm_fn (lie_ad la y) z).
Proof.
  unfold lie_ad. simpl. apply la.(laF_bracket_add_l).
Qed.
