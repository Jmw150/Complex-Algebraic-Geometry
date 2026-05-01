(** * LinAlg/AdSemisimple.v
    Ad-semisimple elements of a Lie algebra: x is ad-semisimple if
    ad x is diagonalizable, i.e. there is a basis of L consisting of
    eigenvectors of ad x.

    For sl(2,F), h is ad-semisimple: x, h, y are eigenvectors with
    eigenvalues 2, 0, -2. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.Lie.LowDimensional.
Require Import CAG.LinAlg.LinearMap.
Require Import CAG.LinAlg.Adjoint.
Require Import CAG.LinAlg.Eigenvalue.
From Stdlib Require Import List Ring Setoid.
Import ListNotations.

(* ================================================================== *)
(** * 1. la3_h's eigenstructure under ad                               *)
(* ================================================================== *)

Section AdHEigen.
  Context {F : Type} (fld : Field F).

  Local Lemma adh_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring adh_ring : adh_ring_theory.

  (** ad la3_h applied to la3_x = 2 · la3_x (eigenvalue 2). *)
  Theorem ad_h_x_eigen :
      lm_fn (lie_ad (la3 fld) (la3_h fld)) (la3_x fld) =
      la3_scale fld (cr_add fld (cr_one fld) (cr_one fld)) (la3_x fld).
  Proof.
    unfold lie_ad. simpl.
    unfold la3_bracket, la3_h, la3_x, la3_scale, mkT, tF_x, tF_h, tF_y.
    cbn. f_equal. - f_equal; ring. - ring.
  Qed.

  (** ad la3_h applied to la3_y = -2 · la3_y (eigenvalue -2). *)
  Theorem ad_h_y_eigen :
      lm_fn (lie_ad (la3 fld) (la3_h fld)) (la3_y fld) =
      la3_scale fld
        (cr_neg fld (cr_add fld (cr_one fld) (cr_one fld)))
        (la3_y fld).
  Proof.
    unfold lie_ad. simpl.
    unfold la3_bracket, la3_h, la3_y, la3_scale, mkT, tF_x, tF_h, tF_y.
    cbn. f_equal. - f_equal; ring. - ring.
  Qed.

  (** ad la3_h applied to la3_h = 0 (eigenvalue 0). *)
  Theorem ad_h_h_eigen :
      lm_fn (lie_ad (la3 fld) (la3_h fld)) (la3_h fld) = la_zero (la3 fld).
  Proof.
    unfold lie_ad. simpl.
    unfold la3_bracket, la3_h, la_zero, la3, ex2_vs, mkT, tF_x, tF_h, tF_y.
    cbn.
    apply (f_equal2 (@pair _ _)); [apply (f_equal2 (@pair _ _))|]; ring.
  Qed.

  (** la3_x is an eigenvector of ad h with eigenvalue 2 (when 1 ≠ 0). *)
  Theorem la3_x_eigenvector_h :
      cr_one fld <> cr_zero fld ->
      IsEigenvector (laF_vs (la3 fld))
        (lie_ad (la3 fld) (la3_h fld))
        (cr_add fld (cr_one fld) (cr_one fld))
        (la3_x fld).
  Proof.
    intros Hone. split.
    - apply (la3_x_nonzero fld). exact Hone.
    - exact ad_h_x_eigen.
  Qed.

  (** la3_y is an eigenvector with eigenvalue -2. *)
  Theorem la3_y_eigenvector_h :
      cr_one fld <> cr_zero fld ->
      IsEigenvector (laF_vs (la3 fld))
        (lie_ad (la3 fld) (la3_h fld))
        (cr_neg fld (cr_add fld (cr_one fld) (cr_one fld)))
        (la3_y fld).
  Proof.
    intros Hone. split.
    - apply (la3_y_nonzero fld). exact Hone.
    - exact ad_h_y_eigen.
  Qed.

  (** la3_h is an eigenvector with eigenvalue 0. *)
  Theorem la3_h_eigenvector_h :
      cr_one fld <> cr_zero fld ->
      IsEigenvector (laF_vs (la3 fld))
        (lie_ad (la3 fld) (la3_h fld))
        (cr_zero fld)
        (la3_h fld).
  Proof.
    intros Hone. split.
    + apply (la3_h_nonzero fld). exact Hone.
    + rewrite ad_h_h_eigen.
      unfold la_zero, la3, ex2_vs, vsF_scale; cbn.
      unfold la3_h, mkT, tF_x, tF_h, tF_y. cbn.
      apply (f_equal2 (@pair _ _)); [apply (f_equal2 (@pair _ _))|]; ring.
  Qed.

  (** Each eigenvalue of ad h is realized: 2, 0, -2 are eigenvalues. *)
  Theorem two_is_eigenvalue_h :
      cr_one fld <> cr_zero fld ->
      IsEigenvalue (laF_vs (la3 fld))
        (lie_ad (la3 fld) (la3_h fld))
        (cr_add fld (cr_one fld) (cr_one fld)).
  Proof.
    intros Hone. exists (la3_x fld). apply la3_x_eigenvector_h. exact Hone.
  Qed.

  Theorem neg_two_is_eigenvalue_h :
      cr_one fld <> cr_zero fld ->
      IsEigenvalue (laF_vs (la3 fld))
        (lie_ad (la3 fld) (la3_h fld))
        (cr_neg fld (cr_add fld (cr_one fld) (cr_one fld))).
  Proof.
    intros Hone. exists (la3_y fld). apply la3_y_eigenvector_h. exact Hone.
  Qed.

  Theorem zero_is_eigenvalue_h :
      cr_one fld <> cr_zero fld ->
      IsEigenvalue (laF_vs (la3 fld))
        (lie_ad (la3 fld) (la3_h fld))
        (cr_zero fld).
  Proof.
    intros Hone. exists (la3_h fld). apply la3_h_eigenvector_h. exact Hone.
  Qed.

End AdHEigen.
