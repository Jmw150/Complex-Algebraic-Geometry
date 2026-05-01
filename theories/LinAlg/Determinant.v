(** * LinAlg/Determinant.v
    Determinants of endomorphisms of F^2 and F^3.

    For an endomorphism f : V → V relative to a basis, the determinant
    is a scalar whose vanishing detects when f is non-invertible.
    Below we give explicit formulas in dimension 2 and 3. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.LinAlg.LinearMap.
Require Import CAG.LinAlg.Concrete.
From Stdlib Require Import List Ring Setoid.
Import ListNotations.

(* ================================================================== *)
(** * 1. det for End(F^2)                                              *)
(* ================================================================== *)

Section DetF2.
  Context {F : Type} (fld : Field F).

  Local Lemma df2_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring df2_ring : df2_ring_theory.

  (** det(f) = a11 * a22 - a12 * a21 *)
  Definition det_F2 (f : EndF (F2_as_VS fld)) : F :=
    cr_add fld
      (cr_mul fld
        (fst (lm_fn f (cr_one fld, cr_zero fld)))
        (snd (lm_fn f (cr_zero fld, cr_one fld))))
      (cr_neg fld (cr_mul fld
        (fst (lm_fn f (cr_zero fld, cr_one fld)))
        (snd (lm_fn f (cr_one fld, cr_zero fld))))).

  (** det of identity = 1. *)
  Theorem det_F2_id : det_F2 (lm_id (F2_as_VS fld)) = cr_one fld.
  Proof.
    unfold det_F2, lm_id. cbn. ring.
  Qed.

  (** det of zero = 0 (when 1+1 ≠ 0; actually 0 always since 0*0 - 0*0 = 0). *)
  Theorem det_F2_zero : det_F2 (end_zero (F2_as_VS fld)) = cr_zero fld.
  Proof.
    unfold det_F2, end_zero. cbn. ring.
  Qed.

  (** det of c·f = c^2 · det f. *)
  Theorem det_F2_scale : forall (c : F) (f : EndF (F2_as_VS fld)),
      det_F2 (end_scale c f) = cr_mul fld (cr_mul fld c c) (det_F2 f).
  Proof.
    intros c f. unfold det_F2, end_scale; cbn.
    destruct (lm_fn f (cr_one fld, cr_zero fld)) as [a1 a2].
    destruct (lm_fn f (cr_zero fld, cr_one fld)) as [b1 b2].
    cbn. ring.
  Qed.

End DetF2.

(* ================================================================== *)
(** * 2. det for End(F^3)                                              *)
(* ================================================================== *)

Section DetF3.
  Context {F : Type} (fld : Field F).

  Local Lemma df3_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring df3_ring : df3_ring_theory.

  (** Standard 3x3 determinant by cofactor expansion along the first row.
      det = a11(a22*a33 - a23*a32) - a12(a21*a33 - a23*a31)
                                   + a13(a21*a32 - a22*a31). *)
  Definition det_F3 (f : EndF (F3_as_VS fld)) : F :=
    let v1 := lm_fn f (cr_one fld, cr_zero fld, cr_zero fld) in
    let v2 := lm_fn f (cr_zero fld, cr_one fld, cr_zero fld) in
    let v3 := lm_fn f (cr_zero fld, cr_zero fld, cr_one fld) in
    let a11 := fst (fst v1) in let a21 := snd (fst v1) in let a31 := snd v1 in
    let a12 := fst (fst v2) in let a22 := snd (fst v2) in let a32 := snd v2 in
    let a13 := fst (fst v3) in let a23 := snd (fst v3) in let a33 := snd v3 in
    cr_add fld
      (cr_mul fld a11
        (cr_add fld (cr_mul fld a22 a33) (cr_neg fld (cr_mul fld a23 a32))))
      (cr_add fld
        (cr_neg fld (cr_mul fld a12
          (cr_add fld (cr_mul fld a21 a33) (cr_neg fld (cr_mul fld a23 a31)))))
        (cr_mul fld a13
          (cr_add fld (cr_mul fld a21 a32) (cr_neg fld (cr_mul fld a22 a31))))).

  Theorem det_F3_id : det_F3 (lm_id (F3_as_VS fld)) = cr_one fld.
  Proof.
    unfold det_F3, lm_id. cbn. ring.
  Qed.

  Theorem det_F3_zero : det_F3 (end_zero (F3_as_VS fld)) = cr_zero fld.
  Proof.
    unfold det_F3, end_zero. cbn. ring.
  Qed.

  Theorem det_F3_scale : forall (c : F) (f : EndF (F3_as_VS fld)),
      det_F3 (end_scale c f) =
      cr_mul fld (cr_mul fld (cr_mul fld c c) c) (det_F3 f).
  Proof.
    intros c f. unfold det_F3, end_scale; cbn.
    destruct (lm_fn f (cr_one fld, cr_zero fld, cr_zero fld)) as [[a11 a21] a31].
    destruct (lm_fn f (cr_zero fld, cr_one fld, cr_zero fld)) as [[a12 a22] a32].
    destruct (lm_fn f (cr_zero fld, cr_zero fld, cr_one fld)) as [[a13 a23] a33].
    cbn. ring.
  Qed.

End DetF3.
