(** * LinAlg/SpectralLa3.v
    Spectral / weight space decomposition of la3 = sl(2,F) with respect
    to ad la3_h.

    Standard fact: la3 = F·h ⊕ F·x ⊕ F·y where:
    - F·h is the 0-eigenspace of ad h
    - F·x is the +2 eigenspace
    - F·y is the -2 eigenspace

    This is the Cartan / weight space decomposition. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.Lie.LowDimensional.
From Stdlib Require Import List Ring Setoid.
Import ListNotations.

Section SpectralLa3.
  Context {F : Type} (fld : Field F).

  Local Lemma slm_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring slm_ring : slm_ring_theory.

  (** Eigenspace of ad la3_h for eigenvalue λ: { v | ad h v = λ·v }. *)
  Definition eigenspace_h (lam : F) (v : F * F * F) : Prop :=
    la3_bracket fld (la3_h fld) v = la3_scale fld lam v.

  (** F·x is in the +2 eigenspace of ad h. *)
  Theorem Fx_in_eigenspace_2 :
      forall a : F,
        eigenspace_h
          (cr_add fld (cr_one fld) (cr_one fld))
          (cr_mul fld a (cr_one fld), cr_zero fld, cr_zero fld).
  Proof.
    intros a. unfold eigenspace_h, la3_bracket, la3_h, la3_scale, mkT,
                    tF_x, tF_h, tF_y. cbn.
    apply (f_equal2 (@pair _ _)); [apply (f_equal2 (@pair _ _))|]; ring.
  Qed.

  (** F·y is in the -2 eigenspace. *)
  Theorem Fy_in_eigenspace_neg2 :
      forall c : F,
        eigenspace_h
          (cr_neg fld (cr_add fld (cr_one fld) (cr_one fld)))
          (cr_zero fld, cr_zero fld, cr_mul fld c (cr_one fld)).
  Proof.
    intros c. unfold eigenspace_h, la3_bracket, la3_h, la3_scale, mkT,
                    tF_x, tF_h, tF_y. cbn.
    apply (f_equal2 (@pair _ _)); [apply (f_equal2 (@pair _ _))|]; ring.
  Qed.

  (** F·h is in the 0 eigenspace. *)
  Theorem Fh_in_eigenspace_0 :
      forall b : F,
        eigenspace_h
          (cr_zero fld)
          (cr_zero fld, cr_mul fld b (cr_one fld), cr_zero fld).
  Proof.
    intros b. unfold eigenspace_h, la3_bracket, la3_h, la3_scale, mkT,
                    tF_x, tF_h, tF_y. cbn.
    apply (f_equal2 (@pair _ _)); [apply (f_equal2 (@pair _ _))|]; ring.
  Qed.

  (** Spectral decomposition: every (a, b, c) is the sum of its
      x-component (in 2-eigenspace), h-component (in 0-eigenspace),
      y-component (in -2-eigenspace). *)
  Theorem la3_spectral_decomp : forall a b c : F,
      (a, b, c) =
      la3_add fld
        (la3_add fld
          (cr_mul fld a (cr_one fld), cr_zero fld, cr_zero fld)
          (cr_zero fld, cr_mul fld b (cr_one fld), cr_zero fld))
        (cr_zero fld, cr_zero fld, cr_mul fld c (cr_one fld)).
  Proof.
    intros a b c. unfold la3_add, mkT, tF_x, tF_h, tF_y. cbn.
    apply (f_equal2 (@pair _ _)); [apply (f_equal2 (@pair _ _))|]; ring.
  Qed.

End SpectralLa3.
