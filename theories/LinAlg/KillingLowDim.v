(** * LinAlg/KillingLowDim.v
    Killing forms for the other low-dim Lie algebras:
    - cross_product_lie (so(3) on F^3)
    - heis (Heisenberg algebra on F^3)
    - nonabelian_2d (the 2D nonabelian on F^2)

    Each has its Killing form computed concretely via direct trace
    of ad-compositions. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.Lie.LowDimensional.
From Stdlib Require Import List Ring Setoid.
Import ListNotations.

(* ================================================================== *)
(** * 1. Killing form for cross_product_lie (so(3))                    *)
(* ================================================================== *)

Section KillingCross.
  Context {F : Type} (fld : Field F).

  Local Lemma kc_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring kc_ring : kc_ring_theory.

  Definition kc_adad (u v w : F * F * F) : F * F * F :=
    cross_product fld u (cross_product fld v w).

  Definition kc_trace (u v : F * F * F) : F :=
    cr_add fld
      (fst (fst (kc_adad u v (cr_one fld, cr_zero fld, cr_zero fld))))
      (cr_add fld
        (snd (fst (kc_adad u v (cr_zero fld, cr_one fld, cr_zero fld))))
        (snd (kc_adad u v (cr_zero fld, cr_zero fld, cr_one fld)))).

  Definition killing_cross (u v : F * F * F) : F := kc_trace u v.

  Notation cre1 := (cr_one fld, cr_zero fld, cr_zero fld) (only parsing).
  Notation cre2 := (cr_zero fld, cr_one fld, cr_zero fld) (only parsing).
  Notation cre3 := (cr_zero fld, cr_zero fld, cr_one fld) (only parsing).

  (** Killing form values on basis: K(e_i, e_j) = -2δ_ij.
      For cross product, K(u, v) = -2 (u · v) where · is standard dot product. *)

  (** K(e1, e1) = -2 = -(1 + 1). *)
  Theorem killing_cross_e1_e1 : killing_cross cre1 cre1 =
    cr_neg fld (cr_add fld (cr_one fld) (cr_one fld)).
  Proof.
    unfold killing_cross, kc_trace, kc_adad, cross_product. cbn. ring.
  Qed.

  Theorem killing_cross_e2_e2 : killing_cross cre2 cre2 =
    cr_neg fld (cr_add fld (cr_one fld) (cr_one fld)).
  Proof.
    unfold killing_cross, kc_trace, kc_adad, cross_product. cbn. ring.
  Qed.

  Theorem killing_cross_e3_e3 : killing_cross cre3 cre3 =
    cr_neg fld (cr_add fld (cr_one fld) (cr_one fld)).
  Proof.
    unfold killing_cross, kc_trace, kc_adad, cross_product. cbn. ring.
  Qed.

  Theorem killing_cross_e1_e2 : killing_cross cre1 cre2 = cr_zero fld.
  Proof.
    unfold killing_cross, kc_trace, kc_adad, cross_product. cbn. ring.
  Qed.

  Theorem killing_cross_e1_e3 : killing_cross cre1 cre3 = cr_zero fld.
  Proof.
    unfold killing_cross, kc_trace, kc_adad, cross_product. cbn. ring.
  Qed.

  Theorem killing_cross_e2_e3 : killing_cross cre2 cre3 = cr_zero fld.
  Proof.
    unfold killing_cross, kc_trace, kc_adad, cross_product. cbn. ring.
  Qed.

  Theorem killing_cross_symm : forall u v, killing_cross u v = killing_cross v u.
  Proof.
    intros [[ux uy] uz] [[vx vy] vz].
    unfold killing_cross, kc_trace, kc_adad, cross_product. cbn. ring.
  Qed.

  Theorem killing_cross_general : forall u v : F * F * F,
      let '(ux, uy, uz) := u in
      let '(vx, vy, vz) := v in
      killing_cross u v =
      cr_neg fld (cr_mul fld (cr_add fld (cr_one fld) (cr_one fld))
        (cr_add fld (cr_mul fld ux vx)
          (cr_add fld (cr_mul fld uy vy) (cr_mul fld uz vz)))).
  Proof.
    intros [[ux uy] uz] [[vx vy] vz].
    unfold killing_cross, kc_trace, kc_adad, cross_product. cbn. ring.
  Qed.

End KillingCross.

(* ================================================================== *)
(** * 2. Killing form for Heisenberg algebra                          *)
(* ================================================================== *)

Section KillingHeis.
  Context {F : Type} (fld : Field F).

  Local Lemma kh_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring kh_ring : kh_ring_theory.

  (** heis_bracket(u, v) = (0, 0, u_x * v_y - u_y * v_x). *)
  Definition khz_bracket (u v : F * F * F) : F * F * F :=
    (cr_zero fld, cr_zero fld,
     cr_add fld (cr_mul fld (fst (fst u)) (snd (fst v)))
                (cr_neg fld (cr_mul fld (snd (fst u)) (fst (fst v))))).

  Definition khz_adad (u v w : F * F * F) : F * F * F :=
    khz_bracket u (khz_bracket v w).

  Definition kh_trace (u v : F * F * F) : F :=
    cr_add fld
      (fst (fst (khz_adad u v (cr_one fld, cr_zero fld, cr_zero fld))))
      (cr_add fld
        (snd (fst (khz_adad u v (cr_zero fld, cr_one fld, cr_zero fld))))
        (snd (khz_adad u v (cr_zero fld, cr_zero fld, cr_one fld)))).

  Definition killing_heis (u v : F * F * F) : F := kh_trace u v.

  (** Heisenberg's Killing form is identically zero (since heis is
      nilpotent, all ad u are nilpotent, and trace of nilpotent is 0). *)
  Theorem killing_heis_zero : forall u v, killing_heis u v = cr_zero fld.
  Proof.
    intros [[ux uy] uz] [[vx vy] vz].
    unfold killing_heis, kh_trace, khz_adad, khz_bracket. cbn. ring.
  Qed.

End KillingHeis.

(* ================================================================== *)
(** * 3. Killing form for nonabelian_2d                                *)
(* ================================================================== *)

Section KillingNonab2d.
  Context {F : Type} (fld : Field F).

  Local Lemma kn_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring kn_ring : kn_ring_theory.

  Definition kn_adad (u v w : F * F) : F * F :=
    nonabelian_2d_bracket fld u (nonabelian_2d_bracket fld v w).

  Definition kn_trace (u v : F * F) : F :=
    cr_add fld
      (fst (kn_adad u v (cr_one fld, cr_zero fld)))
      (snd (kn_adad u v (cr_zero fld, cr_one fld))).

  Definition killing_nonab2d (u v : F * F) : F := kn_trace u v.

  Notation n2x := (cr_one fld, cr_zero fld) (only parsing).
  Notation n2y := (cr_zero fld, cr_one fld) (only parsing).

  Theorem killing_nonab2d_xx : killing_nonab2d n2x n2x = cr_zero fld.
  Proof.
    unfold killing_nonab2d, kn_trace, kn_adad, nonabelian_2d_bracket. cbn. ring.
  Qed.

  Theorem killing_nonab2d_yy : killing_nonab2d n2y n2y = cr_one fld.
  Proof.
    unfold killing_nonab2d, kn_trace, kn_adad, nonabelian_2d_bracket. cbn. ring.
  Qed.

  Theorem killing_nonab2d_xy : killing_nonab2d n2x n2y = cr_zero fld.
  Proof.
    unfold killing_nonab2d, kn_trace, kn_adad, nonabelian_2d_bracket. cbn. ring.
  Qed.

  (** General formula: K(u, v) = u_y * v_y. *)
  Theorem killing_nonab2d_general : forall u v : F * F,
      killing_nonab2d u v = cr_mul fld (snd u) (snd v).
  Proof.
    intros [ux uy] [vx vy].
    unfold killing_nonab2d, kn_trace, kn_adad, nonabelian_2d_bracket. cbn. ring.
  Qed.

  (** Killing form on nonabelian_2d is degenerate: K(x, ·) = 0 always. *)
  Theorem killing_nonab2d_degenerate :
      forall v, killing_nonab2d n2x v = cr_zero fld.
  Proof.
    intro v.
    rewrite killing_nonab2d_general. cbn.
    apply (cr_mul_zero_l fld).
  Qed.

End KillingNonab2d.
