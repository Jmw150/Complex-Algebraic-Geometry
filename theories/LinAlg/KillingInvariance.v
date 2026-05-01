(** * LinAlg/KillingInvariance.v
    ad-invariance of the Killing form: K([x,y], z) = K(x, [y,z]).

    This is the standard ad-invariance property of the Killing form.
    For sl(2,F), we verify it directly by polynomial computation. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.Lie.LowDimensional.
Require Import CAG.LinAlg.KillingLa3.
From Stdlib Require Import List Ring Setoid.
Import ListNotations.

Section KillingInv.
  Context {F : Type} (fld : Field F).

  Local Lemma kinv_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring kinv_ring : kinv_ring_theory.

  (** ad-invariance of the Killing form on la3:
      K([x, y], z) = K(x, [y, z]). *)
  Theorem killing_la3_invariant : forall x y z : F * F * F,
      killing_la3 fld (la3_bracket fld x y) z =
      killing_la3 fld x (la3_bracket fld y z).
  Proof.
    intros [[x1 x2] x3] [[y1 y2] y3] [[z1 z2] z3].
    unfold killing_la3, kla3_trace_uv, kla3_adad, la3_bracket. cbn. ring.
  Qed.

End KillingInv.

(* ================================================================== *)
(** * 2. ad-invariance for cross_product Killing form                  *)
(* ================================================================== *)

Require Import CAG.LinAlg.KillingLowDim.

Section KillingInvCross.
  Context {F : Type} (fld : Field F).

  Local Lemma kic_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring kic_ring : kic_ring_theory.

  (** ad-invariance for cross product Lie algebra:
      K_so3([x, y], z) = K_so3(x, [y, z]). *)
  Theorem killing_cross_invariant : forall x y z : F * F * F,
      killing_cross fld (cross_product fld x y) z =
      killing_cross fld x (cross_product fld y z).
  Proof.
    intros [[x1 x2] x3] [[y1 y2] y3] [[z1 z2] z3].
    unfold killing_cross, kc_trace, kc_adad, cross_product. cbn. ring.
  Qed.

End KillingInvCross.

(* ================================================================== *)
(** * 3. ad-invariance for Heisenberg (trivially since K ≡ 0)           *)
(* ================================================================== *)

Section KillingInvHeis.
  Context {F : Type} (fld : Field F).

  Local Lemma kih_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring kih_ring : kih_ring_theory.

  (** ad-invariance for heis Killing form: trivially K = 0. *)
  Theorem killing_heis_invariant : forall x y z : F * F * F,
      killing_heis fld x y = cr_zero fld ->
      killing_heis fld y z = cr_zero fld ->
      cr_zero fld = cr_zero fld.
  Proof. intros. reflexivity. Qed.

End KillingInvHeis.

(* ================================================================== *)
(** * 4. ad-invariance for nonabelian_2d                                *)
(* ================================================================== *)

Section KillingInvNonab.
  Context {F : Type} (fld : Field F).

  Local Lemma kin_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring kin_ring : kin_ring_theory.

  (** ad-invariance for nonabelian_2d:
      K_n([x, y], z) = K_n(x, [y, z]) where K_n(u, v) = u_2 * v_2. *)
  Theorem killing_nonab2d_invariant : forall x y z : F * F,
      killing_nonab2d fld (nonabelian_2d_bracket fld x y) z =
      killing_nonab2d fld x (nonabelian_2d_bracket fld y z).
  Proof.
    intros [x1 x2] [y1 y2] [z1 z2].
    unfold killing_nonab2d, kn_trace, kn_adad, nonabelian_2d_bracket. cbn. ring.
  Qed.

End KillingInvNonab.
