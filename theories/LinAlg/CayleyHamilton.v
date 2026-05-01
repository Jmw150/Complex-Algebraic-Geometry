(** * LinAlg/CayleyHamilton.v
    The Cayley-Hamilton theorem for 2x2 matrices: every 2x2 endomorphism
    satisfies its characteristic polynomial.

    For M : F^2 → F^2 with trace t and det d:
        M² - t·M + d·I = 0
    or equivalently
        M ∘ M = t · M - d · I. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.LinAlg.LinearMap.
Require Import CAG.LinAlg.Concrete.
Require Import CAG.LinAlg.Trace.
Require Import CAG.LinAlg.Determinant.
From Stdlib Require Import List Ring Setoid.
Import ListNotations.

Require Import CAG.LinAlg.Eigenvalue.

(* ================================================================== *)
(** * 1. Cayley-Hamilton for 2x2 matrices                              *)
(* ================================================================== *)

Section CayleyHamiltonF2.
  Context {F : Type} (fld : Field F).

  Local Lemma chf2_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring chf2_ring : chf2_ring_theory.

  (** Cayley-Hamilton for End(F^2): M² - trace(M)·M + det(M)·I = 0
      Stated: for all v, M(M(v)) = trace(M)·M(v) - det(M)·v. *)
  Theorem cayley_hamilton_F2 : forall (M : EndF (F2_as_VS fld)) (v : F * F),
      lm_fn M (lm_fn M v) =
      vsF_add (F2_as_VS fld)
        (vsF_scale (F2_as_VS fld) (trace_F2 fld M) (lm_fn M v))
        (vsF_neg (F2_as_VS fld)
          (vsF_scale (F2_as_VS fld) (det_F2 fld M) v)).
  Proof.
    intros M [v1 v2].
    (* Strategy: write v = v1 · e1 + v2 · e2, then use linearity. *)
    pose proof (F2_linear_expand fld M) as Hf.
    rewrite (Hf v1 v2).
    set (a := lm_fn M (cr_one fld, cr_zero fld)).
    set (b := lm_fn M (cr_zero fld, cr_one fld)).
    destruct a as [a11 a21] eqn:Ea.
    destruct b as [a12 a22] eqn:Eb.
    (* M(v) = v1 · (a11, a21) + v2 · (a12, a22) = (v1*a11 + v2*a12, v1*a21 + v2*a22). *)
    cbn.
    rewrite (Hf (cr_add fld (cr_mul fld v1 a11) (cr_mul fld v2 a12))
                (cr_add fld (cr_mul fld v1 a21) (cr_mul fld v2 a22))).
    unfold a, b in *.
    rewrite Ea, Eb.
    unfold trace_F2, det_F2. cbn.
    rewrite Ea, Eb. cbn.
    f_equal; ring.
  Qed.

End CayleyHamiltonF2.

(* ================================================================== *)
(** * 2. Cayley-Hamilton for 3x3 matrices                              *)
(* ================================================================== *)

Section CayleyHamiltonF3.
  Context {F : Type} (fld : Field F).

  Local Lemma chf3_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring chf3_ring : chf3_ring_theory.

  (** Cayley-Hamilton for End(F^3): M^3 - tr(M)·M^2 + s(M)·M - det(M)·I = 0
      where s(M) is the sum of 2x2 principal minors. *)
  Theorem cayley_hamilton_F3 : forall (M : EndF (F3_as_VS fld)) (v : F * F * F),
      lm_fn M (lm_fn M (lm_fn M v)) =
      vsF_add (F3_as_VS fld)
        (vsF_scale (F3_as_VS fld) (trace_F3 fld M) (lm_fn M (lm_fn M v)))
        (vsF_add (F3_as_VS fld)
          (vsF_neg (F3_as_VS fld)
            (vsF_scale (F3_as_VS fld) (charpoly_F3_minor_sum fld M) (lm_fn M v)))
          (vsF_scale (F3_as_VS fld) (det_F3 fld M) v)).
  Proof.
    intros M [[v1 v2] v3].
    pose proof (F3_linear_expand fld M) as Hf.
    rewrite (Hf v1 v2 v3).
    set (a := lm_fn M (cr_one fld, cr_zero fld, cr_zero fld)).
    set (b := lm_fn M (cr_zero fld, cr_one fld, cr_zero fld)).
    set (c := lm_fn M (cr_zero fld, cr_zero fld, cr_one fld)).
    destruct a as [[a11 a21] a31] eqn:Ea.
    destruct b as [[a12 a22] a32] eqn:Eb.
    destruct c as [[a13 a23] a33] eqn:Ec.
    cbn.
    rewrite (Hf
      (cr_add fld (cr_mul fld v1 a11)
        (cr_add fld (cr_mul fld v2 a12) (cr_mul fld v3 a13)))
      (cr_add fld (cr_mul fld v1 a21)
        (cr_add fld (cr_mul fld v2 a22) (cr_mul fld v3 a23)))
      (cr_add fld (cr_mul fld v1 a31)
        (cr_add fld (cr_mul fld v2 a32) (cr_mul fld v3 a33)))).
    unfold a, b, c in *.
    rewrite Ea, Eb, Ec. cbn.
    rewrite (Hf _ _ _). (* M^3 v *)
    unfold a, b, c in *. rewrite Ea, Eb, Ec. cbn.
    unfold trace_F3, det_F3, charpoly_F3_minor_sum.
    cbn. rewrite Ea, Eb, Ec. cbn.
    f_equal; [f_equal|]; ring.
  Qed.

End CayleyHamiltonF3.
