(** * LinAlg/Eigenvalue.v
    Eigenvalues and eigenvectors of endomorphisms.

    An eigenvector v of f with eigenvalue λ satisfies f(v) = λ·v.
    A scalar λ is an eigenvalue if there exists a nonzero eigenvector.
    Equivalently (in finite dim): det(f - λ·id) = 0. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.LinAlg.LinearMap.
Require Import CAG.LinAlg.Concrete.
Require Import CAG.LinAlg.Trace.
Require Import CAG.LinAlg.Determinant.
From Stdlib Require Import List Ring Setoid.
Import ListNotations.

(* ================================================================== *)
(** * 1. Eigenvalues / eigenvectors (general)                          *)
(* ================================================================== *)

Section EigenGen.
  Context {F : Type} {fld : Field F} {V : Type} (vs : VectorSpaceF fld V).

  (** v is an eigenvector of f with eigenvalue λ iff f(v) = λ·v and v ≠ 0. *)
  Definition IsEigenvector (f : EndF vs) (lam : F) (v : V) : Prop :=
    v <> vsF_zero vs /\ lm_fn f v = vsF_scale vs lam v.

  (** λ is an eigenvalue of f iff there exists a nonzero eigenvector. *)
  Definition IsEigenvalue (f : EndF vs) (lam : F) : Prop :=
    exists v : V, IsEigenvector f lam v.

End EigenGen.

(* ================================================================== *)
(** * 2. Characteristic polynomial coefficients (2x2 and 3x3)          *)
(* ================================================================== *)

Section CharPolyF2.
  Context {F : Type} (fld : Field F).

  Local Lemma cpf2_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring cpf2_ring : cpf2_ring_theory.

  (** Characteristic polynomial of f : F^2 → F^2 in variable λ:
      p_f(λ) = λ^2 - trace(f)·λ + det(f). *)
  Definition charpoly_F2 (f : EndF (F2_as_VS fld)) (lam : F) : F :=
    cr_add fld (cr_mul fld lam lam)
      (cr_add fld (cr_neg fld (cr_mul fld (trace_F2 fld f) lam))
                  (det_F2 fld f)).

  (** λ is an eigenvalue iff charpoly evaluates to 0. *)
  Definition IsRoot_charpoly_F2 (f : EndF (F2_as_VS fld)) (lam : F) : Prop :=
    charpoly_F2 f lam = cr_zero fld.

  (** Vieta's formulas: if λ_1 + λ_2 = trace and λ_1·λ_2 = det, both are roots. *)
  Theorem charpoly_F2_vieta : forall (f : EndF (F2_as_VS fld)) (lam mu : F),
      cr_add fld lam mu = trace_F2 fld f ->
      cr_mul fld lam mu = det_F2 fld f ->
      charpoly_F2 f lam = cr_zero fld /\ charpoly_F2 f mu = cr_zero fld.
  Proof.
    intros f lam mu Hsum Hprod.
    split.
    - unfold charpoly_F2. rewrite <- Hsum, <- Hprod. ring.
    - unfold charpoly_F2. rewrite <- Hsum, <- Hprod. ring.
  Qed.

End CharPolyF2.

(* ================================================================== *)
(** * 3. Characteristic polynomial for 3x3                             *)
(* ================================================================== *)

Section CharPolyF3.
  Context {F : Type} (fld : Field F).

  Local Lemma cpf3_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring cpf3_ring : cpf3_ring_theory.

  (** Sum of 2x2 principal minors = (a11*a22 - a12*a21) + (a11*a33 - a13*a31)
                                    + (a22*a33 - a23*a32). *)
  Definition charpoly_F3_minor_sum (f : EndF (F3_as_VS fld)) : F :=
    let v1 := lm_fn f (cr_one fld, cr_zero fld, cr_zero fld) in
    let v2 := lm_fn f (cr_zero fld, cr_one fld, cr_zero fld) in
    let v3 := lm_fn f (cr_zero fld, cr_zero fld, cr_one fld) in
    let a11 := fst (fst v1) in let a21 := snd (fst v1) in let a31 := snd v1 in
    let a12 := fst (fst v2) in let a22 := snd (fst v2) in let a32 := snd v2 in
    let a13 := fst (fst v3) in let a23 := snd (fst v3) in let a33 := snd v3 in
    cr_add fld
      (cr_add fld (cr_mul fld a11 a22) (cr_neg fld (cr_mul fld a12 a21)))
      (cr_add fld
        (cr_add fld (cr_mul fld a11 a33) (cr_neg fld (cr_mul fld a13 a31)))
        (cr_add fld (cr_mul fld a22 a33) (cr_neg fld (cr_mul fld a23 a32)))).

  (** Characteristic polynomial of 3x3:
      p_f(λ) = λ^3 - tr(f)·λ^2 + (sum of 2x2 minors)·λ - det(f). *)
  Definition charpoly_F3 (f : EndF (F3_as_VS fld)) (lam : F) : F :=
    cr_add fld (cr_mul fld lam (cr_mul fld lam lam))
      (cr_add fld (cr_neg fld (cr_mul fld (trace_F3 fld f) (cr_mul fld lam lam)))
        (cr_add fld (cr_mul fld (charpoly_F3_minor_sum f) lam)
          (cr_neg fld (det_F3 fld f)))).

End CharPolyF3.
