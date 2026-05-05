(** * DecisionProblems/SL2HorowitzConcrete.v

    Concrete Qc-valued SL2 trace witnesses and finite conjugacy-class
    examples split out from [SL2Horowitz.v] to reduce incremental rebuild
    time for the general Horowitz layer. *)

From CAG Require Import Galois.Field.
From CAG Require Import Group FreeGroup.
From CAG Require Import LinAlg.Matrix2 LinAlg.SL2 LinAlg.SL2Fricke LinAlg.QField.
From Stdlib Require Import QArith Qcanon Lia ZArith List.
Import ListNotations.
From CAG Require Import DecisionProblems.TraceProperties.
From CAG Require Import DecisionProblems.OpenProblems.
From CAG Require Import DecisionProblems.WordLengthFreeGroup.
From CAG Require Import DecisionProblems.HallTheorem.
From CAG Require Import HallFreeGroup.InducedRepresentation.
From CAG Require Import DecisionProblems.SL2Horowitz.

(* CAG zero-dependent Theorem F_2_gens_non_conj_concrete theories/DecisionProblems/SL2Horowitz.v:629 BEGIN
Theorem F_2_gens_non_conj_concrete :
  ~ are_conjugate (FreeGroup 2)
      (free_gen_RWord 2 Fin.F1)
      (free_gen_RWord 2 (Fin.FS Fin.F1)) /\
  ~ are_conjugate (FreeGroup 2)
      (free_gen_RWord 2 Fin.F1)
      (sinv (RWord 2) (FreeGroup 2)
            (free_gen_RWord 2 (Fin.FS Fin.F1))).
Proof.
  apply (F_2_distinct_gens_non_conj_via_witness Qc_Field
            test_A_SL2 test_C_SL2).
  unfold test_A_SL2, test_C_SL2, SL2_trace, SL2_mat, SL2_mk, test_A, test_C.
  cbn. intro Hcontra. inversion Hcontra.
Qed.
   CAG zero-dependent Theorem F_2_gens_non_conj_concrete theories/DecisionProblems/SL2Horowitz.v:629 END *)

(** Concrete same-generator distinct-power non-conjugacy: γ_0 and γ_0^2
    in F_n are non-conjugate via test_A_SL2 (trace 3, trace of square = 7). *)
Theorem F_n_gen_pow_1_2_non_conj_concrete :
  forall (n : nat) (i : Fin.t n),
    ~ are_conjugate (FreeGroup n)
         (gamma_pow (free_gen_RWord n i) 1)
         (gamma_pow (free_gen_RWord n i) 2).
Proof.
  intros n i.
  apply (F_n_same_gen_pow_non_conj_via_trace Qc_Field n i 1 2).
  exists test_A_SL2.
  unfold test_A_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mk, SL2_mul, test_A.
  cbn. intro Hcontra. inversion Hcontra.
Qed.

(** γ_0 ≁ γ_0^3 in F_n: concrete via test_A (trace seq starts 2, 3, 7, 18, ...). *)
Theorem F_n_gen_pow_1_3_non_conj_concrete :
  forall (n : nat) (i : Fin.t n),
    ~ are_conjugate (FreeGroup n)
         (gamma_pow (free_gen_RWord n i) 1)
         (gamma_pow (free_gen_RWord n i) 3).
Proof.
  intros n i.
  apply (F_n_same_gen_pow_non_conj_via_trace Qc_Field n i 1 3).
  exists test_A_SL2.
  unfold test_A_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mk, SL2_mul, test_A.
  cbn. intro Hcontra. inversion Hcontra.
Qed.

(** γ_0^2 ≁ γ_0^3 in F_n: concrete via test_A. *)
Theorem F_n_gen_pow_2_3_non_conj_concrete :
  forall (n : nat) (i : Fin.t n),
    ~ are_conjugate (FreeGroup n)
         (gamma_pow (free_gen_RWord n i) 2)
         (gamma_pow (free_gen_RWord n i) 3).
Proof.
  intros n i.
  apply (F_n_same_gen_pow_non_conj_via_trace Qc_Field n i 2 3).
  exists test_A_SL2.
  unfold test_A_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mk, SL2_mul, test_A.
  cbn. intro Hcontra. inversion Hcontra.
Qed.

(** γ_0 ≁ (γ_0^{-1})^2 over Qc: tr(test_A) = 3 vs tr((test_A^{-1})^2)
    = tr(test_A^2) = 7 (SL2 inv-invariance). *)
Theorem F_n_gen_pos1_neg2_non_conj_concrete :
  forall (n : nat) (i : Fin.t n),
    ~ are_conjugate (FreeGroup n)
         (gamma_pow (free_gen_RWord n i) 1)
         (gamma_pow (rword_inv (free_gen_RWord n i)) 2).
Proof.
  intros n i.
  apply (F_n_pos_neg_pow_non_conj_via_trace Qc_Field n i 1 2).
  exists test_A_SL2.
  unfold test_A_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mk, SL2_mul, test_A.
  cbn. intro Hcontra. inversion Hcontra.
Qed.

(** F_2 γ_0 ≁ γ_0 · γ_1: tr(test_A) = 3, tr(test_A · test_C) = 8. *)
Theorem F_2_gen_non_conj_gens_mul_concrete :
  ~ are_conjugate (FreeGroup 2)
       (free_gen_RWord 2 Fin.F1)
       (rword_mul (free_gen_RWord 2 Fin.F1)
                  (free_gen_RWord 2 (Fin.FS Fin.F1))).
Proof.
  intro Hconj.
  set (f := fun k : Fin.t 2 =>
              if Fin.eq_dec k Fin.F1 then test_A_SL2 else test_C_SL2).
  pose proof (trace_at_conjugate_SL2 (FreeGroup 2) Qc_Field
                (rep_from_gen_map Qc_Field f)
                (free_gen_RWord 2 Fin.F1)
                (rword_mul (free_gen_RWord 2 Fin.F1)
                           (free_gen_RWord 2 (Fin.FS Fin.F1)))
                Hconj) as Heq.
  rewrite (rep_trace_at_from_gen_map_gen Qc_Field f Fin.F1) in Heq.
  rewrite (rep_trace_at_from_gen_map_mul_gens
             Qc_Field f Fin.F1 (Fin.FS Fin.F1)) in Heq.
  unfold f in Heq.
  destruct (Fin.eq_dec Fin.F1 Fin.F1) as [_|HF]; [|contradiction HF; reflexivity].
  destruct (Fin.eq_dec (Fin.FS Fin.F1) Fin.F1) as [Hfs|_]; [inversion Hfs|].
  unfold test_A_SL2, test_C_SL2, SL2_trace, SL2_mat, SL2_mul,
         SL2_mk, test_A, test_C in Heq.
  cbn in Heq. inversion Heq.
Qed.

(** F_2 γ_0·γ_1 ≁ γ_1 over Qc: tr(test_A · test_C) = 8, tr(test_C) = 4. *)
Theorem F_2_gens_mul_non_conj_gen2_concrete :
  ~ are_conjugate (FreeGroup 2)
       (rword_mul (free_gen_RWord 2 Fin.F1)
                  (free_gen_RWord 2 (Fin.FS Fin.F1)))
       (free_gen_RWord 2 (Fin.FS Fin.F1)).
Proof.
  intro Hconj.
  set (f := fun k : Fin.t 2 =>
              if Fin.eq_dec k Fin.F1 then test_A_SL2 else test_C_SL2).
  pose proof (trace_at_conjugate_SL2 (FreeGroup 2) Qc_Field
                (rep_from_gen_map Qc_Field f)
                (rword_mul (free_gen_RWord 2 Fin.F1)
                           (free_gen_RWord 2 (Fin.FS Fin.F1)))
                (free_gen_RWord 2 (Fin.FS Fin.F1)) Hconj) as Heq.
  rewrite (rep_trace_at_from_gen_map_mul_gens
             Qc_Field f Fin.F1 (Fin.FS Fin.F1)) in Heq.
  rewrite (rep_trace_at_from_gen_map_gen Qc_Field f (Fin.FS Fin.F1)) in Heq.
  unfold f in Heq.
  destruct (Fin.eq_dec Fin.F1 Fin.F1) as [_|HF]; [|contradiction HF; reflexivity].
  destruct (Fin.eq_dec (Fin.FS Fin.F1) Fin.F1) as [Hfs|_]; [inversion Hfs|].
  unfold test_A_SL2, test_C_SL2, SL2_trace, SL2_mat, SL2_mul,
         SL2_mk, test_A, test_C in Heq.
  cbn in Heq. inversion Heq.
Qed.

(** F_2 γ_0 ≁ γ_1 · γ_0: derived via cyclic-rotation conjugacy
    (γ_0 · γ_1 ~ γ_1 · γ_0) + transitivity from iter-151. *)
Theorem F_2_gen_non_conj_gens_swap_mul_concrete :
  ~ are_conjugate (FreeGroup 2)
       (free_gen_RWord 2 Fin.F1)
       (rword_mul (free_gen_RWord 2 (Fin.FS Fin.F1))
                  (free_gen_RWord 2 Fin.F1)).
Proof.
  intro Hconj.
  apply F_2_gen_non_conj_gens_mul_concrete.
  apply (are_conjugate_trans (FreeGroup 2) (free_gen_RWord 2 Fin.F1)
            (rword_mul (free_gen_RWord 2 (Fin.FS Fin.F1))
                       (free_gen_RWord 2 Fin.F1))
            (rword_mul (free_gen_RWord 2 Fin.F1)
                       (free_gen_RWord 2 (Fin.FS Fin.F1)))).
  - exact Hconj.
  - apply rword_mul_conjugate_swap.
Qed.

(** F_2 generator product γ_0 · γ_1 has non-trivial trace under
    rep_from_gen_map(test_A, test_C): tr(test_A · test_C) = ... *)
Theorem F_2_gens_mul_non_conj_e_concrete :
  ~ are_conjugate (FreeGroup 2)
       (rword_mul (free_gen_RWord 2 Fin.F1) (free_gen_RWord 2 (Fin.FS Fin.F1)))
       (@rword_e 2).
Proof.
  intro Hconj.
  set (f := fun k : Fin.t 2 =>
              if Fin.eq_dec k Fin.F1 then test_A_SL2 else test_C_SL2).
  pose proof (trace_at_conjugate_SL2 (FreeGroup 2) Qc_Field
                (rep_from_gen_map Qc_Field f)
                (rword_mul (free_gen_RWord 2 Fin.F1)
                           (free_gen_RWord 2 (Fin.FS Fin.F1)))
                (@rword_e 2) Hconj) as Heq.
  rewrite (rep_trace_at_from_gen_map_mul_gens
             Qc_Field f Fin.F1 (Fin.FS Fin.F1)) in Heq.
  rewrite (rep_trace_at_from_gen_map_e Qc_Field f) in Heq.
  unfold f in Heq.
  destruct (Fin.eq_dec Fin.F1 Fin.F1) as [_|HF]; [|contradiction HF; reflexivity].
  destruct (Fin.eq_dec (Fin.FS Fin.F1) Fin.F1) as [Hfs|_]; [inversion Hfs|].
  unfold test_A_SL2, test_C_SL2, SL2_trace, SL2_mat, SL2_mul,
         SL2_mk, test_A, test_C in Heq.
  cbn in Heq. inversion Heq.
Qed.

(** F_2 distinct-generator squared non-conjugacy: γ_0^2 and γ_1^2 are
    not conjugate over Qc. tr(test_A^2) = 7, tr(test_C^2) = ... *)
Theorem F_2_gens_squared_non_conj_concrete :
  ~ are_conjugate (FreeGroup 2)
       (gamma_pow (free_gen_RWord 2 Fin.F1) 2)
       (gamma_pow (free_gen_RWord 2 (Fin.FS Fin.F1)) 2).
Proof.
  apply (@F_n_gens_pow_non_conj_via_trace
           2 Qc Qc_Field Fin.F1 (Fin.FS Fin.F1) 2 2).
  set (f := fun k : Fin.t 2 =>
              if Fin.eq_dec k Fin.F1 then test_A_SL2 else test_C_SL2).
  exists f.
  unfold f.
  destruct (Fin.eq_dec Fin.F1 Fin.F1) as [_|HF]; [|contradiction HF; reflexivity].
  destruct (Fin.eq_dec (Fin.FS Fin.F1) Fin.F1) as [Hfs|_].
  - inversion Hfs.
  - unfold test_A_SL2, test_C_SL2, SL2_trace, SL2_mat, SL2_pow,
           SL2_mk, SL2_mul, test_A, test_C.
    cbn. intro Hcontra. inversion Hcontra.
Qed.

(** *** F_2 has at least 4 distinct conjugacy classes.

    The conjugacy classes of e, γ_0, γ_1, γ_0·γ_1 are pairwise distinct.
    All 6 pairwise non-conjugacies follow from the test_A / test_C
    instantiation of rep_from_gen_map. *)
(* CAG zero-dependent Theorem F_2_at_least_4_conjugacy_classes theories/DecisionProblems/SL2Horowitz.v:826 BEGIN
Theorem F_2_at_least_4_conjugacy_classes :
  ~ are_conjugate (FreeGroup 2) (@rword_e 2) (free_gen_RWord 2 Fin.F1) /\
  ~ are_conjugate (FreeGroup 2) (@rword_e 2)
       (free_gen_RWord 2 (Fin.FS Fin.F1)) /\
  ~ are_conjugate (FreeGroup 2) (@rword_e 2)
       (rword_mul (free_gen_RWord 2 Fin.F1)
                  (free_gen_RWord 2 (Fin.FS Fin.F1))) /\
  ~ are_conjugate (FreeGroup 2) (free_gen_RWord 2 Fin.F1)
       (free_gen_RWord 2 (Fin.FS Fin.F1)) /\
  ~ are_conjugate (FreeGroup 2) (free_gen_RWord 2 Fin.F1)
       (rword_mul (free_gen_RWord 2 Fin.F1)
                  (free_gen_RWord 2 (Fin.FS Fin.F1))) /\
  ~ are_conjugate (FreeGroup 2) (free_gen_RWord 2 (Fin.FS Fin.F1))
       (rword_mul (free_gen_RWord 2 Fin.F1)
                  (free_gen_RWord 2 (Fin.FS Fin.F1))).
Proof.
  repeat split.
  - apply (free_gen_RWord_not_conj_e 2 Fin.F1).
  - apply (free_gen_RWord_not_conj_e 2 (Fin.FS Fin.F1)).
  - intros Hconj. apply F_2_gens_mul_non_conj_e_concrete.
    apply are_conjugate_sym. exact Hconj.
  - exact (proj1 F_2_gens_non_conj_concrete).
  - apply F_2_gen_non_conj_gens_mul_concrete.
  - intros Hconj. apply F_2_gens_mul_non_conj_gen2_concrete.
    apply are_conjugate_sym. exact Hconj.
Qed.
   CAG zero-dependent Theorem F_2_at_least_4_conjugacy_classes theories/DecisionProblems/SL2Horowitz.v:826 END *)

(** γ_0^4 ≁ e in F_n via test_A: tr(test_A^4) = 47 ≠ 2. *)
Theorem F_n_gen_pow_4_non_conj_e_concrete :
  forall (n : nat) (i : Fin.t n),
    ~ are_conjugate (FreeGroup n)
         (gamma_pow (free_gen_RWord n i) 4) (@rword_e n).
Proof.
  intros n i.
  assert (Hex : exists rho : Representation (FreeGroup n) (SL2_as_MG Qc_Field),
                  trace_at rho (gamma_pow (free_gen_RWord n i) 4) <>
                  trace_at rho (@rword_e n)).
  { exists (rep_from_gen_map Qc_Field (fun _ : Fin.t n => test_A_SL2)).
    rewrite (rep_trace_at_from_gen_map_pow Qc_Field (fun _ => test_A_SL2) i 4).
    rewrite (rep_trace_at_from_gen_map_e Qc_Field (fun _ => test_A_SL2)).
    unfold test_A_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mk, SL2_mul, test_A.
    cbn. intro Hcontra. inversion Hcontra. }
  exact (proj1 (F_n_distinguishing_rep_implies_both_non_conjugacies
                  Qc_Field n
                  (gamma_pow (free_gen_RWord n i) 4) (@rword_e n) Hex)).
Qed.

(** γ_0^1 ≁ γ_0^4 in F_n: tr(test_A) = 3 ≠ 47. *)
Theorem F_n_gen_pow_1_4_non_conj_concrete :
  forall (n : nat) (i : Fin.t n),
    ~ are_conjugate (FreeGroup n)
         (gamma_pow (free_gen_RWord n i) 1)
         (gamma_pow (free_gen_RWord n i) 4).
Proof.
  intros n i.
  apply (F_n_same_gen_pow_non_conj_via_trace Qc_Field n i 1 4).
  exists test_A_SL2.
  unfold test_A_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mk, SL2_mul, test_A.
  cbn. intro Hcontra. inversion Hcontra.
Qed.

(** γ_0^2 ≁ γ_0^4: tr(test_A^2) = 7 ≠ 47. *)
Theorem F_n_gen_pow_2_4_non_conj_concrete :
  forall (n : nat) (i : Fin.t n),
    ~ are_conjugate (FreeGroup n)
         (gamma_pow (free_gen_RWord n i) 2)
         (gamma_pow (free_gen_RWord n i) 4).
Proof.
  intros n i.
  apply (F_n_same_gen_pow_non_conj_via_trace Qc_Field n i 2 4).
  exists test_A_SL2.
  unfold test_A_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mk, SL2_mul, test_A.
  cbn. intro Hcontra. inversion Hcontra.
Qed.

(** γ_0^3 ≁ γ_0^4: tr(test_A^3) = 18 ≠ 47. *)
Theorem F_n_gen_pow_3_4_non_conj_concrete :
  forall (n : nat) (i : Fin.t n),
    ~ are_conjugate (FreeGroup n)
         (gamma_pow (free_gen_RWord n i) 3)
         (gamma_pow (free_gen_RWord n i) 4).
Proof.
  intros n i.
  apply (F_n_same_gen_pow_non_conj_via_trace Qc_Field n i 3 4).
  exists test_A_SL2.
  unfold test_A_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mk, SL2_mul, test_A.
  cbn. intro Hcontra. inversion Hcontra.
Qed.

(** γ_0^4 ≁ γ_0^5: tr(test_A^4) = 47 ≠ 123 = tr(test_A^5). *)
Theorem F_n_gen_pow_4_5_non_conj_concrete :
  forall (n : nat) (i : Fin.t n),
    ~ are_conjugate (FreeGroup n)
         (gamma_pow (free_gen_RWord n i) 4)
         (gamma_pow (free_gen_RWord n i) 5).
Proof.
  intros n i.
  apply (F_n_same_gen_pow_non_conj_via_trace Qc_Field n i 4 5).
  exists test_A_SL2.
  unfold test_A_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mk, SL2_mul, test_A.
  cbn. intro Hcontra. inversion Hcontra.
Qed.

(** γ_0^3 ≁ e in F_n via test_A: tr(test_A^3) = 18 ≠ 2. *)
Theorem F_n_gen_pow_3_non_conj_e_concrete :
  forall (n : nat) (i : Fin.t n),
    ~ are_conjugate (FreeGroup n)
         (gamma_pow (free_gen_RWord n i) 3) (@rword_e n).
Proof.
  intros n i.
  assert (Hex : exists rho : Representation (FreeGroup n) (SL2_as_MG Qc_Field),
                  trace_at rho (gamma_pow (free_gen_RWord n i) 3) <>
                  trace_at rho (@rword_e n)).
  { exists (rep_from_gen_map Qc_Field (fun _ : Fin.t n => test_A_SL2)).
    rewrite (rep_trace_at_from_gen_map_pow Qc_Field (fun _ => test_A_SL2) i 3).
    rewrite (rep_trace_at_from_gen_map_e Qc_Field (fun _ => test_A_SL2)).
    unfold test_A_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mk, SL2_mul, test_A.
    cbn. intro Hcontra. inversion Hcontra. }
  exact (proj1 (F_n_distinguishing_rep_implies_both_non_conjugacies
                  Qc_Field n
                  (gamma_pow (free_gen_RWord n i) 3) (@rword_e n) Hex)).
Qed.

(** γ_0^2 ≁ e in F_n via test_A: tr(test_A^2) = 7 ≠ 2. *)
Theorem F_n_gen_pow_2_non_conj_e_concrete :
  forall (n : nat) (i : Fin.t n),
    ~ are_conjugate (FreeGroup n)
         (gamma_pow (free_gen_RWord n i) 2) (@rword_e n).
Proof.
  intros n i.
  assert (Hex : exists rho : Representation (FreeGroup n) (SL2_as_MG Qc_Field),
                  trace_at rho (gamma_pow (free_gen_RWord n i) 2) <>
                  trace_at rho (@rword_e n)).
  { exists (rep_from_gen_map Qc_Field (fun _ : Fin.t n => test_A_SL2)).
    rewrite (rep_trace_at_from_gen_map_pow Qc_Field (fun _ => test_A_SL2) i 2).
    rewrite (rep_trace_at_from_gen_map_e Qc_Field (fun _ => test_A_SL2)).
    unfold test_A_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mk, SL2_mul, test_A.
    cbn. intro Hcontra. inversion Hcontra. }
  exact (proj1 (F_n_distinguishing_rep_implies_both_non_conjugacies
                  Qc_Field n
                  (gamma_pow (free_gen_RWord n i) 2) (@rword_e n) Hex)).
Qed.

(** γ_0^2 ≁ γ_0·γ_1 in F_2 over Qc: tr(test_A^2) = 7, tr(test_A·test_C) = 8. *)
Theorem F_2_gen0_pow2_non_conj_gens_mul_concrete :
  ~ are_conjugate (FreeGroup 2)
       (gamma_pow (free_gen_RWord 2 Fin.F1) 2)
       (rword_mul (free_gen_RWord 2 Fin.F1)
                  (free_gen_RWord 2 (Fin.FS Fin.F1))).
Proof.
  intro Hconj.
  set (f := fun k : Fin.t 2 =>
              if Fin.eq_dec k Fin.F1 then test_A_SL2 else test_C_SL2).
  pose proof (trace_at_conjugate_SL2 (FreeGroup 2) Qc_Field
                (rep_from_gen_map Qc_Field f)
                (gamma_pow (free_gen_RWord 2 Fin.F1) 2)
                (rword_mul (free_gen_RWord 2 Fin.F1)
                           (free_gen_RWord 2 (Fin.FS Fin.F1))) Hconj) as Heq.
  rewrite (rep_trace_at_from_gen_map_pow Qc_Field f Fin.F1 2) in Heq.
  rewrite (rep_trace_at_from_gen_map_mul_gens
             Qc_Field f Fin.F1 (Fin.FS Fin.F1)) in Heq.
  unfold f in Heq.
  destruct (Fin.eq_dec Fin.F1 Fin.F1) as [_|HF]; [|contradiction HF; reflexivity].
  destruct (Fin.eq_dec (Fin.FS Fin.F1) Fin.F1) as [Hfs|_]; [inversion Hfs|].
  unfold test_A_SL2, test_C_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mul,
         SL2_mk, test_A, test_C in Heq.
  cbn in Heq. inversion Heq.
Qed.

(** γ_0^3 ≁ γ_1 in F_2: tr(test_A^3) = 18 ≠ 4 = tr(test_C). *)
Theorem F_2_gen0_pow3_non_conj_gen1_concrete :
  ~ are_conjugate (FreeGroup 2)
       (gamma_pow (free_gen_RWord 2 Fin.F1) 3)
       (free_gen_RWord 2 (Fin.FS Fin.F1)).
Proof.
  rewrite <- (gamma_pow_one_eq (free_gen_RWord 2 (Fin.FS Fin.F1))).
  apply (@F_n_gens_pow_non_conj_via_trace
           2 Qc Qc_Field Fin.F1 (Fin.FS Fin.F1) 3 1).
  set (f := fun k : Fin.t 2 =>
              if Fin.eq_dec k Fin.F1 then test_A_SL2 else test_C_SL2).
  exists f.
  unfold f.
  destruct (Fin.eq_dec Fin.F1 Fin.F1) as [_|HF]; [|contradiction HF; reflexivity].
  destruct (Fin.eq_dec (Fin.FS Fin.F1) Fin.F1) as [Hfs|_]; [inversion Hfs|].
  unfold test_A_SL2, test_C_SL2, SL2_trace, SL2_mat, SL2_pow,
         SL2_mk, SL2_mul, test_A, test_C.
  cbn. intro Hcontra. inversion Hcontra.
Qed.

(** γ_0^3 ≁ γ_0·γ_1 in F_2: tr(test_A^3) = 18 ≠ 8 = tr(test_A·test_C). *)
Theorem F_2_gen0_pow3_non_conj_gens_mul_concrete :
  ~ are_conjugate (FreeGroup 2)
       (gamma_pow (free_gen_RWord 2 Fin.F1) 3)
       (rword_mul (free_gen_RWord 2 Fin.F1)
                  (free_gen_RWord 2 (Fin.FS Fin.F1))).
Proof.
  intro Hconj.
  set (f := fun k : Fin.t 2 =>
              if Fin.eq_dec k Fin.F1 then test_A_SL2 else test_C_SL2).
  pose proof (trace_at_conjugate_SL2 (FreeGroup 2) Qc_Field
                (rep_from_gen_map Qc_Field f)
                (gamma_pow (free_gen_RWord 2 Fin.F1) 3)
                (rword_mul (free_gen_RWord 2 Fin.F1)
                           (free_gen_RWord 2 (Fin.FS Fin.F1))) Hconj) as Heq.
  rewrite (rep_trace_at_from_gen_map_pow Qc_Field f Fin.F1 3) in Heq.
  rewrite (rep_trace_at_from_gen_map_mul_gens
             Qc_Field f Fin.F1 (Fin.FS Fin.F1)) in Heq.
  unfold f in Heq.
  destruct (Fin.eq_dec Fin.F1 Fin.F1) as [_|HF]; [|contradiction HF; reflexivity].
  destruct (Fin.eq_dec (Fin.FS Fin.F1) Fin.F1) as [Hfs|_]; [inversion Hfs|].
  unfold test_A_SL2, test_C_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mul,
         SL2_mk, test_A, test_C in Heq.
  cbn in Heq. inversion Heq.
Qed.

(** γ_0^2 ≁ γ_1 in F_2 via test_A and test_C: tr(test_A^2) = 7 ≠ 4 = tr(test_C). *)
Theorem F_2_gen0_pow2_non_conj_gen1_concrete :
  ~ are_conjugate (FreeGroup 2)
       (gamma_pow (free_gen_RWord 2 Fin.F1) 2)
       (free_gen_RWord 2 (Fin.FS Fin.F1)).
Proof.
  rewrite <- (gamma_pow_one_eq (free_gen_RWord 2 (Fin.FS Fin.F1))).
  apply (@F_n_gens_pow_non_conj_via_trace
           2 Qc Qc_Field Fin.F1 (Fin.FS Fin.F1) 2 1).
  set (f := fun k : Fin.t 2 =>
              if Fin.eq_dec k Fin.F1 then test_A_SL2 else test_C_SL2).
  exists f.
  unfold f.
  destruct (Fin.eq_dec Fin.F1 Fin.F1) as [_|HF]; [|contradiction HF; reflexivity].
  destruct (Fin.eq_dec (Fin.FS Fin.F1) Fin.F1) as [Hfs|_]; [inversion Hfs|].
  unfold test_A_SL2, test_C_SL2, SL2_trace, SL2_mat, SL2_pow,
         SL2_mk, SL2_mul, test_A, test_C.
  cbn. intro Hcontra. inversion Hcontra.
Qed.

(** *** F_2 has at least 5 distinct conjugacy classes:
    e, γ_0, γ_1, γ_0·γ_1, γ_0². The 10 pairwise non-conjugacies are
    each established concretely over Qc. *)
(* CAG zero-dependent Theorem F_2_at_least_5_conjugacy_classes theories/DecisionProblems/SL2Horowitz.v:1064 BEGIN
Theorem F_2_at_least_5_conjugacy_classes :
  let g0 := free_gen_RWord 2 Fin.F1 in
  let g1 := free_gen_RWord 2 (Fin.FS Fin.F1) in
  let g0g1 := rword_mul g0 g1 in
  let g0sq := gamma_pow g0 2 in
  ~ are_conjugate (FreeGroup 2) (@rword_e 2) g0 /\
  ~ are_conjugate (FreeGroup 2) (@rword_e 2) g1 /\
  ~ are_conjugate (FreeGroup 2) (@rword_e 2) g0g1 /\
  ~ are_conjugate (FreeGroup 2) (@rword_e 2) g0sq /\
  ~ are_conjugate (FreeGroup 2) g0 g1 /\
  ~ are_conjugate (FreeGroup 2) g0 g0g1 /\
  ~ are_conjugate (FreeGroup 2) g0 g0sq /\
  ~ are_conjugate (FreeGroup 2) g1 g0g1 /\
  ~ are_conjugate (FreeGroup 2) g1 g0sq /\
  ~ are_conjugate (FreeGroup 2) g0g1 g0sq.
Proof.
  cbv zeta.
  repeat split.
  - apply (free_gen_RWord_not_conj_e 2 Fin.F1).
  - apply (free_gen_RWord_not_conj_e 2 (Fin.FS Fin.F1)).
  - intros Hconj. apply F_2_gens_mul_non_conj_e_concrete.
    apply are_conjugate_sym. exact Hconj.
  - intros Hconj. apply (F_n_gen_pow_2_non_conj_e_concrete 2 Fin.F1).
    apply are_conjugate_sym. exact Hconj.
  - exact (proj1 F_2_gens_non_conj_concrete).
  - apply F_2_gen_non_conj_gens_mul_concrete.
  - intros Hconj. rewrite <- (gamma_pow_one_eq (free_gen_RWord 2 Fin.F1))
                  in Hconj at 1.
    apply (F_n_gen_pow_1_2_non_conj_concrete 2 Fin.F1).
    exact Hconj.
  - intros Hconj. apply F_2_gens_mul_non_conj_gen2_concrete.
    apply are_conjugate_sym. exact Hconj.
  - intros Hconj. apply F_2_gen0_pow2_non_conj_gen1_concrete.
    apply are_conjugate_sym. exact Hconj.
  - intros Hconj. apply F_2_gen0_pow2_non_conj_gens_mul_concrete.
    apply are_conjugate_sym. exact Hconj.
Qed.
   CAG zero-dependent Theorem F_2_at_least_5_conjugacy_classes theories/DecisionProblems/SL2Horowitz.v:1064 END *)

(** γ_0 ≁ (γ_0^{-1})^3: tr(test_A) = 3 ≠ 18 = tr(test_A^3). *)
Theorem F_n_gen_pos1_neg3_non_conj_concrete :
  forall (n : nat) (i : Fin.t n),
    ~ are_conjugate (FreeGroup n)
         (gamma_pow (free_gen_RWord n i) 1)
         (gamma_pow (rword_inv (free_gen_RWord n i)) 3).
Proof.
  intros n i.
  apply (F_n_pos_neg_pow_non_conj_via_trace Qc_Field n i 1 3).
  exists test_A_SL2.
  unfold test_A_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mk, SL2_mul, test_A.
  cbn. intro Hcontra. inversion Hcontra.
Qed.

(** γ_0^2 ≁ (γ_0^{-1})^3: tr(test_A^2) = 7 ≠ 18 = tr(test_A^3). *)
Theorem F_n_gen_pos2_neg3_non_conj_concrete :
  forall (n : nat) (i : Fin.t n),
    ~ are_conjugate (FreeGroup n)
         (gamma_pow (free_gen_RWord n i) 2)
         (gamma_pow (rword_inv (free_gen_RWord n i)) 3).
Proof.
  intros n i.
  apply (F_n_pos_neg_pow_non_conj_via_trace Qc_Field n i 2 3).
  exists test_A_SL2.
  unfold test_A_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mk, SL2_mul, test_A.
  cbn. intro Hcontra. inversion Hcontra.
Qed.

(** F_1 has infinitely many distinct conjugacy classes: distinct
    positive powers of γ_0 are pairwise non-conjugate. F_1 is abelian
    so conjugacy = equality, then gamma_pow_gen_inj closes the loop. *)
Theorem F_1_infinite_conjugacy_classes :
  forall (a b : nat), a <> b ->
    ~ are_conjugate (FreeGroup 1)
        (gamma_pow (free_gen_RWord 1 Fin.F1) a)
        (gamma_pow (free_gen_RWord 1 Fin.F1) b).
Proof.
  intros a b Hab Hconj.
  apply Hab.
  apply (gamma_pow_gen_inj 1%nat Fin.F1 a b).
  apply F_1_are_conjugate_iff_eq. exact Hconj.
Qed.

(** F_1: positive and inverse powers (both nontrivial) are never conjugate. *)
Theorem F_1_pos_neg_distinct_classes :
  forall (a b : nat), (1 <= a)%nat -> (1 <= b)%nat ->
    ~ are_conjugate (FreeGroup 1)
        (gamma_pow (free_gen_RWord 1 Fin.F1) a)
        (gamma_pow (rword_inv (free_gen_RWord 1 Fin.F1)) b).
Proof.
  intros a b Ha Hb Hconj.
  pose proof (F_1_are_conjugate_iff_eq
                (gamma_pow (free_gen_RWord 1 Fin.F1) a)
                (gamma_pow (rword_inv (free_gen_RWord 1 Fin.F1)) b)) as Hiff.
  destruct Hiff as [Hfwd _].
  pose proof (Hfwd Hconj) as Heq.
  apply (gamma_pow_gen_pos_ne_neg 1 Fin.F1 a b Ha Hb Heq).
Qed.

(** *** F_n has at least 4 distinct generator-power conjugacy classes.

    For n ≥ 1, the powers e = γ_0^0, γ_0^1, γ_0^2, γ_0^3 are pairwise
    non-conjugate. All 6 pairwise non-conjugacies follow from concrete
    test_A trace computations (sequence 2, 3, 7, 18). *)
Theorem F_n_gen_pow_0_to_3_pairwise_non_conj :
  forall (n : nat) (i : Fin.t n),
  ~ are_conjugate (FreeGroup n) (@rword_e n) (gamma_pow (free_gen_RWord n i) 1) /\
  ~ are_conjugate (FreeGroup n) (@rword_e n) (gamma_pow (free_gen_RWord n i) 2) /\
  ~ are_conjugate (FreeGroup n) (@rword_e n) (gamma_pow (free_gen_RWord n i) 3) /\
  ~ are_conjugate (FreeGroup n)
       (gamma_pow (free_gen_RWord n i) 1) (gamma_pow (free_gen_RWord n i) 2) /\
  ~ are_conjugate (FreeGroup n)
       (gamma_pow (free_gen_RWord n i) 1) (gamma_pow (free_gen_RWord n i) 3) /\
  ~ are_conjugate (FreeGroup n)
       (gamma_pow (free_gen_RWord n i) 2) (gamma_pow (free_gen_RWord n i) 3).
Proof.
  intros n i.
  repeat split.
  - intro Hconj. apply (free_gen_RWord_not_conj_e n i).
    rewrite gamma_pow_one_eq in Hconj. exact Hconj.
  - intro Hconj. apply (F_n_gen_pow_2_non_conj_e_concrete n i).
    apply are_conjugate_sym. exact Hconj.
  - intro Hconj. apply (F_n_gen_pow_3_non_conj_e_concrete n i).
    apply are_conjugate_sym. exact Hconj.
  - apply (F_n_gen_pow_1_2_non_conj_concrete n i).
  - apply (F_n_gen_pow_1_3_non_conj_concrete n i).
  - apply (F_n_gen_pow_2_3_non_conj_concrete n i).
Qed.

(** F_n has at least 5 distinct generator-power conjugacy classes:
    e, γ_i, γ_i^2, γ_i^3, γ_i^4 are pairwise non-conjugate. C(5,2) = 10 pairs. *)
Theorem F_n_gen_pow_0_to_4_pairwise_non_conj :
  forall (n : nat) (i : Fin.t n),
  ~ are_conjugate (FreeGroup n) (@rword_e n) (gamma_pow (free_gen_RWord n i) 1) /\
  ~ are_conjugate (FreeGroup n) (@rword_e n) (gamma_pow (free_gen_RWord n i) 2) /\
  ~ are_conjugate (FreeGroup n) (@rword_e n) (gamma_pow (free_gen_RWord n i) 3) /\
  ~ are_conjugate (FreeGroup n) (@rword_e n) (gamma_pow (free_gen_RWord n i) 4) /\
  ~ are_conjugate (FreeGroup n)
       (gamma_pow (free_gen_RWord n i) 1) (gamma_pow (free_gen_RWord n i) 2) /\
  ~ are_conjugate (FreeGroup n)
       (gamma_pow (free_gen_RWord n i) 1) (gamma_pow (free_gen_RWord n i) 3) /\
  ~ are_conjugate (FreeGroup n)
       (gamma_pow (free_gen_RWord n i) 1) (gamma_pow (free_gen_RWord n i) 4) /\
  ~ are_conjugate (FreeGroup n)
       (gamma_pow (free_gen_RWord n i) 2) (gamma_pow (free_gen_RWord n i) 3) /\
  ~ are_conjugate (FreeGroup n)
       (gamma_pow (free_gen_RWord n i) 2) (gamma_pow (free_gen_RWord n i) 4) /\
  ~ are_conjugate (FreeGroup n)
       (gamma_pow (free_gen_RWord n i) 3) (gamma_pow (free_gen_RWord n i) 4).
Proof.
  intros n i.
  destruct (F_n_gen_pow_0_to_3_pairwise_non_conj n i)
    as [H1 [H2 [H3 [H12 [H13 H23]]]]].
  repeat split; auto.
  - intro Hconj. apply (F_n_gen_pow_4_non_conj_e_concrete n i).
    apply are_conjugate_sym. exact Hconj.
  - apply F_n_gen_pow_1_4_non_conj_concrete.
  - apply F_n_gen_pow_2_4_non_conj_concrete.
  - apply F_n_gen_pow_3_4_non_conj_concrete.
Qed.
