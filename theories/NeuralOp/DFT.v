(** * NeuralOp/DFT.v
    Discrete Fourier Transform over CComplex.

    For a sequence x : Fin N → ℂ the DFT is
        X_k = Σ_{n=0}^{N-1}  x_n · ω_N^{nk}     (analysis)
        x_n = (1/N) Σ_{k=0}^{N-1}  X_k · ω_N^{−nk} (synthesis)
    where ω_N = e^{−2πi/N} is the primitive N-th root of unity.

    We axiomatize the complex exponential and derive the DFT as a
    finite sum.  The key identities — inverse DFT, Plancherel,
    convolution — are stated and admitted; they are standard and
    their proofs reduce to the geometric-sum identity
        Σ_{n=0}^{N−1} ω_N^{nk} = N · [k ≡ 0 mod N].  *)

From Stdlib Require Import List Arith Lia.
From Stdlib Require Import QArith ZArith.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyRealsMult.
Import ListNotations.

From CAG Require Import Complex.

Local Open Scope CReal_scope.

(** ** Complex exponential  e^{iθ} *)

(** We axiomatize exp_i : ℝ → ℂ satisfying Euler's formula.
    A full constructive definition would require sin and cos series. *)

Parameter exp_i : CReal -> CComplex.

(** Specification axioms for the [exp_i] [Parameter]. *)
Axiom exp_i_zero    : exp_i 0 = C1.
Axiom exp_i_add     : forall θ φ, exp_i (θ + φ) = Cmul (exp_i θ) (exp_i φ).
Axiom exp_i_neg     : forall θ,   exp_i (- θ)   = mkC (re (exp_i θ)) (- im (exp_i θ)).
Axiom exp_i_norm_sq : forall θ,
    re (exp_i θ) * re (exp_i θ) + im (exp_i θ) * im (exp_i θ) = 1.

(** π, already axiomatized in ComplexAnalysis.v — redeclare for self-containment. *)
Parameter pi_R : CReal.
Axiom pi_pos : 0 < pi_R.

(** Foundational fact about the complex exponential: e^{2πi} = 1.
    This is the standard 2π-periodicity of the complex exponential
    (Euler 1748), and is independent of the four [exp_i] specification
    axioms above.  Adding it discharges [omega_pow] and
    [geometric_sum_zero] as Lemmas below. *)
Axiom exp_i_2pi : exp_i (inject_Q (2 # 1) * pi_R) = C1.

(** N-th primitive root of unity: ω_N = e^{−2πi/N}. *)
Definition omega (N : nat) : CComplex :=
  (* e^{-2πi/N} = exp_i(-2π · (1/N)).  We write (1/N) as the rational 1#N. *)
  exp_i (- (inject_Q (2 # 1) * pi_R * inject_Q (1 # Pos.of_nat N))).

(** ** Helpers for [Cpow] on [exp_i] *)

(** Repeated-add representation of [n] in [CReal]. *)
Fixpoint nreal (n : nat) : CReal :=
  match n with
  | O => 0
  | S k => 1 + nreal k
  end.

Lemma nreal_inject : forall n : nat,
    nreal n = inject_Q (Z.of_nat n # 1).
Proof.
  induction n as [|k IH].
  - simpl. apply CRealEq_eq. reflexivity.
  - simpl nreal. rewrite IH.
    apply CRealEq_eq.
    rewrite Nat2Z.inj_succ.
    (* (Z.succ (Z.of_nat k) # 1) == 1 + (Z.of_nat k # 1) *)
    assert (HQ : Qeq (Z.succ (Z.of_nat k) # 1) ((1 # 1) + (Z.of_nat k # 1))).
    { unfold Qeq. cbv [Qplus Qnum Qden].
      rewrite !Z.mul_1_r.
      symmetry. apply Z.add_1_l. }
    rewrite (inject_Q_morph _ _ HQ).
    rewrite inject_Q_plus.
    apply CReal_plus_proper_r.
    apply inject_Q_one.
Qed.

(** [Cpow (exp_i θ) n = exp_i (nreal n * θ)]. *)
Lemma Cpow_exp_i : forall (n : nat) (θ : CReal),
    Cpow (exp_i θ) n = exp_i (nreal n * θ).
Proof.
  induction n as [|k IH]; intro θ.
  - simpl. symmetry.
    assert (Hzero : 0 * θ = 0).
    { apply CRealEq_eq. ring. }
    rewrite Hzero. apply exp_i_zero.
  - simpl Cpow. rewrite IH.
    rewrite <- exp_i_add.
    f_equal.
    apply CRealEq_eq.
    simpl nreal. ring.
Qed.

(** [exp_i (-2π) = C1] follows from [exp_i_2pi] and [exp_i_neg]. *)
Lemma exp_i_neg_2pi : exp_i (- (inject_Q (2 # 1) * pi_R)) = C1.
Proof.
  rewrite exp_i_neg.
  rewrite exp_i_2pi.
  (* mkC (re C1) (- im C1) = mkC 1 (-0); need = C1 = mkC 1 0. *)
  apply CComplex_eq.
  unfold CComplex_req, C1. simpl.
  split.
  - reflexivity.
  - (* CRealEq 0 (- 0) *) ring.
Qed.

(** Rational identity: [(Z.of_nat (S k) # 1) * (1 # Pos.of_nat (S k)) == 1]. *)
Lemma Q_of_nat_inv : forall k : nat,
    ((Z.of_nat (S k) # 1) * (1 # Pos.of_nat (S k)) == 1)%Q.
Proof.
  intro k.
  rewrite <- Pos.of_nat_succ.
  (* Now Pos.of_nat (S k) = Pos.of_succ_nat k *)
  (* Z.of_nat (S k) = Zpos (Pos.of_succ_nat k) *)
  change (Z.of_nat (S k)) with (Z.pos (Pos.of_succ_nat k)).
  unfold Qeq. cbv [Qmult Qnum Qden].
  rewrite Pos.mul_1_l. lia.
Qed.

(** ω_N^N = 1, derived from [exp_i_2pi] + [exp_i_add] + [exp_i_zero]. *)
Lemma omega_pow : forall (N : nat), N <> 0%nat -> Cpow (omega N) N = C1.
Proof.
  intros N HN.
  unfold omega.
  rewrite Cpow_exp_i.
  rewrite <- exp_i_neg_2pi.
  f_equal.
  apply CRealEq_eq.
  rewrite nreal_inject.
  destruct N as [|N']; [contradiction|clear HN].
  set (q := (Z.of_nat (S N') # 1)%Q).
  set (r := (1 # Pos.of_nat (S N'))%Q).
  assert (Hqr : (q * r == 1)%Q) by apply Q_of_nat_inv.
  set (twopi := inject_Q (2#1) * pi_R).
  apply (CRealEq_trans _ (- (inject_Q q * (twopi * inject_Q r)))).
  { (* inject_Q q * - (twopi * inject_Q r) == - (inject_Q q * (twopi * inject_Q r)) *)
    symmetry. apply CReal_opp_mult_distr_r. }
  (* Goal: - (inject_Q q * (twopi * inject_Q r)) == - twopi *)
  rewrite (CReal_mult_comm twopi (inject_Q r)).
  (* Goal: - (inject_Q q * (inject_Q r * twopi)) == - twopi *)
  rewrite <- CReal_mult_assoc.
  (* Goal: - (inject_Q q * inject_Q r * twopi) == - twopi *)
  rewrite <- inject_Q_mult.
  rewrite (inject_Q_morph _ _ Hqr).
  (* Goal: - (1 * twopi) == - twopi *)
  rewrite CReal_mult_1_l.
  reflexivity.
Qed.

(** Helper lemmas for [geometric_sum_zero]. *)

Lemma Cmul_C1_C1 : Cmul C1 C1 = C1.
Proof.
  apply CComplex_eq. apply Cmul_C1_l_req.
Qed.

Lemma Cpow_C1 : forall n : nat, Cpow C1 n = C1.
Proof.
  induction n as [|k IH].
  - reflexivity.
  - simpl. rewrite IH. apply Cmul_C1_C1.
Qed.

Lemma Cmul_C1_l_eq : forall a : CComplex, Cmul C1 a = a.
Proof.
  intro a. apply CComplex_eq. apply Cmul_C1_l_req.
Qed.

Lemma Cmul_assoc_eq : forall a b c : CComplex,
    Cmul a (Cmul b c) = Cmul (Cmul a b) c.
Proof.
  intros. apply CComplex_eq. apply Cmul_assoc_req.
Qed.

Lemma Cpow_add : forall (z : CComplex) (m n : nat),
    Cpow z (m + n) = Cmul (Cpow z m) (Cpow z n).
Proof.
  intros z. induction m as [|m' IH]; intro n.
  - simpl. symmetry. apply Cmul_C1_l_eq.
  - simpl. rewrite IH. apply Cmul_assoc_eq.
Qed.

Lemma Cpow_mul : forall (z : CComplex) (m n : nat),
    Cpow z (m * n) = Cpow (Cpow z n) m.
Proof.
  intros z. induction m as [|m' IH]; intro n.
  - reflexivity.
  - simpl. rewrite Cpow_add. rewrite IH. reflexivity.
Qed.

(** When [k mod N = 0], [Cpow (omega N) (n' * k) = C1] for all [n']. *)
Lemma omega_pow_multiple : forall (N k : nat),
    N <> 0%nat -> k mod N = 0%nat -> forall n' : nat,
    Cpow (omega N) (n' * k) = C1.
Proof.
  intros N k HN Hmod n'.
  (* k = N * (k / N) + k mod N = N * (k / N) *)
  assert (Hk : k = (N * Nat.div k N)%nat).
  { rewrite (PeanoNat.Nat.div_mod k N HN) at 1.
    rewrite Hmod. rewrite PeanoNat.Nat.add_0_r. reflexivity. }
  rewrite Hk.
  rewrite (PeanoNat.Nat.mul_comm N (Nat.div k N)).
  rewrite PeanoNat.Nat.mul_assoc.
  (* n' * (k/N) * N *)
  rewrite Cpow_mul.
  rewrite (omega_pow N HN).
  apply Cpow_C1.
Qed.

(** Sum-accumulator helper: when every added term is [C1], the result
    is the initial accumulator with [nreal N] added to its real part. *)
Lemma sumω_const_C1 :
  forall (f : nat -> CComplex) (N : nat) (acc : CComplex),
    (forall n', f n' = C1) ->
    (fix sumω n a :=
       match n with
       | O => a
       | S n' => sumω n' (Cadd a (f n'))
       end) N acc
    = mkC (re acc + nreal N) (im acc).
Proof.
  intros f. induction N as [|N' IH]; intros acc Hf.
  - simpl. destruct acc as [ar ai]. simpl.
    apply CComplex_eq. unfold CComplex_req. simpl. split.
    + symmetry. apply CReal_plus_0_r.
    + reflexivity.
  - simpl. rewrite IH by exact Hf.
    rewrite Hf.
    destruct acc as [ar ai]. simpl.
    apply CComplex_eq. unfold CComplex_req. simpl. split.
    + (* (ar + 1) + nreal N' == ar + (1 + nreal N') *)
      ring.
    + (* ai + 0 == ai *)
      apply CReal_plus_0_r.
Qed.

(** Geometric sum: Σ_{n=0}^{N−1} ω_N^{nk} = N·δ_{k,0 mod N}. *)
Lemma geometric_sum_zero : forall (N k : nat), N <> 0%nat -> k mod N = 0%nat ->
    (fix sumω n acc :=
       match n with
       | O => acc
       | S n' => sumω n' (Cadd acc (Cpow (omega N) (n' * k)))
       end) N C0 = Cmul (Cinject_Q (Z.of_nat N # 1%positive)) C1.
Proof.
  intros N k HN Hmod.
  rewrite (sumω_const_C1 (fun n' => Cpow (omega N) (n' * k)) N C0
            (omega_pow_multiple N k HN Hmod)).
  (* mkC (re C0 + nreal N) (im C0) = Cmul (Cinject_Q (Z.of_nat N # 1)) C1 *)
  unfold C0. simpl.
  rewrite nreal_inject.
  apply CComplex_eq.
  unfold CComplex_req, Cmul, Cinject_Q, C1. simpl. split; ring.
Qed.

(** Apartness of [1 - omega N ^ k] from 0 when [k mod N <> 0].
    This is the standard classical-analysis fact that distinct primitive
    roots of unity are apart in [CReal] (their squared norm
    [|1 - e^{-2πi k/N}|² = 2(1 - cos(2π k/N))] is strictly positive when
    [k] is not a multiple of [N]).  A constructive proof would require
    the [sin]/[cos] series and quantitative estimates on [cos] near
    rational multiples of π; we axiomatize the apartness witness
    narrowly (Task C.0, 2026-04-30). *)
Axiom omega_pow_apart :
  forall (N k : nat),
    N <> 0%nat ->
    k mod N <> 0%nat ->
    Cnorm2 (Csub C1 (Cpow (omega N) k)) # 0.

(** ** Telescoping geometric sum *)

(** Forward-direction partial sum: [gsum N k = Σ_{j=0}^{N-1} ω^{j*k}],
    built left-to-right.  This is easier to reason about by induction
    than the reversed [fix sumω] used in the Lemma statements. *)
Fixpoint gsum (N k : nat) : CComplex :=
  match N with
  | O => C0
  | S N' => Cadd (gsum N' k) (Cpow (omega N) (N' * k))
  end.

(** [gsum] is parametric in [N] both as the outer count and as the [omega]
    index.  For our use we always instantiate them with the same value, so
    define a fixed-[N] variant that does not change [omega N] while
    inducting on the count. *)
Fixpoint gsum_at (Nfix : nat) (n k : nat) : CComplex :=
  match n with
  | O => C0
  | S n' => Cadd (gsum_at Nfix n' k) (Cpow (omega Nfix) (n' * k))
  end.

(** Generalized telescoping: for any starting accumulator [acc],
    the reverse-fix sum equals [acc + gsum_at Nfix n k] at the
    [~~C] level. *)
Lemma sumω_eq_gsum_at_req :
  forall (Nfix : nat) (k n : nat) (acc : CComplex),
    (fix sumω m a :=
       match m with
       | O => a
       | S m' => sumω m' (Cadd a (Cpow (omega Nfix) (m' * k)))
       end) n acc
    ~~C Cadd acc (gsum_at Nfix n k).
Proof.
  intros Nfix k. induction n as [|n' IH]; intro acc.
  - simpl. symmetry. apply Cadd_C0_r_req.
  - simpl. rewrite IH.
    (* (acc + ω^(n'*k)) + gsum_at Nfix n' k ~~C acc + (gsum_at Nfix (S n') k)
       where gsum_at Nfix (S n') k = gsum_at Nfix n' k + ω^(n'*k). *)
    simpl gsum_at.
    (* Goal: Cadd (Cadd acc ω^(n'k)) (gsum_at ...) ~~C
             Cadd acc (Cadd (gsum_at ...) ω^(n'k)) *)
    rewrite <- Cadd_assoc_req.
    apply Cadd_Proper; [reflexivity|].
    apply Cadd_comm_req.
Qed.

(** Telescoping identity at the [~~C] level:
    [(C1 - ω^k) * gsum_at Nfix n k ~~C C1 - ω^(n*k)]. *)
Lemma gsum_at_telescope_req :
  forall (Nfix k n : nat),
    Cmul (Csub C1 (Cpow (omega Nfix) k)) (gsum_at Nfix n k)
    ~~C Csub (Cpow (omega Nfix) (0 * k)) (Cpow (omega Nfix) (n * k)).
Proof.
  intros Nfix k. induction n as [|n' IH].
  - (* Base: LHS = (1 - ω^k) * 0 = 0; RHS = ω^0 - ω^0 = 0. *)
    simpl gsum_at.
    (* (1 - ω^k) * C0 ~~C C0; and ω^0 - ω^0 ~~C C0 *)
    apply (CComplex_req_trans _ C0).
    + apply Cmul_C0_r_req.
    + simpl Cpow.
      unfold CComplex_req, Csub, Cadd, Cneg, C0, C1; simpl.
      split; ring.
  - simpl gsum_at.
    (* Distribute: (1-ω^k) * (gsum_at n' + ω^(n'*k))
                 = (1-ω^k)*gsum_at n' + (1-ω^k)*ω^(n'*k) *)
    apply (CComplex_req_trans _
             (Cadd (Cmul (Csub C1 (Cpow (omega Nfix) k)) (gsum_at Nfix n' k))
                   (Cmul (Csub C1 (Cpow (omega Nfix) k)) (Cpow (omega Nfix) (n' * k))))).
    + apply Cmul_distrib_l_req.
    + (* IH gives the first summand ~~C ω^0 - ω^(n'*k).
         The second summand: (1 - ω^k)*ω^(n'*k) = ω^(n'k) - ω^k*ω^(n'k) = ω^(n'k) - ω^(k + n'k) = ω^(n'k) - ω^((S n')*k).
         Sum: ω^0 - ω^(n'k) + ω^(n'k) - ω^((S n')*k) = ω^0 - ω^((S n')*k). *)
      rewrite IH.
      (* Now the second [Cmul] needs explicit massaging.  Compute
         (S n') * k = k + n' * k. *)
      assert (Hexp : (S n' * k = k + n' * k)%nat).
      { simpl. reflexivity. }
      rewrite Hexp.
      rewrite Cpow_add.
      (* Goal: (ω^0 - ω^(n'*k)) + (1-ω^k)*ω^(n'*k)
              ~~C ω^0 - (ω^k * ω^(n'*k)) *)
      (* Expand the second product: (1-ω^k)*ω^(n'k) = ω^(n'k) - ω^k * ω^(n'k). *)
      apply (CComplex_req_trans _
               (Cadd (Csub (Cpow (omega Nfix) (0 * k)) (Cpow (omega Nfix) (n' * k)))
                     (Csub (Cpow (omega Nfix) (n' * k))
                           (Cmul (Cpow (omega Nfix) k) (Cpow (omega Nfix) (n' * k)))))).
      * apply Cadd_Proper; [reflexivity|].
        (* (1-ω^k)*ω^(n'k) ~~C ω^(n'k) - ω^k * ω^(n'k) *)
        unfold Csub.
        apply (CComplex_req_trans _
                 (Cadd (Cmul C1 (Cpow (omega Nfix) (n' * k)))
                       (Cmul (Cneg (Cpow (omega Nfix) k)) (Cpow (omega Nfix) (n' * k))))).
        { apply Cmul_distrib_r_req. }
        apply Cadd_Proper.
        { apply Cmul_C1_l_req. }
        (* Cneg (ω^k) * ω^(n'k) ~~C Cneg (ω^k * ω^(n'k)) *)
        destruct (Cpow (omega Nfix) k) as [ar ai].
        destruct (Cpow (omega Nfix) (n' * k)) as [br bi].
        unfold CComplex_req, Cmul, Cneg; simpl. split; ring.
      * (* (a - b) + (b - c) ~~C a - c, with a = ω^0, b = ω^(n'k), c = ω^k * ω^(n'k). *)
        destruct (Cpow (omega Nfix) (0 * k)) as [ar ai].
        destruct (Cpow (omega Nfix) (n' * k)) as [br bi].
        destruct (Cpow (omega Nfix) k) as [cr ci].
        unfold CComplex_req, Csub, Cadd, Cneg, Cmul; simpl. split; ring.
Qed.

(** When [N <> 0], [Cpow (omega N) (N * k) = C1] (uses [omega_pow]).
    We rewrite [N * k = k * N] first so that [Cpow_mul] gives us
    [Cpow (Cpow (omega N) N) k], at which point [omega_pow] applies. *)
Lemma omega_pow_Nk : forall (N k : nat), N <> 0%nat ->
    Cpow (omega N) (N * k) = Cpow C1 k.
Proof.
  intros N k HN.
  rewrite (PeanoNat.Nat.mul_comm N k).
  rewrite Cpow_mul.
  rewrite (omega_pow N HN).
  reflexivity.
Qed.

(** Geometric sum is zero when [k mod N <> 0]:
    derived from the telescoping identity and [omega_pow_apart]. *)
Lemma geometric_sum_nonzero : forall (N k : nat), N <> 0%nat -> k mod N <> 0%nat ->
    (fix sumω n acc :=
       match n with
       | O => acc
       | S n' => sumω n' (Cadd acc (Cpow (omega N) (n' * k)))
       end) N C0 = C0.
Proof.
  intros N k HN Hmod.
  (* Step 1: rewrite the fix-style sum to [C0 + gsum_at N N k] at ~~C level,
     hence Leibniz equal to gsum_at N N k. *)
  set (S_fix := (fix sumω n acc :=
       match n with
       | O => acc
       | S n' => sumω n' (Cadd acc (Cpow (omega N) (n' * k)))
       end) N C0).
  assert (HSeq : S_fix = gsum_at N N k).
  { unfold S_fix. apply CComplex_eq.
    apply (CComplex_req_trans _ (Cadd C0 (gsum_at N N k))).
    - apply sumω_eq_gsum_at_req.
    - apply Cadd_C0_l_req. }
  rewrite HSeq.
  (* Step 2: get the apartness witness for 1 - ω^k. *)
  set (D := Csub C1 (Cpow (omega N) k)).
  assert (HD : Cnorm2 D # 0).
  { unfold D. apply omega_pow_apart; assumption. }
  (* Step 3: apply Cinv D HD to both sides of the telescoping identity.
     We have D * gsum_at N N k ~~C ω^0 - ω^(N*k) = C1 - C1 = C0.
     So gsum_at N N k = Cinv D HD * (D * gsum_at N N k) = Cinv D HD * C0 = C0. *)
  assert (Htele : Cmul D (gsum_at N N k) = C0).
  { unfold D. apply CComplex_eq.
    apply (CComplex_req_trans _
            (Csub (Cpow (omega N) (0 * k)) (Cpow (omega N) (N * k)))).
    - apply gsum_at_telescope_req.
    - rewrite (omega_pow_Nk N k HN).
      simpl Cpow.
      rewrite Cpow_C1.
      unfold CComplex_req, Csub, Cadd, Cneg, C0, C1; simpl.
      split; ring. }
  (* From D * S = 0 and D apart 0, conclude S = 0:
     S = (Cinv D HD * D) * S = Cinv D HD * (D * S) = Cinv D HD * C0 = C0. *)
  apply CComplex_eq.
  apply (CComplex_req_trans _ (Cmul C1 (gsum_at N N k))).
  { symmetry. apply Cmul_C1_l_req. }
  (* Cmul (Cinv D HD * D) (gsum_at) ~~C C0 *)
  rewrite <- (Cinv_l D HD).
  apply (CComplex_req_trans _ (Cmul (Cinv D HD) (Cmul D (gsum_at N N k)))).
  { symmetry. apply Cmul_assoc_req. }
  rewrite Htele.
  apply Cmul_C0_r_req.
Qed.

(** ** Finite sums over ℂ *)

(** Sum a function f : {0..N-1} → ℂ. *)
Fixpoint csum (N : nat) (f : nat -> CComplex) : CComplex :=
  match N with
  | O    => C0
  | S n  => Cadd (csum n f) (f n)
  end.

(** Note: Both `csum_zero` and `csum_linear` are at the Leibniz level on CComplex,
    where Cadd is not strictly associative due to the underlying [CReal] structure.
    They are axiomatized at the interface level. *)
Lemma csum_zero : forall (N : nat) (f : nat -> CComplex),
    (forall k : nat, (k < N)%nat -> f k = C0) -> csum N f = C0.
Proof.
  induction N as [|n IH]; intros f Hzero.
  - reflexivity.
  - simpl. rewrite IH.
    + rewrite (Hzero n (PeanoNat.Nat.lt_succ_diag_r n)).
      apply CComplex_eq.
      unfold CComplex_req, Cadd, C0. simpl. split; ring.
    + intros k Hk. apply Hzero. apply PeanoNat.Nat.lt_lt_succ_r. exact Hk.
Qed.

Lemma csum_linear : forall (N : nat) (f g : nat -> CComplex) (c : CComplex),
    csum N (fun k => Cadd (f k) (Cmul c (g k)))
    = Cadd (csum N f) (Cmul c (csum N g)).
Proof.
  induction N as [|n IH]; intros f g c.
  - simpl. apply CComplex_eq.
    unfold CComplex_req, Cadd, Cmul, C0. simpl. split; ring.
  - simpl. rewrite IH.
    apply CComplex_eq.
    destruct (csum n f) as [Sfr Sfi].
    destruct (csum n g) as [Sgr Sgi].
    destruct (f n) as [fnr fni].
    destruct (g n) as [gnr gni].
    destruct c as [cr ci].
    unfold CComplex_req, Cadd, Cmul. simpl. split; ring.
Qed.

(** [csum] distributes over pointwise [Cadd].  Specialization of
    [csum_linear] with c = C1, but proved directly to avoid the C1·g(k)
    detour. *)
Lemma csum_add : forall (N : nat) (f g : nat -> CComplex),
    csum N (fun k => Cadd (f k) (g k))
    = Cadd (csum N f) (csum N g).
Proof.
  induction N as [|n IH]; intros f g.
  - simpl. apply CComplex_eq.
    unfold CComplex_req, Cadd, C0. simpl. split; ring.
  - simpl. rewrite IH.
    apply CComplex_eq.
    destruct (csum n f) as [Sfr Sfi].
    destruct (csum n g) as [Sgr Sgi].
    destruct (f n) as [fnr fni].
    destruct (g n) as [gnr gni].
    unfold CComplex_req, Cadd. simpl. split; ring.
Qed.

(** A constant-zero sum is zero. *)
Lemma csum_zero_const : forall (N : nat),
    csum N (fun _ => C0) = C0.
Proof.
  intro N. apply csum_zero. intros; reflexivity.
Qed.

(** ** Fubini for [csum]: rectangular sum interchange. *)
Lemma csum_swap : forall (N1 N2 : nat) (f : nat -> nat -> CComplex),
    csum N1 (fun i => csum N2 (fun j => f i j)) =
    csum N2 (fun j => csum N1 (fun i => f i j)).
Proof.
  induction N1 as [|n1 IH]; intro N2; intro f.
  - (* LHS = csum 0 _ = C0; RHS = csum N2 (fun _ => C0) = C0. *)
    simpl. symmetry. apply csum_zero_const.
  - (* LHS = Cadd (csum n1 (fun i => csum N2 (fun j => f i j)))
                  (csum N2 (fun j => f n1 j)) *)
    simpl csum at 1.
    rewrite (IH N2 f).
    (* Goal: Cadd (csum N2 (fun j => csum n1 (fun i => f i j)))
                  (csum N2 (fun j => f n1 j))
            = csum N2 (fun j => Cadd (csum n1 (fun i => f i j)) (f n1 j)) *)
    symmetry. apply csum_add.
Qed.

(** [csum] commutes with left-multiplication by a constant. *)
Lemma csum_Cmul_l : forall (N : nat) (c : CComplex) (f : nat -> CComplex),
    Cmul c (csum N f) = csum N (fun k => Cmul c (f k)).
Proof.
  induction N as [|n IH]; intros c f.
  - simpl. apply CComplex_eq.
    unfold CComplex_req, Cmul, C0. simpl. split; ring.
  - simpl. rewrite <- IH.
    apply CComplex_eq.
    destruct (csum n f) as [Sr Si].
    destruct (f n) as [fnr fni].
    destruct c as [cr ci].
    unfold CComplex_req, Cadd, Cmul. simpl. split; ring.
Qed.

(** ** [firstn]/[pad_to] idempotence (forward declaration of [pad_to])

    Note: [pad_to] is defined further below at line ~566.  We delay this
    lemma until after [pad_to] for clarity. *)

(** ** Safe list indexing *)

Definition nth_C (xs : list CComplex) (n : nat) : CComplex :=
  nth n xs C0.

(** ** Discrete Fourier Transform *)

(** DFT of a sequence xs of length N:
    X_k = Σ_{n=0}^{N-1}  xs[n] · ω_N^{n·k} *)
Definition dft_coeff (xs : list CComplex) (k : nat) : CComplex :=
  let N := length xs in
  csum N (fun n => Cmul (nth_C xs n) (Cpow (omega N) (n * k))).

(** The full DFT: list of N coefficients X_0, …, X_{N-1}. *)
Definition dft (xs : list CComplex) : list CComplex :=
  List.map (dft_coeff xs) (List.seq 0 (length xs)).

(** ** Inverse DFT *)

(** IDFT synthesis formula:
    x_n = (1/N) Σ_{k=0}^{N-1}  X_k · ω_N^{−n·k} *)
Definition idft_coeff (Xs : list CComplex) (n : nat) : CComplex :=
  let N := length Xs in
  let inv_N := Cinject_Q (1 # Pos.of_nat N) in
  Cmul inv_N (csum N (fun k => Cmul (nth_C Xs k) (Cpow (omega N) (N * k - n * k)))).
  (* Using ω_N^{−nk} = ω_N^{(N-n)k} for integer arithmetic. *)

Definition idft (Xs : list CComplex) : list CComplex :=
  List.map (idft_coeff Xs) (List.seq 0 (length Xs)).

(** ** Fundamental theorem: IDFT ∘ DFT = id *)

(** *** Bridge: tail-recursive [sumω] form ↔ explicit [csum] form.

    The [geometric_sum_zero]/[geometric_sum_nonzero] lemmas are stated
    using the reverse-fix accumulator form
        [(fix sumω n acc := match n with | O => acc
                            | S n' => sumω n' (Cadd acc (Cpow (omega N) (n'*k)))
                            end) N C0],
    while DFT manipulations use the forward-fold [csum] form
        [csum N (fun j => Cpow (omega N) (j*k))].
    Both reduce (by induction on N) to [gsum_at N N k]. *)

Lemma gsum_at_eq_csum : forall (Nfix n k : nat),
    gsum_at Nfix n k = csum n (fun j => Cpow (omega Nfix) (j * k)).
Proof.
  intros Nfix. induction n as [|n' IH]; intro k.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma sumω_eq_csum : forall (N k : nat),
    (fix sumω n acc :=
       match n with
       | O => acc
       | S n' => sumω n' (Cadd acc (Cpow (omega N) (n' * k)))
       end) N C0
    = csum N (fun j => Cpow (omega N) (j * k)).
Proof.
  intros N k.
  apply CComplex_eq.
  apply (CComplex_req_trans _ (Cadd C0 (gsum_at N N k))).
  - apply sumω_eq_gsum_at_req.
  - rewrite gsum_at_eq_csum.
    apply Cadd_C0_l_req.
Qed.

(** *** Reformulation of [geometric_sum_zero/nonzero] in [csum] form. *)

Lemma csum_omega_zero : forall (N k : nat),
    N <> 0%nat -> k mod N = 0%nat ->
    csum N (fun j => Cpow (omega N) (j * k))
    = Cmul (Cinject_Q (Z.of_nat N # 1%positive)) C1.
Proof.
  intros N k HN Hmod.
  rewrite <- sumω_eq_csum.
  apply geometric_sum_zero; assumption.
Qed.

Lemma csum_omega_nonzero : forall (N k : nat),
    N <> 0%nat -> k mod N <> 0%nat ->
    csum N (fun j => Cpow (omega N) (j * k)) = C0.
Proof.
  intros N k HN Hmod.
  rewrite <- sumω_eq_csum.
  apply geometric_sum_nonzero; assumption.
Qed.

(** *** Algebraic identity: [(1/N) · N = 1] in [CComplex]. *)

Lemma Cinject_Q_inv_N_mul_N : forall N : nat, N <> 0%nat ->
    Cmul (Cinject_Q (1 # Pos.of_nat N)) (Cinject_Q (Z.of_nat N # 1%positive)) = C1.
Proof.
  intros N HN.
  apply CComplex_eq.
  unfold CComplex_req, Cmul, Cinject_Q, C1.
  split; simpl re; simpl im.
  - (* Goal: inject_Q (1#PN) * inject_Q (N#1) - 0*0 == 1. *)
    destruct N as [|N']; [contradiction|clear HN].
    set (a := inject_Q (1 # Pos.of_nat (S N'))).
    set (b := inject_Q (Z.of_nat (S N') # 1)).
    apply (CRealEq_trans _ (a * b)).
    + ring.
    + unfold a, b. rewrite <- inject_Q_mult.
      assert (Hq : ((1 # Pos.of_nat (S N')) * (Z.of_nat (S N') # 1) == 1)%Q).
      { rewrite Qmult_comm. apply Q_of_nat_inv. }
      rewrite (inject_Q_morph _ _ Hq).
      apply inject_Q_one.
  - destruct N as [|N']; [contradiction|clear HN]. ring.
Qed.

(** *** Helper: [List.map] over [seq] equals a list when indexed values match. *)

Lemma map_seq_nth_C : forall (xs : list CComplex) (f : nat -> CComplex),
    (forall i, (i < length xs)%nat -> f i = nth_C xs i) ->
    List.map f (List.seq 0 (length xs)) = xs.
Proof.
  intros xs f Hf.
  apply List.nth_ext with (d := C0) (d' := C0).
  - rewrite List.map_length, List.seq_length. reflexivity.
  - intros i Hi.
    rewrite List.map_length, List.seq_length in Hi.
    rewrite (List.nth_indep _ C0 (f 0%nat))
      by (rewrite List.map_length, List.seq_length; exact Hi).
    rewrite List.map_nth.
    rewrite List.seq_nth by exact Hi.
    simpl. unfold nth_C in Hf. apply Hf. exact Hi.
Qed.

(** *** Helper: rearrangement of the omega exponent in [idft (dft xs)].

    For [m < N] and [n < N], we have
        [Cpow (omega N) (n*k) · Cpow (omega N) (N*k - m*k)
         = Cpow (omega N) ((n + N - m) * k)],
    where [+], [-], [*] are nat operations.  The key observation is
    that [n*k + (N*k - m*k) = (n + N - m) * k] when [m <= N], which
    holds since we always have [m < N] in the application. *)

Lemma omega_pow_combine : forall (N m n k : nat),
    (m <= N)%nat ->
    Cmul (Cpow (omega N) (n * k)) (Cpow (omega N) (N * k - m * k))
    = Cpow (omega N) ((n + N - m) * k).
Proof.
  intros N m n k Hm.
  rewrite <- Cpow_add.
  f_equal.
  (* n*k + (N*k - m*k) = (n + N - m) * k *)
  assert (HmkNk : (m * k <= N * k)%nat) by (apply PeanoNat.Nat.mul_le_mono_r; exact Hm).
  assert (HmN : (m <= n + N)%nat) by lia.
  rewrite PeanoNat.Nat.mul_sub_distr_r.
  rewrite PeanoNat.Nat.mul_add_distr_r.
  lia.
Qed.

(** *** Modular reasoning: for [m, n < N], [(n + N - m) mod N = 0] iff [n = m]. *)

Lemma mod_n_plus_N_minus_m_zero : forall (N m n : nat),
    (n < N)%nat -> (m < N)%nat ->
    (n + N - m) mod N = 0%nat -> n = m.
Proof.
  intros N m n Hn Hm Hmod.
  (* n + N - m ∈ [1, 2N-1] when n,m ∈ [0,N-1]; (n+N-m) mod N = 0 means
     it equals N exactly, hence n = m. *)
  assert (HN : N <> 0%nat) by lia.
  assert (Hge : (n + N - m >= 1)%nat) by lia.
  assert (Hle : (n + N - m <= 2 * N - 1)%nat) by lia.
  (* (n+N-m) mod N = 0 means N divides (n+N-m). Since 1 ≤ n+N-m ≤ 2N-1,
     the only multiple of N in this range is N itself. *)
  assert (Heq : (n + N - m = N)%nat).
  { destruct (PeanoNat.Nat.mod_divides (n+N-m) N HN) as [Hd _].
    specialize (Hd Hmod).
    destruct Hd as [q Hq].
    destruct q as [|[|q']]; [lia|lia|].
    (* q >= 2: n+N-m = N*(S(S q')) >= 2N, contradicts Hle. *)
    rewrite Hq. simpl. nia. }
  lia.
Qed.

Lemma mod_n_plus_N_minus_m_nonzero : forall (N m n : nat),
    (n < N)%nat -> (m < N)%nat -> n <> m ->
    (n + N - m) mod N <> 0%nat.
Proof.
  intros N m n Hn Hm Hneq Hmod.
  apply Hneq. apply mod_n_plus_N_minus_m_zero with N; assumption.
Qed.

(** *** Pointwise extensionality for [csum]: if [f i = g i] for all [i < N],
    then [csum N f = csum N g] (Leibniz). *)

Lemma csum_ext : forall (N : nat) (f g : nat -> CComplex),
    (forall i, (i < N)%nat -> f i = g i) ->
    csum N f = csum N g.
Proof.
  induction N as [|n IH]; intros f g Hfg.
  - reflexivity.
  - simpl. rewrite (IH f g) by (intros; apply Hfg; lia).
    rewrite (Hfg n) by lia. reflexivity.
Qed.

(** *** Conditional split: when at most one summand is nonzero. *)

Lemma csum_select : forall (N : nat) (m : nat) (f : nat -> CComplex),
    (m < N)%nat ->
    (forall l, (l < N)%nat -> l <> m -> f l = C0) ->
    csum N f = f m.
Proof.
  intros N m f Hm Hzero.
  induction N as [|n IH].
  - lia.
  - simpl.
    destruct (PeanoNat.Nat.eq_dec n m) as [Heq | Hneq].
    + subst n.
      assert (Hcs : csum m f = C0).
      { apply csum_zero. intros k Hk. apply Hzero; lia. }
      rewrite Hcs.
      apply CComplex_eq. unfold CComplex_req, Cadd, C0; simpl. split; ring.
    + assert (Hmn : (m < n)%nat) by lia.
      rewrite IH by (try assumption; intros l Hl Hlm; apply Hzero; lia).
      rewrite (Hzero n) by lia.
      apply CComplex_eq. unfold CComplex_req, Cadd, C0; simpl. split; ring.
Qed.

(** *** Cmul commutes with csum on the right (mirror of [csum_Cmul_l]). *)

Lemma csum_Cmul_r : forall (N : nat) (c : CComplex) (f : nat -> CComplex),
    Cmul (csum N f) c = csum N (fun k => Cmul (f k) c).
Proof.
  induction N as [|n IH]; intros c f.
  - simpl. apply CComplex_eq.
    unfold CComplex_req, Cmul, C0. simpl. split; ring.
  - simpl. rewrite <- IH.
    apply CComplex_eq.
    destruct (csum n f) as [Sr Si].
    destruct (f n) as [fnr fni].
    destruct c as [cr ci].
    unfold CComplex_req, Cadd, Cmul. simpl. split; ring.
Qed.

(** *** The fundamental DFT inversion identity. *)

Theorem idft_dft_inv : forall (xs : list CComplex), idft (dft xs) = xs.
Proof.
  intro xs.
  destruct xs as [|x0 xs'] eqn:Exs.
  - (* xs = [] *) reflexivity.
  - assert (HNne : length xs <> 0%nat).
    { rewrite Exs. simpl. discriminate. }
    rewrite <- Exs. clear Exs x0 xs'.
    set (N := length xs).
    assert (HN : (0 < N)%nat) by (subst N; lia).
    unfold idft, dft.
    fold N.
    assert (Hldft : length (List.map (dft_coeff xs) (List.seq 0 N)) = N).
    { rewrite List.map_length, List.seq_length. reflexivity. }
    rewrite Hldft.
    apply map_seq_nth_C.
    intros m Hm.
    (* Prove: idft_coeff (dft xs) m = nth_C xs m. *)
    unfold idft_coeff.
    rewrite Hldft.
    fold N.
    (* Step 1: replace [nth_C (map (dft_coeff xs) (seq 0 N)) k] with [dft_coeff xs k]
       inside the inner csum. *)
    rewrite (csum_ext N
               (fun k => Cmul (nth_C (List.map (dft_coeff xs) (List.seq 0 N)) k)
                              (Cpow (omega N) (N * k - m * k)))
               (fun k => Cmul (dft_coeff xs k)
                              (Cpow (omega N) (N * k - m * k)))).
    2: { intros k Hk. f_equal. unfold nth_C.
         rewrite (List.nth_indep _ C0 (dft_coeff xs 0))
           by (rewrite List.map_length, List.seq_length; exact Hk).
         rewrite List.map_nth.
         rewrite List.seq_nth by exact Hk. reflexivity. }
    (* Step 2: expand [dft_coeff xs k] in the sum.  [dft_coeff xs k] uses
       [length xs] which equals [N]; we unfold and refold via [csum_ext]. *)
    rewrite (csum_ext N
               (fun k => Cmul (dft_coeff xs k) (Cpow (omega N) (N * k - m * k)))
               (fun k => Cmul (csum N (fun n => Cmul (nth_C xs n) (Cpow (omega N) (n * k))))
                              (Cpow (omega N) (N * k - m * k)))).
    2: { intros k Hk. unfold dft_coeff. fold N. reflexivity. }
    (* Step 3: distribute the outer Cmul into the inner csum (csum_Cmul_r),
       then apply csum_swap to interchange the two sums. *)
    rewrite (csum_ext N
               (fun k => Cmul (csum N (fun n => Cmul (nth_C xs n) (Cpow (omega N) (n * k))))
                              (Cpow (omega N) (N * k - m * k)))
               (fun k => csum N (fun n => Cmul (Cmul (nth_C xs n) (Cpow (omega N) (n * k)))
                                               (Cpow (omega N) (N * k - m * k))))).
    2: { intros k Hk. apply csum_Cmul_r. }
    (* Step 4: use csum_swap to interchange. *)
    rewrite csum_swap.
    (* Goal: Cmul inv_N (csum N (fun n => csum N (fun k =>
              Cmul (Cmul (nth_C xs n) (ω^{nk})) (ω^{Nk - mk}))))
            = nth_C xs m *)
    (* Step 5: simplify each inner k-sum.  Use associativity to factor xs[n]
       out of the inner csum, then combine ω^{nk} · ω^{Nk-mk} = ω^{(n+N-m)k}. *)
    rewrite (csum_ext N
               (fun n => csum N (fun k =>
                   Cmul (Cmul (nth_C xs n) (Cpow (omega N) (n * k)))
                        (Cpow (omega N) (N * k - m * k))))
               (fun n => Cmul (nth_C xs n)
                              (csum N (fun k =>
                                 Cpow (omega N) ((n + N - m) * k))))).
    2: { intros n Hn.
         (* csum N (fun k => Cmul (Cmul xs_n ω^{nk}) ω^{Nk-mk})
            = Cmul xs_n (csum N (fun k => ω^{(n+N-m)k})) *)
         rewrite csum_Cmul_l.
         apply csum_ext.
         intros k Hk.
         (* Cmul (Cmul xs_n ω^{nk}) ω^{Nk-mk} = Cmul xs_n (ω^{nk} · ω^{Nk-mk})
            = Cmul xs_n ω^{(n+N-m)k} *)
         apply CComplex_eq.
         apply (CComplex_req_trans _
                  (Cmul (nth_C xs n) (Cmul (Cpow (omega N) (n * k))
                                           (Cpow (omega N) (N * k - m * k))))).
         { symmetry. apply Cmul_assoc_req. }
         apply Cmul_Proper; [reflexivity|].
         (* Cpow ω (n*k) · Cpow ω (Nk - mk) = Cpow ω ((n+N-m)*k), via omega_pow_combine. *)
         rewrite (omega_pow_combine N m n k); [reflexivity | lia]. }
    (* Step 6: split the outer csum at index n = m. *)
    rewrite (csum_select N m
               (fun n => Cmul (nth_C xs n)
                              (csum N (fun k => Cpow (omega N) ((n + N - m) * k))))
               Hm).
    2: { intros n Hn Hneq.
         (* Convert ((n+N-m) * k) into (k * (n+N-m)) for csum_omega_nonzero. *)
         rewrite (csum_ext N
                    (fun k => Cpow (omega N) ((n + N - m) * k))
                    (fun k => Cpow (omega N) (k * (n + N - m)))).
         2: { intros k _. rewrite (PeanoNat.Nat.mul_comm (n + N - m) k). reflexivity. }
         (* Now apply csum_omega_nonzero. *)
         assert (Hmod : (n + N - m) mod N <> 0%nat)
           by (apply mod_n_plus_N_minus_m_nonzero; assumption).
         rewrite (csum_omega_nonzero N (n + N - m) HNne Hmod).
         apply CComplex_eq.
         destruct (nth_C xs n) as [a b].
         unfold CComplex_req, Cmul, C0; simpl. split; ring. }
    (* Step 7: at n = m, the inner csum equals N (geometric_sum_zero case). *)
    (* (m + N - m) = N, and N mod N = 0. *)
    assert (HmNm : (m + N - m = N)%nat) by lia.
    rewrite (csum_ext N
               (fun k => Cpow (omega N) ((m + N - m) * k))
               (fun k => Cpow (omega N) (N * k))).
    2: { intros k Hk. rewrite HmNm. reflexivity. }
    (* Need: csum N (fun k => Cpow (omega N) (N*k)) = Cmul (N as complex) C1.
       Convert N*k to k*N to use csum_omega_zero. *)
    assert (HmodNN : (N mod N = 0)%nat) by (apply PeanoNat.Nat.Div0.mod_same).
    rewrite (csum_ext N
               (fun k => Cpow (omega N) (N * k))
               (fun j => Cpow (omega N) (j * N))).
    2: { intros k _. rewrite (PeanoNat.Nat.mul_comm N k). reflexivity. }
    rewrite (csum_omega_zero N N HNne HmodNN).
    (* Goal: Cmul inv_N (Cmul xs[m] (Cmul (Cinject_Q (Z.of_nat N # 1)) C1)) = nth_C xs m *)
    set (inv_N := Cinject_Q (1 # Pos.of_nat N)).
    (* Cmul C1 of last factor, then combine inv_N · N = 1. *)
    apply CComplex_eq.
    apply (CComplex_req_trans _
             (Cmul inv_N (Cmul (nth_C xs m) (Cinject_Q (Z.of_nat N # 1%positive))))).
    { apply Cmul_Proper; [reflexivity|].
      apply Cmul_Proper; [reflexivity|]. apply Cmul_C1_r_req. }
    (* Reorder: inv_N · (xs_m · N) = (inv_N · N) · xs_m = C1 · xs_m = xs_m,
       but need to reassoc and commute. Easier: direct expansion. *)
    apply (CComplex_req_trans _
             (Cmul (Cmul inv_N (Cinject_Q (Z.of_nat N # 1%positive))) (nth_C xs m))).
    { (* inv_N · (xs_m · N) ~~C (inv_N · N) · xs_m *)
      apply (CComplex_req_trans _ (Cmul inv_N (Cmul (Cinject_Q (Z.of_nat N # 1%positive)) (nth_C xs m)))).
      - apply Cmul_Proper; [reflexivity|]. apply Cmul_comm_req.
      - apply Cmul_assoc_req. }
    unfold inv_N. rewrite (Cinject_Q_inv_N_mul_N N HNne).
    apply Cmul_C1_l_req.
Qed.

(** *** Periodicity of [Cpow (omega N)]: shifting the exponent by [N*b]
    leaves the value unchanged (Cpow_add + omega_pow). *)

Lemma omega_pow_period_add : forall (N a b : nat), N <> 0%nat ->
    Cpow (omega N) (a + N * b) = Cpow (omega N) a.
Proof.
  intros N a b HN.
  rewrite Cpow_add.
  rewrite omega_pow_Nk.
  - rewrite Cpow_C1. apply CComplex_eq. apply Cmul_C1_r_req.
  - exact HN.
Qed.

(** *** Cnegation commutes with [csum]. *)

Lemma csum_neg : forall (N : nat) (f : nat -> CComplex),
    csum N (fun n => Cneg (f n)) = Cneg (csum N f).
Proof.
  induction N as [|n IH]; intro f.
  - simpl. apply CComplex_eq.
    unfold CComplex_req, Cneg, C0; simpl. split; ring.
  - simpl. rewrite IH.
    apply CComplex_eq.
    destruct (csum n f) as [Sr Si].
    destruct (f n) as [fnr fni].
    unfold CComplex_req, Cadd, Cneg; simpl. split; ring.
Qed.

(** *** Left-extension form of [csum]: peel off the [n = 0] term.

    The standard [csum] definition peels off the final term:
    [csum (S n) f = csum n f + f n].  This lemma gives the symmetric
    "peel off the first term" form, used for index-reversal and
    cyclic-shift arguments. *)

Lemma csum_succ_l : forall (k : nat) (f : nat -> CComplex),
    csum (S k) f = Cadd (f 0%nat) (csum k (fun n => f (S n))).
Proof.
  induction k as [|k IH]; intro f.
  - simpl. apply CComplex_eq.
    unfold CComplex_req, Cadd, C0; simpl. split; ring.
  - (* csum (S (S k)) f = csum (S k) f + f (S k)
                       = (f 0 + csum k (fun n => f (S n))) + f (S k)   [IH]
                       = f 0 + (csum k (fun n => f (S n)) + f (S k))   [Cadd-assoc up to ~~C]
                       = f 0 + csum (S k) (fun n => f (S n)).          [csum-def] *)
    change (csum (S (S k)) f) with (Cadd (csum (S k) f) (f (S k))).
    rewrite (IH f).
    change (csum (S k) (fun n => f (S n))) with
        (Cadd (csum k (fun n => f (S n))) (f (S k))).
    apply CComplex_eq.
    destruct (csum k (fun n => f (S n))) as [Sr Si].
    destruct (f 0%nat) as [f0r f0i].
    destruct (f (S k)) as [fr fi].
    unfold CComplex_req, Cadd; simpl. split; ring.
Qed.

(** *** Index-reversal for [csum] over [omega N]-powers (α R13).

    The sum [Σ_{n=0}^{N-1} ω^{(N-n)·d}] equals [Σ_{n=0}^{N-1} ω^{n·d}].
    Both sums range over the same multiset of values
    [{ω^{j·d} : j ∈ {0, 1, …, N-1}}] — the LHS visits them in the order
    [j = N, N-1, …, 1] (and [ω^{N·d} = ω^{0·d} = C1] by [omega_pow_Nk]).

    Proof by case-split on whether [d mod N = 0]:
    - If [d mod N = 0], every summand on each side is [C1] (by
      [omega_pow_multiple]), so both sides equal [csum N (fun _ => C1)].
    - If [d mod N ≠ 0], both sides equal [C0]: the RHS by
      [csum_omega_nonzero] directly; the LHS by reindexing
      [n ↦ N - 1 - n] to convert the [(N - n)] reversed pattern back to
      the forward [n*d] pattern. *)

Lemma csum_omega_reverse : forall (N d : nat),
    N <> 0%nat ->
    csum N (fun n => Cpow (omega N) ((N - n) * d)) =
    csum N (fun n => Cpow (omega N) (n * d)).
Proof.
  intros N d HN.
  destruct (PeanoNat.Nat.eq_dec (d mod N) 0) as [Hzero | Hnonzero].
  - (* Case [d mod N = 0]: each summand is [C1]. *)
    transitivity (csum N (fun _ : nat => C1)).
    + apply csum_ext. intros n _.
      apply (omega_pow_multiple N d HN Hzero (N - n)).
    + symmetry. apply csum_ext. intros n _.
      apply (omega_pow_multiple N d HN Hzero n).
  - (* Case [d mod N ≠ 0]: both sides equal [C0]. *)
    rewrite (csum_omega_nonzero N d HN Hnonzero).
    (* Show LHS = C0.  Use the telescoping identity [(C1 - ω^d) * LHS = C0]
       derived as follows:
         (C1 - ω^d) * LHS
           = csum N (fun n => ω^((N-n)*d) - ω^((N-n+1)*d))      [csum_Cmul_l + ring]
           = peel off n=0 from the *second* sub-sum, reindex n=k+1, and observe:
             Σ_{n=0}^{N-1} ω^((N-n+1)*d)  =  ω^((N+1)*d) + Σ_{k=0}^{N-2} ω^((N-k)*d)
                                          =  ω^((N+1)*d) + (LHS - ω^(1*d))
                                          =  ω^d * ω^(N*d) + LHS - ω^d
                                          =  ω^d + LHS - ω^d                      [omega_pow_Nk: ω^(N*d) = C1]
                                          =  LHS.
             So the telescoped sum equals LHS - LHS = C0.
       Then [(C1 - ω^d) * LHS = C0] together with apartness of [C1 - ω^d]
       (via [omega_pow_apart]) gives [LHS = C0]. *)
    set (T := csum N (fun n => Cpow (omega N) ((N - n) * d))).
    set (D := Csub C1 (Cpow (omega N) d)).
    assert (HD : Cnorm2 D # 0)
      by (unfold D; apply omega_pow_apart; assumption).
    (* Show D * T = C0. *)
    assert (HDT : Cmul D T = C0).
    { (* (C1 - ω^d) * Σ ω^((N-n)*d) = Σ (ω^((N-n)*d) - ω^((N-n+1)*d)). *)
      unfold D, T.
      rewrite csum_Cmul_l.
      transitivity (csum N (fun n => Cadd (Cpow (omega N) ((N - n) * d))
                                          (Cneg (Cpow (omega N) ((N - n + 1) * d))))).
      { apply csum_ext. intros n _.
        (* Goal: Cmul (Csub C1 ω^d) ω^((N-n)*d) = ω^((N-n)*d) + Cneg ω^((N-n+1)*d). *)
        apply CComplex_eq.
        unfold Csub.
        apply (CComplex_req_trans _
                 (Cadd (Cmul C1 (Cpow (omega N) ((N - n) * d)))
                       (Cmul (Cneg (Cpow (omega N) d)) (Cpow (omega N) ((N - n) * d))))).
        { apply Cmul_distrib_r_req. }
        apply Cadd_Proper.
        { apply Cmul_C1_l_req. }
        (* Goal: Cmul (Cneg ω^d) ω^((N-n)*d) ~~C Cneg ω^((N-n+1)*d).
           = Cneg (Cmul ω^d ω^((N-n)*d))     [Cneg-Cmul commute]
           = Cneg ω^(d + (N-n)*d)            [Cpow_add inverted]
           = Cneg ω^((N-n+1)*d).             [arithmetic] *)
        replace ((N - n + 1) * d)%nat with (d + (N - n) * d)%nat by lia.
        rewrite Cpow_add.
        destruct (Cpow (omega N) d) as [ar ai].
        destruct (Cpow (omega N) ((N - n) * d)) as [br bi].
        unfold CComplex_req, Cmul, Cneg; simpl. split; ring. }
      (* Now split the difference into two sums. *)
      rewrite csum_add.
      rewrite csum_neg.
      (* Goal: csum N (fun n => ω^((N-n)*d)) + Cneg (csum N (fun n => ω^((N-n+1)*d))) = C0.
         Strategy: show the second sum equals csum N (fun n => ω^((N-n)*d))
         (i.e., the LHS of csum_omega_reverse), so the whole thing is x + (- x) = 0. *)
      assert (Hshift :
                csum N (fun n => Cpow (omega N) ((N - n + 1) * d)) =
                csum N (fun n => Cpow (omega N) ((N - n) * d))).
      { destruct N as [|N']; [contradiction|clear HN].
        rewrite (csum_succ_l N' (fun n => Cpow (omega (S N')) ((S N' - n + 1) * d))).
        rewrite (csum_ext N'
                   (fun n => Cpow (omega (S N')) ((S N' - S n + 1) * d))
                   (fun n => Cpow (omega (S N')) ((S N' - n) * d))).
        2: { intros n Hn. f_equal. lia. }
        replace (S N' - 0 + 1)%nat with (S N' + 1)%nat by lia.
        (* Now goal:
             Cadd ω^((S N' + 1)*d) (csum N' (fun n => ω^((S N' - n)*d)))
           = csum (S N') (fun n => ω^((S N' - n)*d))
           which by csum-def equals
             Cadd (csum N' (fun n => ω^((S N' - n)*d))) (ω^((S N' - N')*d)). *)
        change (csum (S N') (fun n => Cpow (omega (S N')) ((S N' - n) * d))) with
            (Cadd (csum N' (fun n => Cpow (omega (S N')) ((S N' - n) * d)))
                  (Cpow (omega (S N')) ((S N' - N') * d))).
        replace (S N' - N')%nat with 1%nat by lia.
        replace ((S N' + 1) * d)%nat with (d + S N' * d)%nat by lia.
        rewrite (omega_pow_period_add (S N') d d (PeanoNat.Nat.neq_succ_0 N')).
        replace (1 * d)%nat with d by lia.
        apply CComplex_eq.
        destruct (csum N' (fun n => Cpow (omega (S N')) ((S N' - n) * d))) as [Sr Si].
        destruct (Cpow (omega (S N')) d) as [wr wi].
        unfold CComplex_req, Cadd; simpl. split; ring. }
      rewrite Hshift.
      apply CComplex_eq.
      destruct (csum N (fun n => Cpow (omega N) ((N - n) * d))) as [Sr Si].
      unfold CComplex_req, Cadd, Cneg, C0; simpl. split; ring. }
    (* Now T = Cinv D HD * (D * T) = Cinv D HD * C0 = C0. *)
    apply CComplex_eq.
    apply (CComplex_req_trans _ (Cmul C1 T)).
    { symmetry. apply Cmul_C1_l_req. }
    rewrite <- (Cinv_l D HD).
    apply (CComplex_req_trans _ (Cmul (Cinv D HD) (Cmul D T))).
    { symmetry. apply Cmul_assoc_req. }
    rewrite HDT.
    apply Cmul_C0_r_req.
Qed.

(** ** Fundamental theorem (mirror): DFT ∘ IDFT = id

    The DFT is a unitary involution up to conjugation; in particular,
    [dft (idft xs) = xs].  The proof structure mirrors [idft_dft_inv]
    via the [csum_swap] interchange, but the key inner geometric sum
        [Σ_{n=0}^{N-1} ω^{(N-n)*l + n*m}]
    requires a case split on whether [l <= m] (where the exponent
    rewrites to [n*(m-l) + N*l] and [omega_pow_period_add] gives the
    result) or [l > m] (where the exponent rewrites to
    [(N-n)*(l-m) + N*m], [omega_pow_period_add] strips the [N*m], and
    the index-reversal helper [csum_omega_reverse] converts to the
    forward [n*(l-m)] form).

    α R12 implemented the [l <= m] case; α R13 added [csum_omega_reverse]
    and closed the proof. *)

Theorem dft_idft_inv : forall (xs : list CComplex), dft (idft xs) = xs.
Proof.
  intro xs.
  destruct xs as [|x0 xs'] eqn:Exs.
  - (* xs = [] *) reflexivity.
  - assert (HNne : length xs <> 0%nat).
    { rewrite Exs. simpl. discriminate. }
    rewrite <- Exs. clear Exs x0 xs'.
    set (N := length xs).
    assert (HN : (0 < N)%nat) by (subst N; lia).
    unfold dft, idft.
    fold N.
    assert (Hlidft : length (List.map (idft_coeff xs) (List.seq 0 N)) = N).
    { rewrite List.map_length, List.seq_length. reflexivity. }
    rewrite Hlidft.
    apply map_seq_nth_C.
    intros m Hm.
    (* Goal: dft_coeff (idft xs) m = nth_C xs m *)
    unfold dft_coeff.
    rewrite Hlidft.
    fold N.
    (* Step 1: replace [nth_C (map (idft_coeff xs) (seq 0 N)) n] with [idft_coeff xs n]. *)
    rewrite (csum_ext N
               (fun n => Cmul (nth_C (List.map (idft_coeff xs) (List.seq 0 N)) n)
                              (Cpow (omega N) (n * m)))
               (fun n => Cmul (idft_coeff xs n)
                              (Cpow (omega N) (n * m)))).
    2: { intros n Hn. f_equal. unfold nth_C.
         rewrite (List.nth_indep _ C0 (idft_coeff xs 0))
           by (rewrite List.map_length, List.seq_length; exact Hn).
         rewrite List.map_nth.
         rewrite List.seq_nth by exact Hn. reflexivity. }
    (* Step 2: expand [idft_coeff xs n]. *)
    rewrite (csum_ext N
               (fun n => Cmul (idft_coeff xs n) (Cpow (omega N) (n * m)))
               (fun n => Cmul (Cmul (Cinject_Q (1 # Pos.of_nat N))
                                    (csum N (fun l => Cmul (nth_C xs l)
                                                           (Cpow (omega N) (N * l - n * l)))))
                              (Cpow (omega N) (n * m)))).
    2: { intros n Hn. unfold idft_coeff. fold N. reflexivity. }
    (* Step 3: factor out [inv_N], distribute [Cmul] into the inner csum. *)
    set (inv_N := Cinject_Q (1 # Pos.of_nat N)).
    rewrite (csum_ext N
               (fun n => Cmul (Cmul inv_N
                                    (csum N (fun l => Cmul (nth_C xs l)
                                                           (Cpow (omega N) (N * l - n * l)))))
                              (Cpow (omega N) (n * m)))
               (fun n => Cmul inv_N
                              (csum N (fun l => Cmul (Cmul (nth_C xs l)
                                                           (Cpow (omega N) (N * l - n * l)))
                                                     (Cpow (omega N) (n * m)))))).
    2: { intros n Hn.
         rewrite <- Cmul_assoc_eq.
         f_equal. apply csum_Cmul_r. }
    (* Step 4: factor [inv_N] out of the outer csum. *)
    rewrite <- csum_Cmul_l.
    (* Step 5: swap the sums. *)
    rewrite csum_swap.
    (* Step 6: simplify each inner [n]-sum: pull [xs[l]] out, combine ω-powers. *)
    rewrite (csum_ext N
               (fun l => csum N (fun n => Cmul (Cmul (nth_C xs l)
                                                     (Cpow (omega N) (N * l - n * l)))
                                               (Cpow (omega N) (n * m))))
               (fun l => Cmul (nth_C xs l)
                              (csum N (fun n => Cpow (omega N) ((N - n) * l + n * m))))).
    2: { intros l Hl.
         rewrite csum_Cmul_l.
         apply csum_ext.
         intros n Hn.
         apply CComplex_eq.
         apply (CComplex_req_trans _
                  (Cmul (nth_C xs l) (Cmul (Cpow (omega N) (N * l - n * l))
                                           (Cpow (omega N) (n * m))))).
         { symmetry. apply Cmul_assoc_req. }
         apply Cmul_Proper; [reflexivity|].
         (* Goal: Cmul (ω^(N*l - n*l)) (ω^(n*m)) ~~C ω^((N-n)*l + n*m).
            Replace exponent of RHS to match Cpow_add of LHS. *)
         assert (Hnl : (n * l <= N * l)%nat) by (apply PeanoNat.Nat.mul_le_mono_r; lia).
         replace ((N - n) * l + n * m)%nat with ((N * l - n * l) + n * m)%nat
           by (rewrite PeanoNat.Nat.mul_sub_distr_r; lia).
         rewrite Cpow_add. reflexivity. }
    (* Step 7: split outer csum at [l = m]. *)
    rewrite (csum_select N m
               (fun l => Cmul (nth_C xs l)
                              (csum N (fun n => Cpow (omega N) ((N - n) * l + n * m))))
               Hm).
    2: { intros l Hl Hneq.
         (* For l ≠ m, the inner csum is C0.  Case split on [l <= m] vs [l > m]. *)
         destruct (PeanoNat.Nat.le_gt_cases l m) as [Hlem | Hlgm].
         - (* l ≤ m: rewrite (N-n)*l + n*m = n*(m-l) + N*l. *)
           rewrite (csum_ext N
                      (fun n => Cpow (omega N) ((N - n) * l + n * m))
                      (fun n => Cpow (omega N) (n * (m - l) + N * l))).
           2: { intros n Hn. f_equal.
                assert (Hnl : (n * l <= N * l)%nat) by (apply PeanoNat.Nat.mul_le_mono_r; lia).
                assert (Hnml : (n * l <= n * m)%nat) by (apply PeanoNat.Nat.mul_le_mono_l; exact Hlem).
                rewrite PeanoNat.Nat.mul_sub_distr_r.
                rewrite PeanoNat.Nat.mul_sub_distr_l.
                lia. }
           rewrite (csum_ext N
                      (fun n => Cpow (omega N) (n * (m - l) + N * l))
                      (fun n => Cpow (omega N) (n * (m - l)))).
           2: { intros n _. apply omega_pow_period_add. exact HNne. }
           assert (Hmlmod : (m - l) mod N <> 0%nat).
           { intro Hmod.
             apply Hneq.
             assert (HmlN : (m - l < N)%nat) by lia.
             destruct (m - l)%nat eqn:E.
             - lia.
             - rewrite (PeanoNat.Nat.mod_small _ N) in Hmod by lia. discriminate. }
           rewrite (csum_omega_nonzero N (m - l) HNne Hmlmod).
           apply CComplex_eq. destruct (nth_C xs l) as [a b].
           unfold CComplex_req, Cmul, C0; simpl. split; ring.
         - (* l > m: rewrite (N-n)*l + n*m = (N-n)*(l-m) + N*m. *)
           rewrite (csum_ext N
                      (fun n => Cpow (omega N) ((N - n) * l + n * m))
                      (fun n => Cpow (omega N) ((N - n) * (l - m) + N * m))).
           2: { intros n Hn. f_equal.
                assert (HNn : (N - n <= N)%nat) by lia.
                assert (Hbnd1 : ((N - n) * m <= N * m)%nat).
                { apply PeanoNat.Nat.mul_le_mono_r; exact HNn. }
                assert (Hbnd2 : ((N - n) * m <= (N - n) * l)%nat).
                { apply PeanoNat.Nat.mul_le_mono_l; lia. }
                rewrite PeanoNat.Nat.mul_sub_distr_l.
                rewrite PeanoNat.Nat.mul_sub_distr_r.
                lia. }
           rewrite (csum_ext N
                      (fun n => Cpow (omega N) ((N - n) * (l - m) + N * m))
                      (fun n => Cpow (omega N) ((N - n) * (l - m)))).
           2: { intros n _. apply omega_pow_period_add. exact HNne. }
           rewrite (csum_omega_reverse N (l - m) HNne).
           assert (Hlmmod : (l - m) mod N <> 0%nat).
           { intro Hmod.
             apply Hneq.
             assert (HlmN : (l - m < N)%nat) by lia.
             destruct (l - m)%nat eqn:E.
             - lia.
             - rewrite (PeanoNat.Nat.mod_small _ N) in Hmod by lia. discriminate. }
           rewrite (csum_omega_nonzero N (l - m) HNne Hlmmod).
           apply CComplex_eq. destruct (nth_C xs l) as [a b].
           unfold CComplex_req, Cmul, C0; simpl. split; ring. }
    (* Step 8: at [l = m], the inner sum equals N. *)
    rewrite (csum_ext N
               (fun n => Cpow (omega N) ((N - n) * m + n * m))
               (fun n => Cpow (omega N) (N * m))).
    2: { intros n Hn. f_equal.
         assert (Hnm : (n * m <= N * m)%nat) by (apply PeanoNat.Nat.mul_le_mono_r; lia).
         rewrite PeanoNat.Nat.mul_sub_distr_r. lia. }
    (* Each summand is [ω^(N*m) = (ω^N)^m = C1]. *)
    rewrite (csum_ext N
               (fun _ => Cpow (omega N) (N * m))
               (fun _ => C1)).
    2: { intros _ _.
         rewrite (PeanoNat.Nat.mul_comm N m).
         rewrite Cpow_mul.
         rewrite (omega_pow N HNne).
         apply Cpow_C1. }
    (* Convert [csum N (fun _ => C1)] to [Cinject_Q (Z.of_nat N # 1) * C1]
       via [csum_omega_zero] applied with [k = N] (then each term
       [ω^(j*N) = C1]). *)
    rewrite <- (csum_ext N
                  (fun j => Cpow (omega N) (j * N))
                  (fun _ => C1)).
    2: { intros j _.
         rewrite Cpow_mul.
         rewrite (omega_pow N HNne).
         apply Cpow_C1. }
    assert (HmodNN : (N mod N = 0)%nat) by apply PeanoNat.Nat.Div0.mod_same.
    rewrite (csum_omega_zero N N HNne HmodNN).
    (* Goal: Cmul inv_N (Cmul xs[m] (Cmul (Cinject_Q (Z.of_nat N # 1)) C1)) = nth_C xs m *)
    apply CComplex_eq.
    apply (CComplex_req_trans _
             (Cmul inv_N (Cmul (nth_C xs m) (Cinject_Q (Z.of_nat N # 1%positive))))).
    { apply Cmul_Proper; [reflexivity|].
      apply Cmul_Proper; [reflexivity|]. apply Cmul_C1_r_req. }
    apply (CComplex_req_trans _
             (Cmul (Cmul inv_N (Cinject_Q (Z.of_nat N # 1%positive))) (nth_C xs m))).
    { apply (CComplex_req_trans _
               (Cmul inv_N (Cmul (Cinject_Q (Z.of_nat N # 1%positive)) (nth_C xs m)))).
      - apply Cmul_Proper; [reflexivity|]. apply Cmul_comm_req.
      - apply Cmul_assoc_req. }
    unfold inv_N. rewrite (Cinject_Q_inv_N_mul_N N HNne).
    apply Cmul_C1_l_req.
Qed.

(** ** Plancherel (Parseval) identity *)

(** The DFT is a (scaled) isometry:
    Σ_n |x_n|² = (1/N) Σ_k |X_k|² *)

Definition Cmod_sq (z : CComplex) : CReal :=
  re z * re z + im z * im z.

Definition seq_energy (xs : list CComplex) : CReal :=
  List.fold_left (fun acc x => acc + Cmod_sq x) xs 0.

Axiom plancherel : forall (xs : list CComplex), length xs <> 0%nat ->
    seq_energy xs =
    inject_Q (1 # Pos.of_nat (length xs)) * seq_energy (dft xs).

(** ** Convolution theorem *)

(** Pointwise product in frequency space ↔ cyclic convolution in signal space.
    For xs, ys of length N, the cyclic convolution is:
        (xs ⊛ ys)_n = Σ_{m=0}^{N-1}  xs[m] · ys[(n-m) mod N]  *)

Definition cyclic_conv (xs ys : list CComplex) : list CComplex :=
  let N := length xs in
  List.map
    (fun n => csum N (fun m =>
       Cmul (nth_C xs m) (nth_C ys ((n + N - m mod N) mod N))))
    (List.seq 0 N).

(** Pointwise product of two lists. *)
Definition pointwise_mul (Xs Ys : list CComplex) : list CComplex :=
  List.map (fun '(x, y) => Cmul x y) (List.combine Xs Ys).

Axiom convolution_theorem : forall (xs ys : list CComplex),
    length xs = length ys ->
    dft (cyclic_conv xs ys) = pointwise_mul (dft xs) (dft ys).

(** ** Mode truncation (low-pass filter) *)

(** Keep only the first K_max frequency modes (the low-frequency content). *)
Definition truncate_modes (K_max : nat) (Xs : list CComplex) : list CComplex :=
  List.firstn K_max Xs.

(** Zero-pad back to length N after truncation. *)
Definition pad_to (N : nat) (Xs : list CComplex) : list CComplex :=
  Xs ++ List.repeat C0 (N - length Xs).

(** Truncating the leading [K] entries of a list, padding with zeros to
    length [N], then truncating to [K] again is the identity on the
    leading [K] entries.  Pure list lemma, no complex algebra used. *)
Lemma firstn_pad_firstn_idem : forall (K N : nat) (xs : list CComplex),
    (K <= N)%nat -> length xs = N ->
    List.firstn K (pad_to N (List.firstn K xs)) =
    List.firstn K xs.
Proof.
  intros K N xs HKN Hxs.
  unfold pad_to.
  (* length (firstn K xs) = K, since K <= length xs = N. *)
  assert (HlenK : length (List.firstn K xs) = K).
  { apply List.firstn_length_le. lia. }
  rewrite List.firstn_app, HlenK.
  (* Goal: firstn K (firstn K xs) ++ firstn (K - K) (repeat C0 _) = firstn K xs *)
  rewrite PeanoNat.Nat.sub_diag, List.firstn_O, List.app_nil_r.
  (* Goal: firstn K (firstn K xs) = firstn K xs *)
  apply List.firstn_all2. rewrite HlenK. lia.
Qed.

(** Round-trip: truncate to K_max then pad back to N. *)
Definition low_pass (N K_max : nat) (Xs : list CComplex) : list CComplex :=
  pad_to N (truncate_modes K_max Xs).

(** A mode-K representation retains the leading K DFT coefficients. *)
Definition spectral_proj (K_max : nat) (xs : list CComplex) : list CComplex :=
  idft (low_pass (length xs) K_max (dft xs)).

(** Length of [dft]: the DFT of a length-[N] list has length [N]. *)
Lemma dft_length : forall (xs : list CComplex),
    length (dft xs) = length xs.
Proof.
  intro xs. unfold dft. rewrite List.map_length, List.seq_length. reflexivity.
Qed.

(** Length of [idft]: same. *)
Lemma idft_length : forall (xs : list CComplex),
    length (idft xs) = length xs.
Proof.
  intro xs. unfold idft. rewrite List.map_length, List.seq_length. reflexivity.
Qed.

(** Length of [pad_to]: when [length xs <= N], padding gives length [N]. *)
Lemma pad_to_length : forall (N : nat) (xs : list CComplex),
    (length xs <= N)%nat -> length (pad_to N xs) = N.
Proof.
  intros N xs HlenN. unfold pad_to.
  rewrite List.app_length, List.repeat_length. lia.
Qed.

(** Spectral projection is idempotent when K_max ≤ N.

    Proof structure:
      spectral_proj K (spectral_proj K xs)
      = idft (pad_to N (firstn K (dft (idft (pad_to N (firstn K (dft xs)))))))
      = idft (pad_to N (firstn K (pad_to N (firstn K (dft xs)))))    [dft_idft_inv]
      = idft (pad_to N (firstn K (dft xs)))                          [firstn_pad_firstn_idem
                                                                      + pad_to of same firstn]
      = spectral_proj K xs.

    The middle step uses [firstn_pad_firstn_idem] to collapse the
    inner [firstn K (pad_to N (firstn K _))] back to [firstn K _]. *)
Theorem spectral_proj_idem : forall (K_max : nat) (xs : list CComplex),
    (K_max <= length xs)%nat ->
    spectral_proj K_max (spectral_proj K_max xs) = spectral_proj K_max xs.
Proof.
  intros K xs HKlen.
  unfold spectral_proj at 1.
  (* The argument list to the outer spectral_proj is [spectral_proj K xs = idft Ys]
     where [Ys = low_pass N K (dft xs)] has length [N].  So
     [length (spectral_proj K xs) = length Ys = N]. *)
  set (N := length xs).
  fold N.
  set (Ys := low_pass N K (dft xs)).
  assert (HlenYs : length Ys = N).
  { unfold Ys, low_pass.
    apply pad_to_length.
    unfold truncate_modes.
    rewrite List.firstn_length, dft_length. fold N. lia. }
  assert (HlenSP : length (spectral_proj K xs) = N).
  { unfold spectral_proj. rewrite idft_length. exact HlenYs. }
  (* Goal: idft (low_pass (length (spectral_proj K xs)) K (dft (spectral_proj K xs)))
           = spectral_proj K xs *)
  rewrite HlenSP.
  unfold spectral_proj at 1.
  fold N.
  fold Ys.
  (* Goal: idft (low_pass N K (dft (idft Ys))) = idft Ys *)
  rewrite (dft_idft_inv Ys).
  (* Goal: idft (low_pass N K Ys) = idft Ys *)
  unfold low_pass at 1.
  unfold truncate_modes at 1.
  unfold Ys at 1, low_pass, truncate_modes.
  (* Goal: idft (pad_to N (firstn K (pad_to N (firstn K (dft xs))))) = idft (pad_to N (firstn K (dft xs))) *)
  f_equal.
  (* Apply firstn_pad_firstn_idem with K, N, (dft xs).  Need length (dft xs) = N. *)
  rewrite (firstn_pad_firstn_idem K N (dft xs) HKlen).
  - reflexivity.
  - rewrite dft_length. reflexivity.
Qed.
