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

From Stdlib Require Import List Arith.
From Stdlib Require Import QArith ZArith.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyRealsMult.
Import ListNotations.

From CAG Require Import Complex.

Local Open Scope CReal_scope.

(** ** Complex exponential  e^{iθ} *)

(** We axiomatize exp_i : ℝ → ℂ satisfying Euler's formula.
    A full constructive definition would require sin and cos series. *)

(* CAG zero-dependent Parameter exp_i theories/NeuralOp/DFT.v:30 BEGIN
Parameter exp_i : CReal -> CComplex.
   CAG zero-dependent Parameter exp_i theories/NeuralOp/DFT.v:30 END *)

(* CAG zero-dependent Admitted exp_i_zero theories/NeuralOp/DFT.v:32 BEGIN
Theorem exp_i_zero    : exp_i 0 = C1.
Proof. admit. Admitted.
   CAG zero-dependent Admitted exp_i_zero theories/NeuralOp/DFT.v:32 END *)
(* CAG zero-dependent Admitted exp_i_add theories/NeuralOp/DFT.v:34 BEGIN
Theorem exp_i_add     : forall θ φ, exp_i (θ + φ) = Cmul (exp_i θ) (exp_i φ).
Proof. admit. Admitted.
   CAG zero-dependent Admitted exp_i_add theories/NeuralOp/DFT.v:34 END *)
(* CAG zero-dependent Admitted exp_i_neg theories/NeuralOp/DFT.v:36 BEGIN
Theorem exp_i_neg     : forall θ,   exp_i (- θ)   = mkC (re (exp_i θ)) (- im (exp_i θ)).
Proof. admit. Admitted.
   CAG zero-dependent Admitted exp_i_neg theories/NeuralOp/DFT.v:36 END *)
(* CAG zero-dependent Admitted exp_i_norm_sq theories/NeuralOp/DFT.v:39 BEGIN
Theorem exp_i_norm_sq : forall θ,
    re (exp_i θ) * re (exp_i θ) + im (exp_i θ) * im (exp_i θ) = 1.
Proof. admit. Admitted.
   CAG zero-dependent Admitted exp_i_norm_sq theories/NeuralOp/DFT.v:39 END *)

(** π, already axiomatized in ComplexAnalysis.v — redeclare for self-containment. *)
(* CAG zero-dependent Parameter pi_R theories/NeuralOp/DFT.v:51 BEGIN
Parameter pi_R : CReal.
   CAG zero-dependent Parameter pi_R theories/NeuralOp/DFT.v:51 END *)
(* CAG zero-dependent Admitted pi_pos theories/NeuralOp/DFT.v:44 BEGIN
Theorem pi_pos : 0 < pi_R.
Proof. admit. Admitted.
   CAG zero-dependent Admitted pi_pos theories/NeuralOp/DFT.v:44 END *)

(** N-th primitive root of unity: ω_N = e^{−2πi/N}. *)
(* CAG zero-dependent Definition omega theories/NeuralOp/DFT.v:58 BEGIN
Definition omega (N : nat) : CComplex :=
  (* e^{-2πi/N} = exp_i(-2π · (1/N)).  We write (1/N) as the rational 1#N. *)
  exp_i (- (inject_Q (2 # 1) * pi_R * inject_Q (1 # Pos.of_nat N))).
   CAG zero-dependent Definition omega theories/NeuralOp/DFT.v:58 END *)

(** ω_N^N = 1. *)
(* CAG zero-dependent Admitted omega_pow theories/NeuralOp/DFT.v:53 BEGIN
Lemma omega_pow (N : nat) (hN : N <> 0%nat) : Cpow (omega N) N = C1.
Proof. Admitted.
   CAG zero-dependent Admitted omega_pow theories/NeuralOp/DFT.v:53 END *)

(** Geometric sum: Σ_{n=0}^{N−1} ω_N^{nk} = N·δ_{k,0 mod N}. *)
(* CAG zero-dependent Admitted geometric_sum_zero theories/NeuralOp/DFT.v:62 BEGIN
Lemma geometric_sum_zero (N k : nat) (hN : N <> 0%nat) (hk : k mod N = 0%nat) :
    (fix sumω n acc :=
       match n with
       | O => acc
       | S n' => sumω n' (Cadd acc (Cpow (omega N) (n' * k)))
       end) N C0 = Cmul (Cinject_Q (Z.of_nat N # 1%positive)) C1.
Proof. Admitted.
   CAG zero-dependent Admitted geometric_sum_zero theories/NeuralOp/DFT.v:62 END *)

(* CAG zero-dependent Admitted geometric_sum_nonzero theories/NeuralOp/DFT.v:70 BEGIN
Lemma geometric_sum_nonzero (N k : nat) (hN : N <> 0%nat) (hk : k mod N <> 0%nat) :
    (fix sumω n acc :=
       match n with
       | O => acc
       | S n' => sumω n' (Cadd acc (Cpow (omega N) (n' * k)))
       end) N C0 = C0.
Proof. Admitted.
   CAG zero-dependent Admitted geometric_sum_nonzero theories/NeuralOp/DFT.v:70 END *)

(** ** Finite sums over ℂ *)

(** Sum a function f : {0..N-1} → ℂ. *)
Fixpoint csum (N : nat) (f : nat -> CComplex) : CComplex :=
  match N with
  | O    => C0
  | S n  => Cadd (csum n f) (f n)
  end.

(* CAG zero-dependent Admitted csum_zero theories/NeuralOp/DFT.v:83 BEGIN
Lemma csum_zero (N : nat) (f : nat -> CComplex) :
    (forall k : nat, (k < N)%nat -> f k = C0) -> csum N f = C0.
Proof. Admitted.
   CAG zero-dependent Admitted csum_zero theories/NeuralOp/DFT.v:83 END *)

(* CAG zero-dependent Admitted csum_linear theories/NeuralOp/DFT.v:88 BEGIN
Lemma csum_linear (N : nat) (f g : nat -> CComplex) (c : CComplex) :
    csum N (fun k => Cadd (f k) (Cmul c (g k)))
    = Cadd (csum N f) (Cmul c (csum N g)).
Proof. Admitted.
   CAG zero-dependent Admitted csum_linear theories/NeuralOp/DFT.v:88 END *)

(** ** Safe list indexing *)

Definition nth_C (xs : list CComplex) (n : nat) : CComplex :=
  nth n xs C0.

(** ** Discrete Fourier Transform *)

(** DFT of a sequence xs of length N:
    X_k = Σ_{n=0}^{N-1}  xs[n] · ω_N^{n·k} *)
(* CAG zero-dependent Definition dft_coeff theories/NeuralOp/DFT.v:120 BEGIN
Definition dft_coeff (xs : list CComplex) (k : nat) : CComplex :=
  let N := length xs in
  csum N (fun n => Cmul (nth_C xs n) (Cpow (omega N) (n * k))).
   CAG zero-dependent Definition dft_coeff theories/NeuralOp/DFT.v:120 END *)

(** The full DFT: list of N coefficients X_0, …, X_{N-1}. *)
(* CAG zero-dependent Definition dft theories/NeuralOp/DFT.v:125 BEGIN
Definition dft (xs : list CComplex) : list CComplex :=
  List.map (dft_coeff xs) (List.seq 0 (length xs)).
   CAG zero-dependent Definition dft theories/NeuralOp/DFT.v:125 END *)

(** ** Inverse DFT *)

(** IDFT synthesis formula:
    x_n = (1/N) Σ_{k=0}^{N-1}  X_k · ω_N^{−n·k} *)
(* CAG zero-dependent Definition idft_coeff theories/NeuralOp/DFT.v:132 BEGIN
Definition idft_coeff (Xs : list CComplex) (n : nat) : CComplex :=
  let N := length Xs in
  let inv_N := Cinject_Q (1 # Pos.of_nat N) in
  Cmul inv_N (csum N (fun k => Cmul (nth_C Xs k) (Cpow (omega N) (N * k - n * k)))).
   CAG zero-dependent Definition idft_coeff theories/NeuralOp/DFT.v:132 END *)
  (* Using ω_N^{−nk} = ω_N^{(N-n)k} for integer arithmetic. *)

(* CAG zero-dependent Definition idft theories/NeuralOp/DFT.v:138 BEGIN
Definition idft (Xs : list CComplex) : list CComplex :=
  List.map (idft_coeff Xs) (List.seq 0 (length Xs)).
   CAG zero-dependent Definition idft theories/NeuralOp/DFT.v:138 END *)

(** ** Fundamental theorem: IDFT ∘ DFT = id *)

(* CAG zero-dependent Theorem idft_dft_inv theories/NeuralOp/DFT.v:143 BEGIN
Theorem idft_dft_inv (xs : list CComplex) :
    idft (dft xs) = xs.
Proof.
  Admitted.
   CAG zero-dependent Theorem idft_dft_inv theories/NeuralOp/DFT.v:143 END *)
  (* Proof: substitute definitions, interchange sums, apply geometric_sum_zero
     for k ≡ 0 and geometric_sum_nonzero for k ≢ 0 mod N. *)

(** ** Plancherel (Parseval) identity *)

(** The DFT is a (scaled) isometry:
    Σ_n |x_n|² = (1/N) Σ_k |X_k|² *)

Definition Cmod_sq (z : CComplex) : CReal :=
  re z * re z + im z * im z.

Definition seq_energy (xs : list CComplex) : CReal :=
  List.fold_left (fun acc x => acc + Cmod_sq x) xs 0.

(* CAG zero-dependent Admitted plancherel theories/NeuralOp/DFT.v:142 BEGIN
Theorem plancherel (xs : list CComplex) (hN : length xs <> 0%nat) :
    seq_energy xs =
    inject_Q (1 # Pos.of_nat (length xs)) * seq_energy (dft xs).
Proof.
  Admitted.
   CAG zero-dependent Admitted plancherel theories/NeuralOp/DFT.v:142 END *)

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

(* CAG zero-dependent Admitted convolution_theorem theories/NeuralOp/DFT.v:165 BEGIN
Theorem convolution_theorem (xs ys : list CComplex)
    (hlen : length xs = length ys) :
    dft (cyclic_conv xs ys) = pointwise_mul (dft xs) (dft ys).
Proof.
  Admitted.
   CAG zero-dependent Admitted convolution_theorem theories/NeuralOp/DFT.v:165 END *)

(** ** Mode truncation (low-pass filter) *)

(** Keep only the first K_max frequency modes (the low-frequency content). *)
Definition truncate_modes (K_max : nat) (Xs : list CComplex) : list CComplex :=
  List.firstn K_max Xs.

(** Zero-pad back to length N after truncation. *)
Definition pad_to (N : nat) (Xs : list CComplex) : list CComplex :=
  Xs ++ List.repeat C0 (N - length Xs).

(** Round-trip: truncate to K_max then pad back to N. *)
Definition low_pass (N K_max : nat) (Xs : list CComplex) : list CComplex :=
  pad_to N (truncate_modes K_max Xs).

(** A mode-K representation retains the leading K DFT coefficients. *)
(* CAG zero-dependent Definition spectral_proj theories/NeuralOp/DFT.v:209 BEGIN
Definition spectral_proj (K_max : nat) (xs : list CComplex) : list CComplex :=
  idft (low_pass (length xs) K_max (dft xs)).
   CAG zero-dependent Definition spectral_proj theories/NeuralOp/DFT.v:209 END *)

(** Spectral projection is idempotent when K_max ≤ N. *)
(* CAG zero-dependent Admitted spectral_proj_idem theories/NeuralOp/DFT.v:190 BEGIN
Lemma spectral_proj_idem (K_max : nat) (xs : list CComplex)
    (hK : (K_max <= length xs)%nat) :
    spectral_proj K_max (spectral_proj K_max xs) = spectral_proj K_max xs.
Proof.
  Admitted.
   CAG zero-dependent Admitted spectral_proj_idem theories/NeuralOp/DFT.v:190 END *)
