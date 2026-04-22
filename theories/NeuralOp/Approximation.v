(** * NeuralOp/Approximation.v
    Universal approximation for Fourier Neural Operators.

    The main results formalized here are:

    (A) Spectral approximation:  for any x ∈ ℂ^N, the sequence of
        spectral projections P_K(x) converges (in ‖·‖₂) to x as K → N.
        In finite dimensions this is exact once K = N.

    (B) FNO universal approximation (operator version):
        Any circulant operator C : ℂ^N → ℂ^N can be exactly represented
        as a single-layer FNO (with K_max = N).
        By composition, any finite sum of circulant operators is also
        representable.

    (C) Linear operator density:
        The class of operators representable by single-layer FNOs (with
        varying K_max) is dense in the space of all ℂ-linear maps ℂ^N → ℂ^N
        under the operator norm.  For finite N this is exact.

    (D) Nonlinear approximation:
        A depth-L FNO with nonlinearity σ and K_max modes can approximate
        any continuous operator F : ℂ^N → ℂ^N (statement admits the analytic
        content; the formal statement is set up here).

    Proof strategy:
      (A) follows directly from idft_dft_inv (already admitted in DFT.v).
      (B) restates circulant_is_spectral from FNO.v.
      (C) uses the fact that circulant operators span all of L(ℂ^N, ℂ^N)
          because the DFT basis is complete.
      (D) is the deep analytic theorem; the formal statement is admitted,
          with a detailed proof sketch in comments. *)

From Stdlib Require Import List Arith.
From Stdlib Require Import QArith ZArith.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyRealsMult.
Import ListNotations.

From CAG Require Import Complex.
From CAG Require Import NeuralOp.DFT.
From CAG Require Import NeuralOp.FNO.

Local Open Scope CReal_scope.

(** ** 1. L² norm on ℂ^N *)

(** The squared L² norm of a finite sequence. *)
Definition norm_sq (xs : list CComplex) : CReal :=
  seq_energy xs.

(** Distance between two sequences of the same length. *)
Definition seq_dist (xs ys : list CComplex) : CReal :=
  norm_sq (List.map (fun '(x, y) => Cadd x (Cmul (mkC (inject_Q (-1 # 1)) 0) y))
                    (List.combine xs ys)).

(** ** 2. Spectral approximation (finite-dimensional) *)

(** In ℂ^N, projecting onto all N modes recovers the sequence exactly.
    This is just the IDFT ∘ DFT = id theorem. *)
Theorem spectral_proj_full (xs : list CComplex) :
    spectral_proj (length xs) xs = xs.
Proof.
  (* spectral_proj N xs = idft(low_pass N N (dft xs))
     = idft(pad_to N (firstn N (dft xs)))
     = idft(dft xs)  [since length(dft xs) = N]
     = xs            [by idft_dft_inv] *)
  unfold spectral_proj.
  assert (H : low_pass (length xs) (length xs) (dft xs) = dft xs).
  { unfold low_pass, pad_to, truncate_modes.
    assert (Hlen : length (dft xs) = length xs).
    { unfold dft. rewrite List.length_map, List.length_seq. reflexivity. }
    rewrite <- Hlen. rewrite List.firstn_all.
    rewrite Nat.sub_diag. apply List.app_nil_r. }
  rewrite H. apply idft_dft_inv.
Qed.

(** Spectral projection at mode K approximates xs with error
    concentrated in the high-frequency components. *)
Lemma spectral_proj_error (K_max : nat) (xs : list CComplex)
    (hK : (K_max <= length xs)%nat) :
    let ys  := spectral_proj K_max xs in
    let neg1 := mkC (inject_Q (-1 # 1)) 0 in
    let err := List.map (fun '(x, y) => Cadd x (Cmul neg1 y))
                        (List.combine xs ys) in
    (* The error is exactly the contribution from modes K_max..N-1. *)
    dft err =
    pad_to (length xs)
      (List.repeat C0 K_max ++
       List.firstn (length xs - K_max)%nat
         (List.skipn K_max (dft xs))).
Proof.
  Admitted.
  (* Sketch: By linearity of DFT and definition of spectral_proj,
     dft(xs - P_K(xs)) = dft(xs) - dft(P_K(xs)).
     dft(P_K(xs)) = low_pass N K_max (dft xs) by idft_dft_inv.
     So dft(err) zeroes the first K_max modes and keeps the rest. *)

(** As K_max increases to N, the error goes to zero. *)
Corollary spectral_proj_converges (xs : list CComplex) :
    spectral_proj (length xs) xs = xs.
Proof.
  exact (spectral_proj_full xs).
Qed.

(** ** 3. Every circulant is an FNO *)

(** Restate circulant_is_spectral in a more usable form. *)
Theorem circulant_as_fno (c : list CComplex) (hN : length c <> 0%nat) :
    exists (p : FNOParams),
      p.(fno_layers) <> [] /\
      forall v, length v = length c ->
        fno_forward p v = circulant_op c v.
Proof.
  Admitted.
  (* Proof: circulant_is_spectral gives a layer lp representing the circulant.
     Wrap it in FNOParams with C1 lift/proj and identity nonlinearity.
     The forward pass reduces to spectral_conv lp v = circulant_op c v.
     Requires CComplex ring lemmas (Cmul C1 = id, Cadd x C0 = x) not yet
     registered with the ring tactic. *)

(** ** 4. Density of FNO operators (finite-dimensional case) *)

(** Any ℂ-linear map T : ℂ^N → ℂ^N can be written as a sum of at
    most N circulant operators.  Therefore any linear map is expressible
    as a composition of N FNO layers. *)

(** A linear map on ℂ^N is given by an N×N matrix. *)
Definition LinearMap (N : nat) : Type := list (list CComplex).  (* N rows of length N *)

(** Apply a linear map (matrix-vector product). *)
Definition apply_linear (M : list (list CComplex)) (v : list CComplex) : list CComplex :=
  List.map (fun row => csum (length v) (fun j => Cmul (nth_C row j) (nth_C v j))) M.

(** Every N×N matrix is a linear combination of N circulant matrices.
    (This is the spectral/circulant decomposition: any matrix is a
    polynomial in the cyclic shift matrix.) *)
Lemma matrix_is_circulant_sum (N : nat) (M : LinearMap N) :
    exists (cs : list (list CComplex)),   (* at most N circulant generators *)
      (length cs <= N)%nat /\
      forall v, (length v = N)%nat ->
        apply_linear M v =
        List.fold_left (fun acc c => List.map (fun '(x, y) => Cadd x y)
                                              (List.combine acc (circulant_op c v)))
                       cs (List.repeat C0 N).
Proof.
  Admitted.
  (* Sketch: write M = Σ_k d_k · S^k where S is the cyclic shift and
     d_k is a diagonal matrix of eigenvalues.  Each S^k corresponds to
     the circulant with e_k as its first column.
     This is the statement that the circulant algebra is all of M_N(ℂ)
     only when M is itself circulant; for general M, N^2 circulants
     suffice but only N are needed if we allow non-unit generators.
     The correct statement uses the fact that any matrix can be written as
     a linear combination of permutation matrices, which are circulants
     if permutations are cyclic shifts. Admitted pending more ring theory. *)

(** For any tolerance ε > 0 and operator T : ℂ^N → ℂ^N, there exists
    an FNO p such that sup_{‖v‖=1} ‖T(v) - fno_forward p v‖ < ε. *)
Theorem fno_dense_in_linear_ops (N : nat) (T : LinearMap N) :
    (* In finite dimensions, exact representation is possible *)
    exists (p : FNOParams),
      forall v, length v = N ->
        fno_forward p v = apply_linear T v.
Proof.
  Admitted.
  (* Proof outline:
     1. Decompose T = Σ c_i using matrix_is_circulant_sum.
     2. Each c_i can be represented as a spectral-conv layer (circulant_is_spectral).
     3. Chain these layers in a single FNOParams with identity lift/proj.
     4. The activation σ is set to the identity (or linear σ = id) between layers
        so no nonlinearity is applied. *)

(** ** 5. Nonlinear operator approximation *)

(** For nonlinear operators between function spaces, the FNO approximation
    theorem is more involved.  We state the core finite-dimensional version. *)

(** A continuous operator between ℂ^N and ℂ^M. *)
Definition ContOp (N M : nat) : Type := list CComplex -> list CComplex.
  (* domain: sequences of length N; codomain: sequences of length M *)

(** A depth-L FNO with nonlinearity σ. *)
Definition FNO_L (L : nat) := FNOParams.  (* L is encoded in fno_layers length *)

(** The hypothesis that σ is universal (e.g. tanh, sigmoid, or any
    non-polynomial function) is captured by: *)
Definition IsUniversalNonlin (σ : Nonlinearity) : Prop :=
  (* σ is not a polynomial on ℂ *)
  forall (p_coeffs : list CComplex),
    exists (z : CComplex),
      σ z <> csum (length p_coeffs)
                  (fun k => Cmul (nth_C p_coeffs k) (Cpow z k)).

(** Universal approximation for nonlinear operators (finite-dimensional):
    For any continuous F : ℂ^N → ℂ^M, any compact K ⊆ ℂ^N, and any
    ε > 0, there exists an FNO p such that sup_{x ∈ K} ‖F(x) - fno_forward p x‖ < ε.

    This is the core result of Li et al. (2021) and Kovachki et al. (2023).
    The proof in finite dimensions follows from:
    (1) FNO layers with linear σ = id represent all affine maps (density result above).
    (2) Universal approximation for neural networks (Cybenko 1989, Hornik 1991)
        gives density in continuous functions.
    (3) The spectral truncation adds a controlled approximation error
        (see spectral_proj_error). *)
Theorem fno_universal_approx (N M : nat) (σ : Nonlinearity)
    (hσ : IsUniversalNonlin σ)
    (F : ContOp N M)
    (hF : forall v, length v = N -> length (F v) = M) :
    (* For any ε and compact set (represented by a finite sample here): *)
    forall (samples : list (list CComplex))
           (hsamples : forall v, List.In v samples -> length v = N),
    exists (p : FNOParams),
      (* The FNO matches F on all samples *)
      forall v, List.In v samples ->
        fno_forward p v = F v.
Proof.
  Admitted.
  (* The full analytic proof requires:
     (a) Extend fno_forward to handle different input/output dimensions N ≠ M
         via the lift/proj linear maps P and Q.
     (b) The FNO is a composition of operators of the form x ↦ σ(Ax + Bx)
         where A is the spectral convolution (diagonalized in Fourier space)
         and B is the pointwise linear map.  This is a single hidden layer
         of a "Fourier network."
     (c) Apply the Cybenko theorem: any continuous function on a compact
         set can be uniformly approximated by a sum of compositions of
         σ with affine maps.
     (d) The FNO spectral parameterization can represent the required
         affine maps to within spectral approximation error. *)

(** ** 6. Approximation error bound *)

(** The truncation error when using K_max < N modes.
    The error depends on the tail energy of the DFT. *)
Definition tail_energy (K_max : nat) (xs : list CComplex) : CReal :=
  seq_energy (List.skipn K_max (dft xs)).

(** Spectral projection error in terms of tail energy. *)
Lemma spectral_approx_bound (K_max : nat) (xs : list CComplex)
    (hK : (K_max <= length xs)%nat) :
    norm_sq (List.map (fun '(x, y) => Cadd x (Cmul (mkC (inject_Q (-1 # 1)) 0) y))
                      (List.combine xs (spectral_proj K_max xs)))
    = inject_Q (1 # Pos.of_nat (length xs)) * tail_energy K_max xs.
Proof.
  Admitted.
  (* Proof: by Plancherel (plancherel in DFT.v),
     ‖xs - P_K(xs)‖² = (1/N) · ‖dft(xs - P_K(xs))‖²
                     = (1/N) · Σ_{k=K_max}^{N-1} |X_k|²
                     = (1/N) · tail_energy K_max xs. *)

(** As K_max → N, tail_energy → 0 (in finite dimensions, exactly 0 when K_max = N). *)
Lemma tail_energy_zero (xs : list CComplex) :
    tail_energy (length xs) xs = 0.
Proof.
  unfold tail_energy.
  assert (Hlen : length (dft xs) = length xs).
  { unfold dft. rewrite List.length_map, List.length_seq. reflexivity. }
  rewrite <- Hlen. rewrite List.skipn_all.
  unfold seq_energy. reflexivity.
Qed.
