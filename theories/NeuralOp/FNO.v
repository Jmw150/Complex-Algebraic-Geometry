(** * NeuralOp/FNO.v
    Fourier Neural Operator architecture.

    A Fourier Neural Operator (FNO, Li et al. 2021) is a neural network
    architecture that learns operators between function spaces.  Given
    a discretized input function v : Fin N → ℂ^{d_v}, each FNO layer
    computes:

        v_{l+1}(x) = σ( K[v_l](x) + W·v_l(x) )

    where
      - K is a spectral convolution operator:
            K[v](x) = IDFT( R · (DFT v)|_{k < K_max} ++ 0 )
        with R : Fin K_max → Mat(d_v, d_v) learnable weights (one matrix
        per kept mode),
      - W : Mat(d_v, d_v) is a pointwise learnable linear transform,
      - σ : ℂ → ℂ is a fixed nonlinearity.

    For clarity the single-channel (d_v = 1) case is formalized first.
    The multi-channel generalization is stated at the end.

    The full FNO stacks L such layers:
        v_0   = P(u)             (channel-lifting projection)
        v_1   = Layer_1(v_0)
        …
        v_L   = Layer_L(v_{L-1})
        output = Q(v_L)          (channel-projection back to target dimension)
    where P and Q are pointwise linear maps. *)

From Stdlib Require Import List Arith.
From Stdlib Require Import QArith ZArith.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyAbs.
From Stdlib Require Import micromega.Lia.
Import ListNotations.

From CAG Require Import Complex.
From CAG Require Import NeuralOp.DFT.

Local Open Scope CReal_scope.

(** ** 1. Nonlinearities *)

(** A nonlinearity is any function ℂ → ℂ.  Typical choices:
    - ReLU on the real part: z ↦ max(Re z, 0) + i·Im z
    - GeLU, SiLU, tanh, etc. *)

Definition Nonlinearity := CComplex -> CComplex.

Definition relu_C : Nonlinearity :=
  fun z => mkC (CReal_max (re z) 0) (im z).

Definition tanh_C : Nonlinearity.
Proof. Admitted. (* requires real tanh *)

(** Apply a nonlinearity pointwise to a sequence. *)
Definition apply_nonlin (σ : Nonlinearity) (xs : list CComplex) : list CComplex :=
  List.map σ xs.

(** ** 2. Single-channel FNO layer (d_v = 1) *)

(** Parameters of one FNO layer (single channel):
    - [fno_weights] : spectral weights R_k ∈ ℂ for k = 0..K_max-1
    - [fno_skip]    : pointwise weight w ∈ ℂ  (W = w·Id)
    - [fno_nonlin]  : nonlinearity σ           *)

Record FNOLayerParams : Type := {
  fno_K_max   : nat;
  fno_weights : list CComplex;  (* length = K_max *)
  fno_skip    : CComplex;
  fno_nonlin  : Nonlinearity;
  fno_weights_len : length fno_weights = fno_K_max;
}.

(** Apply spectral weights to the kept modes:
    R · X_k  for k < K_max,  0 for k ≥ K_max. *)
Definition apply_weights (R Xs : list CComplex) : list CComplex :=
  pointwise_mul R Xs.

(** Spectral convolution  K[v]:
    1. DFT the input
    2. Multiply low modes by R, zero the rest
    3. IDFT back *)
Definition spectral_conv (p : FNOLayerParams) (v : list CComplex) : list CComplex :=
  let N    := length v in
  let Xfull := dft v in
  let Xlow  := truncate_modes p.(fno_K_max) Xfull in
  let Xweighted := apply_weights p.(fno_weights) Xlow in
  let Xpad  := pad_to N Xweighted in
  idft Xpad.

(** Pointwise skip connection  W[v] = fno_skip · v. *)
Definition skip_connection (p : FNOLayerParams) (v : list CComplex) : list CComplex :=
  List.map (fun x => Cmul p.(fno_skip) x) v.

(** One FNO layer:
    v_out = σ( K[v] + W[v] ) *)
Definition fno_layer (p : FNOLayerParams) (v : list CComplex) : list CComplex :=
  let Kv := spectral_conv     p v in
  let Wv := skip_connection   p v in
  apply_nonlin p.(fno_nonlin) (List.map (fun '(k, w) => Cadd k w)
                                        (List.combine Kv Wv)).

(** ** 3. Full FNO (single channel) *)

(** An FNO is a sequence of layer parameters together with a lifting
    scalar P : ℂ → ℂ and a projection scalar Q : ℂ → ℂ. *)

Record FNOParams : Type := {
  fno_lift    : CComplex;        (* P: channel lift (multiply by lift) *)
  fno_proj    : CComplex;        (* Q: channel project *)
  fno_layers  : list FNOLayerParams;
}.

(** Lifting/projection are pointwise scalar multiplications. *)
Definition lift (p : CComplex) (v : list CComplex) : list CComplex :=
  List.map (Cmul p) v.

(** Apply a list of FNO layers in sequence. *)
Fixpoint apply_layers (layers : list FNOLayerParams) (v : list CComplex)
    : list CComplex :=
  match layers with
  | []      => v
  | l :: ls => apply_layers ls (fno_layer l v)
  end.

(** Full FNO forward pass:  u ↦ Q(Layer_L(… Layer_1(P(u)) …)) *)
Definition fno_forward (p : FNOParams) (u : list CComplex) : list CComplex :=
  lift p.(fno_proj) (apply_layers p.(fno_layers) (lift p.(fno_lift) u)).

(** ** 4. Multi-channel FNO layer (d_v channels) *)

(** With d_v channels, each grid point carries a vector in ℂ^{d_v}.
    We represent this as a list of length N*d_v flattened, or equivalently
    as a list (of length N) of lists (of length d_v).
    For clarity we use the latter. *)

Definition MCSeq (dv : nat) := list (list CComplex).

(** A d_v × d_v matrix over ℂ, stored row-major. *)
Definition CMatrix (d : nat) := list (list CComplex).  (* d rows, each of length d *)

(** Multiply a d×d matrix by a d-vector. *)
Definition cmat_vec_mul (M : CMatrix 1) (v : list CComplex) : list CComplex :=
  List.map (fun row => csum (length v) (fun j => Cmul (nth_C row j) (nth_C v j))) M.

(** Multi-channel spectral weight at mode k: a d_v × d_v matrix. *)

Record MCFNOLayerParams (dv : nat) : Type := {
  mc_K_max    : nat;
  mc_weights  : list (CMatrix dv);  (* length = K_max; each CMatrix dv is dv×dv *)
  mc_skip     : CMatrix dv;         (* dv × dv pointwise weight *)
  mc_nonlin   : Nonlinearity;       (* applied componentwise *)
}.

Arguments mc_K_max   {dv}.
Arguments mc_weights {dv}.
Arguments mc_skip    {dv}.
Arguments mc_nonlin  {dv}.

(** Apply multi-channel spectral convolution.
    For each channel separately (simplified: uses channel-wise DFT).
    Full implementation requires matrix-valued Fourier modes. *)
Definition mc_spectral_conv {dv : nat} (p : MCFNOLayerParams dv)
    (vs : MCSeq dv) : MCSeq dv :=
  (* Extract each channel, DFT, multiply by mode-wise matrix weights, IDFT *)
  (* Placeholder implementation: act independently on each channel *)
  vs. (* TODO: implement full matrix-weighted spectral conv *)

(** ** 5. Equivariance and invariance properties *)

(** The spectral conv K is translation-equivariant:
    K[v(· + h)] = K[v](· + h).
    This follows because DFT diagonalizes translation. *)
Lemma spectral_conv_translation_equiv (p : FNOLayerParams)
    (v : list CComplex) (shift : nat) :
    let N  := length v in
    let sv := List.map (fun k => nth_C v ((k + shift) mod N)) (List.seq 0 N) in
    spectral_conv p sv =
    List.map (fun k => nth_C (spectral_conv p v) ((k + shift) mod N))
             (List.seq 0 N).
Proof.
  Admitted.
  (* Proof: DFT of a shifted sequence is e^{2πi k·shift/N} · DFT(v),
     multiplying by R absorbs the scalar, and IDFT undoes the shift. *)

(** The FNO preserves sequence length. *)
Lemma fno_layer_length (p : FNOLayerParams) (v : list CComplex) :
    length (fno_layer p v) = length v.
Proof.
  unfold fno_layer, apply_nonlin, skip_connection, spectral_conv.
  set (N := length v).
  (* length of dft v = N *)
  assert (Hdft : length (dft v) = N).
  { unfold dft. rewrite List.length_map, List.length_seq. reflexivity. }
  (* length of truncate_modes K_max (dft v) <= N *)
  assert (Htrunc : (length (truncate_modes p.(fno_K_max) (dft v)) <= N)%nat).
  { unfold truncate_modes. rewrite List.length_firstn. lia. }
  (* length of apply_weights (fno_weights p) (truncate_modes ...) <= N *)
  assert (Hweighted : (length (apply_weights p.(fno_weights) (truncate_modes p.(fno_K_max) (dft v))) <= N)%nat).
  { unfold apply_weights, pointwise_mul.
    rewrite List.length_map.
    pose proof (length_combine (fno_weights p) (truncate_modes p.(fno_K_max) (dft v))) as Hclen.
    lia. }
  (* length of pad_to N (...) = N *)
  assert (Hpad : length (pad_to N (apply_weights p.(fno_weights) (truncate_modes p.(fno_K_max) (dft v)))) = N).
  { unfold pad_to. rewrite List.length_app, List.repeat_length. lia. }
  (* length of idft (...) = N *)
  assert (Hidft : length (idft (pad_to N (apply_weights p.(fno_weights) (truncate_modes p.(fno_K_max) (dft v))))) = N).
  { unfold idft. rewrite List.length_map, List.length_seq. congruence. }
  (* skip_connection has length N *)
  assert (Hskip : length (List.map (fun x => Cmul p.(fno_skip) x) v) = N).
  { rewrite List.length_map. reflexivity. }
  (* combine has length min N N = N *)
  rewrite List.length_map, List.length_map.
  pose proof (List.length_combine
    (idft (pad_to N (apply_weights (fno_weights p) (truncate_modes (fno_K_max p) (dft v)))))
    (List.map (fun x => Cmul (fno_skip p) x) v)) as Hclen.
  rewrite Hidft, Hskip in Hclen.
  lia.
Qed.

Lemma apply_layers_length (layers : list FNOLayerParams) (v : list CComplex) :
    length (apply_layers layers v) = length v.
Proof.
  induction layers as [| l ls IH] in v |- *.
  - reflexivity.
  - simpl. rewrite IH, fno_layer_length. reflexivity.
Qed.

Lemma fno_forward_length (p : FNOParams) (u : list CComplex) :
    length (fno_forward p u) = length u.
Proof.
  unfold fno_forward, lift.
  rewrite List.length_map, apply_layers_length, List.length_map.
  reflexivity.
Qed.

(** ** 6. Parameterization and composition *)

(** Two FNOs can be composed: the output of one feeds the input of the next. *)
Definition fno_compose (p1 p2 : FNOParams) : FNOParams :=
  {| fno_lift   := Cmul p2.(fno_lift)   p1.(fno_proj);
     fno_proj   := p2.(fno_proj);
     fno_layers := p1.(fno_layers) ++ p2.(fno_layers); |}.

(** Composition is associative (at the level of forward passes). *)
Lemma fno_compose_assoc (p1 p2 p3 : FNOParams) (u : list CComplex) :
    fno_forward (fno_compose p1 (fno_compose p2 p3)) u =
    fno_forward (fno_compose (fno_compose p1 p2) p3) u.
Proof.
  Admitted.

(** ** 7. Density in the spectral basis *)

(** The spectral convolution with K modes is a linear map on ℂ^N.
    As K_max → N, the spectral conv recovers an arbitrary circulant operator. *)

(** A circulant operator C : ℂ^N → ℂ^N is defined by its first column c:
    (C·v)_n = Σ_m c_{(n-m) mod N} · v_m = (c ⊛ v)_n *)
Definition circulant_op (c v : list CComplex) : list CComplex :=
  cyclic_conv c v.

(** Every circulant is representable as a full-mode spectral conv. *)
Theorem circulant_is_spectral (c : list CComplex) :
    exists (p : FNOLayerParams),
      p.(fno_K_max) = length c /\
      p.(fno_skip)  = C0 /\
      forall v, length v = length c ->
        spectral_conv p v = circulant_op c v.
Proof.
  Admitted.
  (* Proof: set p.(fno_weights) = DFT(c), then K[v] = IDFT(DFT(c) · DFT(v))
     = IDFT(DFT(c ⊛ v)) = c ⊛ v  by the convolution theorem. *)
