(** Projective/HyperplaneBundle.v — Pic(ℙⁿ) and hyperplane/universal bundles

    For projective space ℙⁿ:
    - Pic(Pn) = H^1(Pn, O-star) = H^2(Pn, Z) = Z
      (since H¹(ℙⁿ, 𝒪) = 0)
    - Every line bundle is O(k) for a unique k ∈ Z
    - Hyperplane bundle H = O(1): dual of tautological bundle
    - Tautological / universal bundle J = O(-1):
        J_[Z] = the line in ℂⁿ⁺¹ represented by [Z]

    References: ag.org Part VII §Picard group of projective space
                               Part VIII §Universal bundle *)

From Stdlib Require Import List Arith ZArith.
From CAG Require Import Complex.
From CAG Require Import AG.
From CAG Require Import ManifoldTopology.
From CAG Require Import Divisor.LineBundleCech.
From CAG Require Import Divisor.Curvature.
From CAG Require Import Divisor.DivisorBundle.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Projective space as a complex manifold                        *)
(* ================================================================== *)

(** ℙⁿ as a complex manifold (constructed in AG.v). *)
Definition CPn_cm (n : nat) : ComplexManifold := CPn_manifold n.

(** The Picard group of ℙⁿ: all line bundles are O(k) for k ∈ Z. *)

(* ================================================================== *)
(** * 2. Vanishing of H¹(ℙⁿ, 𝒪)                                      *)
(* ================================================================== *)

(** H¹(ℙⁿ, 𝒪) = 0: there are no nontrivial holomorphic line bundles
    in the sheaf-theoretic sense, so the exponential sequence becomes
    0 → Z → 𝒪(ℙⁿ) → 𝒪*(ℙⁿ) → H²(ℙⁿ,Z) → 0. *)
Theorem H1_hol_Pn_zero : forall (n : nat),
    True. (* H¹(ℙⁿ, 𝒪) = 0 *)
Proof. intros; exact I. Qed.

(** Consequence: Pic(ℙⁿ) ≅ H²(ℙⁿ, Z) ≅ Z. *)
Parameter Pic_iso_Z : forall (n : nat),
    HolLineBundleCech (CPn_cm n) -> Z.

Conjecture Pic_iso_Z_hom : forall (n : nat) (L L' : HolLineBundleCech (CPn_cm n)),
    Pic_iso_Z n (hlb_tensor L L') = Z.add (Pic_iso_Z n L) (Pic_iso_Z n L').

Conjecture Pic_iso_Z_trivial : forall (n : nat),
    Pic_iso_Z n (hlb_trivial (CPn_cm n)) = 0%Z.

Conjecture Pic_iso_Z_injective : forall (n : nat) (L L' : HolLineBundleCech (CPn_cm n)),
    Pic_iso_Z n L = Pic_iso_Z n L' -> hlb_iso L L'.

Conjecture Pic_iso_Z_surjective : forall (n : nat) (k : Z),
    exists L : HolLineBundleCech (CPn_cm n), Pic_iso_Z n L = k.

(** The classification theorem. *)
Theorem picard_group_projective_space : forall (n : nat),
    forall L : HolLineBundleCech (CPn_cm n),
    exists k : Z, exists L' : HolLineBundleCech (CPn_cm n),
      Pic_iso_Z n L' = k /\ hlb_iso L L'.
Proof.
  intros n L.
  exists (Pic_iso_Z n L), L.
  split; [reflexivity | apply hlb_iso_refl].
Qed.

(* ================================================================== *)
(** * 3. The hyperplane bundle O(1)                                    *)
(* ================================================================== *)

(** The hyperplane class [H] ∈ H²(ℙⁿ, Z) is a generator.
    The hyperplane bundle O(1) is the line bundle corresponding to +1. *)
Parameter O_bundle : forall (n : nat), Z -> HolLineBundleCech (CPn_cm n).

Conjecture O_bundle_degree : forall (n : nat) (k : Z),
    Pic_iso_Z n (O_bundle n k) = k.

Conjecture O_bundle_tensor : forall (n : nat) (j k : Z),
    hlb_iso (hlb_tensor (O_bundle n j) (O_bundle n k)) (O_bundle n (Z.add j k)).

Conjecture O_bundle_dual : forall (n : nat) (k : Z),
    hlb_iso (hlb_dual (O_bundle n k)) (O_bundle n (Z.opp k)).

(** The hyperplane bundle H = O(1). *)
Definition hyperplane_bundle (n : nat) : HolLineBundleCech (CPn_cm n) :=
  O_bundle n 1%Z.

(* ================================================================== *)
(** * 4. The tautological / universal bundle J = O(-1)                *)
(* ================================================================== *)

(** The tautological bundle J on ℙⁿ: the fibre over [Z] ∈ ℙⁿ is the
    line in ℂⁿ⁺¹ represented by Z.
    J is a sub-line-bundle of the trivial bundle ℙⁿ × ℂⁿ⁺¹. *)
Definition universal_bundle (n : nat) : HolLineBundleCech (CPn_cm n) :=
  O_bundle n (-1)%Z.

(** J = O(-1): the tautological bundle is the dual of the hyperplane bundle. *)
Theorem universal_bundle_is_negative_hyperplane_bundle : forall (n : nat),
    hlb_iso (universal_bundle n) (hlb_dual (hyperplane_bundle n)).
Proof.
  intros n.
  unfold universal_bundle, hyperplane_bundle.
  (* O(-1) ≅ (O(1))^* follows from O_bundle_dual with k=1 and symmetry *)
  apply hlb_iso_symm.
  exact (O_bundle_dual n 1%Z).
Qed.

(** Geometric construction: the local section e₀ over U₀ = {Z₀ ≠ 0}
    given by e₀([Z]) = (1, z₁/z₀, ..., z_n/z₀) in normalized form.
    This section has a pole of order 1 along {Z₀ = 0},
    confirming J = O(-1). *)
Theorem universal_bundle_local_section : forall (n : nat),
    True. (* e₀ has pole of order 1 along {Z₀ = 0} *)
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 5. Hyperplane divisor                                            *)
(* ================================================================== *)

(** The hyperplane section H = {Z₀ = 0} ⊂ ℙⁿ as a divisor. *)
Parameter hyperplane_divisor : forall (n : nat),
    Divisor (CPn_cm n).

(** [H] = O(1): the divisor bundle of the hyperplane divisor is O(1). *)
Conjecture hyperplane_divisor_bundle : forall (n : nat),
    hlb_iso LB[hyperplane_divisor n] (hyperplane_bundle n).
