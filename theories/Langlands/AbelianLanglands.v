(** * Langlands/AbelianLanglands.v
    The GL(1) (abelian) geometric Langlands correspondence.

    For G = GL(1) over a smooth projective curve X, geometric Langlands reduces
    to the classical Picard duality:
        Pic(X) ↔ Char(π₁(X)) = Hom(π₁(X)^ab, C^* )
    via the abelianization
        π₁(X) → π₁(X)^ab = H_1(X, ℤ).

    The Hecke functor in this case is convolution with line-bundle classes on
    Pic(X), and the eigensheaf condition picks out a unique character.

    This file formalizes the *group structure* on rank-1 local systems mod iso:
        — tensor product is the binary operation
        — the trivial line system is the identity
        — the dual local system is the inverse
    and proves the standard consequences (involutivity of dualization, group
    axioms, parametrization of GL(1)-Langlands parameters).

    Structural axioms (existence of trivial system, unit/assoc/comm of tensor,
    dual-as-inverse, tensor functoriality) are paper-attributable to standard
    line-bundle / character-group properties under Riemann–Hilbert. The deep
    inputs are taken from [LocalSystems.v]. The theorems here are proved
    formally from those axioms.

    References:
      - Simpson, "Higgs bundles and local systems" (Publ. Math. IHES 75, 1992).
      - Frenkel, "Lectures on the Langlands program and conformal field
        theory" (esp. §3 for the abelian case).
*)

From Stdlib Require Import List Arith.
From CAG Require Import Complex.
From CAG Require Import ManifoldTopology.
From CAG Require Import Harmonic.BundleCovariantDerivatives.
From CAG Require Import Langlands.LocalSystems.

(* ================================================================== *)
(** * 1. Trivial rank-1 local system (group identity)                  *)
(* ================================================================== *)

(** The trivial rank-1 local system corresponds to the constant character
    χ ≡ 1 : π₁(M) → ℂ*. Under Riemann–Hilbert this is the trivial line
    bundle with the trivial connection. *)
(* CAG zero-dependent Parameter ls_trivial theories/Langlands/AbelianLanglands.v:45 BEGIN
Parameter ls_trivial : forall (M : HermitianManifold), LocalSystem M.
   CAG zero-dependent Parameter ls_trivial theories/Langlands/AbelianLanglands.v:45 END *)

(* CAG zero-dependent Conjecture ls_trivial_rank1 theories/Langlands/AbelianLanglands.v:47 BEGIN
Conjecture ls_trivial_rank1 :
  forall (M : HermitianManifold),
    IsRank1LocalSystem (ls_trivial M).
   CAG zero-dependent Conjecture ls_trivial_rank1 theories/Langlands/AbelianLanglands.v:47 END *)

(* ================================================================== *)
(** * 2. Tensor product as binary operation                             *)
(* ================================================================== *)

(** Tensor unit laws: the trivial system is left/right identity for ⊗. *)
(* CAG zero-dependent Conjecture ls_tensor_unit_l theories/Langlands/AbelianLanglands.v:56 BEGIN
Conjecture ls_tensor_unit_l :
  forall {M : HermitianManifold} (L : LocalSystem M),
    IsRank1LocalSystem L ->
    ls_iso (ls_tensor (ls_trivial M) L) L.
   CAG zero-dependent Conjecture ls_tensor_unit_l theories/Langlands/AbelianLanglands.v:56 END *)

(* CAG zero-dependent Conjecture ls_tensor_unit_r theories/Langlands/AbelianLanglands.v:61 BEGIN
Conjecture ls_tensor_unit_r :
  forall {M : HermitianManifold} (L : LocalSystem M),
    IsRank1LocalSystem L ->
    ls_iso (ls_tensor L (ls_trivial M)) L.
   CAG zero-dependent Conjecture ls_tensor_unit_r theories/Langlands/AbelianLanglands.v:61 END *)

(** Associativity of tensor. *)
(* CAG zero-dependent Conjecture ls_tensor_assoc theories/Langlands/AbelianLanglands.v:67 BEGIN
Conjecture ls_tensor_assoc :
  forall {M : HermitianManifold} (L1 L2 L3 : LocalSystem M),
    IsRank1LocalSystem L1 ->
    IsRank1LocalSystem L2 ->
    IsRank1LocalSystem L3 ->
    ls_iso
      (ls_tensor (ls_tensor L1 L2) L3)
      (ls_tensor L1 (ls_tensor L2 L3)).
   CAG zero-dependent Conjecture ls_tensor_assoc theories/Langlands/AbelianLanglands.v:67 END *)

(** Commutativity. (For rank > 1 this is only a braiding; for rank-1
    line systems tensor is genuinely symmetric.) *)
(* CAG zero-dependent Conjecture ls_tensor_comm theories/Langlands/AbelianLanglands.v:78 BEGIN
Conjecture ls_tensor_comm :
  forall {M : HermitianManifold} (L1 L2 : LocalSystem M),
    IsRank1LocalSystem L1 ->
    IsRank1LocalSystem L2 ->
    ls_iso (ls_tensor L1 L2) (ls_tensor L2 L1).
   CAG zero-dependent Conjecture ls_tensor_comm theories/Langlands/AbelianLanglands.v:78 END *)

(** Tensor is a bifunctor: it respects iso in each argument. *)
(* CAG zero-dependent Conjecture ls_tensor_iso_l theories/Langlands/AbelianLanglands.v:85 BEGIN
Conjecture ls_tensor_iso_l :
  forall {M : HermitianManifold} (L L' N : LocalSystem M),
    ls_iso L L' ->
    ls_iso (ls_tensor L N) (ls_tensor L' N).
   CAG zero-dependent Conjecture ls_tensor_iso_l theories/Langlands/AbelianLanglands.v:85 END *)

(* CAG zero-dependent Conjecture ls_tensor_iso_r theories/Langlands/AbelianLanglands.v:90 BEGIN
Conjecture ls_tensor_iso_r :
  forall {M : HermitianManifold} (L N N' : LocalSystem M),
    ls_iso N N' ->
    ls_iso (ls_tensor L N) (ls_tensor L N').
   CAG zero-dependent Conjecture ls_tensor_iso_r theories/Langlands/AbelianLanglands.v:90 END *)

(** Dual gives the inverse for ⊗. *)
(* CAG zero-dependent Conjecture ls_tensor_dual_l theories/Langlands/AbelianLanglands.v:96 BEGIN
Conjecture ls_tensor_dual_l :
  forall {M : HermitianManifold} (L : LocalSystem M),
    IsRank1LocalSystem L ->
    ls_iso (ls_tensor (ls_dual L) L) (ls_trivial M).
   CAG zero-dependent Conjecture ls_tensor_dual_l theories/Langlands/AbelianLanglands.v:96 END *)

(* CAG zero-dependent Conjecture ls_tensor_dual_r theories/Langlands/AbelianLanglands.v:101 BEGIN
Conjecture ls_tensor_dual_r :
  forall {M : HermitianManifold} (L : LocalSystem M),
    IsRank1LocalSystem L ->
    ls_iso (ls_tensor L (ls_dual L)) (ls_trivial M).
   CAG zero-dependent Conjecture ls_tensor_dual_r theories/Langlands/AbelianLanglands.v:101 END *)

(* ================================================================== *)
(** * 3. Derived theorems                                              *)
(* ================================================================== *)

(** Bifunctorial: iso in BOTH arguments. *)
(* CAG zero-dependent Lemma ls_tensor_iso_both theories/Langlands/AbelianLanglands.v:111 BEGIN
Lemma ls_tensor_iso_both :
    forall {M : HermitianManifold} (L L' N N' : LocalSystem M),
      ls_iso L L' -> ls_iso N N' ->
      ls_iso (ls_tensor L N) (ls_tensor L' N').
Proof.
  intros M L L' N N' HL HN.
  apply (ls_iso_trans _ (ls_tensor L' N)).
  - apply ls_tensor_iso_l. exact HL.
  - apply ls_tensor_iso_r. exact HN.
Qed.
   CAG zero-dependent Lemma ls_tensor_iso_both theories/Langlands/AbelianLanglands.v:111 END *)

(** Dualization is involutive (rank-1 case). *)
(* CAG zero-dependent Theorem ls_dual_involutive theories/Langlands/AbelianLanglands.v:123 BEGIN
Theorem ls_dual_involutive :
    forall {M : HermitianManifold} (L : LocalSystem M),
      IsRank1LocalSystem L ->
      ls_iso (ls_dual (ls_dual L)) L.
Proof.
  intros M L H1.
  pose proof (rank1_dual_rank1 L H1) as Hd.
  pose proof (rank1_dual_rank1 (ls_dual L) Hd) as Hdd.
  apply (ls_iso_trans _ (ls_tensor (ls_trivial M) (ls_dual (ls_dual L)))).
  { apply ls_iso_symm. apply ls_tensor_unit_l. exact Hdd. }
  apply (ls_iso_trans _ (ls_tensor (ls_tensor L (ls_dual L))
                                     (ls_dual (ls_dual L)))).
  { apply ls_tensor_iso_l. apply ls_iso_symm. apply ls_tensor_dual_r. exact H1. }
  apply (ls_iso_trans _ (ls_tensor L (ls_tensor (ls_dual L)
                                                  (ls_dual (ls_dual L))))).
  { apply ls_tensor_assoc; assumption. }
  apply (ls_iso_trans _ (ls_tensor L (ls_trivial M))).
  { apply ls_tensor_iso_r. apply ls_tensor_dual_r. exact Hd. }
  apply ls_tensor_unit_r. exact H1.
Qed.
   CAG zero-dependent Theorem ls_dual_involutive theories/Langlands/AbelianLanglands.v:123 END *)

(** The trivial system is its own dual. *)
(* CAG zero-dependent Theorem ls_dual_trivial theories/Langlands/AbelianLanglands.v:145 BEGIN
Theorem ls_dual_trivial :
    forall (M : HermitianManifold),
      ls_iso (ls_dual (ls_trivial M)) (ls_trivial M).
Proof.
  intro M.
  pose proof (ls_trivial_rank1 M) as H1.
  apply (ls_iso_trans _ (ls_tensor (ls_dual (ls_trivial M)) (ls_trivial M))).
  { apply ls_iso_symm. apply ls_tensor_unit_r.
    apply (rank1_dual_rank1 _ H1). }
  apply ls_tensor_dual_l. exact H1.
Qed.
   CAG zero-dependent Theorem ls_dual_trivial theories/Langlands/AbelianLanglands.v:145 END *)

(** Tensor of inverses: (L₁ ⊗ L₂)^∨ behaves as L₁^∨ ⊗ L₂^∨ — the "tensor
    inverts to tensor of inverses" property. We axiomatize this as
    a separate fact (it is standard but requires going through the
    abelianization, beyond the pure-formal manipulations above). *)
(* Removed dead Axiom `ls_dual_tensor` on 2026-04-30 cleanup pass; no references anywhere in the codebase. *)

(** Tensor closure: tensor of two rank-1 systems lands in the abelian
    Langlands monoid. *)
(* CAG zero-dependent Lemma rank1_tensor_closed theories/Langlands/AbelianLanglands.v:165 BEGIN
Lemma rank1_tensor_closed :
    forall {M : HermitianManifold} (L1 L2 : LocalSystem M),
      IsRank1LocalSystem L1 ->
      IsRank1LocalSystem L2 ->
      IsRank1LocalSystem (ls_tensor L1 L2).
Proof.
  intros. apply rank1_tensor_rank1; assumption.
Qed.
   CAG zero-dependent Lemma rank1_tensor_closed theories/Langlands/AbelianLanglands.v:165 END *)

(** Tensor on rank-1 systems is a (commutative, associative) magma with
    identity and inverses — i.e., an abelian group up to iso. We package
    these into one [Record]-like proposition. *)

(* CAG zero-dependent Definition AbelianLanglandsGroupLaws theories/Langlands/AbelianLanglands.v:178 BEGIN
Definition AbelianLanglandsGroupLaws (M : HermitianManifold) : Prop :=
  (* identity *)
  IsRank1LocalSystem (ls_trivial M)
  /\ (forall L : LocalSystem M, IsRank1LocalSystem L ->
        ls_iso (ls_tensor (ls_trivial M) L) L
        /\ ls_iso (ls_tensor L (ls_trivial M)) L)
  /\ (* assoc *)
     (forall L1 L2 L3 : LocalSystem M,
        IsRank1LocalSystem L1 -> IsRank1LocalSystem L2 -> IsRank1LocalSystem L3 ->
        ls_iso
          (ls_tensor (ls_tensor L1 L2) L3)
          (ls_tensor L1 (ls_tensor L2 L3)))
  /\ (* commutativity *)
     (forall L1 L2 : LocalSystem M,
        IsRank1LocalSystem L1 -> IsRank1LocalSystem L2 ->
        ls_iso (ls_tensor L1 L2) (ls_tensor L2 L1))
  /\ (* inverses *)
     (forall L : LocalSystem M,
        IsRank1LocalSystem L ->
        ls_iso (ls_tensor (ls_dual L) L) (ls_trivial M)
        /\ ls_iso (ls_tensor L (ls_dual L)) (ls_trivial M)).
   CAG zero-dependent Definition AbelianLanglandsGroupLaws theories/Langlands/AbelianLanglands.v:178 END *)

(* CAG zero-dependent Theorem abelian_langlands_group theories/Langlands/AbelianLanglands.v:200 BEGIN
Theorem abelian_langlands_group :
    forall (M : HermitianManifold),
      AbelianLanglandsGroupLaws M.
Proof.
  intro M. unfold AbelianLanglandsGroupLaws.
  split; [apply ls_trivial_rank1 |].
  split; [intros L H; split; [apply ls_tensor_unit_l | apply ls_tensor_unit_r]; auto |].
  split; [intros; apply ls_tensor_assoc; auto |].
  split; [intros; apply ls_tensor_comm; auto |].
  intros L H. split.
  - apply ls_tensor_dual_l; auto.
  - apply ls_tensor_dual_r; auto.
Qed.
   CAG zero-dependent Theorem abelian_langlands_group theories/Langlands/AbelianLanglands.v:200 END *)

(* ================================================================== *)
(** * 4. Connection to the GL(1) Langlands parameter space              *)
(* ================================================================== *)

(** A GL(1) Langlands parameter is a rank-1 local system. We formalize
    the parameter space as a sigma-type and inherit the abelian-group
    structure proved in §3. *)

(* CAG constructive-remove Definition GL1Param theories/Langlands/AbelianLanglands.v:254 BEGIN
Definition GL1Param (M : HermitianManifold) : Type :=
  GL1_Langlands_param M.
   CAG constructive-remove Definition GL1Param theories/Langlands/AbelianLanglands.v:254 END *)

(* CAG zero-dependent Definition GL1_id theories/Langlands/AbelianLanglands.v:225 BEGIN
Definition GL1_id (M : HermitianManifold) : GL1Param M :=
  existT _ (ls_trivial M) (ls_trivial_rank1 M).
   CAG zero-dependent Definition GL1_id theories/Langlands/AbelianLanglands.v:225 END *)

(* CAG zero-dependent Definition GL1_mul theories/Langlands/AbelianLanglands.v:228 BEGIN
Definition GL1_mul {M : HermitianManifold}
    (p q : GL1Param M) : GL1Param M :=
  existT _ (ls_tensor (projT1 p) (projT1 q))
           (rank1_tensor_closed (projT1 p) (projT1 q)
              (projT2 p) (projT2 q)).
   CAG zero-dependent Definition GL1_mul theories/Langlands/AbelianLanglands.v:228 END *)

(* CAG zero-dependent Definition GL1_inv theories/Langlands/AbelianLanglands.v:234 BEGIN
Definition GL1_inv {M : HermitianManifold}
    (p : GL1Param M) : GL1Param M :=
  existT _ (ls_dual (projT1 p)) (rank1_dual_rank1 (projT1 p) (projT2 p)).
   CAG zero-dependent Definition GL1_inv theories/Langlands/AbelianLanglands.v:234 END *)

(** GL(1)-Langlands parameters form an abelian group under tensor product,
    up to local-system isomorphism on the underlying carriers. The group
    laws are exactly the content of [abelian_langlands_group]. *)
(* CAG zero-dependent Theorem gl1_param_group_laws theories/Langlands/AbelianLanglands.v:241 BEGIN
Theorem gl1_param_group_laws :
    forall (M : HermitianManifold),
      let P := GL1Param M in
      let e := GL1_id M in
      let mul := @GL1_mul M in
      let inv := @GL1_inv M in
      (* unit-l *)
      (forall p : P, ls_iso (projT1 (mul e p)) (projT1 p))
      /\ (* unit-r *)
         (forall p : P, ls_iso (projT1 (mul p e)) (projT1 p))
      /\ (* assoc *)
         (forall p q r : P,
             ls_iso (projT1 (mul (mul p q) r)) (projT1 (mul p (mul q r))))
      /\ (* comm *)
         (forall p q : P,
             ls_iso (projT1 (mul p q)) (projT1 (mul q p)))
      /\ (* inv *)
         (forall p : P,
             ls_iso (projT1 (mul (inv p) p)) (projT1 e)).
Proof.
  intros M.
  simpl. repeat split.
  - intros [L H]. simpl. apply ls_tensor_unit_l. exact H.
  - intros [L H]. simpl. apply ls_tensor_unit_r. exact H.
  - intros [L1 H1] [L2 H2] [L3 H3]. simpl.
    apply ls_tensor_assoc; assumption.
  - intros [L1 H1] [L2 H2]. simpl.
    apply ls_tensor_comm; assumption.
  - intros [L H]. simpl. apply ls_tensor_dual_l. exact H.
Qed.
   CAG zero-dependent Theorem gl1_param_group_laws theories/Langlands/AbelianLanglands.v:241 END *)
