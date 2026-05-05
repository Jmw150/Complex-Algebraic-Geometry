(** * Langlands/LocalSystems.v
    Flat vector bundles, local systems, and the Riemann-Hilbert correspondence.

    The spectral side of geometric Langlands for GL(n) over a curve X is:
      Loc_n(X) = moduli of rank-n local systems on X
               ≅ {flat rank-n vector bundles} / gauge equivalence
               ≅ {ρ : π₁(X) → GL(n,ℂ)} / conjugacy

    For G = GL(1): local systems are characters χ : π₁(X) → ℂ*.
    The Riemann-Hilbert correspondence gives the equivalence of categories
    between flat bundles and representations of the fundamental group. *)

From Stdlib Require Import List Arith.
From CAG Require Import Complex.
From CAG Require Import AG.
From CAG Require Import ManifoldTopology.
From CAG Require Import Group.
From CAG Require Import Representation.
From CAG Require Import Harmonic.BundleCovariantDerivatives.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Flat connections                                              *)
(* ================================================================== *)

(** A connection is flat if its curvature vanishes identically.
    Flatness is the de Rham / local system condition:
      Θ_{ij} = [∇_i, ∇_{j̄}] = 0  for all i, j. *)
(* CAG zero-dependent Definition IsFlat theories/Langlands/LocalSystems.v:30 BEGIN
Definition IsFlat {M : HermitianManifold} {E : HermitianBundle M}
    (conn : Connection E) : Prop :=
  forall (i j : nat) (s : Section_E E),
    curvature conn i j s = section_zero.
   CAG zero-dependent Definition IsFlat theories/Langlands/LocalSystems.v:30 END *)

(** A local system on M: a hermitian vector bundle equipped with a flat connection. *)
(* CAG constructive-remove Record LocalSystem theories/Langlands/LocalSystems.v:38 BEGIN -- repair partial command cleanup after removing Connection
Record LocalSystem (M : HermitianManifold) : Type :=
{ ls_bundle : HermitianBundle M
(* CAG constructive-remove Command ; theories/Langlands/LocalSystems.v:40 BEGIN -- missing Connection
; ls_conn   : Connection ls_bundle
; ls_flat   : IsFlat ls_conn
}.

   CAG constructive-remove Command ; theories/Langlands/LocalSystems.v:40 END *)

(* CAG constructive-remove Command Arguments theories/Langlands/LocalSystems.v:47 BEGIN -- compile error
Arguments ls_bundle {M} _.

   CAG constructive-remove Command Arguments theories/Langlands/LocalSystems.v:47 END *)
(* CAG constructive-remove Command Arguments theories/Langlands/LocalSystems.v:51 BEGIN -- compile error
Arguments ls_conn   {M} _.

   CAG constructive-remove Command Arguments theories/Langlands/LocalSystems.v:51 END *)
(* CAG constructive-remove Command Arguments theories/Langlands/LocalSystems.v:55 BEGIN -- compile error
Arguments ls_flat   {M} _.

   CAG constructive-remove Command Arguments theories/Langlands/LocalSystems.v:55 END *)
   CAG constructive-remove Record LocalSystem theories/Langlands/LocalSystems.v:38 END *)

(** Rank of a local system. *)
(* CAG constructive-remove Definition ls_rank theories/Langlands/LocalSystems.v:61 BEGIN -- compile error
Definition ls_rank {M : HermitianManifold} (L : LocalSystem M) : nat :=
  hb_rank M (ls_bundle L).

   CAG constructive-remove Definition ls_rank theories/Langlands/LocalSystems.v:61 END *)

(* ================================================================== *)
(** * 2. Isomorphisms of local systems                                 *)
(* ================================================================== *)

(** Two local systems are isomorphic if there is a flat bundle isomorphism
    (a unitary gauge transformation that preserves the flat connection). *)
(* CAG zero-dependent Parameter ls_iso theories/Langlands/LocalSystems.v:56 BEGIN
Parameter ls_iso : forall {M : HermitianManifold},
    LocalSystem M -> LocalSystem M -> Prop.
   CAG zero-dependent Parameter ls_iso theories/Langlands/LocalSystems.v:56 END *)

(* CAG zero-dependent Axiom ls_iso_refl theories/Langlands/LocalSystems.v:59 BEGIN
Axiom ls_iso_refl : forall {M : HermitianManifold} (L : LocalSystem M),
    ls_iso L L.
   CAG zero-dependent Axiom ls_iso_refl theories/Langlands/LocalSystems.v:59 END *)

(* CAG zero-dependent Axiom ls_iso_symm theories/Langlands/LocalSystems.v:64 BEGIN
Axiom ls_iso_symm : forall {M : HermitianManifold} (L L' : LocalSystem M),
    ls_iso L L' -> ls_iso L' L.
   CAG zero-dependent Axiom ls_iso_symm theories/Langlands/LocalSystems.v:64 END *)

(* CAG zero-dependent Axiom ls_iso_trans theories/Langlands/LocalSystems.v:67 BEGIN
Axiom ls_iso_trans : forall {M : HermitianManifold} (L L' L'' : LocalSystem M),
    ls_iso L L' -> ls_iso L' L'' -> ls_iso L L''.
   CAG zero-dependent Axiom ls_iso_trans theories/Langlands/LocalSystems.v:67 END *)

(* ================================================================== *)
(** * 3. Fundamental group and monodromy                               *)
(* ================================================================== *)

(** The fundamental group π₁(M, p) of a complex manifold (axiomatized).
    For a Riemann surface of genus g: π₁ = ⟨a₁,b₁,...,aₘ,bₘ | ∏[aᵢ,bᵢ]=1⟩. *)
(* CAG zero-dependent Parameter pi1 theories/Langlands/LocalSystems.v:76 BEGIN
Parameter pi1 : ComplexManifold -> Type.
   CAG zero-dependent Parameter pi1 theories/Langlands/LocalSystems.v:76 END *)
(* CAG zero-dependent Parameter pi1_group theories/Langlands/LocalSystems.v:77 BEGIN
Parameter pi1_group : forall (M : ComplexManifold), StrictGroup (pi1 M).
   CAG zero-dependent Parameter pi1_group theories/Langlands/LocalSystems.v:77 END *)

(** Monodromy representation: parallel transport of a flat bundle along
    loops in M determines a representation ρ : π₁(M) → GL(n,ℂ). *)
(* CAG zero-dependent Parameter monodromy theories/Langlands/LocalSystems.v:81 BEGIN
Parameter monodromy : forall {M : HermitianManifold} (L : LocalSystem M),
    GroupRep (pi1_group (hman_manifold M)) (ls_rank L).
   CAG zero-dependent Parameter monodromy theories/Langlands/LocalSystems.v:81 END *)

(** Isomorphic local systems have conjugate monodromy representations.
    Gauge transformation g conjugates: ρ' = g ρ g⁻¹. *)
(* CAG zero-dependent Axiom monodromy_iso_conjugate theories/Langlands/LocalSystems.v:81 BEGIN
Axiom monodromy_iso_conjugate : forall {M : HermitianManifold} (L L' : LocalSystem M),
    ls_iso L L' ->
    exists (g : GLMat (ls_rank L)),
      forall (γ : pi1 (hman_manifold M)),
        gl_mat (hom_fn (monodromy L') γ) =
        mmul (mmul (gl_mat g) (gl_mat (hom_fn (monodromy L) γ)) (ls_rank L))
             (gl_inv_mat g) (ls_rank L).
   CAG zero-dependent Axiom monodromy_iso_conjugate theories/Langlands/LocalSystems.v:81 END *)

(* ================================================================== *)
(** * 4. Riemann-Hilbert correspondence                                *)
(* ================================================================== *)

(** Pointwise equality of two representations (comparing matrices of all group
    elements).  This avoids a universe issue when ranks differ syntactically. *)
(* CAG zero-dependent Definition rep_pointwise_eq theories/Langlands/LocalSystems.v:108 BEGIN
Definition rep_pointwise_eq {G : Type} {sg : StrictGroup G} {n m : nat}
    (ρ : GroupRep sg n) (σ : GroupRep sg m) : Prop :=
  n = m /\
  forall g : G, gl_mat (hom_fn ρ g) = gl_mat (hom_fn σ g).
   CAG zero-dependent Definition rep_pointwise_eq theories/Langlands/LocalSystems.v:108 END *)

(** Riemann-Hilbert (surjectivity): every representation of π₁ arises
    as the monodromy of a flat bundle, unique up to isomorphism.
    This is the central equivalence between the analytic and topological
    descriptions of local systems. *)
(* CAG zero-dependent Axiom riemann_hilbert_surjective theories/Langlands/LocalSystems.v:111 BEGIN
Axiom riemann_hilbert_surjective :
  forall {M : HermitianManifold} (n : nat)
         (ρ : GroupRep (pi1_group (hman_manifold M)) n),
  exists (L : LocalSystem M),
    rep_pointwise_eq (monodromy L) ρ.
   CAG zero-dependent Axiom riemann_hilbert_surjective theories/Langlands/LocalSystems.v:111 END *)

(** Riemann-Hilbert (injectivity): flat bundles with pointwise-equal monodromy
    are isomorphic. *)
(* CAG zero-dependent Axiom riemann_hilbert_injective theories/Langlands/LocalSystems.v:119 BEGIN
Axiom riemann_hilbert_injective :
  forall {M : HermitianManifold} (L L' : LocalSystem M),
    rep_pointwise_eq (monodromy L) (monodromy L') ->
    ls_iso L L'.
   CAG zero-dependent Axiom riemann_hilbert_injective theories/Langlands/LocalSystems.v:119 END *)

(** Corollary: surjectivity + injectivity gives the full correspondence. *)
(* CAG zero-dependent Theorem riemann_hilbert theories/Langlands/LocalSystems.v:125 BEGIN
Theorem riemann_hilbert :
  forall {M : HermitianManifold} (n : nat)
         (ρ : GroupRep (pi1_group (hman_manifold M)) n),
  exists (L : LocalSystem M),
    rep_pointwise_eq (monodromy L) ρ /\
    forall (L' : LocalSystem M),
      rep_pointwise_eq (monodromy L') ρ ->
      ls_iso L L'.
Proof.
  intros M n ρ.
  destruct (riemann_hilbert_surjective n ρ) as [L Hmono].
  exists L. split.
  - exact Hmono.
  - intros L' Hmono'.
    apply riemann_hilbert_injective.
    unfold rep_pointwise_eq in *.
    destruct Hmono as [Hrk Hmat].
    destruct Hmono' as [Hrk' Hmat'].
    split.
    + rewrite Hrk, Hrk'. reflexivity.
    + intro g. rewrite Hmat, <- Hmat'. reflexivity.
Qed.
   CAG zero-dependent Theorem riemann_hilbert theories/Langlands/LocalSystems.v:125 END *)

(* ================================================================== *)
(** * 5. Tensor product and dual local systems                         *)
(* ================================================================== *)

(** Tensor product of local systems (corresponds to ⊗ of representations). *)
(* CAG zero-dependent Parameter ls_tensor theories/Langlands/LocalSystems.v:165 BEGIN
Parameter ls_tensor : forall {M : HermitianManifold},
    LocalSystem M -> LocalSystem M -> LocalSystem M.
   CAG zero-dependent Parameter ls_tensor theories/Langlands/LocalSystems.v:165 END *)

(** Dual local system (corresponds to contragredient representation). *)
(* CAG zero-dependent Parameter ls_dual theories/Langlands/LocalSystems.v:169 BEGIN
Parameter ls_dual : forall {M : HermitianManifold},
    LocalSystem M -> LocalSystem M.
   CAG zero-dependent Parameter ls_dual theories/Langlands/LocalSystems.v:169 END *)

(* CAG zero-dependent Axiom ls_tensor_rank theories/Langlands/LocalSystems.v:172 BEGIN
Axiom ls_tensor_rank : forall {M : HermitianManifold} (L L' : LocalSystem M),
    ls_rank (ls_tensor L L') = ls_rank L * ls_rank L'.
   CAG zero-dependent Axiom ls_tensor_rank theories/Langlands/LocalSystems.v:172 END *)

(* CAG zero-dependent Axiom ls_dual_rank theories/Langlands/LocalSystems.v:175 BEGIN
Axiom ls_dual_rank : forall {M : HermitianManifold} (L : LocalSystem M),
    ls_rank (ls_dual L) = ls_rank L.
   CAG zero-dependent Axiom ls_dual_rank theories/Langlands/LocalSystems.v:175 END *)

(* ================================================================== *)
(** * 6. GL(1) local systems: the abelian case                         *)
(* ================================================================== *)

(** A rank-1 local system is determined by a character χ : π₁(M) → GL(1,ℂ) ≅ ℂ*.
    This is the GL(1) Langlands parameter. *)
(* CAG constructive-remove Definition IsRank1LocalSystem theories/Langlands/LocalSystems.v:217 BEGIN -- compile error
Definition IsRank1LocalSystem {M : HermitianManifold} (L : LocalSystem M) : Prop :=
  ls_rank L = 1.

   CAG constructive-remove Definition IsRank1LocalSystem theories/Langlands/LocalSystems.v:217 END *)

(** Tensor product of rank-1 local systems is rank-1. *)
(* CAG zero-dependent Lemma rank1_tensor_rank1 theories/Langlands/LocalSystems.v:188 BEGIN
Lemma rank1_tensor_rank1 : forall {M : HermitianManifold} (L L' : LocalSystem M),
    IsRank1LocalSystem L -> IsRank1LocalSystem L' ->
    IsRank1LocalSystem (ls_tensor L L').
Proof.
  unfold IsRank1LocalSystem. intros M L L' H H'.
  rewrite ls_tensor_rank, H, H'. reflexivity.
Qed.
   CAG zero-dependent Lemma rank1_tensor_rank1 theories/Langlands/LocalSystems.v:188 END *)

(** Dual of a rank-1 local system is rank-1. *)
(* CAG zero-dependent Lemma rank1_dual_rank1 theories/Langlands/LocalSystems.v:197 BEGIN
Lemma rank1_dual_rank1 : forall {M : HermitianManifold} (L : LocalSystem M),
    IsRank1LocalSystem L -> IsRank1LocalSystem (ls_dual L).
Proof.
  unfold IsRank1LocalSystem. intros M L H.
  rewrite ls_dual_rank. exact H.
Qed.
   CAG zero-dependent Lemma rank1_dual_rank1 theories/Langlands/LocalSystems.v:197 END *)

(** The GL(1) Langlands parameter: a rank-1 local system. *)
(* CAG constructive-remove Definition GL1_Langlands_param theories/Langlands/LocalSystems.v:245 BEGIN -- compile error
Definition GL1_Langlands_param (M : HermitianManifold) : Type :=
  { L : LocalSystem M & IsRank1LocalSystem L }.

   CAG constructive-remove Definition GL1_Langlands_param theories/Langlands/LocalSystems.v:245 END *)

(** GL(1) geometric Langlands (classical form):
    Automorphic D-modules on Pic(X) with Hecke eigenvalue χ are classified
    by characters χ : π₁(X) → ℂ* (rank-1 local systems).
    This is stated as an axiom; see HeckeGL1.v for the Hecke structure. *)
(* CAG zero-dependent Axiom gl1_geometric_langlands theories/Langlands/LocalSystems.v:193 BEGIN
Axiom gl1_geometric_langlands :
  forall {M : HermitianManifold},
    forall (χ : GroupRep (pi1_group (hman_manifold M)) 1),
    exists (L : LocalSystem M),
      IsRank1LocalSystem L /\ rep_pointwise_eq (monodromy L) χ.
   CAG zero-dependent Axiom gl1_geometric_langlands theories/Langlands/LocalSystems.v:193 END *)
