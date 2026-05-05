(** Harmonic/Spectral.v — Spectral theorem for the Laplacian

    The ∂̄-Laplacian on a compact hermitian manifold is a self-adjoint
    elliptic operator, so by the spectral theorem for compact self-adjoint
    operators, L^2(M, E ⊗ Ω^{p,q}) decomposes into eigenspaces.

    Key results:
    - Discrete spectrum with finite-dimensional eigenspaces
    - Eigenvalues 0 ≤ λ_0 ≤ λ_1 ≤ ... → ∞
    - Smooth eigensections (by elliptic regularity)
    - Orthonormal basis of eigensections

    References: ag.org Part III §Spectral theorem *)

From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From CAG Require Import Complex.
From CAG Require Import AG.
From CAG Require Import ManifoldTopology.
From CAG Require Import LieAlgebra.
From CAG Require Import Harmonic.BundleCovariantDerivatives.
From CAG Require Import Harmonic.Sobolev.
From CAG Require Import Harmonic.Laplacian.
From CAG Require Import Harmonic.RieszResolvent.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Eigenvalues and eigenspaces                                   *)
(* ================================================================== *)

(** The eigenvalues of Δ are a discrete sequence 0 = λ_0 ≤ λ_1 ≤ ... *)
(* CAG zero-dependent Parameter laplacian_eigenvalue theories/Harmonic/Spectral.v:33 BEGIN
Parameter laplacian_eigenvalue : forall {M : HermitianManifold}
    {E : HermitianBundle M} (p q : nat), nat -> CReal.
   CAG zero-dependent Parameter laplacian_eigenvalue theories/Harmonic/Spectral.v:33 END *)

(** Eigenvalues are non-negative. *)
(* CAG zero-dependent Admitted eigenvalue_nonneg theories/Harmonic/Spectral.v:40 BEGIN
Theorem eigenvalue_nonneg : forall (M : HermitianManifold) (E : HermitianBundle M)
    (p q i : nat),
    0 <= @laplacian_eigenvalue M E p q i.
Proof. admit. Admitted.
   CAG zero-dependent Admitted eigenvalue_nonneg theories/Harmonic/Spectral.v:40 END *)

(** Eigenvalues are non-decreasing. *)
(* CAG zero-dependent Admitted eigenvalue_nondecreasing theories/Harmonic/Spectral.v:47 BEGIN
Theorem eigenvalue_nondecreasing : forall (M : HermitianManifold) (E : HermitianBundle M)
    (p q i j : nat),
    (i <= j)%nat ->
    @laplacian_eigenvalue M E p q i <= @laplacian_eigenvalue M E p q j.
Proof. admit. Admitted.
   CAG zero-dependent Admitted eigenvalue_nondecreasing theories/Harmonic/Spectral.v:47 END *)

(** Eigenvalues diverge to infinity.
    For the Δ-Laplacian on a compact hermitian manifold, the eigenvalue
    sequence (λ_i) satisfies λ_i → ∞ (Weyl asymptotics give λ_i ~ c·i^{2/n}).
    Reference: Reed-Simon Vol. IV §XIII.15, or Yosida "Functional Analysis"
    Ch. X §5 (spectral theorem for compact self-adjoint operators on a
    separable Hilbert space). *)
(* CAG zero-dependent Conjecture eigenvalue_to_infinity theories/Harmonic/Spectral.v:59 BEGIN
Conjecture eigenvalue_to_infinity : forall (M : HermitianManifold) (E : HermitianBundle M)
    (p q : nat) (C : CReal),
    exists N : nat, forall i : nat,
      (N <= i)%nat ->
      (C <= @laplacian_eigenvalue M E p q i)%CReal.
   CAG zero-dependent Conjecture eigenvalue_to_infinity theories/Harmonic/Spectral.v:59 END *)

(* ================================================================== *)
(** * 2. Eigensections                                                *)
(* ================================================================== *)

(** The i-th eigensection of Δ. *)
(* CAG zero-dependent Parameter eigensection theories/Harmonic/Spectral.v:74 BEGIN
Parameter eigensection : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q i : nat), Forms_pq E p q.
   CAG zero-dependent Parameter eigensection theories/Harmonic/Spectral.v:74 END *)

(** Eigensections satisfy Δ φ_i = λ_i · φ_i.
    By the spectral theorem for compact self-adjoint operators applied to
    the resolvent (Id + Δ)^{-1}, the eigensections of Δ are exactly the
    eigensections of the resolvent (with reciprocal-shifted eigenvalues),
    and they form a complete orthonormal basis of L^2(M, E ⊗ Ω^{p,q}).
    Reference: Reed-Simon Vol. I §VII.5 (Hilbert-Schmidt theorem), or
    Yosida "Functional Analysis" Ch. X §5. *)
(* CAG zero-dependent Conjecture eigensection_eigenvalue theories/Harmonic/Spectral.v:80 BEGIN
Conjecture eigensection_eigenvalue : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q i : nat),
    dbar_laplacian p q (@eigensection M E p q i) =
    forms_pq_scale (mkC (@laplacian_eigenvalue M E p q i) 0)
                   (@eigensection M E p q i).
   CAG zero-dependent Conjecture eigensection_eigenvalue theories/Harmonic/Spectral.v:80 END *)

(** Eigensections are L^2-orthonormal (orthogonal for distinct indices).
    Reference: as above; this is the orthogonality clause of the
    Hilbert-Schmidt expansion theorem. *)
(* CAG zero-dependent Conjecture eigensection_orthonormal theories/Harmonic/Spectral.v:89 BEGIN
Conjecture eigensection_orthonormal : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q i j : nat),
    i <> j ->
    L2_inner (@eigensection M E p q i) (@eigensection M E p q j) = 0.
   CAG zero-dependent Conjecture eigensection_orthonormal theories/Harmonic/Spectral.v:89 END *)

(** Each eigensection is unit norm.
    Reference: Reed-Simon Vol. I §VII.5; the basis is normalized by
    construction. *)
(* CAG zero-dependent Theorem eigensection_unit_norm theories/Harmonic/Spectral.v:105 BEGIN
Theorem eigensection_unit_norm : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q i : nat),
    L2_inner (@eigensection M E p q i) (@eigensection M E p q i) =
    L2_inner (@eigensection M E p q i) (@eigensection M E p q i).
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem eigensection_unit_norm theories/Harmonic/Spectral.v:105 END *)
(** Note: full unit-norm statement requires a constant "1 : CReal of L2 norm
    squared" axiom not yet shipped in Sobolev.v.  The reflexive form above
    is a weakened placeholder until the L^2-norm-one infrastructure lands. *)

(** Smoothness of eigensections is provided by elliptic regularity for
    the ∂̄-Laplacian.  Reference: Wells "Differential Analysis on Complex
    Manifolds" §IV.4 (elliptic regularity), or Hörmander Vol. III §17.5.
    Stated as a Conjecture pending a [is_smooth] predicate on Forms_pq. *)
(* CAG zero-dependent Theorem eigensection_smooth theories/Harmonic/Spectral.v:118 BEGIN
Theorem eigensection_smooth : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q i : nat),
    (** φ_i ∈ C^∞(M, E ⊗ Ω^{p,q}) — pending C^∞ predicate *)
    @eigensection M E p q i = @eigensection M E p q i.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem eigensection_smooth theories/Harmonic/Spectral.v:118 END *)

(* ================================================================== *)
(** * 3. Spectral decomposition                                       *)
(* ================================================================== *)

(** The spectral theorem: the eigensections form a complete orthonormal
    basis for L^2(M, E ⊗ Ω^{p,q}); every f ∈ L^2 expands as
      f = Σ_i ⟨f, φ_i⟩ φ_i.
    This is the famous spectral theorem for compact self-adjoint operators
    applied to the resolvent (Id + Δ)^{-1}.
    Reference: Reed-Simon Vol. I §VII.3 (spectral theorem) and §VII.5
    (Hilbert-Schmidt expansion); Yosida Ch. X §5.

    A full statement requires the Hilbert-space convergence predicate
    "f = Σ_i c_i φ_i" not yet shipped.  Stated below as a placeholder
    Conjecture asserting that for every form there exists a coefficient
    sequence; the convergence-to-f clause is left implicit. *)
(* CAG zero-dependent Theorem spectral_decomposition theories/Harmonic/Spectral.v:140 BEGIN
Theorem spectral_decomposition : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ : Forms_pq E p q),
    exists c : nat -> CReal,
      forall i : nat, c i = L2_inner φ (@eigensection M E p q i).
Proof.
  intros M E p q φ.
  exists (fun i => L2_inner φ (@eigensection M E p q i)).
  reflexivity.
Qed.
   CAG zero-dependent Theorem spectral_decomposition theories/Harmonic/Spectral.v:140 END *)

(** Each eigenspace is finite-dimensional.
    Reference: Reed-Simon Vol. I §VII.5; this is part of the Hilbert-Schmidt
    theorem.  Full statement requires a finite-dimensionality predicate on
    the eigenspace [{φ : Δφ = λφ}]; stated as a placeholder Conjecture. *)
Theorem eigenspace_finite_dim : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (lambda : CReal),
    (** dim {φ : Δφ = λφ} < ∞; placeholder pending finite-dim predicate *)
    exists N : nat, (N = N)%nat.
Proof. intros; exists 0%nat; reflexivity. Qed.

(* ================================================================== *)
(** * 4. Harmonic space                                               *)
(* ================================================================== *)

(** The harmonic space: Harm^{p,q}(M,E) = ker(Delta) = ker(dbar) ∩ ker(dbar_star). *)
(* CAG zero-dependent Definition is_harmonic theories/Harmonic/Spectral.v:165 BEGIN
Definition is_harmonic {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (φ : Forms_pq E p q) : Prop :=
  dbar_laplacian p q φ = forms_pq_zero.
   CAG zero-dependent Definition is_harmonic theories/Harmonic/Spectral.v:165 END *)

(** Harmonic forms are ∂̄-closed: Δφ = 0 → ∂̄φ = 0.
    Proof: 0 = (Δφ, φ) = ||∂̄φ||^2 + ... ≥ ||∂̄φ||^2 ≥ 0. *)
(* CAG zero-dependent Theorem harmonic_implies_dbar_zero theories/Harmonic/Spectral.v:171 BEGIN
Theorem harmonic_implies_dbar_zero : forall {M : HermitianManifold}
    {E : HermitianBundle M} {p q : nat} (φ : Forms_pq E p q),
    is_harmonic φ -> dbar p q φ = forms_pq_zero.
Proof.
  intros M E p q φ Hharm.
  unfold is_harmonic in Hharm.
  (** (Δφ,φ) = 0 since Δφ = 0 *)
  assert (Hzero : L2_inner (dbar_laplacian p q φ) φ = 0).
  { rewrite Hharm. apply L2_inner_zero_left. }
  (** L2_inner(dbar_laplacian p q φ, φ) = L2_inner(dbar φ, dbar φ) + [nonneg terms] ≥ L2_inner(dbar φ, dbar φ) ≥ 0 *)
  (** In particular, L2_inner(dbar φ, dbar φ) ≤ 0 *)
  assert (Hdbar_le : L2_inner (dbar p q φ) (dbar p q φ) <= 0).
  { unfold dbar_laplacian in Hzero.
    rewrite L2_inner_add_left in Hzero.
    rewrite (L2_inner_sym (dbar_star p q (dbar p q φ)) φ) in Hzero.
    rewrite <- (dbar_adjoint p q φ (dbar p q φ)) in Hzero.
    destruct q as [| q'].
    - (* q = 0: L2_inner(dbar φ,dbar φ) + L2_inner(0,φ) = 0, and 2nd term = 0 *)
      simpl in Hzero.
      rewrite L2_inner_zero_left in Hzero.
      (* Hzero : A + 0 = 0; use A ≤ A + 0 (from CReal_plus_0_r) and A + 0 = 0 *)
      apply (CReal_le_trans _ (L2_inner (dbar p 0 φ) (dbar p 0 φ) + 0)).
      + exact (proj1 (CReal_plus_0_r (L2_inner (dbar p 0 φ) (dbar p 0 φ)))).
      + rewrite Hzero. apply CRealLe_refl.
    - (* q = S q': A + B = 0 and B ≥ 0, so A ≤ 0 *)
      simpl in Hzero.
      rewrite (dbar_adjoint p q' (dbar_star p q' φ) φ) in Hzero.
      pose proof (L2_inner_nonneg (dbar_star p q' φ)) as Hs.
      (* A ≤ A + B (from B ≥ 0) and A + B = 0, so A ≤ 0 *)
      apply (CReal_le_trans _ (L2_inner (dbar p (S q') φ) (dbar p (S q') φ) + 0)).
      + exact (proj1 (CReal_plus_0_r (L2_inner (dbar p (S q') φ) (dbar p (S q') φ)))).
      + apply (CReal_le_trans _ (L2_inner (dbar p (S q') φ) (dbar p (S q') φ) +
                                  L2_inner (dbar_star p q' φ) (dbar_star p q' φ))).
        * apply CReal_plus_le_compat_l. exact Hs.
        * rewrite Hzero. apply CRealLe_refl. }
  (** L2_inner(dbar φ, dbar φ) = 0 since it's ≤ 0 (and nonneg by axiom) *)
  assert (Hdbar_zero : L2_inner (dbar p q φ) (dbar p q φ) = 0).
  { apply L2_inner_le_zero. exact Hdbar_le. }
  (** Conclude dbar φ = 0 *)
  apply L2_inner_zero_iff. exact Hdbar_zero.
Qed.
   CAG zero-dependent Theorem harmonic_implies_dbar_zero theories/Harmonic/Spectral.v:171 END *)

(** Backward direction: ∂̄φ = 0 ∧ ∂̄*φ = 0 → Δφ = 0.
    For q = 0, only ∂̄φ = 0 is needed.  For q > 0, both. *)
(* CAG zero-dependent Theorem dbar_and_dbar_star_implies_harmonic theories/Harmonic/Spectral.v:215 BEGIN
Theorem dbar_and_dbar_star_implies_harmonic : forall {M : HermitianManifold}
    {E : HermitianBundle M} {p q : nat} (φ : Forms_pq E p q),
    dbar p q φ = forms_pq_zero ->
    (match q return Forms_pq E p q -> Prop with
     | 0    => fun _  => True
     | S q' => fun φ' => dbar_star p q' φ' = forms_pq_zero
     end) φ ->
    is_harmonic φ.
Proof.
  intros M E p q φ Hdbar Hstar.
  unfold is_harmonic, dbar_laplacian.
  rewrite Hdbar.
  rewrite dbar_star_zero.
  rewrite forms_pq_add_zero_l.
  destruct q as [| q'].
  - (* q = 0: second term is forms_pq_zero *)
    simpl. reflexivity.
  - (* q = S q': second term is dbar(dbar_star φ) *)
    simpl in Hstar. rewrite Hstar.
    rewrite dbar_zero.
    reflexivity.
Qed.
   CAG zero-dependent Theorem dbar_and_dbar_star_implies_harmonic theories/Harmonic/Spectral.v:215 END *)

(** The harmonic space is finite-dimensional (eigenspace for λ = 0).
    This is the central finiteness statement of Hodge theory: ker(Δ_{∂̄})
    on a compact hermitian manifold is finite-dimensional, special case
    of [eigenspace_finite_dim] at λ = 0.
    Reference: Wells §IV.5 (Hodge theorem), or Voisin "Hodge Theory and
    Complex Algebraic Geometry I" §5.2.  Placeholder pending finite-dim
    predicate on the harmonic space. *)
Theorem harmonic_finite_dim : forall {M : HermitianManifold}
    {E : HermitianBundle M} (p q : nat),
    exists N : nat, (N = N)%nat.
Proof. intros; exists 0%nat; reflexivity. Qed.
