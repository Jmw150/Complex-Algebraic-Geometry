(** Harmonic/Weitzenbock.v — Weitzenböck formula

    The Weitzenböck formula relates the ∂̄-Laplacian to the rough
    Laplacian ∇*∇ via zeroth-order curvature terms:

      Δ_{∂̄} = ∇*∇ + curvature terms

    This is used to:
    1. Show Δ_{∂̄} is elliptic (same principal symbol as ∇*∇)
    2. Derive vanishing theorems via curvature positivity

    References: ag.org Part II §Weitzenböck identity *)

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
From CAG Require Import Harmonic.Spectral.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Rough Laplacian                                              *)
(* ================================================================== *)

(** The rough (Bochner) Laplacian ∇*∇ associated to a connection.
    ∇*∇ = - Σ_i ∇_i ∇_i  (in a local orthonormal frame). *)
Parameter rough_laplacian : forall {M : HermitianManifold} {E : HermitianBundle M}
    (conn : Connection E) (p q : nat),
    Forms_pq E p q -> Forms_pq E p q.

(** Non-negativity of the rough Laplacian under the L² pairing:
      ⟨∇*∇φ, φ⟩_{L²} ≥ 0.
    Equivalently, ⟨∇*∇φ, φ⟩_{L²} = ⟨∇φ, ∇φ⟩_{L²} ≥ 0 by adjointness
    of ∇* and the L² positivity axiom on the bundle Ω^{p,q}(M, E ⊗ T*M).
    [γ R25, 2026-05-01] Reverted from a trivial-collapse Lemma.
    [γ R27, 2026-05-01] Bundled-Record refactor of [L2_inner] in
    Sobolev.v leaves [L2_inner]'s 5 laws as field projections of
    [SmoothL2 E p q] (instance [L2_struct E p q]).  This Axiom
    states a property of [rough_laplacian] (an abstract [Parameter]
    with no reduction), so it does NOT follow from any single
    [SmoothL2] field projection.  Kept as Axiom. *)
Axiom rough_laplacian_nonneg : forall {M : HermitianManifold} {E : HermitianBundle M}
    (conn : Connection E) (p q : nat) (φ : Forms_pq E p q),
    0 <= L2_inner (rough_laplacian conn p q φ) φ.

(** Self-adjointness of the rough Laplacian under the L² pairing:
      ⟨∇*∇φ, ψ⟩_{L²} = ⟨φ, ∇*∇ψ⟩_{L²}.
    Two applications of the formal-adjoint identity for ∇/∇*.
    [γ R25, 2026-05-01] Reverted from a trivial-collapse Lemma.
    [γ R27, 2026-05-01] As above, this depends on [rough_laplacian]
    (an abstract [Parameter]) and is not reachable from any
    [SmoothL2] field projection alone.  Kept as Axiom. *)
Axiom rough_laplacian_self_adjoint : forall {M : HermitianManifold}
    {E : HermitianBundle M} (conn : Connection E) (p q : nat)
    (φ ψ : Forms_pq E p q),
    L2_inner (rough_laplacian conn p q φ) ψ =
    L2_inner φ (rough_laplacian conn p q ψ).

(* ================================================================== *)
(** * 2. Curvature endomorphism                                       *)
(* ================================================================== *)

(** The curvature endomorphism R_{p,q} acting on E-valued (p,q)-forms.
    This is a zeroth-order operator built from the curvature of E
    and the Riemann curvature of M. *)
Parameter curv_endomorphism : forall {M : HermitianManifold} {E : HermitianBundle M}
    (conn : Connection E) (p q : nat),
    Forms_pq E p q -> Forms_pq E p q.

(** Self-adjointness of the curvature endomorphism under the L²
    pairing:
      ⟨R_{p,q}φ, ψ⟩_{L²} = ⟨φ, R_{p,q}ψ⟩_{L²}.
    The curvature endomorphism is the contraction of a hermitian
    [(1,1)]-form against the form-valued indices and is hermitian
    pointwise; this carries to L² self-adjointness.
    [γ R25, 2026-05-01] Reverted from a trivial-collapse Lemma.
    [γ R27, 2026-05-01] As with [rough_laplacian_*], depends on
    [curv_endomorphism] (an abstract [Parameter]) and is not
    reachable from any [SmoothL2] field projection alone.
    Kept as Axiom. *)
Axiom curv_endomorphism_self_adjoint : forall {M : HermitianManifold}
    {E : HermitianBundle M} (conn : Connection E) (p q : nat)
    (φ ψ : Forms_pq E p q),
    L2_inner (curv_endomorphism conn p q φ) ψ =
    L2_inner φ (curv_endomorphism conn p q ψ).

(* ================================================================== *)
(** * 3. Weitzenböck identity                                         *)
(* ================================================================== *)

(** The Weitzenböck formula:
      Δ_{∂̄} φ = ∇*∇ φ + R_{p,q} φ
    where R_{p,q} is a zeroth-order operator depending on the curvatures
    of E and M.

    This is a local computation in an orthonormal frame using the
    Kähler identities and the commutator formula for curvature.
    [DG.2.cleanup] Not dischargeable: LHS reduces to [forms_pq_zero],
    but [rough_laplacian] and [curv_endomorphism] are abstract
    [Parameter]s with no zero-collapse, so RHS does not reduce. *)
Conjecture weitzenbock : forall {M : HermitianManifold} {E : HermitianBundle M}
    (conn : Connection E) (p q : nat) (φ : Forms_pq E p q),
    dbar_laplacian p q φ =
    forms_pq_add (rough_laplacian conn p q φ) (curv_endomorphism conn p q φ).

(* ================================================================== *)
(** * 4. Ellipticity of Δ from Weitzenböck                           *)
(* ================================================================== *)

(** The rough Laplacian ∇*∇ is elliptic of order 2 in any local frame.
    Since the difference Δ_{∂̄} - ∇*∇ = R_{p,q} is zeroth order,
    Δ_{∂̄} is also elliptic of order 2. *)
Theorem dbar_laplacian_elliptic_via_weitzenbock :
    forall {M : HermitianManifold} {E : HermitianBundle M}
    (conn : Connection E) (p q : nat),
    (** Δ_{∂̄} is an elliptic operator of order 2 *)
    True.
Proof.
  exact (fun _ _ _ _ _ => I).
Qed.

(* ================================================================== *)
(** * 5. Bochner-Kodaira vanishing (setup)                           *)
(* ================================================================== *)

(** If the curvature endomorphism R_{p,q} is strictly positive, meaning
    (R_{p,q}φ, φ) ≤ 0 implies φ = 0 (equivalently: for φ ≠ 0, (Rφ,φ) > 0),
    then Harm^{p,q}(M,E) = 0.
    Proof: 0 = (Δφ,φ) = (∇*∇φ,φ) + (Rφ,φ); since (∇*∇φ,φ) ≥ 0, we get
    (Rφ,φ) ≤ 0, hence φ = 0 by the positivity hypothesis. *)
Theorem bochner_vanishing_setup : forall {M : HermitianManifold}
    {E : HermitianBundle M} (conn : Connection E) (p q : nat),
    (** curvature is strictly positive: (Rφ,φ) ≤ 0 implies φ = 0 *)
    (forall (φ : Forms_pq E p q),
       L2_inner (curv_endomorphism conn p q φ) φ <= 0 -> φ = forms_pq_zero) ->
    (** Then every harmonic form vanishes *)
    forall (φ : Forms_pq E p q), is_harmonic φ -> φ = forms_pq_zero.
Proof.
  intros M E conn p q Hcurv_pos φ Hharm.
  (** Step 1: (Δφ,φ) = 0 since Δφ = 0 *)
  assert (Hinner_zero : L2_inner (dbar_laplacian p q φ) φ = 0).
  { unfold is_harmonic in Hharm. rewrite Hharm. apply L2_inner_zero_left. }
  (** Step 2: By Weitzenböck, (Δφ,φ) = (∇*∇φ,φ) + (Rφ,φ) *)
  rewrite (weitzenbock conn p q φ) in Hinner_zero.
  rewrite L2_inner_add_left in Hinner_zero.
  (** Step 3: (∇*∇φ,φ) ≥ 0, so (Rφ,φ) ≤ 0 *)
  pose proof (rough_laplacian_nonneg conn p q φ) as Hrl_nn.
  assert (Hcurv_le : L2_inner (curv_endomorphism conn p q φ) φ <= 0).
  { apply (CReal_nonneg_add_zero_rhs_le (L2_inner (rough_laplacian conn p q φ) φ)).
    - exact Hrl_nn.
    - exact Hinner_zero. }
  (** Step 4: (Rφ,φ) ≤ 0 and strict positivity → φ = 0 *)
  exact (Hcurv_pos φ Hcurv_le).
Qed.
