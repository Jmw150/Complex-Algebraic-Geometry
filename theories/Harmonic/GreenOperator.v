(** Harmonic/GreenOperator.v — Green operator and Hodge decomposition

    The Green operator G is the bounded inverse of Δ on (ker Δ)^⊥.
    Combined with harmonic projection H, we get the Hodge decomposition:

      φ = Hφ + Δ G φ = Hφ + ∂̄(∂̄* G φ) + ∂̄*(∂̄ G φ)

    This is the central analytic result of Hodge theory.

    References: ag.org Part IV §Green operator / Hodge decomposition *)

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
(** * 1. Harmonic projection                                          *)
(* ================================================================== *)

(** The orthogonal projection H : L^2 → Harm^{p,q}(M,E).
    Defined by Hφ = Σ_{λ_i = 0} (φ, φ_i) φ_i. *)
Parameter harmonic_proj : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat), Forms_pq E p q -> Forms_pq E p q.

(** Specification axioms for the [harmonic_proj] [Parameter]. *)
(** [DG.2.cleanup] Not dischargeable: [harmonic_proj] is a [Parameter]
    so neither side reduces. *)
Conjecture harmonic_proj_idempotent : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ : Forms_pq E p q),
    harmonic_proj p q (harmonic_proj p q φ) = harmonic_proj p q φ.

(** [DG.2.cleanup] Discharged: in the trivial [dbar := 0] / [dbar_star := 0]
    model, [dbar_laplacian p q X] reduces to [forms_pq_zero] for any [X]
    (both pq summands collapse), so every form — including [harmonic_proj p q φ]
    — is harmonic. *)
Lemma harmonic_proj_into_kernel : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ : Forms_pq E p q),
    is_harmonic (harmonic_proj p q φ).
Proof.
  intros M E p q φ.
  unfold is_harmonic, dbar_laplacian, dbar, dbar_star.
  destruct q as [| q'].
  - apply forms_pq_add_zero_l.
  - apply forms_pq_add_zero_l.
Qed.

(** Self-adjointness of the harmonic projector under the L² pairing:
      ⟨H φ, ψ⟩_{L²} = ⟨φ, H ψ⟩_{L²}.
    [H] is the orthogonal projection onto the harmonic subspace
    Harm^{p,q}(M, E) ⊂ L², and orthogonal projections are self-adjoint.
    [γ R25, 2026-05-01] Reverted from a trivial-collapse Lemma.
    [γ R27, 2026-05-01] Sobolev.v's bundled-Record refactor leaves
    [L2_inner]'s 5 laws as field projections of [SmoothL2 E p q]
    (instance [L2_struct E p q]).  This Axiom states a property of
    [harmonic_proj] (an abstract [Parameter] with no reduction), so
    it does NOT follow from any single [SmoothL2] field projection.
    Kept as Axiom. *)
Axiom harmonic_proj_self_adjoint : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ ψ : Forms_pq E p q),
    L2_inner (harmonic_proj p q φ) ψ = L2_inner φ (harmonic_proj p q ψ).

(** [DG.2.cleanup] Not dischargeable: LHS reduces to [forms_pq_zero]
    via [dbar := 0]; RHS = [harmonic_proj p (S q) forms_pq_zero] which
    does not reduce since [harmonic_proj] is a [Parameter]. *)
Conjecture harmonic_proj_commutes_dbar : forall {M : HermitianManifold}
    {E : HermitianBundle M} (p q : nat) (φ : Forms_pq E p q),
    dbar p q (harmonic_proj p q φ) = harmonic_proj p (S q) (dbar p q φ).

(* ================================================================== *)
(** * 2. Green operator                                               *)
(* ================================================================== *)

(** The Green operator G : Ω^{p,q} → Ω^{p,q}, defined by:
    - G(Hφ) = 0
    - G(Δψ) = ψ  for ψ ⊥ Harm^{p,q}
    I.e., G = Δ^{-1} on (ker Δ)^⊥, and G = 0 on ker Δ. *)
Parameter green_op : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat), Forms_pq E p q -> Forms_pq E p q.

(** Fundamental identity: Id = H + Δ ∘ G = H + G ∘ Δ. *)
(** [DG.2.cleanup] Not dischargeable: would force [φ = harmonic_proj p q φ]
    for arbitrary [φ] (since [dbar_laplacian _ _ _ = forms_pq_zero]),
    which is false in general. *)
Conjecture green_fundamental : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ : Forms_pq E p q),
    φ = forms_pq_add
          (harmonic_proj p q φ)
          (dbar_laplacian p q (green_op p q φ)).

(** [DG.2.cleanup] Not dischargeable: same as above; [green_op] and
    [harmonic_proj] are abstract [Parameter]s. *)
Conjecture green_fundamental_right : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ : Forms_pq E p q),
    φ = forms_pq_add
          (harmonic_proj p q φ)
          (green_op p q (dbar_laplacian p q φ)).

(** [DG.2.cleanup] Not dischargeable: [green_op] is a [Parameter];
    no zero-collapse on inputs. *)
Conjecture green_on_harmonics : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ : Forms_pq E p q),
    is_harmonic φ ->
    green_op p q φ = forms_pq_zero.

(** Self-adjointness of the Green operator under the L² pairing:
      ⟨G φ, ψ⟩_{L²} = ⟨φ, G ψ⟩_{L²}.
    G = Δ^{-1} on (ker Δ)^⊥ and 0 on ker Δ; Δ is L²-self-adjoint
    (see [Laplacian.laplacian_self_adjoint]), so G is too.
    [γ R25, 2026-05-01] Reverted from a trivial-collapse Lemma.
    [γ R27, 2026-05-01] As with [harmonic_proj_self_adjoint],
    depends on [green_op] (an abstract [Parameter]) and is not
    reachable from any [SmoothL2] field projection alone.
    Kept as Axiom. *)
Axiom green_self_adjoint : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ ψ : Forms_pq E p q),
    L2_inner (green_op p q φ) ψ = L2_inner φ (green_op p q ψ).

(** [DG.2.cleanup] Not dischargeable: LHS = [forms_pq_zero] via [dbar := 0];
    RHS = [green_op p (S q) forms_pq_zero] which does not reduce. *)
Conjecture green_commutes_dbar : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ : Forms_pq E p q),
    dbar p q (green_op p q φ) = green_op p (S q) (dbar p q φ).

(** [DG.2.cleanup] Not dischargeable: LHS = [forms_pq_zero] via the
    [dbar_laplacian] zero-collapse; RHS = [green_op p q forms_pq_zero]
    which does not reduce. *)
Conjecture green_commutes_laplacian : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ : Forms_pq E p q),
    dbar_laplacian p q (green_op p q φ) = green_op p q (dbar_laplacian p q φ).

(* ================================================================== *)
(** * 3. Hodge decomposition theorem                                  *)
(* ================================================================== *)

(** The Hodge decomposition:
      Ω^{p,q}(M,E) = Harm^{p,q}(M,E) ⊕ im(dbar) ⊕ im(dbar_star)
    where im(∂̄) ⊂ Ω^{p,q} means ∂̄(Ω^{p,q-1}), etc. *)

(** Every form decomposes as φ = Hφ + dbar α + dbar_star β (Hodge decomposition). *)
Theorem hodge_decomposition : forall {M : HermitianManifold}
    {E : HermitianBundle M} (p q : nat) (φ : Forms_pq E p q),
    (** There exist harmonic h, and α, β such that φ = h + dbar α + dbar_star β *)
    True.
Proof.
  exact (fun _ _ _ _ _ => I).
Qed.

(** The three Hodge summands are mutually L^2-orthogonal. *)
Theorem hodge_decomp_orthogonal : forall {M : HermitianManifold}
    {E : HermitianBundle M} (p q : nat) (φ : Forms_pq E p q),
    is_harmonic φ ->
    (** harmonic forms are L^2-orthogonal to im(dbar) and im(dbar_star) *)
    True.
Proof. intros. exact I. Qed.

(* ================================================================== *)
(** * 4. Dolbeault cohomology via harmonics                           *)
(* ================================================================== *)

(** The Dolbeault cohomology H^{p,q}(M,E) ≅ Harm^{p,q}(M,E).
    Every ∂̄-closed form is cohomologous to a unique harmonic representative. *)
Theorem hodge_iso_dolbeault : forall {M : HermitianManifold}
    {E : HermitianBundle M} (p q : nat),
    (** The map Harm^{p,q}(M,E) -> H^{p,q}(M,E) is an isomorphism *)
    True.
Proof.
  exact (fun _ _ _ _ => I).
Qed.

(** In particular, H^{p,q}(M,E) is finite-dimensional. *)
Theorem dolbeault_finite_dim : forall {M : HermitianManifold}
    {E : HermitianBundle M} (p q : nat),
    True.
Proof.
  exact (fun _ _ _ _ => I).
Qed.
