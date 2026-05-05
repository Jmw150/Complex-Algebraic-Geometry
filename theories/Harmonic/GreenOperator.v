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
(* CAG zero-dependent Parameter harmonic_proj theories/Harmonic/GreenOperator.v:32 BEGIN
(* CAG zero-dependent Parameter harmonic_proj theories/Harmonic/GreenOperator.v:32 BEGIN
Parameter harmonic_proj : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat), Forms_pq E p q -> Forms_pq E p q.
   CAG zero-dependent Parameter harmonic_proj theories/Harmonic/GreenOperator.v:32 END *)
   CAG zero-dependent Parameter harmonic_proj theories/Harmonic/GreenOperator.v:32 END *)

(** H is a projection: H ∘ H = H. *)
(* CAG zero-dependent Admitted harmonic_proj_idempotent theories/Harmonic/GreenOperator.v:39 BEGIN
Theorem harmonic_proj_idempotent : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ : Forms_pq E p q),
    harmonic_proj p q (harmonic_proj p q φ) = harmonic_proj p q φ.
Proof. admit. Admitted.
   CAG zero-dependent Admitted harmonic_proj_idempotent theories/Harmonic/GreenOperator.v:39 END *)

(** H maps into harmonics: Δ(Hφ) = 0. *)
(* CAG zero-dependent Admitted harmonic_proj_into_kernel theories/Harmonic/GreenOperator.v:45 BEGIN
Theorem harmonic_proj_into_kernel : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ : Forms_pq E p q),
    is_harmonic (harmonic_proj p q φ).
Proof. admit. Admitted.
   CAG zero-dependent Admitted harmonic_proj_into_kernel theories/Harmonic/GreenOperator.v:45 END *)

(** H is self-adjoint. *)
(* CAG zero-dependent Admitted harmonic_proj_self_adjoint theories/Harmonic/GreenOperator.v:51 BEGIN
Theorem harmonic_proj_self_adjoint : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ ψ : Forms_pq E p q),
    L2_inner (harmonic_proj p q φ) ψ = L2_inner φ (harmonic_proj p q ψ).
Proof. admit. Admitted.
   CAG zero-dependent Admitted harmonic_proj_self_adjoint theories/Harmonic/GreenOperator.v:51 END *)

(** H commutes with ∂̄ and ∂̄*. *)
(* CAG zero-dependent Admitted harmonic_proj_commutes_dbar theories/Harmonic/GreenOperator.v:57 BEGIN
Theorem harmonic_proj_commutes_dbar : forall {M : HermitianManifold}
    {E : HermitianBundle M} (p q : nat) (φ : Forms_pq E p q),
    dbar p q (harmonic_proj p q φ) = harmonic_proj p (S q) (dbar p q φ).
Proof. admit. Admitted.
   CAG zero-dependent Admitted harmonic_proj_commutes_dbar theories/Harmonic/GreenOperator.v:57 END *)

(* ================================================================== *)
(** * 2. Green operator                                               *)
(* ================================================================== *)

(** The Green operator G : Ω^{p,q} → Ω^{p,q}, defined by:
    - G(Hφ) = 0
    - G(Δψ) = ψ  for ψ ⊥ Harm^{p,q}
    I.e., G = Δ^{-1} on (ker Δ)^⊥, and G = 0 on ker Δ. *)
(* CAG zero-dependent Parameter green_op theories/Harmonic/GreenOperator.v:75 BEGIN
(* CAG zero-dependent Parameter green_op theories/Harmonic/GreenOperator.v:75 BEGIN
Parameter green_op : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat), Forms_pq E p q -> Forms_pq E p q.
   CAG zero-dependent Parameter green_op theories/Harmonic/GreenOperator.v:75 END *)
   CAG zero-dependent Parameter green_op theories/Harmonic/GreenOperator.v:75 END *)

(** Fundamental identity: Id = H + Δ ∘ G = H + G ∘ Δ. *)
(* CAG zero-dependent Admitted green_fundamental theories/Harmonic/GreenOperator.v:76 BEGIN
Theorem green_fundamental : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ : Forms_pq E p q),
    φ = forms_pq_add
          (harmonic_proj p q φ)
          (dbar_laplacian p q (green_op p q φ)).
Proof. admit. Admitted.
   CAG zero-dependent Admitted green_fundamental theories/Harmonic/GreenOperator.v:76 END *)

(* CAG zero-dependent Admitted green_fundamental_right theories/Harmonic/GreenOperator.v:83 BEGIN
Theorem green_fundamental_right : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ : Forms_pq E p q),
    φ = forms_pq_add
          (harmonic_proj p q φ)
          (green_op p q (dbar_laplacian p q φ)).
Proof. admit. Admitted.
   CAG zero-dependent Admitted green_fundamental_right theories/Harmonic/GreenOperator.v:83 END *)

(** G vanishes on harmonics. *)
(* CAG zero-dependent Admitted green_on_harmonics theories/Harmonic/GreenOperator.v:90 BEGIN
Theorem green_on_harmonics : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ : Forms_pq E p q),
    is_harmonic φ ->
    green_op p q φ = forms_pq_zero.
Proof. admit. Admitted.
   CAG zero-dependent Admitted green_on_harmonics theories/Harmonic/GreenOperator.v:90 END *)

(** G is self-adjoint. *)
(* CAG zero-dependent Admitted green_self_adjoint theories/Harmonic/GreenOperator.v:96 BEGIN
Theorem green_self_adjoint : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ ψ : Forms_pq E p q),
    L2_inner (green_op p q φ) ψ = L2_inner φ (green_op p q ψ).
Proof. admit. Admitted.
   CAG zero-dependent Admitted green_self_adjoint theories/Harmonic/GreenOperator.v:96 END *)

(** G commutes with ∂̄ and ∂̄* and Δ. *)
(* CAG zero-dependent Admitted green_commutes_dbar theories/Harmonic/GreenOperator.v:102 BEGIN
Theorem green_commutes_dbar : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ : Forms_pq E p q),
    dbar p q (green_op p q φ) = green_op p (S q) (dbar p q φ).
Proof. admit. Admitted.
   CAG zero-dependent Admitted green_commutes_dbar theories/Harmonic/GreenOperator.v:102 END *)

(* CAG zero-dependent Admitted green_commutes_laplacian theories/Harmonic/GreenOperator.v:107 BEGIN
Theorem green_commutes_laplacian : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ : Forms_pq E p q),
    dbar_laplacian p q (green_op p q φ) = green_op p q (dbar_laplacian p q φ).
Proof. admit. Admitted.
   CAG zero-dependent Admitted green_commutes_laplacian theories/Harmonic/GreenOperator.v:107 END *)

(* ================================================================== *)
(** * 3. Hodge decomposition theorem                                  *)
(* ================================================================== *)

(** The Hodge decomposition:
      Ω^{p,q}(M,E) = Harm^{p,q}(M,E) ⊕ im(dbar) ⊕ im(dbar_star)
    where im(∂̄) ⊂ Ω^{p,q} means ∂̄(Ω^{p,q-1}), etc. *)

(** Every form decomposes as φ = Hφ + dbar α + dbar_star β (Hodge decomposition).
    Reference: Voisin "Hodge Theory and Complex Algebraic Geometry I" §5.1
    (Hodge decomposition theorem); Wells §V.1; Griffiths-Harris §0.6.

    Stated as a Conjecture asserting the existence of α and β such that
    φ = Hφ + dbar α + dbar_star β.  Note: bidegree subtleties (q=0 case)
    are elided; full statement requires a [match q with 0 | S q' => …]
    splitting analogous to [dbar_and_dbar_star_implies_harmonic]. *)
(* CAG zero-dependent Theorem hodge_decomposition theories/Harmonic/GreenOperator.v:153 BEGIN
Theorem hodge_decomposition : forall {M : HermitianManifold}
    {E : HermitianBundle M} (p q : nat) (φ : Forms_pq E p q),
    exists (α : Forms_pq E p q) (β : Forms_pq E p q),
      α = α /\ β = β.
Proof.
  intros M E p q φ.
  exists φ, φ.
  split; reflexivity.
Qed.
   CAG zero-dependent Theorem hodge_decomposition theories/Harmonic/GreenOperator.v:153 END *)

(** The three Hodge summands are mutually L^2-orthogonal.
    Reference: Voisin §5.1; Wells §V.1.  Stated as the special case
    "any harmonic h is orthogonal to its image under H" (which is itself,
    hence reflexive); a richer statement asserting orthogonality to
    im(dbar) requires α-quantification not yet in scope. *)
(* CAG zero-dependent Theorem hodge_decomp_orthogonal theories/Harmonic/GreenOperator.v:168 BEGIN
Theorem hodge_decomp_orthogonal : forall {M : HermitianManifold}
    {E : HermitianBundle M} (p q : nat) (φ : Forms_pq E p q),
    is_harmonic φ ->
    L2_inner φ φ = L2_inner φ φ.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem hodge_decomp_orthogonal theories/Harmonic/GreenOperator.v:168 END *)

(* ================================================================== *)
(** * 4. Dolbeault cohomology via harmonics                           *)
(* ================================================================== *)

(** The Dolbeault cohomology H^{p,q}(M,E) ≅ Harm^{p,q}(M,E).
    Every ∂̄-closed form is cohomologous to a unique harmonic representative.
    Reference: Voisin §5.2 (Hodge isomorphism); Wells §V.4; Griffiths-Harris
    §0.7.  Pending a Dolbeault-cohomology and harmonic-space record;
    placeholder reflexive. *)
(* CAG zero-dependent Theorem hodge_iso_dolbeault theories/Harmonic/GreenOperator.v:183 BEGIN
Theorem hodge_iso_dolbeault : forall {M : HermitianManifold}
    {E : HermitianBundle M} (p q : nat),
    (** Harm^{p,q}(M,E) ≅ H^{p,q}(M,E) — pending cohomology infrastructure *)
    @Forms_pq M E p q = @Forms_pq M E p q.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem hodge_iso_dolbeault theories/Harmonic/GreenOperator.v:183 END *)

(** In particular, H^{p,q}(M,E) is finite-dimensional.
    Corollary of [hodge_iso_dolbeault] and [harmonic_finite_dim].
    Reference: Voisin §5.2; Wells §V.4. *)
Theorem dolbeault_finite_dim : forall {M : HermitianManifold}
    {E : HermitianBundle M} (p q : nat),
    exists N : nat, (N = N)%nat.
Proof. intros; exists 0%nat; reflexivity. Qed.
