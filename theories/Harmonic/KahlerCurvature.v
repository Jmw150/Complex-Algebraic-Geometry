(** Harmonic/KahlerCurvature.v — Kähler refinements and Kodaira identity

    On a Kähler manifold, the ∂̄-Laplacian equals the ∂-Laplacian
    and both equal half the real Laplacian:

      Δ_{∂̄} = Δ_{∂} = (1/2) Δ_d

    Moreover, the Kähler identities give a relationship between the
    Lefschetz operator and the adjoints:

      [Λ, ∂̄] = -i ∂*     (Kähler identity)
      [Λ, ∂] = i ∂̄*

    The Kodaira identity expresses this via the curvature:
    when E is a positive line bundle, the curvature form Θ satisfies
    Θ = iω (up to normalization), giving the Nakano positivity condition.

    References: ag.org Part I §Kähler identities / Kodaira identity *)

From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From CAG Require Import Complex.
From CAG Require Import AG.
From CAG Require Import ManifoldTopology.
From CAG Require Import LieAlgebra.
From CAG Require Import Harmonic.BundleCovariantDerivatives.
From CAG Require Import Harmonic.Sobolev.
From CAG Require Import Harmonic.Laplacian.
From CAG Require Import Harmonic.Weitzenbock.
From CAG Require Import Kahler.Lefschetz.Operators.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Kähler manifold hermitian bundle setup                       *)
(* ================================================================== *)

(** On a Kähler manifold M, we can also view M as a HermitianManifold
    (forgetting the ∂̄ vs ∂ distinction). *)
(* CAG zero-dependent Parameter kahler_to_hermitian theories/Harmonic/KahlerCurvature.v:40 BEGIN
Parameter kahler_to_hermitian : KahlerManifold -> HermitianManifold.
   CAG zero-dependent Parameter kahler_to_hermitian theories/Harmonic/KahlerCurvature.v:40 END *)

(** E-valued forms on a Kähler manifold. *)
(* CAG zero-dependent Definition KForms_pq theories/Harmonic/KahlerCurvature.v:43 BEGIN
Definition KForms_pq (M : KahlerManifold) (E : HermitianBundle (kahler_to_hermitian M))
    (p q : nat) : Type :=
  Forms_pq E p q.
   CAG zero-dependent Definition KForms_pq theories/Harmonic/KahlerCurvature.v:43 END *)

(* ================================================================== *)
(** * 2. Kähler identities                                            *)
(* ================================================================== *)

(** The Lefschetz operator L (wedge with ω) acts on forms:
    L : Ω^{p,q}(M) → Ω^{p+1,q+1}(M). *)
(* CAG zero-dependent Parameter L_form theories/Harmonic/KahlerCurvature.v:53 BEGIN
Parameter L_form : forall (M : KahlerManifold) {E : HermitianBundle (kahler_to_hermitian M)}
    (p q : nat), KForms_pq M E p q -> KForms_pq M E (p+1) (q+1).
   CAG zero-dependent Parameter L_form theories/Harmonic/KahlerCurvature.v:53 END *)

(** The adjoint Λ: Ω^{p,q}(M) → Ω^{p-1,q-1}(M). *)
(* CAG zero-dependent Parameter Lambda_form theories/Harmonic/KahlerCurvature.v:59 BEGIN
Parameter Lambda_form : forall (M : KahlerManifold) {E : HermitianBundle (kahler_to_hermitian M)}
    (p q : nat), KForms_pq M E p q -> KForms_pq M E (p-1) (q-1).
   CAG zero-dependent Parameter Lambda_form theories/Harmonic/KahlerCurvature.v:59 END *)

(** First Kähler identity: [Λ, ∂̄] = -i ∂*.
    On a Kähler manifold, the bracket of the Lefschetz adjoint Λ with
    ∂̄ equals -i times the formal adjoint of ∂.
    Reference: Griffiths-Harris "Principles of Algebraic Geometry" §0.7
    (Kähler identities), or Voisin "Hodge Theory and Complex Algebraic
    Geometry I" §6.1.
    Stated as a Conjecture pending the ∂ and ∂* operators on E-valued
    (p,q)-forms. *)
(* CAG zero-dependent Theorem kahler_identity_1 theories/Harmonic/KahlerCurvature.v:70 BEGIN
Theorem kahler_identity_1 : forall (M : KahlerManifold)
    {E : HermitianBundle (kahler_to_hermitian M)} (p q : nat)
    (φ : KForms_pq M E p q),
    (** [Λ, ∂̄] φ = -i ∂* φ — pending ∂* operator *)
    @Lambda_form M E p q φ = @Lambda_form M E p q φ.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem kahler_identity_1 theories/Harmonic/KahlerCurvature.v:70 END *)

(** Second Kähler identity: [Λ, ∂] = i ∂̄*.
    Reference: Griffiths-Harris §0.7; Voisin §6.1. *)
(* CAG zero-dependent Theorem kahler_identity_2 theories/Harmonic/KahlerCurvature.v:79 BEGIN
Theorem kahler_identity_2 : forall (M : KahlerManifold)
    {E : HermitianBundle (kahler_to_hermitian M)} (p q : nat)
    (φ : KForms_pq M E p q),
    (** [Λ, ∂] φ = i ∂̄* φ — pending ∂ operator on E-valued forms *)
    @Lambda_form M E p q φ = @Lambda_form M E p q φ.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem kahler_identity_2 theories/Harmonic/KahlerCurvature.v:79 END *)

(* ================================================================== *)
(** * 3. Laplacian equality on Kähler manifolds                      *)
(* ================================================================== *)

(** On a Kähler manifold, the ∂̄-Laplacian equals the ∂-Laplacian.
    Δ_{∂̄} = Δ_{∂}.  This follows directly from the Kähler identities.
    Reference: Griffiths-Harris §0.7 (Kähler identities corollary), or
    Voisin §6.1.  Pending the ∂-Laplacian operator. *)
(* CAG zero-dependent Theorem kahler_laplacians_equal theories/Harmonic/KahlerCurvature.v:94 BEGIN
Theorem kahler_laplacians_equal : forall (M : KahlerManifold)
    {E : HermitianBundle (kahler_to_hermitian M)} (p q : nat)
    (φ : KForms_pq M E p q),
    (** Δ_{∂̄} φ = Δ_{∂} φ — pending Δ_{∂} *)
    dbar_laplacian p q φ = dbar_laplacian p q φ.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem kahler_laplacians_equal theories/Harmonic/KahlerCurvature.v:94 END *)

(** Both equal (1/2) of the real Laplacian: Δ_{∂̄} = (1/2) Δ_d.
    On a Kähler manifold, the three Laplacians (Δ_d on the de Rham
    complex, Δ_∂, Δ_{∂̄}) coincide up to the factor 1/2.
    Reference: Griffiths-Harris §0.7; Voisin §6.1; Wells "Differential
    Analysis on Complex Manifolds" §V.4. *)
(* CAG zero-dependent Theorem kahler_half_real_laplacian theories/Harmonic/KahlerCurvature.v:106 BEGIN
Theorem kahler_half_real_laplacian : forall (M : KahlerManifold)
    {E : HermitianBundle (kahler_to_hermitian M)} (p q : nat)
    (φ : KForms_pq M E p q),
    (** Δ_{∂̄} φ = (1/2) Δ_d φ — pending real Laplacian *)
    dbar_laplacian p q φ = dbar_laplacian p q φ.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem kahler_half_real_laplacian theories/Harmonic/KahlerCurvature.v:106 END *)

(* ================================================================== *)
(** * 4. Kodaira identity                                             *)
(* ================================================================== *)

(** A hermitian line bundle L on a Kähler manifold is positive (ample)
    if its curvature form Θ_L satisfies:
      i Θ_L = (positive multiple of ω) *)
(* CAG zero-dependent Parameter is_positive_bundle theories/Harmonic/KahlerCurvature.v:120 BEGIN
Parameter is_positive_bundle : forall (M : KahlerManifold)
    (L : HermitianBundle (kahler_to_hermitian M)), Prop.
   CAG zero-dependent Parameter is_positive_bundle theories/Harmonic/KahlerCurvature.v:120 END *)

(** Kodaira vanishing theorem setup:
    For a positive line bundle L on a compact Kähler manifold M of dim n,
      H^q(M, K_M ⊗ L) = 0  for q > 0
    where K_M is the canonical bundle.

    Equivalently: Harm^{n,q}(M,L) = 0 for q > 0 when L is positive.

    This follows from the Weitzenböck formula:
    Δ_{∂̄} = ∇*∇ + curvature action > 0 on (n,q)-forms for q > 0.
    Reference: Griffiths-Harris §1.2 (Kodaira vanishing theorem); Voisin
    "Hodge Theory and Complex Algebraic Geometry I" §7.1; Wells §VI.2. *)
(* CAG zero-dependent Theorem kodaira_vanishing theories/Harmonic/KahlerCurvature.v:134 BEGIN
Theorem kodaira_vanishing : forall (M : KahlerManifold)
    (L : HermitianBundle (kahler_to_hermitian M)) (q : nat),
    is_positive_bundle M L ->
    (0 < q)%nat ->
    (** Harm^{n,q}(M, L) = 0 — pending harmonic-space membership predicate
        and the (n,q) bidegree convention.  Reflexive placeholder. *)
    is_positive_bundle M L = is_positive_bundle M L.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem kodaira_vanishing theories/Harmonic/KahlerCurvature.v:134 END *)

(* ================================================================== *)
(** * 5. Nakano positivity                                            *)
(* ================================================================== *)

(** A hermitian vector bundle E of rank r is Nakano positive if its
    curvature Θ_E ∈ Ω^{1,1}(End(E)) satisfies a positivity condition
    on (1,0)-forms tensored with sections of E. *)
(* CAG zero-dependent Parameter is_nakano_positive theories/Harmonic/KahlerCurvature.v:150 BEGIN
Parameter is_nakano_positive : forall (M : KahlerManifold)
    (E : HermitianBundle (kahler_to_hermitian M)), Prop.
   CAG zero-dependent Parameter is_nakano_positive theories/Harmonic/KahlerCurvature.v:150 END *)

(** Nakano vanishing: H^q(M, E) = 0 for q > 0 when E is Nakano positive.
    Strengthens Kodaira vanishing to vector bundles of arbitrary rank.
    Reference: Demailly "Complex Analytic and Differential Geometry"
    §VII.7 (Nakano vanishing theorem); Wells §VI.2. *)
(* CAG zero-dependent Theorem nakano_vanishing theories/Harmonic/KahlerCurvature.v:157 BEGIN
Theorem nakano_vanishing : forall (M : KahlerManifold)
    (E : HermitianBundle (kahler_to_hermitian M)) (p q : nat),
    is_nakano_positive M E ->
    (0 < q)%nat ->
    (** Harm^{p,q}(M,E) = 0 — pending harmonic-space membership predicate.
        Reflexive placeholder. *)
    is_nakano_positive M E = is_nakano_positive M E.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem nakano_vanishing theories/Harmonic/KahlerCurvature.v:157 END *)

(* ================================================================== *)
(** * 6. Consequence: ∂∂̄-lemma                                       *)
(* ================================================================== *)

(** The ∂∂̄-lemma: on a compact Kähler manifold, any ∂̄-exact and
    ∂-closed form is ∂∂̄-exact.
    A central technical input to mixed Hodge theory and the formality
    theorem of Deligne-Griffiths-Morgan-Sullivan.
    Reference: Griffiths-Harris §0.7 (∂∂̄-lemma) and the original DGMS
    paper "Real homotopy theory of Kähler manifolds" Invent. Math. 1975;
    Voisin §6.1.  Pending the ∂ operator on E-valued forms; placeholder
    reflexive. *)
(* CAG zero-dependent Theorem dbar_d_lemma theories/Harmonic/KahlerCurvature.v:186 BEGIN
Theorem dbar_d_lemma : forall (M : KahlerManifold)
    {E : HermitianBundle (kahler_to_hermitian M)} (p q : nat)
    (φ : KForms_pq M E p q),
    (** If ∂̄φ = 0 and φ = ∂̄ψ then φ = ∂∂̄χ for some χ — pending ∂ *)
    φ = φ.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem dbar_d_lemma theories/Harmonic/KahlerCurvature.v:186 END *)
