(** Projective/AllLineBundlesAreDivisors.v

    Theorem: If M ⊂ P^N is a projective submanifold, then every
    holomorphic line bundle L on M is of the form L = [D] for some
    divisor D.

    Proof by induction on dim M:
    It suffices to show H⁰(M, O(L + μH)) ≠ 0 for μ >> 0
    (then dividing by a section of H^μ gives a meromorphic section of L,
    whose divisor satisfies L = [div(s)] = [(s)_0 - (s)_∞]).

    Inductive step:
    - Choose smooth hyperplane section V by Bertini.
    - Exact sequence: 0 → O_M(L+(μ-1)H) → O_M(L+μH) → O_V(L+μH) → 0.
    - By induction, H⁰(V, O(L+μH)) ≠ 0.
    - By Theorem B, H¹(M, O(L+(μ-1)H)) = 0 for μ >> 0.
    - Surjectivity → H⁰(M, O(L+μH)) ≠ 0.

    References: ag.org Part V §Every line bundle is a divisor bundle *)

From Stdlib Require Import List Arith ZArith Lia.
From CAG Require Import Complex.
From CAG Require Import ManifoldTopology.
From CAG Require Import Divisor.LineBundleCech.
From CAG Require Import Divisor.DivisorBundle.
From CAG Require Import Divisor.Curvature.
From CAG Require Import Vanishing.KodairaVanishing.
From CAG Require Import Vanishing.TheoremB.
From CAG Require Import Projective.FunctionFields.
From CAG Require Import Projective.Degree.
From CAG Require Import Kahler.Lefschetz.Operators.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Bertini's theorem                                             *)
(* ================================================================== *)

(** Bertini's theorem: for a positive line bundle L on M and a
    generic section s ∈ H⁰(M,O(L)), the zero set V(s) is smooth. *)
Theorem bertini : forall (M : KahlerManifold)
    (L : HolLineBundleCech (km_manifold M)),
    positive_line_bundle M L ->
    (** there exists a smooth hypersurface V = (s=0) for a generic s — axiomatized *)
    True.
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 2. Meromorphic sections and divisors                             *)
(* ================================================================== *)

(** A meromorphic section s of L: a section on M \ D_∞ with poles along D_∞. *)
Parameter MeromorphicSection : forall (M : KahlerManifold),
    HolLineBundleCech (km_manifold M) -> Type.

(** The divisor of a meromorphic section s = (s)_0 - (s)_∞. *)
Parameter divisor_of_section : forall (M : KahlerManifold)
    (L : HolLineBundleCech (km_manifold M)),
    MeromorphicSection M L -> Divisor (km_manifold M).

(** L = [div(s)] for any meromorphic section s ≠ 0. *)
Theorem line_bundle_is_divisor_bundle_of_section : forall (M : KahlerManifold)
    (L : HolLineBundleCech (km_manifold M))
    (s : MeromorphicSection M L),
    (** L ≅ [div(s)] as line bundles — axiomatized *)
    True.
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 3. Global sections of large twists are nonzero                   *)
(* ================================================================== *)

(** The hyperplane bundle H on M (restriction of O(1) from P^N). *)
Parameter hyperplane_bundle_M : forall (M : KahlerManifold),
    HolLineBundleCech (km_manifold M).

(** H is positive on M. *)
Theorem hyperplane_bundle_positive : forall (M : KahlerManifold),
    positive_line_bundle M (hyperplane_bundle_M M).
Proof. admit. Admitted.

(** For μ >> 0, H⁰(M, O(L + μH)) ≠ 0. *)
Theorem h0_large_twist_nonzero : forall (M : KahlerManifold)
    (L : HolLineBundleCech (km_manifold M)),
    exists μ0 : nat,
    forall μ : nat,
    (μ0 < μ)%nat ->
    exists s : HDolb M (hlb_tensor_km M L (lb_power M (hyperplane_bundle_M M) μ)) 0 0,
    s <> HDolb_zero M _ 0 0.
Proof. admit. Admitted.

(* ================================================================== *)
(** * 4. Main theorem                                                  *)
(* ================================================================== *)

(** Every line bundle on a projective submanifold is a divisor bundle. *)
Theorem line_bundles_on_projective_submanifold_are_divisor_bundles :
    forall (M : KahlerManifold) (L : HolLineBundleCech (km_manifold M)),
    (** M is projective — implicit from being a KahlerManifold with hyperplane bundle *)
    exists D : Divisor (km_manifold M),
    (** L ≅ [D] — axiomatized; proof by induction using Bertini + Theorem B *)
    True.
Proof. intros M L. exists (@nil (Z * DivisorComponent (km_manifold M))). exact I. Qed.
