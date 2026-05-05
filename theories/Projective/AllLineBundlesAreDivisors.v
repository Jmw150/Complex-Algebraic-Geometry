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

(** Predicate: a hypersurface (zero set of a section) is smooth. *)
(* CAG zero-dependent Parameter is_smooth_hypersurface theories/Projective/AllLineBundlesAreDivisors.v:40 BEGIN
Parameter is_smooth_hypersurface : forall (M : KahlerManifold),
    Divisor (km_manifold M) -> Prop.
   CAG zero-dependent Parameter is_smooth_hypersurface theories/Projective/AllLineBundlesAreDivisors.v:40 END *)

(** Bertini's theorem (famous; Conjecture per skip policy):
    for a positive line bundle [L] on [M] and a generic section
    [s ∈ H⁰(M, 𝒪(L))], the zero set [V(s)] is smooth.
    Source: Bertini 1882; Griffiths–Harris Ch. 1.1 §"Bertini's theorem";
    Hartshorne III.10.9. *)
(* CAG zero-dependent Conjecture bertini theories/Projective/AllLineBundlesAreDivisors.v:48 BEGIN
Conjecture bertini : forall (M : KahlerManifold)
    (L : HolLineBundleCech (km_manifold M)),
    positive_line_bundle M L ->
    exists D : Divisor (km_manifold M), is_smooth_hypersurface M D.
   CAG zero-dependent Conjecture bertini theories/Projective/AllLineBundlesAreDivisors.v:48 END *)

(* ================================================================== *)
(** * 2. Meromorphic sections and divisors                             *)
(* ================================================================== *)

(** A meromorphic section s of L: a section on M \ D_∞ with poles along D_∞. *)
(* CAG zero-dependent Parameter MeromorphicSection theories/Projective/AllLineBundlesAreDivisors.v:58 BEGIN
Parameter MeromorphicSection : forall (M : KahlerManifold),
    HolLineBundleCech (km_manifold M) -> Type.
   CAG zero-dependent Parameter MeromorphicSection theories/Projective/AllLineBundlesAreDivisors.v:58 END *)

(** The divisor of a meromorphic section s = (s)_0 - (s)_∞. *)
(* CAG zero-dependent Parameter divisor_of_section theories/Projective/AllLineBundlesAreDivisors.v:62 BEGIN
(* CAG zero-dependent Parameter divisor_of_section theories/Projective/AllLineBundlesAreDivisors.v:62 BEGIN
Parameter divisor_of_section : forall (M : KahlerManifold)
    (L : HolLineBundleCech (km_manifold M)),
    MeromorphicSection M L -> Divisor (km_manifold M).
   CAG zero-dependent Parameter divisor_of_section theories/Projective/AllLineBundlesAreDivisors.v:62 END *)
   CAG zero-dependent Parameter divisor_of_section theories/Projective/AllLineBundlesAreDivisors.v:62 END *)

(** [L ≅ [div(s)]] for any meromorphic section [s ≠ 0].

    Informal definition: every line bundle is canonically isomorphic
    to the divisor bundle of the divisor of any of its meromorphic
    sections (Griffiths–Harris Ch. 1.1 §"Divisor of a meromorphic
    section"; Hartshorne II.6.4).  Stated using the project's
    [hlb_iso] iso-relation between holomorphic line bundles and
    divisor-bundle [LB[_]] notation. *)
(* CAG zero-dependent Axiom line_bundle_is_divisor_bundle_of_section theories/Projective/AllLineBundlesAreDivisors.v:74 BEGIN
Axiom line_bundle_is_divisor_bundle_of_section : forall (M : KahlerManifold)
    (L : HolLineBundleCech (km_manifold M))
    (s : MeromorphicSection M L),
    hlb_iso L LB[divisor_of_section M L s].
   CAG zero-dependent Axiom line_bundle_is_divisor_bundle_of_section theories/Projective/AllLineBundlesAreDivisors.v:74 END *)

(* ================================================================== *)
(** * 3. Global sections of large twists are nonzero                   *)
(* ================================================================== *)

(** The hyperplane bundle H on M (restriction of O(1) from P^N). *)
(* CAG zero-dependent Parameter hyperplane_bundle_M theories/Projective/AllLineBundlesAreDivisors.v:86 BEGIN
(* CAG zero-dependent Parameter hyperplane_bundle_M theories/Projective/AllLineBundlesAreDivisors.v:86 BEGIN
Parameter hyperplane_bundle_M : forall (M : KahlerManifold),
    HolLineBundleCech (km_manifold M).
   CAG zero-dependent Parameter hyperplane_bundle_M theories/Projective/AllLineBundlesAreDivisors.v:86 END *)
   CAG zero-dependent Parameter hyperplane_bundle_M theories/Projective/AllLineBundlesAreDivisors.v:86 END *)

(** H is positive on M. *)
(* CAG zero-dependent Admitted hyperplane_bundle_positive theories/Projective/AllLineBundlesAreDivisors.v:90 BEGIN
Theorem hyperplane_bundle_positive : forall (M : KahlerManifold),
    positive_line_bundle M (hyperplane_bundle_M M).
Proof. admit. Admitted.
   CAG zero-dependent Admitted hyperplane_bundle_positive theories/Projective/AllLineBundlesAreDivisors.v:90 END *)

(** For μ >> 0, H⁰(M, O(L + μH)) ≠ 0. *)
(* CAG zero-dependent Admitted h0_large_twist_nonzero theories/Projective/AllLineBundlesAreDivisors.v:100 BEGIN
Theorem h0_large_twist_nonzero : forall (M : KahlerManifold)
    (L : HolLineBundleCech (km_manifold M)),
    exists μ0 : nat,
    forall μ : nat,
    (μ0 < μ)%nat ->
    exists s : HDolb M (hlb_tensor_km M L (lb_power M (hyperplane_bundle_M M) μ)) 0 0,
    s <> HDolb_zero M _ 0 0.
Proof. admit. Admitted.
   CAG zero-dependent Admitted h0_large_twist_nonzero theories/Projective/AllLineBundlesAreDivisors.v:100 END *)

(* ================================================================== *)
(** * 4. Main theorem                                                  *)
(* ================================================================== *)

(** Every line bundle on a projective submanifold is a divisor bundle.

    Informal definition: [L ≅ [D]] for some divisor [D] (Griffiths–Harris
    Ch. 1.1 §"Every line bundle is a divisor bundle"; Hartshorne II.6.11).
    The proof is by induction on dim M, using Bertini + Theorem B.
    The statement uses the project's [hlb_iso] for the isomorphism;
    the previous [True]-as-witness form was busywork. *)
(* CAG zero-dependent Conjecture line_bundles_on_projective_submanifold_are_divisor_bundles theories/Projective/AllLineBundlesAreDivisors.v:129 BEGIN
Conjecture line_bundles_on_projective_submanifold_are_divisor_bundles :
    forall (M : KahlerManifold) (L : HolLineBundleCech (km_manifold M)),
    exists D : Divisor (km_manifold M),
      hlb_iso L LB[D].
   CAG zero-dependent Conjecture line_bundles_on_projective_submanifold_are_divisor_bundles theories/Projective/AllLineBundlesAreDivisors.v:129 END *)
