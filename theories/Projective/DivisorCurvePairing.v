(** Projective/DivisorCurvePairing.v — Nondegeneracy of divisor-curve pairing

    From hard Lefschetz + Poincaré duality + Lefschetz (1,1):
    The intersection pairing Div(M)/≡  ×  C_1(M)/≡  →  Z
    between divisors (codimension-1 cycles) and curves (dimension-1 cycles)
    is nondegenerate.

    This follows because:
    - Hard Lefschetz identifies H^{2n-2}(M,Q) with H^{1,1}(M) ∩ H²(M,Q)
      via the map L^{n-1} : H²(M) → H^{2n-2}(M).
    - Lefschetz (1,1) identifies these with Q-linear combinations of η_D.
    - Poincaré duality gives a perfect pairing between H²(M,Q) and H^{2n-2}(M,Q).

    References: ag.org Part VIII §Nondegeneracy *)

From Stdlib Require Import List Arith ZArith Lia.
From CAG Require Import Complex.
From CAG Require Import ManifoldTopology.
From CAG Require Import Divisor.LineBundleCech.
From CAG Require Import Divisor.DivisorBundle.
From CAG Require Import Hodge.AnalyticClasses.
From CAG Require Import Hodge.Lefschetz11.
From CAG Require Import Kahler.Lefschetz.HardLefschetz.
From CAG Require Import Kahler.HodgeRiemann.BilinearForm.
From CAG Require Import Kahler.Lefschetz.Operators.
From CAG Require Import LieAlgebra.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Poincaré duality                                              *)
(* ================================================================== *)

(** Poincaré duality (famous; Conjecture per skip policy):
    [Hᵏ(M, Q) ≅ H^{2n−k}(M, Q)*] as vector spaces.
    Source: Poincaré 1893; Griffiths–Harris Ch. 0.4 §"Poincaré
    duality"; Hartshorne III.7.  Stated as inverse-pair isomorphisms
    on the [HdR] vector spaces, in the style of γ R34's
    [kodaira_serre_duality_iso]. *)
(* CAG zero-dependent Conjecture poincare_duality theories/Projective/DivisorCurvePairing.v:40 BEGIN
Conjecture poincare_duality : forall (M : KahlerManifold) (k : nat)
    (Hle : (k <= 2 * km_dim M)%nat),
    exists (φ : HdR M k -> HdR M (2 * km_dim M - k))
           (ψ : HdR M (2 * km_dim M - k) -> HdR M k),
      (forall α, ψ (φ α) = α) /\
      (forall β, φ (ψ β) = β).
   CAG zero-dependent Conjecture poincare_duality theories/Projective/DivisorCurvePairing.v:40 END *)

(** The Poincaré pairing: H^k(M) × H^{2n-k}(M) → C. *)
(* CAG zero-dependent Parameter poincare_pairing theories/Projective/DivisorCurvePairing.v:48 BEGIN
(* CAG zero-dependent Parameter poincare_pairing theories/Projective/DivisorCurvePairing.v:48 BEGIN
Parameter poincare_pairing : forall (M : KahlerManifold) (k : nat),
    HdR M k -> HdR M (2 * km_dim M - k) -> CComplex.
   CAG zero-dependent Parameter poincare_pairing theories/Projective/DivisorCurvePairing.v:48 END *)
   CAG zero-dependent Parameter poincare_pairing theories/Projective/DivisorCurvePairing.v:48 END *)

(** Nondegeneracy: if ⟨α, β⟩ = 0 for all β, then α = 0. *)
(* CAG zero-dependent Admitted poincare_nondegenerate theories/Projective/DivisorCurvePairing.v:57 BEGIN
Theorem poincare_nondegenerate : forall (M : KahlerManifold) (k : nat)
    (α : HdR M k),
    (forall β : HdR M (2 * km_dim M - k),
        poincare_pairing M k α β = C0) ->
    α = vs_zero (HdR_vs M k).
Proof. admit. Admitted.
   CAG zero-dependent Admitted poincare_nondegenerate theories/Projective/DivisorCurvePairing.v:57 END *)

(* ================================================================== *)
(** * 2. Divisor classes and curve classes                             *)
(* ================================================================== *)

(** A curve class in H^{2n-2}(M,Z). *)
(* CAG zero-dependent Parameter CurveClass theories/Projective/DivisorCurvePairing.v:70 BEGIN
Parameter CurveClass : KahlerManifold -> Type.
   CAG zero-dependent Parameter CurveClass theories/Projective/DivisorCurvePairing.v:70 END *)

(** The class of a curve C in cohomology. *)
(* CAG zero-dependent Parameter curve_cohomology_class theories/Projective/DivisorCurvePairing.v:67 BEGIN
Parameter curve_cohomology_class : forall (M : KahlerManifold),
    CurveClass M -> HdR M (2 * km_dim M - 2).
   CAG zero-dependent Parameter curve_cohomology_class theories/Projective/DivisorCurvePairing.v:67 END *)

(** The divisor-curve intersection number D · C. *)
(* CAG zero-dependent Parameter intersection_number theories/Projective/DivisorCurvePairing.v:75 BEGIN
(* CAG zero-dependent Parameter intersection_number theories/Projective/DivisorCurvePairing.v:75 BEGIN
Parameter intersection_number : forall (M : KahlerManifold),
    Divisor (km_manifold M) -> CurveClass M -> Z.
   CAG zero-dependent Parameter intersection_number theories/Projective/DivisorCurvePairing.v:75 END *)
   CAG zero-dependent Parameter intersection_number theories/Projective/DivisorCurvePairing.v:75 END *)

(* ================================================================== *)
(** * 3. Main nondegeneracy theorem                                    *)
(* ================================================================== *)

(** Predicate: a divisor is numerically trivial — its class in
    Pic(M) ⊗ Q is zero (axiomatized). *)
(* CAG zero-dependent Parameter is_numerically_trivial_divisor theories/Projective/DivisorCurvePairing.v:84 BEGIN
(* CAG zero-dependent Parameter is_numerically_trivial_divisor theories/Projective/DivisorCurvePairing.v:84 BEGIN
Parameter is_numerically_trivial_divisor : forall (M : KahlerManifold),
    Divisor (km_manifold M) -> Prop.
   CAG zero-dependent Parameter is_numerically_trivial_divisor theories/Projective/DivisorCurvePairing.v:84 END *)
   CAG zero-dependent Parameter is_numerically_trivial_divisor theories/Projective/DivisorCurvePairing.v:84 END *)

(** Predicate: a curve class is numerically trivial. *)
(* CAG zero-dependent Parameter is_numerically_trivial_curve theories/Projective/DivisorCurvePairing.v:88 BEGIN
(* CAG zero-dependent Parameter is_numerically_trivial_curve theories/Projective/DivisorCurvePairing.v:88 BEGIN
Parameter is_numerically_trivial_curve : forall (M : KahlerManifold),
    CurveClass M -> Prop.
   CAG zero-dependent Parameter is_numerically_trivial_curve theories/Projective/DivisorCurvePairing.v:88 END *)
   CAG zero-dependent Parameter is_numerically_trivial_curve theories/Projective/DivisorCurvePairing.v:88 END *)

(** Nondegeneracy of the divisor-curve pairing.

    Informal definition: a divisor [D] with vanishing intersection
    against every curve class is numerically trivial.  Follows from
    Hard Lefschetz + Poincaré duality + Lefschetz (1,1) (Griffiths–Harris
    Ch. 1.4 §"Nondegeneracy of the divisor-curve pairing"). *)
(* CAG zero-dependent Axiom divisor_curve_pairing_nondeg theories/Projective/DivisorCurvePairing.v:93 BEGIN
Axiom divisor_curve_pairing_nondeg : forall (M : KahlerManifold),
    (1 <= km_dim M)%nat ->
    forall D : Divisor (km_manifold M),
    (forall C : CurveClass M, intersection_number M D C = 0%Z) ->
    is_numerically_trivial_divisor M D.
   CAG zero-dependent Axiom divisor_curve_pairing_nondeg theories/Projective/DivisorCurvePairing.v:93 END *)

(** The dual nondegeneracy: a curve class [C] with [D · C = 0] for all
    [D] is numerically trivial.  Source: same as above (Griffiths–Harris
    Ch. 1.4 §"Dual nondegeneracy"). *)
(* CAG zero-dependent Axiom curve_class_nondeg theories/Projective/DivisorCurvePairing.v:102 BEGIN
Axiom curve_class_nondeg : forall (M : KahlerManifold),
    (1 <= km_dim M)%nat ->
    forall C : CurveClass M,
    (forall D : Divisor (km_manifold M), intersection_number M D C = 0%Z) ->
    is_numerically_trivial_curve M C.
   CAG zero-dependent Axiom curve_class_nondeg theories/Projective/DivisorCurvePairing.v:102 END *)

(** Perfect pairing predicate (axiomatized for the Q-tensor of the
    Néron–Severi / cycle groups). *)
(* CAG zero-dependent Parameter is_perfect_pairing_divisor_curve theories/Projective/DivisorCurvePairing.v:138 BEGIN
Parameter is_perfect_pairing_divisor_curve : forall (M : KahlerManifold), Prop.
   CAG zero-dependent Parameter is_perfect_pairing_divisor_curve theories/Projective/DivisorCurvePairing.v:138 END *)

(** The pairing is perfect over Q.  Famous (Néron–Severi nondegeneracy);
    Conjecture per skip policy.  Source: Griffiths–Harris Ch. 1.4
    §"Perfect pairing"; Hartshorne V.1. *)
(* CAG zero-dependent Conjecture divisor_curve_perfect_pairing theories/Projective/DivisorCurvePairing.v:141 BEGIN
Conjecture divisor_curve_perfect_pairing : forall (M : KahlerManifold),
    (1 <= km_dim M)%nat ->
    is_perfect_pairing_divisor_curve M.
   CAG zero-dependent Conjecture divisor_curve_perfect_pairing theories/Projective/DivisorCurvePairing.v:141 END *)
