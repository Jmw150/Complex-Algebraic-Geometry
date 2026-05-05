(** Projective/Intersections.v — Intersection theory and degree multiplicativity

    For properly intersecting projective varieties V, W ⊂ P^n:

    Bézout's theorem: if V^k and W^m intersect properly (dimension k+m-n),
        deg(V) · deg(W) = Σ_i mult_{Z_i}(V·W) · deg(Z_i)
    where Z_i are the irreducible components of V ∩ W.

    Corollary (weak Bézout for plane curves):
    Two relatively prime plane curves of degrees d₁,d₂ meet in ≤ d₁d₂ points.

    References: ag.org Part V §Degree under intersections *)

From Stdlib Require Import List Arith ZArith Lia.
From CAG Require Import Complex.
From CAG Require Import ManifoldTopology.
From CAG Require Import Projective.TangentSpace.
From CAG Require Import Projective.FunctionFields.
From CAG Require Import Projective.Degree.
From CAG Require Import Kahler.Lefschetz.Operators.
From CAG Require Import LieAlgebra.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Intersection multiplicity                                     *)
(* ================================================================== *)

(** The intersection multiplicity mult_Z(V·W) of V and W along an
    irreducible component Z of V ∩ W. *)
(* CAG zero-dependent Parameter intersection_multiplicity theories/Projective/Intersections.v:31 BEGIN
Parameter intersection_multiplicity : forall (V W Z : ProjectiveVariety),
    nat.
   CAG zero-dependent Parameter intersection_multiplicity theories/Projective/Intersections.v:31 END *)

(** The irreducible components of V ∩ W. *)
(* CAG zero-dependent Parameter intersection_components theories/Projective/Intersections.v:35 BEGIN
Parameter intersection_components : forall (V W : ProjectiveVariety),
    list ProjectiveVariety.
   CAG zero-dependent Parameter intersection_components theories/Projective/Intersections.v:35 END *)

(** Expected codimension of V ∩ W (proper intersection). *)
Definition expected_codim (V W : ProjectiveVariety) : nat :=
  (pv_ambient_dim V - pv_complex_dim V) +
  (pv_ambient_dim W - pv_complex_dim W).

(** V and W intersect properly iff dim(V ∩ W) = k+m-n. *)
Definition proper_intersection (V W : ProjectiveVariety) : Prop :=
  pv_ambient_dim V = pv_ambient_dim W /\
  (pv_complex_dim V + pv_complex_dim W >= pv_ambient_dim V)%nat.

(* ================================================================== *)
(** * 2. Bézout's theorem                                              *)
(* ================================================================== *)

(** Helper: sum of [mult_Z(V,W) · deg(Z)] over the components in
    [intersection_components V W]. *)
(* CAG zero-dependent Fixpoint sum_mults_times_degs theories/Projective/Intersections.v:56 BEGIN
Fixpoint sum_mults_times_degs (V W : ProjectiveVariety)
    (cs : list ProjectiveVariety) : nat :=
  match cs with
  | nil => 0
  | Z :: cs' =>
      Nat.add
        (Nat.mul (intersection_multiplicity V W Z) (degree_of Z))
        (sum_mults_times_degs V W cs')
  end.
   CAG zero-dependent Fixpoint sum_mults_times_degs theories/Projective/Intersections.v:56 END *)

(** Bézout's theorem (famous; Conjecture per skip policy).
    Source: Bézout 1779; Griffiths–Harris Ch. 1.3, Hartshorne I.7.7.
    For proper intersections, [deg(V) · deg(W)] equals the sum over
    irreducible components [Z] of [V ∩ W] of [mult_Z(V,W) · deg(Z)]. *)
(* CAG zero-dependent Conjecture bezout theories/Projective/Intersections.v:68 BEGIN
Conjecture bezout : forall (V W : ProjectiveVariety),
    proper_intersection V W ->
    Nat.mul (degree_of V) (degree_of W) =
    sum_mults_times_degs V W (intersection_components V W).
   CAG zero-dependent Conjecture bezout theories/Projective/Intersections.v:68 END *)

(** Predicate: V and W intersect transversely along Z. *)
(* CAG zero-dependent Parameter is_transverse_along theories/Projective/Intersections.v:74 BEGIN
(* CAG zero-dependent Parameter is_transverse_along theories/Projective/Intersections.v:74 BEGIN
Parameter is_transverse_along : forall (V W Z : ProjectiveVariety), Prop.
   CAG zero-dependent Parameter is_transverse_along theories/Projective/Intersections.v:74 END *)
   CAG zero-dependent Parameter is_transverse_along theories/Projective/Intersections.v:74 END *)

(** Transverse intersection: all multiplicities are 1.

    Informal definition: when [V ∩ W] meets transversely along an
    irreducible component [Z] (the tangent spaces at any smooth point
    of [Z] span the ambient tangent space), then the intersection
    multiplicity equals 1 (Griffiths–Harris Ch. 1.2 §"Transversality
    and multiplicity"; Hartshorne I.7.4). *)
(* CAG zero-dependent Axiom transverse_intersection_unit_mult theories/Projective/Intersections.v:83 BEGIN
Axiom transverse_intersection_unit_mult : forall (V W Z : ProjectiveVariety),
    is_transverse_along V W Z ->
    intersection_multiplicity V W Z = 1%nat.
   CAG zero-dependent Axiom transverse_intersection_unit_mult theories/Projective/Intersections.v:83 END *)

(* ================================================================== *)
(** * 3. Bézout for hypersurfaces                                      *)
(* ================================================================== *)

(** Predicate: [V(F)] and [V(G)] share no irreducible component
    (axiomatized). *)
(* CAG zero-dependent Parameter no_common_component theories/Projective/Intersections.v:101 BEGIN
Parameter no_common_component : forall {n d1 d2 : nat},
    HomogPoly n d1 -> HomogPoly n d2 -> Prop.
   CAG zero-dependent Parameter no_common_component theories/Projective/Intersections.v:101 END *)

(** For two hypersurfaces V = (F=0) and W = (G=0) of degrees d₁, d₂,
    if V and W have no common component, their intersection has
    degree d₁·d₂.  Famous (Bézout for hypersurfaces); Conjecture per
    skip policy.  Source: Griffiths–Harris Ch. 1.3 §"Bézout for
    hypersurfaces"; Hartshorne I.7.8 corollary. *)
(* CAG zero-dependent Conjecture bezout_hypersurfaces theories/Projective/Intersections.v:107 BEGIN
Conjecture bezout_hypersurfaces : forall (n d1 d2 : nat)
    (F : HomogPoly n d1) (G : HomogPoly n d2),
    no_common_component F G ->
    degree_of (hypersurface_variety n d1 F) *
    degree_of (hypersurface_variety n d2 G) = (d1 * d2)%nat.
   CAG zero-dependent Conjecture bezout_hypersurfaces theories/Projective/Intersections.v:107 END *)

(* ================================================================== *)
(** * 4. Weak Bézout for plane curves                                  *)
(* ================================================================== *)

(** Predicate: F and G are coprime as homogeneous polynomials in 3
    variables (the [n = 2] projective-plane case). *)
(* CAG zero-dependent Parameter coprime_plane theories/Projective/Intersections.v:123 BEGIN
Parameter coprime_plane : forall (d1 d2 : nat),
    HomogPoly 2 d1 -> HomogPoly 2 d2 -> Prop.
   CAG zero-dependent Parameter coprime_plane theories/Projective/Intersections.v:123 END *)

(** Cardinality of the intersection of two plane curves
    (axiomatized count). *)
(* CAG zero-dependent Parameter plane_intersection_card theories/Projective/Intersections.v:128 BEGIN
Parameter plane_intersection_card : forall (d1 d2 : nat),
    HomogPoly 2 d1 -> HomogPoly 2 d2 -> nat.
   CAG zero-dependent Parameter plane_intersection_card theories/Projective/Intersections.v:128 END *)

(** Two relatively prime plane curves of degrees d₁, d₂ have at most
    d₁·d₂ intersection points.  Famous (weak Bézout for plane curves);
    Conjecture per skip policy.  Source: Griffiths–Harris Ch. 1.3
    §"Weak Bézout"; Hartshorne I.7.7 special case. *)
(* CAG zero-dependent Conjecture weak_bezout_plane_curves theories/Projective/Intersections.v:131 BEGIN
Conjecture weak_bezout_plane_curves : forall (d1 d2 : nat)
    (F : HomogPoly 2 d1) (G : HomogPoly 2 d2),
    coprime_plane d1 d2 F G ->
    (plane_intersection_card d1 d2 F G <= d1 * d2)%nat.
   CAG zero-dependent Conjecture weak_bezout_plane_curves theories/Projective/Intersections.v:131 END *)

(* ================================================================== *)
(** * 5. Self-intersection                                             *)
(* ================================================================== *)

(** Self-intersection number of a projective variety, expressed as a
    natural number (axiomatized count). *)
(* CAG zero-dependent Parameter self_intersection_number theories/Projective/Intersections.v:138 BEGIN
(* CAG zero-dependent Parameter self_intersection_number theories/Projective/Intersections.v:138 BEGIN
Parameter self_intersection_number : ProjectiveVariety -> nat.
   CAG zero-dependent Parameter self_intersection_number theories/Projective/Intersections.v:138 END *)
   CAG zero-dependent Parameter self_intersection_number theories/Projective/Intersections.v:138 END *)

(** Top Chern class of the normal bundle, restricted to V (axiomatized
    structural quantity). *)
(* CAG zero-dependent Parameter top_chern_normal theories/Projective/Intersections.v:142 BEGIN
(* CAG zero-dependent Parameter top_chern_normal theories/Projective/Intersections.v:142 BEGIN
Parameter top_chern_normal : ProjectiveVariety -> nat.
   CAG zero-dependent Parameter top_chern_normal theories/Projective/Intersections.v:142 END *)
   CAG zero-dependent Parameter top_chern_normal theories/Projective/Intersections.v:142 END *)

(** The self-intersection V · V equals the degree of the top Chern
    class of the normal bundle.

    Informal definition: [V · V = deg(cₖ(N_{V/M}))], the standard
    excess-intersection formula (Fulton, "Intersection Theory" §6;
    Griffiths–Harris Ch. 1.3 §"Self-intersection"). *)
(* CAG zero-dependent Axiom self_intersection_normal_bundle theories/Projective/Intersections.v:148 BEGIN
Axiom self_intersection_normal_bundle : forall (V : ProjectiveVariety),
    self_intersection_number V = top_chern_normal V.
   CAG zero-dependent Axiom self_intersection_normal_bundle theories/Projective/Intersections.v:148 END *)

(* ================================================================== *)
(** * 6. Intersection pairing is nondegenerate                         *)
(* ================================================================== *)

(** The intersection pairing on cohomology of a Kähler manifold
    (axiomatized as a bilinear form). *)
(* CAG zero-dependent Parameter cohom_intersection_pairing theories/Projective/Intersections.v:179 BEGIN
Parameter cohom_intersection_pairing : forall (M : KahlerManifold) (k : nat),
    HdR M (2 * k) -> HdR M (2 * (km_dim M - k)) -> CComplex.
   CAG zero-dependent Parameter cohom_intersection_pairing theories/Projective/Intersections.v:179 END *)

(** The intersection pairing is nondegenerate (a famous corollary of
    Poincaré duality; Conjecture per skip policy).
    Source: Griffiths–Harris Ch. 0.4 §"Poincaré duality on a Kähler
    manifold"; Hartshorne III.7. *)
(* CAG zero-dependent Conjecture intersection_pairing_nondegenerate theories/Projective/Intersections.v:180 BEGIN
Conjecture intersection_pairing_nondegenerate : forall (M : KahlerManifold) (k : nat)
    (α : HdR M (2 * k)),
    (forall β : HdR M (2 * (km_dim M - k)),
        cohom_intersection_pairing M k α β = C0) ->
    α = vs_zero (HdR_vs M (2 * k)).
   CAG zero-dependent Conjecture intersection_pairing_nondegenerate theories/Projective/Intersections.v:180 END *)
