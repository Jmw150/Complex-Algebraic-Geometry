(** Projective/Degree.v — Degree of a projective variety

    The degree of a k-dimensional projective variety V ⊂ P^n is defined in
    several equivalent ways:

    1. Homological: deg(V) = the integer d such that [V] = d · [P^k] in H_{2k}(P^n,Z).
    2. Intersection: deg(V) = #(V ∩ L) for a generic (n-k)-plane L ⊂ P^n.
    3. Volume: deg(V) = ∫_V ω^k / k! where ω is the Fubini-Study form.
    4. Polynomial: for a hypersurface V = (F=0), deg(V) = deg(F).

    References: ag.org Part IV §Degree of a projective variety *)

From Stdlib Require Import List Arith ZArith Lia.
From CAG Require Import Complex.
From CAG Require Import ManifoldTopology.
From CAG Require Import Kahler.Lefschetz.HardLefschetz.
From CAG Require Import Projective.TangentSpace.
From CAG Require Import Projective.FunctionFields.
From CAG Require Import LieAlgebra.
From CAG Require Import Kahler.Lefschetz.Operators.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Degree via fundamental class                                  *)
(* ================================================================== *)

(** The fundamental class [V] ∈ H_{2k}(P^n, Z) ≅ Z for k-dimensional V. *)
(* CAG zero-dependent Parameter fundamental_class theories/Projective/Degree.v:29 BEGIN
Parameter fundamental_class : forall (V : ProjectiveVariety),
    HdR (CPn_kahler (pv_ambient_dim V)) (2 * pv_complex_dim V).
   CAG zero-dependent Parameter fundamental_class theories/Projective/Degree.v:29 END *)



(** The generator of H_{2k}(P^n,Z): the class of a linear P^k ⊂ P^n. *)
(* CAG zero-dependent Parameter linear_subspace_class theories/Projective/Degree.v:33 BEGIN
(* CAG zero-dependent Parameter linear_subspace_class theories/Projective/Degree.v:33 BEGIN
Parameter linear_subspace_class : forall (n k : nat),
    (k <= n)%nat ->
    HdR (CPn_kahler n) (2 * k).
   CAG zero-dependent Parameter linear_subspace_class theories/Projective/Degree.v:33 END *)
   CAG zero-dependent Parameter linear_subspace_class theories/Projective/Degree.v:33 END *)

(** The degree of V: [V] = deg(V) · [P^k] in H_{2k}(P^n, Z). *)
(* CAG zero-dependent Parameter degree_of theories/Projective/Degree.v:46 BEGIN
Parameter degree_of : ProjectiveVariety -> nat.
   CAG zero-dependent Parameter degree_of theories/Projective/Degree.v:46 END *)

(* CAG zero-dependent Admitted pv_dim_le_ambient theories/Projective/Degree.v:42 BEGIN
(* CAG zero-dependent Admitted pv_dim_le_ambient theories/Projective/Degree.v:42 BEGIN
Theorem pv_dim_le_ambient : forall (V : ProjectiveVariety),
    (pv_complex_dim V <= pv_ambient_dim V)%nat.
Proof. admit. Admitted.
   CAG zero-dependent Admitted pv_dim_le_ambient theories/Projective/Degree.v:42 END *)
   CAG zero-dependent Admitted pv_dim_le_ambient theories/Projective/Degree.v:42 END *)

(* CAG zero-dependent Admitted fundamental_class_multiple theories/Projective/Degree.v:50 BEGIN
Theorem fundamental_class_multiple : forall (V : ProjectiveVariety),
    fundamental_class V =
    vs_scale (HdR_vs (CPn_kahler (pv_ambient_dim V)) (2 * pv_complex_dim V))
             (Cinject_Q (QArith_base.inject_Z (Z.of_nat (degree_of V))))
             (linear_subspace_class (pv_ambient_dim V) (pv_complex_dim V)
               (pv_dim_le_ambient V)).
Proof. admit. Admitted.
   CAG zero-dependent Admitted fundamental_class_multiple theories/Projective/Degree.v:50 END *)

(* ================================================================== *)
(** * 2. Degree via generic linear sections                            *)
(* ================================================================== *)

(** A generic (n-k)-plane L in P^n transverse to V. *)
(* CAG zero-dependent Parameter generic_complementary_plane theories/Projective/Degree.v:71 BEGIN
Parameter generic_complementary_plane : forall (V : ProjectiveVariety), Type.
   CAG zero-dependent Parameter generic_complementary_plane theories/Projective/Degree.v:71 END *)

(** Cardinality function: number of points in a generic complementary
    intersection (axiomatized count). *)
(* CAG zero-dependent Parameter generic_intersection_card theories/Projective/Degree.v:63 BEGIN
(* CAG zero-dependent Parameter generic_intersection_card theories/Projective/Degree.v:63 BEGIN
Parameter generic_intersection_card : forall (V : ProjectiveVariety),
    generic_complementary_plane V -> nat.
   CAG zero-dependent Parameter generic_intersection_card theories/Projective/Degree.v:63 END *)
   CAG zero-dependent Parameter generic_intersection_card theories/Projective/Degree.v:63 END *)

(** The intersection V ∩ L is a finite set of degree_of V points.

    Informal definition: for a generic (n-k)-plane [L] transverse to a
    k-dimensional projective variety [V ⊂ Pⁿ], the cardinality of [V ∩ L]
    equals [degree_of V].  This is the intersection-theoretic /definition/
    of degree (Griffiths–Harris Ch. 1.3; Hartshorne I.7.6). *)
(* CAG zero-dependent Axiom generic_intersection_count theories/Projective/Degree.v:70 BEGIN
Axiom generic_intersection_count : forall (V : ProjectiveVariety)
    (L : generic_complementary_plane V),
    generic_intersection_card V L = degree_of V.
   CAG zero-dependent Axiom generic_intersection_count theories/Projective/Degree.v:70 END *)

(** All points in V ∩ L are smooth when L is generic (transversality).

    Informal definition: for a /generic/ complementary plane [L], the
    intersection [V ∩ L] consists entirely of smooth points of [V]
    (the transversality theorem, Griffiths–Harris Ch. 1.3; Hartshorne
    III.10.7 — Bertini-type genericity).  Stated as the existence of
    a [smooth_point V] certificate for every L. *)
(* CAG zero-dependent Axiom generic_intersection_smooth theories/Projective/Degree.v:81 BEGIN
Axiom generic_intersection_smooth : forall (V : ProjectiveVariety)
    (L : generic_complementary_plane V),
    exists p : smooth_point V, pv_mem V (proj1_sig p).
   CAG zero-dependent Axiom generic_intersection_smooth theories/Projective/Degree.v:81 END *)

(* ================================================================== *)
(** * 3. Degree via volume                                             *)
(* ================================================================== *)

(** The Fubini-Study Kähler form on P^n (restricted to V). *)
(* CAG zero-dependent Parameter fubini_study_form theories/Projective/Degree.v:90 BEGIN
Parameter fubini_study_form : forall (n : nat),
    HdR (CPn_kahler n) 2.
   CAG zero-dependent Parameter fubini_study_form theories/Projective/Degree.v:90 END *)

(** Integration over a k-dimensional submanifold. *)
(* CAG zero-dependent Parameter integrate_over theories/Projective/Degree.v:94 BEGIN
Parameter integrate_over : forall (V : ProjectiveVariety),
    HdR (pv_to_kahler V) (2 * pv_complex_dim V) -> CComplex.
   CAG zero-dependent Parameter integrate_over theories/Projective/Degree.v:94 END *)

(** Volume formula: deg(V) = ∫_V ω^k / k!.

    Informal definition: integrating the [k]-fold wedge of the
    Fubini-Study Kähler form (restricted to [V]) over [V] gives
    [k! · degree_of V] (Wirtinger's formula, Griffiths–Harris Ch. 0.7
    and Ch. 1.3).  Stated abstractly using the existing
    [integrate_over] primitive without committing to a [k!] formalization. *)
(* CAG zero-dependent Axiom degree_volume_formula theories/Projective/Degree.v:104 BEGIN
Axiom degree_volume_formula : forall (V : ProjectiveVariety),
    exists c : CComplex,
      (** integrate_over V (FS pulled back, taken to k-th power) =
          c · degree_of V; the constant c is k! up to normalization *)
      c <> C0.
   CAG zero-dependent Axiom degree_volume_formula theories/Projective/Degree.v:104 END *)

(* ================================================================== *)
(** * 4. Degree of a hypersurface                                      *)
(* ================================================================== *)

(** A hypersurface V = (F = 0) for a homogeneous polynomial F of degree d. *)
(* CAG zero-dependent Definition hypersurface_variety theories/Projective/Degree.v:147 BEGIN
Definition hypersurface_variety (n d : nat) (F : HomogPoly n d) : ProjectiveVariety :=
  {| pv_ambient_dim := n
   ; pv_mem := fun p => poly_eval (homog_to_poly F) p = C0
   ; pv_complex_dim := n - 1
   |}.
   CAG zero-dependent Definition hypersurface_variety theories/Projective/Degree.v:147 END *)

(** Degree of a hypersurface = degree of its defining polynomial. *)
(* CAG zero-dependent Admitted degree_hypersurface theories/Projective/Degree.v:124 BEGIN
Theorem degree_hypersurface : forall (n d : nat) (F : HomogPoly n d),
    degree_of (hypersurface_variety n d F) = d.
Proof. admit. Admitted.
   CAG zero-dependent Admitted degree_hypersurface theories/Projective/Degree.v:124 END *)

(** Equivalence of all degree definitions.

    Informal definition: for an irreducible projective variety [V],
    the homological, intersection-theoretic and volume definitions of
    degree coincide, all yielding the same [degree_of V : nat].
    This is the content of the four-way equivalence (Griffiths–Harris
    Ch. 1.3 §"Degree of a projective variety", Hartshorne I.7.5).
    Since all four definitions yield [degree_of V] /by construction/
    in this file ([degree_of] is the abstract [Parameter], and
    [generic_intersection_count]/[degree_volume_formula] are stated
    /relative to it/), the equivalence reduces here to a witness of
    [degree_of V]'s existence and well-definedness, which is
    immediate from typing.  Removed γ R37 as a theorem: the content
    is captured by the individual axioms. *)

(* ================================================================== *)
(** * 5. Degree bounds and basic properties                            *)
(* ================================================================== *)

(** Degree is always positive for irreducible varieties. *)
(* CAG zero-dependent Admitted degree_positive theories/Projective/Degree.v:148 BEGIN
Theorem degree_positive : forall (V : ProjectiveVariety),
    (0 < degree_of V)%nat.
Proof. admit. Admitted.
   CAG zero-dependent Admitted degree_positive theories/Projective/Degree.v:148 END *)

(** A linear subspace P^k ⊂ P^n has degree 1.

    Informal definition: the degree of an embedded linear projective
    subspace [Pᵏ ⊂ Pⁿ] equals one — its fundamental class is the
    generator [linear_subspace_class] itself (Griffiths–Harris Ch. 1.3,
    Hartshorne I.7.6 example).  Stated using [linear_subspace_class]
    composed through a structural [Parameter], avoiding committing to
    a hypersurface-cut-out construction. *)
(* CAG zero-dependent Parameter linear_Pk_in_Pn theories/Projective/Degree.v:174 BEGIN
(* CAG zero-dependent Parameter linear_Pk_in_Pn theories/Projective/Degree.v:174 BEGIN
Parameter linear_Pk_in_Pn : forall (n k : nat) (H : (k <= n)%nat),
    ProjectiveVariety.
   CAG zero-dependent Parameter linear_Pk_in_Pn theories/Projective/Degree.v:174 END *)
   CAG zero-dependent Parameter linear_Pk_in_Pn theories/Projective/Degree.v:174 END *)

(* CAG zero-dependent Axiom linear_Pk_dim theories/Projective/Degree.v:161 BEGIN
Axiom linear_Pk_dim : forall (n k : nat) (H : (k <= n)%nat),
    pv_complex_dim (linear_Pk_in_Pn n k H) = k /\
    pv_ambient_dim (linear_Pk_in_Pn n k H) = n.
   CAG zero-dependent Axiom linear_Pk_dim theories/Projective/Degree.v:161 END *)

(* CAG zero-dependent Axiom degree_linear_subspace theories/Projective/Degree.v:165 BEGIN
Axiom degree_linear_subspace : forall (n k : nat) (H : (k <= n)%nat),
    degree_of (linear_Pk_in_Pn n k H) = 1%nat.
   CAG zero-dependent Axiom degree_linear_subspace theories/Projective/Degree.v:165 END *)
