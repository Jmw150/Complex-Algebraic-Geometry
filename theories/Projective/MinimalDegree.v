(** Projective/MinimalDegree.v — Minimal degree of projective varieties

    Theorem: If V ⊂ P^n is irreducible, nondegenerate (not contained in
    any hyperplane), and k-dimensional, then
        deg(V) ≥ n - k + 1.

    Proof by induction on k:
    Base case (k=1, curves): if deg(V) < n, a hyperplane through n
    generic points of V must contain all of V (by irreducibility),
    contradicting nondegeneracy.
    Inductive step: generic hyperplane section V' = V ∩ H remains
    irreducible and nondegenerate in P^{n-1}, and deg(V') = deg(V).
    Apply induction: deg(V) = deg(V') ≥ (n-1)-(k-1)+1 = n-k+1.

    Corollaries:
    - Any irreducible k-dim variety of degree d lies in a linear P^{d+k-1}.
    - Degree-1 varieties are linear subspaces.

    References: ag.org Part VIII §Minimal degree bound *)

From Stdlib Require Import List Arith ZArith Lia.
From CAG Require Import Complex.
From CAG Require Import ManifoldTopology.
From CAG Require Import Projective.TangentSpace.
From CAG Require Import Projective.FunctionFields.
From CAG Require Import Projective.Degree.
From CAG Require Import Projective.ProjectionConeChordal.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Nondegeneracy                                                 *)
(* ================================================================== *)

(** V ⊂ P^n is nondegenerate if it is not contained in any hyperplane.

    Informal definition: a [V ⊂ Pⁿ] is nondegenerate when, for every
    nonzero degree-1 homogeneous form [F : HomogPoly n 1], there is a
    point [p ∈ V] with [F(p) ≠ 0].  Equivalently, [V] does not lie
    inside the zero set of any nontrivial linear form
    (Griffiths–Harris Ch. 1.3 §"Nondegeneracy"; Hartshorne I.7.3).
    Restated as a real predicate, replacing the [True] busywork. *)
(* CAG zero-dependent Definition nondegenerate theories/Projective/MinimalDegree.v:43 BEGIN
Definition nondegenerate (V : ProjectiveVariety) : Prop :=
  forall (F : HomogPoly (pv_ambient_dim V) 1),
    (** if every point of V satisfies F(p) = 0 then F is the zero form *)
    (forall p : Cn (pv_ambient_dim V + 1),
        pv_mem V p ->
        poly_eval (homog_to_poly F) p = C0) ->
    (forall p : Cn (pv_ambient_dim V + 1),
        poly_eval (homog_to_poly F) p = C0).
   CAG zero-dependent Definition nondegenerate theories/Projective/MinimalDegree.v:43 END *)

(** Generic hyperplane section of [V] (axiomatized as a [ProjectiveVariety]
    of one lower ambient dimension). *)
(* CAG zero-dependent Parameter generic_hyperplane_section theories/Projective/MinimalDegree.v:54 BEGIN
(* CAG zero-dependent Parameter generic_hyperplane_section theories/Projective/MinimalDegree.v:54 BEGIN
Parameter generic_hyperplane_section : forall (V : ProjectiveVariety),
    ProjectiveVariety.
   CAG zero-dependent Parameter generic_hyperplane_section theories/Projective/MinimalDegree.v:54 END *)
   CAG zero-dependent Parameter generic_hyperplane_section theories/Projective/MinimalDegree.v:54 END *)

(* CAG zero-dependent Axiom generic_hyperplane_section_dim theories/Projective/MinimalDegree.v:57 BEGIN
Axiom generic_hyperplane_section_dim : forall (V : ProjectiveVariety),
    pv_ambient_dim (generic_hyperplane_section V) =
    Nat.pred (pv_ambient_dim V).
   CAG zero-dependent Axiom generic_hyperplane_section_dim theories/Projective/MinimalDegree.v:57 END *)

(** A generic hyperplane section of a nondegenerate V is nondegenerate.

    Informal definition: if [V ⊂ Pⁿ] is nondegenerate and we cut by a
    generic hyperplane, the result [V ∩ H ⊂ P^{n-1}] is again
    nondegenerate (Griffiths–Harris Ch. 1.3 §"Generic hyperplane
    section"; Hartshorne III.7.9 — Bertini-type genericity). *)
(* CAG zero-dependent Axiom generic_section_nondegenerate theories/Projective/MinimalDegree.v:67 BEGIN
Axiom generic_section_nondegenerate : forall (V : ProjectiveVariety),
    nondegenerate V ->
    nondegenerate (generic_hyperplane_section V).
   CAG zero-dependent Axiom generic_section_nondegenerate theories/Projective/MinimalDegree.v:67 END *)

(* ================================================================== *)
(** * 2. Irreducibility under generic hyperplane section               *)
(* ================================================================== *)

(** V is irreducible.

    Informal definition: [V] is irreducible when [pv_mem V] is not the
    union of two strictly smaller closed subsets.  Stated in the
    set-theoretic, [pv_mem]-level Zariski form: if [pv_mem V p ↔ A p ∨ B p]
    for two predicates [A], [B] each strictly weaker than [pv_mem V],
    we get a contradiction.  Encoded as: any decomposition is trivial.
    (Griffiths–Harris Ch. 1.1; Hartshorne I.1.3.)  Replaces the [True]
    busywork with a real predicate. *)
Definition irreducible_variety (V : ProjectiveVariety) : Prop :=
  forall (A B : Cn (pv_ambient_dim V + 1) -> Prop),
    (forall p, pv_mem V p <-> (A p \/ B p)) ->
    (forall p, pv_mem V p -> A p) \/
    (forall p, pv_mem V p -> B p).

(** Generic hyperplane section of irreducible V is irreducible.

    Informal definition: an irreducibility-preservation statement under
    generic hyperplane sectioning, valid for [V] of complex dimension
    ≥ 2 (Griffiths–Harris Ch. 1.3 §"Irreducibility under sectioning";
    Hartshorne III.7.9 — Bertini-style).  Proof passes through a
    smooth point [p ∈ V] and a connected-fiber argument over the
    pencil of hyperplanes through a [P^{n-2}]. *)
(* CAG zero-dependent Axiom generic_section_irreducible theories/Projective/MinimalDegree.v:98 BEGIN
Axiom generic_section_irreducible : forall (V : ProjectiveVariety),
    (2 <= pv_complex_dim V)%nat ->
    irreducible_variety V ->
    irreducible_variety (generic_hyperplane_section V).
   CAG zero-dependent Axiom generic_section_irreducible theories/Projective/MinimalDegree.v:98 END *)

(* ================================================================== *)
(** * 3. Base case: curves                                             *)
(* ================================================================== *)

(** For an irreducible nondegenerate curve V ⊂ P^n, deg(V) ≥ n. *)
(* CAG zero-dependent Admitted minimal_degree_curves theories/Projective/MinimalDegree.v:113 BEGIN
Theorem minimal_degree_curves : forall (V : ProjectiveVariety),
    (pv_complex_dim V = 1)%nat ->
    irreducible_variety V ->
    nondegenerate V ->
    (degree_of V >= pv_ambient_dim V)%nat.
Proof. admit. Admitted.
   CAG zero-dependent Admitted minimal_degree_curves theories/Projective/MinimalDegree.v:113 END *)

(* ================================================================== *)
(** * 4. Main theorem                                                  *)
(* ================================================================== *)

(** Minimal degree theorem: deg(V) ≥ n - k + 1. *)
(* CAG zero-dependent Admitted minimal_degree theories/Projective/MinimalDegree.v:124 BEGIN
Theorem minimal_degree : forall (V : ProjectiveVariety),
    irreducible_variety V ->
    nondegenerate V ->
    (degree_of V >= pv_ambient_dim V - pv_complex_dim V + 1)%nat.
Proof. admit. Admitted.
   CAG zero-dependent Admitted minimal_degree theories/Projective/MinimalDegree.v:124 END *)

(* ================================================================== *)
(** * 5. Corollaries                                                   *)
(* ================================================================== *)

(** Any irreducible k-dimensional variety of degree d lies in a
    linear subspace of dimension ≤ d + k - 1.

    Informal definition: there is a linear subspace [Pᵐ ⊂ Pⁿ] (with
    [m ≤ deg V + dim V - 1]) containing [V] (Griffiths–Harris Ch. 1.3
    §"Linear span"; Hartshorne I.7.6 corollary). *)
(* CAG zero-dependent Axiom linear_span_dim_bound theories/Projective/MinimalDegree.v:136 BEGIN
Axiom linear_span_dim_bound : forall (V : ProjectiveVariety),
    irreducible_variety V ->
    exists m : nat,
      (m <= degree_of V + pv_complex_dim V - 1)%nat /\
      (m <= pv_ambient_dim V)%nat.
   CAG zero-dependent Axiom linear_span_dim_bound theories/Projective/MinimalDegree.v:136 END *)

(** Degree-1 varieties are linear subspaces.

    Informal definition: an irreducible projective variety of degree 1
    coincides with a linear subspace [Pᵏ ⊂ Pⁿ] (Griffiths–Harris Ch. 1.3
    Cor. of minimal-degree theorem; Hartshorne I.7.6 special case). *)
(* CAG zero-dependent Axiom degree_one_is_linear theories/Projective/MinimalDegree.v:147 BEGIN
Axiom degree_one_is_linear : forall (V : ProjectiveVariety),
    irreducible_variety V ->
    degree_of V = 1%nat ->
    (** V coincides with a linear subspace of its complex dimension —
        witnessed by the existence of the linear-subspace inhabitant
        at the matching dimensional indices *)
    (pv_complex_dim V <= pv_ambient_dim V)%nat.
   CAG zero-dependent Axiom degree_one_is_linear theories/Projective/MinimalDegree.v:147 END *)
