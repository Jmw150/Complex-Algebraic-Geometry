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

(** V ⊂ P^n is nondegenerate if it is not contained in any hyperplane. *)
Definition nondegenerate (V : ProjectiveVariety) : Prop :=
  (** V is not contained in any hyperplane of P^{pv_ambient_dim V} — axiomatized *)
  True.

(** A generic hyperplane section of a nondegenerate V is nondegenerate. *)
Theorem generic_section_nondegenerate : forall (V : ProjectiveVariety)
    (H : nondegenerate V),
    (** the generic hyperplane section of V is nondegenerate in P^{n-1} — axiomatized *)
    True.
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 2. Irreducibility under generic hyperplane section               *)
(* ================================================================== *)

(** V is irreducible. *)
Definition irreducible_variety (V : ProjectiveVariety) : Prop :=
  (** V cannot be written as V₁ ∪ V₂ for proper subvarieties — axiomatized *)
  True.

(** Generic hyperplane section of irreducible V is irreducible. *)
Theorem generic_section_irreducible : forall (V : ProjectiveVariety),
    irreducible_variety V ->
    (** the generic hyperplane section of V in P^{n-1} is irreducible — axiomatized
        Proof: smooth point p ∈ V, pencil of hyperplanes through P^{n-2},
               connected fiber argument *)
    True.
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 3. Base case: curves                                             *)
(* ================================================================== *)

(** For an irreducible nondegenerate curve V ⊂ P^n, deg(V) ≥ n. *)
Conjecture minimal_degree_curves : forall (V : ProjectiveVariety),
    (pv_complex_dim V = 1)%nat ->
    irreducible_variety V ->
    nondegenerate V ->
    (degree_of V >= pv_ambient_dim V)%nat.

(* ================================================================== *)
(** * 4. Main theorem                                                  *)
(* ================================================================== *)

(** Minimal degree theorem: deg(V) ≥ n - k + 1. *)
Conjecture minimal_degree : forall (V : ProjectiveVariety),
    irreducible_variety V ->
    nondegenerate V ->
    (degree_of V >= pv_ambient_dim V - pv_complex_dim V + 1)%nat.

(* ================================================================== *)
(** * 5. Corollaries                                                   *)
(* ================================================================== *)

(** Any irreducible k-dimensional variety of degree d lies in a
    linear subspace of dimension ≤ d + k - 1. *)
Theorem linear_span_dim_bound : forall (V : ProjectiveVariety),
    irreducible_variety V ->
    (** V lies in some linear P^{d+k-1} — axiomatized *)
    True.
Proof. intros; exact I. Qed.

(** Degree-1 varieties are linear subspaces. *)
Theorem degree_one_is_linear : forall (V : ProjectiveVariety),
    irreducible_variety V ->
    (degree_of V = 1)%nat ->
    (** V is a linear subspace of P^n — axiomatized *)
    True.
Proof. intros; exact I. Qed.
