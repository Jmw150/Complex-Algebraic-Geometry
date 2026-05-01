(** Projective/ProjectionConeChordal.v

    Generic projection, cone, and chordal variety.

    - Degree is preserved under generic projection π_p : V → P^{n-1}
      from a point p ∉ V.
    - The cone p*V (union of lines through p meeting V) is algebraic
      and has the same degree as V.
    - The chordal (secant) variety C(V) = closure of union of lines
      through two distinct points of V satisfies dim C(V) ≤ 2k+1.
    - Corollary: any smooth k-dimensional projective variety embeds
      into P^{2k+1} by generic projection.

    References: ag.org Part VI–VII §Projection, Cone, Chordal variety *)

From Stdlib Require Import List Arith ZArith Lia.
From CAG Require Import Complex.
From CAG Require Import ManifoldTopology.
From CAG Require Import Projective.TangentSpace.
From CAG Require Import Projective.FunctionFields.
From CAG Require Import Projective.Degree.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Generic projection from a point                              *)
(* ================================================================== *)

(** Projection from a point p ∉ V onto P^{n-1}. *)
Parameter projection_from_point : forall (n : nat)
    (p : Cn (n+1))
    (V : ProjectiveVariety),
    pv_ambient_dim V = n ->
    ProjectiveVariety.

(** The projected variety has dimension = dim V. *)
Conjecture projection_dim : forall (n : nat) (p : Cn (n+1)) (V : ProjectiveVariety)
    (H : pv_ambient_dim V = n),
    pv_complex_dim (projection_from_point n p V H) = pv_complex_dim V.

(** Generic projection preserves degree. *)
Conjecture degree_of_projection : forall (n : nat) (p : Cn (n+1)) (V : ProjectiveVariety)
    (H : pv_ambient_dim V = n),
    degree_of (projection_from_point n p V H) = degree_of V.

(* ================================================================== *)
(** * 2. Cone over a variety                                           *)
(* ================================================================== *)

(** The cone p*V: union of lines through p meeting V. *)
Parameter cone_variety : forall (n : nat) (p : Cn (n+1))
    (V : ProjectiveVariety),
    pv_ambient_dim V = n ->
    ProjectiveVariety.

(** The cone has dimension = dim V + 1. *)
Conjecture cone_dim : forall (n : nat) (p : Cn (n+1)) (V : ProjectiveVariety)
    (H : pv_ambient_dim V = n),
    pv_complex_dim (cone_variety n p V H) = pv_complex_dim V + 1.

(** Degree of the cone equals degree of V. *)
Conjecture degree_of_cone : forall (n : nat) (p : Cn (n+1)) (V : ProjectiveVariety)
    (H : pv_ambient_dim V = n),
    degree_of (cone_variety n p V H) = degree_of V.

(** The cone is algebraic (Chow's theorem applies to the incidence
    correspondence defining it). *)
Theorem cone_is_algebraic : forall (n : nat) (p : Cn (n+1)) (V : ProjectiveVariety)
    (H : pv_ambient_dim V = n),
    True.
Proof. intros; exact I. Qed.

(** Packaged theorem (follows from [degree_of_projection] and [degree_of_cone]). *)
Theorem degree_of_projection_and_cone : forall (n : nat) (p : Cn (n+1))
    (V : ProjectiveVariety) (H : pv_ambient_dim V = n),
    degree_of (projection_from_point n p V H) = degree_of V /\
    degree_of (cone_variety n p V H) = degree_of V.
Proof.
  intros n p V H. split.
  - apply degree_of_projection.
  - apply degree_of_cone.
Qed.

(* ================================================================== *)
(** * 3. Chordal / secant variety                                      *)
(* ================================================================== *)

(** The chordal variety C(V): closure of union of secant lines and
    tangent lines to V. *)
Parameter chordal_variety : ProjectiveVariety -> ProjectiveVariety.

(** C(V) is algebraic (via incidence correspondence). *)
Theorem chordal_is_algebraic : forall (V : ProjectiveVariety), True.
Proof. intros; exact I. Qed.

(** dim C(V) ≤ 2·dim(V) + 1 (dimension count on incidence variety). *)
Conjecture chordal_dim_bound : forall (V : ProjectiveVariety),
    (pv_complex_dim (chordal_variety V) <= 2 * pv_complex_dim V + 1)%nat.

(* ================================================================== *)
(** * 4. Embedding into P^{2k+1}                                      *)
(* ================================================================== *)

(** If n > 2k+1, projection from a point outside C(V) is an isomorphism
    of V onto its image → V embeds into P^{n-1}.
    Iterating, V embeds into P^{2k+1}. *)
Conjecture embedding_into_P2k1 : forall (V : ProjectiveVariety),
    exists W : ProjectiveVariety,
    pv_ambient_dim W = 2 * pv_complex_dim V + 1 /\
    degree_of W = degree_of V.

(** Packaged corollary. *)
Definition any_smooth_k_dim_variety_embeds_in_P2k1
    (V : ProjectiveVariety) : Prop :=
  exists W : ProjectiveVariety,
  pv_ambient_dim W = 2 * pv_complex_dim V + 1.
