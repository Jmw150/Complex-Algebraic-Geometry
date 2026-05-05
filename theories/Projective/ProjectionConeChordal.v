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
(* CAG zero-dependent Parameter projection_from_point theories/Projective/ProjectionConeChordal.v:30 BEGIN
Parameter projection_from_point : forall (n : nat)
    (p : Cn (n+1))
    (V : ProjectiveVariety),
    pv_ambient_dim V = n ->
    ProjectiveVariety.
   CAG zero-dependent Parameter projection_from_point theories/Projective/ProjectionConeChordal.v:30 END *)

(** The projected variety has dimension = dim V. *)
(* CAG zero-dependent Admitted projection_dim theories/Projective/ProjectionConeChordal.v:40 BEGIN
Theorem projection_dim : forall (n : nat) (p : Cn (n+1)) (V : ProjectiveVariety)
    (H : pv_ambient_dim V = n),
    pv_complex_dim (projection_from_point n p V H) = pv_complex_dim V.
Proof. admit. Admitted.
   CAG zero-dependent Admitted projection_dim theories/Projective/ProjectionConeChordal.v:40 END *)

(** Generic projection preserves degree. *)
(* CAG zero-dependent Admitted degree_of_projection theories/Projective/ProjectionConeChordal.v:48 BEGIN
Theorem degree_of_projection : forall (n : nat) (p : Cn (n+1)) (V : ProjectiveVariety)
    (H : pv_ambient_dim V = n),
    degree_of (projection_from_point n p V H) = degree_of V.
Proof. admit. Admitted.
   CAG zero-dependent Admitted degree_of_projection theories/Projective/ProjectionConeChordal.v:48 END *)

(* ================================================================== *)
(** * 2. Cone over a variety                                           *)
(* ================================================================== *)

(** The cone p*V: union of lines through p meeting V. *)
(* CAG zero-dependent Parameter cone_variety theories/Projective/ProjectionConeChordal.v:57 BEGIN
Parameter cone_variety : forall (n : nat) (p : Cn (n+1))
    (V : ProjectiveVariety),
    pv_ambient_dim V = n ->
    ProjectiveVariety.
   CAG zero-dependent Parameter cone_variety theories/Projective/ProjectionConeChordal.v:57 END *)

(** The cone has dimension = dim V + 1. *)
(* CAG zero-dependent Admitted cone_dim theories/Projective/ProjectionConeChordal.v:62 BEGIN
Theorem cone_dim : forall (n : nat) (p : Cn (n+1)) (V : ProjectiveVariety)
    (H : pv_ambient_dim V = n),
    pv_complex_dim (cone_variety n p V H) = pv_complex_dim V + 1.
Proof. admit. Admitted.
   CAG zero-dependent Admitted cone_dim theories/Projective/ProjectionConeChordal.v:62 END *)

(** Degree of the cone equals degree of V. *)
(* CAG zero-dependent Admitted degree_of_cone theories/Projective/ProjectionConeChordal.v:72 BEGIN
Theorem degree_of_cone : forall (n : nat) (p : Cn (n+1)) (V : ProjectiveVariety)
    (H : pv_ambient_dim V = n),
    degree_of (cone_variety n p V H) = degree_of V.
Proof. admit. Admitted.
   CAG zero-dependent Admitted degree_of_cone theories/Projective/ProjectionConeChordal.v:72 END *)

(** The cone is algebraic.

    NOTE: this statement is /tautological/: [cone_variety] already returns
    an inhabitant of the bundled record [ProjectiveVariety], and being a
    [ProjectiveVariety] /is/ being algebraic (the predicate [pv_mem]
    cuts out a Zariski-closed subset of [Cⁿ⁺¹]).  The original
    [Theorem ... True. Proof. exact I. Qed.] form added no information.
    Removed γ R37 — the bundled-Record return type already encodes
    algebraicity (Griffiths–Harris Ch. 1.1; Mumford Lec. 4 on Chow's
    theorem for incidence correspondences). *)

(** Packaged theorem. *)
(* CAG zero-dependent Theorem degree_of_projection_and_cone theories/Projective/ProjectionConeChordal.v:86 BEGIN
Theorem degree_of_projection_and_cone : forall (n : nat) (p : Cn (n+1))
    (V : ProjectiveVariety) (H : pv_ambient_dim V = n),
    degree_of (projection_from_point n p V H) = degree_of V /\
    degree_of (cone_variety n p V H) = degree_of V.
Proof.
  intros n p V H.
  split.
  - apply degree_of_projection.
  - apply degree_of_cone.
Qed.
   CAG zero-dependent Theorem degree_of_projection_and_cone theories/Projective/ProjectionConeChordal.v:86 END *)

(* ================================================================== *)
(** * 3. Chordal / secant variety                                      *)
(* ================================================================== *)

(** The chordal variety C(V): closure of union of secant lines and
    tangent lines to V. *)
(* CAG zero-dependent Parameter chordal_variety theories/Projective/ProjectionConeChordal.v:103 BEGIN
(* CAG zero-dependent Parameter chordal_variety theories/Projective/ProjectionConeChordal.v:103 BEGIN
Parameter chordal_variety : ProjectiveVariety -> ProjectiveVariety.
   CAG zero-dependent Parameter chordal_variety theories/Projective/ProjectionConeChordal.v:103 END *)
   CAG zero-dependent Parameter chordal_variety theories/Projective/ProjectionConeChordal.v:103 END *)

(** C(V) is algebraic.

    NOTE: tautological — [chordal_variety] returns a [ProjectiveVariety],
    so [C(V)] inhabits the bundled algebraic structure by typing.
    Removed γ R37 (Griffiths–Harris Ch. 1.1 on the incidence
    correspondence; Chow's theorem giving algebraicity from the
    analytic definition is itself stated as [chow_theorem] in
    [Projective/FunctionFields.v]). *)

(** dim C(V) ≤ 2·dim(V) + 1 (dimension count on incidence variety). *)
(* CAG zero-dependent Admitted chordal_dim_bound theories/Projective/ProjectionConeChordal.v:113 BEGIN
Theorem chordal_dim_bound : forall (V : ProjectiveVariety),
    (pv_complex_dim (chordal_variety V) <= 2 * pv_complex_dim V + 1)%nat.
Proof. admit. Admitted.
   CAG zero-dependent Admitted chordal_dim_bound theories/Projective/ProjectionConeChordal.v:113 END *)

(* ================================================================== *)
(** * 4. Embedding into P^{2k+1}                                      *)
(* ================================================================== *)

(** If n > 2k+1, projection from a point outside C(V) is an isomorphism
    of V onto its image → V embeds into P^{n-1}.
    Iterating, V embeds into P^{2k+1}. *)
(* CAG zero-dependent Admitted embedding_into_P2k1 theories/Projective/ProjectionConeChordal.v:127 BEGIN
Theorem embedding_into_P2k1 : forall (V : ProjectiveVariety),
    (** there exists a projective embedding V ↪ P^{2·dim(V)+1} — axiomatized *)
    exists W : ProjectiveVariety,
    pv_ambient_dim W = 2 * pv_complex_dim V + 1 /\
    degree_of W = degree_of V.
Proof. admit. Admitted.
   CAG zero-dependent Admitted embedding_into_P2k1 theories/Projective/ProjectionConeChordal.v:127 END *)

(** Packaged corollary. *)
Definition any_smooth_k_dim_variety_embeds_in_P2k1
    (V : ProjectiveVariety) : Prop :=
  exists W : ProjectiveVariety,
  pv_ambient_dim W = 2 * pv_complex_dim V + 1.
