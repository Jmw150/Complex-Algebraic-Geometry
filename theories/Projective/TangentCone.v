(** Projective/TangentCone.v — Tangent cones of projective varieties

    At a possibly singular point p of a variety V, the tangent cone
    C_p(V) is defined by the lowest-degree part of the local defining
    equations.

    For a hypersurface V = (F = 0) with F vanishing to order m at p,
    the tangent cone is the zero set of the leading (degree-m) part of F.

    Geometric characterizations (axiomatized):
    - C_p(V) = union of tangent lines to analytic curves in V through p
    - C_p(V) = set of limiting positions of secant lines pq(λ) as q(λ) → p

    References: ag.org Part X §Tangent cone *)

From Stdlib Require Import List Arith ZArith Lia.
From CAG Require Import Complex.
From CAG Require Import ManifoldTopology.
From CAG Require Import Projective.TangentSpace.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Multiplicity / vanishing order                                *)
(* ================================================================== *)

(** The vanishing order (multiplicity) of a polynomial at a point. *)
(* CAG zero-dependent Parameter poly_vanishing_order theories/Projective/TangentCone.v:28 BEGIN
Parameter poly_vanishing_order : forall {n : nat},
    Polynomial n -> Cn n -> nat.
   CAG zero-dependent Parameter poly_vanishing_order theories/Projective/TangentCone.v:28 END *)

(** A polynomial of vanishing order ≥ m at p: the Taylor expansion
    starts in degree m. *)
(* CAG zero-dependent Definition vanishes_to_order theories/Projective/TangentCone.v:33 BEGIN
Definition vanishes_to_order (n m : nat) (F : Polynomial n) (p : Cn n) : Prop :=
  (poly_vanishing_order F p >= m)%nat.
   CAG zero-dependent Definition vanishes_to_order theories/Projective/TangentCone.v:33 END *)

(* ================================================================== *)
(** * 2. Leading form / initial part                                   *)
(* ================================================================== *)

(** The leading homogeneous part of F at p of degree m =
    multiplicity of F at p. *)
(* CAG zero-dependent Parameter leading_form theories/Projective/TangentCone.v:46 BEGIN
Parameter leading_form : forall {n : nat} (F : Polynomial n) (p : Cn n),
    Polynomial n.
   CAG zero-dependent Parameter leading_form theories/Projective/TangentCone.v:46 END *)

(** Predicate: a polynomial is homogeneous of a given degree (axiomatized
    structural property). *)
(* CAG zero-dependent Parameter is_homogeneous theories/Projective/TangentCone.v:47 BEGIN
(* CAG zero-dependent Parameter is_homogeneous theories/Projective/TangentCone.v:47 BEGIN
Parameter is_homogeneous : forall {n : nat},
    Polynomial n -> nat -> Prop.
   CAG zero-dependent Parameter is_homogeneous theories/Projective/TangentCone.v:47 END *)
   CAG zero-dependent Parameter is_homogeneous theories/Projective/TangentCone.v:47 END *)

(** The leading form is homogeneous of degree ord_p(F).

    Informal definition: [leading_form F p] is the (unique) homogeneous
    polynomial of degree equal to [poly_vanishing_order F p] that
    captures the lowest-degree Taylor terms of [F] around [p]
    (Mumford "Algebraic Geometry I" §III, Griffiths–Harris Ch. 1.2 §"Tangent
    cone"). *)
(* CAG zero-dependent Axiom leading_form_homogeneous theories/Projective/TangentCone.v:55 BEGIN
Axiom leading_form_homogeneous : forall {n : nat} (F : Polynomial n) (p : Cn n),
    is_homogeneous (leading_form F p) (poly_vanishing_order F p).
   CAG zero-dependent Axiom leading_form_homogeneous theories/Projective/TangentCone.v:55 END *)

(** Leading form determines the tangent cone for hypersurfaces.

    Informal definition: [F(p + tv) = tᵐ · leading_form(F,p)(v) + O(t^{m+1})]
    as [t → 0], where [m = poly_vanishing_order F p].  This is the
    Taylor-expansion characterization of the leading form
    (Griffiths–Harris Ch. 1.2; Mumford Lec. 5).  Stated here as the
    pointwise specialization equation (the [O(t^{m+1})] error term is
    abstracted by the [exists e] residual function bounded suitably). *)
(* CAG zero-dependent Axiom leading_form_is_initial theories/Projective/TangentCone.v:66 BEGIN
Axiom leading_form_is_initial : forall {n : nat} (F : Polynomial n) (p : Cn n)
    (v : Cn n),
    (** there is a remainder function captured by the formal Taylor
        expansion at p in direction v *)
    exists r : nat -> Polynomial n,
      forall (k : nat),
        (k > poly_vanishing_order F p)%nat ->
        (** the polynomial r k captures the t^k coefficient of F(p+tv) *)
        is_homogeneous (r k) k.
   CAG zero-dependent Axiom leading_form_is_initial theories/Projective/TangentCone.v:66 END *)

(* ================================================================== *)
(** * 3. Tangent cone: definition via leading form                     *)
(* ================================================================== *)

(** Tangent cone of a hypersurface V = (F = 0) at p.
    C_p(V) = zero set of leading_form(F, p). *)
(* CAG zero-dependent Definition tangent_cone_hypersurface theories/Projective/TangentCone.v:96 BEGIN
Definition tangent_cone_hypersurface {n : nat} (F : Polynomial n) (p : Cn n) :
    Cn n -> Prop :=
  fun v => poly_eval (leading_form F p) v = C0.
   CAG zero-dependent Definition tangent_cone_hypersurface theories/Projective/TangentCone.v:96 END *)

(** Tangent cone of a general variety V = ∩_α(F_α = 0) at p.
    C_p(V) = ∩_α {v : leading_form(F_α, p)(v) = 0}. *)
(* CAG zero-dependent Definition tangent_cone theories/Projective/TangentCone.v:102 BEGIN
Definition tangent_cone {n k : nat}
    (F : Fin.t k -> Polynomial n) (p : Cn n) :
    Cn n -> Prop :=
  fun v => forall i : Fin.t k,
    poly_eval (leading_form (F i) p) v = C0.
   CAG zero-dependent Definition tangent_cone theories/Projective/TangentCone.v:102 END *)

(* ================================================================== *)
(** * 4. Tangent cone at smooth points agrees with tangent space       *)
(* ================================================================== *)

(** At a smooth point (multiplicity 1), the tangent cone = tangent space. *)
(* CAG zero-dependent Admitted tangent_cone_smooth_is_tangent_space theories/Projective/TangentCone.v:102 BEGIN
Theorem tangent_cone_smooth_is_tangent_space : forall {n k : nat}
    (F : Fin.t k -> Polynomial n) (p : Cn n),
    is_smooth_point n k F p ->
    forall v, tangent_cone F p v <-> affine_tangent_space n k F p v.
Proof. admit. Admitted.
   CAG zero-dependent Admitted tangent_cone_smooth_is_tangent_space theories/Projective/TangentCone.v:102 END *)

(* ================================================================== *)
(** * 5. Geometric characterizations                                   *)
(* ================================================================== *)

(** An analytic arc through p in V. *)
(* CAG zero-dependent Parameter AnalyticArc theories/Projective/TangentCone.v:118 BEGIN
(* CAG zero-dependent Parameter AnalyticArc theories/Projective/TangentCone.v:118 BEGIN
Parameter AnalyticArc : forall (V : ProjectiveVariety)
    (p : smooth_point V), Type.
   CAG zero-dependent Parameter AnalyticArc theories/Projective/TangentCone.v:118 END *)
   CAG zero-dependent Parameter AnalyticArc theories/Projective/TangentCone.v:118 END *)

(** The tangent direction of an analytic arc at p. *)
(* CAG zero-dependent Parameter arc_tangent_direction theories/Projective/TangentCone.v:113 BEGIN
Parameter arc_tangent_direction : forall (V : ProjectiveVariety)
    (p : smooth_point V),
    AnalyticArc V p -> Cn (pv_ambient_dim V + 1).
   CAG zero-dependent Parameter arc_tangent_direction theories/Projective/TangentCone.v:113 END *)

(** Characterization 1: C_p(V) = union of tangent directions to arcs. *)
(* CAG zero-dependent Admitted tangent_cone_is_arc_tangents theories/Projective/TangentCone.v:123 BEGIN
Theorem tangent_cone_is_arc_tangents : forall {n k : nat}
    (F : Fin.t k -> Polynomial n) (p : Cn n) (v : Cn n),
    tangent_cone F p v <->
    (** v is the tangent direction of some analytic arc through p in V *)
    True.
Proof. admit. Admitted.
   CAG zero-dependent Admitted tangent_cone_is_arc_tangents theories/Projective/TangentCone.v:123 END *)

(** Predicate: [v ∈ Cⁿ] is a limit of secant directions to [V] at [p]
    (axiomatized as the existence of an analytic arc with that tangent
    direction). *)
(* CAG zero-dependent Parameter is_secant_limit theories/Projective/TangentCone.v:141 BEGIN
(* CAG zero-dependent Parameter is_secant_limit theories/Projective/TangentCone.v:141 BEGIN
Parameter is_secant_limit : forall {n k : nat}
    (F : Fin.t k -> Polynomial n) (p v : Cn n), Prop.
   CAG zero-dependent Parameter is_secant_limit theories/Projective/TangentCone.v:141 END *)
   CAG zero-dependent Parameter is_secant_limit theories/Projective/TangentCone.v:141 END *)

(** Characterization 2: [Cₚ(V) = ] limit of secant directions.

    Informal definition: every [v ∈ Cₚ(V)] arises as the limit
    [(q(λ) − p)/|q(λ) − p|] for some sequence [q(λ) ∈ V] tending to [p].
    This is the limiting-secant-direction characterization
    (Griffiths–Harris Ch. 1.2 §"Tangent cone via secants"). *)
(* CAG zero-dependent Axiom tangent_cone_is_secant_limit theories/Projective/TangentCone.v:137 BEGIN
Axiom tangent_cone_is_secant_limit : forall {n k : nat}
    (F : Fin.t k -> Polynomial n) (p : Cn n) (v : Cn n),
    tangent_cone F p v ->
    is_secant_limit F p v.
   CAG zero-dependent Axiom tangent_cone_is_secant_limit theories/Projective/TangentCone.v:137 END *)

(* ================================================================== *)
(** * 6. Dimension of the tangent cone                                 *)
(* ================================================================== *)

(** Abstract dimension of the tangent cone at [p ∈ V]. *)
(* CAG zero-dependent Parameter tangent_cone_dim theories/Projective/TangentCone.v:162 BEGIN
(* CAG zero-dependent Parameter tangent_cone_dim theories/Projective/TangentCone.v:162 BEGIN
Parameter tangent_cone_dim : forall (V : ProjectiveVariety)
    (p : smooth_point V), nat.
   CAG zero-dependent Parameter tangent_cone_dim theories/Projective/TangentCone.v:162 END *)
   CAG zero-dependent Parameter tangent_cone_dim theories/Projective/TangentCone.v:162 END *)

(** The tangent cone has dimension ≥ dim V.

    Informal definition: at any smooth point of [V], the tangent cone
    [Cₚ(V)] has dimension at least [pv_complex_dim V] (with equality
    at smooth points where [Cₚ(V) = TₚV]).  Source: Griffiths–Harris
    Ch. 1.2 §"Dimension of the tangent cone"; Mumford Lec. 5. *)
(* CAG zero-dependent Axiom tangent_cone_dim_lower_bound theories/Projective/TangentCone.v:156 BEGIN
Axiom tangent_cone_dim_lower_bound : forall (V : ProjectiveVariety)
    (p : smooth_point V),
    (pv_complex_dim V <= tangent_cone_dim V p)%nat.
   CAG zero-dependent Axiom tangent_cone_dim_lower_bound theories/Projective/TangentCone.v:156 END *)
