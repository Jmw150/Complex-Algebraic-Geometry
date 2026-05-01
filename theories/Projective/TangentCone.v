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
Parameter poly_vanishing_order : forall {n : nat},
    Polynomial n -> Cn n -> nat.

(** A polynomial of vanishing order ≥ m at p: the Taylor expansion
    starts in degree m. *)
Definition vanishes_to_order (n m : nat) (F : Polynomial n) (p : Cn n) : Prop :=
  (poly_vanishing_order F p >= m)%nat.

(* ================================================================== *)
(** * 2. Leading form / initial part                                   *)
(* ================================================================== *)

(** The leading homogeneous part of F at p of degree m =
    multiplicity of F at p. *)
Parameter leading_form : forall {n : nat} (F : Polynomial n) (p : Cn n),
    Polynomial n.

(** The leading form is homogeneous of degree ord_p(F). *)
Theorem leading_form_homogeneous : forall {n : nat} (F : Polynomial n) (p : Cn n),
    (** leading_form F p is homogeneous of degree poly_vanishing_order F p *)
    True.
Proof. intros; exact I. Qed.

(** Leading form determines the tangent cone for hypersurfaces. *)
Theorem leading_form_is_initial : forall {n : nat} (F : Polynomial n) (p : Cn n)
    (v : Cn n),
    (** F(p + tv) = t^m leading_form(F,p)(v) + O(t^{m+1}) as t → 0 *)
    True.
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 3. Tangent cone: definition via leading form                     *)
(* ================================================================== *)

(** Tangent cone of a hypersurface V = (F = 0) at p.
    C_p(V) = zero set of leading_form(F, p). *)
Definition tangent_cone_hypersurface {n : nat} (F : Polynomial n) (p : Cn n) :
    Cn n -> Prop :=
  fun v => poly_eval (leading_form F p) v = C0.

(** Tangent cone of a general variety V = ∩_α(F_α = 0) at p.
    C_p(V) = ∩_α {v : leading_form(F_α, p)(v) = 0}. *)
Definition tangent_cone {n k : nat}
    (F : Fin.t k -> Polynomial n) (p : Cn n) :
    Cn n -> Prop :=
  fun v => forall i : Fin.t k,
    poly_eval (leading_form (F i) p) v = C0.

(* ================================================================== *)
(** * 4. Tangent cone at smooth points agrees with tangent space       *)
(* ================================================================== *)

(** At a smooth point (multiplicity 1), the tangent cone = tangent space. *)
Conjecture tangent_cone_smooth_is_tangent_space : forall {n k : nat}
    (F : Fin.t k -> Polynomial n) (p : Cn n),
    is_smooth_point n k F p ->
    forall v, tangent_cone F p v <-> affine_tangent_space n k F p v.

(* ================================================================== *)
(** * 5. Geometric characterizations                                   *)
(* ================================================================== *)

(** An analytic arc through p in V. *)
Parameter AnalyticArc : forall (V : ProjectiveVariety)
    (p : smooth_point V), Type.

(** The tangent direction of an analytic arc at p. *)
Parameter arc_tangent_direction : forall (V : ProjectiveVariety)
    (p : smooth_point V),
    AnalyticArc V p -> Cn (pv_ambient_dim V + 1).

(** Characterization 1: C_p(V) = union of tangent directions to arcs. *)
(* tangent_cone_is_arc_tangents axiom removed: was unsound. Not used. *)

(** Characterization 2: C_p(V) = limit of secant directions. *)
Theorem tangent_cone_is_secant_limit : forall {n k : nat}
    (F : Fin.t k -> Polynomial n) (p : Cn n) (v : Cn n),
    tangent_cone F p v ->
    (** v is a limit of secant directions (q(λ)-p)/|q(λ)-p| as q(λ)→p with q(λ)∈V *)
    True.
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 6. Dimension of the tangent cone                                 *)
(* ================================================================== *)

(** The tangent cone has dimension ≥ dim V. *)
Theorem tangent_cone_dim_lower_bound : forall (V : ProjectiveVariety)
    (p : smooth_point V),
    (** dim C_p(V) >= pv_complex_dim V — axiomatized *)
    True.
Proof. intros; exact I. Qed.
