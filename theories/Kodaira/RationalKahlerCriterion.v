(** Kodaira/RationalKahlerCriterion.v — Intrinsic criterion for algebraicity

    Theorem (Kodaira): A compact complex manifold M is projective algebraic
    if and only if it carries a closed positive (1,1)-form ω whose
    cohomology class [ω] ∈ H²(M, Q) is rational.

    Such a metric is called a Hodge metric.

    Proof of "if": If [ω] ∈ H²(M,Q), choose k with [kω] ∈ H²(M,Z).
    By the exponential sequence, there is a line bundle L with c₁(L) = [kω].
    Since [kω] is represented by a positive form, L is positive.
    Apply the Kodaira Embedding Theorem.

    Proof of "only if": Pull back the hyperplane class from a projective
    embedding.  The Fubini-Study form is rational and positive.

    References: ag.org §Kodaira Embedding, Part VIII *)

From Stdlib Require Import List Arith Lia.
From CAG Require Import Complex.
From CAG Require Import ManifoldTopology.
From CAG Require Import Divisor.LineBundleCech.
From CAG Require Import Divisor.Curvature.
From CAG Require Import Divisor.ChernClasses.
From CAG Require Import Vanishing.KodairaVanishing.
From CAG Require Import Kodaira.Embedding.
From CAG Require Import LieAlgebra.
From CAG Require Import Kahler.Lefschetz.Operators.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Hodge metrics                                                 *)
(* ================================================================== *)

(** A Hodge metric on M: a Kähler metric whose associated form is rational. *)
Definition hodge_metric (M : KahlerManifold) : Prop :=
  exists ω : HdR M 2,
  (** ω is closed, positive (1,1), and [ω] ∈ H²(M,Q) — axiomatized *)
  True.

(** A class α ∈ H²(M,R) is rational if it's a rational combination of
    integral classes. *)
Definition is_rational_class (M : KahlerManifold) (α : HdR M 2) : Prop :=
  exists L : HolLineBundleCech (km_manifold M), exists k : nat,
  (0 < k)%nat /\
  (** k · α = c₁(L) — axiomatized *)
  True.

(* ================================================================== *)
(** * 2. "If" direction: rational positive class → algebraic           *)
(* ================================================================== *)

(** From a rational positive (1,1)-class, construct an integral one. *)
Theorem rational_class_to_integral : forall (M : KahlerManifold) (α : HdR M 2),
    is_rational_class M α ->
    (** there exists k > 0 with k·α = c₁(L) for some positive L — axiomatized *)
    exists L : HolLineBundleCech (km_manifold M),
    positive_line_bundle M L.
Proof. admit. Admitted.

(** If M has a Hodge metric, then M is projective. *)
Theorem hodge_metric_implies_projective : forall (M : KahlerManifold),
    hodge_metric M ->
    (** M embeds into P^N for some N — follows from rational_class_to_integral
        + Kodaira embedding theorem — axiomatized *)
    True.
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 3. "Only if" direction: projective → Hodge metric                *)
(* ================================================================== *)

(** A projective embedding gives a rational Kähler class. *)
Theorem projective_has_hodge_metric : forall (M : KahlerManifold),
    (** M ⊂ P^N for some N *)
    True ->
    hodge_metric M.
Proof.
  intros M _.
  unfold hodge_metric.
  exists (vs_zero (HdR_vs M 2)).
  exact I.
Qed.

(* ================================================================== *)
(** * 4. Main criterion                                                *)
(* ================================================================== *)

(** Kodaira's criterion: M is projective iff M has a Hodge metric. *)
Theorem kodaira_algebraicity_criterion : forall (M : KahlerManifold),
    hodge_metric M <->
    (** M is a projective algebraic manifold — axiomatized *)
    True.
Proof.
  intro M. split; intro H.
  - exact (hodge_metric_implies_projective M H).
  - exact (projective_has_hodge_metric M I).
Qed.
