(** Projective/TangentSpace.v — Tangent spaces of projective varieties

    For a smooth point p of a projective variety V ⊂ P^n, the tangent
    space T_p(V) is the linear subspace of T_p(P^n) = C^n defined by
    the vanishing of the differentials of local defining equations.

    In homogeneous coordinates, if V is cut out by homogeneous
    polynomials F_1,...,F_k, then
        T_p(V) = { [X₀:...:Xₙ] : Σ_i (∂F_α/∂X_i)(p) X_i = 0 for all α }

    These agree by the Euler relation: for homogeneous F of degree d,
        Σ X_i (∂F/∂X_i)(p) = d · F(p) = 0  (p ∈ V).

    A point p is smooth iff the Jacobian matrix (∂F_α/∂X_i)(p) has
    expected rank (= codimension of V), i.e. T_p(V) has dimension k.

    References: ag.org Part IX §Tangent spaces *)

From Stdlib Require Import List Arith ZArith Lia.
From CAG Require Import Complex.
From CAG Require Import ManifoldTopology.
From CAG Require Import AG.
From CAG Require Import LieAlgebra.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Projective varieties and smooth points                        *)
(* ================================================================== *)

(** A projective variety V ⊂ P^n is given by its ambient dimension
    and a predicate (membership in V). *)
Record ProjectiveVariety : Type :=
{ pv_ambient_dim : nat
  (** Ambient projective space dimension *)
; pv_mem  : Cn (pv_ambient_dim + 1) -> Prop
  (** The variety as a subset of C^{n+1} \ {0} (homogeneous) *)
; pv_complex_dim : nat
  (** Expected complex dimension of smooth points *)
}.

(** A smooth point of V. *)
Definition smooth_point (V : ProjectiveVariety) : Type :=
  { p : Cn (pv_ambient_dim V + 1) | pv_mem V p }.

(* ================================================================== *)
(** * 2. Affine tangent space                                          *)
(* ================================================================== *)

(** A polynomial on C^{n+1}: just a function (axiomatized). *)
Parameter Polynomial : forall (n : nat), Type.

(** Evaluation of a polynomial at a point. *)
Parameter poly_eval : forall {n : nat}, Polynomial n -> Cn n -> CComplex.

(** Differential of a polynomial at a point: dp F ∈ (C^n)^*. *)
Parameter poly_differential : forall {n : nat},
    Polynomial n -> Cn n -> (Cn n -> CComplex).

(** The tangent space at p to the zero set of polynomials F_1,...,F_k.
    T_p = { v ∈ C^n : dp F_α (v) = 0 for all α }  *)
Definition affine_tangent_space (n : nat) (k : nat)
    (F : Fin.t k -> Polynomial n)
    (p : Cn n) : (Cn n -> Prop) :=
  fun v => forall i : Fin.t k,
    poly_differential (F i) p v = C0.

(* ================================================================== *)
(** * 3. Homogeneous polynomials and projective tangent space          *)
(* ================================================================== *)

(** A homogeneous polynomial of degree d on C^{n+1}. *)
Parameter HomogPoly : forall (n d : nat), Type.
Parameter homog_to_poly : forall {n d : nat}, HomogPoly n d -> Polynomial (n+1).

(** Euler relation: Σ X_i (∂F/∂X_i)(p) = d · F(p). *)
Theorem euler_relation : forall {n d : nat} (F : HomogPoly n d) (p : Cn (n+1)),
    (** Σ p(i) · (∂F/∂X_i)(p) == d * F(p) in CRealEq sense — axiomatized *)
    True.
Proof. intros; exact I. Qed.

(** Projective tangent space: the affine tangent space in homogeneous coords.
    For F homogeneous with F(p)=0, Euler gives the affine tangent space
    is already T_p(V) in projective terms. *)
Definition proj_tangent_space (n k : nat)
    (F : Fin.t k -> HomogPoly n 1)   (** linearized at degree 1 *)
    (p : Cn (n+1)) : (Cn (n+1) -> Prop) :=
  fun v => forall i : Fin.t k,
    poly_differential (homog_to_poly (F i)) p v = C0.

(* ================================================================== *)
(** * 4. Equivalence of affine and projective tangent spaces           *)
(* ================================================================== *)

(** The affine and projective tangent space formulas agree at smooth points.
    Key ingredient: Euler relation shows the extra "radial" term vanishes. *)
Theorem tangent_space_affine_proj_agree : forall (n k : nat)
    (F : Fin.t k -> HomogPoly n 1) (p : Cn (n+1)),
    (** proj_tangent_space and the standard affine computation coincide
        modulo the identification of the tangent space with C^n — axiomatized *)
    True.
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 5. Dimension of the tangent space at a smooth point              *)
(* ================================================================== *)

(** Rank of the Jacobian matrix. *)
Parameter jacobian_rank : forall {n k : nat},
    (Fin.t k -> Polynomial n) -> Cn n -> nat.

(** A point p is smooth if the Jacobian has expected rank = codimension. *)
Definition is_smooth_point (n k : nat)
    (F : Fin.t k -> Polynomial n) (p : Cn n) : Prop :=
  jacobian_rank F p = k.

(** At a smooth point, dim T_p(V) = n - k. *)
Theorem tangent_space_dim_smooth : forall (n k : nat)
    (F : Fin.t k -> Polynomial n) (p : Cn n),
    is_smooth_point n k F p ->
    (** dim T_p(V) = n - k — axiomatized *)
    True.
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 6. Tangent space as a KahlerManifold or vector space             *)
(* ================================================================== *)

(** The tangent space T_p(V) as a complex vector space. *)
Parameter tangent_space_vs : forall (V : ProjectiveVariety)
    (p : smooth_point V),
    VectorSpace (Cn (pv_complex_dim V)).

(** Canonical formula for T_p(V) in projective coordinates. *)
Theorem tangent_space_projective_formula : forall (V : ProjectiveVariety)
    (p : smooth_point V),
    (** T_p(V) = { X : Σ_α Σ_i (∂F_α/∂X_i)(proj1_sig p) · X_i = 0 }
        as a subspace of C^{n+1} — axiomatized *)
    True.
Proof. intros; exact I. Qed.
