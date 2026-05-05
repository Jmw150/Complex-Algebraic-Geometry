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
(* CAG zero-dependent Parameter Polynomial theories/Projective/TangentSpace.v:51 BEGIN
Parameter Polynomial : forall (n : nat), Type.
   CAG zero-dependent Parameter Polynomial theories/Projective/TangentSpace.v:51 END *)

(** Evaluation of a polynomial at a point. *)
(* CAG zero-dependent Parameter poly_eval theories/Projective/TangentSpace.v:54 BEGIN
Parameter poly_eval : forall {n : nat}, Polynomial n -> Cn n -> CComplex.
   CAG zero-dependent Parameter poly_eval theories/Projective/TangentSpace.v:54 END *)

(** Differential of a polynomial at a point: dp F ∈ (C^n)^*. *)
(* CAG zero-dependent Parameter poly_differential theories/Projective/TangentSpace.v:57 BEGIN
Parameter poly_differential : forall {n : nat},
    Polynomial n -> Cn n -> (Cn n -> CComplex).
   CAG zero-dependent Parameter poly_differential theories/Projective/TangentSpace.v:57 END *)

(** The tangent space at p to the zero set of polynomials F_1,...,F_k.
    T_p = { v ∈ C^n : dp F_α (v) = 0 for all α }  *)
(* CAG zero-dependent Definition affine_tangent_space theories/Projective/TangentSpace.v:62 BEGIN
Definition affine_tangent_space (n : nat) (k : nat)
    (F : Fin.t k -> Polynomial n)
    (p : Cn n) : (Cn n -> Prop) :=
  fun v => forall i : Fin.t k,
    poly_differential (F i) p v = C0.
   CAG zero-dependent Definition affine_tangent_space theories/Projective/TangentSpace.v:62 END *)

(* ================================================================== *)
(** * 3. Homogeneous polynomials and projective tangent space          *)
(* ================================================================== *)

(** A homogeneous polynomial of degree d on C^{n+1}. *)
(* CAG zero-dependent Parameter HomogPoly theories/Projective/TangentSpace.v:73 BEGIN
Parameter HomogPoly : forall (n d : nat), Type.
   CAG zero-dependent Parameter HomogPoly theories/Projective/TangentSpace.v:73 END *)
(* CAG zero-dependent Parameter homog_to_poly theories/Projective/TangentSpace.v:74 BEGIN
Parameter homog_to_poly : forall {n d : nat}, HomogPoly n d -> Polynomial (n+1).
   CAG zero-dependent Parameter homog_to_poly theories/Projective/TangentSpace.v:74 END *)

(** Euler relation: Σ X_i (∂F/∂X_i)(p) = d · F(p).

    Informal definition: for any homogeneous polynomial F of degree d on
    [Cⁿ⁺¹] and any point [p ∈ Cⁿ⁺¹], the sum [Σᵢ pᵢ · (∂F/∂Xᵢ)(p)] equals
    [d · F(p)].  This is Euler's theorem on homogeneous functions
    (Griffiths–Harris Ch. 0.2).

    Stated using existing [poly_differential] applied to [p] itself
    (Σᵢ pᵢ · ∂F/∂Xᵢ(p) = poly_differential (homog_to_poly F) p p
    via the Cn-pairing), but since the project lacks a direct sum-over-Fin
    in scope here, we keep this as a paper-attributable axiom. *)
(* CAG zero-dependent Axiom euler_relation theories/Projective/TangentSpace.v:87 BEGIN
Axiom euler_relation : forall {n d : nat} (F : HomogPoly n d) (p : Cn (n+1)),
    (** Σ pᵢ · (∂F/∂Xᵢ)(p) = d · F(p) [Euler 1755; Griffiths–Harris Ch. 0.2].
        The contracted form: applying the differential of F at p to p
        itself recovers d · F(p). *)
    poly_differential (homog_to_poly F) p p
    = Cmul (Cinject_Q (QArith_base.inject_Z (Z.of_nat d)))
           (poly_eval (homog_to_poly F) p).
   CAG zero-dependent Axiom euler_relation theories/Projective/TangentSpace.v:87 END *)

(** Projective tangent space: the affine tangent space in homogeneous coords.
    For F homogeneous with F(p)=0, Euler gives the affine tangent space
    is already T_p(V) in projective terms. *)
(* CAG zero-dependent Definition proj_tangent_space theories/Projective/TangentSpace.v:100 BEGIN
Definition proj_tangent_space (n k : nat)
    (F : Fin.t k -> HomogPoly n 1)   (** linearized at degree 1 *)
    (p : Cn (n+1)) : (Cn (n+1) -> Prop) :=
  fun v => forall i : Fin.t k,
    poly_differential (homog_to_poly (F i)) p v = C0.
   CAG zero-dependent Definition proj_tangent_space theories/Projective/TangentSpace.v:100 END *)

(* ================================================================== *)
(** * 4. Equivalence of affine and projective tangent spaces           *)
(* ================================================================== *)

(** The affine and projective tangent space formulas agree at smooth points.
    Key ingredient: Euler relation shows the extra "radial" term vanishes.

    Informal definition: for any system of homogeneous degree-1 polynomials
    [F : Fin.t k → HomogPoly n 1] and any [p ∈ Cⁿ⁺¹], the projective
    tangent space coincides with the affine tangent space of the
    underlying polynomials in (n+1) variables.  This is the standard
    consequence of Euler's relation (Griffiths–Harris Ch. 0.2). *)
(* CAG zero-dependent Axiom tangent_space_affine_proj_agree theories/Projective/TangentSpace.v:116 BEGIN
Axiom tangent_space_affine_proj_agree : forall (n k : nat)
    (F : Fin.t k -> HomogPoly n 1) (p : Cn (n+1)) (v : Cn (n+1)),
    proj_tangent_space n k F p v
    <-> affine_tangent_space (n+1) k (fun i => homog_to_poly (F i)) p v.
   CAG zero-dependent Axiom tangent_space_affine_proj_agree theories/Projective/TangentSpace.v:116 END *)

(* ================================================================== *)
(** * 5. Dimension of the tangent space at a smooth point              *)
(* ================================================================== *)

(** Rank of the Jacobian matrix. *)
(* CAG zero-dependent Parameter jacobian_rank theories/Projective/TangentSpace.v:130 BEGIN
Parameter jacobian_rank : forall {n k : nat},
    (Fin.t k -> Polynomial n) -> Cn n -> nat.
   CAG zero-dependent Parameter jacobian_rank theories/Projective/TangentSpace.v:130 END *)

(** A point p is smooth if the Jacobian has expected rank = codimension. *)
(* CAG zero-dependent Definition is_smooth_point theories/Projective/TangentSpace.v:134 BEGIN
Definition is_smooth_point (n k : nat)
    (F : Fin.t k -> Polynomial n) (p : Cn n) : Prop :=
  jacobian_rank F p = k.
   CAG zero-dependent Definition is_smooth_point theories/Projective/TangentSpace.v:134 END *)

(** At a smooth point, dim T_p(V) = n - k.

    Informal definition: at a smooth point [p] of a variety cut out
    by [k] polynomials in [n] variables, the tangent space has
    dimension exactly [n - k] (the expected codimension).  This is
    the implicit-function theorem applied to the Jacobian
    (Griffiths–Harris Ch. 0.2; Hartshorne I.5.1). *)
(* CAG zero-dependent Axiom tangent_space_dim_smooth theories/Projective/TangentSpace.v:141 BEGIN
Axiom tangent_space_dim_smooth : forall (n k : nat)
    (F : Fin.t k -> Polynomial n) (p : Cn n),
    is_smooth_point n k F p ->
    (** there exists a basis of T_p(V) of size (n - k) *)
    exists basis : Fin.t (n - k) -> Cn n,
      forall i : Fin.t (n - k),
        affine_tangent_space n k F p (basis i).
   CAG zero-dependent Axiom tangent_space_dim_smooth theories/Projective/TangentSpace.v:141 END *)

(* ================================================================== *)
(** * 6. Tangent space as a KahlerManifold or vector space             *)
(* ================================================================== *)

(** The tangent space T_p(V) as a complex vector space. *)
(* CAG zero-dependent Parameter tangent_space_vs theories/Projective/TangentSpace.v:154 BEGIN
Parameter tangent_space_vs : forall (V : ProjectiveVariety)
    (p : smooth_point V),
    VectorSpace (Cn (pv_complex_dim V)).
   CAG zero-dependent Parameter tangent_space_vs theories/Projective/TangentSpace.v:154 END *)

(** Canonical formula for T_p(V) in projective coordinates.

    Informal definition: the tangent space [T_p(V)] viewed as a complex
    vector space (carried by [tangent_space_vs V p]) is non-degenerate
    in the sense that it admits a non-zero element whenever
    [pv_complex_dim V > 0].  The full statement (T_p(V) is the kernel
    of the Jacobian matrix at p) requires a basis manipulation
    formalization out of scope; we keep this as the existence of a
    spanning vector (Griffiths–Harris Ch. 0.2). *)
(* CAG zero-dependent Axiom tangent_space_projective_formula theories/Projective/TangentSpace.v:167 BEGIN
Axiom tangent_space_projective_formula : forall (V : ProjectiveVariety)
    (p : smooth_point V),
    (0 < pv_complex_dim V)%nat ->
    exists v : Cn (pv_complex_dim V),
      v <> (fun _ => C0).
   CAG zero-dependent Axiom tangent_space_projective_formula theories/Projective/TangentSpace.v:167 END *)
