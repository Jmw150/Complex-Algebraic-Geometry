(** Divisor/RiemannSurfaceDegree.v — Degree on compact Riemann surfaces

    For a compact Riemann surface M (complex dimension 1):
    - deg D = Σ a_i  for D = Σ a_i · p_i  (sum of coefficients)
    - deg L = ⟨c₁(L), [M]⟩  (pairing with fundamental class)
    - If Θ is the curvature of a connection on L,
        deg L = (i/2π) ∫_M Θ
    - Applied to T'(M): deg T'(M) = χ(M)  (Gauss-Bonnet)

    References: ag.org Part VI §Riemann surface consequences;
    Griffiths–Harris §I.1 ("Compact Riemann surfaces"),
    Forster, *Lectures on Riemann Surfaces*. *)

From Stdlib Require Import List Arith ZArith Lia.
From CAG Require Import Complex.
From CAG Require Import AG.
From CAG Require Import ManifoldTopology.
From CAG Require Import Divisor.LineBundleCech.
From CAG Require Import Divisor.Curvature.
From CAG Require Import Divisor.DivisorBundle.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Riemann surfaces                                              *)
(* ================================================================== *)

(** A compact Riemann surface: a complex manifold of dimension 1. *)
Definition RiemannSurface : Type :=
  { M : ComplexManifold | cm_dim M = 1 }.

Definition rs_manifold (S : RiemannSurface) : ComplexManifold :=
  proj1_sig S.

(** Compactness: an opaque [Prop]-valued predicate.  The genuine
    compactness of [cm_carrier (rs_manifold S)] would require the
    topological-compactness predicate of [Topology.v]; we record
    this as a [Prop]-valued Parameter so [rs_compact S] is a
    meaningful (axiomatic) hypothesis rather than the trivially-true
    [True].  Reference: Forster §1 ("Compact Riemann surfaces"). *)
(* CAG zero-dependent Parameter rs_compact theories/Divisor/RiemannSurfaceDegree.v:41 BEGIN
Parameter rs_compact : RiemannSurface -> Prop.
   CAG zero-dependent Parameter rs_compact theories/Divisor/RiemannSurfaceDegree.v:41 END *)
(** [rs_compact S]: the underlying complex manifold of [S] is
    topologically compact. *)

(* ================================================================== *)
(** * 2. Degree of a divisor                                           *)
(* ================================================================== *)

(** Points on a Riemann surface as divisor components. *)
(** For a Riemann surface, a divisor is a formal integer combination
    of points: D = Σ n_p · {p}. *)

(** Degree of a divisor: sum of integer coefficients. *)
Definition divisor_degree {S : RiemannSurface} (D : Divisor (rs_manifold S)) : Z :=
  List.fold_left (fun acc '(n, _) => Z.add n acc) D 0%Z.

(** Degree is a homomorphism: deg(D + E) = deg D + deg E. *)
Local Notation deg_fold M :=
  (List.fold_left (fun acc (nV : Z * DivisorComponent M) =>
     let '(n, _) := nV in Z.add n acc)).

Lemma deg_fold_linear : forall {M : ComplexManifold}
    (D : Divisor M) (init : Z),
    deg_fold M D init = Z.add (deg_fold M D 0%Z) init.
Proof.
  induction D as [| [n V] D IH]; intro init.
  - simpl. lia.
  - simpl. rewrite IH. rewrite (IH (Z.add n 0%Z)). lia.
Qed.

Lemma divisor_degree_add : forall {S : RiemannSurface}
    (D E : Divisor (rs_manifold S)),
    divisor_degree (add_divisors D E) = Z.add (divisor_degree D) (divisor_degree E).
Proof.
  intros S D E.
  unfold divisor_degree, add_divisors.
  rewrite List.fold_left_app.
  rewrite deg_fold_linear.
  lia.
Qed.

(* ================================================================== *)
(** * 3. Degree of a line bundle                                       *)
(* ================================================================== *)

(** The pairing H²(M,Z) ⊗ H₀(M,Z) → Z on a compact oriented surface. *)
(* CAG zero-dependent Parameter H2Z_pair_surface theories/Divisor/RiemannSurfaceDegree.v:89 BEGIN
Parameter H2Z_pair_surface : forall {S : RiemannSurface},
    H2Z (rs_manifold S) -> Z.
   CAG zero-dependent Parameter H2Z_pair_surface theories/Divisor/RiemannSurfaceDegree.v:89 END *)

(** [H2Z_pair_surface] is a group homomorphism on the [H2Z M]
    additive structure.  Reference: Griffiths–Harris §I.1
    "Cohomology pairing on a compact surface". *)
(* CAG zero-dependent Axiom H2Z_pair_surface_add theories/Divisor/RiemannSurfaceDegree.v:95 BEGIN
Axiom H2Z_pair_surface_add :
  forall {S : RiemannSurface} (a b : H2Z (rs_manifold S)),
  H2Z_pair_surface (H2Z_add a b)
  = Z.add (H2Z_pair_surface a) (H2Z_pair_surface b).
   CAG zero-dependent Axiom H2Z_pair_surface_add theories/Divisor/RiemannSurfaceDegree.v:95 END *)
(** [H2Z_pair_surface] is additive: pairs the cohomology
    addition with [Z.add]. *)

(** Degree of a line bundle: deg L = ⟨c₁(L), [M]⟩. *)
(* CAG zero-dependent Definition line_bundle_degree theories/Divisor/RiemannSurfaceDegree.v:105 BEGIN
Definition line_bundle_degree {S : RiemannSurface}
    (L : HolLineBundleCech (rs_manifold S)) : Z :=
  H2Z_pair_surface (c1_map L).
   CAG zero-dependent Definition line_bundle_degree theories/Divisor/RiemannSurfaceDegree.v:105 END *)

(** Degree is a group homomorphism on Pic.  Provable from
    [c1_tensor] (in [LineBundleCech.v]: c₁(L⊗L') = c₁(L) + c₁(L'))
    and [H2Z_pair_surface_add] above. *)
(* CAG zero-dependent Theorem degree_tensor theories/Divisor/RiemannSurfaceDegree.v:110 BEGIN
Theorem degree_tensor : forall {S : RiemannSurface}
    (L L' : HolLineBundleCech (rs_manifold S)),
    line_bundle_degree (hlb_tensor L L') =
    Z.add (line_bundle_degree L) (line_bundle_degree L').
Proof.
  intros S L L'.
  unfold line_bundle_degree.
  rewrite c1_tensor.
  apply H2Z_pair_surface_add.
Qed.
   CAG zero-dependent Theorem degree_tensor theories/Divisor/RiemannSurfaceDegree.v:110 END *)

(** deg[D] = deg D: the degree of the divisor bundle equals the
    degree of the divisor.  Famous-classical (Griffiths–Harris
    §I.3 "Divisor degree on a Riemann surface").  Recorded as a
    Conjecture: requires the [c1_map LB[D] = sum of point-classes]
    identity at the [H2Z] level, which the Phase-E-2 degenerate
    [c1_map ≡ 0] / [LB[D] ≡ trivial] model collapses to
    [0 = divisor_degree D], which is FALSE in general. *)
(* CAG zero-dependent Conjecture degree_divisor_bundle theories/Divisor/RiemannSurfaceDegree.v:128 BEGIN
Conjecture degree_divisor_bundle : forall {S : RiemannSurface}
    (D : Divisor (rs_manifold S)),
    line_bundle_degree LB[D] = divisor_degree D.
   CAG zero-dependent Conjecture degree_divisor_bundle theories/Divisor/RiemannSurfaceDegree.v:128 END *)

(* ================================================================== *)
(** * 4. Degree via curvature integral                                 *)
(* ================================================================== *)

(** Integration over M: the fundamental class pairing for a Riemann surface. *)
(* CAG zero-dependent Parameter integrate_RS theories/Divisor/RiemannSurfaceDegree.v:130 BEGIN
Parameter integrate_RS : forall {S : RiemannSurface},
    PQForm 1 1 1 -> CComplex.
   CAG zero-dependent Parameter integrate_RS theories/Divisor/RiemannSurfaceDegree.v:130 END *)

(** Degree via curvature: if Θ is the Chern curvature of a Hermitian
    metric on L, then [deg L = (i/2π) ∫_M Θ].  Famous-classical
    (Griffiths–Harris §I.3 "Curvature represents c₁",
    Chern–Weil theory).  The genuine identity requires the
    de-Rham comparison map [HdR M 2 → ℝ] composed with the
    integration form; left as a Conjecture per famous-old. *)
(* CAG zero-dependent Conjecture degree_equals_curvature_integral theories/Divisor/RiemannSurfaceDegree.v:148 BEGIN
Conjecture degree_equals_curvature_integral : forall {S : RiemannSurface}
    (L : HolLineBundleCech (rs_manifold S))
    (h : HermitianMetric (rs_manifold S) L),
  exists Θ : PQForm (cm_dim (rs_manifold S)) 1 1,
    Θ = hermitian_curvature L h.
   CAG zero-dependent Conjecture degree_equals_curvature_integral theories/Divisor/RiemannSurfaceDegree.v:148 END *)
(** Existence-of-curvature-form slot for [deg L = (i/2π) ∫_M Θ];
    the genuine identity needs the [PQForm → CComplex → Z]
    integration pairing. *)

(* ================================================================== *)
(** * 5. Gauss-Bonnet: deg T'(M) = χ(M)                               *)
(* ================================================================== *)

(** The holomorphic tangent bundle T'(M) of a Riemann surface. *)
(* CAG zero-dependent Parameter tangent_bundle_RS theories/Divisor/RiemannSurfaceDegree.v:166 BEGIN
Parameter tangent_bundle_RS : forall (S : RiemannSurface),
    HolLineBundleCech (rs_manifold S).
   CAG zero-dependent Parameter tangent_bundle_RS theories/Divisor/RiemannSurfaceDegree.v:166 END *)

(** The Euler characteristic χ(M) = 2 - 2g for a genus-g surface. *)
(* CAG zero-dependent Parameter euler_char theories/Divisor/RiemannSurfaceDegree.v:172 BEGIN
Parameter euler_char : RiemannSurface -> Z.
   CAG zero-dependent Parameter euler_char theories/Divisor/RiemannSurfaceDegree.v:172 END *)


(** Gauss-Bonnet: deg T'(M) = χ(M).
    Famous classical (Gauss–Bonnet theorem; Griffiths–Harris §I.3
    "Degree of the tangent bundle").  The integral form
    [∫_M K dA = 2π χ(M)] needs the integration layer.  Conjecture
    per famous-old. *)
(* CAG zero-dependent Conjecture degree_of_tangent_bundle_equals_euler_characteristic theories/Divisor/RiemannSurfaceDegree.v:173 BEGIN
Conjecture degree_of_tangent_bundle_equals_euler_characteristic :
    forall (S : RiemannSurface),
    line_bundle_degree (tangent_bundle_RS S) = euler_char S.
   CAG zero-dependent Conjecture degree_of_tangent_bundle_equals_euler_characteristic theories/Divisor/RiemannSurfaceDegree.v:173 END *)
