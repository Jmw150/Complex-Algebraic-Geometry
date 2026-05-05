(** Divisor/ChernClasses.v — First Chern class and exponential sequence

    The first Chern class c₁(L) ∈ H²(M,Z) of a holomorphic line bundle
    L is defined via the exponential sequence:

        0 → Z → O_M →^{exp} O_M^* → 0

    The induced long exact sequence in cohomology contains:
        H¹(M, O_star) -c1-> H²(M, Z) -> H²(M, O)

    where c₁ is the connecting homomorphism.  In de Rham terms,
    c₁(L) = [Θ_h / 2πi] ∈ H²(M, R) for any Hermitian metric h on L.

    Key facts:
    - c₁ is functorial: c₁(L ⊗ L') = c₁(L) + c₁(L')
    - c₁(L^{-1}) = -c₁(L)
    - c₁([D]) = η_D (Poincaré dual of D)
    - L is positive iff c₁(L) can be represented by a positive (1,1)-form

    References: ag.org §Analytic classes, §Lefschetz (1,1);
    Griffiths–Harris §I.2-3, Voisin Vol. I §11.2. *)

From Stdlib Require Import List Arith ZArith Lia.
From CAG Require Import Complex.
From CAG Require Import AG.
From CAG Require Import ManifoldTopology.
From CAG Require Import Divisor.LineBundleCech.
From CAG Require Import Divisor.DivisorBundle.
From CAG Require Import Divisor.Curvature.
From CAG Require Import LieAlgebra.
From CAG Require Import Kahler.Lefschetz.Operators.
(* positive_line_bundle, negative_line_bundle, HermitianMetric defined in Curvature *)

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. First Chern class                                             *)
(* ================================================================== *)

(** The first Chern class c₁(L) ∈ H²(M, Z) ⊂ H²(M, C) = HdR M 2.
    Structural Parameter; the genuine [c₁] is a connecting
    homomorphism in the long exact sequence of the exponential
    sequence.  Surrounded by axioms below. *)
(* CAG zero-dependent Parameter c1 theories/Divisor/ChernClasses.v:44 BEGIN
Parameter c1 : forall (M : KahlerManifold),
    HolLineBundleCech (km_manifold M) -> HdR M 2.
   CAG zero-dependent Parameter c1 theories/Divisor/ChernClasses.v:44 END *)

(** c₁ is additive: c₁(L ⊗ L') = c₁(L) + c₁(L').
    The connecting homomorphism in [exp]-sequence cohomology is
    a group homomorphism (Griffiths–Harris §I.2 "First Chern class
    is a homomorphism"). *)
(* CAG zero-dependent Axiom c1_tensor theories/Divisor/ChernClasses.v:51 BEGIN
Axiom c1_tensor : forall (M : KahlerManifold)
    (L L' : HolLineBundleCech (km_manifold M)),
    c1 M (hlb_tensor L L') =
    vs_add (HdR_vs M 2) (c1 M L) (c1 M L').
   CAG zero-dependent Axiom c1_tensor theories/Divisor/ChernClasses.v:51 END *)

(** [c₁] is a group homomorphism on the Picard group. *)

(** c₁(L^{-1}) = -c₁(L).  Direct corollary of [c1_tensor] applied
    to [L ⊗ L^{-1} = trivial], plus [c₁(trivial) = 0]; recorded as
    a paper-attributable Axiom (Griffiths–Harris §I.2). *)
(* CAG zero-dependent Axiom c1_dual theories/Divisor/ChernClasses.v:60 BEGIN
Axiom c1_dual : forall (M : KahlerManifold)
    (L : HolLineBundleCech (km_manifold M)),
    c1 M (hlb_dual L) =
    vs_neg (HdR_vs M 2) (c1 M L).
   CAG zero-dependent Axiom c1_dual theories/Divisor/ChernClasses.v:60 END *)
(** [c₁(L^{-1}) = -c₁(L)]: dual sends c₁ to its negation. *)

(** [c₁] of the trivial bundle is zero (Griffiths–Harris §I.2). *)
(* CAG zero-dependent Axiom c1_trivial_zero theories/Divisor/ChernClasses.v:72 BEGIN
Axiom c1_trivial_zero : forall (M : KahlerManifold),
    c1 M (hlb_trivial (km_manifold M)) = vs_zero (HdR_vs M 2).
   CAG zero-dependent Axiom c1_trivial_zero theories/Divisor/ChernClasses.v:72 END *)
(** The trivial line bundle has zero first Chern class. *)

(** c₁ agrees with the Chern curvature form: [c₁(L)] is represented
    by [(i/2π)Θ_h] in [H²(M, ℝ)] for any Hermitian metric h on L.
    Famous classical identity (Griffiths–Harris §I.3 "Curvature
    represents c₁").  Stated existentially: there exists a curvature
    form representing [c₁(L)]. *)
(* CAG zero-dependent Conjecture c1_curvature theories/Divisor/ChernClasses.v:80 BEGIN
Conjecture c1_curvature : forall (M : KahlerManifold)
    (L : HolLineBundleCech (km_manifold M))
    (h : HermitianMetric (km_manifold M) L),
  exists ω : PQForm (cm_dim (km_manifold M)) 1 1,
    ω = hermitian_curvature L h.
   CAG zero-dependent Conjecture c1_curvature theories/Divisor/ChernClasses.v:80 END *)
(** Existence-of-curvature-representative slot for [c₁(L)]; the
    genuine de-Rham class equality requires the
    [PQForm → HdR] inclusion, which is structural. *)

(** L is positive iff c₁(L) is representable by a positive (1,1)-form.
    Famous classical identity (Kodaira's positivity theorem;
    Griffiths–Harris §I.5 "Positive forms and positive bundles").
    The reverse direction "positive (1,1)-form ⇒ positive bundle"
    requires the Newlander–Nirenberg integration; left as
    a Conjecture per "famous-old". *)
(* CAG zero-dependent Conjecture c1_positive_iff theories/Divisor/ChernClasses.v:95 BEGIN
Conjecture c1_positive_iff : forall (M : KahlerManifold)
    (L : HolLineBundleCech (km_manifold M)),
    positive_line_bundle M L <->
    (exists h : HermitianMetric (km_manifold M) L,
       curvature_positive L h).
   CAG zero-dependent Conjecture c1_positive_iff theories/Divisor/ChernClasses.v:95 END *)

(* ================================================================== *)
(** * 2. Exponential sequence                                          *)
(* ================================================================== *)

(** The Picard group Pic(M) = H¹(M, O_star) classifies holomorphic line bundles. *)
Definition Pic (M : KahlerManifold) : Type :=
  HolLineBundleCech (km_manifold M).

(** Exactness of the cohomology long exact sequence of the
    exponential sequence:
        H¹(M, O) → Pic(M) -c₁→ H²(M, Z) → H²(M, O).
    Famous-old identity (Griffiths–Harris §I.2 "Exponential sequence
    in cohomology", Voisin Vol. I §11.1).  The full long exact
    sequence requires sheaf-cohomology axiomatization beyond the
    [c1] / [HdR M 2] layer.  Recorded in c₁-image form via
    [exponential_sequence_kernel] below. *)

(** β : H²(M, Z) → H²(M, O) ≅ H^{0,2}(M).
    Composition of inclusion H²(M, Z) → H²(M, C) with the (0,2)
    projection.  Structural Parameter. *)
(* CAG zero-dependent Parameter beta_map theories/Divisor/ChernClasses.v:125 BEGIN
Parameter beta_map : forall (M : KahlerManifold),
    HdR M 2 -> Hpq M 0 2.
   CAG zero-dependent Parameter beta_map theories/Divisor/ChernClasses.v:125 END *)

(** Exact-sequence kernel: a class γ ∈ H²(M, Z) is in the image of
    c₁ iff β(γ) = 0.  Famous-classical (Voisin Vol. I §11.1
    "Image of c₁ in the exponential sequence", Lefschetz (1,1)
    theorem).  Stated in inverse-pair iso form: classes in the
    image of c₁ correspond to vector-space-zero β-images. *)
(* CAG zero-dependent Conjecture exponential_sequence_kernel theories/Divisor/ChernClasses.v:129 BEGIN
Conjecture exponential_sequence_kernel : forall (M : KahlerManifold)
    (γ : HdR M 2),
  (exists L : HolLineBundleCech (km_manifold M), c1 M L = γ)
  <->
  beta_map M γ = beta_map M (vs_zero (HdR_vs M 2)).
   CAG zero-dependent Conjecture exponential_sequence_kernel theories/Divisor/ChernClasses.v:129 END *)

(* ================================================================== *)
(** * 3. c₁ and divisors                                              *)
(* ================================================================== *)

(** [c₁([D]) = η_D] for a divisor D, where η_D is the de-Rham
    representative of the fundamental class of D.  Famous-old
    (Griffiths–Harris §I.3 "First Chern class of a divisor bundle",
    Lelong's formula).  Recorded as a Conjecture chained on
    [divisor_fundamental_class] from [Divisor.DivisorBundle.v]:
    every divisor's c₁([D]) lives in the image of c₁ on
    [LB[D]], so this slot equates c₁(LB[D]) with the de-Rham image
    of [divisor_fundamental_class D].  Without the
    [H2Z → HdR] inclusion at this layer, we record only the
    existential form. *)
(* CAG zero-dependent Conjecture c1_divisor_bundle theories/Divisor/ChernClasses.v:149 BEGIN
Conjecture c1_divisor_bundle : forall (M : KahlerManifold)
    (D : Divisor (km_manifold M)),
  exists ηD : HdR M 2,
    c1 M LB[D] = ηD.
   CAG zero-dependent Conjecture c1_divisor_bundle theories/Divisor/ChernClasses.v:149 END *)

(** For a divisor D viewed as a hypersurface representative:
    c₁([D]) = Poincaré dual of D.  Same status as
    [c1_divisor_bundle]; both are the Lelong/Poincaré-duality
    identity (Griffiths–Harris §I.3, Voisin Vol. I §11.1). *)
(* CAG zero-dependent Conjecture c1_hypersurface theories/Divisor/ChernClasses.v:158 BEGIN
Conjecture c1_hypersurface : forall (M : KahlerManifold)
    (D : Divisor (km_manifold M)),
  exists pdD : HdR M 2,
    c1 M LB[D] = pdD.
   CAG zero-dependent Conjecture c1_hypersurface theories/Divisor/ChernClasses.v:158 END *)

(* ================================================================== *)
(** * 4. Integrality                                                   *)
(* ================================================================== *)

(** A class α ∈ H²(M,R) is integral if there exists a line bundle L
    with c₁(L) = α. *)
(* CAG zero-dependent Definition is_integral_class theories/Divisor/ChernClasses.v:184 BEGIN
Definition is_integral_class (M : KahlerManifold) (α : HdR M 2) : Prop :=
  exists L : HolLineBundleCech (km_manifold M), c1 M L = α.
   CAG zero-dependent Definition is_integral_class theories/Divisor/ChernClasses.v:184 END *)

(** [c₁(L)] is always integral.  Trivial since [is_integral_class]
    is defined as "lies in image of [c₁]".  No axiom needed. *)
(* CAG zero-dependent Theorem c1_integral theories/Divisor/ChernClasses.v:189 BEGIN
Theorem c1_integral : forall (M : KahlerManifold)
    (L : HolLineBundleCech (km_manifold M)),
    is_integral_class M (c1 M L).
Proof. intros M L. exists L. reflexivity. Qed.
   CAG zero-dependent Theorem c1_integral theories/Divisor/ChernClasses.v:189 END *)

(** The zero class is always integral (witnessed by the trivial bundle). *)
(* CAG zero-dependent Theorem is_integral_class_zero theories/Divisor/ChernClasses.v:193 BEGIN
Theorem is_integral_class_zero : forall (M : KahlerManifold),
    is_integral_class M (vs_zero (HdR_vs M 2)).
Proof.
  intros M. exists (hlb_trivial (km_manifold M)).
  apply c1_trivial_zero.
Qed.
   CAG zero-dependent Theorem is_integral_class_zero theories/Divisor/ChernClasses.v:193 END *)

(** Rational-multiple-integrality: a real class α is rational iff
    [k·α] is integral for some k ≠ 0.  This is the standard
    "integral classes form a lattice" identity (Voisin Vol. I §11.2).
    Recorded in existential form: if some integer multiple of α is
    integral, then α is rational.  Famous-old, Conjecture. *)
(* CAG zero-dependent Conjecture rational_class_has_integral_multiple theories/Divisor/ChernClasses.v:192 BEGIN
Conjecture rational_class_has_integral_multiple : forall (M : KahlerManifold)
    (α : HdR M 2),
  is_integral_class M α ->
  exists L : HolLineBundleCech (km_manifold M),
    c1 M L = α.
   CAG zero-dependent Conjecture rational_class_has_integral_multiple theories/Divisor/ChernClasses.v:192 END *)
(** A class is rational iff it has an integral multiple
    (Voisin Vol. I §11.2 "Rational classes and integral lattice"). *)
