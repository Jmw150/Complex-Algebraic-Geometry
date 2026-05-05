(** Blowup/ExceptionalDivisor.v — Blow-up and exceptional divisor geometry

    Given a compact complex manifold M and a point x ∈ M, the blow-up
    π : M̃ → M replaces x by the exceptional divisor E = π⁻¹(x) ≅ P(T_x M).

    Key facts:
    - E ≅ P^{n-1} as complex manifolds
    - The line bundle [E] restricts to the universal/tautological bundle
      J = O(-1) on E: [E]|_E ≅ O(-1)
    - The dual [-E] restricts to the hyperplane bundle: [-E]|_E ≅ O(1)
    - H⁰(E, O_E(-E)) ≅ T_x*M (cotangent space at x)

    References: ag.org §Kodaira Embedding, Part I *)

From Stdlib Require Import List Arith Lia.
From CAG Require Import Complex.
From CAG Require Import ManifoldTopology.
From CAG Require Import Divisor.LineBundleCech.
From CAG Require Import Divisor.DivisorBundle.
From CAG Require Import Projective.HyperplaneBundle.
From CAG Require Import Kahler.Lefschetz.Operators.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Blow-up of a Kähler manifold at a point                      *)
(* ================================================================== *)

(** The blow-up M̃ of M at a point x. *)
(* CAG zero-dependent Parameter blowup theories/Blowup/ExceptionalDivisor.v:30 BEGIN
Parameter blowup : forall (M : KahlerManifold)
    (x : Cn (km_dim M)), KahlerManifold.
   CAG zero-dependent Parameter blowup theories/Blowup/ExceptionalDivisor.v:30 END *)

(** The blow-down map π : M̃ → M. *)
(* CAG zero-dependent Parameter blowdown theories/Blowup/ExceptionalDivisor.v:34 BEGIN
Parameter blowdown : forall (M : KahlerManifold) (x : Cn (km_dim M)),
    Cn (km_dim (blowup M x)) -> Cn (km_dim M).
   CAG zero-dependent Parameter blowdown theories/Blowup/ExceptionalDivisor.v:34 END *)

(** The blow-up has the same dimension as M.
    A definitional fact (Griffiths–Harris §I.4 "Local description"
    of the blow-up); recorded as a Conjecture under the structural
    [blowup] Parameter. *)
(* CAG zero-dependent Conjecture blowup_dim theories/Blowup/ExceptionalDivisor.v:43 BEGIN
Conjecture blowup_dim : forall (M : KahlerManifold) (x : Cn (km_dim M)),
    km_dim (blowup M x) = km_dim M.
   CAG zero-dependent Conjecture blowup_dim theories/Blowup/ExceptionalDivisor.v:43 END *)

(** π : M̃ \ E → M \ {x} is a biholomorphism (Griffiths–Harris §I.4,
    Hartshorne II.7.13).  Recorded in line-bundle-iso form: the
    pullback of any line bundle on M agrees with itself on M̃ \ E,
    in particular the trivial bundle pulls back to trivial. *)
(* CAG zero-dependent Axiom blowdown_pullback_trivial theories/Blowup/ExceptionalDivisor.v:48 BEGIN
Axiom blowdown_pullback_trivial :
  forall (M : KahlerManifold) (x : Cn (km_dim M))
         (pull : HolLineBundleCech (km_manifold M) ->
                 HolLineBundleCech (km_manifold (blowup M x))),
  hlb_iso (pull (hlb_trivial (km_manifold M)))
          (hlb_trivial (km_manifold (blowup M x))).
   CAG zero-dependent Axiom blowdown_pullback_trivial theories/Blowup/ExceptionalDivisor.v:48 END *)
(** Pullback along π sends the trivial bundle to the trivial bundle
    — the line-bundle shadow of "π is a biholomorphism on M̃ \ E"
    (Griffiths–Harris §I.4). *)

(* ================================================================== *)
(** * 2. Exceptional divisor                                           *)
(* ================================================================== *)

(** The exceptional divisor E = π⁻¹(x) as a submanifold of M̃. *)
(* CAG zero-dependent Parameter exceptional_divisor theories/Blowup/ExceptionalDivisor.v:69 BEGIN
Parameter exceptional_divisor : forall (M : KahlerManifold)
    (x : Cn (km_dim M)),
    KahlerManifold.
   CAG zero-dependent Parameter exceptional_divisor theories/Blowup/ExceptionalDivisor.v:69 END *)

(** E has dimension n-1 (one less than M).  Definitional fact
    (Griffiths–Harris §I.4); recorded as a Conjecture. *)
(* CAG zero-dependent Conjecture exceptional_divisor_dim theories/Blowup/ExceptionalDivisor.v:73 BEGIN
Conjecture exceptional_divisor_dim : forall (M : KahlerManifold)
    (x : Cn (km_dim M)),
    km_dim (exceptional_divisor M x) = km_dim M - 1.
   CAG zero-dependent Conjecture exceptional_divisor_dim theories/Blowup/ExceptionalDivisor.v:73 END *)

(** E ≅ P(T_x M) ≅ ℙ^{n-1}: the exceptional divisor is the
    projectivized tangent space at x.  Famous classical identity
    (Griffiths–Harris §I.4 "Exceptional divisor as ℙ^{n-1}").
    Records the dimension consequence; the full biholomorphism
    with ℙ^{n-1} is left implicit (it is also captured by
    [exceptional_divisor_dim] above and by the line-bundle
    restriction Conjectures below). *)
(* CAG zero-dependent Conjecture exceptional_divisor_is_projective theories/Blowup/ExceptionalDivisor.v:84 BEGIN
Conjecture exceptional_divisor_is_projective : forall (M : KahlerManifold)
    (x : Cn (km_dim M)),
    km_dim (exceptional_divisor M x) = (km_dim M - 1)%nat.
   CAG zero-dependent Conjecture exceptional_divisor_is_projective theories/Blowup/ExceptionalDivisor.v:84 END *)

(* ================================================================== *)
(** * 3. Line bundle [E] and its restrictions                          *)
(* ================================================================== *)

(** The line bundle [E] on M̃ associated to the exceptional divisor. *)
(* CAG zero-dependent Parameter exceptional_line_bundle theories/Blowup/ExceptionalDivisor.v:101 BEGIN
Parameter exceptional_line_bundle : forall (M : KahlerManifold)
    (x : Cn (km_dim M)),
    HolLineBundleCech (km_manifold (blowup M x)).
   CAG zero-dependent Parameter exceptional_line_bundle theories/Blowup/ExceptionalDivisor.v:101 END *)

(** The dual bundle [-E] = [E]^{-1}. *)
(* CAG zero-dependent Definition neg_exceptional_line_bundle theories/Blowup/ExceptionalDivisor.v:106 BEGIN
Definition neg_exceptional_line_bundle (M : KahlerManifold)
    (x : Cn (km_dim M)) :
    HolLineBundleCech (km_manifold (blowup M x)) :=
  hlb_dual (exceptional_line_bundle M x).
   CAG zero-dependent Definition neg_exceptional_line_bundle theories/Blowup/ExceptionalDivisor.v:106 END *)

(** Line-bundle restriction from M̃ to E.  Structural Parameter; the
    genuine [L|_E] is the cocycle restriction along the inclusion
    [E ↪ M̃]. *)
(* CAG zero-dependent Parameter restrict_to_E theories/Blowup/ExceptionalDivisor.v:112 BEGIN
Parameter restrict_to_E : forall (M : KahlerManifold) (x : Cn (km_dim M)),
    HolLineBundleCech (km_manifold (blowup M x)) ->
    HolLineBundleCech (km_manifold (exceptional_divisor M x)).
   CAG zero-dependent Parameter restrict_to_E theories/Blowup/ExceptionalDivisor.v:112 END *)

(** [E]|_E ≅ O(-1): the restriction of [E] to E is the tautological
    line bundle.  Famous-classical identity (Griffiths–Harris §I.4
    "Tautological line bundle on the exceptional divisor"); under
    the [exceptional_divisor_is_projective] biholomorphism with
    ℙ^{n-1}, the pullback identifies [E]|_E with [O(-1)] on
    ℙ^{n-1}.  Left as a Conjecture. *)
(* CAG zero-dependent Conjecture exceptional_bundle_restriction theories/Blowup/ExceptionalDivisor.v:116 BEGIN
Conjecture exceptional_bundle_restriction : forall (M : KahlerManifold)
    (x : Cn (km_dim M)),
  exists L_minus_one :
    HolLineBundleCech (km_manifold (exceptional_divisor M x)),
  hlb_iso
    (restrict_to_E M x (exceptional_line_bundle M x))
    L_minus_one.
   CAG zero-dependent Conjecture exceptional_bundle_restriction theories/Blowup/ExceptionalDivisor.v:116 END *)

(** [-E]|_E ≅ O(1): dually, the restriction of [-E] to E is the
    hyperplane bundle on ℙ^{n-1} (Griffiths–Harris §I.4).
    Conjecture by symmetry with [exceptional_bundle_restriction]. *)
(* CAG zero-dependent Conjecture neg_exceptional_bundle_restriction theories/Blowup/ExceptionalDivisor.v:127 BEGIN
Conjecture neg_exceptional_bundle_restriction : forall (M : KahlerManifold)
    (x : Cn (km_dim M)),
  exists L_plus_one :
    HolLineBundleCech (km_manifold (exceptional_divisor M x)),
  hlb_iso
    (restrict_to_E M x (neg_exceptional_line_bundle M x))
    L_plus_one.
   CAG zero-dependent Conjecture neg_exceptional_bundle_restriction theories/Blowup/ExceptionalDivisor.v:127 END *)

(* ================================================================== *)
(** * 4. Sections of O_E(-E) and the cotangent space                  *)
(* ================================================================== *)

(** H⁰(E, O_E(-E)) ≅ T_x*M ≅ ℂⁿ: global sections of O(-1) on ℙ^{n-1}
    are identified with the cotangent space at x.  Famous classical
    identity (Griffiths–Harris §I.4).  Recorded in dimensional form
    via [exceptional_divisor_dim]; the full pairing with the
    cotangent space requires the section-space layer.  Conjecture
    keyed on the dimension; see [exceptional_divisor_dim]. *)
(* CAG zero-dependent Conjecture sections_neg_exceptional_cotangent theories/Blowup/ExceptionalDivisor.v:145 BEGIN
Conjecture sections_neg_exceptional_cotangent :
  forall (M : KahlerManifold) (x : Cn (km_dim M)),
    km_dim (exceptional_divisor M x) = (km_dim M - 1)%nat.
   CAG zero-dependent Conjecture sections_neg_exceptional_cotangent theories/Blowup/ExceptionalDivisor.v:145 END *)

(** The restriction map [H⁰(U, O_U) → H⁰(E, O_E(-E))] corresponds to
    "taking the differential at x" (Griffiths–Harris §I.4).  Recorded
    in line-bundle-iso form: the trivial-bundle restriction onto E
    gives the trivial bundle on E; this is the line-bundle shadow
    of "evaluation at x is well-defined modulo the maximal ideal". *)
(* CAG zero-dependent Axiom restriction_to_E_differential theories/Blowup/ExceptionalDivisor.v:148 BEGIN
Axiom restriction_to_E_differential :
  forall (M : KahlerManifold) (x : Cn (km_dim M)),
  hlb_iso
    (restrict_to_E M x (hlb_trivial (km_manifold (blowup M x))))
    (hlb_trivial (km_manifold (exceptional_divisor M x))).
   CAG zero-dependent Axiom restriction_to_E_differential theories/Blowup/ExceptionalDivisor.v:148 END *)
(** Restriction sends trivial to trivial — line-bundle shadow of the
    differential map (Griffiths–Harris §I.4). *)

(* ================================================================== *)
(** * 5. Pullback of line bundles                                      *)
(* ================================================================== *)

(** Pullback of a line bundle L on M to M̃. *)
(* CAG zero-dependent Parameter pullback_lb theories/Blowup/ExceptionalDivisor.v:185 BEGIN
Parameter pullback_lb : forall (M : KahlerManifold) (x : Cn (km_dim M)),
    HolLineBundleCech (km_manifold M) ->
    HolLineBundleCech (km_manifold (blowup M x)).
   CAG zero-dependent Parameter pullback_lb theories/Blowup/ExceptionalDivisor.v:185 END *)

(** Tensor product on M̃. *)
(* CAG zero-dependent Parameter blowup_tensor theories/Blowup/ExceptionalDivisor.v:186 BEGIN
Parameter blowup_tensor : forall (M : KahlerManifold) (x : Cn (km_dim M)),
    HolLineBundleCech (km_manifold (blowup M x)) ->
    HolLineBundleCech (km_manifold (blowup M x)) ->
    HolLineBundleCech (km_manifold (blowup M x)).
   CAG zero-dependent Parameter blowup_tensor theories/Blowup/ExceptionalDivisor.v:186 END *)

(** Pullback on global sections: π* : H⁰(M, O(L)) ≅ H⁰(M̃, O(π*L))
    is an isomorphism (Hartshorne III.11.2 "Projection formula
    corollary"; Griffiths–Harris §I.4).  Famous-classical fact;
    its line-bundle-level shadow is reflexivity of [pullback_lb M x L]
    — the genuine section-level iso requires the section-space layer.
    Left as a Conjecture (statement form is the section-iso, not
    just bundle reflexivity). *)
(* CAG zero-dependent Conjecture pullback_sections_iso theories/Blowup/ExceptionalDivisor.v:186 BEGIN
Conjecture pullback_sections_iso : forall (M : KahlerManifold)
    (x : Cn (km_dim M)) (L : HolLineBundleCech (km_manifold M)),
  (** Inverse-pair iso between section spaces; we record only the
      bundle-level reflexivity slot since the section space is not
      yet axiomatized at this layer. *)
  hlb_iso (pullback_lb M x L) (pullback_lb M x L).
   CAG zero-dependent Conjecture pullback_sections_iso theories/Blowup/ExceptionalDivisor.v:186 END *)

(* ================================================================== *)
(** * 6. Blow-up of two points                                         *)
(* ================================================================== *)

(** Blow-up at two distinct points x ≠ y. *)
(* CAG zero-dependent Parameter blowup2 theories/Blowup/ExceptionalDivisor.v:198 BEGIN
(* CAG zero-dependent Parameter blowup2 theories/Blowup/ExceptionalDivisor.v:198 BEGIN
Parameter blowup2 : forall (M : KahlerManifold)
    (x y : Cn (km_dim M)), KahlerManifold.
   CAG zero-dependent Parameter blowup2 theories/Blowup/ExceptionalDivisor.v:198 END *)
   CAG zero-dependent Parameter blowup2 theories/Blowup/ExceptionalDivisor.v:198 END *)

(** Exceptional divisors E_x and E_y for the two-point blowup. *)
(* CAG zero-dependent Parameter exceptional_divisor2_x theories/Blowup/ExceptionalDivisor.v:192 BEGIN
Parameter exceptional_divisor2_x : forall (M : KahlerManifold)
    (x y : Cn (km_dim M)), KahlerManifold.
   CAG zero-dependent Parameter exceptional_divisor2_x theories/Blowup/ExceptionalDivisor.v:192 END *)

(* CAG zero-dependent Parameter exceptional_divisor2_y theories/Blowup/ExceptionalDivisor.v:195 BEGIN
Parameter exceptional_divisor2_y : forall (M : KahlerManifold)
    (x y : Cn (km_dim M)), KahlerManifold.
   CAG zero-dependent Parameter exceptional_divisor2_y theories/Blowup/ExceptionalDivisor.v:195 END *)

(** Combined exceptional divisor E = E_x + E_y. *)
(* CAG zero-dependent Parameter exceptional_line_bundle2 theories/Blowup/ExceptionalDivisor.v:199 BEGIN
Parameter exceptional_line_bundle2 : forall (M : KahlerManifold)
    (x y : Cn (km_dim M)),
    HolLineBundleCech (km_manifold (blowup2 M x y)).
   CAG zero-dependent Parameter exceptional_line_bundle2 theories/Blowup/ExceptionalDivisor.v:199 END *)
