(** Divisor/DivisorBundle.v — Divisors, [D], and c₁([D]) = η_D

    A divisor on a complex manifold M is a formal integer combination
    D = Σ a_i V_i of irreducible analytic hypersurfaces V_i.

    The associated line bundle [D]: transition functions g_{αβ} = f_α / f_β
    where f_α is the local defining equation for D on U_α.

    Fundamental theorem: c₁([D]) = η_D in H²(M, Z) where η_D is the
    Poincaré dual / fundamental class of D.

    Consequence: principal divisors (D = div(f)) have c₁ = 0, so
    they represent the trivial element in Pic(M).

    References: ag.org Part IV §Fundamental class of divisors *)

From Stdlib Require Import List Arith ZArith Lia.
From CAG Require Import Complex.
From CAG Require Import AG.
From CAG Require Import ManifoldTopology.
From CAG Require Import Divisor.LineBundleCech.
From CAG Require Import Divisor.Curvature.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Divisors                                                      *)
(* ================================================================== *)

(** An irreducible analytic hypersurface V ⊂ M together with its
    local defining equations and integer coefficient. *)
Record DivisorComponent (M : ComplexManifold) : Type :=
{ dc_variety : Cn (cm_dim M) -> Prop   (** the underlying hypersurface *)
; dc_is_hypersurface :
    AnalyticHypersurface (fun _ => True) dc_variety
    (** V is an irreducible analytic hypersurface in M *)
}.
Arguments dc_variety {M} _.
Arguments dc_is_hypersurface {M} _.

(** A divisor is a finite formal integer combination of irreducible
    analytic hypersurfaces. *)
Definition Divisor (M : ComplexManifold) : Type :=
  list (Z * DivisorComponent M).

(** The support of D: the set of points lying on some component. *)
Definition divisor_support {M : ComplexManifold} (D : Divisor M) :
    Cn (cm_dim M) -> Prop :=
  fun z => exists n V, List.In (n, V) D /\ dc_variety V z.

(** D is effective if all coefficients are nonneg. *)
Definition effective_divisor {M : ComplexManifold} (D : Divisor M) : Prop :=
  forall n V, List.In (n, V) D -> (0 <= n)%Z.

(** The zero divisor. *)
Definition zero_divisor (M : ComplexManifold) : Divisor M := [].

(** Addition of divisors. *)
Definition add_divisors {M : ComplexManifold} (D E : Divisor M) : Divisor M :=
  List.app D E.

(** Negation (reverse all signs). *)
Definition neg_divisor {M : ComplexManifold} (D : Divisor M) : Divisor M :=
  List.map (fun '(n, V) => (Z.opp n, V)) D.

(* ================================================================== *)
(** * 2. The associated line bundle [D]                                *)
(* ================================================================== *)

(** The line bundle [D] associated to a divisor D.
    Locally: if f_α is the defining equation for D on U_α, then
    the transition function is g_{αβ} = f_α / f_β (a nonzero holomorphic
    function on U_α ∩ U_β since f_α / f_β has no zeroes or poles there). *)
(* CAG zero-dependent Parameter divisor_bundle theories/Divisor/DivisorBundle.v:74 BEGIN
Parameter divisor_bundle : forall {M : ComplexManifold},
    Divisor M -> HolLineBundleCech M.
   CAG zero-dependent Parameter divisor_bundle theories/Divisor/DivisorBundle.v:74 END *)






(* CAG constructive-remove Command Notation theories/Divisor/DivisorBundle.v:84 BEGIN -- missing divisor_bundle
Notation "'LB[' D ']'" := (divisor_bundle D) (at level 0).

   CAG constructive-remove Command Notation theories/Divisor/DivisorBundle.v:84 END *)

(** [D + E] ≅ [D] ⊗ [E]: addition of divisors corresponds to
    tensor product of associated line bundles.  The fundamental
    homomorphism property of the divisor-to-Pic map; reference:
    Griffiths–Harris §I.3 "The map [D] from Div(M) to Pic(M) is a
    homomorphism", Hartshorne II.6.13. *)
(* CAG zero-dependent Axiom divisor_bundle_add theories/Divisor/DivisorBundle.v:84 BEGIN
Axiom divisor_bundle_add :
  forall {M : ComplexManifold} (D E : Divisor M),
    hlb_iso LB[add_divisors D E] (hlb_tensor LB[D] LB[E]).
   CAG zero-dependent Axiom divisor_bundle_add theories/Divisor/DivisorBundle.v:84 END *)
(** [LB[D + E] ≅ LB[D] ⊗ LB[E]]. *)

(** [-D] ≅ [D]^*: divisor negation corresponds to bundle dualization.
    Direct corollary of [divisor_bundle_add] applied to [D + (-D) = 0]
    plus [divisor_bundle_zero]; recorded as a paper-attributable
    Axiom (Griffiths–Harris §I.3, Hartshorne II.6.13). *)
(* CAG zero-dependent Axiom divisor_bundle_neg theories/Divisor/DivisorBundle.v:93 BEGIN
Axiom divisor_bundle_neg :
  forall {M : ComplexManifold} (D : Divisor M),
    hlb_iso LB[neg_divisor D] (hlb_dual LB[D]).
   CAG zero-dependent Axiom divisor_bundle_neg theories/Divisor/DivisorBundle.v:93 END *)
(** [LB[-D] ≅ (LB[D])^*]. *)

(** [0] ≅ trivial bundle: the zero divisor's bundle is trivial.
    Reference: Griffiths–Harris §I.3 "Identity element of the
    Picard group". *)
(* CAG zero-dependent Axiom divisor_bundle_zero theories/Divisor/DivisorBundle.v:101 BEGIN
Axiom divisor_bundle_zero :
  forall (M : ComplexManifold),
    hlb_iso LB[zero_divisor M] (hlb_trivial M).
   CAG zero-dependent Axiom divisor_bundle_zero theories/Divisor/DivisorBundle.v:101 END *)
(** [LB[0] ≅ trivial line bundle]. *)

(* ================================================================== *)
(** * 3. Fundamental class / Poincaré dual                            *)
(* ================================================================== *)

(** The fundamental class η_V ∈ H²(M,Z) of an irreducible hypersurface V.
    This is the Poincaré dual of the cycle [V] ∈ H_{2n-2}(M,Z). *)
(* CAG zero-dependent Parameter fundamental_class theories/Divisor/DivisorBundle.v:123 BEGIN
Parameter fundamental_class : forall {M : ComplexManifold},
    DivisorComponent M -> H2Z M.
   CAG zero-dependent Parameter fundamental_class theories/Divisor/DivisorBundle.v:123 END *)

(** Linearity: η_{a·V} = a · η_V. *)
(* CAG zero-dependent Parameter H2Z_scalar_mult theories/Divisor/DivisorBundle.v:127 BEGIN
Parameter H2Z_scalar_mult : forall {M : ComplexManifold},
    Z -> H2Z M -> H2Z M.
   CAG zero-dependent Parameter H2Z_scalar_mult theories/Divisor/DivisorBundle.v:127 END *)

(** The fundamental class of a divisor D = Σ a_i V_i is η_D = Σ a_i η_{V_i}. *)
(* CAG zero-dependent Definition divisor_fundamental_class theories/Divisor/DivisorBundle.v:131 BEGIN
Definition divisor_fundamental_class {M : ComplexManifold} (D : Divisor M) : H2Z M :=
  List.fold_left
    (fun acc '(n, V) => H2Z_add (H2Z_scalar_mult n (fundamental_class V)) acc)
    D
    H2Z_zero.
   CAG zero-dependent Definition divisor_fundamental_class theories/Divisor/DivisorBundle.v:131 END *)

(* ================================================================== *)
(** * 4. Main theorem: c₁([D]) = η_D                                  *)
(* ================================================================== *)

(** The first Chern class of the line bundle associated to a divisor
    equals the fundamental class (Poincaré dual) of the divisor.

    Proof strategy:
    A. Curvature of the metric connection on [V]:
       For smooth V with local section s, the curvature is
       Θ = ∂∂̄ log |s|² = 2πi · dd^c log |s|².
    B. Stokes computation near V:
       Apply Stokes to d^c log |s|² ∧ ψ near V using a tubular
       neighborhood {|s| < ε}; the boundary integral converges to ∫_V ψ.
    C. Conclude: ∫_M (i/2π) Θ ∧ ψ = ∫_V ψ for all test forms ψ,
       which is the defining property of η_V. *)

(** First Chern class of a divisor bundle = Poincaré dual of the
    divisor: [c₁([D]) = η_D] in [H²(M, ℤ)].  Famous-old classical
    identity (Griffiths–Harris §I.3 "Fundamental class of a
    divisor", Hartshorne app. C, Lelong's formula).  Recorded as
    a Conjecture per "famous-old". *)
(* CAG zero-dependent Axiom chern_class_of_divisor_bundle_is_poincare_dual theories/Divisor/DivisorBundle.v:156 BEGIN
Axiom chern_class_of_divisor_bundle_is_poincare_dual :
    forall {M : ComplexManifold} (D : Divisor M),
    c1_map LB[D] = divisor_fundamental_class D.
   CAG zero-dependent Axiom chern_class_of_divisor_bundle_is_poincare_dual theories/Divisor/DivisorBundle.v:156 END *)

(* ================================================================== *)
(** * 5. Principal divisors                                            *)
(* ================================================================== *)

(** A principal divisor: div(f) for a global meromorphic function f.
    We axiomatize the order-of-vanishing data. *)
(* CAG zero-dependent Parameter meromorphic_fn theories/Divisor/DivisorBundle.v:169 BEGIN
Parameter meromorphic_fn : ComplexManifold -> Type.
   CAG zero-dependent Parameter meromorphic_fn theories/Divisor/DivisorBundle.v:169 END *)
(* CAG zero-dependent Parameter div_fn theories/Divisor/DivisorBundle.v:169 BEGIN
Parameter div_fn : forall {M : ComplexManifold}, meromorphic_fn M -> Divisor M.
   CAG zero-dependent Parameter div_fn theories/Divisor/DivisorBundle.v:169 END *)

(** The line bundle of a principal divisor is trivial:
    [LB[div(f)] ≅ trivial] for any meromorphic [f].
    Reference: Griffiths–Harris §I.3 "Principal divisors are
    trivial in Pic(M)" — the meromorphic function [f] itself
    trivializes the cocycle. *)
(* CAG zero-dependent Axiom principal_divisor_trivial_bundle theories/Divisor/DivisorBundle.v:174 BEGIN
Axiom principal_divisor_trivial_bundle :
  forall {M : ComplexManifold} (f : meromorphic_fn M),
    hlb_iso LB[div_fn f] (hlb_trivial M).
   CAG zero-dependent Axiom principal_divisor_trivial_bundle theories/Divisor/DivisorBundle.v:174 END *)
(** [LB[div(f)] ≅ trivial]: principal divisors give the identity
    in the Picard group. *)

(** Consequence: a principal divisor has zero fundamental class. *)
(* CAG zero-dependent Theorem principal_divisor_has_zero_fundamental_class theories/Divisor/DivisorBundle.v:181 BEGIN
Theorem principal_divisor_has_zero_fundamental_class :
    forall {M : ComplexManifold} (f : meromorphic_fn M),
    divisor_fundamental_class (div_fn f) = H2Z_zero.
Proof.
  intros M f.
  rewrite <- chern_class_of_divisor_bundle_is_poincare_dual.
  rewrite (c1_iso_invariant _ _ (principal_divisor_trivial_bundle f)).
  apply c1_trivial.
Qed.
   CAG zero-dependent Theorem principal_divisor_has_zero_fundamental_class theories/Divisor/DivisorBundle.v:181 END *)
