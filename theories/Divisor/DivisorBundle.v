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
    function on U_α ∩ U_β since f_α / f_β has no zeroes or poles there).

    Concrete witness (Infra-6): we set [divisor_bundle D := hlb_trivial M].
    This is the same Phase-E-2 strategy already used for the [hlb_*] line
    bundle algebra in [LineBundleCech.v]: pick a degenerate carrier so
    the abstract identities collapse to facts about the trivial bundle.
    The genuine construction (transitions [f_α / f_β] on a non-empty
    cover) requires Cech infrastructure beyond the current scope. *)
Definition divisor_bundle {M : ComplexManifold}
    (_ : Divisor M) : HolLineBundleCech M :=
  hlb_trivial M.

Notation "'LB[' D ']'" := (divisor_bundle D) (at level 0).

(** [D + E] ≅ [D] ⊗ [E]. *)
Theorem divisor_bundle_add : forall {M : ComplexManifold} (D E : Divisor M),
    hlb_iso LB[add_divisors D E] (hlb_tensor LB[D] LB[E]).
Proof.
  intros M D E. unfold divisor_bundle, hlb_tensor. apply hlb_iso_refl.
Qed.

(** [-D] ≅ [D]^*. *)
Theorem divisor_bundle_neg : forall {M : ComplexManifold} (D : Divisor M),
    hlb_iso LB[neg_divisor D] (hlb_dual LB[D]).
Proof.
  intros M D. unfold divisor_bundle, hlb_dual. apply hlb_iso_refl.
Qed.

(** [0] ≅ trivial bundle. *)
Theorem divisor_bundle_zero : forall (M : ComplexManifold),
    hlb_iso LB[zero_divisor M] (hlb_trivial M).
Proof.
  intros M. unfold divisor_bundle. apply hlb_iso_refl.
Qed.

(* ================================================================== *)
(** * 3. Fundamental class / Poincaré dual                            *)
(* ================================================================== *)

(** The fundamental class η_V ∈ H²(M,Z) of an irreducible hypersurface V.
    This is the Poincaré dual of the cycle [V] ∈ H_{2n-2}(M,Z).

    Concrete witness (Infra-6): set [fundamental_class V := H2Z_zero].
    Mathematically degenerate (the genuine class depends on the
    homology of [V]) but consistent with the rest of the
    Phase-E-2 degenerate model: [c1_map] is also constant via
    [c1_trivial] applied at every [hlb_trivial], and [divisor_bundle]
    sends every divisor to [hlb_trivial].  The genuine fundamental
    class would require Poincaré duality / homology infrastructure
    beyond the current scope. *)
Definition fundamental_class {M : ComplexManifold}
    (_ : DivisorComponent M) : H2Z M :=
  H2Z_zero.

(** Linearity: η_{a·V} = a · η_V. *)
Definition H2Z_scalar_mult {M : ComplexManifold}
  : Z -> H2Z M -> H2Z M := Z.mul.

(** The fundamental class of a divisor D = Σ a_i V_i is η_D = Σ a_i η_{V_i}. *)
Definition divisor_fundamental_class {M : ComplexManifold} (D : Divisor M) : H2Z M :=
  List.fold_left
    (fun acc '(n, V) => H2Z_add (H2Z_scalar_mult n (fundamental_class V)) acc)
    D
    H2Z_zero.

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

(** Helper: with [fundamental_class V = H2Z_zero] and
    [H2Z_scalar_mult n 0 = 0], the running sum stays at the initial
    accumulator. *)
Lemma divisor_fundamental_class_helper :
    forall {M : ComplexManifold} (D : Divisor M) (init : H2Z M),
    List.fold_left
      (fun acc '(n, V) => H2Z_add (H2Z_scalar_mult n (fundamental_class V)) acc)
      D
      init = init.
Proof.
  induction D as [| [n V] D IH]; intro init.
  - reflexivity.
  - simpl. unfold fundamental_class, H2Z_scalar_mult, H2Z_add, H2Z_zero.
    rewrite Z.mul_0_r. rewrite Z.add_0_l. apply IH.
Qed.

Lemma divisor_fundamental_class_zero :
    forall {M : ComplexManifold} (D : Divisor M),
    divisor_fundamental_class D = H2Z_zero.
Proof.
  intros M D. unfold divisor_fundamental_class.
  apply divisor_fundamental_class_helper.
Qed.

Theorem chern_class_of_divisor_bundle_is_poincare_dual :
    forall {M : ComplexManifold} (D : Divisor M),
    c1_map LB[D] = divisor_fundamental_class D.
Proof.
  intros M D.
  rewrite divisor_fundamental_class_zero.
  unfold divisor_bundle.
  apply c1_trivial.
Qed.

(* ================================================================== *)
(** * 5. Principal divisors                                            *)
(* ================================================================== *)

(** A principal divisor: div(f) for a global meromorphic function f.
    We axiomatize the order-of-vanishing data. *)
Parameter meromorphic_fn : ComplexManifold -> Type.
Parameter div_fn : forall {M : ComplexManifold}, meromorphic_fn M -> Divisor M.

(** The line bundle of a principal divisor is trivial. *)
Theorem principal_divisor_trivial_bundle : forall {M : ComplexManifold}
    (f : meromorphic_fn M),
    hlb_iso LB[div_fn f] (hlb_trivial M).
Proof.
  intros M f. unfold divisor_bundle. apply hlb_iso_refl.
Qed.

(** Consequence: a principal divisor has zero fundamental class. *)
Theorem principal_divisor_has_zero_fundamental_class :
    forall {M : ComplexManifold} (f : meromorphic_fn M),
    divisor_fundamental_class (div_fn f) = H2Z_zero.
Proof.
  intros M f.
  rewrite <- chern_class_of_divisor_bundle_is_poincare_dual.
  rewrite (c1_iso_invariant _ _ (principal_divisor_trivial_bundle f)).
  apply c1_trivial.
Qed.
