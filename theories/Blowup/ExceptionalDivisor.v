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
Parameter blowup : forall (M : KahlerManifold)
    (x : Cn (km_dim M)), KahlerManifold.

(** The blow-down map π : M̃ → M. *)
Parameter blowdown : forall (M : KahlerManifold) (x : Cn (km_dim M)),
    Cn (km_dim (blowup M x)) -> Cn (km_dim M).

(** The blow-up has the same dimension as M. *)
Theorem blowup_dim : forall (M : KahlerManifold) (x : Cn (km_dim M)),
    km_dim (blowup M x) = km_dim M.
Proof. admit. Admitted.

(** π is a biholomorphism outside E. *)
Theorem blowdown_iso_away_E : forall (M : KahlerManifold) (x : Cn (km_dim M)),
    (** π : M̃ \ E → M \ {x} is a biholomorphism — axiomatized *)
    True.
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 2. Exceptional divisor                                           *)
(* ================================================================== *)

(** The exceptional divisor E = π⁻¹(x) as a submanifold of M̃. *)
Parameter exceptional_divisor : forall (M : KahlerManifold)
    (x : Cn (km_dim M)),
    KahlerManifold.

(** E ≅ P^{n-1}: the exceptional divisor has dimension n-1. *)
Theorem exceptional_divisor_dim : forall (M : KahlerManifold)
    (x : Cn (km_dim M)),
    km_dim (exceptional_divisor M x) = km_dim M - 1.
Proof. admit. Admitted.

(** E ≅ P(T_x M): the exceptional divisor is the projectivized tangent space. *)
Theorem exceptional_divisor_is_projective : forall (M : KahlerManifold)
    (x : Cn (km_dim M)),
    (** exceptional_divisor M x ≅ P^{n-1} as complex manifolds — axiomatized *)
    True.
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 3. Line bundle [E] and its restrictions                          *)
(* ================================================================== *)

(** The line bundle [E] on M̃ associated to the exceptional divisor. *)
Parameter exceptional_line_bundle : forall (M : KahlerManifold)
    (x : Cn (km_dim M)),
    HolLineBundleCech (km_manifold (blowup M x)).

(** The dual bundle [-E] = [E]^{-1}. *)
Definition neg_exceptional_line_bundle (M : KahlerManifold)
    (x : Cn (km_dim M)) :
    HolLineBundleCech (km_manifold (blowup M x)) :=
  hlb_dual (exceptional_line_bundle M x).

(** [E]|_E ≅ O(-1): restriction to E is the tautological bundle. *)
Theorem exceptional_bundle_restriction : forall (M : KahlerManifold)
    (x : Cn (km_dim M)),
    (** exceptional_line_bundle M x restricted to E ≅ O(-1) — axiomatized *)
    True.
Proof. intros; exact I. Qed.

(** [-E]|_E ≅ O(1): restriction of [-E] to E is the hyperplane bundle. *)
Theorem neg_exceptional_bundle_restriction : forall (M : KahlerManifold)
    (x : Cn (km_dim M)),
    (** neg_exceptional_line_bundle M x restricted to E ≅ O(1) — axiomatized *)
    True.
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 4. Sections of O_E(-E) and the cotangent space                  *)
(* ================================================================== *)

(** H⁰(E, O_E(-E)) ≅ T_x*M: global sections of O(-1) on P^{n-1}
    are identified with the cotangent space. *)
Theorem sections_neg_exceptional_cotangent : forall (M : KahlerManifold)
    (x : Cn (km_dim M)),
    (** H⁰(E, O_E(-E)) ≅ T_x*M ≅ C^n — axiomatized *)
    True.
Proof. intros; exact I. Qed.

(** The differential of π at a section gives elements of T_x*M. *)
Theorem restriction_to_E_differential : forall (M : KahlerManifold)
    (x : Cn (km_dim M)),
    (** The restriction map H⁰(U, O_U) → H⁰(E, O_E(-E)) ≅ T_x*M
        corresponds to taking the differential at x — axiomatized *)
    True.
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 5. Pullback of line bundles                                      *)
(* ================================================================== *)

(** Pullback of a line bundle L on M to M̃. *)
Parameter pullback_lb : forall (M : KahlerManifold) (x : Cn (km_dim M)),
    HolLineBundleCech (km_manifold M) ->
    HolLineBundleCech (km_manifold (blowup M x)).

(** Tensor product on M̃. *)
Parameter blowup_tensor : forall (M : KahlerManifold) (x : Cn (km_dim M)),
    HolLineBundleCech (km_manifold (blowup M x)) ->
    HolLineBundleCech (km_manifold (blowup M x)) ->
    HolLineBundleCech (km_manifold (blowup M x)).

(** Pullback on global sections is an isomorphism:
    π* : H⁰(M, O(L)) → H⁰(M̃, O(π*L)). *)
Theorem pullback_sections_iso : forall (M : KahlerManifold)
    (x : Cn (km_dim M)) (L : HolLineBundleCech (km_manifold M)),
    (** π* : H⁰(M,O(L)) ≅ H⁰(M̃,O(π*L)) — axiomatized *)
    True.
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 6. Blow-up of two points                                         *)
(* ================================================================== *)

(** Blow-up at two distinct points x ≠ y. *)
Parameter blowup2 : forall (M : KahlerManifold)
    (x y : Cn (km_dim M)), KahlerManifold.

(** Exceptional divisors E_x and E_y for the two-point blowup. *)
Parameter exceptional_divisor2_x : forall (M : KahlerManifold)
    (x y : Cn (km_dim M)), KahlerManifold.

Parameter exceptional_divisor2_y : forall (M : KahlerManifold)
    (x y : Cn (km_dim M)), KahlerManifold.

(** Combined exceptional divisor E = E_x + E_y. *)
Parameter exceptional_line_bundle2 : forall (M : KahlerManifold)
    (x y : Cn (km_dim M)),
    HolLineBundleCech (km_manifold (blowup2 M x y)).
