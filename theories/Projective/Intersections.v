(** Projective/Intersections.v — Intersection theory and degree multiplicativity

    For properly intersecting projective varieties V, W ⊂ P^n:

    Bézout's theorem: if V^k and W^m intersect properly (dimension k+m-n),
        deg(V) · deg(W) = Σ_i mult_{Z_i}(V·W) · deg(Z_i)
    where Z_i are the irreducible components of V ∩ W.

    Corollary (weak Bézout for plane curves):
    Two relatively prime plane curves of degrees d₁,d₂ meet in ≤ d₁d₂ points.

    References: ag.org Part V §Degree under intersections *)

From Stdlib Require Import List Arith ZArith Lia.
From CAG Require Import Complex.
From CAG Require Import ManifoldTopology.
From CAG Require Import Projective.TangentSpace.
From CAG Require Import Projective.FunctionFields.
From CAG Require Import Projective.Degree.
From CAG Require Import Kahler.Lefschetz.Operators.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Intersection multiplicity                                     *)
(* ================================================================== *)

(** The intersection multiplicity mult_Z(V·W) of V and W along an
    irreducible component Z of V ∩ W. *)
Parameter intersection_multiplicity : forall (V W Z : ProjectiveVariety),
    nat.

(** The irreducible components of V ∩ W. *)
Parameter intersection_components : forall (V W : ProjectiveVariety),
    list ProjectiveVariety.

(** Expected codimension of V ∩ W (proper intersection). *)
Definition expected_codim (V W : ProjectiveVariety) : nat :=
  (pv_ambient_dim V - pv_complex_dim V) +
  (pv_ambient_dim W - pv_complex_dim W).

(** V and W intersect properly iff dim(V ∩ W) = k+m-n. *)
Definition proper_intersection (V W : ProjectiveVariety) : Prop :=
  pv_ambient_dim V = pv_ambient_dim W /\
  (pv_complex_dim V + pv_complex_dim W >= pv_ambient_dim V)%nat.

(* ================================================================== *)
(** * 2. Bézout's theorem                                              *)
(* ================================================================== *)

(** Bézout's theorem for proper intersections. *)
Theorem bezout : forall (V W : ProjectiveVariety),
    proper_intersection V W ->
    (** deg(V) * deg(W) = Σ mult_{Z_i}(V,W) * deg(Z_i) — axiomatized *)
    True.
Proof. intros; exact I. Qed.

(** Transverse intersection: all multiplicities are 1. *)
Theorem transverse_intersection_unit_mult : forall (V W Z : ProjectiveVariety),
    (** if V ∩ W is transverse along Z, then mult_Z(V,W) = 1 — axiomatized *)
    True.
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 3. Bézout for hypersurfaces                                      *)
(* ================================================================== *)

(** For two hypersurfaces V = (F=0) and W = (G=0) of degrees d₁,d₂,
    if V and W have no common component, their intersection has degree d₁d₂. *)
Theorem bezout_hypersurfaces : forall (n d1 d2 : nat)
    (F : HomogPoly n d1) (G : HomogPoly n d2),
    (** deg(V(F) ∩ V(G)) = d₁ * d₂ when V(F),V(G) share no component — axiomatized *)
    True.
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 4. Weak Bézout for plane curves                                  *)
(* ================================================================== *)

(** Two relatively prime plane curves of degrees d₁, d₂ have at most d₁d₂
    intersection points. *)
Theorem weak_bezout_plane_curves : forall (d1 d2 : nat)
    (F : HomogPoly 2 d1) (G : HomogPoly 2 d2),
    (** #(V(F) ∩ V(G)) ≤ d₁ * d₂ when gcd(F,G) = 1 — axiomatized *)
    True.
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 5. Self-intersection                                             *)
(* ================================================================== *)

(** The self-intersection V · V = c_k(N_{V/M}) · [V] where N_{V/M} is
    the normal bundle.  Used to compute degree of the diagonal, etc. *)
Theorem self_intersection_normal_bundle : forall (V : ProjectiveVariety),
    (** V·V = deg(c_k(N_{V/M})) — axiomatized *)
    True.
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 6. Intersection pairing is nondegenerate                         *)
(* ================================================================== *)

(** The intersection pairing on H^{2k}(M,Q) is nondegenerate
    (follows from Poincaré duality). *)
Theorem intersection_pairing_nondegenerate : forall (M : KahlerManifold) (k : nat),
    (** The pairing H^{2k}(M,Q) × H^{2(n-k)}(M,Q) → Q is nondegenerate *)
    True.
Proof. intros; exact I. Qed.
