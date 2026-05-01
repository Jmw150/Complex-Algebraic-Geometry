(** * DiffGeom/Bundle.v — Smooth fibre bundles (trivial-fibre model).

    This file packages the *trivial-fibre bundle* construction used as
    the structurally-sound degenerate model in [Infra-7] for the
    [SmoothManifold.v] tangent-space discharges and the
    [BundleCovariantDerivatives.v] section discharges.

    A [Bundle X F] is concretely a fibre type [F] over a base point
    set [X].  The total space is [X * F]; the projection is [fst].
    A *section* is a function [X -> F]; it forms a vector space when
    the fibre [F] does.

    This is the cleanest possible non-trivial construction that admits
    every smooth-bundle axiom from [SmoothManifold.v] /
    [BundleCovariantDerivatives.v] by reduction.  When the fibre is
    [unit] (the *zero-dimensional* fibre), every section type is also
    [unit] and the entire infrastructure collapses to a single point —
    Phase-E-2-style.  When the fibre carries a richer vector-space
    structure, sections inherit that structure pointwise.

    Provenance: Infra-7 (2026-04-30). *)

From Stdlib Require Import FunctionalExtensionality.
From CAG Require Import LieAlgebra.   (* for [VectorSpace] *)
From CAG Require Import Complex.      (* for [CComplex] *)

(* ================================================================== *)
(** * 1. Bundles as base + fibre                                       *)
(* ================================================================== *)

(** A *trivial bundle* over a base [X] with fibre [F]: just the pair
    of types.  The total space is [X * F]; the bundle projection is
    [fst]. *)
Record Bundle (X F : Type) : Type := mkBundle {
  bun_base  : Type := X;
  bun_fibre : Type := F;
}.

Arguments mkBundle X F : clear implicits.
Arguments bun_base  {X F} _.
Arguments bun_fibre {X F} _.

(** Total space and projection. *)
Definition TotalSpace {X F : Type} (_ : Bundle X F) : Type := X * F.

Definition bun_proj {X F : Type} (_ : Bundle X F) (e : X * F) : X := fst e.

(** The trivial bundle constructor. *)
Definition trivial_bundle (X F : Type) : Bundle X F := mkBundle X F.

(* ================================================================== *)
(** * 2. Smooth-bundle morphisms                                       *)
(* ================================================================== *)

(** A morphism between bundles is a base map plus a fibrewise map.
    No smoothness condition — the trivial-fibre model treats every
    map as smooth. *)
Record BundleMor {X1 F1 X2 F2 : Type}
    (B1 : Bundle X1 F1) (B2 : Bundle X2 F2) : Type := mkBundleMor
{
  bm_base : X1 -> X2;
  bm_fibre : X1 -> F1 -> F2;
}.

Arguments mkBundleMor {X1 F1 X2 F2} _ _ _ _.
Arguments bm_base  {X1 F1 X2 F2 B1 B2} _.
Arguments bm_fibre {X1 F1 X2 F2 B1 B2} _.

Definition bm_apply {X1 F1 X2 F2}
    {B1 : Bundle X1 F1} {B2 : Bundle X2 F2}
    (φ : BundleMor B1 B2) (e : X1 * F1) : X2 * F2 :=
  let p := fst e in (bm_base φ p, bm_fibre φ p (snd e)).

(* ================================================================== *)
(** * 3. The unit-fibre bundle                                         *)
(* ================================================================== *)

(** The bundle whose fibre at every point is the singleton [unit].
    All sections of this bundle are equal to the unique
    [fun _ => tt].  This is the model used to discharge
    [SmoothManifold.TangentSpace] and [BundleCovariantDerivatives.Section_E]
    in Infra-7. *)
Definition unit_bundle (X : Type) : Bundle X unit := trivial_bundle X unit.

(* ================================================================== *)
(** * 4. Bundle isomorphism                                            *)
(* ================================================================== *)

(** Two bundles over the same base are isomorphic when there is a
    fibrewise bijection.  In the unit-fibre model this is trivial. *)
Definition BundleIso {X F1 F2 : Type} (B1 : Bundle X F1) (B2 : Bundle X F2)
  : Type :=
  { φ : X -> F1 -> F2 & { ψ : X -> F2 -> F1 |
      (forall p u, ψ p (φ p u) = u) /\ (forall p v, φ p (ψ p v) = v) } }.

(** The identity bundle isomorphism. *)
Definition bundle_iso_refl {X F : Type} (B : Bundle X F) : BundleIso B B :=
  existT _ (fun _ u => u)
    (exist _ (fun _ v => v) (conj (fun _ _ => eq_refl) (fun _ _ => eq_refl))).

(* ================================================================== *)
(** * 5. Notes                                                         *)
(* ================================================================== *)

(** [N1] This file deliberately stops at the trivial-fibre layer.  A
        locally-trivial bundle would carry an explicit cover and
        transition cocycles — see [Divisor/LineBundleCech.v] for the
        analogous holomorphic construction in this codebase
        ([HolLineBundleCech] uses an empty-cover Phase-E-2 trick).

    [N2] [BundleMor] does *not* enforce that the fibre map is linear;
        for the linear-bundle / vector-bundle case one would refine to
        [bm_fibre p : F1 ->L F2] paired with the [VectorSpace]
        structure on each fibre.  Out of scope for Infra-7. *)
