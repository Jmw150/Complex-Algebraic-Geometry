(** * DiffGeom/Section.v — Sections of trivial fibre bundles.

    A *section* of a [Bundle X F] is a function [X -> F].  When the
    fibre [F] carries a vector-space structure, sections inherit a
    pointwise vector-space structure.

    This file packages the section infrastructure used by
    [SmoothManifold.v] (vector fields = sections of the tangent bundle)
    and [BundleCovariantDerivatives.v] (sections of a hermitian
    bundle).  Both currently use a unit-fibre model under Infra-7;
    this file is the underlying abstraction.

    Provenance: Infra-7 (2026-04-30). *)

From Stdlib Require Import FunctionalExtensionality.
From CAG Require Import LieAlgebra.   (* for [VectorSpace] *)
From CAG Require Import Complex.      (* for [CComplex] *)
From CAG Require Import DiffGeom.Bundle.

(* ================================================================== *)
(** * 1. Sections                                                      *)
(* ================================================================== *)

(** A section of a bundle [B] over base [X] is a function from [X] to
    the fibre [F]. *)
Definition Section {X F : Type} (_ : Bundle X F) : Type := X -> F.

(** Pointwise zero, addition, and scalar multiplication of sections,
    given operations on the fibre. *)
Definition section_zero_pt {X F : Type} (B : Bundle X F) (z : F)
  : Section B := fun _ => z.

Definition section_add_pt {X F : Type} (B : Bundle X F)
    (add : F -> F -> F) (s t : Section B) : Section B :=
  fun p => add (s p) (t p).

Definition section_scale_pt {X F : Type} (B : Bundle X F)
    (scale : CComplex -> F -> F) (c : CComplex) (s : Section B) : Section B :=
  fun p => scale c (s p).

Definition section_neg_pt {X F : Type} (B : Bundle X F)
    (neg : F -> F) (s : Section B) : Section B :=
  fun p => neg (s p).

(* ================================================================== *)
(** * 2. Sections form a vector space when the fibre does              *)
(* ================================================================== *)

(** Given a vector-space structure on the fibre, the sections of [B]
    inherit a pointwise vector-space structure.  All laws follow from
    the corresponding fibre laws via [functional_extensionality]. *)
Definition sections_vs_pt {X F : Type} (B : Bundle X F) (vsF : VectorSpace F)
  : VectorSpace (Section B).
Proof.
  refine (mkVS (Section B)
    (section_add_pt   B (vs_add   vsF))
    (section_scale_pt B (vs_scale vsF))
    (section_zero_pt  B (vs_zero  vsF))
    (section_neg_pt   B (vs_neg   vsF))
    _ _ _ _ _ _ _ _).
  - (* vs_add_assoc *)
    intros u v w. apply functional_extensionality.
    intros p. unfold section_add_pt. apply (vs_add_assoc _ vsF).
  - (* vs_add_comm *)
    intros u v. apply functional_extensionality.
    intros p. unfold section_add_pt. apply (vs_add_comm _ vsF).
  - (* vs_add_zero_r *)
    intros v. apply functional_extensionality.
    intros p. unfold section_add_pt, section_zero_pt.
    apply (vs_add_zero_r _ vsF).
  - (* vs_add_neg_r *)
    intros v. apply functional_extensionality.
    intros p. unfold section_add_pt, section_neg_pt, section_zero_pt.
    apply (vs_add_neg_r _ vsF).
  - (* vs_scale_one *)
    intros v. apply functional_extensionality.
    intros p. unfold section_scale_pt. apply (vs_scale_one _ vsF).
  - (* vs_scale_assoc *)
    intros a b v. apply functional_extensionality.
    intros p. unfold section_scale_pt. apply (vs_scale_assoc _ vsF).
  - (* vs_scale_add_v *)
    intros a u v. apply functional_extensionality.
    intros p. unfold section_scale_pt, section_add_pt.
    apply (vs_scale_add_v _ vsF).
  - (* vs_scale_add_s *)
    intros a b v. apply functional_extensionality.
    intros p. unfold section_scale_pt, section_add_pt.
    apply (vs_scale_add_s _ vsF).
Defined.

(* ================================================================== *)
(** * 3. The unit-fibre case                                           *)
(* ================================================================== *)

(** [unit] is the zero-dimensional vector space.  Every operation is
    [tt]; every law holds by [reflexivity] / [unit]-eta. *)
Lemma unit_eq_tt : forall u : unit, u = tt.
Proof. intros []; reflexivity. Qed.

Definition unit_VectorSpace : VectorSpace unit.
Proof.
  refine (mkVS unit
    (fun _ _ => tt) (fun _ _ => tt) tt (fun _ => tt)
    _ _ _ _ _ _ _ _);
    intros; try reflexivity;
    repeat match goal with u : unit |- _ => destruct u end; reflexivity.
Defined.

(** Sections of the unit bundle form the trivial vector space.
    Equivalently every section is propositionally equal. *)
Lemma section_unit_eq : forall {X : Type} (s t : Section (unit_bundle X)), s = t.
Proof.
  intros X s t. apply functional_extensionality.
  intros p. destruct (s p), (t p). reflexivity.
Qed.
