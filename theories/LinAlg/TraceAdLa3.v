(** * LinAlg/TraceAdLa3.v
    Trace of ad u for u ∈ sl(2,F) is always 0.

    This is the standard fact: for any Lie algebra L, the linear
    functional x ↦ tr(ad x) vanishes (since tr ad is a derivation
    on the abelian image, must be 0).

    For sl(2,F) we verify this directly via the explicit ad action. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.Lie.LowDimensional.
From Stdlib Require Import List Ring Setoid.
Import ListNotations.

Section TraceAdLa3.
  Context {F : Type} (fld : Field F).

  Local Lemma tal3_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring tal3_ring : tal3_ring_theory.

  (** Trace of ad u (operating on F^3) computed via diagonal sum. *)
  Definition trace_ad_la3 (u : F * F * F) : F :=
    let bx := la3_bracket fld u (cr_one fld, cr_zero fld, cr_zero fld) in
    let bh := la3_bracket fld u (cr_zero fld, cr_one fld, cr_zero fld) in
    let by_ := la3_bracket fld u (cr_zero fld, cr_zero fld, cr_one fld) in
    cr_add fld
      (fst (fst bx))
      (cr_add fld
        (snd (fst bh))
        (snd by_)).

  (** trace(ad la3_x) = 0. *)
  Theorem trace_ad_la3_x : trace_ad_la3 (la3_x fld) = cr_zero fld.
  Proof.
    unfold trace_ad_la3, la3_bracket, la3_x, mkT, tF_x, tF_h, tF_y. cbn. ring.
  Qed.

  (** trace(ad la3_h) = 0. *)
  Theorem trace_ad_la3_h : trace_ad_la3 (la3_h fld) = cr_zero fld.
  Proof.
    unfold trace_ad_la3, la3_bracket, la3_h, mkT, tF_x, tF_h, tF_y. cbn. ring.
  Qed.

  (** trace(ad la3_y) = 0. *)
  Theorem trace_ad_la3_y : trace_ad_la3 (la3_y fld) = cr_zero fld.
  Proof.
    unfold trace_ad_la3, la3_bracket, la3_y, mkT, tF_x, tF_h, tF_y. cbn. ring.
  Qed.

  (** trace(ad u) = 0 for all u ∈ sl(2,F). *)
  Theorem trace_ad_la3_all : forall u : F * F * F, trace_ad_la3 u = cr_zero fld.
  Proof.
    intros [[a b] c]. unfold trace_ad_la3, la3_bracket. cbn. ring.
  Qed.

End TraceAdLa3.
