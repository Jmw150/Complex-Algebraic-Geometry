(** * LinAlg/TraceAdAll.v
    Trace of ad u for the four low-dim Lie algebras.

    Standard fact: for any L, tr(ad x) is a linear functional that
    vanishes on [L, L]. For sl(2), heis, cross_product, this means
    tr(ad x) = 0 always. For nonabelian_2d (solvable not nilpotent),
    tr(ad x) is nontrivial.

    These computations show concretely how trace of ad detects
    solvability vs. semisimplicity. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.Lie.LowDimensional.
From Stdlib Require Import List Ring Setoid.
Import ListNotations.

(* ================================================================== *)
(** * 1. Trace of ad on cross_product_lie (so(3))                     *)
(* ================================================================== *)

Section TraceAdCross.
  Context {F : Type} (fld : Field F).

  Local Lemma tac_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring tac_ring : tac_ring_theory.

  Definition trace_ad_cross (u : F * F * F) : F :=
    let bx := cross_product fld u (cr_one fld, cr_zero fld, cr_zero fld) in
    let bh := cross_product fld u (cr_zero fld, cr_one fld, cr_zero fld) in
    let bz := cross_product fld u (cr_zero fld, cr_zero fld, cr_one fld) in
    cr_add fld (fst (fst bx)) (cr_add fld (snd (fst bh)) (snd bz)).

  (** trace(ad u) = 0 for all u in so(3). *)
  Theorem trace_ad_cross_zero : forall u, trace_ad_cross u = cr_zero fld.
  Proof.
    intros [[a b] c]. unfold trace_ad_cross, cross_product. cbn. ring.
  Qed.

End TraceAdCross.

(* ================================================================== *)
(** * 2. Trace of ad on heis                                           *)
(* ================================================================== *)

Section TraceAdHeis.
  Context {F : Type} (fld : Field F).

  Local Lemma tah_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring tah_ring : tah_ring_theory.

  (** heis_bracket(u, v) = (0, 0, u_x*v_y - u_y*v_x). *)
  Definition heis_br (u v : F * F * F) : F * F * F :=
    (cr_zero fld, cr_zero fld,
     cr_add fld (cr_mul fld (fst (fst u)) (snd (fst v)))
                (cr_neg fld (cr_mul fld (snd (fst u)) (fst (fst v))))).

  Definition trace_ad_heis (u : F * F * F) : F :=
    let bx := heis_br u (cr_one fld, cr_zero fld, cr_zero fld) in
    let bh := heis_br u (cr_zero fld, cr_one fld, cr_zero fld) in
    let bz := heis_br u (cr_zero fld, cr_zero fld, cr_one fld) in
    cr_add fld (fst (fst bx)) (cr_add fld (snd (fst bh)) (snd bz)).

  (** trace(ad u) = 0 for all u in heis. *)
  Theorem trace_ad_heis_zero : forall u, trace_ad_heis u = cr_zero fld.
  Proof.
    intros [[a b] c]. unfold trace_ad_heis, heis_br. cbn. ring.
  Qed.

End TraceAdHeis.

(* ================================================================== *)
(** * 3. Trace of ad on nonabelian_2d                                  *)
(* ================================================================== *)

Section TraceAdNonab2d.
  Context {F : Type} (fld : Field F).

  Local Lemma tan_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring tan_ring : tan_ring_theory.

  Definition trace_ad_nonab2d (u : F * F) : F :=
    let bx := nonabelian_2d_bracket fld u (cr_one fld, cr_zero fld) in
    let by_ := nonabelian_2d_bracket fld u (cr_zero fld, cr_one fld) in
    cr_add fld (fst bx) (snd by_).

  (** trace(ad u) = -u_2 for u = (u_1, u_2). NONZERO in general! *)
  Theorem trace_ad_nonab2d_eq : forall u : F * F,
      trace_ad_nonab2d u = cr_neg fld (snd u).
  Proof.
    intros [a b]. unfold trace_ad_nonab2d, nonabelian_2d_bracket. cbn. ring.
  Qed.

  (** trace(ad x) = 0 (since x = (1, 0) has 0 second coord). *)
  Theorem trace_ad_nonab2d_x_zero :
      trace_ad_nonab2d (cr_one fld, cr_zero fld) = cr_zero fld.
  Proof.
    rewrite trace_ad_nonab2d_eq. cbn. ring.
  Qed.

  (** trace(ad y) = -1 (NONZERO in non-trivial fields). *)
  Theorem trace_ad_nonab2d_y :
      trace_ad_nonab2d (cr_zero fld, cr_one fld) =
      cr_neg fld (cr_one fld).
  Proof.
    rewrite trace_ad_nonab2d_eq. cbn. reflexivity.
  Qed.

End TraceAdNonab2d.
