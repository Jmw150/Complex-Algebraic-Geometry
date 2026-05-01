(** * LinAlg/InnerProduct.v
    Standard dot product on F^2 and F^3, and connections to Killing forms. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.LinAlg.Concrete.
From Stdlib Require Import List Ring Setoid.
Import ListNotations.

(* ================================================================== *)
(** * 1. Dot product on F^2                                           *)
(* ================================================================== *)

Section DotF2.
  Context {F : Type} (fld : Field F).

  Local Lemma df2_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring df2_ring : df2_ring_theory.

  Definition dot_F2 (u v : F * F) : F :=
    cr_add fld (cr_mul fld (fst u) (fst v)) (cr_mul fld (snd u) (snd v)).

  Theorem dot_F2_symm : forall u v, dot_F2 u v = dot_F2 v u.
  Proof. intros [a b] [c d]. unfold dot_F2. cbn. ring. Qed.

  Theorem dot_F2_add_l : forall u v w,
      dot_F2 (cr_add fld (fst u) (fst w), cr_add fld (snd u) (snd w)) v =
      cr_add fld (dot_F2 u v) (dot_F2 w v).
  Proof. intros [a b] [c d] [e f]. unfold dot_F2. cbn. ring. Qed.

  Theorem dot_F2_scale_l : forall (a : F) (u v : F * F),
      dot_F2 (cr_mul fld a (fst u), cr_mul fld a (snd u)) v =
      cr_mul fld a (dot_F2 u v).
  Proof. intros a [b1 b2] [c d]. unfold dot_F2. cbn. ring. Qed.

  (** Non-degeneracy: u ⊥ everything → u = 0. *)
  Theorem dot_F2_nondeg :
      cr_one fld <> cr_zero fld ->
      forall u : F * F,
        (forall v, dot_F2 u v = cr_zero fld) -> u = (cr_zero fld, cr_zero fld).
  Proof.
    intros Hone [a b] Hall.
    pose proof (Hall (cr_one fld, cr_zero fld)) as H1.
    pose proof (Hall (cr_zero fld, cr_one fld)) as H2.
    unfold dot_F2 in H1, H2. cbn in H1, H2.
    assert (Ha : a = cr_zero fld).
    { transitivity (cr_add fld (cr_mul fld a (cr_one fld))
                              (cr_mul fld b (cr_zero fld))).
      - ring.
      - exact H1. }
    assert (Hb : b = cr_zero fld).
    { transitivity (cr_add fld (cr_mul fld a (cr_zero fld))
                              (cr_mul fld b (cr_one fld))).
      - ring.
      - exact H2. }
    rewrite Ha, Hb. reflexivity.
  Qed.

End DotF2.

(* ================================================================== *)
(** * 2. Dot product on F^3                                           *)
(* ================================================================== *)

Section DotF3.
  Context {F : Type} (fld : Field F).

  Local Lemma df3_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring df3_ring : df3_ring_theory.

  Definition dot_F3 (u v : F * F * F) : F :=
    cr_add fld (cr_mul fld (fst (fst u)) (fst (fst v)))
      (cr_add fld (cr_mul fld (snd (fst u)) (snd (fst v)))
                  (cr_mul fld (snd u) (snd v))).

  Theorem dot_F3_symm : forall u v, dot_F3 u v = dot_F3 v u.
  Proof. intros [[a b] c] [[d e] f]. unfold dot_F3. cbn. ring. Qed.

  (** Non-degeneracy. *)
  Theorem dot_F3_nondeg :
      cr_one fld <> cr_zero fld ->
      forall u : F * F * F,
        (forall v, dot_F3 u v = cr_zero fld) ->
        u = (cr_zero fld, cr_zero fld, cr_zero fld).
  Proof.
    intros Hone [[a b] c] Hall.
    pose proof (Hall (cr_one fld, cr_zero fld, cr_zero fld)) as H1.
    pose proof (Hall (cr_zero fld, cr_one fld, cr_zero fld)) as H2.
    pose proof (Hall (cr_zero fld, cr_zero fld, cr_one fld)) as H3.
    unfold dot_F3 in H1, H2, H3. cbn in H1, H2, H3.
    assert (Ha : a = cr_zero fld).
    { transitivity (cr_add fld (cr_mul fld a (cr_one fld))
                              (cr_add fld (cr_mul fld b (cr_zero fld))
                                          (cr_mul fld c (cr_zero fld)))).
      - ring.
      - exact H1. }
    assert (Hb : b = cr_zero fld).
    { transitivity (cr_add fld (cr_mul fld a (cr_zero fld))
                              (cr_add fld (cr_mul fld b (cr_one fld))
                                          (cr_mul fld c (cr_zero fld)))).
      - ring.
      - exact H2. }
    assert (Hc : c = cr_zero fld).
    { transitivity (cr_add fld (cr_mul fld a (cr_zero fld))
                              (cr_add fld (cr_mul fld b (cr_zero fld))
                                          (cr_mul fld c (cr_one fld)))).
      - ring.
      - exact H3. }
    rewrite Ha, Hb, Hc. reflexivity.
  Qed.

End DotF3.
