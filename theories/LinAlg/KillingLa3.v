(** * LinAlg/KillingLa3.v
    Concrete Killing form for la3 (sl(2,F) on F^3 with basis x, h, y).

    K(u, v) = trace(ad_u ∘ ad_v).

    For sl(2,F), the standard basis x = (1,0,0), h = (0,1,0), y = (0,0,1)
    gives the Killing matrix [[0, 0, 4]; [0, 8, 0]; [4, 0, 0]] up to
    normalization conventions.

    This module computes K(u, v) directly using the explicit bracket
    formula and the trace_F3 function from Trace.v, without going through
    abstract trace_end. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.Lie.LowDimensional.
Require Import CAG.LinAlg.LinearMap.
Require Import CAG.LinAlg.Concrete.
Require Import CAG.LinAlg.Trace.
From Stdlib Require Import List Ring Setoid.
Import ListNotations.

(* ================================================================== *)
(** * 1. Direct Killing form on F^3 via explicit la3_bracket           *)
(* ================================================================== *)

Section KillingLa3.
  Context {F : Type} (fld : Field F).

  Local Lemma kla3_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring kla3_ring : kla3_ring_theory.

  (** la3_bracket from LowDimensional.v applied at u and v with concrete formula:
      [u, v] = (2(uh*vx - ux*vh), ux*vy - uy*vx, 2(uy*vh - uh*vy))
      where u = (ux, uh, uy), v = (vx, vh, vy). *)

  (** ad u v = la3_bracket u v. *)
  Definition kla3_ad (u v : F * F * F) : F * F * F :=
    la3_bracket fld u v.

  (** ad u (ad v w) = la3_bracket u (la3_bracket v w). *)
  Definition kla3_adad (u v w : F * F * F) : F * F * F :=
    la3_bracket fld u (la3_bracket fld v w).

  (** Apply ad u ∘ ad v to a basis vector and extract the
      relevant trace-component. *)
  Definition kla3_trace_uv (u v : F * F * F) : F :=
    (* trace = (ad u (ad v e1)).fst.fst + (ad u (ad v e2)).fst.snd
              + (ad u (ad v e3)).snd                                *)
    cr_add fld
      (fst (fst (kla3_adad u v (cr_one fld, cr_zero fld, cr_zero fld))))
      (cr_add fld
        (snd (fst (kla3_adad u v (cr_zero fld, cr_one fld, cr_zero fld))))
        (snd (kla3_adad u v (cr_zero fld, cr_zero fld, cr_one fld)))).

  (** Killing form K(u, v) = trace(ad u ∘ ad v). *)
  Definition killing_la3 (u v : F * F * F) : F := kla3_trace_uv u v.

  (** la3 standard basis. *)
  Notation la3x := (cr_one fld, cr_zero fld, cr_zero fld) (only parsing).
  Notation la3h := (cr_zero fld, cr_one fld, cr_zero fld) (only parsing).
  Notation la3y := (cr_zero fld, cr_zero fld, cr_one fld) (only parsing).

  (* ============================================================== *)
  (** ** Explicit Killing form values                                *)
  (* ============================================================== *)

  (** K(x, x) = 0. *)
  Theorem killing_la3_xx : killing_la3 la3x la3x = cr_zero fld.
  Proof.
    unfold killing_la3, kla3_trace_uv, kla3_adad, la3_bracket. cbn. ring.
  Qed.

  (** K(y, y) = 0. *)
  Theorem killing_la3_yy : killing_la3 la3y la3y = cr_zero fld.
  Proof.
    unfold killing_la3, kla3_trace_uv, kla3_adad, la3_bracket. cbn. ring.
  Qed.

  (** K(h, h) = 8 = 2 * 4. (Using the convention 2 := 1+1, 8 := 2*2*2.) *)
  Theorem killing_la3_hh : killing_la3 la3h la3h =
    cr_mul fld
      (cr_add fld (cr_one fld) (cr_one fld))
      (cr_mul fld
        (cr_add fld (cr_one fld) (cr_one fld))
        (cr_add fld (cr_one fld) (cr_one fld))).
  Proof.
    unfold killing_la3, kla3_trace_uv, kla3_adad, la3_bracket. cbn. ring.
  Qed.

  (** K(x, y) = 4 = 2 * 2. *)
  Theorem killing_la3_xy : killing_la3 la3x la3y =
    cr_mul fld
      (cr_add fld (cr_one fld) (cr_one fld))
      (cr_add fld (cr_one fld) (cr_one fld)).
  Proof.
    unfold killing_la3, kla3_trace_uv, kla3_adad, la3_bracket. cbn. ring.
  Qed.

  (** K(y, x) = 4 (symmetric). *)
  Theorem killing_la3_yx : killing_la3 la3y la3x =
    cr_mul fld
      (cr_add fld (cr_one fld) (cr_one fld))
      (cr_add fld (cr_one fld) (cr_one fld)).
  Proof.
    unfold killing_la3, kla3_trace_uv, kla3_adad, la3_bracket. cbn. ring.
  Qed.

  (** K(x, h) = 0. *)
  Theorem killing_la3_xh : killing_la3 la3x la3h = cr_zero fld.
  Proof.
    unfold killing_la3, kla3_trace_uv, kla3_adad, la3_bracket. cbn. ring.
  Qed.

  (** K(h, x) = 0 (symmetric). *)
  Theorem killing_la3_hx : killing_la3 la3h la3x = cr_zero fld.
  Proof.
    unfold killing_la3, kla3_trace_uv, kla3_adad, la3_bracket. cbn. ring.
  Qed.

  (** K(y, h) = 0. *)
  Theorem killing_la3_yh : killing_la3 la3y la3h = cr_zero fld.
  Proof.
    unfold killing_la3, kla3_trace_uv, kla3_adad, la3_bracket. cbn. ring.
  Qed.

  (** K(h, y) = 0. *)
  Theorem killing_la3_hy : killing_la3 la3h la3y = cr_zero fld.
  Proof.
    unfold killing_la3, kla3_trace_uv, kla3_adad, la3_bracket. cbn. ring.
  Qed.

  (* ============================================================== *)
  (** ** Symmetry: K(u, v) = K(v, u) (general identity)              *)
  (* ============================================================== *)

  Theorem killing_la3_symm : forall u v, killing_la3 u v = killing_la3 v u.
  Proof.
    intros [[ux uh] uy] [[vx vh] vy].
    unfold killing_la3, kla3_trace_uv, kla3_adad, la3_bracket. cbn. ring.
  Qed.

  (* ============================================================== *)
  (** ** Bilinearity: K is bilinear                                    *)
  (* ============================================================== *)

  Theorem killing_la3_add_l : forall u v w,
      killing_la3 (la3_add fld u w) v =
      cr_add fld (killing_la3 u v) (killing_la3 w v).
  Proof.
    intros [[ux uh] uy] [[vx vh] vy] [[wx wh] wy].
    unfold killing_la3, kla3_trace_uv, kla3_adad, la3_bracket, la3_add, mkT,
           tF_x, tF_h, tF_y. cbn. ring.
  Qed.

  Theorem killing_la3_add_r : forall u v w,
      killing_la3 u (la3_add fld v w) =
      cr_add fld (killing_la3 u v) (killing_la3 u w).
  Proof.
    intros [[ux uh] uy] [[vx vh] vy] [[wx wh] wy].
    unfold killing_la3, kla3_trace_uv, kla3_adad, la3_bracket, la3_add, mkT,
           tF_x, tF_h, tF_y. cbn. ring.
  Qed.

  Theorem killing_la3_scale_l : forall c u v,
      killing_la3 (la3_scale fld c u) v =
      cr_mul fld c (killing_la3 u v).
  Proof.
    intros c [[ux uh] uy] [[vx vh] vy].
    unfold killing_la3, kla3_trace_uv, kla3_adad, la3_bracket, la3_scale, mkT,
           tF_x, tF_h, tF_y. cbn. ring.
  Qed.

  Theorem killing_la3_scale_r : forall c u v,
      killing_la3 u (la3_scale fld c v) =
      cr_mul fld c (killing_la3 u v).
  Proof.
    intros c [[ux uh] uy] [[vx vh] vy].
    unfold killing_la3, kla3_trace_uv, kla3_adad, la3_bracket, la3_scale, mkT,
           tF_x, tF_h, tF_y. cbn. ring.
  Qed.

  (* ============================================================== *)
  (** ** Non-degeneracy in characteristic ≠ 2                         *)
  (* ============================================================== *)

  (** K(u, x) = 4·u_y. *)
  Lemma killing_la3_ux_eq : forall u : F * F * F,
      let '(_, _, uy) := u in
      killing_la3 u la3x = cr_mul fld
        (cr_mul fld (cr_add fld (cr_one fld) (cr_one fld))
                    (cr_add fld (cr_one fld) (cr_one fld)))
        uy.
  Proof.
    intros [[ux uh] uy].
    unfold killing_la3, kla3_trace_uv, kla3_adad, la3_bracket. cbn. ring.
  Qed.

  (** K(u, h) = 8·u_h. *)
  Lemma killing_la3_uh_eq : forall u : F * F * F,
      let '(_, uh, _) := u in
      killing_la3 u la3h = cr_mul fld
        (cr_mul fld (cr_add fld (cr_one fld) (cr_one fld))
          (cr_mul fld (cr_add fld (cr_one fld) (cr_one fld))
                      (cr_add fld (cr_one fld) (cr_one fld))))
        uh.
  Proof.
    intros [[ux uh] uy].
    unfold killing_la3, kla3_trace_uv, kla3_adad, la3_bracket. cbn. ring.
  Qed.

  (** K(u, y) = 4·u_x. *)
  Lemma killing_la3_uy_eq : forall u : F * F * F,
      let '(ux, _, _) := u in
      killing_la3 u la3y = cr_mul fld
        (cr_mul fld (cr_add fld (cr_one fld) (cr_one fld))
                    (cr_add fld (cr_one fld) (cr_one fld)))
        ux.
  Proof.
    intros [[ux uh] uy].
    unfold killing_la3, kla3_trace_uv, kla3_adad, la3_bracket. cbn. ring.
  Qed.

  (** Non-degeneracy: when char ≠ 2, K(u, v) = 0 for all v implies u = 0. *)
  Theorem killing_la3_nondeg :
      cr_add fld (cr_one fld) (cr_one fld) <> cr_zero fld ->
      forall u : F * F * F,
        (forall v, killing_la3 u v = cr_zero fld) ->
        u = (cr_zero fld, cr_zero fld, cr_zero fld).
  Proof.
    intros Htwo [[ux uh] uy] Hzero.
    pose proof (Hzero la3x) as Hx.
    pose proof (Hzero la3h) as Hh.
    pose proof (Hzero la3y) as Hy.
    pose proof (killing_la3_ux_eq (ux, uh, uy)) as Heq_ux.
    pose proof (killing_la3_uh_eq (ux, uh, uy)) as Heq_uh.
    pose proof (killing_la3_uy_eq (ux, uh, uy)) as Heq_uy.
    cbn in Heq_ux, Heq_uh, Heq_uy.
    rewrite Heq_ux in Hx. rewrite Heq_uh in Hh. rewrite Heq_uy in Hy.
    (* From Hx: 4 * uy = 0. Since 4 ≠ 0 (char ≠ 2), uy = 0. *)
    set (two := cr_add fld (cr_one fld) (cr_one fld)).
    set (four := cr_mul fld two two).
    set (eight := cr_mul fld two four).
    fold two four eight in Hx, Hh, Hy.
    assert (Hfour : four <> cr_zero fld).
    { unfold four.
      intros Habsurd.
      destruct (field_no_zero_div fld two two Habsurd) as [H | H];
        [unfold two in H; exact (Htwo H) | unfold two in H; exact (Htwo H)]. }
    assert (Height : eight <> cr_zero fld).
    { unfold eight. intros Habsurd.
      destruct (field_no_zero_div fld two four Habsurd) as [H | H];
        [unfold two in H; exact (Htwo H) | exact (Hfour H)]. }
    assert (Huy : uy = cr_zero fld).
    { destruct (field_no_zero_div fld four uy Hx) as [H | H];
        [contradiction|exact H]. }
    assert (Huh : uh = cr_zero fld).
    { destruct (field_no_zero_div fld eight uh Hh) as [H | H];
        [contradiction|exact H]. }
    assert (Hux : ux = cr_zero fld).
    { destruct (field_no_zero_div fld four ux Hy) as [H | H];
        [contradiction|exact H]. }
    rewrite Hux, Huh, Huy. reflexivity.
  Qed.

End KillingLa3.
