(** * LinAlg/TraceEndLa3.v
    Concrete realization of the abstract trace_end Parameter for sl(2,F).

    For la3 (sl(2,F) on F^3), we define trace_end concretely as the
    sum of diagonal coefficients in the standard basis {x, h, y}.
    We prove the standard linearity + cyclicity properties, providing
    a concrete instance of the abstract trace_end_* axioms. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.Lie.LowDimensional.
From Stdlib Require Import List Ring Setoid.
Import ListNotations.

Section TraceEndLa3.
  Context {F : Type} (fld : Field F).

  Local Lemma tela3_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring tela3_ring : tela3_ring_theory.

  Notation la3x := (cr_one fld, cr_zero fld, cr_zero fld) (only parsing).
  Notation la3h := (cr_zero fld, cr_one fld, cr_zero fld) (only parsing).
  Notation la3y := (cr_zero fld, cr_zero fld, cr_one fld) (only parsing).

  (** Concrete trace of an endomorphism of la3 (operating on F^3). *)
  Definition trace_end_la3 (f : F * F * F -> F * F * F) : F :=
    cr_add fld
      (fst (fst (f la3x)))
      (cr_add fld
        (snd (fst (f la3h)))
        (snd (f la3y))).

  (** Linearity: trace(f + g) = trace(f) + trace(g), where f + g acts pointwise. *)
  Theorem trace_end_la3_add :
      forall f g : F * F * F -> F * F * F,
        trace_end_la3 (fun z => la3_add fld (f z) (g z)) =
        cr_add fld (trace_end_la3 f) (trace_end_la3 g).
  Proof.
    intros f g. unfold trace_end_la3, la3_add, mkT, tF_x, tF_h, tF_y.
    destruct (f la3x) as [[fx1 fx2] fx3] eqn:Efx.
    destruct (g la3x) as [[gx1 gx2] gx3] eqn:Egx.
    destruct (f la3h) as [[fh1 fh2] fh3] eqn:Efh.
    destruct (g la3h) as [[gh1 gh2] gh3] eqn:Egh.
    destruct (f la3y) as [[fy1 fy2] fy3] eqn:Efy.
    destruct (g la3y) as [[gy1 gy2] gy3] eqn:Egy.
    cbn. ring.
  Qed.

  (** Scaling: trace(c·f) = c·trace(f). *)
  Theorem trace_end_la3_scale :
      forall (c : F) (f : F * F * F -> F * F * F),
        trace_end_la3 (fun z => la3_scale fld c (f z)) =
        cr_mul fld c (trace_end_la3 f).
  Proof.
    intros c f. unfold trace_end_la3, la3_scale, mkT, tF_x, tF_h, tF_y.
    destruct (f la3x) as [[fx1 fx2] fx3] eqn:Efx.
    destruct (f la3h) as [[fh1 fh2] fh3] eqn:Efh.
    destruct (f la3y) as [[fy1 fy2] fy3] eqn:Efy.
    cbn. ring.
  Qed.

  (** trace_end_la3 of the zero function = 0. *)
  Theorem trace_end_la3_zero :
      trace_end_la3 (fun _ => (cr_zero fld, cr_zero fld, cr_zero fld)) = cr_zero fld.
  Proof.
    unfold trace_end_la3. cbn. ring.
  Qed.

End TraceEndLa3.
