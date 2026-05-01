(** * LinAlg/Trace.v
    Trace of endomorphisms relative to standard bases of F, F^2, F^3.

    For F (1-dim): trace(f) = f(1).
    For F^2 (2-dim): trace(f) = (f(e_1)).fst + (f(e_2)).snd.
    For F^3 (3-dim): trace(f) = (f(e_1)).fst + (f(e_2)).snd_fst + (f(e_3)).snd.

    Key results:
    - Trace is linear: trace(f+g) = trace(f) + trace(g).
    - Trace is scaled: trace(c·f) = c·trace(f).
    - Trace is cyclic: trace(f∘g) = trace(g∘f).
    - Trace of zero endomorphism is 0.
    - Trace of negation. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.LinAlg.Basis.
Require Import CAG.LinAlg.LinearMap.
Require Import CAG.LinAlg.Concrete.
From Stdlib Require Import List Ring Setoid.
Import ListNotations.

(* ================================================================== *)
(** * 1. Trace on End(F)                                              *)
(* ================================================================== *)

Section TraceF.
  Context {F : Type} (fld : Field F).

  (** Trace of an endomorphism of F: just evaluate at 1. *)
  Definition trace_F (f : EndF (F_as_VS fld)) : F :=
    lm_fn f (cr_one fld).

  Lemma trace_F_zero : trace_F (end_zero (F_as_VS fld)) = cr_zero fld.
  Proof. unfold trace_F, end_zero. reflexivity. Qed.

  Lemma trace_F_add : forall (f g : EndF (F_as_VS fld)),
      trace_F (end_add f g) = cr_add fld (trace_F f) (trace_F g).
  Proof. intros f g. unfold trace_F, end_add. reflexivity. Qed.

  Lemma trace_F_scale : forall (a : F) (f : EndF (F_as_VS fld)),
      trace_F (end_scale a f) = cr_mul fld a (trace_F f).
  Proof. intros a f. unfold trace_F, end_scale. reflexivity. Qed.

  Lemma trace_F_neg : forall (f : EndF (F_as_VS fld)),
      trace_F (end_neg f) = cr_neg fld (trace_F f).
  Proof. intro f. unfold trace_F, end_neg. reflexivity. Qed.

  (** Cyclicity for End(F) is trivial: F is 1-dim so trace_F (f∘g) = f(g(1)). *)
  Lemma trace_F_cyclic : forall (f g : EndF (F_as_VS fld)),
      trace_F (lm_comp f g) = trace_F (lm_comp g f).
  Proof.
    intros f g. unfold trace_F, lm_comp; cbn.
    set (a := lm_fn g (cr_one fld)).
    set (b := lm_fn f (cr_one fld)).
    (* f(a) = a*b and g(b) = b*a; equal by commutativity. *)
    assert (Hfa : lm_fn f a = cr_mul fld a b).
    { assert (Ha : a = vsF_scale (F_as_VS fld) a (cr_one fld)).
      { unfold F_as_VS, vsF_scale; cbn.
        symmetry. apply (cr_mul_one fld). }
      rewrite Ha at 1.
      rewrite f.(lm_scale).
      unfold F_as_VS, vsF_scale; cbn. reflexivity. }
    assert (Hgb : lm_fn g b = cr_mul fld b a).
    { assert (Hb : b = vsF_scale (F_as_VS fld) b (cr_one fld)).
      { unfold F_as_VS, vsF_scale; cbn.
        symmetry. apply (cr_mul_one fld). }
      rewrite Hb at 1.
      rewrite g.(lm_scale).
      unfold F_as_VS, vsF_scale; cbn. reflexivity. }
    rewrite Hfa, Hgb. apply cr_mul_comm.
  Qed.

End TraceF.

(* ================================================================== *)
(** * 2. Trace on End(F^2)                                            *)
(* ================================================================== *)

Section TraceF2.
  Context {F : Type} (fld : Field F).

  Local Lemma F2_trace_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring F2_trace_ring : F2_trace_ring_theory.

  Notation e1 := (cr_one fld, cr_zero fld) (only parsing).
  Notation e2 := (cr_zero fld, cr_one fld) (only parsing).

  (** Trace = (f(e_1)).fst + (f(e_2)).snd. *)
  Definition trace_F2 (f : EndF (F2_as_VS fld)) : F :=
    cr_add fld (fst (lm_fn f e1)) (snd (lm_fn f e2)).

  Lemma trace_F2_zero : trace_F2 (end_zero (F2_as_VS fld)) = cr_zero fld.
  Proof.
    unfold trace_F2, end_zero. cbn.
    apply cr_add_zero.
  Qed.

  Lemma trace_F2_add : forall (f g : EndF (F2_as_VS fld)),
      trace_F2 (end_add f g) = cr_add fld (trace_F2 f) (trace_F2 g).
  Proof.
    intros f g. unfold trace_F2, end_add; cbn.
    destruct (lm_fn f (cr_one fld, cr_zero fld)) as [a1f a2f].
    destruct (lm_fn g (cr_one fld, cr_zero fld)) as [a1g a2g].
    destruct (lm_fn f (cr_zero fld, cr_one fld)) as [b1f b2f].
    destruct (lm_fn g (cr_zero fld, cr_one fld)) as [b1g b2g].
    cbn. ring.
  Qed.

  Lemma trace_F2_scale : forall (a : F) (f : EndF (F2_as_VS fld)),
      trace_F2 (end_scale a f) = cr_mul fld a (trace_F2 f).
  Proof.
    intros a f. unfold trace_F2, end_scale; cbn.
    destruct (lm_fn f (cr_one fld, cr_zero fld)) as [a1 a2].
    destruct (lm_fn f (cr_zero fld, cr_one fld)) as [b1 b2].
    cbn. ring.
  Qed.

  Lemma trace_F2_neg : forall (f : EndF (F2_as_VS fld)),
      trace_F2 (end_neg f) = cr_neg fld (trace_F2 f).
  Proof.
    intro f. unfold trace_F2, end_neg; cbn.
    destruct (lm_fn f (cr_one fld, cr_zero fld)) as [a1 a2].
    destruct (lm_fn f (cr_zero fld, cr_one fld)) as [b1 b2].
    cbn. ring.
  Qed.

  (** Linearity expansion: f((a,b)) = a·f(e1) + b·f(e2). *)
  Lemma F2_linear_expand : forall (f : EndF (F2_as_VS fld)) (a b : F),
      lm_fn f (a, b) =
      vsF_add (F2_as_VS fld)
        (vsF_scale (F2_as_VS fld) a (lm_fn f (cr_one fld, cr_zero fld)))
        (vsF_scale (F2_as_VS fld) b (lm_fn f (cr_zero fld, cr_one fld))).
  Proof.
    intros f a b.
    (* (a, b) = (a, 0) + (0, b) = a·(1,0) + b·(0,1) *)
    assert (Hab : (a, b) =
      vsF_add (F2_as_VS fld)
        (vsF_scale (F2_as_VS fld) a (cr_one fld, cr_zero fld))
        (vsF_scale (F2_as_VS fld) b (cr_zero fld, cr_one fld))).
    { unfold F2_as_VS, vsF_scale, vsF_add. cbn. f_equal; ring. }
    rewrite Hab.
    rewrite f.(lm_add).
    rewrite !f.(lm_scale). reflexivity.
  Qed.

  Lemma trace_F2_cyclic : forall (f g : EndF (F2_as_VS fld)),
      trace_F2 (lm_comp f g) = trace_F2 (lm_comp g f).
  Proof.
    intros f g.
    unfold trace_F2; cbn.
    (* Destructure the basis-image pairs *)
    pose proof (F2_linear_expand f) as Hf.
    pose proof (F2_linear_expand g) as Hg.
    set (a := lm_fn f (cr_one fld, cr_zero fld)).
    set (b := lm_fn f (cr_zero fld, cr_one fld)).
    set (c := lm_fn g (cr_one fld, cr_zero fld)).
    set (d := lm_fn g (cr_zero fld, cr_one fld)).
    destruct a as [a11 a21] eqn:Ea.
    destruct b as [a12 a22] eqn:Eb.
    destruct c as [b11 b21] eqn:Ec.
    destruct d as [b12 b22] eqn:Ed.
    rewrite (Hg a11 a21).
    rewrite (Hg a12 a22).
    rewrite (Hf b11 b21).
    rewrite (Hf b12 b22).
    unfold a, b, c, d in *.
    rewrite Ea, Eb, Ec, Ed.
    cbn. ring.
  Qed.

End TraceF2.

(* ================================================================== *)
(** * 3. Trace on End(F^3)                                            *)
(* ================================================================== *)

Section TraceF3.
  Context {F : Type} (fld : Field F).

  Local Lemma F3_trace_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring F3_trace_ring : F3_trace_ring_theory.

  Notation e1 := (cr_one fld, cr_zero fld, cr_zero fld) (only parsing).
  Notation e2 := (cr_zero fld, cr_one fld, cr_zero fld) (only parsing).
  Notation e3 := (cr_zero fld, cr_zero fld, cr_one fld) (only parsing).

  (** Trace = (f(e_1))_1 + (f(e_2))_2 + (f(e_3))_3. *)
  Definition trace_F3 (f : EndF (F3_as_VS fld)) : F :=
    cr_add fld
      (fst (fst (lm_fn f e1)))
      (cr_add fld
        (snd (fst (lm_fn f e2)))
        (snd (lm_fn f e3))).

  Lemma trace_F3_zero : trace_F3 (end_zero (F3_as_VS fld)) = cr_zero fld.
  Proof.
    unfold trace_F3, end_zero. cbn. ring.
  Qed.

  Lemma trace_F3_add : forall (f g : EndF (F3_as_VS fld)),
      trace_F3 (end_add f g) = cr_add fld (trace_F3 f) (trace_F3 g).
  Proof.
    intros f g. unfold trace_F3, end_add; cbn.
    destruct (lm_fn f (cr_one fld, cr_zero fld, cr_zero fld)) as [[a1f a2f] a3f].
    destruct (lm_fn g (cr_one fld, cr_zero fld, cr_zero fld)) as [[a1g a2g] a3g].
    destruct (lm_fn f (cr_zero fld, cr_one fld, cr_zero fld)) as [[b1f b2f] b3f].
    destruct (lm_fn g (cr_zero fld, cr_one fld, cr_zero fld)) as [[b1g b2g] b3g].
    destruct (lm_fn f (cr_zero fld, cr_zero fld, cr_one fld)) as [[c1f c2f] c3f].
    destruct (lm_fn g (cr_zero fld, cr_zero fld, cr_one fld)) as [[c1g c2g] c3g].
    cbn. ring.
  Qed.

  Lemma trace_F3_scale : forall (a : F) (f : EndF (F3_as_VS fld)),
      trace_F3 (end_scale a f) = cr_mul fld a (trace_F3 f).
  Proof.
    intros a f. unfold trace_F3, end_scale; cbn.
    destruct (lm_fn f (cr_one fld, cr_zero fld, cr_zero fld)) as [[a1 a2] a3].
    destruct (lm_fn f (cr_zero fld, cr_one fld, cr_zero fld)) as [[b1 b2] b3].
    destruct (lm_fn f (cr_zero fld, cr_zero fld, cr_one fld)) as [[c1 c2] c3].
    cbn. ring.
  Qed.

  Lemma trace_F3_neg : forall (f : EndF (F3_as_VS fld)),
      trace_F3 (end_neg f) = cr_neg fld (trace_F3 f).
  Proof.
    intro f. unfold trace_F3, end_neg; cbn.
    destruct (lm_fn f (cr_one fld, cr_zero fld, cr_zero fld)) as [[a1 a2] a3].
    destruct (lm_fn f (cr_zero fld, cr_one fld, cr_zero fld)) as [[b1 b2] b3].
    destruct (lm_fn f (cr_zero fld, cr_zero fld, cr_one fld)) as [[c1 c2] c3].
    cbn. ring.
  Qed.

  (** Linearity expansion for F^3: f((a,b,c)) = a·f(e1) + b·f(e2) + c·f(e3). *)
  Lemma F3_linear_expand : forall (f : EndF (F3_as_VS fld)) (a b c : F),
      lm_fn f (a, b, c) =
      vsF_add (F3_as_VS fld)
        (vsF_scale (F3_as_VS fld) a (lm_fn f (cr_one fld, cr_zero fld, cr_zero fld)))
        (vsF_add (F3_as_VS fld)
          (vsF_scale (F3_as_VS fld) b (lm_fn f (cr_zero fld, cr_one fld, cr_zero fld)))
          (vsF_scale (F3_as_VS fld) c (lm_fn f (cr_zero fld, cr_zero fld, cr_one fld)))).
  Proof.
    intros f a b c.
    assert (Habc : (a, b, c) =
      vsF_add (F3_as_VS fld)
        (vsF_scale (F3_as_VS fld) a (cr_one fld, cr_zero fld, cr_zero fld))
        (vsF_add (F3_as_VS fld)
          (vsF_scale (F3_as_VS fld) b (cr_zero fld, cr_one fld, cr_zero fld))
          (vsF_scale (F3_as_VS fld) c (cr_zero fld, cr_zero fld, cr_one fld)))).
    { unfold F3_as_VS, vsF_scale, vsF_add. cbn. f_equal; [f_equal|]; ring. }
    rewrite Habc.
    rewrite f.(lm_add).
    rewrite f.(lm_scale).
    rewrite f.(lm_add).
    rewrite !f.(lm_scale).
    reflexivity.
  Qed.

  Lemma trace_F3_cyclic : forall (f g : EndF (F3_as_VS fld)),
      trace_F3 (lm_comp f g) = trace_F3 (lm_comp g f).
  Proof.
    intros f g.
    unfold trace_F3; cbn.
    pose proof (F3_linear_expand f) as Hf.
    pose proof (F3_linear_expand g) as Hg.
    set (a := lm_fn f (cr_one fld, cr_zero fld, cr_zero fld)).
    set (b := lm_fn f (cr_zero fld, cr_one fld, cr_zero fld)).
    set (c := lm_fn f (cr_zero fld, cr_zero fld, cr_one fld)).
    set (d := lm_fn g (cr_one fld, cr_zero fld, cr_zero fld)).
    set (e := lm_fn g (cr_zero fld, cr_one fld, cr_zero fld)).
    set (k := lm_fn g (cr_zero fld, cr_zero fld, cr_one fld)).
    destruct a as [[a11 a21] a31] eqn:Ea.
    destruct b as [[a12 a22] a32] eqn:Eb.
    destruct c as [[a13 a23] a33] eqn:Ec.
    destruct d as [[b11 b21] b31] eqn:Ed.
    destruct e as [[b12 b22] b32] eqn:Ee.
    destruct k as [[b13 b23] b33] eqn:Ek.
    rewrite (Hg a11 a21 a31).
    rewrite (Hg a12 a22 a32).
    rewrite (Hg a13 a23 a33).
    rewrite (Hf b11 b21 b31).
    rewrite (Hf b12 b22 b32).
    rewrite (Hf b13 b23 b33).
    unfold a, b, c, d, e, k in *.
    rewrite Ea, Eb, Ec, Ed, Ee, Ek.
    cbn. ring.
  Qed.

End TraceF3.
