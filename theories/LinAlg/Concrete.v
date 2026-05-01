(** * LinAlg/Concrete.v
    Concrete vector spaces and their standard bases:
    - F as a 1-dim VS over itself.
    - F * F as a 2-dim VS.
    - F * F * F as a 3-dim VS (matches [ex2_vs] in LowDimensional.v).

    These are the basic working examples used throughout the Lie
    theory development. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.LinAlg.Basis.
From Stdlib Require Import List Lia Ring Setoid.
Import ListNotations.

(* ================================================================== *)
(** * 1. F as a 1-dim vector space over itself                        *)
(* ================================================================== *)

(** F as a vector space over itself: scalar mult is just field mult. *)
Definition F_as_VS {F : Type} (fld : Field F) : VectorSpaceF fld F.
Proof.
  refine {|
    vsF_add   := cr_add fld;
    vsF_zero  := cr_zero fld;
    vsF_neg   := cr_neg fld;
    vsF_scale := cr_mul fld;
  |}.
  - intros u v w. apply fld.(cr_add_assoc).
  - intros u v. apply fld.(cr_add_comm).
  - intros v. apply fld.(cr_add_zero).
  - intros v. apply fld.(cr_add_neg).
  - intros v. rewrite fld.(cr_mul_comm). apply fld.(cr_mul_one).
  - intros a b v. apply fld.(cr_mul_assoc).
  - intros a u v. apply fld.(cr_distrib).
  - intros a b v.
    rewrite (fld.(cr_mul_comm) (cr_add fld a b) v).
    rewrite fld.(cr_distrib).
    f_equal; apply fld.(cr_mul_comm).
Defined.

(** The standard basis of F = {1}. *)
Definition F_basis {F : Type} (fld : Field F) : list F := [cr_one fld].

(** {1} spans F: every v = v · 1. *)
Lemma F_basis_spans : forall {F : Type} (fld : Field F),
    Spans (F_as_VS fld) (F_basis fld).
Proof.
  intros F fld v.
  exists [v]. simpl. split; [reflexivity|].
  rewrite (fld.(cr_mul_one) v). symmetry. apply fld.(cr_add_zero).
Qed.

(** {1} is linearly independent in F (assuming 1 ≠ 0). *)
Lemma F_basis_lin_indep : forall {F : Type} (fld : Field F),
    cr_one fld <> cr_zero fld ->
    LinIndependent (F_as_VS fld) (F_basis fld).
Proof.
  intros F fld Hone coeffs Hlen Hlc i Hi.
  unfold F_basis in *. simpl in Hlen.
  destruct coeffs as [|c [|d cs]]; simpl in Hlen; try discriminate.
  destruct i as [|i'].
  - (* i = 0 *)
    cbn in Hlc.
    (* The goal is c = cr_zero fld; Hlc has the field-level eqn after unfolding. *)
    transitivity (cr_mul fld c (cr_one fld)).
    + symmetry. apply (fld.(cr_mul_one) c).
    + rewrite <- (fld.(cr_add_zero) (cr_mul fld c (cr_one fld))).
      exact Hlc.
  - simpl in Hi. lia.
Qed.

(** F is 1-dimensional. *)
Theorem F_has_dim_1 : forall {F : Type} (fld : Field F),
    cr_one fld <> cr_zero fld ->
    HasDim (F_as_VS fld) 1.
Proof.
  intros F fld Hone.
  exists (F_basis fld). split; [reflexivity|].
  split.
  - apply F_basis_lin_indep. exact Hone.
  - apply F_basis_spans.
Qed.

(* ================================================================== *)
(** * 2. F * F as a 2-dim vector space                                *)
(* ================================================================== *)

(** F * F as a vector space (componentwise). *)
Definition F2_as_VS {F : Type} (fld : Field F) : VectorSpaceF fld (F * F).
Proof.
  refine {|
    vsF_add   := fun '(a, b) '(c, d) => (cr_add fld a c, cr_add fld b d);
    vsF_zero  := (cr_zero fld, cr_zero fld);
    vsF_neg   := fun '(a, b) => (cr_neg fld a, cr_neg fld b);
    vsF_scale := fun c '(a, b) => (cr_mul fld c a, cr_mul fld c b);
  |}.
  - intros [a b] [c d] [e f]. simpl. f_equal; apply fld.(cr_add_assoc).
  - intros [a b] [c d]. simpl. f_equal; apply fld.(cr_add_comm).
  - intros [a b]. simpl. f_equal; apply fld.(cr_add_zero).
  - intros [a b]. simpl. f_equal; apply fld.(cr_add_neg).
  - intros [a b]. simpl. f_equal; (rewrite fld.(cr_mul_comm); apply fld.(cr_mul_one)).
  - intros c d [a b]. simpl. f_equal; apply fld.(cr_mul_assoc).
  - intros c [a b] [d e]. simpl. f_equal; apply fld.(cr_distrib).
  - intros c d [a b]. simpl. f_equal;
      (rewrite (fld.(cr_mul_comm) (cr_add fld c d) _), fld.(cr_distrib);
       f_equal; apply fld.(cr_mul_comm)).
Defined.

(** Standard basis of F*F: {(1,0), (0,1)}. *)
Definition F2_basis {F : Type} (fld : Field F) : list (F * F) :=
  [(cr_one fld, cr_zero fld); (cr_zero fld, cr_one fld)].

Section F2BasisSpans.
  Context {F : Type} (fld : Field F).

  Local Lemma F2_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring F2_ring_inst : F2_ring_theory.

  (** {(1,0), (0,1)} spans F*F: (a, b) = a·(1,0) + b·(0,1). *)
  Lemma F2_basis_spans : Spans (F2_as_VS fld) (F2_basis fld).
  Proof.
    intros [a b].
    exists [a; b]. split; [reflexivity|].
    cbn. f_equal; ring.
  Qed.

  (** F2_basis is linearly independent (when 1 ≠ 0). *)
  Lemma F2_basis_lin_indep :
      cr_one fld <> cr_zero fld ->
      LinIndependent (F2_as_VS fld) (F2_basis fld).
  Proof.
    intros Hone coeffs Hlen Hlc i Hi.
    unfold F2_basis in *. simpl in Hlen.
    destruct coeffs as [|c1 [|c2 [|c3 cs]]]; simpl in Hlen; try discriminate.
    cbn in Hlc.
    (* Hlc reduces to: (c1*1 + (c2*0 + 0), c1*0 + (c2*1 + 0)) = (0, 0) *)
    assert (Hfst : c1 = cr_zero fld).
    { pose proof (f_equal fst Hlc) as Hfst.
      cbn in Hfst.
      assert (Heq : c1 = cr_add fld (cr_mul fld c1 (cr_one fld))
                                    (cr_add fld (cr_mul fld c2 (cr_zero fld))
                                                (cr_zero fld))).
      { ring. }
      rewrite Heq. exact Hfst. }
    assert (Hsnd : c2 = cr_zero fld).
    { pose proof (f_equal snd Hlc) as Hsnd.
      cbn in Hsnd.
      assert (Heq : c2 = cr_add fld (cr_mul fld c1 (cr_zero fld))
                                    (cr_add fld (cr_mul fld c2 (cr_one fld))
                                                (cr_zero fld))).
      { ring. }
      rewrite Heq. exact Hsnd. }
    destruct i as [|[|i'']]; simpl.
    + exact Hfst.
    + exact Hsnd.
    + simpl in Hi. lia.
  Qed.

  (** F * F has dimension 2. *)
  Theorem F2_has_dim_2 :
      cr_one fld <> cr_zero fld ->
      HasDim (F2_as_VS fld) 2.
  Proof.
    intros Hone.
    exists (F2_basis fld). split; [reflexivity|].
    split.
    - apply F2_basis_lin_indep. exact Hone.
    - apply F2_basis_spans.
  Qed.

End F2BasisSpans.

(* ================================================================== *)
(** * 3. F * F * F as a 3-dim vector space (matches ex2_vs)            *)
(* ================================================================== *)

Section F3Basis.
  Context {F : Type} (fld : Field F).

  Local Lemma F3_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring F3_ring_inst : F3_ring_theory.

  (** F*F*F as a vector space (componentwise) — same as ex2_vs in LowDim. *)
  Definition F3_as_VS : VectorSpaceF fld (F * F * F).
  Proof.
    refine {|
      vsF_add   := fun '(a,b,c) '(d,e,f) => (cr_add fld a d, cr_add fld b e, cr_add fld c f);
      vsF_zero  := (cr_zero fld, cr_zero fld, cr_zero fld);
      vsF_neg   := fun '(a,b,c) => (cr_neg fld a, cr_neg fld b, cr_neg fld c);
      vsF_scale := fun s '(a,b,c) => (cr_mul fld s a, cr_mul fld s b, cr_mul fld s c);
    |}.
    - intros [[a b] c] [[d e] f] [[g h] i]. cbn.
      f_equal; [f_equal|]; ring.
    - intros [[a b] c] [[d e] f]. cbn. f_equal; [f_equal|]; ring.
    - intros [[a b] c]. cbn. f_equal; [f_equal|]; ring.
    - intros [[a b] c]. cbn. f_equal; [f_equal|]; ring.
    - intros [[a b] c]. cbn. f_equal; [f_equal|]; ring.
    - intros s t [[a b] c]. cbn. f_equal; [f_equal|]; ring.
    - intros s [[a b] c] [[d e] f]. cbn. f_equal; [f_equal|]; ring.
    - intros s t [[a b] c]. cbn. f_equal; [f_equal|]; ring.
  Defined.

  (** Standard basis of F^3: {(1,0,0), (0,1,0), (0,0,1)}. *)
  Definition F3_basis : list (F * F * F) :=
    [(cr_one fld, cr_zero fld, cr_zero fld);
     (cr_zero fld, cr_one fld, cr_zero fld);
     (cr_zero fld, cr_zero fld, cr_one fld)].

  Lemma F3_basis_spans : Spans F3_as_VS F3_basis.
  Proof.
    intros [[a b] c].
    exists [a; b; c]. split; [reflexivity|].
    cbn. f_equal; [f_equal|]; ring.
  Qed.

  Lemma F3_basis_lin_indep :
      cr_one fld <> cr_zero fld ->
      LinIndependent F3_as_VS F3_basis.
  Proof.
    intros Hone coeffs Hlen Hlc i Hi.
    unfold F3_basis in *. simpl in Hlen.
    destruct coeffs as [|c1 [|c2 [|c3 [|c4 cs]]]]; simpl in Hlen; try discriminate.
    cbn in Hlc.
    assert (H1 : c1 = cr_zero fld).
    { pose proof (f_equal (fun p => fst (fst p)) Hlc) as Hfst. cbn in Hfst.
      assert (Heq : c1 = cr_add fld (cr_mul fld c1 (cr_one fld))
                          (cr_add fld (cr_mul fld c2 (cr_zero fld))
                            (cr_add fld (cr_mul fld c3 (cr_zero fld)) (cr_zero fld)))).
      { ring. }
      rewrite Heq. exact Hfst. }
    assert (H2 : c2 = cr_zero fld).
    { pose proof (f_equal (fun p => snd (fst p)) Hlc) as Hsnd. cbn in Hsnd.
      assert (Heq : c2 = cr_add fld (cr_mul fld c1 (cr_zero fld))
                          (cr_add fld (cr_mul fld c2 (cr_one fld))
                            (cr_add fld (cr_mul fld c3 (cr_zero fld)) (cr_zero fld)))).
      { ring. }
      rewrite Heq. exact Hsnd. }
    assert (H3 : c3 = cr_zero fld).
    { pose proof (f_equal snd Hlc) as Hthrd. cbn in Hthrd.
      assert (Heq : c3 = cr_add fld (cr_mul fld c1 (cr_zero fld))
                          (cr_add fld (cr_mul fld c2 (cr_zero fld))
                            (cr_add fld (cr_mul fld c3 (cr_one fld)) (cr_zero fld)))).
      { ring. }
      rewrite Heq. exact Hthrd. }
    destruct i as [|[|[|i''']]]; simpl.
    + exact H1.
    + exact H2.
    + exact H3.
    + simpl in Hi. lia.
  Qed.

  Theorem F3_has_dim_3 :
      cr_one fld <> cr_zero fld ->
      HasDim F3_as_VS 3.
  Proof.
    intros Hone.
    exists F3_basis. split; [reflexivity|].
    split.
    - apply F3_basis_lin_indep. exact Hone.
    - apply F3_basis_spans.
  Qed.

End F3Basis.
