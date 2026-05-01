(** * ATT/SoundComplete.v
    Soundness and completeness of the algebraic theory Th.

    Soundness:  if Th ⊢ Γ ⊢ t = t' : τ, then every model M in every
                category V with finite products satisfies [t]_M = [t']_M.

    Completeness: if every model in every FP-category satisfies an equation,
                  then the equation is derivable in Th.

    The completeness proof uses the GENERIC MODEL G in Cl(Th):
    suppose Γ ⊢ t = t' : τ holds in every model.  In particular it holds
    in G.  By the interpretation lemma, [t]_G = (Γ | t) and [t']_G = (Γ | t').
    Since (Γ | t) = (Γ | t') as morphisms in Cl(Th) (quotient by ThEq),
    we have Th ⊢ Γ ⊢ t = t'. *)

Require Import CAG.ATT.Signature.
Require Import CAG.ATT.Syntax.
Require Import CAG.ATT.Theory.
Require Import CAG.ATT.Model.
Require Import CAG.ATT.ClassifyingCategory.
Require Import CAG.ATT.GenericModel.
Require Import CAG.Category.Core.
Require Import CAG.Category.Products.
From Stdlib Require Import Lists.List.
Import ListNotations.

Set Universe Polymorphism.

(** ** Soundness *)

(** *** Strong induction principle for [ThEq]

    The auto-generated [ThEq_ind] does not provide an IH for the
    per-argument equations in the [theq_cong] case.  This stronger
    principle does. *)
Lemma ThEq_strong_ind :
    forall (Sg : Signature) (ax : list (TheoryAxiom Sg))
           (Γ : list Sg.(sg_ty))
           (P : Term Sg -> Term Sg -> Sg.(sg_ty) -> Prop),
    (forall (t : Term Sg) (τ : Sg.(sg_ty)),
        HasType Sg Γ t τ -> P t t τ) ->
    (forall (t1 t2 : Term Sg) (τ : Sg.(sg_ty)),
        ThEq Sg ax Γ t1 t2 τ -> P t1 t2 τ -> P t2 t1 τ) ->
    (forall (t1 t2 t3 : Term Sg) (τ : Sg.(sg_ty)),
        ThEq Sg ax Γ t1 t2 τ -> P t1 t2 τ ->
        ThEq Sg ax Γ t2 t3 τ -> P t2 t3 τ -> P t1 t3 τ) ->
    (forall (f : Sg.(sg_fun)) (args1 args2 : list (Term Sg)),
        List.Forall2 (fun a1 a2 => exists τ,
                        ThEq Sg ax Γ a1 a2 τ /\ P a1 a2 τ) args1 args2 ->
        P (t_app f args1) (t_app f args2) (Sg.(sg_cod) f)) ->
    (forall (a : TheoryAxiom Sg) (sub : list (Term Sg)),
        List.In a ax ->
        List.Forall2 (HasType Sg Γ) sub a.(ax_ctx) ->
        P (subst_term Sg sub a.(ax_lhs)) (subst_term Sg sub a.(ax_rhs))
          a.(ax_sort)) ->
    forall t t' τ, ThEq Sg ax Γ t t' τ -> P t t' τ.
Proof.
  intros Sg ax Γ P Prefl Psym Ptrans Pcong Pax.
  fix IH 4.
  intros t t' τ Heq.
  destruct Heq as [t τ Ht
                  | t1 t2 τ Heq1
                  | t1 t2 t3 τ Heq1 Heq2
                  | f args1 args2 Hargs
                  | a sub Hin Htyp ].
  - apply Prefl. exact Ht.
  - apply (Psym _ _ _ Heq1). apply IH. exact Heq1.
  - apply (Ptrans _ _ _ _ Heq1 (IH _ _ _ Heq1) Heq2 (IH _ _ _ Heq2)).
  - apply Pcong.
    induction Hargs as [| a1 a2 l1 l2 [τ' Heq'] Hrest IHrest].
    + constructor.
    + constructor.
      * exists τ'. split. exact Heq'. apply IH. exact Heq'.
      * exact IHrest.
  - apply Pax. exact Hin. exact Htyp.
Qed.

(** *** Type uniqueness for well-typed terms *)

(** If a term has two type derivations, the types are equal. *)
Lemma hastype_uniq : forall (Sg : Signature) (Γ : list Sg.(sg_ty))
    (t : Term Sg) (τ1 τ2 : Sg.(sg_ty)),
    HasType Sg Γ t τ1 -> HasType Sg Γ t τ2 -> τ1 = τ2.
Proof.
  intros Sg Γ t.
  induction t as [n | f args]; intros τ1 τ2 Ht1 Ht2.
  - apply ht_var_nth_err in Ht1. apply ht_var_nth_err in Ht2.
    rewrite Ht1 in Ht2. injection Ht2. auto.
  - apply ht_app_cod_eq in Ht1. apply ht_app_cod_eq in Ht2. congruence.
Qed.

(** *** ThEq's typing tag matches any HasType derivation on either side *)

(** If [ThEq Sg ax Γ t1 t2 τ] holds and [t1] is otherwise known to have
    type [τ'], then [τ = τ'].  Symmetric on [t2].  This says: the [τ] in
    a ThEq judgment is forced by the typings of either side. *)
Lemma theq_typed_eq : forall (Sg : Signature) (ax : list (TheoryAxiom Sg))
    (Γ : list Sg.(sg_ty))
    (t1 t2 : Term Sg) (τ : Sg.(sg_ty))
    (Heq : ThEq Sg ax Γ t1 t2 τ),
    (forall τ', HasType Sg Γ t1 τ' -> τ = τ') /\
    (forall τ', HasType Sg Γ t2 τ' -> τ = τ').
Proof.
  intros Sg ax Γ t1 t2 τ Heq.
  induction Heq
    as [ t τ Ht
       | t1 t2 τ Heq1 [IHL IHR]
       | t1 t2 t3 τ Heq1 [IH1L IH1R] Heq2 [IH2L IH2R]
       | f args1 args2 Hargs
       | a sub Hin Htyp ]
    using ThEq_strong_ind.
  - (* refl *) split; intros τ' Ht'; eapply hastype_uniq; eauto.
  - (* sym: roles of t1 and t2 swap *)
    split.
    + exact IHR.
    + exact IHL.
  - (* trans *)
    split.
    + exact IH1L.
    + exact IH2R.
  - (* cong: both terms are t_app f _, type from inversion *)
    split; intros τ' Ht'; symmetry; apply (ht_app_cod_eq Ht').
  - (* ax: subst preserves type, then uniqueness *)
    pose proof (ax_lhs_typed a) as Halhs.
    pose proof (ax_rhs_typed a) as Harhs.
    pose proof (subst_preserves_type Sg Γ a.(ax_ctx) sub Htyp
                  a.(ax_lhs) a.(ax_sort) Halhs) as HsLHS.
    pose proof (subst_preserves_type Sg Γ a.(ax_ctx) sub Htyp
                  a.(ax_rhs) a.(ax_sort) Harhs) as HsRHS.
    split; intros τ' Ht'.
    + eapply hastype_uniq; [ exact HsLHS | exact Ht' ].
    + eapply hastype_uniq; [ exact HsRHS | exact Ht' ].
Qed.

(** *** ThEq preserves typedness across both sides *)

(** Helper: given [Forall2 (∃ τ, ThEq a1 a2 τ ∧ Φ a1 a2 τ)] and
    [Forall2 (HasType Γ) args1 dom], produce [Forall2 (HasType Γ) args2 dom]
    by transporting per-index typing through Φ.  Φ is instantiated
    below by the bidirectional preservation property. *)
Lemma cong_transport_args :
    forall (Sg : Signature) (ax : list (TheoryAxiom Sg))
           (Γ : list Sg.(sg_ty))
           (args1 args2 : list (Term Sg))
           (Hargs : List.Forall2
                      (fun a1 a2 => exists τ,
                         ThEq Sg ax Γ a1 a2 τ /\
                         ((HasType Sg Γ a1 τ -> HasType Sg Γ a2 τ) /\
                          (HasType Sg Γ a2 τ -> HasType Sg Γ a1 τ)))
                      args1 args2)
           (dom : list Sg.(sg_ty))
           (Hd1 : List.Forall2 (HasType Sg Γ) args1 dom),
    List.Forall2 (HasType Sg Γ) args2 dom.
Proof.
  intros Sg ax Γ args1 args2 Hargs.
  induction Hargs as [| b1 b2 l1 l2 [τ' [Heq' [IHFL _]]] Hrest IHrest];
    intros dom Hd1.
  - inversion Hd1; subst. constructor.
  - inversion Hd1 as [|x y l3 l4 Hxy Hrest_typed Eq3 Eq4]; subst.
    constructor.
    + pose proof (theq_typed_eq Sg ax Γ b1 b2 τ' Heq') as [Hteq_l _].
      specialize (Hteq_l y Hxy). subst τ'.
      apply IHFL. exact Hxy.
    + apply IHrest. exact Hrest_typed.
Qed.

(** Symmetric version: transport args2 typing to args1 typing. *)
Lemma cong_transport_args_rev :
    forall (Sg : Signature) (ax : list (TheoryAxiom Sg))
           (Γ : list Sg.(sg_ty))
           (args1 args2 : list (Term Sg))
           (Hargs : List.Forall2
                      (fun a1 a2 => exists τ,
                         ThEq Sg ax Γ a1 a2 τ /\
                         ((HasType Sg Γ a1 τ -> HasType Sg Γ a2 τ) /\
                          (HasType Sg Γ a2 τ -> HasType Sg Γ a1 τ)))
                      args1 args2)
           (dom : list Sg.(sg_ty))
           (Hd2 : List.Forall2 (HasType Sg Γ) args2 dom),
    List.Forall2 (HasType Sg Γ) args1 dom.
Proof.
  intros Sg ax Γ args1 args2 Hargs.
  induction Hargs as [| b1 b2 l1 l2 [τ' [Heq' [_ IHFR]]] Hrest IHrest];
    intros dom Hd2.
  - inversion Hd2; subst. constructor.
  - inversion Hd2 as [|x y l3 l4 Hxy Hrest_typed Eq3 Eq4]; subst.
    constructor.
    + pose proof (theq_typed_eq Sg ax Γ b1 b2 τ' Heq') as [_ Hteq_r].
      specialize (Hteq_r y Hxy). subst τ'.
      apply IHFR. exact Hxy.
    + apply IHrest. exact Hrest_typed.
Qed.

Lemma theq_preserves_typed : forall (Sg : Signature) (ax : list (TheoryAxiom Sg))
    (Γ : list Sg.(sg_ty))
    (t1 t2 : Term Sg) (τ : Sg.(sg_ty))
    (Heq : ThEq Sg ax Γ t1 t2 τ),
    (HasType Sg Γ t1 τ -> HasType Sg Γ t2 τ) /\
    (HasType Sg Γ t2 τ -> HasType Sg Γ t1 τ).
Proof.
  intros Sg ax Γ t1 t2 τ Heq.
  induction Heq
    as [ t τ Ht
       | t1 t2 τ Heq1 [IHL IHR]
       | t1 t2 t3 τ Heq1 [IH1L IH1R] Heq2 [IH2L IH2R]
       | f args1 args2 Hargs
       | a sub Hin Htyp ]
    using ThEq_strong_ind.
  - split; intro; assumption.
  - split. exact IHR. exact IHL.
  - split.
    + intro Hl. apply IH2L. apply IH1L. exact Hl.
    + intro Hr. apply IH1R. apply IH2R. exact Hr.
  - split.
    + intros Ht1.
      pose proof (ht_app_args_f2 Ht1) as Hargs1_typed.
      apply ht_app.
      apply (cong_transport_args Sg ax Γ args1 args2 Hargs _ Hargs1_typed).
    + intros Ht2.
      pose proof (ht_app_args_f2 Ht2) as Hargs2_typed.
      apply ht_app.
      apply (cong_transport_args_rev Sg ax Γ args1 args2 Hargs _ Hargs2_typed).
  - pose proof (ax_lhs_typed a) as Halhs.
    pose proof (ax_rhs_typed a) as Harhs.
    pose proof (subst_preserves_type Sg Γ a.(ax_ctx) sub Htyp
                  a.(ax_lhs) a.(ax_sort) Halhs) as HsLHS.
    pose proof (subst_preserves_type Sg Γ a.(ax_ctx) sub Htyp
                  a.(ax_rhs) a.(ax_sort) Harhs) as HsRHS.
    split; intro; assumption.
Qed.

(** Helper for the [theq_cong] case of soundness: equality of the
    [app_cont] functions on a per-index basis.  Takes a [Forall2] whose
    payload is the bidirectional IH together with the per-arg
    interpretation equality. *)
Lemma cong_app_cont_eq :
    forall (Th : Theory) (C : Category) (hp : HasFiniteProducts C)
           (M : Model Th C hp) (Γ : list Th.(th_sig).(sg_ty))
           (f : Th.(th_sig).(sg_fun))
           (args1 args2 : list (Term Th.(th_sig)))
           (Hargs : List.Forall2
                      (fun a1 a2 => exists τ,
                         ThEq Th.(th_sig) Th.(th_ax) Γ a1 a2 τ /\
                         (forall (Ht1 : HasType Th.(th_sig) Γ a1 τ)
                                 (Ht2 : HasType Th.(th_sig) Γ a2 τ),
                            interp_term M Γ a1 τ Ht1 =
                            interp_term M Γ a2 τ Ht2))
                      args1 args2)
           (Hargs1_typed : List.Forall2 (HasType Th.(th_sig) Γ) args1
                                        (Th.(th_sig).(sg_dom) f))
           (Hargs2_typed : List.Forall2 (HasType Th.(th_sig) Γ) args2
                                        (Th.(th_sig).(sg_dom) f))
           (i : nat) (A : C.(Ob))
           (H : List.nth_error
                  (List.map (md_ty (mod_data M)) (Th.(th_sig).(sg_dom) f)) i
                = Some A),
    app_cont (mod_data M) Γ f args1 Hargs1_typed i A H =
    app_cont (mod_data M) Γ f args2 Hargs2_typed i A H.
Proof.
  intros Th C hp M Γ f args1 args2 Hargs Hargs1_typed Hargs2_typed i A H.
  pose proof H as H'.
  rewrite List.nth_error_map in H'.
  destruct (List.nth_error (Th.(th_sig).(sg_dom) f) i) as [τi|] eqn:Hτi;
    [| simpl in H'; discriminate].
  simpl in H'. injection H' as HA.
  destruct (Forall2_nth_error_l _ _ _ Hargs1_typed i τi Hτi)
    as [a1 [Ha1_eq Ha1_typed]].
  destruct (Forall2_nth_error_l _ _ _ Hargs2_typed i τi Hτi)
    as [a2 [Ha2_eq Ha2_typed]].
  rewrite (app_cont_some (mod_data M) Γ f args1 Hargs1_typed i A H τi Hτi HA
                         a1 Ha1_eq Ha1_typed).
  rewrite (app_cont_some (mod_data M) Γ f args2 Hargs2_typed i A H τi Hτi HA
                         a2 Ha2_eq Ha2_typed).
  f_equal.
  (* Now use Hargs at index i: extract τ' and the equality, then bridge τ' = τi
     via theq_typed_eq. *)
  unfold interp_term.
  revert Ha1_eq Ha2_eq Ha1_typed Ha2_typed.
  clear -Hargs.
  revert i a1 a2.
  induction Hargs as [| b1 b2 l1 l2 [τ' [Heq' IH']] Hrest IHrest];
    intros i a1 a2 Ha1_eq Ha2_eq Ha1_typed Ha2_typed.
  - destruct i; discriminate Ha1_eq.
  - destruct i as [|i].
    + simpl in Ha1_eq. injection Ha1_eq as Hb1_eq.
      simpl in Ha2_eq. injection Ha2_eq as Hb2_eq.
      subst b1 b2.
      pose proof (theq_typed_eq _ _ _ _ _ _ Heq') as [Hteq_l _].
      specialize (Hteq_l _ Ha1_typed). subst τ'.
      apply (IH' Ha1_typed Ha2_typed).
    + simpl in Ha1_eq, Ha2_eq.
      apply (IHrest i a1 a2 Ha1_eq Ha2_eq Ha1_typed Ha2_typed).
Qed.

(** Soundness: derivable equations are satisfied by every model. *)
Theorem soundness : forall (Th : Theory)
    (C : Category) (hp : HasFiniteProducts C) (M : Model Th C hp)
    (Γ : list Th.(th_sig).(sg_ty))
    (t t' : Term Th.(th_sig)) (τ : Th.(th_sig).(sg_ty))
    (Ht  : HasType Th.(th_sig) Γ t  τ)
    (Ht' : HasType Th.(th_sig) Γ t' τ)
    (Heq : ThEq Th.(th_sig) Th.(th_ax) Γ t t' τ),
    interp_term M Γ t  τ Ht =
    interp_term M Γ t' τ Ht'.
Proof.
  intros Th C hp M Γ t t' τ Ht Ht' Heq.
  revert Ht Ht'.
  induction Heq
    as [ t τ Ht
       | t1 t2 τ Heq1 IH1
       | t1 t2 t3 τ Heq1 IH1 Heq2 IH2
       | f args1 args2 Hargs
       | a sub Hin Htyp ]
    using ThEq_strong_ind.
  - (* theq_refl *)
    intros Ht1 Ht2. apply interp_term_pi.
  - (* theq_sym *)
    intros Ht2 Ht1. symmetry. apply IH1.
  - (* theq_trans: extract HasType of t2 via theq_preserves_typed on Heq1. *)
    intros Ht1 Ht3.
    pose proof (theq_preserves_typed _ _ _ _ _ _ Heq1) as [Hl_to_r _].
    specialize (Hl_to_r Ht1) as Ht2.
    rewrite (IH1 Ht1 Ht2). apply IH2.
  - (* theq_cong: τ here is [sg_cod f] *)
    intros Ht1 Ht2.
    unfold interp_term.
    rewrite (interp_term_data_app_explicit (mod_data M) Γ f args1 Ht1).
    rewrite (interp_term_data_app_explicit (mod_data M) Γ f args2 Ht2).
    f_equal.
    apply fp_tuple_ext. intros i A H.
    apply (cong_app_cont_eq Th C hp M Γ f args1 args2 Hargs
             (ht_app_args_f2 Ht1) (ht_app_args_f2 Ht2) i A H).
  - (* theq_ax *)
    intros Hsubt_lhs Hsubt_rhs.
    unfold interp_term.
    rewrite (interp_subst (mod_data M) a.(ax_lhs) Γ a.(ax_ctx) sub Htyp
                          a.(ax_sort) a.(ax_lhs_typed) Hsubt_lhs).
    rewrite (interp_subst (mod_data M) a.(ax_rhs) Γ a.(ax_ctx) sub Htyp
                          a.(ax_sort) a.(ax_rhs_typed) Hsubt_rhs).
    rewrite (M.(mod_ax) a Hin). reflexivity.
Qed.

(** ** Completeness via the generic model *)

Theorem completeness_from_generic_model (Th : Theory)
    (Γ : list Th.(th_sig).(sg_ty))
    (t t' : Term Th.(th_sig)) (τ : Th.(th_sig).(sg_ty))
    (Ht  : HasType Th.(th_sig) Γ t  τ)
    (Ht' : HasType Th.(th_sig) Γ t' τ)
    (Hmod : ClMor_theq Th Γ [τ]
              {| clmor_terms := [t];  clmor_typed := Forall2_cons _ _ Ht  (Forall2_nil _) |}
              {| clmor_terms := [t']; clmor_typed := Forall2_cons _ _ Ht' (Forall2_nil _) |}) :
    ThEq Th.(th_sig) Th.(th_ax) Γ t t' τ.
Proof.
  apply Hmod with 0.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** ** Full completeness

    Discharged via the generic model [GenericModelTh] in [ClTh Th].
    Specialise [Hall] to [GenericModelTh Th]; the interpretation lemma
    [interp_term_eq_transport] shows both sides reduce to
    [transport_clmor_dom] of [term_to_clmor_q].  Equality of these
    transports gives [ClMor_theq] equality of the underlying clmors,
    which is precisely what [completeness_from_generic_model] needs. *)

Theorem completeness : forall (Th : Theory)
    (Γ : list Th.(th_sig).(sg_ty))
    (t t' : Term Th.(th_sig)) (τ : Th.(th_sig).(sg_ty))
    (Ht  : HasType Th.(th_sig) Γ t  τ)
    (Ht' : HasType Th.(th_sig) Γ t' τ)
    (Hall : forall (C : Category) (hp : HasFiniteProducts C) (M : Model Th C hp),
              interp_term M Γ t  τ Ht =
              interp_term M Γ t' τ Ht'),
    ThEq Th.(th_sig) Th.(th_ax) Γ t t' τ.
Proof.
  intros Th Γ t t' τ Ht Ht' Hall.
  apply (completeness_from_generic_model Th Γ t t' τ Ht Ht').
  pose proof (Hall (ClTh Th) (clth_finite_products Th) (GenericModelTh Th)) as Hint.
  unfold interp_term in Hint. simpl in Hint.
  rewrite (interp_term_eq_transport Th Γ t τ Ht) in Hint.
  rewrite (interp_term_eq_transport Th Γ t' τ Ht') in Hint.
  unfold transport_clmor_dom in Hint.
  unfold term_to_clmor_q, term_to_clmor in Hint.
  (* Hint: eq_rect_r ... (clth_mk_q m_lhs) ... = eq_rect_r ... (clth_mk_q m_rhs) ...
     Strip the eq_rect_r by congruence: this needs that the eq_rect_r's are
     injective in their "x" argument, which holds because eq_rect is a bijection. *)
  (* eq_rect_r is a bijection.  Apply the inverse transport via a generic
     [eq_rect_inj] lemma. *)
  assert (eq_rect_inj : forall {A : Type} {P : A -> Type} {x y : A} (e : x = y)
                               (a b : P x),
                        eq_rect x P a y e = eq_rect x P b y e -> a = b).
  { intros A P x y e a b H. destruct e. exact H. }
  unfold eq_rect_r in Hint.
  pose proof (eq_rect_inj _ _ _ _
                (eq_sym (fp_prod_singleton_list_th Th Γ))
                (clth_mk_q {| clmor_terms := [t];
                              clmor_typed := Forall2_cons _ _ Ht (Forall2_nil _) |})
                (clth_mk_q {| clmor_terms := [t'];
                              clmor_typed := Forall2_cons _ _ Ht' (Forall2_nil _) |})
                Hint) as Hclmor_eq.
  apply clth_mk_q_eq_iff in Hclmor_eq.
  exact Hclmor_eq.
Qed.

(** ** Packaging *)

Theorem algebraic_theory_sound_and_complete : forall (Th : Theory)
    (Γ : list Th.(th_sig).(sg_ty))
    (t t' : Term Th.(th_sig)) (τ : Th.(th_sig).(sg_ty))
    (Ht  : HasType Th.(th_sig) Γ t  τ)
    (Ht' : HasType Th.(th_sig) Γ t' τ),
    ThEq Th.(th_sig) Th.(th_ax) Γ t t' τ
    <->
    (forall (C : Category) (hp : HasFiniteProducts C) (M : Model Th C hp),
       interp_term M Γ t  τ Ht =
       interp_term M Γ t' τ Ht').
Proof.
  intros Th Γ t t' τ Ht Ht'. split.
  - intros Heq C hp M. exact (soundness Th C hp M Γ t t' τ Ht Ht' Heq).
  - intros Hall. exact (completeness Th Γ t t' τ Ht Ht' Hall).
Qed.
