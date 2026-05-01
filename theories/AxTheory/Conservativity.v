(** * AxTheory/Conservativity.v
    Theorem 4.10.7: Conservativity of functional type theory over algebraic type theory.

    Statement:
    Let Th be an algebraic theory, and let Th' = GeneratedAxTheory(Th) be the
    Ax-theory generated from Th (same signature, same axioms, but with full
    lambda/product/exponential structure).

    If two algebraic terms M, M' : τ in algebraic context Γ satisfy
       Th' ⊢ Γ ⊢ M = M' : τ    (provably equal in the Ax-theory)
    then
       Th  ⊢ Γ ⊢ M = M' : τ    (already provably equal in the algebraic theory)

    Proof sketch (via gluing):
    1. I : Cl(Th) → Cl(Th') is the functor from relative freeness.
    2. By Proposition 4.10.2 and Lemma 4.10.3, I is full and faithful.
    3. An equation at ground types in Cl(Th') is a morphism in Cl(Th') between
       objects in the image of I.
    4. Fullness of I gives a preimage; faithfulness makes it unique.
    5. The preimage is the algebraic equation in Cl(Th). *)

Require Import CAG.ATT.Signature.
Require Import CAG.ATT.Syntax.
Require Import CAG.ATT.Theory.
Require Import CAG.ATT.Model.            (* for ht_app_args_f2, ht_app_cod_eq *)
Require Import CAG.ATT.ClassifyingCategory.
Require Import CAG.ATT.SoundComplete.    (* for ThEq_strong_ind, theq_preserves_typed, theq_typed_eq *)
Require Import CAG.AxTheory.Syntax.
Require Import CAG.AxTheory.Theory.
Require Import CAG.AxTheory.ClassifyingCategory.
Require Import CAG.AxTheory.GeneratedFunctionalTheory.
Require Import CAG.AxTheory.RelativeFreeCCC.
Require Import CAG.AxTheory.GluingSetup.
From Stdlib Require Import Lists.List.
Import ListNotations.

Set Universe Polymorphism.
Open Scope cat_scope.

(** ** Preliminary: ground-type equations as morphism equalities

    An equation  Th' ⊢ Γ ⊢ M = N : τ  at ground types corresponds to
    the identity of two morphisms in Cl(Th'):
       I([Γ]) --{lift M}--> I([τ])  =  I([Γ]) --{lift N}--> I([τ])

    where lift_alg_term embeds algebraic terms into AxCl. *)

Parameter alg_term_to_axcl_mor : forall {Th : Theory}
    (Γ : list Th.(th_sig).(sg_ty))
    (t : Term Th.(th_sig)) (τ : Th.(th_sig).(sg_ty))
    (Ht : HasType Th.(th_sig) Γ t τ),
    AxClMor Th.(th_sig) (I_obj Γ) (I_obj [τ]).

(** ** Main conservativity theorem

    BLOCKED on Task A.3 (gluing) per REFACTOR_PLAN.org Round 5 audit.

    Diagnosis: the proof of conservativity-from-Ax-to-alg goes through the
    gluing argument (Discussion 4.10.5 / Lemma 4.10.3 / Theorem 4.10.7).
    Specifically, given [Heq_ax : AxThEq ... (lift_alg_term t1) (lift_alg_term t2) ...]
    we view it as a morphism equality [I_map ⟦t1⟧ = I_map ⟦t2⟧] in
    [AxCl Sg], and then [I_is_faithful] (provided by [GluingSetup.v]'s
    [I_is_faithful] axiom) collapses it to [⟦t1⟧ = ⟦t2⟧] in [Cl Sg],
    which is precisely [ThEq] of [t1, t2].

    [I_is_faithful] is currently AXIOM in [GluingSetup.v], because its
    proof requires [gluing_data_exists] (the existence of the glued
    category Gl(T) with its CCC structure and the J/P2 functors), which
    is itself AXIOM pending Task A.3.  Thus this conservativity statement
    is BLOCKED behind A.3.

    Once A.3 lands ([gluing_data_exists] becomes a Definition), the
    discharge here will be a ~30-line proof: faithfulness of I gives a
    morphism preimage in [Cl Sg], which corresponds to [t1 = t2] up to
    [ThEq] (the algebraic congruence closure equivalent to morphism
    equality in [Cl Sg]). *)

Axiom conservativity_of_generated_functional_type_theory_over_ground_terms : forall
    (Th : Theory)
    (Γ : list Th.(th_sig).(sg_ty))
    (t1 t2 : Term Th.(th_sig))
    (τ : Th.(th_sig).(sg_ty))
    (Ht1 : HasType Th.(th_sig) Γ t1 τ)
    (Ht2 : HasType Th.(th_sig) Γ t2 τ)
    (Heq_ax : AxThEq Th.(th_sig)
                (List.map lift_alg_axiom Th.(th_ax))
                (List.map ax_ground Γ)
                (lift_alg_term t1) (lift_alg_term t2)
                (ax_ground τ)),
    ThEq Th.(th_sig) Th.(th_ax) Γ t1 t2 τ.

(** ** Uniqueness: the algebraic representative is unique up to ThEq

    DISCHARGED in Task A.4 (α R5, 2026-05-01).

    Diagnosis: the obligation here is not "uniqueness of a representative"
    in the universal-property sense; it is the soundness of [lift_alg_term]
    as a translation [ThEq → AxThEq]. Each [ThEq]-constructor lifts
    structurally to its [AxThEq] counterpart:
      [theq_refl] -> [axeq_refl] (via [lift_alg_term_typed])
      [theq_sym]  -> [axeq_sym]
      [theq_trans]-> [axeq_trans]
      [theq_cong] -> [axeq_app_fn_cong]   (constructor added to AxThEq in Task A.4)
      [theq_ax]   -> [axeq_ax]            (via [lift_alg_term_subst] commutation)

    Discharge approach: induction on [Heq] using [ThEq_strong_ind] (so the
    [theq_cong] case carries pointwise IH, not just pointwise [ThEq]).
    Type-uniqueness witnesses ([theq_typed_eq], [theq_preserves_typed]) are
    needed to bridge the existential [τ] in [theq_cong] to the [sg_dom f]
    type at each argument position. *)

(** *** Custom strong induction with typing premises carried through.

    [ThEq_strong_ind]'s motive [P t1 t2 τ] doesn't carry [HasType] witnesses
    of either side; the [theq_cong] case needs them to type the args.  We
    encode the typing premises into [P] and re-export. *)

Lemma ThEq_typed_strong_ind :
    forall (Sg : Signature) (ax : list (TheoryAxiom Sg))
           (Γ : list Sg.(sg_ty))
           (P : Term Sg -> Term Sg -> Sg.(sg_ty) -> Prop),
    (forall (t : Term Sg) (τ : Sg.(sg_ty)),
        HasType Sg Γ t τ -> P t t τ) ->
    (forall (t1 t2 : Term Sg) (τ : Sg.(sg_ty)),
        ThEq Sg ax Γ t1 t2 τ ->
        HasType Sg Γ t1 τ -> HasType Sg Γ t2 τ ->
        P t1 t2 τ -> P t2 t1 τ) ->
    (forall (t1 t2 t3 : Term Sg) (τ : Sg.(sg_ty)),
        ThEq Sg ax Γ t1 t2 τ ->
        HasType Sg Γ t1 τ -> HasType Sg Γ t2 τ -> HasType Sg Γ t3 τ ->
        P t1 t2 τ ->
        ThEq Sg ax Γ t2 t3 τ -> P t2 t3 τ -> P t1 t3 τ) ->
    (forall (f : Sg.(sg_fun)) (args1 args2 : list (Term Sg)),
        List.Forall2 (fun a1 a2 => exists τ,
                        ThEq Sg ax Γ a1 a2 τ /\
                        HasType Sg Γ a1 τ /\ HasType Sg Γ a2 τ /\
                        P a1 a2 τ) args1 args2 ->
        P (t_app f args1) (t_app f args2) (Sg.(sg_cod) f)) ->
    (forall (a : TheoryAxiom Sg) (sub : list (Term Sg)),
        List.In a ax ->
        List.Forall2 (HasType Sg Γ) sub a.(ax_ctx) ->
        P (subst_term Sg sub a.(ax_lhs)) (subst_term Sg sub a.(ax_rhs))
          a.(ax_sort)) ->
    forall t t' τ,
      HasType Sg Γ t τ -> HasType Sg Γ t' τ ->
      ThEq Sg ax Γ t t' τ -> P t t' τ.
Proof.
  intros Sg ax Γ P Prefl Psym Ptrans Pcong Pax.
  fix IH 6.
  intros t t' τ Ht Ht' Heq.
  destruct Heq as [t0 τ0 Ht0
                  | t1 t2 τ0 Heq1
                  | t1 t2 t3 τ0 Heq1 Heq2
                  | f args1 args2 Hargs
                  | a sub Hin Htyp ].
  - apply Prefl. exact Ht0.
  - apply (Psym _ _ _ Heq1 Ht' Ht).
    apply IH; [exact Ht' | exact Ht | exact Heq1].
  - (* For trans we need typing of the middle term. *)
    pose proof (theq_preserves_typed Sg ax Γ t1 t2 τ0 Heq1) as [Hpres _].
    pose proof (Hpres Ht) as Ht_mid.
    apply (Ptrans _ _ _ _ Heq1 Ht Ht_mid Ht'
                  (IH _ _ _ Ht Ht_mid Heq1)
                  Heq2
                  (IH _ _ _ Ht_mid Ht' Heq2)).
  - (* cong: typing of t_app f args1 gives typing of each arg.  Same for args2. *)
    pose proof (ht_app_args_f2 Ht)  as Hargs1_typed.
    pose proof (ht_app_args_f2 Ht') as Hargs2_typed.
    apply Pcong.
    (* Walk three lists in lockstep — generalize over an arbitrary dom list.
       Clear Ht / Ht' so they don't pollute IHrest's hypotheses. *)
    clear Ht Ht'.
    revert Hargs Hargs1_typed Hargs2_typed.
    generalize (Sg.(sg_dom) f) as dom.
    intros dom Hargs.
    revert dom.
    induction Hargs as [| b1 b2 l1 l2 [τ_b Heq_b] Hrest IHrest];
      intros dom H1typed H2typed.
    + constructor.
    + inversion H1typed as [|? ? ? dom_rest Hb1 Hl1]; subst.
      inversion H2typed as [|? ? ? ? Hb2 Hl2]; subst.
      constructor.
      * pose proof (theq_typed_eq Sg ax Γ b1 b2 τ_b Heq_b) as [Heq_l _].
        specialize (Heq_l _ Hb1). subst τ_b.
        eexists. split. exact Heq_b.
        split. exact Hb1.
        split. exact Hb2.
        apply IH; [ exact Hb1 | exact Hb2 | exact Heq_b ].
      * exact (IHrest dom_rest Hl1 Hl2).
  - apply Pax. exact Hin. exact Htyp.
Qed.

Lemma conservativity_uniqueness : forall
    (Th : Theory)
    (Γ : list Th.(th_sig).(sg_ty))
    (t1 t2 : Term Th.(th_sig))
    (τ : Th.(th_sig).(sg_ty))
    (Ht1 : HasType Th.(th_sig) Γ t1 τ)
    (Ht2 : HasType Th.(th_sig) Γ t2 τ)
    (Heq : ThEq Th.(th_sig) Th.(th_ax) Γ t1 t2 τ),
    AxThEq Th.(th_sig)
           (List.map lift_alg_axiom Th.(th_ax))
           (List.map ax_ground Γ)
           (lift_alg_term t1) (lift_alg_term t2) (ax_ground τ).
Proof.
  intros Th Γ t1 t2 τ Ht1 Ht2 Heq.
  set (Sg := Th.(th_sig)) in *.
  set (ax := Th.(th_ax)) in *.
  set (axS := List.map (@lift_alg_axiom Sg) ax).
  set (ΓS := List.map (@ax_ground Sg) Γ).
  (* Strengthened motive: bundle the HasType premises so [theq_cong] can
     recover [Forall2 (HasType Sg Γ) argsi (sg_dom f)] from [t_app f argsi]
     via [ht_app_args_f2]. *)
  cut (forall u v σ,
         HasType Sg Γ u σ -> HasType Sg Γ v σ ->
         ThEq Sg ax Γ u v σ ->
         AxThEq Sg axS ΓS (lift_alg_term u) (lift_alg_term v) (ax_ground σ)).
  { intro K. exact (K t1 t2 τ Ht1 Ht2 Heq). }
  clear Heq Ht1 Ht2 t1 t2 τ.
  intros u v σ Hu Hv Heq.
  apply (ThEq_typed_strong_ind Sg ax Γ
    (fun u' v' σ' =>
       HasType Sg Γ u' σ' -> HasType Sg Γ v' σ' ->
       AxThEq Sg axS ΓS (lift_alg_term u') (lift_alg_term v') (ax_ground σ')))
    with (t := u) (t' := v) (τ := σ); try assumption.
  - (* refl *)
    intros t σ' Ht _ _.
    apply axeq_refl. exact (lift_alg_term_typed Sg Γ t σ' Ht).
  - (* sym *)
    intros u' v' σ' _ Hu' Hv' IH' Hv'2 Hu'2.
    apply axeq_sym. apply IH'; assumption.
  - (* trans *)
    intros u' v' w' σ' Heq1 Hu' Hv' Hw' IH1 Heq2 IH2 Hu'2 Hw'2.
    apply (axeq_trans Sg axS ΓS (lift_alg_term u') (lift_alg_term v')
             (lift_alg_term w') (ax_ground σ')).
    + apply IH1; assumption.
    + apply IH2; assumption.
  - (* cong *)
    intros f args1 args2 Hargs Ht_app1 Ht_app2.
    simpl.
    pose proof (ht_app_args_f2 Ht_app1) as Hargs1_typed.
    pose proof (ht_app_args_f2 Ht_app2) as Hargs2_typed.
    apply (axeq_app_fn_cong Sg axS ΓS f
             (List.map (@lift_alg_term Sg) args1)
             (List.map (@lift_alg_term Sg) args2)).
    + (* Forall2 typing of map lift_alg_term args1 against sg_dom f *)
      clear Hargs Hargs2_typed Ht_app1 Ht_app2.
      induction Hargs1_typed as [| a τa rest dom Ha Hrest IHrest]; simpl.
      * constructor.
      * constructor.
        -- exact (lift_alg_term_typed Sg Γ a τa Ha).
        -- exact IHrest.
    + (* args2 typed *)
      clear Hargs Hargs1_typed Ht_app1 Ht_app2.
      induction Hargs2_typed as [| a τa rest dom Ha Hrest IHrest]; simpl.
      * constructor.
      * constructor.
        -- exact (lift_alg_term_typed Sg Γ a τa Ha).
        -- exact IHrest.
    + (* per-index AxThEq.  Walk Hargs alongside Hargs1_typed (whose
         second list IS sg_dom f).  Generalize over an arbitrary dom list
         so the IHrest types correctly across nested induction. *)
      intros i τi M M' Hτi HM HM'.
      rewrite List.nth_error_map in HM.
      rewrite List.nth_error_map in HM'.
      destruct (List.nth_error args1 i) as [a1|] eqn:Ha1; [|discriminate].
      destruct (List.nth_error args2 i) as [a2|] eqn:Ha2; [|discriminate].
      simpl in HM, HM'. injection HM as <-. injection HM' as <-.
      (* Generalize the dom (= sg_dom Sg f) so IHrest types over arbitrary doms. *)
      clear Ht_app1 Ht_app2.
      revert i Ha1 Ha2 Hτi Hargs1_typed Hargs2_typed.
      generalize (Sg.(sg_dom) f) as dom.
      intros dom i Ha1 Ha2 Hτi H1typed H2typed.
      revert dom i Ha1 Ha2 Hτi H1typed H2typed.
      induction Hargs as [| b1 b2 l1 l2 [τ_b [Heq_b [Hb1 [Hb2 IH_b]]]] Hrest IHrest];
        intros dom i Ha1 Ha2 Hτi H1typed H2typed.
      * destruct i; discriminate Ha1.
      * inversion H1typed as [|? y ? dom_rest Hbb1 Hl1]; subst.
        inversion H2typed as [|? ? ? ? Hbb2 Hl2]; subst.
        destruct i as [|i].
        -- simpl in Ha1, Ha2, Hτi.
           injection Ha1 as <-. injection Ha2 as <-. injection Hτi as <-.
           pose proof (theq_typed_eq Sg ax Γ b1 b2 τ_b Heq_b) as [Heq_l _].
           specialize (Heq_l _ Hbb1). subst τ_b.
           apply IH_b; assumption.
        -- simpl in Ha1, Ha2, Hτi.
           exact (IHrest dom_rest i Ha1 Ha2 Hτi Hl1 Hl2).
  - (* ax *)
    intros a sub Hin Hsub _ _.
    rewrite (lift_alg_term_subst Sg Γ a.(ax_ctx) sub Hsub
                                 a.(ax_lhs) a.(ax_sort) a.(ax_lhs_typed)).
    rewrite (lift_alg_term_subst Sg Γ a.(ax_ctx) sub Hsub
                                 a.(ax_rhs) a.(ax_sort) a.(ax_rhs_typed)).
    apply (axeq_ax Sg axS ΓS (lift_alg_axiom a) (List.map (@lift_alg_term Sg) sub)).
    + apply List.in_map. exact Hin.
    + simpl.
      induction Hsub as [| s τs rest dom Hs Hrest IHrest]; simpl.
      * constructor.
      * constructor.
        -- exact (lift_alg_term_typed Sg Γ s τs Hs).
        -- exact IHrest.
Qed.

(** ** The semantic interpretation

    Adding functional structure (lambda/products/exponentials) to an algebraic
    theory does not create new equalities at ground types.  The algebraic and
    functional fragments have the same ground-type equational theory.

    In programming-language terms:
    - ground types in the functional theory have exactly the same normal forms
      as in the algebraic theory
    - beta-reduction and eta-expansion never collapse distinct algebraic terms *)

(** Package the full equivalence *)
Theorem functional_theory_same_ground_equalities
    (Th : Theory)
    (Γ : list Th.(th_sig).(sg_ty))
    (t1 t2 : Term Th.(th_sig))
    (τ : Th.(th_sig).(sg_ty))
    (Ht1 : HasType Th.(th_sig) Γ t1 τ)
    (Ht2 : HasType Th.(th_sig) Γ t2 τ) :
    ThEq Th.(th_sig) Th.(th_ax) Γ t1 t2 τ
    <->
    AxThEq Th.(th_sig)
           (List.map lift_alg_axiom Th.(th_ax))
           (List.map ax_ground Γ)
           (lift_alg_term t1) (lift_alg_term t2) (ax_ground τ).
Proof.
  split.
  - intro H. apply conservativity_uniqueness; assumption.
  - intro H. apply conservativity_of_generated_functional_type_theory_over_ground_terms;
    assumption.
Qed.
