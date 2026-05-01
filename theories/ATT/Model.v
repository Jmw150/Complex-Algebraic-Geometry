(** * ATT/Model.v
    Models of an algebraic theory in a category with finite products.

    A model of Th in C (with finite products) assigns:
    - to each sort α an object [α]_M ∈ C
    - to each function symbol f : (α₁,...,αₙ) → β a morphism
        [f]_M : [α₁]_M × ... × [αₙ]_M → [β]_M
    satisfying all axioms of Th (interpreted via term interpretation). *)

Require Import CAG.ATT.Signature.
Require Import CAG.ATT.Syntax.
Require Import CAG.ATT.Theory.
Require Import CAG.Category.Core.
Require Import CAG.Category.Products.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.Wf_nat.
From Stdlib Require Import Wellfounded.Inverse_Image.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Logic.FunctionalExtensionality.
Import ListNotations.

Set Universe Polymorphism.
Open Scope cat_scope.

(** ** Finite product of a list of objects

    [fp_prod hp [A₁,...,Aₙ]] is the iterated product A₁ × ... × Aₙ,
    with the terminal object for the empty list. *)

Fixpoint fp_prod {C : Category} (hp : HasFiniteProducts C)
    (objs : list C.(Ob)) : C.(Ob) :=
  match objs with
  | []      => projT1 (@fp_terminal C hp)
  | [A]     => A
  | A :: As => @prod_obj C (@fp_binary C hp) A (fp_prod hp As)
  end.

(** ** Model data record

    The "data" of a model: just the interpretation of sorts and function
    symbols.  We split this from the axiom obligation so that term
    interpretation can be defined first and then referenced inside the
    real [mod_ax] obligation below. *)

Record ModelData (Th : Theory) (C : Category) (hp : HasFiniteProducts C) : Type := {
  (** Interpretation of sorts. *)
  md_ty   : Th.(th_sig).(sg_ty) -> C.(Ob);

  (** Interpretation of function symbols.
      [f : α₁,...,αₙ → β] is sent to a morphism
        md_fun f : Πᵢ md_ty αᵢ → md_ty β *)
  md_fun  : forall (f : Th.(th_sig).(sg_fun)),
              C⟦ fp_prod hp (List.map md_ty (Th.(th_sig).(sg_dom) f)),
                 md_ty (Th.(th_sig).(sg_cod) f) ⟧;
}.

Arguments md_ty  {Th C hp}.
Arguments md_fun {Th C hp}.

(** ** Term interpretation

    Given model data and a context Γ, interpret a well-typed term
    t : τ as a morphism   fp_prod hp (map md_ty Γ) → md_ty τ.

    We use well-founded induction on the size of the term to avoid
    large elimination of the Prop-valued HasType predicate. *)

(** Term size measure for well-founded recursion. *)
Fixpoint att_term_size {Sg : Signature} (t : Term Sg) : nat :=
  match t with
  | t_var _      => 1
  | t_app _ args => 1 + List.fold_right (fun t' acc => att_term_size t' + acc) 0 args
  end.

Definition att_term_lt {Sg : Signature} (s t : Term Sg) : Prop :=
  att_term_size s < att_term_size t.

Lemma att_term_lt_wf {Sg : Signature} : well_founded (@att_term_lt Sg).
Proof.
  intro x.
  apply (Acc_inverse_image (Term Sg) nat lt att_term_size).
  apply lt_wf.
Qed.

Lemma att_args_size_fold {Sg : Signature} (args : list (Term Sg))
    (arg : Term Sg) (i : nat)
    (H : List.nth_error args i = Some arg) :
    att_term_size arg <=
    List.fold_right (fun t' acc => att_term_size t' + acc) 0 args.
Proof.
  revert i H.
  induction args as [| a rest IH]; intros i H.
  - destruct i; discriminate H.
  - destruct i as [| i].
    + simpl in H. injection H as <-. simpl. lia.
    + simpl in H. simpl. specialize (IH i H). lia.
Qed.

Lemma att_args_size_lt {Sg : Signature} (f : Sg.(sg_fun)) (args : list (Term Sg))
    (arg : Term Sg) (i : nat)
    (H : List.nth_error args i = Some arg) :
    att_term_lt arg (t_app f args).
Proof.
  unfold att_term_lt. simpl.
  pose proof (att_args_size_fold args arg i H). lia.
Qed.

(** Inversion helpers for HasType (Prop → Prop, safe for Type goals). *)

Lemma ht_var_nth_err {Sg : Signature} {Γ : list Sg.(sg_ty)} {n : nat} {τ : Sg.(sg_ty)}
    (Ht : HasType Sg Γ (t_var n) τ) : List.nth_error Γ n = Some τ.
Proof. inversion Ht; assumption. Qed.

Lemma ht_app_cod_eq {Sg : Signature} {Γ : list Sg.(sg_ty)} {f : Sg.(sg_fun)}
    {args : list (Term Sg)} {τ : Sg.(sg_ty)}
    (Ht : HasType Sg Γ (t_app f args) τ) : τ = Sg.(sg_cod) f.
Proof. inversion Ht; reflexivity. Qed.

Lemma ht_app_args_f2 {Sg : Signature} {Γ : list Sg.(sg_ty)} {f : Sg.(sg_fun)}
    {args : list (Term Sg)} {τ : Sg.(sg_ty)}
    (Ht : HasType Sg Γ (t_app f args) τ) :
    Forall2 (HasType Sg Γ) args (Sg.(sg_dom) f).
Proof. inversion Ht; assumption. Qed.

(** Extract HasType for the i-th argument directly (Prop → Prop, safe). *)
Lemma forall2_nth_hastype {Sg : Signature} {Γ : list Sg.(sg_ty)}
    {args : list (Term Sg)} {dom : list Sg.(sg_ty)}
    (F : Forall2 (HasType Sg Γ) args dom)
    (i : nat) (arg : Term Sg) (τ : Sg.(sg_ty))
    (Harg : List.nth_error args i = Some arg)
    (Hτ : List.nth_error dom i = Some τ) :
    HasType Sg Γ arg τ.
Proof.
  revert i arg τ Harg Hτ.
  induction F as [| a b l1 l2 Hab Hrest IH]; intros i arg τ Harg Hτ.
  - destruct i; discriminate Harg.
  - destruct i as [| i].
    + simpl in Harg, Hτ.
      injection Harg as <-. injection Hτ as <-. exact Hab.
    + simpl in Harg, Hτ. exact (IH i arg τ Harg Hτ).
Qed.

(** A "typed term" packages a term with its type. *)
Record TypedTerm (Th : Theory) (Γ : list Th.(th_sig).(sg_ty)) : Type := {
  tt_term : Term Th.(th_sig);
  tt_sort : Th.(th_sig).(sg_ty);
  tt_typed : HasType Th.(th_sig) Γ tt_term tt_sort;
}.

(** Projection from context product: the i-th variable.
    We extract this as the i-th projection morphism from the iterated product. *)
Theorem context_proj : forall {C : Category} (hp : HasFiniteProducts C)
    {objs : list C.(Ob)} (i : nat) (A : C.(Ob)),
    List.nth_error objs i = Some A ->
    C⟦ fp_prod hp objs, A ⟧.
Proof.
  intros C hp objs.
  induction objs as [|B Bs IH]; intros i A Hnth.
  - destruct i; discriminate Hnth.
  - destruct i as [|i]; simpl in Hnth.
    + injection Hnth as <-.
      destruct Bs as [|B2 Bs'].
      * simpl. exact (C.(id) B).
      * simpl.
        exact (bp_proj1 (prod_bp (@fp_binary C hp) B (fp_prod hp (B2 :: Bs')))).
    + destruct Bs as [|B2 Bs'].
      * destruct i; discriminate Hnth.
      * simpl.
        exact (IH i A Hnth ∘ bp_proj2 (prod_bp (@fp_binary C hp) B (fp_prod hp (B2 :: Bs')))).
Defined.

(** Pairing into a product: given morphisms to each factor, build a morphism
    into the iterated product.  *)
Theorem fp_tuple : forall {C : Category} (hp : HasFiniteProducts C)
    {X : C.(Ob)} (objs : list C.(Ob))
    (fs : forall i A, List.nth_error objs i = Some A -> C⟦X, A⟧),
    C⟦X, fp_prod hp objs⟧.
Proof.
  intros C hp X objs.
  induction objs as [|A As IH]; intros fs.
  - simpl.
    exact (term_arr (projT1 (@fp_terminal C hp)) (projT2 (@fp_terminal C hp)) X).
  - destruct As as [|B Bs].
    + simpl. exact (fs 0 A eq_refl).
    + simpl.
      exact (bp_pair (prod_bp (@fp_binary C hp) A (fp_prod hp (B :: Bs)))
               (fs 0 A eq_refl)
               (IH (fun i A' H => fs (S i) A' H))).
Defined.

(** Term interpretation function, parametric in [ModelData].
    This is the workhorse used to define both [interp_term] (on full Models)
    and to state the [mod_ax] obligation below. *)
Theorem interp_term_data : forall {Th : Theory} {C : Category} {hp : HasFiniteProducts C}
    (D : ModelData Th C hp)
    (Γ : list Th.(th_sig).(sg_ty))
    (t : Term Th.(th_sig))
    (τ : Th.(th_sig).(sg_ty))
    (Ht : HasType Th.(th_sig) Γ t τ),
    C⟦ fp_prod hp (List.map D.(md_ty) Γ), D.(md_ty) τ ⟧.
Proof.
  intros Th C hp D Γ t τ Ht.
  revert Γ τ Ht.
  refine (Fix (@att_term_lt_wf Th.(th_sig))
              (fun t => forall Γ τ,
                        HasType Th.(th_sig) Γ t τ ->
                        C⟦ fp_prod hp (List.map (md_ty D) Γ), md_ty D τ ⟧)
              _ t).
  intros t0 IH Γ τ Ht.
  destruct t0 as [n | f args].
  - (* t_var n: project from the context product *)
    apply (context_proj hp n (md_ty D τ)).
    rewrite List.nth_error_map.
    rewrite (ht_var_nth_err Ht).
    reflexivity.
  - (* t_app f args: interpret args via IH, pair, then apply md_fun *)
    rewrite (ht_app_cod_eq Ht).
    refine (md_fun D f ∘ fp_tuple hp (List.map (md_ty D) (Th.(th_sig).(sg_dom) f)) _).
    intros i A H.
    rewrite List.nth_error_map in H.
    destruct (List.nth_error (Th.(th_sig).(sg_dom) f) i) as [τi|] eqn:Hτi.
    + simpl in H. injection H as <-.
      destruct (List.nth_error args i) as [arg |] eqn:Harg.
      * exact (IH arg (att_args_size_lt f args arg i Harg) Γ τi
                 (forall2_nth_hastype (ht_app_args_f2 Ht) i arg τi Harg Hτi)).
      * exfalso.
        destruct (Forall2_nth_error_l _ _ _ (ht_app_args_f2 Ht) i τi Hτi)
          as [arg [Harg' _]].
        rewrite Harg in Harg'. discriminate.
    + simpl in H. discriminate.
Defined.

(** ** Model record

    A model of Th in (C, hp) consists of model data together with a
    soundness obligation: for every axiom (Γ ⊢ ax_lhs = ax_rhs : ax_sort)
    of Th, the interpretations of [ax_lhs] and [ax_rhs] in [ax_ctx] coincide
    as morphisms in C.

    This replaces the previous [True] placeholder.  The obligation is
    structural: it must be discharged by every concrete [Model] constructor.
    For theories with empty axiom sets ([th_ax := []]) the obligation is
    vacuously true (there is no [a : TheoryAxiom] with [In a []]). *)

Record Model (Th : Theory) (C : Category) (hp : HasFiniteProducts C) : Type := {
  mod_data : ModelData Th C hp;

  (** The axioms of Th hold in M.

      For each axiom [a] of Th, the morphisms obtained by interpreting
      [a.(ax_lhs)] and [a.(ax_rhs)] in the context [a.(ax_ctx)] (using
      the data of [mod_data]) are equal in C. *)
  mod_ax   : forall (a : TheoryAxiom Th.(th_sig))
                    (Hin : List.In a Th.(th_ax)),
               interp_term_data mod_data a.(ax_ctx)
                 a.(ax_lhs) a.(ax_sort) a.(ax_lhs_typed)
               =
               interp_term_data mod_data a.(ax_ctx)
                 a.(ax_rhs) a.(ax_sort) a.(ax_rhs_typed);
}.

Arguments mod_data {Th C hp}.
Arguments mod_ax   {Th C hp}.

(** ** Compatibility accessors

    These wrap the [mod_data] field so that downstream code can keep using
    [mod_ty M] and [mod_fun M] as before.  Note: the record-projection
    notation [M.(mod_ty)] is no longer available because [mod_ty] is now
    a [Definition], not a record field — call sites use [mod_ty M]. *)

Definition mod_ty {Th : Theory} {C : Category} {hp : HasFiniteProducts C}
    (M : Model Th C hp) : Th.(th_sig).(sg_ty) -> C.(Ob) :=
  md_ty (mod_data M).

Definition mod_fun {Th : Theory} {C : Category} {hp : HasFiniteProducts C}
    (M : Model Th C hp)
    (f : Th.(th_sig).(sg_fun)) :
    C⟦ fp_prod hp (List.map (mod_ty M) (Th.(th_sig).(sg_dom) f)),
       mod_ty M (Th.(th_sig).(sg_cod) f) ⟧ :=
  md_fun (mod_data M) f.

(** Term interpretation on a full model: just the data version. *)
Definition interp_term {Th : Theory} {C : Category} {hp : HasFiniteProducts C}
    (M : Model Th C hp)
    (Γ : list Th.(th_sig).(sg_ty))
    (t : Term Th.(th_sig))
    (τ : Th.(th_sig).(sg_ty))
    (Ht : HasType Th.(th_sig) Γ t τ) :
    C⟦ fp_prod hp (List.map (mod_ty M) Γ), mod_ty M τ ⟧ :=
  interp_term_data (mod_data M) Γ t τ Ht.

(** ** Reduction lemmas for [interp_term_data]
    (Task L.2a — bridges the opaque [Fix]-based definition to a
    computational form, so the soundness proof in SoundComplete.v
    can rewrite with these.)

    [interp_term_data] is defined via well-founded recursion on the
    term size, so it does not reduce by [simpl] or [unfold] alone.
    These lemmas expose its computational content.

    They depend on [Stdlib.Logic.ProofIrrelevance.proof_irrelevance]
    and [Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep],
    both already used elsewhere in the project. *)

(** [Fix_eq] F_ext witness for the body of [interp_term_data]: any two
    extensionally-equal IH continuations are propositionally equal, by
    [functional_extensionality_dep]. *)
Lemma interp_term_data_IH_eq :
    forall {Th : Theory} {C : Category} {hp : HasFiniteProducts C}
           (D : ModelData Th C hp)
           (x : Term Th.(th_sig))
           (f g : forall y : Term Th.(th_sig), att_term_lt y x ->
                  forall (Γ : list Th.(th_sig).(sg_ty))
                         (τ : Th.(th_sig).(sg_ty)),
                  HasType Th.(th_sig) Γ y τ ->
                  C⟦ fp_prod hp (List.map (md_ty D) Γ), md_ty D τ ⟧),
    (forall y p, f y p = g y p) ->
    f = g.
Proof.
  intros Th C hp D x f g Hext.
  apply functional_extensionality_dep. intro y.
  apply functional_extensionality_dep. intro p.
  apply Hext.
Qed.

(** Proof irrelevance for the [HasType] argument of [interp_term_data].
    This is the workhorse lemma for soundness: when two derivations
    [Ht1, Ht2 : HasType Sg Γ t τ] of the same judgment are present,
    the two interpretations are equal as morphisms in C. *)
Lemma interp_term_data_pi : forall {Th : Theory} {C : Category}
    {hp : HasFiniteProducts C} (D : ModelData Th C hp)
    (Γ : list Th.(th_sig).(sg_ty)) (t : Term Th.(th_sig))
    (τ : Th.(th_sig).(sg_ty))
    (Ht1 Ht2 : HasType Th.(th_sig) Γ t τ),
    interp_term_data D Γ t τ Ht1 = interp_term_data D Γ t τ Ht2.
Proof.
  intros. rewrite (proof_irrelevance _ Ht1 Ht2). reflexivity.
Qed.

(** Same for [interp_term] on a full model. *)
Lemma interp_term_pi : forall {Th : Theory} {C : Category}
    {hp : HasFiniteProducts C} (M : Model Th C hp)
    (Γ : list Th.(th_sig).(sg_ty)) (t : Term Th.(th_sig))
    (τ : Th.(th_sig).(sg_ty))
    (Ht1 Ht2 : HasType Th.(th_sig) Γ t τ),
    interp_term M Γ t τ Ht1 = interp_term M Γ t τ Ht2.
Proof.
  intros. apply interp_term_data_pi.
Qed.

(** Reduction lemma at a variable: [interp_term_data] of [t_var n]
    is the [n]-th projection from the iterated context product.

    The user supplies the proof [Hn] that [n] is in range with the
    right type in the projected list; by [proof_irrelevance] all such
    proofs yield the same morphism. *)
Lemma interp_term_data_var :
    forall {Th : Theory} {C : Category} {hp : HasFiniteProducts C}
           (D : ModelData Th C hp)
           (Γ : list Th.(th_sig).(sg_ty))
           (n : nat) (τ : Th.(th_sig).(sg_ty))
           (Ht : HasType Th.(th_sig) Γ (t_var n) τ)
           (Hn : List.nth_error (List.map (md_ty D) Γ) n = Some (md_ty D τ)),
    interp_term_data D Γ (t_var n) τ Ht =
    context_proj hp n (md_ty D τ) Hn.
Proof.
  intros Th C hp D Γ n τ Ht Hn.
  unfold interp_term_data.
  rewrite Fix_eq.
  - simpl. f_equal. apply proof_irrelevance.
  - intros x u v Huv.
    assert (Hu : u = v).
    { apply functional_extensionality_dep; intro y.
      apply functional_extensionality_dep; intro p. apply Huv. }
    rewrite Hu. reflexivity.
Qed.

(** Reduction lemma at a function application: when [Ht] is a
    [HasType] derivation for [t_app f args] at sort [sg_cod f] (the
    "natural" sort), [interp_term_data] is [md_fun D f] composed with
    some tuple [g] of the argument interpretations.

    The tuple [g] is presented existentially because the explicit form
    is heavily dependent (involves [eq_rect] over [List.nth_error_map]).
    The witness equation [Hg] characterises [g] pointwise: the i-th
    component is the interpretation of the i-th argument. *)
Lemma interp_term_data_app :
    forall {Th : Theory} {C : Category} {hp : HasFiniteProducts C}
           (D : ModelData Th C hp)
           (Γ : list Th.(th_sig).(sg_ty))
           (f : Th.(th_sig).(sg_fun))
           (args : list (Term Th.(th_sig)))
           (Ht : HasType Th.(th_sig) Γ (t_app f args) (Th.(th_sig).(sg_cod) f)),
    exists g : C⟦ fp_prod hp (List.map (md_ty D) Γ),
                  fp_prod hp (List.map (md_ty D) (Th.(th_sig).(sg_dom) f)) ⟧,
      interp_term_data D Γ (t_app f args) (Th.(th_sig).(sg_cod) f) Ht =
      md_fun D f ∘ g.
Proof.
  intros Th C hp D Γ f args Ht.
  eexists.
  unfold interp_term_data at 1.
  rewrite Fix_eq.
  - simpl. unfold eq_rect_r.
    assert (eq_sym (ht_app_cod_eq Ht) = eq_refl) as ->
      by apply proof_irrelevance.
    simpl. reflexivity.
  - intros x u v Huv.
    assert (Hu : u = v).
    { apply functional_extensionality_dep; intro y.
      apply functional_extensionality_dep; intro p. apply Huv. }
    rewrite Hu. reflexivity.
Qed.

(** ** Task L.2c — Fully-explicit [interp_term_data_app] + [interp_subst]

    Below: the canonical "argument-tuple continuation" [app_cont], the
    fully-explicit reduction lemma [interp_term_data_app_explicit], the
    "substitution-tuple continuation" [subst_cont] / [subst_morph], and
    the substitution-interpretation lemma [interp_subst].

    Resolution of the L.2a dependent-pattern blocker: [app_cont] is
    [Defined] and structurally mirrors the inner continuation produced
    by [interp_term_data] on [t_app f args].  Both [context_proj] and
    [fp_tuple] above were converted from [Qed] to [Defined] so that
    [simpl]/[cbn] can drive the proofs to definitional equality.  The
    explicit lemma then closes by [f_equal] alone — Coq's
    convertibility checker reduces [app_cont] back to the inline body. *)

(** Pointwise extensionality of [fp_tuple] — used in proofs that two
    differently-named continuations agree. *)
Lemma fp_tuple_ext : forall {C : Category} (hp : HasFiniteProducts C)
    {X : C.(Ob)} (objs : list C.(Ob))
    (fs gs : forall i A, List.nth_error objs i = Some A -> C⟦X, A⟧),
    (forall i A H, fs i A H = gs i A H) ->
    fp_tuple hp objs fs = fp_tuple hp objs gs.
Proof.
  intros C hp X objs fs gs Hext.
  assert (Hfg : fs = gs).
  { apply functional_extensionality_dep. intro i.
    apply functional_extensionality_dep. intro A.
    apply functional_extensionality_dep. intro H.
    apply Hext. }
  rewrite Hfg. reflexivity.
Qed.

(** Beta law for [fp_tuple] / [context_proj]:
    [context_proj n A Hn ∘ fp_tuple objs fs = fs n A Hn].

    By induction on [objs], using [bp_beta1]/[bp_beta2] and
    [proof_irrelevance] to identify the equality witnesses. *)
Lemma fp_tuple_proj : forall {C : Category} (hp : HasFiniteProducts C)
    {X : C.(Ob)} (objs : list C.(Ob))
    (fs : forall i A, List.nth_error objs i = Some A -> C⟦X, A⟧)
    (n : nat) (A : C.(Ob))
    (Hn : List.nth_error objs n = Some A),
    context_proj hp n A Hn ∘ fp_tuple hp objs fs = fs n A Hn.
Proof.
  intros C hp X objs.
  induction objs as [|B Bs IH]; intros fs n A Hn.
  - destruct n; discriminate Hn.
  - destruct n as [|n].
    + simpl in Hn. injection Hn as Heq. subst.
      destruct Bs as [|B2 Bs'].
      * simpl. rewrite (proof_irrelevance _ Hn eq_refl).
        cbn. apply id_left.
      * simpl. rewrite (proof_irrelevance _ Hn eq_refl).
        cbn. rewrite bp_beta1. reflexivity.
    + destruct Bs as [|B2 Bs'].
      * destruct n; discriminate Hn.
      * simpl. cbn. rewrite <- comp_assoc.
        rewrite bp_beta2. apply IH.
Qed.

(** Canonical continuation for the argument tuple of an application
    [t_app f args].  Given the [Forall2 (HasType Sg Γ) args (sg_dom f)]
    derivation, it returns at index [i] the morphism interpreting the
    [i]-th argument. *)
Definition app_cont {Th : Theory} {C : Category} {hp : HasFiniteProducts C}
    (D : ModelData Th C hp) (Γ : list Th.(th_sig).(sg_ty))
    (f : Th.(th_sig).(sg_fun)) (args : list (Term Th.(th_sig)))
    (Hargs : Forall2 (HasType Th.(th_sig) Γ) args (Th.(th_sig).(sg_dom) f))
    (i : nat) (A : C.(Ob))
    (H : List.nth_error (List.map (md_ty D) (Th.(th_sig).(sg_dom) f)) i = Some A) :
    C⟦fp_prod hp (List.map (md_ty D) Γ), A⟧.
Proof.
  rewrite List.nth_error_map in H.
  destruct (List.nth_error (Th.(th_sig).(sg_dom) f) i) as [τi|] eqn:Hτi.
  - simpl in H. injection H as <-.
    destruct (List.nth_error args i) as [arg|] eqn:Harg.
    + exact (interp_term_data D Γ arg τi
               (forall2_nth_hastype Hargs i arg τi Harg Hτi)).
    + exfalso.
      destruct (Forall2_nth_error_l _ _ _ Hargs i τi Hτi) as [arg [Harg' _]].
      rewrite Harg in Harg'. discriminate.
  - simpl in H. discriminate.
Defined.

(** **Fully-explicit** reduction lemma at a function application.

    The right-hand side is [md_fun D f ∘ fp_tuple hp _ (app_cont …)],
    where [app_cont] is the canonical argument-interpretation
    continuation defined above.  No existential quantifier — the
    explicit witness is named.

    Proof: unfold [interp_term_data], drive [Fix_eq], collapse the
    [eq_rect_r] over [ht_app_cod_eq Ht] via [proof_irrelevance], and
    close by [f_equal] — Coq's convertibility checker recognises that
    the inline body of [interp_term_data] and [app_cont] reduce to the
    same term (because [app_cont] is [Defined] and [fp_tuple],
    [context_proj] above are [Defined] too). *)
Lemma interp_term_data_app_explicit :
    forall {Th : Theory} {C : Category} {hp : HasFiniteProducts C}
           (D : ModelData Th C hp)
           (Γ : list Th.(th_sig).(sg_ty))
           (f : Th.(th_sig).(sg_fun))
           (args : list (Term Th.(th_sig)))
           (Ht : HasType Th.(th_sig) Γ (t_app f args) (Th.(th_sig).(sg_cod) f)),
    interp_term_data D Γ (t_app f args) (Th.(th_sig).(sg_cod) f) Ht =
    md_fun D f ∘ fp_tuple hp (List.map (md_ty D) (Th.(th_sig).(sg_dom) f))
      (app_cont D Γ f args (ht_app_args_f2 Ht)).
Proof.
  intros Th C hp D Γ f args Ht.
  unfold interp_term_data at 1.
  rewrite Fix_eq.
  2: { intros x u v Huv.
       assert (Hu : u = v).
       { apply functional_extensionality_dep; intro y.
         apply functional_extensionality_dep; intro p. apply Huv. }
       rewrite Hu. reflexivity. }
  simpl. unfold eq_rect_r.
  assert (eq_sym (ht_app_cod_eq Ht) = eq_refl) as ->
    by apply proof_irrelevance.
  simpl. f_equal.
Qed.

(** ** Substitution morphism

    Given a substitution [sub : list (Term Sg)] and a typing derivation
    [Hsub : Forall2 (HasType Sg Γ) sub Γ'], we build a morphism
    [subst_morph : fp_prod (map md_ty Γ) → fp_prod (map md_ty Γ')].

    Pointwise: at index [i], the morphism is the interpretation of
    [sub[i]] (which has type [Γ'[i]] in context [Γ]). *)

(** Helper: when we know [List.nth_error Γ' i = Some τ], build the morphism
    interpreting the [i]-th substitute term [sub[i]] at type [τ].
    This is a "single-output-type" form that avoids the dependent
    [eq_rect] over [List.nth_error_map] that the obvious continuation
    needs.  Defined via a clean [match … as … return … with] — the
    match-with-refl trick lets us derive a computation lemma below. *)
Definition subst_at {Th : Theory} {C : Category} {hp : HasFiniteProducts C}
    (D : ModelData Th C hp) (Γ Γ' : list Th.(th_sig).(sg_ty))
    (sub : list (Term Th.(th_sig)))
    (Hsub : Forall2 (HasType Th.(th_sig) Γ) sub Γ')
    (i : nat) (τ : Th.(th_sig).(sg_ty))
    (Hi : List.nth_error Γ' i = Some τ) :
    C⟦fp_prod hp (List.map (md_ty D) Γ), md_ty D τ⟧ :=
  match List.nth_error sub i as o
        return List.nth_error sub i = o ->
               C⟦fp_prod hp (List.map (md_ty D) Γ), md_ty D τ⟧
  with
  | Some t => fun Hsi =>
      interp_term_data D Γ t τ
        (forall2_nth_hastype Hsub i t τ Hsi Hi)
  | None => fun Hsi =>
      False_rect _
        (match Forall2_nth_error_l _ _ _ Hsub i τ Hi with
         | ex_intro _ x (conj Hsi' _) =>
             eq_ind None
               (fun e => match e with Some _ => False | None => True end)
               I (Some x) (eq_ind (List.nth_error sub i)
                                  (fun o => o = Some x) Hsi' None Hsi)
         end)
  end eq_refl.

(** General computation lemma for a [match] with the refl trick.
    Avoids dependent-pattern abstraction issues by isolating the pattern
    in a free-of-dependencies setting. *)
Lemma match_at_some_compute :
    forall {A : Type} {C : Category} (oa : option A) (a : A) (Heq : oa = Some a)
           {X Y : C.(Ob)}
           (f_some : forall a', oa = Some a' -> C⟦X, Y⟧)
           (f_none : oa = None -> C⟦X, Y⟧),
    (match oa as o return oa = o -> C⟦X, Y⟧ with
     | Some a' => fun H => f_some a' H
     | None => fun H => f_none H
     end eq_refl) = f_some a Heq.
Proof.
  intros A C oa a Heq X Y f_some f_none.
  destruct oa as [a'|] eqn:E.
  - inversion Heq. subst.
    cbn. f_equal. apply proof_irrelevance.
  - discriminate.
Qed.

(** [subst_at] computation lemma: when [sub[i] = Some tn] and [Γ'[i] = Some τ],
    the morphism is the interpretation of [tn] at [τ]. *)
Lemma subst_at_compute :
    forall {Th : Theory} {C : Category} {hp : HasFiniteProducts C}
           (D : ModelData Th C hp)
           (Γ Γ' : list Th.(th_sig).(sg_ty))
           (sub : list (Term Th.(th_sig)))
           (Hsub : Forall2 (HasType Th.(th_sig) Γ) sub Γ')
           (n : nat) (τ : Th.(th_sig).(sg_ty))
           (tn : Term Th.(th_sig))
           (Hn : List.nth_error Γ' n = Some τ)
           (Htn_eq : List.nth_error sub n = Some tn)
           (Htn : HasType Th.(th_sig) Γ tn τ),
    subst_at D Γ Γ' sub Hsub n τ Hn = interp_term_data D Γ tn τ Htn.
Proof.
  intros.
  unfold subst_at.
  rewrite (match_at_some_compute (List.nth_error sub n) tn Htn_eq).
  apply (interp_term_data_pi D Γ tn τ).
Qed.

(** [subst_morph]: recursive definition over [sub] using only binary [bp_pair]
    and [interp_term_data].  This formulation has clean [cbn] reduction —
    unlike a [fp_tuple]-based version, which suffers dependent-pattern
    abstraction issues at the [t_var] case of [interp_subst] below. *)
Fixpoint subst_morph {Th : Theory} {C : Category} {hp : HasFiniteProducts C}
    (D : ModelData Th C hp) (Γ : list Th.(th_sig).(sg_ty))
    (sub : list (Term Th.(th_sig)))
    {struct sub}
    : forall (Γ' : list Th.(th_sig).(sg_ty))
             (Hsub : Forall2 (HasType Th.(th_sig) Γ) sub Γ'),
      C⟦fp_prod hp (List.map (md_ty D) Γ),
        fp_prod hp (List.map (md_ty D) Γ')⟧ :=
  match sub with
  | [] =>
      fun Γ' Hsub =>
        match Γ' return Forall2 (HasType Th.(th_sig) Γ) [] Γ' ->
                       C⟦fp_prod hp (List.map (md_ty D) Γ),
                         fp_prod hp (List.map (md_ty D) Γ')⟧ with
        | [] => fun _ =>
            term_arr (projT1 (@fp_terminal C hp))
                     (projT2 (@fp_terminal C hp))
                     (fp_prod hp (List.map (md_ty D) Γ))
        | _ :: _ => fun H => False_rect _ ltac:(inversion H)
        end Hsub
  | s :: ss =>
      fun Γ' Hsub =>
        match Γ' return Forall2 (HasType Th.(th_sig) Γ) (s :: ss) Γ' ->
                       C⟦fp_prod hp (List.map (md_ty D) Γ),
                         fp_prod hp (List.map (md_ty D) Γ')⟧ with
        | [] => fun H => False_rect _ ltac:(inversion H)
        | y :: ys => fun H =>
            let Hxy : HasType Th.(th_sig) Γ s y :=
              ltac:(inversion H; assumption) in
            let Hrest : Forall2 (HasType Th.(th_sig) Γ) ss ys :=
              ltac:(inversion H; assumption) in
            match ys as ys0 return Forall2 (HasType Th.(th_sig) Γ) ss ys0 ->
                                    C⟦fp_prod hp (List.map (md_ty D) Γ),
                                      fp_prod hp (List.map (md_ty D) (y :: ys0))⟧ with
            | [] => fun _ => interp_term_data D Γ s y Hxy
            | y' :: ys' => fun Hr =>
                bp_pair (prod_bp (@fp_binary C hp) (md_ty D y)
                                (fp_prod hp (List.map (md_ty D) (y' :: ys'))))
                  (interp_term_data D Γ s y Hxy)
                  (subst_morph D Γ ss (y' :: ys') Hr)
            end Hrest
        end Hsub
  end.

(** Computation rule for [subst_morph] in the cons-cons case (≥ 2 elements). *)
Lemma subst_morph_cons2 :
    forall {Th : Theory} {C : Category} {hp : HasFiniteProducts C}
           (D : ModelData Th C hp)
           (Γ : list Th.(th_sig).(sg_ty)) (s : Term Th.(th_sig)) (ss : list (Term Th.(th_sig)))
           (y y' : Th.(th_sig).(sg_ty)) (ys' : list Th.(th_sig).(sg_ty))
           (Hsub : Forall2 (HasType Th.(th_sig) Γ) (s :: ss) (y :: y' :: ys'))
           (Hxy : HasType Th.(th_sig) Γ s y)
           (Hrest : Forall2 (HasType Th.(th_sig) Γ) ss (y' :: ys')),
    subst_morph D Γ (s :: ss) (y :: y' :: ys') Hsub =
    bp_pair (prod_bp (@fp_binary C hp) (md_ty D y)
                    (fp_prod hp (List.map (md_ty D) (y' :: ys'))))
      (interp_term_data D Γ s y Hxy)
      (subst_morph D Γ ss (y' :: ys') Hrest).
Proof.
  intros. cbn.
  rewrite (interp_term_data_pi D Γ s y _ Hxy).
  rewrite (proof_irrelevance _ _ Hrest). reflexivity.
Qed.

(** Projection-tuple law for [subst_morph]:
    composing the [n]-th [context_proj] with [subst_morph] yields the
    interpretation of [sub[n]]. *)
Lemma subst_morph_proj :
    forall {Th : Theory} {C : Category} {hp : HasFiniteProducts C}
           (D : ModelData Th C hp)
           (Γ : list Th.(th_sig).(sg_ty))
           (sub : list (Term Th.(th_sig)))
           (Γ' : list Th.(th_sig).(sg_ty))
           (Hsub : Forall2 (HasType Th.(th_sig) Γ) sub Γ')
           (n : nat) (τ : Th.(th_sig).(sg_ty))
           (tn : Term Th.(th_sig))
           (Hn : List.nth_error Γ' n = Some τ)
           (Htn_eq : List.nth_error sub n = Some tn)
           (Htn : HasType Th.(th_sig) Γ tn τ)
           (Hn_map : List.nth_error (List.map (md_ty D) Γ') n = Some (md_ty D τ)),
    context_proj hp n (md_ty D τ) Hn_map ∘ subst_morph D Γ sub Γ' Hsub =
    interp_term_data D Γ tn τ Htn.
Proof.
  intros Th C hp D Γ sub.
  induction sub as [|s ss IH]; intros Γ' Hsub n τ tn Hn Htn_eq Htn Hn_map.
  - destruct n; discriminate Htn_eq.
  - inversion Hsub as [|x y l1' l2' Hxy Hrest Eq1 Eq2]. subst.
    destruct n as [|n].
    + simpl in Htn_eq. injection Htn_eq as Hs_eq.
      simpl in Hn. injection Hn as Hy_eq.
      subst y. subst s.
      destruct l2' as [|y' ys'].
      * cbn -[fp_prod].
        rewrite (proof_irrelevance _ Hn_map eq_refl).
        cbn. rewrite id_left.
        apply (interp_term_data_pi D Γ tn τ).
      * cbn -[fp_prod].
        rewrite (proof_irrelevance _ Hn_map eq_refl).
        cbn. rewrite bp_beta1.
        apply (interp_term_data_pi D Γ tn τ).
    + simpl in Htn_eq. simpl in Hn.
      destruct l2' as [|y' ys'].
      * destruct n; discriminate Hn.
      * assert (Hn_map' : List.nth_error (List.map (md_ty D) (y' :: ys')) n = Some (md_ty D τ)).
        { simpl in Hn_map. exact Hn_map. }
        rewrite (subst_morph_cons2 D Γ s ss y y' ys' Hsub Hxy Hrest).
        cbn -[fp_prod subst_morph].
        rewrite (proof_irrelevance _ Hn_map Hn_map').
        rewrite <- comp_assoc.
        rewrite bp_beta2.
        apply (IH (y' :: ys') Hrest n τ tn Hn Htn_eq Htn Hn_map').
Qed.

(** Composition law for binary pair: [⟨f, g⟩ ∘ m = ⟨f ∘ m, g ∘ m⟩]. *)
Lemma bp_pair_precomp : forall {C : Category} {A B P : C.(Ob)} (bp : IsBinaryProduct A B P)
    {X Y : C.(Ob)} (f : C⟦Y, A⟧) (g : C⟦Y, B⟧) (m : C⟦X, Y⟧),
    bp_pair bp f g ∘ m = bp_pair bp (f ∘ m) (g ∘ m).
Proof.
  intros.
  rewrite (bp_uniq bp (bp_pair bp f g ∘ m)).
  rewrite comp_assoc, bp_beta1.
  rewrite comp_assoc, bp_beta2.
  reflexivity.
Qed.

(** Composition law for [fp_tuple]:
    [fp_tuple objs fs ∘ m = fp_tuple objs (fun i A H => fs i A H ∘ m)]. *)
Lemma fp_tuple_precomp : forall {C : Category} (hp : HasFiniteProducts C)
    {Y X : C.(Ob)} (objs : list C.(Ob))
    (fs : forall i A, List.nth_error objs i = Some A -> C⟦Y, A⟧)
    (m : C⟦X, Y⟧),
    fp_tuple hp objs fs ∘ m = fp_tuple hp objs (fun i A H => fs i A H ∘ m).
Proof.
  intros C hp Y X objs fs m.
  induction objs as [|B Bs IH].
  - cbn.
    pose proof (term_uniq _ (projT2 (fp_terminal C hp)) X
                  (term_arr _ (projT2 (fp_terminal C hp)) Y ∘ m)) as H1.
    rewrite H1. reflexivity.
  - destruct Bs as [|B2 Bs'].
    + cbn. reflexivity.
    + change (fp_tuple hp (B :: B2 :: Bs') fs)
        with (bp_pair (prod_bp (fp_binary C hp) B (fp_prod hp (B2 :: Bs')))
                (fs 0 B eq_refl)
                (fp_tuple hp (B2 :: Bs') (fun i A' H => fs (S i) A' H))).
      change (fp_tuple hp (B :: B2 :: Bs') (fun i A H => fs i A H ∘ m))
        with (bp_pair (prod_bp (fp_binary C hp) B (fp_prod hp (B2 :: Bs')))
                (fs 0 B eq_refl ∘ m)
                (fp_tuple hp (B2 :: Bs') (fun i A' H => fs (S i) A' H ∘ m))).
      rewrite bp_pair_precomp.
      rewrite IH. reflexivity.
Qed.

(** ** Substitution-interpretation lemma — t_var case

    The full [interp_subst] is split into two pieces.  This var case is
    self-contained and clean; the [t_app] case is more involved (see below). *)
Lemma interp_subst_var :
    forall {Th : Theory} {C : Category} {hp : HasFiniteProducts C}
           (D : ModelData Th C hp)
           (Γ Γ' : list Th.(th_sig).(sg_ty))
           (sub : list (Term Th.(th_sig)))
           (Hsub : Forall2 (HasType Th.(th_sig) Γ) sub Γ')
           (n : nat)
           (τ : Th.(th_sig).(sg_ty))
           (Ht : HasType Th.(th_sig) Γ' (t_var n) τ)
           (Hsubt : HasType Th.(th_sig) Γ (subst_term Th.(th_sig) sub (t_var n)) τ),
    interp_term_data D Γ (subst_term Th.(th_sig) sub (t_var n)) τ Hsubt =
    interp_term_data D Γ' (t_var n) τ Ht ∘ subst_morph D Γ sub Γ' Hsub.
Proof.
  intros Th C hp D Γ Γ' sub Hsub n τ Ht Hsubt.
  pose proof (ht_var_nth_err Ht) as Hn.
  destruct (Forall2_nth_error_l _ _ _ Hsub n τ Hn) as [tn [Htn_eq Htn]].
  assert (Hsubst_eq : subst_term Th.(th_sig) sub (t_var n) = tn).
  { rewrite subst_var. rewrite Htn_eq. reflexivity. }
  revert Hsubt. rewrite Hsubst_eq. intro Hsubt.
  rewrite (interp_term_data_pi D Γ tn τ Hsubt Htn).
  assert (Hn_map' : List.nth_error (List.map (md_ty D) Γ') n = Some (md_ty D τ)).
  { rewrite List.nth_error_map. rewrite Hn. reflexivity. }
  rewrite (interp_term_data_var D Γ' n τ Ht Hn_map').
  rewrite (subst_morph_proj D Γ sub Γ' Hsub n τ tn Hn Htn_eq Htn Hn_map'). reflexivity.
Qed.

(** ** Task L.2d — [app_cont] compute lemma + full [interp_subst]

    Resolution of the dependent-pattern blocker that defeated the
    γ-L.2c attempts: rather than attacking [app_cont] directly via
    [destruct] (which fails because the inner match uses [eq_refl]
    proofs of [nth_error … = …]), we prove a "compute" lemma
    [app_cont_some] that reduces [app_cont] to a single
    [eq_rect (md_ty D τi) … (interp_term_data D Γ arg τi …) A HA]
    when both [nth_error (sg_dom f) i] and [nth_error args i] hit
    [Some]-cases.  The proof goes through a 2-argument analogue of
    [match_at_some_compute] ([match_at_some_compute2]) that handles
    the outer match's [eq_refl + parameter] application form.

    With [app_cont_some] in hand, the substitution-composition lemma
    [app_cont_subst_compose] is a straightforward
    [destruct (nth_error (sg_dom f) i)] + [destruct (nth_error args i)]
    + IH application, with no dependent-pattern issues.

    The full [interp_subst] follows by strong (well-founded) induction
    on the term: variable case via [interp_subst_var]; application case
    via [interp_term_data_app_explicit] on both sides + [comp_assoc]
    + [fp_tuple_precomp] + [fp_tuple_ext] + [app_cont_subst_compose]
    (with the IH supplied for each argument). *)

(** Two-argument variant of [match_at_some_compute].  Handles the
    [match … as o return (… = o -> Q o -> R) with … end eq_refl q]
    form that arises in [app_cont]'s outer match. *)
Lemma match_at_some_compute2 :
    forall {A : Type} {R : Type} (oa : option A) (a : A) (Heq : oa = Some a)
           (Q : option A -> Type) (q : Q oa)
           (f_some : forall a', oa = Some a' -> Q (Some a') -> R)
           (f_none : oa = None -> Q None -> R),
    (match oa as o return oa = o -> Q o -> R with
     | Some a' => fun H qo => f_some a' H qo
     | None    => fun H qo => f_none H qo
     end eq_refl q) =
    f_some a Heq (eq_rect oa Q q (Some a) Heq).
Proof.
  intros A R oa a Heq Q q f_some f_none.
  destruct oa as [a'|].
  - injection Heq. intro Ha'. subst a'.
    rewrite (proof_irrelevance _ Heq eq_refl). simpl. reflexivity.
  - discriminate.
Qed.

(** [app_cont] compute lemma: when [nth_error (sg_dom f) i = Some τi]
    and [nth_error args i = Some arg], [app_cont] reduces to
    [eq_rect (md_ty D τi) _ (interp_term_data D Γ arg τi …) A HA].
    The [eq_rect] is identity at the type level: it merely transports
    along the proof [HA : md_ty D τi = A]. *)
Lemma app_cont_some :
    forall {Th : Theory} {C : Category} {hp : HasFiniteProducts C}
           (D : ModelData Th C hp)
           (Γ : list Th.(th_sig).(sg_ty))
           (f : Th.(th_sig).(sg_fun))
           (args : list (Term Th.(th_sig)))
           (Hargs : Forall2 (HasType Th.(th_sig) Γ) args (Th.(th_sig).(sg_dom) f))
           (i : nat) (A : C.(Ob))
           (H : List.nth_error
                  (List.map (md_ty D) (Th.(th_sig).(sg_dom) f)) i = Some A)
           (τi : Th.(th_sig).(sg_ty))
           (Hτi : List.nth_error (Th.(th_sig).(sg_dom) f) i = Some τi)
           (HA : md_ty D τi = A)
           (arg : Term Th.(th_sig))
           (Harg : List.nth_error args i = Some arg)
           (Harg_typ : HasType Th.(th_sig) Γ arg τi),
    app_cont D Γ f args Hargs i A H =
    eq_rect (md_ty D τi)
            (fun A0 => C ⟦ fp_prod hp (List.map (md_ty D) Γ), A0 ⟧)
            (interp_term_data D Γ arg τi Harg_typ) A HA.
Proof.
  intros.
  unfold app_cont.
  rewrite (match_at_some_compute2
             (List.nth_error (Th.(th_sig).(sg_dom) f) i) τi Hτi
             (fun o => option_map (md_ty D) o = Some A)
             (eq_ind (List.nth_error
                        (List.map (md_ty D) (Th.(th_sig).(sg_dom) f)) i)
                (fun o => o = Some A) H
                (option_map (md_ty D) (List.nth_error
                   (Th.(th_sig).(sg_dom) f) i))
                (List.nth_error_map (md_ty D) i (Th.(th_sig).(sg_dom) f)))).
  rewrite (match_at_some_compute (List.nth_error args i) arg Harg).
  rewrite (interp_term_data_pi D Γ arg τi _ Harg_typ).
  rewrite (proof_irrelevance _ _ HA).
  reflexivity.
Qed.

(** Per-component substitution-composition for [app_cont]:
    interpreting the substituted arguments equals interpreting the
    original arguments and then post-composing with [subst_morph].

    Takes an inductive hypothesis [IH] supplying [interp_subst] for
    each argument [arg] of the application; this resolves the
    mutual-recursion structure (terms call into argument lists, which
    contain terms). *)
Lemma app_cont_subst_compose :
    forall {Th : Theory} {C : Category} {hp : HasFiniteProducts C}
           (D : ModelData Th C hp)
           (Γ Γ' : list Th.(th_sig).(sg_ty))
           (sub : list (Term Th.(th_sig)))
           (Hsub : Forall2 (HasType Th.(th_sig) Γ) sub Γ')
           (f : Th.(th_sig).(sg_fun))
           (args : list (Term Th.(th_sig)))
           (Hargs_subst : Forall2 (HasType Th.(th_sig) Γ)
                         (List.map (subst_term Th.(th_sig) sub) args)
                         (Th.(th_sig).(sg_dom) f))
           (Hargs : Forall2 (HasType Th.(th_sig) Γ') args
                            (Th.(th_sig).(sg_dom) f))
           (IH : forall arg, List.In arg args ->
                 forall (τ : Th.(th_sig).(sg_ty))
                   (Harg_typ : HasType Th.(th_sig) Γ' arg τ)
                   (Hsubt : HasType Th.(th_sig) Γ
                              (subst_term Th.(th_sig) sub arg) τ),
                 interp_term_data D Γ (subst_term Th.(th_sig) sub arg) τ Hsubt =
                 interp_term_data D Γ' arg τ Harg_typ
                   ∘ subst_morph D Γ sub Γ' Hsub)
           (i : nat) (A : C.(Ob))
           (H : List.nth_error
                  (List.map (md_ty D) (Th.(th_sig).(sg_dom) f)) i = Some A),
    app_cont D Γ f (List.map (subst_term Th.(th_sig) sub) args)
             Hargs_subst i A H =
    app_cont D Γ' f args Hargs i A H
      ∘ subst_morph D Γ sub Γ' Hsub.
Proof.
  intros Th C hp D Γ Γ' sub Hsub f args Hargs_subst Hargs IH i A H.
  pose proof H as H'.
  rewrite List.nth_error_map in H'.
  destruct (List.nth_error (Th.(th_sig).(sg_dom) f) i) as [τi|] eqn:Hτi;
    [| simpl in H'; discriminate].
  simpl in H'. injection H' as HA.
  destruct (Forall2_nth_error_l _ _ _ Hargs i τi Hτi)
    as [arg [Harg Harg_typ]].
  assert (Harg_subst_typ :
            HasType Th.(th_sig) Γ (subst_term Th.(th_sig) sub arg) τi).
  { apply (forall2_nth_hastype Hargs_subst i
             (subst_term Th.(th_sig) sub arg) τi).
    - rewrite List.nth_error_map, Harg. reflexivity.
    - exact Hτi. }
  rewrite (app_cont_some D Γ f
             (List.map (subst_term Th.(th_sig) sub) args)
             Hargs_subst i A H τi Hτi HA
             (subst_term Th.(th_sig) sub arg)
             (eq_trans (List.nth_error_map _ i args)
                       (f_equal (option_map _) Harg))
             Harg_subst_typ).
  rewrite (app_cont_some D Γ' f args Hargs i A H τi Hτi HA arg Harg Harg_typ).
  destruct HA. simpl.
  apply (IH arg).
  apply (List.nth_error_In _ _ Harg).
Qed.

(** Full substitution-interpretation lemma, by strong induction on the
    term [t].  The variable case is [interp_subst_var]; the application
    case folds [interp_term_data_app_explicit] on both sides, pushes
    the [subst_morph] through [fp_tuple] via [fp_tuple_precomp], then
    closes via [fp_tuple_ext] + [app_cont_subst_compose] (the
    inductive-hypothesis is the strong-induction hypothesis specialised
    to each argument by [att_args_size_lt]). *)
Lemma interp_subst :
    forall {Th : Theory} {C : Category} {hp : HasFiniteProducts C}
           (D : ModelData Th C hp)
           (t : Term Th.(th_sig))
           (Γ Γ' : list Th.(th_sig).(sg_ty))
           (sub : list (Term Th.(th_sig)))
           (Hsub : Forall2 (HasType Th.(th_sig) Γ) sub Γ')
           (τ : Th.(th_sig).(sg_ty))
           (Ht : HasType Th.(th_sig) Γ' t τ)
           (Hsubt : HasType Th.(th_sig) Γ (subst_term Th.(th_sig) sub t) τ),
    interp_term_data D Γ (subst_term Th.(th_sig) sub t) τ Hsubt =
    interp_term_data D Γ' t τ Ht ∘ subst_morph D Γ sub Γ' Hsub.
Proof.
  intros Th C hp D t.
  induction t as [t IH]
    using (well_founded_induction (@att_term_lt_wf Th.(th_sig))).
  intros Γ Γ' sub Hsub τ Ht Hsubt.
  destruct t as [n | f args].
  - (* t_var n *) apply interp_subst_var.
  - (* t_app f args *)
    pose proof (ht_app_cod_eq Ht) as Hcod. subst τ.
    rewrite (interp_term_data_app_explicit D Γ' f args Ht).
    simpl subst_term in Hsubt.
    change (subst_term Th.(th_sig) sub (t_app f args))
      with (t_app f (List.map (subst_term Th.(th_sig) sub) args)).
    rewrite (interp_term_data_app_explicit D Γ f
               (List.map (subst_term Th.(th_sig) sub) args) Hsubt).
    rewrite <- comp_assoc.
    rewrite fp_tuple_precomp.
    f_equal.
    apply fp_tuple_ext.
    intros i A H.
    apply (app_cont_subst_compose D Γ Γ' sub Hsub f args
             (ht_app_args_f2 Hsubt) (ht_app_args_f2 Ht)).
    intros arg Harg_in τ' Harg_typ Hsubt'.
    apply (IH arg).
    apply List.In_nth_error in Harg_in.
    destruct Harg_in as [j Hj].
    apply (att_args_size_lt f args arg j Hj).
Qed.

(** ** Model homomorphism

    A homomorphism of models M → N is a family of morphisms φ_α : [α]_M → [α]_N
    compatible with the interpretations of function symbols. *)

Record ModelHom {Th : Theory} {C : Category} {hp : HasFiniteProducts C}
    (M N : Model Th C hp) : Type := {
  mhom_on_ty : forall (α : Th.(th_sig).(sg_ty)),
                 C⟦ mod_ty M α, mod_ty N α ⟧;
  mhom_nat   : forall (f : Th.(th_sig).(sg_fun)),
                 (* Compatibility: the obvious square commutes. *)
                 True;  (* placeholder *)
}.

Arguments mhom_on_ty {Th C hp M N}.
