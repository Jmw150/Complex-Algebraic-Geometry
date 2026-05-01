(** * ATT/ClassifyingCategory.v
    The classifying category Cl(Th) of an algebraic theory Th.

    Objects:  lists of sorts  [α₁,...,αₙ]
    Morphisms α → β:  lists of terms  [t₁,...,tₘ] where m = length β,
              each tⱼ has sort βⱼ in the canonical context for α,
              and terms are identified by provable equality in Th.

    Here we build the SYNTACTIC category (before quotienting by Th).
    The true classifying category is the setoid quotient by ThEq;
    we note this as Cl_quotient and state soundness/completeness there.

    The syntactic category already satisfies all categorical laws,
    making it a well-defined category. *)

Require Import CAG.ATT.Signature.
Require Import CAG.ATT.Syntax.
Require Import CAG.ATT.Theory.
Require Import CAG.Category.Core.
Require Import CAG.Category.Products.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.PropExtensionality.
From Stdlib Require Import Logic.IndefiniteDescription.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import micromega.Lia.
Import ListNotations.

Set Universe Polymorphism.
Open Scope cat_scope.

(** ** Morphisms of Cl(Th)

    A morphism from α to β is a list of terms typed in context α
    with types given by β. *)

Record ClMor (Sg : Signature) (α β : list Sg.(sg_ty)) : Type := {
  clmor_terms  : list (Term Sg);
  clmor_typed  : Forall2 (HasType Sg α) clmor_terms β;
}.

Arguments clmor_terms {Sg α β}.
Arguments clmor_typed {Sg α β}.

(** Two ClMor values with the same term list are equal (proof irrelevance). *)
Lemma clmor_ext (Sg : Signature) (α β : list Sg.(sg_ty)) (f g : ClMor Sg α β) :
    f.(clmor_terms) = g.(clmor_terms) -> f = g.
Proof.
  intro H.
  destruct f as [tf Hf], g as [tg Hg].
  simpl in H. subst tg.
  f_equal.
  apply proof_irrelevance.
Qed.

(** ** Identity morphism

    id[α] = [x₀:α₀,...,xₙ₋₁:αₙ₋₁] with variables typed by the context itself. *)

(** Typing of variable xᵢ in context α: x_i : α_i when i < length α. *)
Lemma var_typed (Sg : Signature) (α : list Sg.(sg_ty)) (i : nat) (τ : Sg.(sg_ty)) :
    List.nth_error α i = Some τ ->
    HasType Sg α (t_var i) τ.
Proof.
  intro H. exact (ht_var Sg α i τ H).
Qed.

(** Helper: variables [t_var k, ..., t_var (k+|α|-1)] are typed in Γ when
    each nth_error α i = Some τ implies nth_error Γ (k+i) = Some τ. *)
Local Lemma id_vars_typed_aux (Sg : Signature) (Γ : list Sg.(sg_ty)) (k : nat) (α : list Sg.(sg_ty)) :
    (forall i τ, List.nth_error α i = Some τ -> List.nth_error Γ (k + i) = Some τ) ->
    Forall2 (HasType Sg Γ) (List.map t_var (List.seq k (length α))) α.
Proof.
  revert k.
  induction α as [| τ α' IH]; intros k Hnth.
  - simpl. constructor.
  - simpl. constructor.
    + apply ht_var.
      specialize (Hnth 0 τ eq_refl).
      simpl in Hnth. rewrite Nat.add_0_r in Hnth. exact Hnth.
    + apply IH with (k := S k).
      intros i τ' H.
      replace (S k + i) with (k + S i) by lia.
      exact (Hnth (S i) τ' H).
Qed.

(** The identity variable list [t_var 0, ..., t_var (n-1)] is typed by α
    when α has length n. *)
Lemma id_vars_typed (Sg : Signature) (α : list Sg.(sg_ty)) :
    Forall2 (HasType Sg α) (id_sub Sg (length α)) α.
Proof.
  unfold id_sub.
  apply id_vars_typed_aux with (k := 0).
  intros i τ H. simpl. exact H.
Qed.

(** Duplicate of id_vars_typed, kept for compatibility. *)
Lemma id_vars_typed' (Sg : Signature) (α : list Sg.(sg_ty)) :
    Forall2 (HasType Sg α) (id_sub Sg (length α)) α.
Proof.
  exact (id_vars_typed Sg α).
Qed.

(** Direct proof using an auxiliary lemma about shifted variables. *)
Lemma nth_error_shift (Sg : Signature) (α : list Sg.(sg_ty)) (k : nat) :
    Forall2 (HasType Sg α)
            (List.map t_var (List.seq k (length α - k)))
            (List.skipn k α).
Proof.
  rewrite <- List.length_skipn with (n := k).
  apply id_vars_typed_aux with (k := k).
  intros i τ H.
  rewrite <- List.nth_error_skipn.
  exact H.
Qed.

Lemma id_vars_typed_ok (Sg : Signature) (α : list Sg.(sg_ty)) :
    Forall2 (HasType Sg α) (id_sub Sg (length α)) α.
Proof.
  unfold id_sub.
  (* map t_var (seq 0 n) is typed in α = skipn 0 α by the above *)
  assert (H := nth_error_shift Sg α 0).
  rewrite Nat.sub_0_r, List.skipn_O in H.
  exact H.
Qed.

(** The identity morphism. *)
Definition cl_id (Sg : Signature) (α : list Sg.(sg_ty)) : ClMor Sg α α :=
  {| clmor_terms := id_sub Sg (length α);
     clmor_typed := id_vars_typed_ok Sg α; |}.

(** ** Composition

    Given f : α → β (terms ts_f typed in α, types β)
    and   g : β → γ (terms ts_g typed in β, types γ),
    define g ∘ f : α → γ by substituting ts_f into each term of ts_g. *)

Lemma cl_comp_typed (Sg : Signature) (α β γ : list Sg.(sg_ty))
    (f : ClMor Sg α β) (g : ClMor Sg β γ) :
    Forall2 (HasType Sg α)
            (subst_list Sg f.(clmor_terms) g.(clmor_terms))
            γ.
Proof.
  apply subst_preserves_type_list with β.
  - exact f.(clmor_typed).
  - exact g.(clmor_typed).
Qed.

Definition cl_comp (Sg : Signature) (α β γ : list Sg.(sg_ty))
    (g : ClMor Sg β γ) (f : ClMor Sg α β) : ClMor Sg α γ :=
  {| clmor_terms := subst_list Sg f.(clmor_terms) g.(clmor_terms);
     clmor_typed := cl_comp_typed Sg α β γ f g; |}.

(** ** Category laws *)

(** Left identity: id[β] ∘ f = f.
    subst_list (ts_f) (id_sub (length β)) = ts_f
    since id_sub(m) = [x₀,...,x_{m-1}] and subst [x₀,...,x_{m-1}] t = ts_f[i]
    when the i-th element is t_var i.  *)
Lemma cl_id_left (Sg : Signature) (α β : list Sg.(sg_ty)) (f : ClMor Sg α β) :
    cl_comp Sg α β β (cl_id Sg β) f = f.
Proof.
  apply clmor_ext. simpl.
  assert (Hlen : length f.(clmor_terms) = length β).
  { exact (Forall2_length f.(clmor_typed)). }
  rewrite <- Hlen.
  exact (subst_var_list Sg f.(clmor_terms)).
Qed.

(** Right identity: f ∘ id[α] = f.
    subst_list (id_sub (length α)) (ts_f) = ts_f  since subst id = id. *)
Lemma cl_id_right (Sg : Signature) (α β : list Sg.(sg_ty)) (f : ClMor Sg α β) :
    cl_comp Sg α α β f (cl_id Sg α) = f.
Proof.
  apply clmor_ext.
  unfold cl_comp, cl_id. simpl.
  apply subst_id_list.
Qed.

(** Associativity: h ∘ (g ∘ f) = (h ∘ g) ∘ f.
    Both sides equal [subst (subst ts_f ts_g) ts_h],
    which is the content of subst_comp_list. *)
Lemma cl_comp_assoc (Sg : Signature) (α β γ δ : list Sg.(sg_ty))
    (f : ClMor Sg α β) (g : ClMor Sg β γ) (h : ClMor Sg γ δ) :
    cl_comp Sg α γ δ h (cl_comp Sg α β γ g f) =
    cl_comp Sg α β δ (cl_comp Sg β γ δ h g) f.
Proof.
  apply clmor_ext. simpl.
  symmetry.
  eapply (subst_comp_list_wt Sg γ f.(clmor_terms) g.(clmor_terms)).
  - rewrite (Forall2_length g.(clmor_typed)). exact (Nat.le_refl _).
  - exact h.(clmor_typed).
Qed.

(** ** Cl(Th) as a Category *)

(** We wrap the syntactic classifying category as a Rocq [Category] record.
    The objects are [list Sg.(sg_ty)] (type lists).
    The morphisms are [ClMor Sg α β] (well-typed term tuples). *)

Definition ClassifyingCat (Sg : Signature) : Category := {|
  Ob   := list Sg.(sg_ty);
  Hom  := ClMor Sg;
  id   := cl_id Sg;
  comp := fun α β γ g f => cl_comp Sg α β γ g f;
  comp_assoc := fun α β γ δ h g f =>
    cl_comp_assoc Sg α β γ δ f g h;
  id_left  := fun α β f => cl_id_left  Sg α β f;
  id_right := fun α β f => cl_id_right Sg α β f;
|}.

Notation "'Cl' Sg" := (ClassifyingCat Sg) (at level 9) : cat_scope.

(** ** Finite products in Cl(Sg)

    The terminal object is [] (empty list).
    The binary product of α and β is α ++ β. *)

(** *** Terminal object *)

(** There is a unique morphism α → [] for every α:
    the empty list of terms is the unique morphism to the empty target. *)

Lemma cl_terminal_unique (Sg : Signature) (α : list Sg.(sg_ty))
    (f : ClMor Sg α []) :
    f = {| clmor_terms := []; clmor_typed := Forall2_nil _ |}.
Proof.
  apply clmor_ext. simpl.
  destruct f as [ts Hts]. simpl.
  apply Forall2_length in Hts. simpl in Hts.
  symmetry. destruct ts. reflexivity. discriminate Hts.
Qed.

Definition cl_to_nil (Sg : Signature) (α : list Sg.(sg_ty)) : Cl Sg ⟦ α, [] ⟧ :=
  {| clmor_terms := []; clmor_typed := Forall2_nil _ |}.

Definition cl_terminal (Sg : Signature) : @IsTerminal (Cl Sg) [].
Proof.
  apply Build_IsTerminal with (term_arr := cl_to_nil Sg).
  intros α f. exact (cl_terminal_unique Sg α f).
Defined.

(** *** Binary product by list concatenation *)

(** Projection morphisms: the first half of variables go to α, second to β. *)

Lemma cl_proj1_typed (Sg : Signature) (α β : list Sg.(sg_ty)) :
    Forall2 (HasType Sg (α ++ β))
            (id_sub Sg (length α))
            α.
Proof.
  unfold id_sub.
  apply id_vars_typed_aux with (k := 0).
  intros i τ H.
  simpl.
  rewrite List.nth_error_app1.
  - exact H.
  - rewrite <- List.nth_error_Some. rewrite H. discriminate.
Qed.

Lemma cl_proj2_typed (Sg : Signature) (α β : list Sg.(sg_ty)) :
    Forall2 (HasType Sg (α ++ β))
            (List.map t_var (List.seq (length α) (length β)))
            β.
Proof.
  apply id_vars_typed_aux with (k := length α).
  intros i τ H.
  rewrite List.nth_error_app2 by lia.
  replace (length α + i - length α) with i by lia.
  exact H.
Qed.

Definition cl_proj1 (Sg : Signature) (α β : list Sg.(sg_ty)) : Cl Sg ⟦ α ++ β, α ⟧ :=
  {| clmor_terms := id_sub Sg (length α);
     clmor_typed := cl_proj1_typed Sg α β; |}.

Definition cl_proj2 (Sg : Signature) (α β : list Sg.(sg_ty)) : Cl Sg ⟦ α ++ β, β ⟧ :=
  {| clmor_terms := List.map t_var (List.seq (length α) (length β));
     clmor_typed := cl_proj2_typed Sg α β; |}.

(** Pairing: given f : γ → α and g : γ → β, define ⟨f,g⟩ : γ → α++β by
    concatenating the term lists. *)

Lemma cl_pair_typed (Sg : Signature) (γ α β : list Sg.(sg_ty))
    (f : Cl Sg ⟦ γ, α ⟧) (g : Cl Sg ⟦ γ, β ⟧) :
    Forall2 (HasType Sg γ) (f.(clmor_terms) ++ g.(clmor_terms)) (α ++ β).
Proof.
  apply Forall2_app.
  - exact f.(clmor_typed).
  - exact g.(clmor_typed).
Qed.

Definition cl_pair (Sg : Signature) (γ α β : list Sg.(sg_ty))
    (f : Cl Sg ⟦ γ, α ⟧) (g : Cl Sg ⟦ γ, β ⟧) : Cl Sg ⟦ γ, α ++ β ⟧ :=
  {| clmor_terms := f.(clmor_terms) ++ g.(clmor_terms);
     clmor_typed := cl_pair_typed Sg γ α β f g; |}.

(** The binary product satisfies the universal property. *)

Lemma cl_bp_beta1 (Sg : Signature) (γ α β : list Sg.(sg_ty))
    (f : Cl Sg ⟦ γ, α ⟧) (g : Cl Sg ⟦ γ, β ⟧) :
    cl_comp Sg γ (α ++ β) α (cl_proj1 Sg α β) (cl_pair Sg γ α β f g) = f.
Proof.
  apply clmor_ext. simpl.
  assert (Hlen : length f.(clmor_terms) = length α).
  { exact (Forall2_length f.(clmor_typed)). }
  rewrite <- Hlen.
  exact (subst_take Sg f.(clmor_terms) g.(clmor_terms)).
Qed.

Lemma cl_bp_beta2 (Sg : Signature) (γ α β : list Sg.(sg_ty))
    (f : Cl Sg ⟦ γ, α ⟧) (g : Cl Sg ⟦ γ, β ⟧) :
    cl_comp Sg γ (α ++ β) β (cl_proj2 Sg α β) (cl_pair Sg γ α β f g) = g.
Proof.
  apply clmor_ext. simpl.
  assert (Hlen1 : length f.(clmor_terms) = length α).
  { exact (Forall2_length f.(clmor_typed)). }
  assert (Hlen2 : length g.(clmor_terms) = length β).
  { exact (Forall2_length g.(clmor_typed)). }
  rewrite <- Hlen1, <- Hlen2.
  exact (subst_take_right Sg f.(clmor_terms) g.(clmor_terms)).
Qed.

Lemma cl_bp_uniq (Sg : Signature) (γ α β : list Sg.(sg_ty))
    (h : Cl Sg ⟦ γ, α ++ β ⟧) :
    h = cl_pair Sg γ α β
          (cl_comp Sg γ (α ++ β) α (cl_proj1 Sg α β) h)
          (cl_comp Sg γ (α ++ β) β (cl_proj2 Sg α β) h).
Proof.
  apply clmor_ext. simpl.
  set (n := length α). set (m := length β). set (h_ts := h.(clmor_terms)).
  assert (Hlen : length h_ts = n + m).
  { unfold h_ts, n, m.
    rewrite (Forall2_length h.(clmor_typed)), List.length_app. lia. }
  (* LHS: h_ts.  RHS: subst_list h_ts (id_sub n) ++ subst_list h_ts (map t_var (seq n m)) *)
  (* Prove by pointwise equality *)
  apply List.nth_error_ext. intro i.
  (* Length of first part: |id_sub n| = n *)
  assert (Hfst_len : length (subst_list Sg h_ts (id_sub Sg n)) = n).
  { unfold subst_list, id_sub.
    rewrite List.length_map, List.length_map, List.length_seq. reflexivity. }
  rewrite List.nth_error_app, Hfst_len.
  destruct (i <? n) eqn:Hi.
  - (* i < n: LHS and first-part both give h_ts[i] *)
    unfold subst_list. rewrite List.nth_error_map, nth_error_id_sub, Hi.
    simpl.
    apply Nat.ltb_lt in Hi.
    destruct (List.nth_error h_ts i) eqn:Hni.
    + reflexivity.
    + apply List.nth_error_None in Hni. lia.
  - (* i >= n: LHS gives h_ts[i], second part gives h_ts[n + (i-n)] = h_ts[i] *)
    apply Nat.ltb_ge in Hi.
    unfold subst_list. rewrite List.nth_error_map.
    rewrite List.nth_error_map, nth_error_seq.
    destruct ((i - n) <? m) eqn:Hj.
    + apply Nat.ltb_lt in Hj. simpl.
      replace (n + (i - n)) with i by lia.
      destruct (List.nth_error h_ts i) eqn:Hni.
      * reflexivity.
      * apply List.nth_error_None in Hni. lia.
    + apply Nat.ltb_ge in Hj. simpl.
      apply List.nth_error_None. lia.
Qed.

Definition cl_binary_product (Sg : Signature) (α β : list Sg.(sg_ty)) :
    @IsBinaryProduct (Cl Sg) α β (α ++ β).
Proof.
  apply Build_IsBinaryProduct with
    (bp_proj1 := cl_proj1 Sg α β)
    (bp_proj2 := cl_proj2 Sg α β)
    (bp_pair  := fun γ f g => cl_pair Sg γ α β f g).
  - intros γ f g. exact (cl_bp_beta1 Sg γ α β f g).
  - intros γ f g. exact (cl_bp_beta2 Sg γ α β f g).
  - intros γ h.   exact (cl_bp_uniq  Sg γ α β h).
Defined.

(** ** Cl(Sg) has finite products *)

Definition cl_has_binary_products (Sg : Signature) : HasBinaryProducts (Cl Sg).
Proof.
  apply Build_HasBinaryProducts with (prod_obj := fun α β : list Sg.(sg_ty) => α ++ β).
  exact (cl_binary_product Sg).
Defined.

Definition cl_finite_products (Sg : Signature) : HasFiniteProducts (Cl Sg).
Proof.
  refine {|
    fp_terminal := existT (fun T => @IsTerminal (Cl Sg) T) [] (cl_terminal Sg);
    fp_binary   := cl_has_binary_products Sg;
  |}.
Defined.

(** ** Morphism equality modulo theory

    Two morphisms f, g : α → β are Th-equal if each corresponding
    term is provably equal in Th. *)

Definition ClMor_eq (Th : Theory) (α β : list Th.(th_sig).(sg_ty))
    (f g : ClMor Th.(th_sig) α β) : Prop :=
  Forall2 (fun t1 t2 => forall τ,
      List.In (t1, t2, τ) (List.combine (List.combine f.(clmor_terms) g.(clmor_terms))
                                          β) ->
      ThEq Th.(th_sig) Th.(th_ax) α t1 t2 τ)
    f.(clmor_terms) g.(clmor_terms).

(** Simpler: component-wise provable equality. *)
Definition ClMor_theq (Th : Theory) (α β : list Th.(th_sig).(sg_ty))
    (f g : ClMor Th.(th_sig) α β) : Prop :=
  forall i t1 t2 τ,
    List.nth_error f.(clmor_terms) i = Some t1 ->
    List.nth_error g.(clmor_terms) i = Some t2 ->
    List.nth_error β i = Some τ ->
    ThEq Th.(th_sig) Th.(th_ax) α t1 t2 τ.

(** The TRUE classifying category Cl(Th) is the quotient of the syntactic
    category by [ClMor_theq].  Earlier versions of this file left the
    quotient construction as a remark; Task L.1 (this section) builds the
    quotient explicitly, mirroring the AxTheory/ClassifyingCategory.v
    pattern (Tasks A.1 + A.1b).

    The quotient uses sigma-of-equivalence-class predicates with
    propositional + functional extensionality and proof irrelevance to
    identify equivalent classes.  The only project-internal axioms
    relied on are:
    - [proof_irrelevance] (Stdlib)
    - [functional_extensionality] / [propositional_extensionality]
      (Stdlib)
    plus the structural congruence lemma [theq_subst_cong] proved
    BELOW (no new project axiom). *)

(* ================================================================== *)
(** ** Substitution congruence for ThEq

    To build the quotient, we need: provable equality is preserved by
    substitution, both in the term being substituted and in the
    substitution itself.

    These are PROVED here by structural induction (no new axioms);
    they parallel AxTheory's [ax_subst_cong] (which is axiomatised
    there because AxTerm carries lambda binders that complicate the
    formal induction; ATT terms are first-order so the induction goes
    through directly). *)
(* ================================================================== *)

(** Helper: [ThEq] under a fixed substitution applied to both sides.

    By induction on the [ThEq] derivation, with the [theq_cong] case
    handled by structural recursion on the inner [Forall2]. *)
Lemma theq_subst (Sg : Signature) (ax : list (TheoryAxiom Sg))
    (Γ Γ' : list Sg.(sg_ty))
    (sub : list (Term Sg))
    (Hsub : Forall2 (HasType Sg Γ) sub Γ') :
    forall (M M' : Term Sg) (τ : Sg.(sg_ty)),
      ThEq Sg ax Γ' M M' τ ->
      ThEq Sg ax Γ (subst_term Sg sub M) (subst_term Sg sub M') τ.
Proof.
  fix IH 4. intros M M' τ HM.
  destruct HM as
    [t τ Ht
    | t1 t2 τ HM
    | t1 t2 t3 τ H12 H23
    | f args1 args2 Hargs
    | a sub_a Hin Htyp_sub_a].
  - (* theq_refl *)
    apply theq_refl.
    exact (subst_preserves_type Sg Γ Γ' sub Hsub t τ Ht).
  - (* theq_sym *)
    apply theq_sym. exact (IH _ _ _ HM).
  - (* theq_trans *)
    apply theq_trans with (subst_term Sg sub t2).
    + exact (IH _ _ _ H12).
    + exact (IH _ _ _ H23).
  - (* theq_cong : t_app f args1 ~~ t_app f args2 *)
    simpl.
    apply theq_cong.
    (* Need: Forall2 (fun a1 a2 => exists τ, ThEq ax Γ a1 a2 τ)
              (map (subst sub) args1) (map (subst sub) args2). *)
    induction Hargs as [| a1 a2 args1' args2' Ha12 Hrest IHargs].
    + constructor.
    + simpl. constructor.
      * destruct Ha12 as [τ' HτEq].
        exists τ'. exact (IH _ _ _ HτEq).
      * exact IHargs.
  - (* theq_ax : we have HasType-typed substitution sub_a in Γ',
       so subst_term sub (subst_term sub_a a.lhs) =
       subst_term (subst_list sub sub_a) a.lhs (by subst_comp_term_wt). *)
    assert (Hlen : length a.(ax_ctx) <= length sub_a).
    { rewrite (Forall2_length Htyp_sub_a). exact (Nat.le_refl _). }
    rewrite (subst_comp_term_wt Sg a.(ax_ctx) sub sub_a Hlen
                                a.(ax_lhs) a.(ax_sort) a.(ax_lhs_typed)).
    rewrite (subst_comp_term_wt Sg a.(ax_ctx) sub sub_a Hlen
                                a.(ax_rhs) a.(ax_sort) a.(ax_rhs_typed)).
    apply theq_ax.
    + exact Hin.
    + exact (subst_preserves_type_list Sg Γ Γ' sub Hsub sub_a a.(ax_ctx) Htyp_sub_a).
Qed.

(** Helper: pointwise-[ThEq] substitutions agree on any well-typed term.

    By induction on the [HasType] derivation. *)
Lemma subst_pointwise_theq (Sg : Signature) (ax : list (TheoryAxiom Sg))
    (Γ Γ' : list Sg.(sg_ty))
    (sub sub' : list (Term Sg))
    (Hsub  : Forall2 (HasType Sg Γ) sub  Γ')
    (Hsub' : Forall2 (HasType Sg Γ) sub' Γ')
    (Hpw : forall i τ_i s s',
        List.nth_error Γ'  i = Some τ_i ->
        List.nth_error sub  i = Some s ->
        List.nth_error sub' i = Some s' ->
        ThEq Sg ax Γ s s' τ_i) :
    forall (t : Term Sg) (τ : Sg.(sg_ty)),
      HasType Sg Γ' t τ ->
      ThEq Sg ax Γ (subst_term Sg sub t) (subst_term Sg sub' t) τ.
Proof.
  fix IH 3. intros t τ Ht.
  destruct Ht as [n τ Hn | f args Hargs].
  - (* t_var n: lookup in sub vs sub' *)
    simpl.
    destruct (Forall2_nth_error_l _ _ _ Hsub  n τ Hn) as [s  [Hs  Hts ]].
    destruct (Forall2_nth_error_l _ _ _ Hsub' n τ Hn) as [s' [Hs' Hts']].
    rewrite Hs, Hs'.
    exact (Hpw n τ s s' Hn Hs Hs').
  - (* t_app f args *)
    simpl.
    apply theq_cong.
    induction Hargs as [| a τ' args' dom' Ha Hrest IHargs].
    + constructor.
    + simpl. constructor.
      * exists τ'. exact (IH a τ' Ha).
      * exact IHargs.
Qed.

(** Combined congruence: sub ~~ sub' AND M ~~ M' both lift through.

    The auxiliary [HM'_typed] hypothesis asserts well-typedness of M'
    in Γ'; this is always available in our use case (composition of
    well-typed morphisms in the classifying category).  Decomposes via
    [theq_subst] (sub fixed) + [subst_pointwise_theq] (M' fixed). *)
Lemma theq_subst_cong (Sg : Signature) (ax : list (TheoryAxiom Sg))
    (Γ Γ' : list Sg.(sg_ty))
    (sub sub' : list (Term Sg))
    (M M' : Term Sg) (τ : Sg.(sg_ty))
    (Hsub  : Forall2 (HasType Sg Γ) sub  Γ')
    (Hsub' : Forall2 (HasType Sg Γ) sub' Γ')
    (Hpw : forall i τ_i s s',
        List.nth_error Γ'  i = Some τ_i ->
        List.nth_error sub  i = Some s ->
        List.nth_error sub' i = Some s' ->
        ThEq Sg ax Γ s s' τ_i)
    (HM'_typed : HasType Sg Γ' M' τ)
    (HM : ThEq Sg ax Γ' M M' τ) :
    ThEq Sg ax Γ (subst_term Sg sub M) (subst_term Sg sub' M') τ.
Proof.
  (* Use transitivity:
       subst sub M ~~ subst sub M' ~~ subst sub' M'. *)
  apply theq_trans with (subst_term Sg sub M').
  - exact (theq_subst Sg ax Γ Γ' sub Hsub M M' τ HM).
  - exact (subst_pointwise_theq Sg ax Γ Γ' sub sub' Hsub Hsub' Hpw M' τ HM'_typed).
Qed.

(* ================================================================== *)
(** ** Equivalence-relation properties of [ClMor_theq] *)
(* ================================================================== *)

Lemma ClMor_theq_refl (Th : Theory) (α β : list Th.(th_sig).(sg_ty))
    (f : ClMor Th.(th_sig) α β) :
    ClMor_theq Th α β f f.
Proof.
  unfold ClMor_theq. intros i t1 t2 τ H1 H2 Hβ.
  rewrite H1 in H2. injection H2 as <-.
  apply theq_refl.
  (* Need: HasType α t1 τ.  Use clmor_typed: Forall2 (HasType α) f.terms β. *)
  destruct (Forall2_nth_error_l _ _ _ f.(clmor_typed) i τ Hβ) as [t' [Ht'_pos Ht'_typed]].
  rewrite H1 in Ht'_pos. injection Ht'_pos as <-. exact Ht'_typed.
Qed.

Lemma ClMor_theq_sym (Th : Theory) (α β : list Th.(th_sig).(sg_ty))
    (f g : ClMor Th.(th_sig) α β) :
    ClMor_theq Th α β f g -> ClMor_theq Th α β g f.
Proof.
  unfold ClMor_theq. intros H i t1 t2 τ H1 H2 Hβ.
  apply theq_sym. exact (H i t2 t1 τ H2 H1 Hβ).
Qed.

Lemma ClMor_theq_trans (Th : Theory) (α β : list Th.(th_sig).(sg_ty))
    (f g h : ClMor Th.(th_sig) α β) :
    ClMor_theq Th α β f g -> ClMor_theq Th α β g h ->
    ClMor_theq Th α β f h.
Proof.
  unfold ClMor_theq. intros H1 H2 i t1 t2 τ Hf Hh Hβ.
  (* g may have a term at position i; extract it via Forall2_nth_error_l. *)
  destruct (Forall2_nth_error_l _ _ _ g.(clmor_typed) i τ Hβ) as [tg [Hg_pos Hg_typed]].
  apply theq_trans with tg.
  - exact (H1 i t1 tg τ Hf Hg_pos Hβ).
  - exact (H2 i tg t2 τ Hg_pos Hh Hβ).
Qed.

(* ================================================================== *)
(** ** Sigma-of-equivalence-class quotient (Quotients.v / A.1 pattern) *)
(* ================================================================== *)

(** The equivalence class of a representative as a predicate. *)
Definition ClMor_theq_class_of {Th : Theory} {α β : list Th.(th_sig).(sg_ty)}
    (m : ClMor Th.(th_sig) α β) : ClMor Th.(th_sig) α β -> Prop :=
  fun m' => ClMor_theq Th α β m m'.

(** Quotient morphisms: predicates that are representable as some class. *)
Definition ClMor_q (Th : Theory) (α β : list Th.(th_sig).(sg_ty)) : Type :=
  { S : ClMor Th.(th_sig) α β -> Prop | exists m, S = ClMor_theq_class_of m }.

(** Constructing a quotient morphism from a representative. *)
Definition clth_mk_q {Th : Theory} {α β : list Th.(th_sig).(sg_ty)}
    (m : ClMor Th.(th_sig) α β) : ClMor_q Th α β :=
  exist _ (ClMor_theq_class_of m) (ex_intro _ m eq_refl).

Lemma clth_class_of_eq_iff (Th : Theory) (α β : list Th.(th_sig).(sg_ty))
    (m m' : ClMor Th.(th_sig) α β) :
    ClMor_theq_class_of m = ClMor_theq_class_of m' <-> ClMor_theq Th α β m m'.
Proof.
  unfold ClMor_theq_class_of. split.
  - intro Heq.
    assert (Hself : (fun m'0 : ClMor Th.(th_sig) α β => ClMor_theq Th α β m' m'0) m').
    { apply ClMor_theq_refl. }
    rewrite <- Heq in Hself.
    exact Hself.
  - intro Hmm'.
    apply functional_extensionality. intro x.
    apply propositional_extensionality. split.
    + intro Hmx. apply (ClMor_theq_trans Th α β m' m x).
      * apply ClMor_theq_sym. exact Hmm'.
      * exact Hmx.
    + intro Hm'x. apply (ClMor_theq_trans Th α β m m' x); assumption.
Qed.

Lemma clth_mk_q_eq_iff (Th : Theory) (α β : list Th.(th_sig).(sg_ty))
    (m m' : ClMor Th.(th_sig) α β) :
    clth_mk_q m = clth_mk_q m' <-> ClMor_theq Th α β m m'.
Proof.
  split.
  - intro Heq.
    assert (Hpred : ClMor_theq_class_of m = ClMor_theq_class_of m').
    { apply (f_equal (@proj1_sig _ _)) in Heq. exact Heq. }
    apply clth_class_of_eq_iff. exact Hpred.
  - intro Hmm'.
    assert (Hpred : ClMor_theq_class_of m = ClMor_theq_class_of m').
    { apply clth_class_of_eq_iff. exact Hmm'. }
    unfold clth_mk_q.
    apply eq_sig_uncurried. simpl.
    exists Hpred. apply proof_irrelevance.
Qed.

Lemma clth_mk_q_surj (Th : Theory) (α β : list Th.(th_sig).(sg_ty))
    (q : ClMor_q Th α β) :
    exists m : ClMor Th.(th_sig) α β, clth_mk_q m = q.
Proof.
  destruct q as [S [m Hm]]. exists m.
  unfold clth_mk_q.
  apply eq_sig_uncurried. simpl.
  exists (eq_sym Hm). apply proof_irrelevance.
Qed.

Lemma ClMor_q_eq (Th : Theory) (α β : list Th.(th_sig).(sg_ty))
    (q1 q2 : ClMor_q Th α β) :
    proj1_sig q1 = proj1_sig q2 -> q1 = q2.
Proof.
  intro H. destruct q1 as [S1 H1], q2 as [S2 H2]. simpl in H.
  apply eq_sig_uncurried. simpl. exists H. apply proof_irrelevance.
Qed.

(* ================================================================== *)
(** ** Operations on the quotient *)
(* ================================================================== *)

Definition clth_id (Th : Theory) (α : list Th.(th_sig).(sg_ty)) :
    ClMor_q Th α α :=
  clth_mk_q (cl_id Th.(th_sig) α).

(** Composition is well-defined modulo [ClMor_theq] via [theq_subst_cong]. *)
Lemma clth_comp_well_defined (Th : Theory) (α β γ : list Th.(th_sig).(sg_ty))
    (g1 g2 : ClMor Th.(th_sig) β γ) (f1 f2 : ClMor Th.(th_sig) α β) :
    ClMor_theq Th β γ g1 g2 ->
    ClMor_theq Th α β f1 f2 ->
    ClMor_theq Th α γ
      (cl_comp Th.(th_sig) α β γ g1 f1)
      (cl_comp Th.(th_sig) α β γ g2 f2).
Proof.
  unfold ClMor_theq, cl_comp. simpl. intros Hg Hf i t1 t2 τ H1 H2 Hγ.
  unfold subst_list in H1, H2.
  rewrite List.nth_error_map in H1, H2.
  destruct (List.nth_error g1.(clmor_terms) i) as [g1i|] eqn:Hg1i;
    [|discriminate].
  destruct (List.nth_error g2.(clmor_terms) i) as [g2i|] eqn:Hg2i;
    [|discriminate].
  simpl in H1, H2.
  injection H1 as <-. injection H2 as <-.
  (* Goal: ThEq α (subst f1.terms g1i) (subst f2.terms g2i) τ. *)
  (* Apply theq_subst_cong with sub=f1.terms, sub'=f2.terms,
     M=g1i, M'=g2i, Γ=α, Γ'=β. *)
  (* Need: typing of g2i in β at sort τ. *)
  destruct (Forall2_nth_error_l _ _ _ g2.(clmor_typed) i τ Hγ)
    as [g2i' [Hg2i' Hg2i_typed]].
  rewrite Hg2i in Hg2i'. injection Hg2i' as <-.
  apply (theq_subst_cong Th.(th_sig) Th.(th_ax) α β
           f1.(clmor_terms) f2.(clmor_terms)
           g1i g2i τ
           f1.(clmor_typed) f2.(clmor_typed)).
  - (* pointwise ThEq on f1, f2 substitutions *)
    intros j τ_j s s' Hβj Hf1j Hf2j.
    exact (Hf j s s' τ_j Hf1j Hf2j Hβj).
  - exact Hg2i_typed.
  - exact (Hg i g1i g2i τ Hg1i Hg2i Hγ).
Qed.

(** Composition on quotient morphisms: build the predicate
    [exists representatives g0, f0 in the input classes whose
    representative-level composition is in this class]. *)
Definition clth_comp (Th : Theory) (α β γ : list Th.(th_sig).(sg_ty))
    (g : ClMor_q Th β γ) (f : ClMor_q Th α β) : ClMor_q Th α γ.
Proof.
  refine (exist _
            (fun h => exists g0 f0,
                proj1_sig g g0 /\ proj1_sig f f0 /\
                ClMor_theq Th α γ (cl_comp Th.(th_sig) α β γ g0 f0) h)
            _).
  destruct g as [Sg' [g0 Hg]]; destruct f as [Sf [f0 Hf]]; simpl.
  exists (cl_comp Th.(th_sig) α β γ g0 f0).
  apply functional_extensionality. intro x.
  apply propositional_extensionality. split.
  - intros [g1 [f1 [Hg1 [Hf1 Hcomp]]]].
    rewrite Hg in Hg1. rewrite Hf in Hf1.
    unfold ClMor_theq_class_of in Hg1, Hf1.
    apply (ClMor_theq_trans Th α γ
              (cl_comp Th.(th_sig) α β γ g0 f0)
              (cl_comp Th.(th_sig) α β γ g1 f1) x).
    + apply clth_comp_well_defined; assumption.
    + exact Hcomp.
  - intro Hx.
    exists g0, f0.
    rewrite Hg, Hf. unfold ClMor_theq_class_of.
    repeat split.
    + apply ClMor_theq_refl.
    + apply ClMor_theq_refl.
    + exact Hx.
Defined.

(** Computational lemma for composition. *)
Lemma clth_comp_mk (Th : Theory) (α β γ : list Th.(th_sig).(sg_ty))
    (g : ClMor Th.(th_sig) β γ) (f : ClMor Th.(th_sig) α β) :
    clth_comp Th α β γ (clth_mk_q g) (clth_mk_q f) =
    clth_mk_q (cl_comp Th.(th_sig) α β γ g f).
Proof.
  apply ClMor_q_eq. simpl.
  apply functional_extensionality. intro x.
  apply propositional_extensionality. split.
  - intros [g0 [f0 [Hg0 [Hf0 Hcomp]]]].
    unfold ClMor_theq_class_of in Hg0, Hf0.
    apply (ClMor_theq_trans Th α γ
             (cl_comp Th.(th_sig) α β γ g f)
             (cl_comp Th.(th_sig) α β γ g0 f0) x).
    + apply clth_comp_well_defined; assumption.
    + exact Hcomp.
  - intro Hx.
    exists g, f. unfold ClMor_theq_class_of. repeat split.
    + apply ClMor_theq_refl.
    + apply ClMor_theq_refl.
    + exact Hx.
Qed.

(* ================================================================== *)
(** ** Category laws on the quotient *)
(* ================================================================== *)

Lemma clth_id_left (Th : Theory) (α β : list Th.(th_sig).(sg_ty))
    (f : ClMor_q Th α β) :
    clth_comp Th α β β (clth_id Th β) f = f.
Proof.
  destruct (clth_mk_q_surj Th α β f) as [f0 Hf]. subst f.
  unfold clth_id. rewrite clth_comp_mk.
  apply clth_mk_q_eq_iff.
  rewrite cl_id_left. apply ClMor_theq_refl.
Qed.

Lemma clth_id_right (Th : Theory) (α β : list Th.(th_sig).(sg_ty))
    (f : ClMor_q Th α β) :
    clth_comp Th α α β f (clth_id Th α) = f.
Proof.
  destruct (clth_mk_q_surj Th α β f) as [f0 Hf]. subst f.
  unfold clth_id. rewrite clth_comp_mk.
  apply clth_mk_q_eq_iff.
  rewrite cl_id_right. apply ClMor_theq_refl.
Qed.

Lemma clth_comp_assoc (Th : Theory) (α β γ δ : list Th.(th_sig).(sg_ty))
    (f : ClMor_q Th α β) (g : ClMor_q Th β γ) (h : ClMor_q Th γ δ) :
    clth_comp Th α γ δ h (clth_comp Th α β γ g f) =
    clth_comp Th α β δ (clth_comp Th β γ δ h g) f.
Proof.
  destruct (clth_mk_q_surj Th α β f) as [f0 Hf]. subst f.
  destruct (clth_mk_q_surj Th β γ g) as [g0 Hg]. subst g.
  destruct (clth_mk_q_surj Th γ δ h) as [h0 Hh]. subst h.
  rewrite !clth_comp_mk.
  apply clth_mk_q_eq_iff.
  rewrite (cl_comp_assoc Th.(th_sig) α β γ δ f0 g0 h0).
  apply ClMor_theq_refl.
Qed.

(* ================================================================== *)
(** ** The classifying category Cl(Th) as a Category *)
(* ================================================================== *)

Definition ClassifyingThCat (Th : Theory) : Category := {|
  Ob   := list Th.(th_sig).(sg_ty);
  Hom  := ClMor_q Th;
  id   := clth_id Th;
  comp := fun α β γ g f => clth_comp Th α β γ g f;
  comp_assoc := fun α β γ δ h g f => clth_comp_assoc Th α β γ δ f g h;
  id_left  := fun α β f => clth_id_left  Th α β f;
  id_right := fun α β f => clth_id_right Th α β f;
|}.

(** Notation for the quotient classifying category.  We use [ClTh] to
    avoid colliding with the existing [Cl Sg] notation for the
    syntactic category on a Signature. *)
Notation "'ClTh' Th" := (ClassifyingThCat Th) (at level 9) : cat_scope.

(* ================================================================== *)
(** ** Finite products on the quotient [ClTh Th]                       *)
(*                                                                     *)
(*  We lift the terminal object and binary products from [Cl Sg] to    *)
(*  [ClTh Th] through the quotient map [clth_mk_q].  Universal         *)
(*  properties transport via [clth_mk_q_eq_iff].                       *)
(* ================================================================== *)

(** Helper: composition reduces on representatives. *)

(** *** Terminal object in [ClTh Th]. *)
Definition clth_to_nil (Th : Theory) (α : list Th.(th_sig).(sg_ty)) :
    ClTh Th ⟦ α, [] ⟧ :=
  clth_mk_q (cl_to_nil Th.(th_sig) α).

Lemma clth_terminal_unique (Th : Theory) (α : list Th.(th_sig).(sg_ty))
    (f : ClTh Th ⟦ α, [] ⟧) :
    f = clth_to_nil Th α.
Proof.
  destruct (clth_mk_q_surj Th α [] f) as [f0 Hf]. subst f.
  unfold clth_to_nil.
  apply clth_mk_q_eq_iff.
  rewrite (cl_terminal_unique Th.(th_sig) α f0).
  apply ClMor_theq_refl.
Qed.

Definition clth_terminal (Th : Theory) : @IsTerminal (ClTh Th) [].
Proof.
  apply Build_IsTerminal with (term_arr := clth_to_nil Th).
  intros α f. apply clth_terminal_unique.
Defined.

(** *** Binary product on [ClTh Th]:  α ×^q β  := α ++ β. *)
Definition clth_proj1 (Th : Theory) (α β : list Th.(th_sig).(sg_ty)) :
    ClTh Th ⟦ α ++ β, α ⟧ :=
  clth_mk_q (cl_proj1 Th.(th_sig) α β).

Definition clth_proj2 (Th : Theory) (α β : list Th.(th_sig).(sg_ty)) :
    ClTh Th ⟦ α ++ β, β ⟧ :=
  clth_mk_q (cl_proj2 Th.(th_sig) α β).

(** [clth_pair] uses the existence of representatives via [proj1_sig] of
    the [exists]-witness packaged inside [ClMor_q].  We extract a witness
    by indefinite description (an axiom already used elsewhere in the
    project, e.g. ClassifyingEquivalence.v:Ap_G_inv_map). *)
Definition clth_pair (Th : Theory) (γ α β : list Th.(th_sig).(sg_ty))
    (f : ClTh Th ⟦ γ, α ⟧) (g : ClTh Th ⟦ γ, β ⟧) :
    ClTh Th ⟦ γ, α ++ β ⟧.
Proof.
  destruct (constructive_indefinite_description _
              (clth_mk_q_surj Th γ α f)) as [f0 _].
  destruct (constructive_indefinite_description _
              (clth_mk_q_surj Th γ β g)) as [g0 _].
  exact (clth_mk_q (cl_pair Th.(th_sig) γ α β f0 g0)).
Defined.

(** Pairing is well-defined modulo [ClMor_theq] on each input. *)
Lemma cl_pair_well_defined (Th : Theory) (γ α β : list Th.(th_sig).(sg_ty))
    (f1 f2 : ClMor Th.(th_sig) γ α) (g1 g2 : ClMor Th.(th_sig) γ β) :
    ClMor_theq Th γ α f1 f2 ->
    ClMor_theq Th γ β g1 g2 ->
    ClMor_theq Th γ (α ++ β)
      (cl_pair Th.(th_sig) γ α β f1 g1)
      (cl_pair Th.(th_sig) γ α β f2 g2).
Proof.
  unfold ClMor_theq, cl_pair. simpl.
  intros Hf Hg i t1 t2 τ H1 H2 Hβ.
  assert (Hlen_f1 : length f1.(clmor_terms) = length α).
  { exact (Forall2_length f1.(clmor_typed)). }
  assert (Hlen_f2 : length f2.(clmor_terms) = length α).
  { exact (Forall2_length f2.(clmor_typed)). }
  rewrite List.nth_error_app in H1, H2, Hβ.
  rewrite Hlen_f1 in H1.
  rewrite Hlen_f2 in H2.
  destruct (i <? length α) eqn:Hi.
  - apply (Hf i t1 t2 τ H1 H2 Hβ).
  - apply (Hg (i - length α) t1 t2 τ H1 H2 Hβ).
Qed.

(** Pairing on representatives reduces. *)
Lemma clth_pair_mk (Th : Theory) (γ α β : list Th.(th_sig).(sg_ty))
    (f : ClMor Th.(th_sig) γ α) (g : ClMor Th.(th_sig) γ β) :
    clth_pair Th γ α β (clth_mk_q f) (clth_mk_q g) =
    clth_mk_q (cl_pair Th.(th_sig) γ α β f g).
Proof.
  unfold clth_pair.
  destruct (constructive_indefinite_description _
              (clth_mk_q_surj Th γ α (clth_mk_q f))) as [f' Hf].
  destruct (constructive_indefinite_description _
              (clth_mk_q_surj Th γ β (clth_mk_q g))) as [g' Hg].
  apply clth_mk_q_eq_iff in Hf.
  apply clth_mk_q_eq_iff in Hg.
  apply clth_mk_q_eq_iff.
  apply cl_pair_well_defined; assumption.
Qed.

Lemma clth_bp_beta1 (Th : Theory) (γ α β : list Th.(th_sig).(sg_ty))
    (f : ClTh Th ⟦ γ, α ⟧) (g : ClTh Th ⟦ γ, β ⟧) :
    clth_comp Th γ (α ++ β) α (clth_proj1 Th α β) (clth_pair Th γ α β f g) = f.
Proof.
  destruct (clth_mk_q_surj Th γ α f) as [f0 Hf]. subst f.
  destruct (clth_mk_q_surj Th γ β g) as [g0 Hg]. subst g.
  unfold clth_proj1.
  rewrite clth_pair_mk.
  rewrite clth_comp_mk.
  apply clth_mk_q_eq_iff.
  rewrite (cl_bp_beta1 Th.(th_sig) γ α β f0 g0).
  apply ClMor_theq_refl.
Qed.

Lemma clth_bp_beta2 (Th : Theory) (γ α β : list Th.(th_sig).(sg_ty))
    (f : ClTh Th ⟦ γ, α ⟧) (g : ClTh Th ⟦ γ, β ⟧) :
    clth_comp Th γ (α ++ β) β (clth_proj2 Th α β) (clth_pair Th γ α β f g) = g.
Proof.
  destruct (clth_mk_q_surj Th γ α f) as [f0 Hf]. subst f.
  destruct (clth_mk_q_surj Th γ β g) as [g0 Hg]. subst g.
  unfold clth_proj2.
  rewrite clth_pair_mk.
  rewrite clth_comp_mk.
  apply clth_mk_q_eq_iff.
  rewrite (cl_bp_beta2 Th.(th_sig) γ α β f0 g0).
  apply ClMor_theq_refl.
Qed.

Lemma clth_bp_uniq (Th : Theory) (γ α β : list Th.(th_sig).(sg_ty))
    (h : ClTh Th ⟦ γ, α ++ β ⟧) :
    h = clth_pair Th γ α β
          (clth_comp Th γ (α ++ β) α (clth_proj1 Th α β) h)
          (clth_comp Th γ (α ++ β) β (clth_proj2 Th α β) h).
Proof.
  destruct (clth_mk_q_surj Th γ (α ++ β) h) as [h0 Hh]. subst h.
  unfold clth_proj1, clth_proj2.
  rewrite !clth_comp_mk.
  rewrite clth_pair_mk.
  apply clth_mk_q_eq_iff.
  rewrite <- (cl_bp_uniq Th.(th_sig) γ α β h0).
  apply ClMor_theq_refl.
Qed.

Definition clth_binary_product (Th : Theory) (α β : list Th.(th_sig).(sg_ty)) :
    @IsBinaryProduct (ClTh Th) α β (α ++ β).
Proof.
  apply Build_IsBinaryProduct with
    (bp_proj1 := clth_proj1 Th α β)
    (bp_proj2 := clth_proj2 Th α β)
    (bp_pair  := fun γ f g => clth_pair Th γ α β f g).
  - intros γ f g. exact (clth_bp_beta1 Th γ α β f g).
  - intros γ f g. exact (clth_bp_beta2 Th γ α β f g).
  - intros γ h.   exact (clth_bp_uniq  Th γ α β h).
Defined.

Definition clth_has_binary_products (Th : Theory) : HasBinaryProducts (ClTh Th).
Proof.
  apply Build_HasBinaryProducts with
    (prod_obj := fun α β : list Th.(th_sig).(sg_ty) => α ++ β).
  exact (clth_binary_product Th).
Defined.

Definition clth_finite_products (Th : Theory) : HasFiniteProducts (ClTh Th).
Proof.
  refine {|
    fp_terminal := existT (fun T => @IsTerminal (ClTh Th) T) [] (clth_terminal Th);
    fp_binary   := clth_has_binary_products Th;
  |}.
Defined.
