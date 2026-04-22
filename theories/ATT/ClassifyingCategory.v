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
    category by [ClMor_theq].  We leave this as a remark: the quotient
    exists (by propositional extensionality + proof irrelevance applied to
    the set of equivalent morphisms), but we do not package it as a [Category]
    here.  Instead we use [ClassifyingCat Sg] as the syntactic approximation
    and note that [ClMor_theq] is a congruence with respect to composition. *)
