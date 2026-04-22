(** * ATT/Syntax.v
    Raw terms, well-typed terms, substitution, provable equality in context.

    Contexts are lists of sorts.  Variables are de Bruijn indices (nat).
    The variable x_i in context [τ₀,...,τₙ₋₁] has type τᵢ when i < n. *)

Require Import CAG.ATT.Signature.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import micromega.Lia.
Import ListNotations.

(** ** Raw terms *)

(** A term is either a variable (de Bruijn index) or a function symbol
    applied to a list of arguments. *)
Inductive Term (Sg : Signature) : Type :=
  | t_var : nat -> Term Sg
  | t_app : Sg.(sg_fun) -> list (Term Sg) -> Term Sg.

Arguments t_var {Sg} n.
Arguments t_app {Sg} f args.

(** ** Typing judgment

    [HasType Sg Γ t τ] means that term [t] has sort [τ] in context [Γ]. *)
Inductive HasType (Sg : Signature) (Γ : list Sg.(sg_ty)) :
    Term Sg -> Sg.(sg_ty) -> Prop :=
  | ht_var : forall n τ,
      List.nth_error Γ n = Some τ ->
      HasType Sg Γ (t_var n) τ
  | ht_app : forall (f : Sg.(sg_fun)) (args : list (Term Sg)),
      Forall2 (HasType Sg Γ) args (Sg.(sg_dom) f) ->
      HasType Sg Γ (t_app f args) (Sg.(sg_cod) f).

(** ** Substitution

    [subst_term sub t] replaces variable i in t by [sub[i]], or leaves it
    as [t_var i] if i is out of range. *)
Fixpoint subst_term (Sg : Signature) (sub : list (Term Sg)) (t : Term Sg) : Term Sg :=
  match t with
  | t_var n   => match List.nth_error sub n with
                 | Some t' => t'
                 | None    => t_var n
                 end
  | t_app f args => t_app f (List.map (subst_term Sg sub) args)
  end.

(** The identity substitution for a context of length n. *)
Definition id_sub (Sg : Signature) (n : nat) : list (Term Sg) :=
  List.map t_var (List.seq 0 n).

(** Simultaneous substitution over a list of terms. *)
Definition subst_list (Sg : Signature) (sub : list (Term Sg))
    (ts : list (Term Sg)) : list (Term Sg) :=
  List.map (subst_term Sg sub) ts.

(** ** Key substitution lemmas *)

(** Substituting variable i gives sub[i] when in range, t_var i otherwise. *)
Lemma subst_var (Sg : Signature) (sub : list (Term Sg)) (i : nat) :
    subst_term Sg sub (t_var i) =
    match List.nth_error sub i with Some t => t | None => t_var i end.
Proof.
  reflexivity.
Qed.

(** The identity substitution is an identity on all terms. *)
Lemma subst_id_term (Sg : Signature) (n : nat) :
    forall t : Term Sg, subst_term Sg (id_sub Sg n) t = t.
Proof.
  fix IH 1. intros [i | f args].
  - (* t_var i: look up in id_sub = map t_var (seq 0 n) *)
    simpl. unfold id_sub.
    rewrite List.nth_error_map, nth_error_seq.
    destruct (Compare_dec.lt_dec i n) as [Hlt | Hge].
    + replace (i <? n) with true by (symmetry; apply Nat.ltb_lt; exact Hlt).
      simpl. reflexivity.
    + replace (i <? n) with false by (symmetry; apply Nat.ltb_nlt; lia).
      reflexivity.
  - (* t_app f args: recurse into args *)
    simpl. f_equal.
    induction args as [| a args' IHargs].
    + reflexivity.
    + simpl. f_equal. apply IH. apply IHargs.
Qed.

(** Substituting by the identity list is identity on all term lists. *)
Lemma subst_id_list (Sg : Signature) (n : nat) (ts : list (Term Sg)) :
    subst_list Sg (id_sub Sg n) ts = ts.
Proof.
  unfold subst_list.
  transitivity (List.map (fun t => t) ts).
  - apply List.map_ext. intro t. apply subst_id_term.
  - apply List.map_id.
Qed.

(** Helper: nth_error of id_sub. *)
Lemma nth_error_id_sub (Sg : Signature) (n i : nat) :
    List.nth_error (id_sub Sg n) i =
    if i <? n then Some (t_var i) else None.
Proof.
  unfold id_sub.
  rewrite List.nth_error_map, nth_error_seq.
  destruct (Compare_dec.lt_dec i n) as [Hlt | Hge].
  - replace (i <? n) with true by (symmetry; apply Nat.ltb_lt; exact Hlt).
    reflexivity.
  - replace (i <? n) with false by (symmetry; apply Nat.ltb_nlt; lia).
    reflexivity.
Qed.

(** Substituting variables by sub gives the list back. *)
Lemma subst_var_list (Sg : Signature) (sub : list (Term Sg)) :
    subst_list Sg sub (id_sub Sg (length sub)) = sub.
Proof.
  unfold subst_list.
  apply List.nth_error_ext.
  intro i.
  rewrite List.nth_error_map.
  rewrite nth_error_id_sub.
  destruct (i <? length sub) eqn:Hi.
  - apply Nat.ltb_lt in Hi.
    simpl.
    destruct (List.nth_error sub i) eqn:Hni.
    + reflexivity.
    + apply List.nth_error_None in Hni. lia.
  - apply Nat.ltb_ge in Hi. simpl.
    symmetry. apply List.nth_error_None. lia.
Qed.

(** Substitution composition: sub1 ∘ (sub2 applied to t) = (sub1 ∘ sub2) applied to t.
    This holds when all variables in t are in range for sub2. *)
Lemma subst_comp_term (Sg : Signature) (sub1 sub2 : list (Term Sg)) (t : Term Sg) :
    (forall i, List.nth_error sub2 i = None ->
               List.nth_error sub1 i = None) ->
    subst_term Sg sub1 (subst_term Sg sub2 t) =
    subst_term Sg (subst_list Sg sub1 sub2) t.
Proof.
  intro Hdom.
  revert t.
  fix IH 1. intros [i | f args].
  - (* t_var i *)
    simpl.
    destruct (List.nth_error sub2 i) as [t|] eqn:H2.
    + (* sub2[i] = Some t: recurse with sub1 *)
      unfold subst_list.
      rewrite List.nth_error_map, H2. simpl. reflexivity.
    + (* sub2[i] = None: variable stays as t_var i *)
      unfold subst_list.
      rewrite List.nth_error_map, H2. simpl.
      specialize (Hdom i H2).
      rewrite Hdom. reflexivity.
  - (* t_app f args *)
    simpl. f_equal.
    induction args as [| a args' IHargs].
    + reflexivity.
    + simpl. f_equal. exact (IH a). exact IHargs.
Qed.

(** Composition of substitution lists (generalisation over all terms). *)
Lemma subst_comp_list (Sg : Signature) (sub1 sub2 sub3 : list (Term Sg)) :
    (forall i, List.nth_error sub2 i = None ->
               List.nth_error sub1 i = None) ->
    subst_list Sg sub1 (subst_list Sg sub2 sub3) =
    subst_list Sg (subst_list Sg sub1 sub2) sub3.
Proof.
  intro Hdom.
  unfold subst_list.
  rewrite List.map_map.
  apply List.map_ext.
  intro t. apply subst_comp_term. exact Hdom.
Qed.

(** ** Typing preservation under substitution *)

(** Helper: Forall2 gives nth_error correspondence. *)
Lemma Forall2_nth_error_l {A B : Type} (R : A -> B -> Prop)
    (l1 : list A) (l2 : list B) :
    Forall2 R l1 l2 ->
    forall i y, List.nth_error l2 i = Some y ->
    exists x, List.nth_error l1 i = Some x /\ R x y.
Proof.
  induction 1 as [|x y0 l1' l2' Hxy Hrest IH].
  - intros i y. destruct i; simpl; discriminate.
  - intros [|i] y Hy.
    + simpl in Hy. injection Hy as <-. exists x. split. reflexivity. exact Hxy.
    + simpl in Hy. apply IH in Hy as [x' [Hx' HR]].
      exists x'. split. simpl. exact Hx'. exact HR.
Qed.

(** If sub[i] has type Γ'[i] for each i, and t has type τ in Γ',
    then (subst sub t) has type τ in Γ. *)
Lemma subst_preserves_type (Sg : Signature)
    (Γ Γ' : list Sg.(sg_ty))
    (sub : list (Term Sg))
    (Hsub : Forall2 (HasType Sg Γ) sub Γ') :
    forall (t : Term Sg) (τ : Sg.(sg_ty)),
    HasType Sg Γ' t τ ->
    HasType Sg Γ (subst_term Sg sub t) τ.
Proof.
  fix IH 3. intros t τ Ht.
  destruct Ht as [n τ Hn | f args Hargs].
  - (* ht_var: look up sub[n] *)
    simpl.
    destruct (Forall2_nth_error_l _ _ _ Hsub n τ Hn) as [t' [Ht' Htype]].
    rewrite Ht'. exact Htype.
  - (* ht_app: recurse into each argument *)
    simpl. apply ht_app.
    induction Hargs as [|a τ' args' dom' Ha Hrest IHargs].
    + constructor.
    + constructor.
      * exact (IH a τ' Ha).
      * exact IHargs.
Qed.

(** Substitution preserves a list of types. *)
Lemma subst_preserves_type_list (Sg : Signature)
    (Γ Γ' : list Sg.(sg_ty))
    (sub : list (Term Sg))
    (Hsub : Forall2 (HasType Sg Γ) sub Γ')
    (ts : list (Term Sg)) (τs : list Sg.(sg_ty))
    (Hts : Forall2 (HasType Sg Γ') ts τs) :
    Forall2 (HasType Sg Γ) (subst_list Sg sub ts) τs.
Proof.
  unfold subst_list.
  induction Hts as [|t τ ts' τs' Ht Hrest IH].
  - constructor.
  - constructor.
    + exact (subst_preserves_type Sg Γ Γ' sub Hsub t τ Ht).
    + exact IH.
Qed.

(** ** Additional substitution lemmas *)

(** Substitution composition for well-typed terms (no global domain condition needed). *)
Lemma subst_comp_term_wt (Sg : Signature)
    (Γ : list Sg.(sg_ty)) (sub1 sub2 : list (Term Sg))
    (Hlen : length Γ <= length sub2) :
    forall (t : Term Sg) (τ : Sg.(sg_ty)),
    HasType Sg Γ t τ ->
    subst_term Sg sub1 (subst_term Sg sub2 t) =
    subst_term Sg (subst_list Sg sub1 sub2) t.
Proof.
  fix IH 3. intros t τ Ht.
  destruct Ht as [n τ Hn | f args Hargs].
  - simpl.
    destruct (List.nth_error sub2 n) as [t'|] eqn:H2.
    + unfold subst_list. rewrite List.nth_error_map, H2. simpl. reflexivity.
    + exfalso.
      apply List.nth_error_None in H2.
      assert (Hn_lt : n < length Γ).
      { rewrite <- List.nth_error_Some. rewrite Hn. discriminate. }
      lia.
  - simpl. f_equal.
    induction Hargs as [| a τ' args' dom' Ha Hrest IHargs].
    + reflexivity.
    + simpl. f_equal. exact (IH a τ' Ha). exact IHargs.
Qed.

(** Substitution composition over a well-typed list of terms. *)
Lemma subst_comp_list_wt (Sg : Signature)
    (Γ : list Sg.(sg_ty)) (sub1 sub2 : list (Term Sg))
    (Hlen : length Γ <= length sub2)
    (ts : list (Term Sg)) (τs : list Sg.(sg_ty))
    (Hts : Forall2 (HasType Sg Γ) ts τs) :
    subst_list Sg sub1 (subst_list Sg sub2 ts) =
    subst_list Sg (subst_list Sg sub1 sub2) ts.
Proof.
  induction Hts as [| t τ ts' τs' Ht Hrest IH].
  - reflexivity.
  - unfold subst_list. simpl. f_equal.
    + exact (subst_comp_term_wt Sg Γ sub1 sub2 Hlen t τ Ht).
    + exact IH.
Qed.

(** Substitution of the first n variables by (sub1 ++ sub2) gives sub1. *)
Lemma subst_take (Sg : Signature) (sub1 sub2 : list (Term Sg)) :
    subst_list Sg (sub1 ++ sub2) (id_sub Sg (length sub1)) = sub1.
Proof.
  apply List.nth_error_ext. intro i.
  unfold subst_list.
  rewrite List.nth_error_map, nth_error_id_sub.
  destruct (i <? length sub1) eqn:Hi.
  - apply Nat.ltb_lt in Hi. simpl.
    rewrite List.nth_error_app1 by exact Hi.
    destruct (List.nth_error sub1 i) eqn:Hni.
    + reflexivity.
    + apply List.nth_error_None in Hni. lia.
  - apply Nat.ltb_ge in Hi. simpl.
    symmetry. apply List.nth_error_None. lia.
Qed.

(** Substitution of variables seq (|sub1|) (|sub2|) by (sub1 ++ sub2) gives sub2. *)
Lemma subst_take_right (Sg : Signature) (sub1 sub2 : list (Term Sg)) :
    subst_list Sg (sub1 ++ sub2)
               (List.map t_var (List.seq (length sub1) (length sub2))) = sub2.
Proof.
  apply List.nth_error_ext. intro i.
  unfold subst_list.
  rewrite List.nth_error_map.
  rewrite List.nth_error_map, nth_error_seq.
  destruct (i <? length sub2) eqn:Hi.
  - apply Nat.ltb_lt in Hi. simpl.
    rewrite List.nth_error_app2 by lia.
    replace (length sub1 + i - length sub1) with i by lia.
    destruct (List.nth_error sub2 i) eqn:Hni.
    + reflexivity.
    + apply List.nth_error_None in Hni. lia.
  - apply Nat.ltb_ge in Hi. simpl.
    symmetry. apply List.nth_error_None. lia.
Qed.

(** ** Provable equality in context (theory equations)

    [ThEq Sg ax Γ t1 t2 τ] means the equation (t1 = t2 : τ) is derivable
    from the axioms [ax] in context [Γ].

    The axioms are given as a set of universally quantified equations:
    each axiom has a context (arity), a pair of terms, and a sort. *)

Record TheoryAxiom (Sg : Signature) : Type := {
  ax_ctx  : list Sg.(sg_ty);          (* the variable context *)
  ax_lhs  : Term Sg;                   (* left-hand side *)
  ax_rhs  : Term Sg;                   (* right-hand side *)
  ax_sort : Sg.(sg_ty);                (* the common sort *)
  ax_lhs_typed : HasType Sg ax_ctx ax_lhs ax_sort;
  ax_rhs_typed : HasType Sg ax_ctx ax_rhs ax_sort;
}.

Arguments ax_ctx  {Sg}.
Arguments ax_lhs  {Sg}.
Arguments ax_rhs  {Sg}.
Arguments ax_sort {Sg}.
Arguments ax_lhs_typed {Sg}.
Arguments ax_rhs_typed {Sg}.

(** Provable equality is the congruence closure of the axioms. *)
Inductive ThEq (Sg : Signature) (ax : list (TheoryAxiom Sg))
    (Γ : list Sg.(sg_ty)) :
    Term Sg -> Term Sg -> Sg.(sg_ty) -> Prop :=
  | theq_refl  : forall t τ, HasType Sg Γ t τ -> ThEq Sg ax Γ t t τ
  | theq_sym   : forall t1 t2 τ, ThEq Sg ax Γ t1 t2 τ -> ThEq Sg ax Γ t2 t1 τ
  | theq_trans : forall t1 t2 t3 τ,
      ThEq Sg ax Γ t1 t2 τ -> ThEq Sg ax Γ t2 t3 τ -> ThEq Sg ax Γ t1 t3 τ
  | theq_cong  : forall (f : Sg.(sg_fun)) args1 args2,
      Forall2 (fun a1 a2 => exists τ, ThEq Sg ax Γ a1 a2 τ) args1 args2 ->
      ThEq Sg ax Γ (t_app f args1) (t_app f args2) (Sg.(sg_cod) f)
  | theq_ax    : forall (a : TheoryAxiom Sg) (sub : list (Term Sg)),
      List.In a ax ->
      Forall2 (HasType Sg Γ) sub (a.(ax_ctx)) ->
      ThEq Sg ax Γ
        (subst_term Sg sub a.(ax_lhs))
        (subst_term Sg sub a.(ax_rhs))
        a.(ax_sort).
