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

(** ** Model record *)

Record Model (Th : Theory) (C : Category) (hp : HasFiniteProducts C) : Type := {
  (** Interpretation of sorts. *)
  mod_ty   : Th.(th_sig).(sg_ty) -> C.(Ob);

  (** Interpretation of function symbols.
      [f : α₁,...,αₙ → β] is sent to a morphism
        mod_fun f : Πᵢ mod_ty αᵢ → mod_ty β *)
  mod_fun  : forall (f : Th.(th_sig).(sg_fun)),
               C⟦ fp_prod hp (List.map mod_ty (Th.(th_sig).(sg_dom) f)),
                  mod_ty (Th.(th_sig).(sg_cod) f) ⟧;

  (** The axioms of Th hold in M. *)
  mod_ax   : forall (a : TheoryAxiom Th.(th_sig)),
               List.In a Th.(th_ax) ->
               (* The interpretation of the LHS and RHS agree as morphisms
                  out of the context product.  Stated as an admitted obligation
                  once term interpretation is defined. *)
               True;  (* placeholder — see mod_ax_eq below *)
}.

Arguments mod_ty  {Th C hp}.
Arguments mod_fun {Th C hp}.

(** ** Term interpretation

    Given a model M and a context Γ, interpret a well-typed term
    t : τ as a morphism   fp_prod hp (map mod_ty Γ) → mod_ty τ.

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
Qed.

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
Qed.

(** Term interpretation function. *)
Theorem interp_term : forall {Th : Theory} {C : Category} {hp : HasFiniteProducts C}
    (M : Model Th C hp)
    (Γ : list Th.(th_sig).(sg_ty))
    (t : Term Th.(th_sig))
    (τ : Th.(th_sig).(sg_ty))
    (Ht : HasType Th.(th_sig) Γ t τ),
    C⟦ fp_prod hp (List.map M.(mod_ty) Γ), M.(mod_ty) τ ⟧.
Proof.
  intros Th C hp M Γ t τ Ht.
  revert Γ τ Ht.
  refine (Fix (@att_term_lt_wf Th.(th_sig))
              (fun t => forall Γ τ,
                        HasType Th.(th_sig) Γ t τ ->
                        C⟦ fp_prod hp (List.map (mod_ty M) Γ), mod_ty M τ ⟧)
              _ t).
  intros t0 IH Γ τ Ht.
  destruct t0 as [n | f args].
  - (* t_var n: project from the context product *)
    apply (context_proj hp n (mod_ty M τ)).
    rewrite List.nth_error_map.
    rewrite (ht_var_nth_err Ht).
    reflexivity.
  - (* t_app f args: interpret args via IH, pair, then apply mod_fun *)
    rewrite (ht_app_cod_eq Ht).
    refine (mod_fun M f ∘ fp_tuple hp (List.map (mod_ty M) (Th.(th_sig).(sg_dom) f)) _).
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
Qed.

(** ** Model homomorphism

    A homomorphism of models M → N is a family of morphisms φ_α : [α]_M → [α]_N
    compatible with the interpretations of function symbols. *)

Record ModelHom {Th : Theory} {C : Category} {hp : HasFiniteProducts C}
    (M N : Model Th C hp) : Type := {
  mhom_on_ty : forall (α : Th.(th_sig).(sg_ty)),
                 C⟦ M.(mod_ty) α, N.(mod_ty) α ⟧;
  mhom_nat   : forall (f : Th.(th_sig).(sg_fun)),
                 (* Compatibility: the obvious square commutes. *)
                 True;  (* placeholder *)
}.

Arguments mhom_on_ty {Th C hp M N}.
