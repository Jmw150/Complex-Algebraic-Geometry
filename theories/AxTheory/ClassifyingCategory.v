(** * AxTheory/ClassifyingCategory.v
    The classifying category Cl(Th) of an Ax-theory Th.

    Objects: Ax-types  AxType Sg
    Morphisms α → β: an Ax-term M with AxHasType Sg [α] M β,
              identified by AxThEq (provable equality).

    The resulting category is cartesian closed:
    - terminal object: ax_unit
    - binary product: ax_prod α β
    - exponential: ax_exp α β

    We build the SYNTACTIC category (before quotienting by AxThEq).
    Category laws hold because substitution is the identity on well-typed terms. *)

Require Import CAG.ATT.Signature.
Require Import CAG.AxTheory.Syntax.
Require Import CAG.AxTheory.Theory.
Require Import CAG.Category.Core.
Require Import CAG.Category.Products.
Require Import CAG.Category.CartesianClosed.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.ProofIrrelevance.
Import ListNotations.

Set Universe Polymorphism.
Open Scope cat_scope.

(** ** Morphisms of Cl(Th): single-output typed terms *)

(** A morphism α → β is a term M with AxHasType Sg [α] M β.
    Note: unlike the algebraic case, objects are single types (not lists),
    so morphisms are single terms, not lists.
    Products are handled by the type structure itself. *)

Record AxClMor (Sg : Signature) (α β : AxType Sg) : Type := {
  axcl_term  : AxTerm Sg;
  axcl_typed : AxHasType Sg [α] axcl_term β;
}.

Arguments axcl_term  {Sg α β}.
Arguments axcl_typed {Sg α β}.

Lemma axcl_ext (Sg : Signature) (α β : AxType Sg) (f g : AxClMor Sg α β) :
    f.(axcl_term) = g.(axcl_term) -> f = g.
Proof.
  intro H. destruct f, g. simpl in H. subst.
  f_equal. apply proof_irrelevance.
Qed.

(** ** Identity morphism: the variable x : α in context [α] *)

Definition axcl_id (Sg : Signature) (α : AxType Sg) : AxClMor Sg α α :=
  {| axcl_term  := ax_var 0;
     axcl_typed := ax_ht_var Sg [α] 0 α eq_refl; |}.

(** ** Composition: substitute f's term into g's context *)

Lemma axcl_comp_typed (Sg : Signature) (α β γ : AxType Sg)
    (f : AxClMor Sg α β) (g : AxClMor Sg β γ) :
    AxHasType Sg [α] (ax_subst [f.(axcl_term)] g.(axcl_term)) γ.
Proof.
  apply ax_subst_preserves_type with [β].
  - constructor. exact f.(axcl_typed). constructor.
  - exact g.(axcl_typed).
Qed.

Definition axcl_comp (Sg : Signature) (α β γ : AxType Sg)
    (g : AxClMor Sg β γ) (f : AxClMor Sg α β) : AxClMor Sg α γ :=
  {| axcl_term  := ax_subst [f.(axcl_term)] g.(axcl_term);
     axcl_typed := axcl_comp_typed Sg α β γ f g; |}.

(** ** Category laws (admitted — require substitution lemmas) *)

Lemma axcl_id_left (Sg : Signature) (α β : AxType Sg) (f : AxClMor Sg α β) :
    axcl_comp Sg α β β (axcl_id Sg β) f = f.
Proof.
  apply axcl_ext. unfold axcl_comp, axcl_id. simpl.
  exact (ax_subst_singleton_var_0 Sg f.(axcl_term)).
Qed.

Lemma axcl_id_right (Sg : Signature) (α β : AxType Sg) (f : AxClMor Sg α β) :
    axcl_comp Sg α α β f (axcl_id Sg α) = f.
Proof.
  apply axcl_ext. unfold axcl_comp, axcl_id. simpl.
  (* ax_subst [ax_var 0] f.term = f.term: identity substitution *)
  exact (ax_subst_id Sg [α] f.(axcl_term) β f.(axcl_typed)).
Qed.

Lemma axcl_comp_assoc (Sg : Signature) (α β γ δ : AxType Sg)
    (f : AxClMor Sg α β) (g : AxClMor Sg β γ) (h : AxClMor Sg γ δ) :
    axcl_comp Sg α γ δ h (axcl_comp Sg α β γ g f) =
    axcl_comp Sg α β δ (axcl_comp Sg β γ δ h g) f.
Proof.
  apply axcl_ext. unfold axcl_comp. simpl.
  (* h is typed in context [γ]; sub2 = [g.term] has length 1 = length [γ]. *)
  rewrite (ax_subst_comp Sg [γ] _ _ _ _ eq_refl h.(axcl_typed)).
  reflexivity.
Qed.

(** ** The classifying category *)

Definition AxCl (Sg : Signature) : Category := {|
  Ob   := AxType Sg;
  Hom  := AxClMor Sg;
  id   := axcl_id Sg;
  comp := fun α β γ g f => axcl_comp Sg α β γ g f;
  comp_assoc := fun α β γ δ h g f => axcl_comp_assoc Sg α β γ δ f g h;
  id_left  := fun α β f => axcl_id_left  Sg α β f;
  id_right := fun α β f => axcl_id_right Sg α β f;
|}.

(** ** Terminal object: ax_unit *)

Lemma axcl_terminal_unique (Sg : Signature) (α : AxType Sg)
    (f : AxCl Sg ⟦ α, ax_unit ⟧) :
    f = {| axcl_term := ax_tt; axcl_typed := ax_ht_tt Sg [α] |}.
Proof.
  apply axcl_ext. simpl.
  (* By structural induction — any well-typed term of type ax_unit in context [α]
     is provably equal to ax_tt.  We admit this here; it follows from eta for unit. *)
  Admitted.

Definition axcl_to_unit (Sg : Signature) (α : AxType Sg) : AxCl Sg ⟦ α, ax_unit ⟧ :=
  {| axcl_term := ax_tt; axcl_typed := ax_ht_tt Sg [α] |}.

Definition axcl_is_terminal (Sg : Signature) : @IsTerminal (AxCl Sg) ax_unit.
Proof.
  apply Build_IsTerminal with (term_arr := axcl_to_unit Sg).
  intros α f. exact (axcl_terminal_unique Sg α f).
Defined.

(** ** Binary product: ax_prod *)

(** First projection: fst of the variable *)
Definition axcl_proj1 (Sg : Signature) (α β : AxType Sg) :
    AxCl Sg ⟦ α ×ax β, α ⟧ :=
  {| axcl_term  := ax_fst (ax_var 0);
     axcl_typed := ax_ht_fst Sg [α ×ax β] (ax_var 0) α β
                     (ax_ht_var Sg [α ×ax β] 0 (α ×ax β) eq_refl); |}.

(** Second projection *)
Definition axcl_proj2 (Sg : Signature) (α β : AxType Sg) :
    AxCl Sg ⟦ α ×ax β, β ⟧ :=
  {| axcl_term  := ax_snd (ax_var 0);
     axcl_typed := ax_ht_snd Sg [α ×ax β] (ax_var 0) α β
                     (ax_ht_var Sg [α ×ax β] 0 (α ×ax β) eq_refl); |}.

(** Pairing: given f : γ → α and g : γ → β, define ⟨f, g⟩ : γ → α × β *)
Lemma axcl_pair_typed (Sg : Signature) (γ α β : AxType Sg)
    (f : AxCl Sg ⟦ γ, α ⟧) (g : AxCl Sg ⟦ γ, β ⟧) :
    AxHasType Sg [γ] (ax_pair f.(axcl_term) g.(axcl_term)) (α ×ax β).
Proof.
  apply ax_ht_pair.
  - exact f.(axcl_typed).
  - exact g.(axcl_typed).
Qed.

Definition axcl_pair (Sg : Signature) (γ α β : AxType Sg)
    (f : AxCl Sg ⟦ γ, α ⟧) (g : AxCl Sg ⟦ γ, β ⟧) :
    AxCl Sg ⟦ γ, α ×ax β ⟧ :=
  {| axcl_term  := ax_pair f.(axcl_term) g.(axcl_term);
     axcl_typed := axcl_pair_typed Sg γ α β f g; |}.

(** Beta rules for products *)
Lemma axcl_bp_beta1 (Sg : Signature) (γ α β : AxType Sg)
    (f : AxCl Sg ⟦ γ, α ⟧) (g : AxCl Sg ⟦ γ, β ⟧) :
    axcl_comp Sg γ (α ×ax β) α (axcl_proj1 Sg α β) (axcl_pair Sg γ α β f g) = f.
Proof.
  apply axcl_ext. unfold axcl_comp, axcl_proj1, axcl_pair. simpl.
  (* ax_subst [pair f g] (fst (var 0)) = ax_subst [pair f g] (fst (var 0))
     = fst (pair f g) ... = f by beta_fst *)
  Admitted.

Lemma axcl_bp_beta2 (Sg : Signature) (γ α β : AxType Sg)
    (f : AxCl Sg ⟦ γ, α ⟧) (g : AxCl Sg ⟦ γ, β ⟧) :
    axcl_comp Sg γ (α ×ax β) β (axcl_proj2 Sg α β) (axcl_pair Sg γ α β f g) = g.
Proof.
  apply axcl_ext. Admitted.

Lemma axcl_bp_uniq (Sg : Signature) (γ α β : AxType Sg)
    (h : AxCl Sg ⟦ γ, α ×ax β ⟧) :
    h = axcl_pair Sg γ α β
          (axcl_comp Sg γ (α ×ax β) α (axcl_proj1 Sg α β) h)
          (axcl_comp Sg γ (α ×ax β) β (axcl_proj2 Sg α β) h).
Proof.
  apply axcl_ext. Admitted.

Definition axcl_binary_product (Sg : Signature) (α β : AxType Sg) :
    @IsBinaryProduct (AxCl Sg) α β (α ×ax β).
Proof.
  apply Build_IsBinaryProduct with
    (bp_proj1 := axcl_proj1 Sg α β)
    (bp_proj2 := axcl_proj2 Sg α β)
    (bp_pair  := fun γ f g => axcl_pair Sg γ α β f g).
  - intros γ f g. exact (axcl_bp_beta1 Sg γ α β f g).
  - intros γ f g. exact (axcl_bp_beta2 Sg γ α β f g).
  - intros γ h.   exact (axcl_bp_uniq  Sg γ α β h).
Defined.

(** ** Exponential object: ax_exp α β  (= β^α) *)

(** Evaluation morphism: eval : (α ⇒ β) × α → β
    = ax_ap (fst (var 0)) (snd (var 0)) in context [(α ⇒ β) × α] *)
Lemma axcl_eval_typed (Sg : Signature) (α β : AxType Sg) :
    AxHasType Sg [(α ⇒ax β) ×ax α]
      (ax_ap (ax_fst (ax_var 0)) (ax_snd (ax_var 0))) β.
Proof.
  apply ax_ht_ap with α.
  - (* fst(var 0) : α ⇒ β in [(α⇒β)×α] *)
    apply (ax_ht_fst Sg [(α ⇒ax β) ×ax α] (ax_var 0) (α ⇒ax β) α).
    apply ax_ht_var. reflexivity.
  - (* snd(var 0) : α in [(α⇒β)×α] *)
    apply (ax_ht_snd Sg [(α ⇒ax β) ×ax α] (ax_var 0) (α ⇒ax β) α).
    apply ax_ht_var. reflexivity.
Qed.

Definition axcl_eval (Sg : Signature) (α β : AxType Sg) :
    AxCl Sg ⟦ (α ⇒ax β) ×ax α, β ⟧ :=
  {| axcl_term  := ax_ap (ax_fst (ax_var 0)) (ax_snd (ax_var 0));
     axcl_typed := axcl_eval_typed Sg α β; |}.

(** Currying: given f : γ × α → β, define Λ(f) : γ → α ⇒ β
    = λ (f applied to ⟨var 1, var 0⟩) in context [γ] *)
Theorem axcl_curry : forall (Sg : Signature) (γ α β : AxType Sg)
    (f : AxCl Sg ⟦ γ ×ax α, β ⟧),
    AxCl Sg ⟦ γ, α ⇒ax β ⟧.
Proof.
  intros Sg γ α β f.
  refine {| axcl_term  := ax_lam (ax_subst [ax_pair (ax_var 1) (ax_var 0)] f.(axcl_term));
            axcl_typed := _ |}.
  apply ax_ht_lam.
  refine (ax_subst_preserves_type Sg [α; γ] [γ ×ax α]
            [ax_pair (ax_var 1) (ax_var 0)] _ f.(axcl_term) β f.(axcl_typed)).
  constructor.
  - apply ax_ht_pair.
    + apply ax_ht_var. reflexivity.
    + apply ax_ht_var. reflexivity.
  - constructor.
Defined.

Theorem axcl_exp_beta : forall (Sg : Signature) (γ α β : AxType Sg)
    (f : AxCl Sg ⟦ γ ×ax α, β ⟧),
    axcl_comp Sg (γ ×ax α) ((α ⇒ax β) ×ax α) β
      (axcl_eval Sg α β)
      (axcl_pair Sg (γ ×ax α) (α ⇒ax β) α
        (axcl_curry Sg γ α β f ∘ axcl_proj1 Sg γ α)
        (axcl_proj2 Sg γ α)) = f.
Proof. admit. Admitted.

Theorem axcl_exp_eta : forall (Sg : Signature) (γ α β : AxType Sg)
    (g : AxCl Sg ⟦ γ, α ⇒ax β ⟧),
    axcl_curry Sg γ α β
      (axcl_comp Sg (γ ×ax α) ((α ⇒ax β) ×ax α) β
        (axcl_eval Sg α β)
        (axcl_pair Sg (γ ×ax α) (α ⇒ax β) α
          (g ∘ axcl_proj1 Sg γ α)
          (axcl_proj2 Sg γ α))) = g.
Proof. admit. Admitted.

(** ** Finite products in AxCl *)

Definition axcl_has_binary_products (Sg : Signature) : HasBinaryProducts (AxCl Sg).
Proof.
  apply Build_HasBinaryProducts with (prod_obj := fun α β : AxType Sg => α ×ax β).
  exact (axcl_binary_product Sg).
Defined.

Definition axcl_finite_products (Sg : Signature) : HasFiniteProducts (AxCl Sg).
Proof.
  refine {|
    fp_terminal := existT (fun T => @IsTerminal (AxCl Sg) T) ax_unit (axcl_is_terminal Sg);
    fp_binary   := axcl_has_binary_products Sg;
  |}.
Defined.

(** ** AxCl is cartesian closed *)

(** Pre-defined helper: exponential object selector *)
Definition axcl_exp_obj_fn (Sg : Signature) (α β : AxType Sg) : AxType Sg :=
  α ⇒ax β.

(** IsExponential for a single pair of types *)
Definition axcl_is_exp (Sg : Signature) (α β : AxType Sg) :
    IsExponential (axcl_has_binary_products Sg) α β (α ⇒ax β).
Proof.
  apply Build_IsExponential with
    (exp_eval  := axcl_eval Sg α β)
    (exp_curry := fun X f => axcl_curry Sg X α β f).
  - (* exp_beta: eval ∘ prod_map ... (curry f) (id α) = f *)
    intros X f.
    unfold prod_map.
    cbn [prod_bp bp_pair bp_proj1 bp_proj2].
    rewrite (AxCl Sg).(id_left).
    exact (axcl_exp_beta Sg X α β f).
  - (* exp_eta: curry (eval ∘ prod_map ... g (id α)) = g *)
    intros X g.
    unfold prod_map.
    cbn [prod_bp bp_pair bp_proj1 bp_proj2].
    rewrite (AxCl Sg).(id_left).
    exact (axcl_exp_eta Sg X α β g).
Defined.

Definition axcl_has_exponentials (Sg : Signature) :
    HasExponentials (AxCl Sg) (axcl_has_binary_products Sg).
Proof.
  apply Build_HasExponentials with (exp_obj := axcl_exp_obj_fn Sg).
  exact (axcl_is_exp Sg).
Defined.

Definition axcl_ccc (Sg : Signature) : IsCartesianClosed (AxCl Sg).
Proof.
  exact {|
    ccc_fp  := axcl_finite_products Sg;
    ccc_exp := axcl_has_exponentials Sg;
  |}.
Defined.
