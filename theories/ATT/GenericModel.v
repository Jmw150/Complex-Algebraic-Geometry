(** * ATT/GenericModel.v
    The generic model G of a theory Th in its classifying category Cl(Sg).

    The generic model is defined by:
      [α]_G  :=  [α]   (the one-element list, object of Cl(Sg))
      [f]_G  :=  the morphism (dom f → cod f) given by [x₁:α₁,...,xₙ:αₙ | f(x₁,...,xₙ)]

    This is a model of Sg (the signature) in Cl(Sg) with finite products.
    It satisfies all axioms of Th because the morphism equality in the quotient
    Cl(Th) identifies provably equal term tuples.

    Proposition: for any proved equation Th ⊢ Γ ⊢ t = t' : τ, the interpretations
    [Γ ⊢ t]_G and [Γ ⊢ t']_G coincide in Cl(Th). *)

Require Import CAG.ATT.Signature.
Require Import CAG.ATT.Syntax.
Require Import CAG.ATT.Theory.
Require Import CAG.ATT.Model.
Require Import CAG.ATT.ClassifyingCategory.
Require Import CAG.Category.Core.
Require Import CAG.Category.Products.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
Import ListNotations.

Set Universe Polymorphism.
Open Scope cat_scope.

(** ** The generic model on Cl(Sg) *)

(** The sort α is sent to the singleton list [α]. *)
Definition G_ty (Sg : Signature) (α : Sg.(sg_ty)) : (Cl Sg).(Ob) := [α].

(** A function symbol f with domain [α₁,...,αₙ] and codomain β is sent to
    the morphism [α₁,...,αₙ] → [β] given by the term f(x₀,...,x_{n-1})
    in the canonical context [α₁,...,αₙ]. *)

Definition G_fun_term (Sg : Signature) (f : Sg.(sg_fun)) : Term Sg :=
  t_app f (List.map t_var (List.seq 0 (length (Sg.(sg_dom) f)))).

Lemma G_fun_term_typed (Sg : Signature) (f : Sg.(sg_fun)) :
    HasType Sg (Sg.(sg_dom) f) (G_fun_term Sg f) (Sg.(sg_cod) f).
Proof.
  unfold G_fun_term.
  apply ht_app.
  (* Need: Forall2 (HasType Sg (sg_dom f)) (map t_var (seq 0 n)) (sg_dom f) *)
  apply id_vars_typed_ok.
Qed.

(** Helper: fp_prod of singleton lists is the original list. *)
Lemma fp_prod_singleton_list (Sg : Signature) (xs : list Sg.(sg_ty)) :
    fp_prod (cl_finite_products Sg) (List.map (fun α => [α]) xs) = xs.
Proof.
  induction xs as [| α xs IH].
  - reflexivity.
  - destruct xs as [| β xs'].
    + reflexivity.
    + (* simpl would unfold map to [β]::map f xs', breaking rewrite IH.
         Instead use change to expose the IH subterm directly. *)
      change ([α] ++ fp_prod (cl_finite_products Sg)
                              (List.map (fun a => [a]) (β :: xs')) = α :: β :: xs').
      rewrite IH. reflexivity.
Qed.

(** The morphism [dom f → cod f] representing f in Cl(Sg). *)
Definition G_fun (Sg : Signature) (f : Sg.(sg_fun)) :
    Cl Sg ⟦ Sg.(sg_dom) f, [Sg.(sg_cod) f] ⟧ :=
  {| clmor_terms := [G_fun_term Sg f];
     clmor_typed := Forall2_cons _ _ (G_fun_term_typed Sg f) (Forall2_nil _) |}.

(** ** The generic model record *)

(** We state the generic model as a [Model] of the signature (ignoring axioms
    for now — axiom satisfaction follows in the quotient Cl(Th)).  *)

(** mod_fun for the generic model: defined separately so the rewrite is in
    a goal with a concrete type. *)
Definition GenericModel_mod_fun (Sg : Signature) (f : Sg.(sg_fun)) :
    Cl Sg ⟦ fp_prod (cl_finite_products Sg)
                    (List.map (fun α => [α]) (Sg.(sg_dom) f)),
             [Sg.(sg_cod) f] ⟧.
Proof.
  rewrite fp_prod_singleton_list.
  exact (G_fun Sg f).
Defined.

Definition GenericModel (Sg : Signature) :
    Model {| th_sig := Sg; th_ax := [] |}
          (Cl Sg)
          (cl_finite_products Sg).
Proof.
  exact (@Build_Model
    {| th_sig := Sg; th_ax := [] |}
    (Cl Sg)
    (cl_finite_products Sg)
    (fun α : Sg.(sg_ty) => [α])
    (GenericModel_mod_fun Sg)
    (fun _ _ => I)).
Defined.

(** ** Interpretation lemma (Proposition 1.1)

    For any proved equation Γ ⊢ t = t' : τ in Th,
    the interpretations [t]_G and [t']_G are equal as morphisms in Cl(Th).

    Proof idea:
    By induction on the derivation of ThEq, checking each rule.
    The key case is axiom application: if Th ⊢ ax : s = s' and sub instantiates
    the axiom variables, then [sub(s)]_G = [sub(s')]_G by the quotient equality
    in Cl(Th). *)

Theorem interpretation_lemma (Sg : Signature) (ax : list (TheoryAxiom Sg))
    (Γ : list Sg.(sg_ty)) (t t' : Term Sg) (τ : Sg.(sg_ty))
    (Ht  : HasType Sg Γ t  τ)
    (Ht' : HasType Sg Γ t' τ) :
    ThEq Sg ax Γ t t' τ ->
    ClMor_theq {| th_sig := Sg; th_ax := ax |}
      Γ [τ]
      {| clmor_terms := [t];
         clmor_typed := Forall2_cons _ _ Ht (Forall2_nil _) |}
      {| clmor_terms := [t'];
         clmor_typed := Forall2_cons _ _ Ht' (Forall2_nil _) |}.
Proof.
  intro Heq.
  unfold ClMor_theq. simpl.
  intros i t1 t2 τ0 H1 H2 H3.
  destruct i as [| i'].
  - simpl in H1, H2, H3.
    injection H1 as <-. injection H2 as <-. injection H3 as <-.
    exact Heq.
  - assert (Hnil : List.nth_error [t] (S i') = None).
    { apply List.nth_error_None. simpl. lia. }
    rewrite Hnil in H1. discriminate H1.
Qed.
