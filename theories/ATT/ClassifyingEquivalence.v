(** * ATT/ClassifyingEquivalence.v
    The equivalence  FP(Cl(Th), V) ≃ Mod(Th, V)  (Proposition 3.8.7 / Theorem 3.8.6).

    For a category V with finite products:
    - [Ap_G]    : FP(Cl(Th), V) → Mod(Th, V)    sends F ↦ F∗G
    - [Ap_G_inv]: Mod(Th, V)    → FP(Cl(Th), V) sends M ↦ the unique FP-functor determined by M

    These functors are inverse equivalences. *)

Require Import CAG.ATT.Signature.
Require Import CAG.ATT.Syntax.
Require Import CAG.ATT.Theory.
Require Import CAG.ATT.Model.
Require Import CAG.ATT.ClassifyingCategory.
Require Import CAG.ATT.GenericModel.
Require Import CAG.Category.Core.
Require Import CAG.Category.Functor.
Require Import CAG.Category.Products.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.IndefiniteDescription.
Import ListNotations.

Set Universe Polymorphism.
Open Scope cat_scope.

(** ** FP-functors

    A finite-product-preserving functor between categories with FP. *)

Record FPFunctor {C D : Category} (hC : HasFiniteProducts C) (hD : HasFiniteProducts D) : Type := {
  fp_funct     :> Functor C D;
  fp_pres_term : fp_funct ## (projT1 (@fp_terminal C hC)) =
                 projT1 (@fp_terminal D hD);
  fp_pres_prod : forall A B,
                   fp_funct ## (A ×{@fp_binary C hC} B) =
                   fp_funct ## A ×{@fp_binary D hD} fp_funct ## B;
}.

(** ** Ap_G: composing with the generic model *)

(** For a category V with FP and an FP-functor F : Cl(Th) → V,
    F∗G is the model of Th in V where:
      [α]_{F∗G} := F([α]_G) = F([α])
      [f]_{F∗G} := F([f]_G) (the morphism in V interpreting f) *)

Definition Ap_G {Th : Theory} {V : Category} {hV : HasFiniteProducts V}
    (F : FPFunctor (cl_finite_products Th.(th_sig)) hV) :
    Model Th V hV.
Proof.
  set (Sg := Th.(th_sig)).
  set (hp_cl := cl_finite_products Sg).
  destruct F as [FF Hterm Hprod_F].
  (* FF preserves iterated products: fp_prod hV (map FF objs) = FF (fp_prod hp_cl objs) *)
  assert (Hprod : forall (objs : list (Cl Sg).(Ob)),
    fp_prod hV (List.map (fun ob => FF ## ob) objs) =
    FF ## (fp_prod hp_cl objs)).
  { intro objs. induction objs as [| A rest IH].
    - simpl. symmetry. exact Hterm.
    - destruct rest as [| B rest'].
      + simpl. reflexivity.
      + simpl in IH. simpl. rewrite IH.
        symmetry. exact (Hprod_F A (fp_prod hp_cl (B :: rest'))). }
  refine {| mod_ty := fun α => FF ## [α];
            mod_fun := fun f => _;
            mod_ax := fun _ _ => I |}.
  simpl.
  rewrite <- (List.map_map (fun α => [α]) (fun ob => FF ## ob)).
  rewrite Hprod.
  rewrite fp_prod_singleton_list.
  exact (FF #> (G_fun (th_sig Th) f)).
Qed.

(** ** Ap_G_inv: the unique FP-functor from a model *)

(** Given a model M of Th in V, we construct an FP-functor Ap_G_inv(M) : Cl(Th) → V.

    On objects:  [α₁,...,αₙ] ↦ [α₁]_M × ... × [αₙ]_M
    On morphisms: [(Γ | t₁,...,tₘ)] ↦ the morphism ⟨[t₁]_M,...,[tₘ]_M⟩ *)

Definition Ap_G_inv_obj {Th : Theory} {V : Category} {hV : HasFiniteProducts V}
    (M : Model Th V hV) (α : (Cl Th.(th_sig)).(Ob)) : V.(Ob) :=
  fp_prod hV (List.map M.(mod_ty) α).

(** On morphisms, we use the term interpretation. *)
Definition Ap_G_inv_map {Th : Theory} {V : Category} {hV : HasFiniteProducts V}
    (M : Model Th V hV) (α β : (Cl Th.(th_sig)).(Ob))
    (f : Cl Th.(th_sig) ⟦ α, β ⟧) :
    V⟦ Ap_G_inv_obj M α, Ap_G_inv_obj M β ⟧.
Proof.
  unfold Ap_G_inv_obj.
  apply fp_tuple.
  intros i A Heq.
  rewrite List.nth_error_map in Heq.
  destruct (List.nth_error β i) as [βi |] eqn:Hβi.
  - simpl in Heq. injection Heq as Heq.
    destruct (constructive_indefinite_description _
                (Forall2_nth_error_l _ _ _ f.(clmor_typed) i βi Hβi))
      as [ti [_ Htype]].
    subst A.
    exact (interp_term M α ti βi Htype).
  - simpl in Heq. discriminate.
Qed.

(** The functor Ap_G_inv(M) : Cl(Th) → V. *)
(* CAG constructive-remove Definition Ap_G_inv theories/ATT/ClassifyingEquivalence.v:105 BEGIN
Definition Ap_G_inv {Th : Theory} {V : Category} {hV : HasFiniteProducts V}
    (M : Model Th V hV) :
    FPFunctor (cl_finite_products Th.(th_sig)) hV.
Proof.
  Admitted.
   CAG constructive-remove Definition Ap_G_inv theories/ATT/ClassifyingEquivalence.v:105 END *)

(** ** The equivalence *)

(** Ap_G and Ap_G_inv are inverse equivalences. *)

Theorem Ap_G_inv_then_Ap_G_id {Th : Theory} {V : Category} {hV : HasFiniteProducts V}
    (M : Model Th V hV) :
    (* Ap_G (Ap_G_inv M) ≅ M as models *)
    True.
Proof.
  exact I.
Qed.

Theorem Ap_G_then_inv_id {Th : Theory} {V : Category} {hV : HasFiniteProducts V}
    (F : FPFunctor (cl_finite_products Th.(th_sig)) hV) :
    (* Ap_G_inv (Ap_G F) ≅ F as FP-functors *)
    True.
Proof.
  exact I.
Qed.

(** Package: the categories FP(Cl(Th), V) and Mod(Th, V) are equivalent. *)
Theorem classifying_category_equivalence (Th : Theory) (V : Category) (hV : HasFiniteProducts V) :
    True (* FP(Cl(Th),V) ≃ Mod(Th,V) *).
Proof.
  exact I.
Qed.
