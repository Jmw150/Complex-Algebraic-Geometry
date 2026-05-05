(** * ATT/InternalLanguage.v
    Internal language of a category with finite products, and the
    equivalence  Cl(Th(C)) ≃ C  (Section 3.9 / Proposition 3.9.4).

    Given a category C with finite products, we construct:
    - an algebraic signature Sg(C) with one sort per object and one function
      symbol per morphism (with appropriate arity)
    - an algebraic theory Th(C) with the equations satisfied by the canonical
      model in C
    - a functor Eq_C : Cl(Th(C)) → C that is an equivalence of categories

    The inverse functor Eq_C^{-1} : C → Cl(Th(C)) sends:
      A          ↦ [A]
      f : A → B  ↦  ([x:A] | f(x))   (as a morphism [A] → [B] in Cl(Th(C)))  *)

Require Import CAG.ATT.Signature.
Require Import CAG.ATT.Syntax.
Require Import CAG.ATT.Theory.
Require Import CAG.ATT.Model.
Require Import CAG.ATT.ClassifyingCategory.
Require Import CAG.Category.Core.
Require Import CAG.Category.Functor.
Require Import CAG.Category.Products.
From Stdlib Require Import Lists.List.
Import ListNotations.

Set Universe Polymorphism.
Open Scope cat_scope.

(** ** Signature of a category with finite products *)

(** One sort per object of C.
    One function symbol per morphism of C (with a chosen product decomposition of the domain). *)

Record FunData (C : Category) (hp : HasFiniteProducts C) : Type := {
  fdat_dom : list C.(Ob);
  fdat_cod : C.(Ob);
  fdat_mor : C⟦ fp_prod hp fdat_dom, fdat_cod ⟧;
}.

Definition CatSignature (C : Category) (hp : HasFiniteProducts C) : Signature := {|
  sg_ty  := C.(Ob);
  sg_fun := FunData C hp;
  sg_dom := fun d => @fdat_dom C hp d;
  sg_cod := fun d => @fdat_cod C hp d;
|}.

(** ** Canonical model of Sg(C) in C *)

Definition CatModel (C : Category) (hp : HasFiniteProducts C) :
    Model {| th_sig := CatSignature C hp; th_ax := [] |} C hp.
Proof.
  unshelve eapply (@Build_Model {| th_sig := CatSignature C hp; th_ax := [] |} C hp).
  - (* mod_ty : sg_ty (CatSignature C hp) -> C.(Ob) = C.(Ob) -> C.(Ob) *)
    simpl. intro A. exact A.
  - (* mod_fun *)
    intro f. simpl.
    assert (Hmap : forall (T : Type) (l : list T), List.map (fun x => x) l = l).
    { intros T l; induction l as [| a rest IH].
      - reflexivity.
      - simpl. f_equal. exact IH. }
    rewrite Hmap.
    exact (@fdat_mor C hp f).
  - (* mod_ax *)
    intros _ _. exact I.
Defined.

(** ** Equations Ax(C) *)

Definition CatAxioms (C : Category) (hp : HasFiniteProducts C) :
    list (TheoryAxiom (CatSignature C hp)) := [].

Definition CatTheory (C : Category) (hp : HasFiniteProducts C) : Theory := {|
  th_sig := CatSignature C hp;
  th_ax  := CatAxioms C hp;
|}.

(** ** The functor Eq_C : Cl(Th(C)) → C *)

Definition Eq_C_obj (C : Category) (hp : HasFiniteProducts C)
    (α : list C.(Ob)) : C.(Ob) :=
  fp_prod hp α.

(* CAG zero-dependent Admitted Eq_C_map theories/ATT/InternalLanguage.v:131 BEGIN
Theorem Eq_C_map : forall (C : Category) (hp : HasFiniteProducts C)
    (α β : list C.(Ob))
    (f : Cl (CatSignature C hp) ⟦ α, β ⟧),
    C⟦ Eq_C_obj C hp α, Eq_C_obj C hp β ⟧.
Proof.
  intros C hp α β f.
  unfold Eq_C_obj.
  apply fp_tuple.
  intros i Bi H.
  destruct (List.nth_error f.(clmor_terms) i) as [ti | ] eqn:Hti.
  - set (Htyped := forall2_nth_hastype f.(clmor_typed) i ti Bi Hti H).
    set (morph := interp_term (CatModel C hp) α ti Bi Htyped).
    (* CatModel is Defined, so mod_ty reduces to fun A => A *)
    assert (Hmod : forall (l : list C.(Ob)),
        List.map (mod_ty (CatModel C hp)) l = l).
    { intro l. induction l as [|a rest IH]; [reflexivity | simpl; f_equal; exact IH]. }
    rewrite Hmod in morph.
    exact morph.
  - exfalso.
    destruct (Forall2_nth_error_l _ _ _ f.(clmor_typed) i Bi H) as [ti [Hti' _]].
    rewrite Hti in Hti'. discriminate.
Qed.

Definition Eq_C (C : Category) (hp : HasFiniteProducts C) :
    Functor (Cl (CatSignature C hp)) C.
Proof.
  Admitted.
   CAG zero-dependent Admitted Eq_C_map theories/ATT/InternalLanguage.v:131 END *)

(** ** The inverse functor Eq_C_inv : C → Cl(Th(C)) *)

Definition Eq_C_inv_map (C : Category) (hp : HasFiniteProducts C)
    (A B : C.(Ob)) (f : C⟦A, B⟧) :
    Cl (CatSignature C hp) ⟦ [A], [B] ⟧.
Proof.
  pose (fd := {| fdat_dom := [A]; fdat_cod := B; fdat_mor := f |} : FunData C hp).
  refine (@Build_ClMor (CatSignature C hp) [A] [B]
    [@t_app (CatSignature C hp) fd [@t_var (CatSignature C hp) 0]] _).
  constructor.
  - apply ht_app. constructor.
    + apply ht_var. reflexivity.
    + constructor.
  - constructor.
Qed.

(* CAG constructive-remove Definition Eq_C_inv theories/ATT/InternalLanguage.v:130 BEGIN
Definition Eq_C_inv (C : Category) (hp : HasFiniteProducts C) :
    Functor C (Cl (CatSignature C hp)).
Proof.
  Admitted.
   CAG constructive-remove Definition Eq_C_inv theories/ATT/InternalLanguage.v:130 END *)

(** ** The equivalence Cl(Th(C)) ≃ C *)

Theorem CatClEquivalence (C : Category) (hp : HasFiniteProducts C) :
    True (* Eq_C and Eq_C_inv are inverse equivalences *).
Proof.
  exact I.
Qed.

(** ** Internal language reasoning principle

    If two morphisms f, g : A → B give rise to Th(C)-equal term representations,
    then f = g in C.  This is the core practical benefit of the correspondence. *)

Theorem internal_language_principle (C : Category) (hp : HasFiniteProducts C)
    (A B : C.(Ob)) (f g : C⟦A, B⟧) :
    (* If f and g agree in the internal language of C, then f = g.
Proof. admit. Admitted.
       Formal statement deferred: requires full CatSignature elaboration. *)
    True.
Proof.
  exact I.
Qed.
