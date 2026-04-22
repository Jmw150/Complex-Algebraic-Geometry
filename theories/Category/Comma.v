(** * Category/Comma.v
    Comma categories, under-categories (A ↓ G), and over-categories. *)

Require Import CAG.Category.Core.
Require Import CAG.Category.Functor.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.

Set Universe Polymorphism.
Open Scope cat_scope.

(* ------------------------------------------------------------------ *)
(** ** Under-category  (A ↓ G)                                         *)
(*                                                                      *)
(*   Objects:   pairs (B : S, f : C⟦A, G B⟧)                           *)
(*   Morphisms from (B, f) to (B', f'):                                 *)
(*              h : S⟦B, B'⟧  with  G(h) ∘ f = f'                      *)
(* ------------------------------------------------------------------ *)

Section UnderCategory.

  Context {C S : Category} (A : C.(Ob)) (G : Functor S C).

  (** Objects *)
  Record UnderOb : Type := {
    under_ob  : S.(Ob);
    under_map : C⟦A, G ## under_ob⟧;
  }.

  (** Morphisms *)
  Record UnderHom (X Y : UnderOb) : Type := {
    under_hom   : S⟦X.(under_ob), Y.(under_ob)⟧;
    under_comm  : G #> under_hom ∘ X.(under_map) = Y.(under_map);
  }.

  Arguments under_hom  {X Y} h : rename.
  Arguments under_comm {X Y} h : rename.

  Definition under_id (X : UnderOb) : UnderHom X X.
  Proof.
    refine {| under_hom := S.(id) X.(under_ob) |}.
    rewrite G.(fmap_id). apply C.(id_left).
  Defined.

  Definition under_comp {X Y Z : UnderOb}
      (g : UnderHom Y Z) (f : UnderHom X Y) : UnderHom X Z.
  Proof.
    refine {| under_hom := g.(under_hom) ∘ f.(under_hom) |}.
    rewrite G.(fmap_comp).
    rewrite <- C.(comp_assoc).
    rewrite f.(under_comm).
    rewrite g.(under_comm).
    reflexivity.
  Defined.

  Lemma under_hom_eq {X Y : UnderOb} (f g : UnderHom X Y) :
      f.(under_hom) = g.(under_hom) -> f = g.
  Proof.
    intros H.
    destruct f as [hf cf], g as [hg cg]. cbn in H. subst hg.
    f_equal. apply proof_irrelevance.
  Qed.

  Definition UnderCat : Category.
  Proof.
    refine {|
      Ob   := UnderOb;
      Hom  := UnderHom;
      id   := under_id;
      comp := fun X Y Z g f => under_comp g f;
    |}.
    - intros X Y Z W h g f. apply under_hom_eq. cbn. apply S.(comp_assoc).
    - intros X Y f.          apply under_hom_eq. cbn. apply S.(id_left).
    - intros X Y f.          apply under_hom_eq. cbn. apply S.(id_right).
  Defined.

  (** Forgetful functor U : (A ↓ G) -> S. *)
  Definition UnderForget : Functor UnderCat S.
  Proof.
    apply (Build_Functor UnderCat S
      (fun X : UnderOb => X.(under_ob))
      (fun X Y (f : UnderHom X Y) => f.(under_hom))).
    - intros X. reflexivity.
    - intros X Y Z g f. reflexivity.
  Defined.

End UnderCategory.

Notation "A ↓ G" := (UnderCat A G) (at level 60) : cat_scope.

(* ------------------------------------------------------------------ *)
(** ** Over-category  (G ↓ A)  (dual)                                  *)
(*                                                                      *)
(*   Objects:   pairs (B : S, f : C⟦G B, A⟧)                           *)
(*   Morphisms: h : S⟦B, B'⟧ with f' ∘ G(h) = f                        *)
(* ------------------------------------------------------------------ *)

Section OverCategory.

  Context {C S : Category} (A : C.(Ob)) (G : Functor S C).

  Record OverOb : Type := {
    over_ob  : S.(Ob);
    over_map : C⟦G ## over_ob, A⟧;
  }.

  Record OverHom (X Y : OverOb) : Type := {
    over_hom  : S⟦X.(over_ob), Y.(over_ob)⟧;
    over_comm : Y.(over_map) ∘ G #> over_hom = X.(over_map);
  }.

  Arguments over_hom  {X Y} h : rename.
  Arguments over_comm {X Y} h : rename.

  Definition over_id (X : OverOb) : OverHom X X.
  Proof.
    refine {| over_hom := S.(id) X.(over_ob) |}.
    rewrite G.(fmap_id). apply C.(id_right).
  Defined.

  Definition over_comp {X Y Z : OverOb}
      (g : OverHom Y Z) (f : OverHom X Y) : OverHom X Z.
  Proof.
    refine {| over_hom := g.(over_hom) ∘ f.(over_hom) |}.
    rewrite G.(fmap_comp).
    rewrite C.(comp_assoc).
    rewrite g.(over_comm).
    rewrite f.(over_comm).
    reflexivity.
  Defined.

  Lemma over_hom_eq {X Y : OverOb} (f g : OverHom X Y) :
      f.(over_hom) = g.(over_hom) -> f = g.
  Proof.
    intros H.
    destruct f as [hf cf], g as [hg cg]. cbn in H. subst hg.
    f_equal. apply proof_irrelevance.
  Qed.

  Definition OverCat : Category.
  Proof.
    refine {|
      Ob   := OverOb;
      Hom  := OverHom;
      id   := over_id;
      comp := fun X Y Z g f => over_comp g f;
    |}.
    - intros X Y Z W h g f. apply over_hom_eq. cbn. apply S.(comp_assoc).
    - intros X Y f.          apply over_hom_eq. cbn. apply S.(id_left).
    - intros X Y f.          apply over_hom_eq. cbn. apply S.(id_right).
  Defined.

  Definition OverForget : Functor OverCat S.
  Proof.
    apply (Build_Functor OverCat S
      (fun X : OverOb => X.(over_ob))
      (fun X Y (f : OverHom X Y) => f.(over_hom))).
    - intros X. reflexivity.
    - intros X Y Z g f. reflexivity.
  Defined.

End OverCategory.

Notation "G ↑ A" := (OverCat A G) (at level 60) : cat_scope.
