(** * Category/Representable.v
    Hom-functors, representable functors, representations.
    TypeCat is used as the ambient "Set". *)

Require Import CAG.Category.Core.
Require Import CAG.Category.Functor.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.

Set Universe Polymorphism.
Open Scope cat_scope.

(** ** The category of types (playing the role of Set) *)

Definition TypeCat : Category := {|
  Ob   := Type;
  Hom  := fun A B => A -> B;
  id   := fun A x => x;
  comp := fun A B C f g x => f (g x);
  comp_assoc := fun A B C D f g h => eq_refl;
  id_left    := fun A B f => eq_refl;
  id_right   := fun A B f => eq_refl;
|}.

(** ** Covariant Hom-functor H[A] = C(A, -) : C -> TypeCat *)

Definition HomFunctor_cov {C : Category} (A : C.(Ob)) : Functor C TypeCat.
Proof.
  apply (Build_Functor C TypeCat (fun B => C.(Hom) A B) (fun B D f h => f ∘ h)).
  - intros B. extensionality h. apply C.(id_left).
  - intros B D E f g. extensionality h. cbn. apply eq_sym. apply C.(comp_assoc).
Defined.

Notation "H[ A ]" := (HomFunctor_cov A) (at level 9) : cat_scope.

(** ** Contravariant Hom-functor H^[B] = C(-, B) : C^op -> TypeCat *)

Definition HomFunctor_contra {C : Category} (B : C.(Ob)) : Functor (C^op) TypeCat.
Proof.
  apply (Build_Functor (C^op) TypeCat (fun A => C.(Hom) A B) (fun A' A f h => h ∘ f)).
  - intros A. extensionality h. apply C.(id_right).
  - intros A' A'' A f g. extensionality h. cbn. apply C.(comp_assoc).
Defined.

Notation "H^[ B ]" := (HomFunctor_contra B) (at level 9) : cat_scope.

(** ** Induced natural transformation for a morphism

    For h : A' -> A, precomposition gives H[h] : H[A] ⟹ H[A']. *)

Definition HomNatTrans {C : Category} {A A' : C.(Ob)} (h : C⟦A', A⟧) :
    NatTrans H[A] H[A'].
Proof.
  apply Build_NatTrans with (component := fun B (f : C.(Hom) A B) => f ∘ h).
  intros B D k. extensionality f. cbn.
  rewrite <- C.(comp_assoc). reflexivity.
Defined.

(** ** Product category C × D *)

Definition ProdCat (C E : Category) : Category := {|
  Ob   := C.(Ob) * E.(Ob);
  Hom  := fun AB PQ => (C.(Hom) (fst AB) (fst PQ) * E.(Hom) (snd AB) (snd PQ))%type;
  id   := fun AB => (C.(id) (fst AB), E.(id) (snd AB));
  comp := fun AB PQ RS '(f1, f2) '(g1, g2) => (f1 ∘ g1, f2 ∘ g2);
  comp_assoc := fun AB PQ RS ST '(f1, f2) '(g1, g2) '(h1, h2) =>
    f_equal2 pair (C.(comp_assoc) f1 g1 h1) (E.(comp_assoc) f2 g2 h2);
  id_left  := fun AB PQ '(f1, f2) =>
    f_equal2 pair (C.(id_left) f1) (E.(id_left) f2);
  id_right := fun AB PQ '(f1, f2) =>
    f_equal2 pair (C.(id_right) f1) (E.(id_right) f2);
|}.

Notation "C ×Cat D" := (ProdCat C D) (at level 40) : cat_scope.

(** ** Hom bifunctor Hom_C : C^op ×Cat C -> TypeCat *)

Definition HomBifunctor (C : Category) : Functor (C^op ×Cat C) TypeCat.
Proof.
  apply (Build_Functor (C^op ×Cat C) TypeCat
    (fun AB => C.(Hom) (fst AB) (snd AB))
    (fun AB CD fg h => snd fg ∘ h ∘ fst fg)).
  - intros [A B]. extensionality h. cbn.
    rewrite C.(id_left). rewrite C.(id_right). reflexivity.
  - intros [A B] [A' B'] [A'' B''] [f1 f2] [g1 g2].
    extensionality h. cbn.
    repeat rewrite <- C.(comp_assoc). reflexivity.
Defined.

(** ** Representable functor *)

(** F : C -> TypeCat is representable if there exists A and an iso H[A] ≅ F. *)
Record Representable {C : Category} (F : Functor C TypeCat) : Type := {
  rep_obj     : C.(Ob);
  rep_to      : NatTrans H[rep_obj] F;
  rep_from    : NatTrans F H[rep_obj];
  rep_to_from : forall A,
    component (NatComp rep_from rep_to) A = component (NatId H[rep_obj]) A;
  rep_from_to : forall A,
    component (NatComp rep_to rep_from) A = component (NatId F) A;
}.

(** Representation by a universal element a ∈ F(A). *)
Record IsRepresentation {C : Category} (F : Functor C TypeCat)
    (A : C.(Ob)) (a : F ## A) : Type := {
  ir_nat       : NatTrans H[A] F;
  ir_component : forall B (f : C⟦A, B⟧), component ir_nat B f = F #> f a;
  ir_inv       : NatTrans F H[A];
  ir_to_from   : forall B,
    component (NatComp ir_inv ir_nat) B = component (NatId H[A]) B;
  ir_from_to   : forall B,
    component (NatComp ir_nat ir_inv) B = component (NatId F) B;
}.
