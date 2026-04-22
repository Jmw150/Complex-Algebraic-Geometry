(** * Category/Examples/Set.v
    Products, coproducts, and powerset representability in TypeCat. *)

Require Import CAG.Category.Core.
Require Import CAG.Category.Products.
Require Import CAG.Category.Coproducts.
Require Import CAG.Category.Functor.
Require Import CAG.Category.Representable.
Require Import CAG.Category.Yoneda.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.

Set Universe Polymorphism.
Open Scope cat_scope.

(** ** Binary product in TypeCat is the cartesian product *)

Definition TypeCat_BinaryProduct (A B : Type) :
    @IsBinaryProduct TypeCat A B (A * B)%type.
Proof.
  refine (Build_IsBinaryProduct TypeCat A B (A * B)%type
    fst snd (fun X f g x => (f x, g x))
    (fun X f g => eq_refl) (fun X f g => eq_refl) _).
  intros X h. extensionality x. cbn.
  destruct (h x). reflexivity.
Defined.

(** ** Terminal object in TypeCat is unit *)

Definition TypeCat_Terminal : @IsTerminal TypeCat unit.
Proof.
  refine (Build_IsTerminal TypeCat unit (fun A _ => tt) _).
  intros A f. extensionality x. destruct (f x). reflexivity.
Defined.

(** ** Binary coproduct in TypeCat is the disjoint union *)

Definition TypeCat_BinaryCoproduct (A B : Type) :
    @IsBinaryCoproduct TypeCat A B (A + B)%type.
Proof.
  refine (Build_IsBinaryCoproduct TypeCat A B (A + B)%type
    inl inr (fun X f g s => match s with inl a => f a | inr b => g b end)
    (fun X f g => eq_refl) (fun X f g => eq_refl) _).
  intros X h. extensionality s. destruct s; reflexivity.
Defined.

(** ** Initial object in TypeCat is the empty type *)

Definition TypeCat_Initial : @IsInitial TypeCat False.
Proof.
  refine (Build_IsInitial TypeCat False (fun A (x : False) => match x with end) _).
  intros A f. extensionality x. destruct x.
Defined.

(** ** Powerset functor P_dec : TypeCat^op -> TypeCat *)

(** P_dec(X) = X -> bool, with functorial action by precomposition. *)
Definition PowersetFunctor : Functor (TypeCat^op) TypeCat.
Proof.
  apply (Build_Functor (TypeCat^op) TypeCat
    (fun X => X -> bool)
    (fun X Y f p y => p (f y))).
  - intros X. reflexivity.
  - intros X Y Z f g. reflexivity.
Defined.

(** The natural bijection Set(X, bool) ≅ P_dec(X) is the identity,
    since P_dec(X) = X -> bool = TypeCat⟦X, bool⟧. *)

Lemma powerset_representable (X : Type) :
    (X -> bool) = TypeCat⟦X, bool⟧.
Proof. reflexivity. Qed.
