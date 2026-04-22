(** * Category/PreservesLimits.v
    Preservation, reflection, and creation of limits and colimits. *)

Require Import CAG.Category.Core.
Require Import CAG.Category.Functor.
Require Import CAG.Category.Limits.

Set Universe Polymorphism.
Open Scope cat_scope.

(* ------------------------------------------------------------------ *)
(** ** Preservation                                                     *)
(* ------------------------------------------------------------------ *)

(** F preserves limits of shape I:
    every limit cone in C maps to a limit cone in D. *)
Definition PreservesLimitsOfShape (I : Category) {C D : Category}
    (F : Functor C D) : Type :=
  forall (Dg : Functor I C) (L : Cone Dg),
    IsLimit L ->
    IsLimit (cone_fmap F L).

(** F preserves colimits of shape I. *)
Definition PreservesColimitsOfShape (I : Category) {C D : Category}
    (F : Functor C D) : Type :=
  forall (Dg : Functor I C) (L : Cocone Dg),
    IsColimit L ->
    IsColimit (cocone_fmap F L).

(* ------------------------------------------------------------------ *)
(** ** Reflection                                                       *)
(* ------------------------------------------------------------------ *)

(** F reflects limits of shape I:
    if the image cone is a limit in D, then the original cone was a limit in C. *)
Definition ReflectsLimitsOfShape (I : Category) {C D : Category}
    (F : Functor C D) : Type :=
  forall (Dg : Functor I C) (L : Cone Dg),
    IsLimit (cone_fmap F L) ->
    IsLimit L.

Definition ReflectsColimitsOfShape (I : Category) {C D : Category}
    (F : Functor C D) : Type :=
  forall (Dg : Functor I C) (L : Cocone Dg),
    IsColimit (cocone_fmap F L) ->
    IsColimit L.

(* ------------------------------------------------------------------ *)
(** ** Creation                                                         *)
(* ------------------------------------------------------------------ *)

(** F creates limits of shape I:
    given a limit of (F ∘ Dg) in D, there is a unique cone over Dg in C
    whose image is that limit, and that cone is a limit in C.

    We encode this as: existence of a "lift" function from limit cones
    of F∘Dg to limit cones of Dg. *)
Definition CreatesLimitsOfShape (I : Category) {C D : Category}
    (F : Functor C D) : Type :=
  forall (Dg : Functor I C) (L : Cone (FunctorComp F Dg)),
    IsLimit L ->
    { K : Cone Dg & prod (cone_fmap F K = L) (IsLimit K) }.

(* ------------------------------------------------------------------ *)
(** ** Example 2.11.11(1):
       preserving limits of shape n (discrete) = preserving products   *)
(* ------------------------------------------------------------------ *)

(** Discrete category on a type:
    objects are elements of T, only identity morphisms. *)
Definition DiscreteCat (T : Type) : Category := {|
  Ob   := T;
  Hom  := fun a b => a = b;
  id   := fun a => eq_refl;
  comp := fun a b c f g => eq_trans g f;
  comp_assoc := fun a b c d f g h =>
    eq_sym (eq_trans_assoc h g f);
  id_left  := fun a b f => match f with eq_refl => eq_refl end;
  id_right := fun a b f => eq_trans_refl_l f;
|}.

(** A functor from a discrete category is just a family of objects. *)
Lemma discrete_functor_is_family {T : Type} {C : Category}
    (D : Functor (DiscreteCat T) C) :
    forall t, (FunctorComp D (IdFunctor (DiscreteCat T))) ## t = D ## t.
Proof.
  intros t. reflexivity.
Qed.
