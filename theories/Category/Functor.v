(** * Category/Functor.v
    Functors and natural transformations. *)

Require Import CAG.Category.Core.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.

Set Universe Polymorphism.
Open Scope cat_scope.

(** ** Functor *)

Record Functor (C D : Category) : Type := {
  fobj : C.(Ob) -> D.(Ob);
  fmap : forall {A B}, C⟦A, B⟧ -> D⟦fobj A, fobj B⟧;

  fmap_id   : forall A, fmap (C.(id) A) = D.(id) (fobj A);
  fmap_comp : forall {A B E} (f : C⟦B, E⟧) (g : C⟦A, B⟧),
    fmap (f ∘ g) = fmap f ∘ fmap g;
}.

Arguments fobj     {C D} f0 A.
Arguments fmap     {C D} f0 {A B} f.
Arguments fmap_id  {C D} f0 A.
Arguments fmap_comp {C D} f0 {A B E} f g.

Notation "F ## A" := (fobj F A) (at level 9) : cat_scope.
Notation "F #> f" := (fmap F f) (at level 9) : cat_scope.

(** Identity functor. *)
Definition IdFunctor (C : Category) : Functor C C := {|
  fobj := fun A => A;
  fmap := fun A B f => f;
  fmap_id   := fun A => eq_refl;
  fmap_comp := fun A B E f g => eq_refl;
|}.

(** Functor composition. *)
Definition FunctorComp {C D E : Category}
    (G : Functor D E) (F : Functor C D) : Functor C E := {|
  fobj := fun X => G ## (F ## X);
  fmap := fun X Y h => G #> (F #> h);
  fmap_id := fun X =>
    eq_trans (f_equal (fun h => G #> h) (F.(fmap_id) X)) (G.(fmap_id) _);
  fmap_comp := fun X Y Z h k =>
    eq_trans (f_equal (fun h' => G #> h') (F.(fmap_comp) h k)) (G.(fmap_comp) _ _);
|}.

Notation "G ∘F F" := (FunctorComp G F) (at level 40) : cat_scope.

(** Opposite functor — deferred: requires care with C^op hom direction. *)
(* FunctorOp is defined later once we have more infrastructure. *)

(** ** Natural transformation *)

Record NatTrans {C D : Category} (F G : Functor C D) : Type := {
  component  : forall A, D⟦F ## A, G ## A⟧;
  naturality : forall {A B} (f : C⟦A, B⟧),
    G #> f ∘ component A = component B ∘ F #> f;
}.

Arguments component  {C D F G} n A.
Arguments naturality {C D F G} n {A B} f.

Notation "F ⟹ G" := (NatTrans F G) (at level 60) : cat_scope.

(** Equality of natural transformations via components. *)
Lemma nattrans_eq {C D : Category} {F G : Functor C D}
    (α β : F ⟹ G) :
    (forall A, α.(component) A = β.(component) A) -> α = β.
Proof.
  intros H.
  destruct α as [ca na], β as [cb nb]. cbn in H.
  assert (Hc : ca = cb) by (extensionality A; apply H).
  subst cb.
  f_equal.
  apply proof_irrelevance.
Qed.

(** Identity natural transformation. *)
Definition NatId {C D : Category} (F : Functor C D) : F ⟹ F := {|
  component  := fun A => D.(id) (F ## A);
  naturality := fun A B f =>
    eq_trans (D.(id_right) (F #> f)) (eq_sym (D.(id_left) (F #> f)));
|}.

(** Vertical composition of natural transformations. *)
Definition NatComp {C D : Category} {F G H : Functor C D}
    (β : G ⟹ H) (α : F ⟹ G) : F ⟹ H.
Proof.
  refine {| component := fun A => β.(component) A ∘ α.(component) A |}.
  intros A B f.
  rewrite D.(comp_assoc).
  rewrite β.(naturality).
  rewrite <- D.(comp_assoc).
  rewrite α.(naturality).
  rewrite D.(comp_assoc).
  reflexivity.
Defined.

Notation "β ∘N α" := (NatComp β α) (at level 40) : cat_scope.

(** Right whiskering: (H ∘F F) ⟹ (H ∘F G) given F ⟹ G and H. *)
Definition NatWhiskerRight {C D E : Category}
    {F G : Functor C D} (α : F ⟹ G) (H : Functor D E) : (H ∘F F) ⟹ (H ∘F G).
Proof.
  apply Build_NatTrans with (component := fun A => H #> (α.(component) A)).
  intros A B f. cbn.
  rewrite <- H.(fmap_comp). rewrite α.(naturality). rewrite H.(fmap_comp).
  reflexivity.
Defined.

(** Left whiskering: (F ∘F H) ⟹ (G ∘F H) given F ⟹ G and H. *)
Definition NatWhiskerLeft {C D E : Category}
    (H : Functor C D) {F G : Functor D E} (α : F ⟹ G) : (F ∘F H) ⟹ (G ∘F H).
Proof.
  apply Build_NatTrans with (component := fun A => α.(component) (H ## A)).
  intros A B f. cbn. apply α.(naturality).
Defined.

(** ** Functor category [C, D] *)

Definition FunctorCat (C D : Category) : Category.
Proof.
  refine {|
    Ob   := Functor C D;
    Hom  := @NatTrans C D;
    id   := @NatId C D;
    comp := fun F G H β α => NatComp β α;
  |}.
  - intros F G H K γ β α.
    apply nattrans_eq. intros A. cbn. apply D.(comp_assoc).
  - intros F G α.
    apply nattrans_eq. intros A. cbn. apply D.(id_left).
  - intros F G α.
    apply nattrans_eq. intros A. cbn. apply D.(id_right).
Defined.

Notation "FunCat( C , D )" := (FunctorCat C D) (at level 0) : cat_scope.
