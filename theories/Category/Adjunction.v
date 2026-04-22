(** * Category/Adjunction.v
    Categorical adjunctions via unit/counit, hom-set bijection,
    and basic triangle identities. *)

Require Import CAG.Category.Core.
Require Import CAG.Category.Functor.

Set Universe Polymorphism.
Open Scope cat_scope.

(* ------------------------------------------------------------------ *)
(** ** Adjunction record  F ⊣ G                                        *)
(* ------------------------------------------------------------------ *)

Record Adjunction {C D : Category} (F : Functor C D) (G : Functor D C) : Type := {
  adj_unit   : NatTrans (IdFunctor C) (FunctorComp G F);
  adj_counit : NatTrans (FunctorComp F G) (IdFunctor D);

  (** ε_{F A} ∘ F(η_A) = id_{F A}  (left triangle) *)
  adj_triangle_left : forall A : C.(Ob),
    adj_counit.(component) (F ## A) ∘ F #> (adj_unit.(component) A) =
    D.(id) (F ## A);

  (** G(ε_B) ∘ η_{G B} = id_{G B}  (right triangle) *)
  adj_triangle_right : forall B : D.(Ob),
    G #> (adj_counit.(component) B) ∘ adj_unit.(component) (G ## B) =
    C.(id) (G ## B);
}.

Arguments adj_unit          {C D F G} a.
Arguments adj_counit        {C D F G} a.
Arguments adj_triangle_left  {C D F G} a A.
Arguments adj_triangle_right {C D F G} a B.

Notation "F ⊣ G" := (Adjunction F G) (at level 70) : cat_scope.

(* ------------------------------------------------------------------ *)
(** ** Hom-set bijection                                                *)
(* ------------------------------------------------------------------ *)

(** Transpose right: C(A, G B) → D(F A, B). *)
Definition adj_lr {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) {A : C.(Ob)} {B : D.(Ob)}
    (f : C⟦A, G ## B⟧) : D⟦F ## A, B⟧ :=
  adj.(adj_counit).(component) B ∘ F #> f.

(** Transpose left: D(F A, B) → C(A, G B). *)
Definition adj_rl {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) {A : C.(Ob)} {B : D.(Ob)}
    (g : D⟦F ## A, B⟧) : C⟦A, G ## B⟧ :=
  G #> g ∘ adj.(adj_unit).(component) A.

(** adj_lr ∘ adj_rl = id *)
Lemma adj_lr_rl {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) {A : C.(Ob)} {B : D.(Ob)}
    (g : D⟦F ## A, B⟧) :
    adj_lr adj (adj_rl adj g) = g.
Proof.
  unfold adj_lr, adj_rl. cbn.
  rewrite F.(fmap_comp). rewrite D.(comp_assoc).
  assert (Hnat := adj.(adj_counit).(naturality) g). cbn in Hnat.
  (* Hnat: (IdFunctor D) #> g ∘ ε_{FA} = ε_B ∘ (F∘G) #> g *)
  (* After cbn: g ∘ ε_{FA} = ε_B ∘ F(G(g)) *)
  rewrite <- Hnat. rewrite <- D.(comp_assoc).
  assert (Htri := adj.(adj_triangle_left) A). cbn in Htri.
  rewrite Htri. apply D.(id_right).
Qed.

(** adj_rl ∘ adj_lr = id *)
Lemma adj_rl_lr {C D : Category} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) {A : C.(Ob)} {B : D.(Ob)}
    (f : C⟦A, G ## B⟧) :
    adj_rl adj (adj_lr adj f) = f.
Proof.
  unfold adj_lr, adj_rl. cbn.
  rewrite G.(fmap_comp). rewrite <- C.(comp_assoc).
  assert (Hnat := adj.(adj_unit).(naturality) f). cbn in Hnat.
  (* Hnat: (G∘F) #> f ∘ η_A = η_{GB} ∘ (IdFunctor C) #> f *)
  (* After cbn: G(F(f)) ∘ η_A = η_{GB} ∘ f *)
  rewrite Hnat. rewrite C.(comp_assoc).
  assert (Htri := adj.(adj_triangle_right) B). cbn in Htri.
  rewrite Htri. apply C.(id_left).
Qed.
