(** * Category/Coproducts.v
    Initial objects, binary coproducts, copairing.
    Dual to Products.v — coproduct in C = product in C^op. *)

Require Import CAG.Category.Core.
Require Import CAG.Category.Products.

Set Universe Polymorphism.
Open Scope cat_scope.

(** ** Binary coproduct *)

Record IsBinaryCoproduct {C : Category} (A B S : C.(Ob)) : Type := {
  bcp_inj1  : C⟦A, S⟧;
  bcp_inj2  : C⟦B, S⟧;
  bcp_case  : forall {X}, C⟦A, X⟧ -> C⟦B, X⟧ -> C⟦S, X⟧;
  bcp_beta1 : forall {X} (f : C⟦A, X⟧) (g : C⟦B, X⟧),
    bcp_case f g ∘ bcp_inj1 = f;
  bcp_beta2 : forall {X} (f : C⟦A, X⟧) (g : C⟦B, X⟧),
    bcp_case f g ∘ bcp_inj2 = g;
  bcp_uniq  : forall {X} (h : C⟦S, X⟧),
    h = bcp_case (h ∘ bcp_inj1) (h ∘ bcp_inj2);
}.

Arguments bcp_inj1  {C A B S} i.
Arguments bcp_inj2  {C A B S} i.
Arguments bcp_case  {C A B S} i {X} f g.
Arguments bcp_beta1 {C A B S} i {X} f g.
Arguments bcp_beta2 {C A B S} i {X} f g.
Arguments bcp_uniq  {C A B S} i {X} h.

Notation "[ f , g ]{ bcp }" := (bcp_case bcp f g)
  (at level 0, f at level 99, g at level 99) : cat_scope.

(** ** Copairing identities *)

(** l ∘ [f,g] = [l ∘ f, l ∘ g] *)
Lemma case_comp {C : Category} {A B S : C.(Ob)} (bcp : IsBinaryCoproduct A B S)
    {X Y} (f : C⟦A, X⟧) (g : C⟦B, X⟧) (l : C⟦X, Y⟧) :
    l ∘ [f, g]{bcp} = [l ∘ f, l ∘ g]{bcp}.
Proof.
  rewrite (bcp.(bcp_uniq) (l ∘ [f, g]{bcp})).
  f_equal.
  - rewrite <- C.(comp_assoc). rewrite bcp.(bcp_beta1). reflexivity.
  - rewrite <- C.(comp_assoc). rewrite bcp.(bcp_beta2). reflexivity.
Qed.

(** ** Binary coproduct is unique up to isomorphism  (Exercise 2.6.10) *)
Lemma binary_coproduct_unique {C : Category} {A B S S' : C.(Ob)}
    (bcp  : IsBinaryCoproduct A B S)
    (bcp' : IsBinaryCoproduct A B S') : S ≅[C] S'.
Proof.
  refine {|
    iso_fwd := [bcp'.(bcp_inj1), bcp'.(bcp_inj2)]{bcp};
    iso_bwd := [bcp.(bcp_inj1),  bcp.(bcp_inj2)]{bcp'};
  |}.
  - rewrite case_comp.
    rewrite bcp'.(bcp_beta1). rewrite bcp'.(bcp_beta2).
    symmetry.
    rewrite (bcp.(bcp_uniq) (C.(id) S)).
    rewrite C.(id_left). rewrite C.(id_left). reflexivity.
  - rewrite case_comp.
    rewrite bcp.(bcp_beta1). rewrite bcp.(bcp_beta2).
    symmetry.
    rewrite (bcp'.(bcp_uniq) (C.(id) S')).
    rewrite C.(id_left). rewrite C.(id_left). reflexivity.
Qed.

(** ** Category with binary coproducts *)

Record HasBinaryCoproducts (C : Category) : Type := {
  coprod_obj : C.(Ob) -> C.(Ob) -> C.(Ob);
  coprod_bcp : forall A B, IsBinaryCoproduct A B (coprod_obj A B);
}.

Arguments coprod_obj {C} h A B.
Arguments coprod_bcp {C} h A B.

Notation "A +{ HCP } B" := (coprod_obj HCP A B) (at level 50) : cat_scope.

(** ** Duality: coproduct in C = product in C^op *)

Lemma op_product_is_coproduct {C : Category} {A B P : C.(Ob)}
    (bp : @IsBinaryProduct (C^op) A B P) :
    IsBinaryCoproduct A B P.
Proof.
  unshelve econstructor.
  - exact bp.(bp_proj1).
  - exact bp.(bp_proj2).
  - intros X f g. exact (bp.(bp_pair) f g).
  - intros X f g. exact (bp.(bp_beta1) f g).
  - intros X f g. exact (bp.(bp_beta2) f g).
  - intros X h. exact (bp.(bp_uniq) h).
Qed.

Lemma op_coproduct_is_product {C : Category} {A B S : C.(Ob)}
    (bcp : IsBinaryCoproduct A B S) :
    @IsBinaryProduct (C^op) A B S.
Proof.
  unshelve econstructor.
  - exact bcp.(bcp_inj1).
  - exact bcp.(bcp_inj2).
  - intros X f g. exact (bcp.(bcp_case) f g).
  - intros X f g. exact (bcp.(bcp_beta1) f g).
  - intros X f g. exact (bcp.(bcp_beta2) f g).
  - intros X h. exact (bcp.(bcp_uniq) h).
Qed.
