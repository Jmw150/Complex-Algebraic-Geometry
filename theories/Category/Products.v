(** * Category/Products.v
    Terminal objects, binary products, finite products, pairing, product of morphisms. *)

Require Import CAG.Category.Core.

Set Universe Polymorphism.
Open Scope cat_scope.

(** ** Binary product *)

Record IsBinaryProduct {C : Category} (A B P : C.(Ob)) : Type := {
  bp_proj1 : C⟦P, A⟧;
  bp_proj2 : C⟦P, B⟧;
  bp_pair  : forall {X}, C⟦X, A⟧ -> C⟦X, B⟧ -> C⟦X, P⟧;
  bp_beta1 : forall {X} (f : C⟦X, A⟧) (g : C⟦X, B⟧),
    bp_proj1 ∘ bp_pair f g = f;
  bp_beta2 : forall {X} (f : C⟦X, A⟧) (g : C⟦X, B⟧),
    bp_proj2 ∘ bp_pair f g = g;
  bp_uniq  : forall {X} (h : C⟦X, P⟧),
    h = bp_pair (bp_proj1 ∘ h) (bp_proj2 ∘ h);
}.

Arguments bp_proj1 {C A B P} i.
Arguments bp_proj2 {C A B P} i.
Arguments bp_pair  {C A B P} i {X} f g.
Arguments bp_beta1 {C A B P} i {X} f g.
Arguments bp_beta2 {C A B P} i {X} f g.
Arguments bp_uniq  {C A B P} i {X} h.

Notation "⟨ f , g ⟩{ bp }" := (bp_pair bp f g)
  (at level 0, f at level 99, g at level 99) : cat_scope.

(** ** Product of morphisms
    For f : A -> A' and g : B -> B', define f ×m g : A×B -> A'×B'. *)
Definition prod_map {C : Category} {A A' B B' P P' : C.(Ob)}
    (bp  : IsBinaryProduct A  B  P)
    (bp' : IsBinaryProduct A' B' P')
    (f : C⟦A, A'⟧) (g : C⟦B, B'⟧) : C⟦P, P'⟧ :=
  ⟨ f ∘ bp.(bp_proj1) , g ∘ bp.(bp_proj2) ⟩{bp'}.

(** ** Key identities *)

(** Exercise 2.6.7(2a): (h ×m k) ∘ ⟨f,g⟩ = ⟨h ∘ f, k ∘ g⟩ *)
Lemma prod_map_pair {C : Category} {A A' B B' P P' : C.(Ob)}
    (bp  : IsBinaryProduct A  B  P)
    (bp' : IsBinaryProduct A' B' P')
    {X} (f : C⟦X, A⟧) (g : C⟦X, B⟧)
    (h : C⟦A, A'⟧) (k : C⟦B, B'⟧) :
    prod_map bp bp' h k ∘ ⟨f, g⟩{bp} = ⟨h ∘ f, k ∘ g⟩{bp'}.
Proof.
  unfold prod_map.
  (* Both sides are morphisms X -> P'.  Show they have the same projections. *)
  rewrite (bp'.(bp_uniq) (⟨h ∘ bp.(bp_proj1), k ∘ bp.(bp_proj2)⟩{bp'} ∘ ⟨f, g⟩{bp})).
  f_equal.
  - rewrite C.(comp_assoc). rewrite bp'.(bp_beta1).
    rewrite <- C.(comp_assoc). rewrite bp.(bp_beta1). reflexivity.
  - rewrite C.(comp_assoc). rewrite bp'.(bp_beta2).
    rewrite <- C.(comp_assoc). rewrite bp.(bp_beta2). reflexivity.
Qed.

(** Exercise 2.6.7(2b): ⟨f,g⟩ ∘ l = ⟨f ∘ l, g ∘ l⟩ *)
Lemma pair_comp {C : Category} {A B P : C.(Ob)} (bp : IsBinaryProduct A B P)
    {X Y} (f : C⟦X, A⟧) (g : C⟦X, B⟧) (l : C⟦Y, X⟧) :
    ⟨f, g⟩{bp} ∘ l = ⟨f ∘ l, g ∘ l⟩{bp}.
Proof.
  rewrite (bp.(bp_uniq) (⟨f, g⟩{bp} ∘ l)).
  f_equal.
  - rewrite C.(comp_assoc). rewrite bp.(bp_beta1). reflexivity.
  - rewrite C.(comp_assoc). rewrite bp.(bp_beta2). reflexivity.
Qed.

(** id ×m id = id *)
Lemma prod_map_id {C : Category} {A B P : C.(Ob)} (bp : IsBinaryProduct A B P) :
    prod_map bp bp (C.(id) A) (C.(id) B) = C.(id) P.
Proof.
  unfold prod_map.
  rewrite C.(id_left). rewrite C.(id_left).
  rewrite (bp.(bp_uniq) (C.(id) P)).
  rewrite C.(id_right). rewrite C.(id_right).
  reflexivity.
Qed.

(** (g ×m g') ∘ (f ×m f') = (g ∘ f) ×m (g' ∘ f') *)
Lemma prod_map_comp {C : Category}
    {A A' A'' B B' B'' P P' P'' : C.(Ob)}
    (bp   : IsBinaryProduct A   B   P)
    (bp'  : IsBinaryProduct A'  B'  P')
    (bp'' : IsBinaryProduct A'' B'' P'')
    (f  : C⟦A,  A' ⟧) (g  : C⟦B,  B' ⟧)
    (f' : C⟦A', A''⟧) (g' : C⟦B', B''⟧) :
    prod_map bp' bp'' f' g' ∘ prod_map bp bp' f g =
    prod_map bp bp'' (f' ∘ f) (g' ∘ g).
Proof.
  unfold prod_map.
  rewrite (bp''.(bp_uniq) (⟨f' ∘ bp'.(bp_proj1), g' ∘ bp'.(bp_proj2)⟩{bp''} ∘ ⟨f ∘ bp.(bp_proj1), g ∘ bp.(bp_proj2)⟩{bp'})).
  f_equal.
  - rewrite C.(comp_assoc). rewrite bp''.(bp_beta1).
    rewrite <- C.(comp_assoc). rewrite bp'.(bp_beta1).
    rewrite C.(comp_assoc). reflexivity.
  - rewrite C.(comp_assoc). rewrite bp''.(bp_beta2).
    rewrite <- C.(comp_assoc). rewrite bp'.(bp_beta2).
    rewrite C.(comp_assoc). reflexivity.
Qed.

(** ** Binary product is unique up to isomorphism *)
Lemma binary_product_unique {C : Category} {A B P P' : C.(Ob)}
    (bp : IsBinaryProduct A B P)
    (bp' : IsBinaryProduct A B P') : P ≅[C] P'.
Proof.
  refine {|
    iso_fwd := ⟨bp.(bp_proj1), bp.(bp_proj2)⟩{bp'};
    iso_bwd := ⟨bp'.(bp_proj1), bp'.(bp_proj2)⟩{bp};
  |}.
  - (* iso_bwd ∘ iso_fwd = id P *)
    rewrite pair_comp.
    rewrite bp'.(bp_beta1). rewrite bp'.(bp_beta2).
    symmetry.
    rewrite (bp.(bp_uniq) (C.(id) P)).
    rewrite C.(id_right). rewrite C.(id_right). reflexivity.
  - (* iso_fwd ∘ iso_bwd = id P' *)
    rewrite pair_comp.
    rewrite bp.(bp_beta1). rewrite bp.(bp_beta2).
    symmetry.
    rewrite (bp'.(bp_uniq) (C.(id) P')).
    rewrite C.(id_right). rewrite C.(id_right). reflexivity.
Qed.

(** ** Category with binary products *)

Record HasBinaryProducts (C : Category) : Type := {
  prod_obj : C.(Ob) -> C.(Ob) -> C.(Ob);
  prod_bp  : forall A B, IsBinaryProduct A B (prod_obj A B);
}.

Arguments prod_obj {C} h A B.
Arguments prod_bp  {C} h A B.

Notation "A ×{ HP } B" := (prod_obj HP A B) (at level 40) : cat_scope.

(** ** Category with finite products (terminal + binary) *)

Record HasFiniteProducts (C : Category) : Type := {
  fp_terminal : {T : C.(Ob) & IsTerminal T};
  fp_binary   : HasBinaryProducts C;
}.

(** ** Associativity: A × (B × C) ≅ (A × B) × C *)

Lemma prod_assoc {C : Category} {A B D : C.(Ob)}
    {P_BC P_AB P_A_BC P_AB_C : C.(Ob)}
    (bp_BC    : IsBinaryProduct B    D   P_BC)
    (bp_AB    : IsBinaryProduct A    B   P_AB)
    (bp_A_BC  : IsBinaryProduct A    P_BC P_A_BC)
    (bp_AB_C  : IsBinaryProduct P_AB D   P_AB_C) :
    P_A_BC ≅[C] P_AB_C.
Proof.
  refine {|
    iso_fwd :=
      ⟨ ⟨bp_A_BC.(bp_proj1),
          bp_BC.(bp_proj1) ∘ bp_A_BC.(bp_proj2)⟩{bp_AB},
        bp_BC.(bp_proj2) ∘ bp_A_BC.(bp_proj2)
      ⟩{bp_AB_C};
    iso_bwd :=
      ⟨ bp_AB.(bp_proj1) ∘ bp_AB_C.(bp_proj1),
        ⟨bp_AB.(bp_proj2) ∘ bp_AB_C.(bp_proj1),
            bp_AB_C.(bp_proj2)⟩{bp_BC}
      ⟩{bp_A_BC};
  |}.
  - (* bwd ∘ fwd = id P_A_BC *)
    rewrite pair_comp.
    symmetry.
    rewrite (bp_A_BC.(bp_uniq) (C.(id) P_A_BC)).
    rewrite C.(id_right). rewrite C.(id_right). f_equal.
    + rewrite <- C.(comp_assoc). rewrite bp_AB_C.(bp_beta1).
      symmetry. apply bp_AB.(bp_beta1).
    + transitivity (⟨bp_BC.(bp_proj1) ∘ bp_A_BC.(bp_proj2),
                     bp_BC.(bp_proj2) ∘ bp_A_BC.(bp_proj2)⟩{bp_BC}).
      * apply bp_BC.(bp_uniq).
      * rewrite pair_comp. f_equal.
        -- rewrite <- C.(comp_assoc). rewrite bp_AB_C.(bp_beta1).
           symmetry. apply bp_AB.(bp_beta2).
        -- symmetry. apply bp_AB_C.(bp_beta2).
  - (* fwd ∘ bwd = id P_AB_C *)
    rewrite pair_comp.
    symmetry.
    rewrite (bp_AB_C.(bp_uniq) (C.(id) P_AB_C)).
    rewrite C.(id_right). rewrite C.(id_right). f_equal.
    + transitivity (⟨bp_AB.(bp_proj1) ∘ bp_AB_C.(bp_proj1),
                     bp_AB.(bp_proj2) ∘ bp_AB_C.(bp_proj1)⟩{bp_AB}).
      * apply bp_AB.(bp_uniq).
      * rewrite pair_comp. f_equal.
        -- symmetry. apply bp_A_BC.(bp_beta1).
        -- rewrite <- C.(comp_assoc). rewrite bp_A_BC.(bp_beta2).
           symmetry. apply bp_BC.(bp_beta1).
    + rewrite <- C.(comp_assoc). rewrite bp_A_BC.(bp_beta2).
      symmetry. apply bp_BC.(bp_beta2).
Qed.
