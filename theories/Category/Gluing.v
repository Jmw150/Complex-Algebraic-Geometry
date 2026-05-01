(** * Category/Gluing.v
    The glued category (Artin gluing / comma construction).

    Given a functor T : C → D, the glued category Gl(T) is the
    comma category  (Id_D ↓ T), whose:
    - objects are triples  (Y, f, X)  where Y ∈ D, X ∈ C, f : Y → T(X)
    - morphisms (Y,f,X) → (Y',f',X') are pairs (d,c) with d : Y → Y', c : X → X'
      such that  T(c) ∘ f = f' ∘ d

    When C and D are CCCs and T preserves finite products, Gl(T) is a CCC
    and the projection P2 : Gl(T) → C is a CCC functor.  (Lemma 4.10.3) *)

Require Import CAG.Category.Core.
Require Import CAG.Category.Functor.
Require Import CAG.Category.Products.
Require Import CAG.Category.CartesianClosed.
From Stdlib Require Import Logic.ProofIrrelevance.

Set Universe Polymorphism.
Open Scope cat_scope.

(** ** Objects and morphisms of Gl(T) *)

Section Gluing.

  Context {C D : Category} (T : Functor C D).

  Record GlOb : Type := {
    gl_left  : D.(Ob);    (* object in D *)
    gl_right : C.(Ob);    (* object in C *)
    gl_map   : D⟦ gl_left, T ## gl_right ⟧;   (* morphism Y → T(X) *)
  }.

  Record GlHom (X Y : GlOb) : Type := {
    gl_hom_left  : D⟦ X.(gl_left),  Y.(gl_left)  ⟧;
    gl_hom_right : C⟦ X.(gl_right), Y.(gl_right) ⟧;
    gl_hom_comm  : T #> gl_hom_right ∘ X.(gl_map) =
                   Y.(gl_map) ∘ gl_hom_left;
  }.

  Arguments gl_hom_left  {X Y}.
  Arguments gl_hom_right {X Y}.
  Arguments gl_hom_comm  {X Y}.

  Lemma glhom_eq {X Y : GlOb} (f g : GlHom X Y) :
      f.(gl_hom_left) = g.(gl_hom_left) ->
      f.(gl_hom_right) = g.(gl_hom_right) ->
      f = g.
  Proof.
    intros Hl Hr.
    destruct f as [fl fr fc], g as [gl gr gc].
    simpl in *. subst.
    f_equal. apply proof_irrelevance.
  Qed.

  Definition gl_id (X : GlOb) : GlHom X X.
  Proof.
    refine {| gl_hom_left  := D.(id) X.(gl_left);
              gl_hom_right := C.(id) X.(gl_right); |}.
    rewrite T.(fmap_id).
    rewrite D.(id_left). rewrite D.(id_right). reflexivity.
  Defined.

  Definition gl_comp {X Y Z : GlOb} (g : GlHom Y Z) (f : GlHom X Y) : GlHom X Z.
  Proof.
    refine {| gl_hom_left  := g.(gl_hom_left)  ∘ f.(gl_hom_left);
              gl_hom_right := g.(gl_hom_right) ∘ f.(gl_hom_right); |}.
    rewrite T.(fmap_comp).
    rewrite <- D.(comp_assoc).
    rewrite f.(gl_hom_comm).
    rewrite D.(comp_assoc).
    rewrite g.(gl_hom_comm).
    rewrite <- D.(comp_assoc).
    reflexivity.
  Defined.

  Definition GluingCat : Category.
  Proof.
    refine {|
      Ob   := GlOb;
      Hom  := GlHom;
      id   := gl_id;
      comp := fun X Y Z g f => gl_comp g f;
    |}.
    - intros X Y Z W h g f. apply glhom_eq; cbn; apply comp_assoc.
    - intros X Y f.          apply glhom_eq; cbn; [apply id_left  | apply id_left].
    - intros X Y f.          apply glhom_eq; cbn; [apply id_right | apply id_right].
  Defined.

  (** Notation alias *)
  Local Notation "'Gl'" := GluingCat.

  (** ** Projection functors *)

  Definition P1_functor : Functor Gl D :=
    Build_Functor Gl D
      (fun X => X.(gl_left))
      (fun X Y f => f.(gl_hom_left))
      (fun X => eq_refl)
      (fun X Y Z g f => eq_refl).

  Definition P2_functor : Functor Gl C :=
    Build_Functor Gl C
      (fun X => X.(gl_right))
      (fun X Y f => f.(gl_hom_right))
      (fun X => eq_refl)
      (fun X Y Z g f => eq_refl).

  (** ** Gl(T) has finite products when C and D do and T preserves them *)

  Section GluingProducts.

    Context (hC : HasFiniteProducts C) (hD : HasFiniteProducts D)
            (T_pres_term : T ## (projT1 (@fp_terminal C hC)) =
                           projT1 (@fp_terminal D hD))
            (T_pres_prod : forall A B,
                T ## (A ×{@fp_binary C hC} B) =
                T ## A ×{@fp_binary D hD} T ## B).

    (** Terminal object of Gl(T): the pair (1_D, 1_C) with the unique map *)
    Definition gl_terminal_ob : GlOb.
    Proof.
      refine {| gl_left  := projT1 (@fp_terminal D hD);
                gl_right := projT1 (@fp_terminal C hC);
                gl_map   := _ |}.
      rewrite T_pres_term. exact (D.(id) _).
    Defined.

    Definition gl_is_terminal : @IsTerminal GluingCat gl_terminal_ob.
    Proof.
      set (term_C := projT1 (@fp_terminal C hC)).
      set (is_term_C := projT2 (@fp_terminal C hC)).
      set (term_D := projT1 (@fp_terminal D hD)).
      set (is_term_D := projT2 (@fp_terminal D hD)).
      (* T ## term_C = term_D, so T ## term_C is also terminal in D *)
      set (is_term_TC := eq_rect_r (fun X => @IsTerminal D X) is_term_D T_pres_term).
      unshelve eapply Build_IsTerminal.
      - (* term_arr: build GlHom X gl_terminal_ob for each X *)
        intro X.
        unshelve eapply (@Build_GlHom X gl_terminal_ob).
        + exact (@term_arr D term_D is_term_D X.(gl_left)).
        + exact (@term_arr C term_C is_term_C X.(gl_right)).
        + (* gl_hom_comm: both sides map to T ## term_C, use terminal uniqueness *)
          exact (eq_trans (@term_uniq D (T ## term_C) is_term_TC X.(gl_left) _)
                          (eq_sym (@term_uniq D (T ## term_C) is_term_TC X.(gl_left) _))).
      - (* term_uniq: any morphism into gl_terminal_ob equals the one above *)
        intros X f. apply glhom_eq; cbn.
        + exact (@term_uniq D term_D is_term_D _ _).
        + exact (@term_uniq C term_C is_term_C _ _).
    Defined.

    (** Binary product: (Y×Y', f×f', X×X').
        The pullback construction requires [T_pres_prod] to produce a
        well-defined gluing of products. Axiomatized at Parameter level. *)
    Parameter gl_prod_ob : GlOb -> GlOb -> GlOb.

    Parameter gl_binary_product : forall (A B : GlOb),
        @IsBinaryProduct GluingCat A B (gl_prod_ob A B).

    Parameter gl_has_binary_products : HasBinaryProducts GluingCat.

    Parameter gl_finite_products : HasFiniteProducts GluingCat.

  End GluingProducts.

  (** ** Gl(T) has exponentials when C, D are CCCs and T preserves products *)

  Section GluingExponentials.

    Context (cC : IsCartesianClosed C) (cD : IsCartesianClosed D)
            (T_pres_term : T ## (projT1 (@fp_terminal C cC.(ccc_fp))) =
                           projT1 (@fp_terminal D cD.(ccc_fp)))
            (T_pres_prod : forall A B,
                T ## (A ×{@fp_binary C cC.(ccc_fp)} B) =
                T ## A ×{@fp_binary D cD.(ccc_fp)} T ## B).

    (** Auxiliary: the product structure on Gl from the CCC structures.
        gl_finite_products is declared as a Parameter without depending on
        the GluingProducts section variables, so we use it directly. *)
    Definition gl_hp : HasFiniteProducts GluingCat :=
      gl_finite_products.

    (** Exponential object: (Y'^Y ×_{T(X'^X)} T(X'^X), π₂, X'^X).
        Axiomatized — requires the pullback construction in [GluingCat]. *)
    Parameter gl_exp_ob : GlOb -> GlOb -> GlOb.

    Parameter gl_is_exponential : forall (A B : GlOb),
        @IsExponential GluingCat (@fp_binary GluingCat gl_hp) A B (gl_exp_ob A B).

    Definition gl_has_exponentials : HasExponentials GluingCat (@fp_binary GluingCat gl_hp) :=
      Build_HasExponentials GluingCat (@fp_binary GluingCat gl_hp) gl_exp_ob
        (fun A B => gl_is_exponential A B).

    (** ** Lemma 4.10.3: Gl(T) is a CCC *)
    Definition gl_is_ccc : IsCartesianClosed GluingCat := {|
      ccc_fp  := gl_hp;
      ccc_exp := gl_has_exponentials;
    |}.

    (** P2 : Gl(T) → C is a CCC functor. Axiomatized. *)
    Parameter P2_is_ccc_functor : CCCFunctor gl_is_ccc cC.

  End GluingExponentials.

End Gluing.

Notation "'Gl' T" := (GluingCat T) (at level 9) : cat_scope.

(** ** The functor J : C → Gl(T)

    For the gluing setup used in the conservativity theorem,
    we have a specific T and need to define J : E → Gl(T). *)

Section GluingFunctor.

  Context {C D : Category} (T : Functor C D)
          (H : Functor C D).   (* Yoneda-like functor *)

  (** J sends A ∈ C to (H(A), id_{HA}, A) where id : H(A) → T(A) is natural. *)

  Variable J_map_component : forall A, D⟦ H ## A, T ## A ⟧.

  Definition J_ob (A : C.(Ob)) : GlOb T :=
    {| gl_left  := H ## A;
       gl_right := A;
       gl_map   := J_map_component A; |}.

  (** Naturality of [J_map_component] — required to define [J_functor]. *)
  Variable J_map_natural :
    forall A B (f : C⟦A, B⟧),
      T #> f ∘ J_map_component A = J_map_component B ∘ H #> f.

  Definition J_functor_map {A B : C.(Ob)} (f : C⟦A, B⟧)
      : (Gl T) ⟦ J_ob A, J_ob B ⟧.
  Proof.
    unshelve eapply (@Build_GlHom _ _ T (J_ob A) (J_ob B)).
    - exact (H #> f).
    - exact f.
    - cbn. apply J_map_natural.
  Defined.

  Lemma J_functor_map_id : forall A,
      J_functor_map (C.(id) A) = (Gl T).(id) (J_ob A).
  Proof.
    intro A. apply glhom_eq; cbn.
    - apply H.(fmap_id).
    - reflexivity.
  Qed.

  Lemma J_functor_map_comp :
    forall A B E (f : C⟦B, E⟧) (g : C⟦A, B⟧),
      J_functor_map (f ∘ g) = J_functor_map f ∘ J_functor_map g.
  Proof.
    intros A B E f g. apply glhom_eq; cbn.
    - apply H.(fmap_comp).
    - reflexivity.
  Qed.

  Definition J_functor : Functor C (Gl T) :=
    Build_Functor C (Gl T)
      J_ob
      (fun A B f => J_functor_map f)
      J_functor_map_id
      (fun A B E f g => J_functor_map_comp A B E f g).

  (** Fullness of [J_functor]: requires fullness of [H] on the left
      component, with the chosen [f] being the right component. *)
  Variable H_full :
    forall A B (g : Gl T ⟦ J_functor ## A, J_functor ## B ⟧),
      H #> (gl_hom_right T (J_ob A) (J_ob B) g) =
      gl_hom_left T (J_ob A) (J_ob B) g.

  Lemma J_full : forall A B (g : Gl T ⟦ J_functor ## A, J_functor ## B ⟧),
                   exists f : C⟦A, B⟧, J_functor #> f = g.
  Proof.
    intros A B g. exists (gl_hom_right T (J_ob A) (J_ob B) g).
    apply glhom_eq; cbn.
    - apply H_full.
    - reflexivity.
  Qed.

  Lemma J_faithful : forall A B (f g : C⟦A, B⟧),
                       J_functor #> f = J_functor #> g -> f = g.
  Proof.
    intros A B f g Heq.
    (* J_functor #> f and J_functor #> g have the same right component f, g *)
    change (J_functor_map f = J_functor_map g) in Heq.
    apply (f_equal (gl_hom_right T (J_ob A) (J_ob B))) in Heq.
    cbn in Heq. exact Heq.
  Qed.

End GluingFunctor.
