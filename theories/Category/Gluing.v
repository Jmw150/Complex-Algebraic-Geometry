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

(* CAG constructive-remove Record GlHom theories/Category/Gluing.v:34 BEGIN -- constructive downstream cleanup: missing GluingCat
  Record GlHom (X Y : GlOb) : Type := {
    gl_hom_left  : D⟦ X.(gl_left),  Y.(gl_left)  ⟧;
    gl_hom_right : C⟦ X.(gl_right), Y.(gl_right) ⟧;
    gl_hom_comm  : T #> gl_hom_right ∘ X.(gl_map) =
                   Y.(gl_map) ∘ gl_hom_left;
  }.
   CAG constructive-remove Record GlHom theories/Category/Gluing.v:34 END *)

  (* CAG constructive-remove Command Arguments theories/Category/Gluing.v:43 BEGIN -- missing gl_hom_left
Arguments gl_hom_left  {X Y}.

   CAG constructive-remove Command Arguments theories/Category/Gluing.v:43 END *)
  (* CAG constructive-remove Command Arguments theories/Category/Gluing.v:47 BEGIN -- missing gl_hom_right
Arguments gl_hom_right {X Y}.

   CAG constructive-remove Command Arguments theories/Category/Gluing.v:47 END *)
  (* CAG constructive-remove Command Arguments theories/Category/Gluing.v:51 BEGIN -- missing gl_hom_comm
Arguments gl_hom_comm  {X Y}.

   CAG constructive-remove Command Arguments theories/Category/Gluing.v:51 END *)

(* CAG zero-dependent Lemma glhom_eq theories/Category/Gluing.v:45 BEGIN
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
   CAG zero-dependent Lemma glhom_eq theories/Category/Gluing.v:45 END *)

(* CAG constructive-remove Definition gl_id theories/Category/Gluing.v:58 BEGIN -- constructive downstream cleanup: missing GluingCat
  Definition gl_id (X : GlOb) : GlHom X X.
  Proof.
    refine {| gl_hom_left  := D.(id) X.(gl_left);
              gl_hom_right := C.(id) X.(gl_right); |}.
    rewrite T.(fmap_id).
    rewrite D.(id_left). rewrite D.(id_right). reflexivity.
  Defined.
   CAG constructive-remove Definition gl_id theories/Category/Gluing.v:58 END *)

(* CAG constructive-remove Definition gl_comp theories/Category/Gluing.v:66 BEGIN -- constructive downstream cleanup: missing GluingCat
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
   CAG constructive-remove Definition gl_comp theories/Category/Gluing.v:66 END *)

(* CAG zero-dependent Definition GluingCat theories/Category/Gluing.v:77 BEGIN
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
   CAG zero-dependent Definition GluingCat theories/Category/Gluing.v:77 END *)

  (** Notation alias *)
  (* CAG constructive-remove Command Local theories/Category/Gluing.v:110 BEGIN -- missing GluingCat
Local Notation "'Gl'" := GluingCat.

   CAG constructive-remove Command Local theories/Category/Gluing.v:110 END *)

  (** ** Projection functors *)

  (* CAG constructive-remove Command Definition theories/Category/Gluing.v:117 BEGIN -- missing Gl
Definition P1_functor : Functor Gl D :=
    Build_Functor Gl D
      (fun X => X.(gl_left))
      (fun X Y f => f.(gl_hom_left))
      (fun X => eq_refl)
      (fun X Y Z g f => eq_refl).

   CAG constructive-remove Command Definition theories/Category/Gluing.v:117 END *)

  (* CAG constructive-remove Command Definition theories/Category/Gluing.v:127 BEGIN -- missing Gl
Definition P2_functor : Functor Gl C :=
    Build_Functor Gl C
      (fun X => X.(gl_right))
      (fun X Y f => f.(gl_hom_right))
      (fun X => eq_refl)
      (fun X Y Z g f => eq_refl).

   CAG constructive-remove Command Definition theories/Category/Gluing.v:127 END *)

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

(* CAG zero-dependent Definition gl_is_terminal theories/Category/Gluing.v:129 BEGIN
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
   CAG zero-dependent Definition gl_is_terminal theories/Category/Gluing.v:129 END *)

    (** Binary product: (Y×Y', f×f', X×X') *)
    (* CAG constructive-remove Definition gl_prod_ob theories/Category/Gluing.v:183 BEGIN
    Definition gl_prod_ob (A B : GlOb) : GlOb.
    Proof.
      Admitted.
       CAG constructive-remove Definition gl_prod_ob theories/Category/Gluing.v:183 END *)

(* CAG zero-dependent Definition gl_binary_product theories/Category/Gluing.v:157 BEGIN
    Definition gl_binary_product (A B : GlOb) :
        @IsBinaryProduct GluingCat A B (gl_prod_ob A B).
    Proof.
      Admitted.
   CAG zero-dependent Definition gl_binary_product theories/Category/Gluing.v:157 END *)

(* CAG zero-dependent Definition gl_has_binary_products theories/Category/Gluing.v:162 BEGIN
    Definition gl_has_binary_products : HasBinaryProducts GluingCat.
    Proof.
      Admitted.
   CAG zero-dependent Definition gl_has_binary_products theories/Category/Gluing.v:162 END *)

(* CAG zero-dependent Definition gl_finite_products theories/Category/Gluing.v:166 BEGIN
    Definition gl_finite_products : HasFiniteProducts GluingCat.
    Proof.
      Admitted.
   CAG zero-dependent Definition gl_finite_products theories/Category/Gluing.v:166 END *)

  End GluingProducts.

  (** ** Gl(T) has exponentials when C, D are CCCs and T preserves products *)

  Section GluingExponentials.

    Context (cC : IsCartesianClosed C) (cD : IsCartesianClosed D)
            (T_pres_term : T ## (projT1 (@fp_terminal C cC.(ccc_fp))) =
                           projT1 (@fp_terminal D cD.(ccc_fp)))
            (T_pres_prod : forall A B,
                T ## (A ×{@fp_binary C cC.(ccc_fp)} B) =
                T ## A ×{@fp_binary D cD.(ccc_fp)} T ## B).

    (** Auxiliary: the product structure on Gl from the CCC structures *)
(* CAG zero-dependent Definition gl_hp theories/Category/Gluing.v:184 BEGIN
    Definition gl_hp : HasFiniteProducts GluingCat :=
      gl_finite_products cC.(ccc_fp) cD.(ccc_fp) T_pres_term T_pres_prod.
   CAG zero-dependent Definition gl_hp theories/Category/Gluing.v:184 END *)

    (** Exponential object: (Y'^Y ×_{T(X'^X)} T(X'^X), π₂, X'^X)
        This requires a pullback; we admit the details. *)
    (* CAG constructive-remove Definition gl_exp_ob theories/Category/Gluing.v:227 BEGIN
    Definition gl_exp_ob (A B : GlOb) : GlOb.
    Proof.
      Admitted.
       CAG constructive-remove Definition gl_exp_ob theories/Category/Gluing.v:227 END *)

(* CAG zero-dependent Definition gl_is_exponential theories/Category/Gluing.v:193 BEGIN
    Definition gl_is_exponential (A B : GlOb) :
        @IsExponential GluingCat (@fp_binary GluingCat gl_hp) A B (gl_exp_ob A B).
    Proof.
      Admitted.
   CAG zero-dependent Definition gl_is_exponential theories/Category/Gluing.v:193 END *)

(* CAG zero-dependent Definition gl_has_exponentials theories/Category/Gluing.v:198 BEGIN
    Definition gl_has_exponentials : HasExponentials GluingCat (@fp_binary GluingCat gl_hp) :=
      Build_HasExponentials GluingCat (@fp_binary GluingCat gl_hp) gl_exp_ob
        (fun A B => gl_is_exponential A B).
   CAG zero-dependent Definition gl_has_exponentials theories/Category/Gluing.v:198 END *)

    (** ** Lemma 4.10.3: Gl(T) is a CCC *)
(* CAG zero-dependent Definition gl_is_ccc theories/Category/Gluing.v:203 BEGIN
    Definition gl_is_ccc : IsCartesianClosed GluingCat := {|
      ccc_fp  := gl_hp;
      ccc_exp := gl_has_exponentials;
    |}.
   CAG zero-dependent Definition gl_is_ccc theories/Category/Gluing.v:203 END *)

    (** P2 : Gl(T) → C is a CCC functor *)
(* CAG zero-dependent Definition P2_is_ccc_functor theories/Category/Gluing.v:209 BEGIN
    Definition P2_is_ccc_functor : CCCFunctor gl_is_ccc cC.
    Proof.
      Admitted.
   CAG zero-dependent Definition P2_is_ccc_functor theories/Category/Gluing.v:209 END *)

  End GluingExponentials.

End Gluing.

(* CAG constructive-remove Command Notation theories/Category/Gluing.v:263 BEGIN -- missing GluingCat
Notation "'Gl' T" := (GluingCat T) (at level 9) : cat_scope.

   CAG constructive-remove Command Notation theories/Category/Gluing.v:263 END *)

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

(* CAG zero-dependent Axiom J_functor theories/Category/Gluing.v:238 BEGIN
  Axiom J_functor : Functor C (Gl T).
   CAG zero-dependent Axiom J_functor theories/Category/Gluing.v:238 END *)

(* CAG zero-dependent Axiom J_full theories/Category/Gluing.v:240 BEGIN
  Axiom J_full    : forall A B (g : Gl T ⟦ J_functor ## A, J_functor ## B ⟧),
                      exists f : C⟦A, B⟧, J_functor #> f = g.
   CAG zero-dependent Axiom J_full theories/Category/Gluing.v:240 END *)

(* CAG zero-dependent Axiom J_faithful theories/Category/Gluing.v:243 BEGIN
  Axiom J_faithful : forall A B (f g : C⟦A, B⟧),
                       J_functor #> f = J_functor #> g -> f = g.
   CAG zero-dependent Axiom J_faithful theories/Category/Gluing.v:243 END *)

End GluingFunctor.
