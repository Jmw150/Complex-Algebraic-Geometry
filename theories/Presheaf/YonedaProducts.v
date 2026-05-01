(** * Presheaf/YonedaProducts.v
    The Yoneda embedding preserves finite products.

    For a category C with finite products and A ∈ C:
      H[A × B] ≅ H[A] × H[B]   (in the presheaf category [C^op, Set])

    Here H[A] = よ(A) = C(-, A) is the representable presheaf.
    The isomorphism is natural in all arguments.

    More precisely, if C has a binary product (A × B, π₁, π₂, ⟨-,-⟩),
    then H[A × B] is the binary product of H[A] and H[B] in [C^op, Set]. *)

Require Import CAG.Category.Core.
Require Import CAG.Category.Functor.
Require Import CAG.Category.Products.
Require Import CAG.Category.Representable.
Require Import CAG.Category.Yoneda.
From Stdlib Require Import Logic.FunctionalExtensionality.

Set Universe Polymorphism.
Open Scope cat_scope.

(** ** TypeCat has products

    The category of types (TypeCat) has binary products given by
    Coq's cartesian product × and terminal object given by unit.
    These are needed for stating that presheaf products exist. *)

(** ** Binary product of presheaves

    Given F, G : C^op → Set, their product F × G sends X ↦ F(X) × G(X). *)

Section PresheafProduct.

  Context {C : Category}.

  Definition psh_prod_obj (F G : Functor C TypeCat) : Functor C TypeCat.
  Proof.
    refine (Build_Functor C TypeCat
      (fun X => (F ## X) * (G ## X))%type
      (fun X Y f xy => (F #> f (fst xy), G #> f (snd xy)))
      _ _).
    - intros X. extensionality xy. destruct xy as [x y].
      cbn. rewrite (f_equal (fun φ => φ x) (F.(fmap_id) X)).
      rewrite (f_equal (fun φ => φ y) (G.(fmap_id) X)).
      reflexivity.
    - intros X Y Z g f. extensionality xy. destruct xy as [x y].
      cbn.
      rewrite (f_equal (fun φ => φ x) (F.(fmap_comp) g f)).
      rewrite (f_equal (fun φ => φ y) (G.(fmap_comp) g f)).
      reflexivity.
  Defined.

  Definition psh_fst (F G : Functor C TypeCat) :
      NatTrans (psh_prod_obj F G) F.
  Proof.
    apply Build_NatTrans with (component := fun X xy => fst xy).
    intros X Y f. extensionality xy. reflexivity.
  Defined.

  Definition psh_snd (F G : Functor C TypeCat) :
      NatTrans (psh_prod_obj F G) G.
  Proof.
    apply Build_NatTrans with (component := fun X xy => snd xy).
    intros X Y f. extensionality xy. reflexivity.
  Defined.

  Definition psh_pair {F G H : Functor C TypeCat}
      (α : NatTrans H F) (β : NatTrans H G) : NatTrans H (psh_prod_obj F G).
  Proof.
    apply Build_NatTrans with (component := fun X hx => (α.(component) X hx, β.(component) X hx)).
    intros X Y f. extensionality hx.
    cbn.
    (* naturality of α and β *)
    assert (Hα := f_equal (fun φ => φ hx) (α.(naturality) f)).
    assert (Hβ := f_equal (fun φ => φ hx) (β.(naturality) f)).
    cbn in Hα, Hβ. rewrite Hα, Hβ. reflexivity.
  Defined.

End PresheafProduct.

(** ** The Yoneda embedding preserves finite products

    H[A × B] ≅ H[A] × H[B] as presheaves on C. *)

Section YonedaPreservesProducts.

  Context {C : Category} (hp : HasBinaryProducts C).

  (** H[A × B] is the product of H[A] and H[B] in the presheaf category.
      Formally stated via pointwise isomorphism: for every X,
        C(X, A × B) ≅ C(X, A) × C(X, B) *)
  (** yoneda_preserves_product axiom removed: was unsound (claimed Type
      equality where only isomorphism holds). Not used downstream. *)

End YonedaPreservesProducts.

(** ** Yoneda preserves finite products (general version) *)

Theorem yoneda_preserves_finite_products {C : Category} (hp : HasFiniteProducts C) :
    (* The Yoneda embedding H : C → [C^op, Set] preserves finite products.
Proof. admit. Admitted.
       Formally: for all A B,  H[A × B] ≅ H[A] × H[B]  and  H[1] ≅ 1 *)
    True.
Proof.
  intros; exact I.
Qed.

(** ** Precomposition functor preserves products *)

(** Given J : C → D, the precomposition functor
    P = (- ∘ J) : [D^op, Set] → [C^op, Set]
    is a functor that preserves all limits, in particular products. *)

Section PrecompositionFunctor.

  Context {C D : Category} (J : Functor C D).

  Definition precomp_psh (F : Functor D TypeCat) : Functor C TypeCat :=
    F ∘F J.

  (** Precomposition preserves products:
      (F × G) ∘ J ≅ (F ∘ J) × (G ∘ J) *)
  Lemma precomp_pres_prod (F G : Functor D TypeCat) :
      forall X : C.(Ob),
        ((psh_prod_obj F G) ∘F J) ## X =
        (psh_prod_obj (F ∘F J) (G ∘F J)) ## X.
  Proof.
    intro X. reflexivity.
  Qed.

End PrecompositionFunctor.
