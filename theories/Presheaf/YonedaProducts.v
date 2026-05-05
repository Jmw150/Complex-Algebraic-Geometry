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

  Lemma psh_fst_pair {F G H : Functor C TypeCat}
      (α : NatTrans H F) (β : NatTrans H G) :
    NatComp (psh_fst F G) (psh_pair α β) = α.
  Proof.
    apply nattrans_eq. intros X.
    extensionality hx. reflexivity.
  Qed.

  Lemma psh_snd_pair {F G H : Functor C TypeCat}
      (α : NatTrans H F) (β : NatTrans H G) :
    NatComp (psh_snd F G) (psh_pair α β) = β.
  Proof.
    apply nattrans_eq. intros X.
    extensionality hx. reflexivity.
  Qed.

  Lemma psh_pair_eta {F G H : Functor C TypeCat}
      (γ : NatTrans H (psh_prod_obj F G)) :
    γ =
    psh_pair (NatComp (psh_fst F G) γ)
             (NatComp (psh_snd F G) γ).
  Proof.
    apply nattrans_eq. intros X.
    extensionality hx.
    cbn. apply surjective_pairing.
  Qed.

  Record PresheafBinaryProduct (F G P : Functor C TypeCat) : Type := {
    psh_product_fst : NatTrans P F;
    psh_product_snd : NatTrans P G;
    psh_product_pair : forall H,
      NatTrans H F -> NatTrans H G -> NatTrans H P;
    psh_product_beta_fst : forall H
      (α : NatTrans H F) (β : NatTrans H G),
      NatComp psh_product_fst (psh_product_pair H α β) = α;
    psh_product_beta_snd : forall H
      (α : NatTrans H F) (β : NatTrans H G),
      NatComp psh_product_snd (psh_product_pair H α β) = β;
    psh_product_eta : forall H (γ : NatTrans H P),
      γ =
      psh_product_pair H
        (NatComp psh_product_fst γ)
        (NatComp psh_product_snd γ);
  }.

  Definition psh_prod_is_product (F G : Functor C TypeCat) :
      PresheafBinaryProduct F G (psh_prod_obj F G).
  Proof.
    refine {|
      psh_product_fst := psh_fst F G;
      psh_product_snd := psh_snd F G;
      psh_product_pair := fun H α β => psh_pair α β;
      psh_product_beta_fst := _;
      psh_product_beta_snd := _;
      psh_product_eta := _;
    |}.
    - intros H α β. apply psh_fst_pair.
    - intros H α β. apply psh_snd_pair.
    - intros H γ. apply psh_pair_eta.
  Defined.

End PresheafProduct.

(** ** The Yoneda embedding preserves finite products

    H[A × B] ≅ H[A] × H[B] as presheaves on C. *)

Section YonedaPreservesProducts.

  Context {C : Category} (hp : HasBinaryProducts C).

  (** H^[A × B] is pointwise equivalent to H^[A] × H^[B].  This is the
      object-level content behind product preservation by the Yoneda
      embedding A ↦ C(-, A), expressed against the concrete chosen binary
      product [hp]. *)
  Definition yoneda_product_forward (A B X : C.(Ob)) :
      (H^[A ×{hp} B] ## X) -> (H^[A] ## X * H^[B] ## X)%type :=
    fun f =>
      (bp_proj1 (prod_bp hp A B) ∘ f,
       bp_proj2 (prod_bp hp A B) ∘ f).

  Definition yoneda_product_backward (A B X : C.(Ob)) :
      (H^[A] ## X * H^[B] ## X)%type -> (H^[A ×{hp} B] ## X) :=
    fun fg => bp_pair (prod_bp hp A B) (fst fg) (snd fg).

  Lemma yoneda_product_forward_backward (A B X : C.(Ob))
      (fg : (H^[A] ## X * H^[B] ## X)%type) :
    yoneda_product_forward A B X (yoneda_product_backward A B X fg) = fg.
  Proof.
    destruct fg as [f g].
    unfold yoneda_product_forward, yoneda_product_backward.
    cbn. rewrite bp_beta1, bp_beta2. reflexivity.
  Qed.

  Lemma yoneda_product_backward_forward (A B X : C.(Ob))
      (f : H^[A ×{hp} B] ## X) :
    yoneda_product_backward A B X (yoneda_product_forward A B X f) = f.
  Proof.
    unfold yoneda_product_forward, yoneda_product_backward.
    cbn. symmetry. apply bp_uniq.
  Qed.

  Record YonedaPreservesProductData (A B : C.(Ob)) : Type := {
    ypp_forward : forall X,
      (H^[A ×{hp} B] ## X) -> (H^[A] ## X * H^[B] ## X)%type;
    ypp_backward : forall X,
      (H^[A] ## X * H^[B] ## X)%type -> (H^[A ×{hp} B] ## X);
    ypp_forward_backward : forall X fg,
      ypp_forward X (ypp_backward X fg) = fg;
    ypp_backward_forward : forall X f,
      ypp_backward X (ypp_forward X f) = f;
  }.

  Definition yoneda_preserves_product (A B : C.(Ob)) :
      YonedaPreservesProductData A B.
  Proof.
    refine {|
      ypp_forward := yoneda_product_forward A B;
      ypp_backward := yoneda_product_backward A B;
      ypp_forward_backward := yoneda_product_forward_backward A B;
      ypp_backward_forward := yoneda_product_backward_forward A B;
    |}.
  Defined.

(* CAG zero-dependent Admitted yoneda_preserves_product theories/Presheaf/YonedaProducts.v:97 BEGIN
  Lemma yoneda_preserves_product (A B : C.(Ob)) :
      forall X : C.(Ob),
        (H[A ×{hp} B] ## X) = (H[A] ## X * H[B] ## X)%type.
  Proof.
    Admitted.
   CAG zero-dependent Admitted yoneda_preserves_product theories/Presheaf/YonedaProducts.v:97 END *)

End YonedaPreservesProducts.

(** ** Yoneda preserves finite products (general version) *)

Record YonedaPreservesFiniteProductsData {C : Category}
    (hp : HasFiniteProducts C) : Type := {
  ypfp_binary : forall A B : C.(Ob),
    @YonedaPreservesProductData C (@fp_binary C hp) A B;
}.

Definition yoneda_preserves_finite_products {C : Category}
    (hp : HasFiniteProducts C) : YonedaPreservesFiniteProductsData hp.
Proof.
  refine {| ypfp_binary := fun A B => @yoneda_preserves_product C (@fp_binary C hp) A B |}.
Defined.

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
