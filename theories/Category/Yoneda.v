(** * Category/Yoneda.v
    Yoneda embedding, Yoneda lemma (objectwise and natural). *)

Require Import CAG.Category.Core.
Require Import CAG.Category.Functor.
Require Import CAG.Category.Representable.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.

Set Universe Polymorphism.
Open Scope cat_scope.

(** ** Yoneda lemma — objectwise form

    For F : C -> TypeCat and A ∈ C:
      Nat(H[A], F)  ≅  F(A)

    Forward:  Φ(α) := α_A(id_A)
    Backward: Ψ(a)_B(f) := F(f)(a)
*)

Section YonedaLemma.

  Context {C : Category} (F : Functor C TypeCat).

  (** *** Forward map Φ *)
  Definition yoneda_forward (A : C.(Ob)) (α : NatTrans H[A] F) : F ## A :=
    α.(component) A (C.(id) A).

  (** *** Backward map Ψ *)
  Definition yoneda_backward (A : C.(Ob)) (a : F ## A) : NatTrans H[A] F.
  Proof.
    apply Build_NatTrans with (component := fun B (f : C.(Hom) A B) => F #> f a).
    intros B D g.
    extensionality f. cbn.
    symmetry. exact (f_equal (fun φ => φ a) (F.(fmap_comp) g f)).
  Defined.

  (** *** Φ ∘ Ψ = id *)
  Lemma yoneda_bwd_fwd (A : C.(Ob)) (a : F ## A) :
      yoneda_forward A (yoneda_backward A a) = a.
  Proof.
    unfold yoneda_forward. cbn.
    exact (f_equal (fun φ => φ a) (F.(fmap_id) A)).
  Qed.

  (** *** Ψ ∘ Φ = id *)
  Lemma yoneda_fwd_bwd (A : C.(Ob)) (α : NatTrans H[A] F) :
      yoneda_backward A (yoneda_forward A α) = α.
  Proof.
    apply nattrans_eq. intros B. extensionality f.
    unfold yoneda_forward. cbn.
    (* naturality of α: (F g ∘ α_A)(h) = (α_B ∘ H[A] g)(h) *)
    assert (Hnat := f_equal (fun φ => φ (C.(id) A)) (α.(naturality) f)).
    cbn in Hnat.
    rewrite C.(id_right) in Hnat.
    exact Hnat.
  Qed.

End YonedaLemma.

(** ** Yoneda embedding H : C^op -> [C, TypeCat]

    A ↦ H[A],   (h : A' -> A) ↦ H[h] : H[A] ⟹ H[A']. *)

Definition YonedaEmbedding (C : Category) : Functor (C^op) (FunctorCat C TypeCat).
Proof.
  apply (Build_Functor (C^op) (FunctorCat C TypeCat)
    (fun A => HomFunctor_cov (C := C) A)
    (fun A A' h => @HomNatTrans C A A' h)).
  - intros A. apply nattrans_eq. intros B. extensionality f. cbn.
    apply C.(id_right).
  - intros A A' A'' f g.
    apply nattrans_eq. intros B. extensionality h. cbn.
    apply C.(comp_assoc).
Defined.

(** ** Naturality in F

    For β : F ⟹ G, the Yoneda bijection commutes with β:
      β_A(Φ_{A,F}(α)) = Φ_{A,G}(β ∘N α)
*)
Lemma yoneda_natural_in_F {C : Category}
    {F G : Functor C TypeCat} (β : NatTrans F G) (A : C.(Ob))
    (α : NatTrans H[A] F) :
    yoneda_forward G A (NatComp β α) = β.(component) A (yoneda_forward F A α).
Proof.
  unfold yoneda_forward. cbn. reflexivity.
Qed.

(** ** Naturality in A

    For h : A' -> A, the Yoneda bijection commutes with restriction:
      Φ_{A',F}(α ∘N H[h]) = F(h)(Φ_{A,F}(α))
*)
Lemma yoneda_natural_in_A {C : Category}
    (F : Functor C TypeCat) {A A' : C.(Ob)} (h : C⟦A, A'⟧)
    (α : NatTrans H[A] F) :
    yoneda_forward F A' (NatComp α (HomNatTrans h)) =
    F #> h (yoneda_forward F A α).
Proof.
  unfold yoneda_forward. cbn.
  rewrite C.(id_left).
  assert (Hnat := f_equal (fun φ => φ (C.(id) A)) (α.(naturality) h)).
  cbn in Hnat.
  rewrite C.(id_right) in Hnat.
  exact (eq_sym Hnat).
Qed.

(** ** Packaged Yoneda isomorphism *)

Record YonedaIso {C : Category} (F : Functor C TypeCat) (A : C.(Ob)) : Type := {
  yi_forward  : NatTrans H[A] F -> F ## A;
  yi_backward : F ## A -> NatTrans H[A] F;
  yi_bwd_fwd  : forall a, yi_forward (yi_backward a) = a;
  yi_fwd_bwd  : forall α, yi_backward (yi_forward α) = α;
}.

Definition yoneda_iso {C : Category} (F : Functor C TypeCat) (A : C.(Ob)) :
    YonedaIso F A := {|
  yi_forward  := yoneda_forward F A;
  yi_backward := yoneda_backward F A;
  yi_bwd_fwd  := yoneda_bwd_fwd F A;
  yi_fwd_bwd  := yoneda_fwd_bwd F A;
|}.

(** ** Yoneda embedding is fully faithful

    The map A ↦ H[A] is injective on objects (in a suitable sense) and
    the action on morphisms is a bijection. *)

(** The map on morphisms: Hom_C(A', A) -> Nat(H[A], H[A'])
    given by h ↦ HomNatTrans h is a bijection (the Yoneda bijection for F = H[A']). *)

(** Forward: extract the morphism from a natural transformation. *)
Definition yoneda_emb_forward {C : Category} {A A' : C.(Ob)}
    (α : NatTrans H[A] H[A']) : C⟦A', A⟧ :=
  yoneda_forward H[A'] A α.

(** Backward: build a natural transformation from a morphism. *)
Definition yoneda_emb_backward {C : Category} {A A' : C.(Ob)}
    (h : C⟦A', A⟧) : NatTrans H[A] H[A'] :=
  yoneda_backward H[A'] A h.

Lemma yoneda_emb_bwd_fwd {C : Category} {A A' : C.(Ob)} (h : C⟦A', A⟧) :
    yoneda_emb_forward (yoneda_emb_backward h) = h.
Proof.
  unfold yoneda_emb_forward, yoneda_emb_backward.
  exact (yoneda_bwd_fwd H[A'] A h).
Qed.

(* CAG zero-dependent Admitted yoneda_emb_fwd_bwd theories/Category/Yoneda.v:167 BEGIN
Lemma yoneda_emb_fwd_bwd {C : Category} {A A' : C.(Ob)}
    (α : NatTrans H[A] H[A']) :
    yoneda_emb_backward (yoneda_emb_forward α) = α.
Proof.
  unfold yoneda_emb_forward, yoneda_emb_backward.
  exact (yoneda_fwd_bwd H[A'] A α).
Qed.

(** ** Representable functor from a universal element *)

(** Given a ∈ F(A), produce a Representable structure using the Yoneda backward map
    and its inverse. *)
Definition representable_of_element {C : Category} (F : Functor C TypeCat)
    (A : C.(Ob)) (a : F ## A) : IsRepresentation F A a.
Proof.
  Admitted.
   CAG zero-dependent Admitted yoneda_emb_fwd_bwd theories/Category/Yoneda.v:167 END *)

(** Note: [representable_of_element] requires an independent inverse construction.
    The Yoneda lemma tells us: given a ∈ F(A), the nat trans Ψ(a) is an iso
    iff Ψ(a) has an inverse.  The inverse is (Φ_{A,F})^{-1} applied via Yoneda:
    the inverse nat trans sends α_B : F(B) -> C(A,B) via the adjoint transpose.
    In full generality this requires the category to be locally small and F to
    satisfy a representability condition.  We admit this piece for now and record
    the complete Yoneda bijection (yoneda_iso) as the main result. *)
