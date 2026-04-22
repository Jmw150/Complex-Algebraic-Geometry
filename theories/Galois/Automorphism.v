(** * Galois/Automorphism.v
    K-automorphisms of a field extension L/K and their group structure.

    A K-automorphism of L/K is a field automorphism σ : L → L that fixes
    every element in the image of K:  σ(ι(k)) = ι(k) for all k ∈ K.

    The collection Gal(L/K) of all K-automorphisms forms a group under
    composition.  We also build the poset of subgroups of Gal(L/K)
    (ordered by inclusion), which is the other side of the Galois
    correspondence. *)

Require Import CAG.Order.Poset.
Require Import CAG.Galois.Field.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Logic.Classical.
From Stdlib Require Import Logic.PropExtensionality.

Open Scope order_scope.

(** ** Field automorphism *)

(** A field automorphism of L is a ring homomorphism σ : L → L that has a
    two-sided inverse (which is automatically also a ring hom). *)

Record FieldAuto {L : Type} (fL : Field L) : Type := {
  fa_map    : L -> L;
  fa_inv    : L -> L;
  fa_rhom   : RingHom fL.(fld_ring) fL.(fld_ring);
  fa_map_eq : fa_rhom.(rhom_map) = fa_map;
  fa_inv_l  : forall x, fa_inv (fa_map x) = x;
  fa_inv_r  : forall x, fa_map (fa_inv x) = x;
}.

Arguments fa_map    {L fL}.
Arguments fa_inv    {L fL}.
Arguments fa_rhom   {L fL}.
Arguments fa_map_eq {L fL}.
Arguments fa_inv_l  {L fL}.
Arguments fa_inv_r  {L fL}.

(** The identity automorphism. *)
Definition id_auto {L : Type} (fL : Field L) : FieldAuto fL.
Proof.
  refine {|
    fa_map  := fun x => x;
    fa_inv  := fun x => x;
    fa_rhom := {| rhom_map := fun x => x;
                  rhom_add := fun a b => eq_refl _;
                  rhom_mul := fun a b => eq_refl _;
                  rhom_one := eq_refl _ |};
    fa_map_eq := eq_refl;
    fa_inv_l  := fun x => eq_refl;
    fa_inv_r  := fun x => eq_refl;
  |}.
Defined.

(** Composition of automorphisms. *)
Definition comp_auto {L : Type} {fL : Field L}
    (σ τ : FieldAuto fL) : FieldAuto fL.
Proof.
  set (στ_map := fun x => σ.(fa_map) (τ.(fa_map) x)).
  set (στ_rhom := {|
    rhom_map := fun x => σ.(fa_rhom).(rhom_map) (τ.(fa_rhom).(rhom_map) x);
    rhom_add := fun a b =>
      (eq_trans (f_equal σ.(fa_rhom).(rhom_map) (rhom_add τ.(fa_rhom) a b))
                (rhom_add σ.(fa_rhom) _ _));
    rhom_mul := fun a b =>
      (eq_trans (f_equal σ.(fa_rhom).(rhom_map) (rhom_mul τ.(fa_rhom) a b))
                (rhom_mul σ.(fa_rhom) _ _));
    rhom_one :=
      (eq_trans (f_equal σ.(fa_rhom).(rhom_map) (rhom_one τ.(fa_rhom)))
                (rhom_one σ.(fa_rhom)));
  |} : RingHom fL.(fld_ring) fL.(fld_ring)).
  refine {|
    fa_map    := στ_map;
    fa_inv    := fun x => τ.(fa_inv) (σ.(fa_inv) x);
    fa_rhom   := στ_rhom;
    fa_map_eq := _;
    fa_inv_l  := _;
    fa_inv_r  := _;
  |}.
  - (* rhom_map of στ_rhom equals στ_map *)
    unfold στ_rhom, στ_map. cbn.
    apply functional_extensionality. intros x.
    rewrite <- σ.(fa_map_eq), <- τ.(fa_map_eq). reflexivity.
  - intros x. unfold στ_map.
    rewrite σ.(fa_inv_l), τ.(fa_inv_l). reflexivity.
  - intros x. unfold στ_map.
    rewrite τ.(fa_inv_r), σ.(fa_inv_r). reflexivity.
Defined.

(** Inverse automorphism.
    σ^{-1} is also a field automorphism: it preserves ring operations
    because σ does (injectivity argument). *)
Definition inv_auto {L : Type} {fL : Field L} (σ : FieldAuto fL) : FieldAuto fL.
Proof.
  refine {|
    fa_map    := σ.(fa_inv);
    fa_inv    := σ.(fa_map);
    fa_rhom   := {|
      rhom_map := σ.(fa_inv);
      rhom_add := _;
      rhom_mul := _;
      rhom_one := _;
    |};
    fa_map_eq := eq_refl;
    fa_inv_l  := σ.(fa_inv_r);
    fa_inv_r  := σ.(fa_inv_l);
  |}.
  - (* rhom_add: σ.(fa_inv) (a + b) = σ.(fa_inv) a + σ.(fa_inv) b *)
    intros a b. symmetry.
    rewrite <- (σ.(fa_inv_l) (fL.(fld_ring).(cr_add) (σ.(fa_inv) a) (σ.(fa_inv) b))).
    f_equal. rewrite <- σ.(fa_map_eq).
    rewrite σ.(fa_rhom).(rhom_add).
    rewrite σ.(fa_map_eq).
    rewrite σ.(fa_inv_r). rewrite σ.(fa_inv_r). reflexivity.
  - (* rhom_mul: σ.(fa_inv) (a * b) = σ.(fa_inv) a * σ.(fa_inv) b *)
    intros a b. symmetry.
    rewrite <- (σ.(fa_inv_l) (fL.(fld_ring).(cr_mul) (σ.(fa_inv) a) (σ.(fa_inv) b))).
    f_equal. rewrite <- σ.(fa_map_eq).
    rewrite σ.(fa_rhom).(rhom_mul).
    rewrite σ.(fa_map_eq).
    rewrite σ.(fa_inv_r). rewrite σ.(fa_inv_r). reflexivity.
  - (* rhom_one: σ.(fa_inv) 1 = 1 *)
    (* σ maps 1 to 1, so σ^{-1}(1) = σ^{-1}(σ(1)) = 1 *)
    assert (Hmap1 : σ.(fa_map) fL.(fld_ring).(cr_one) = fL.(fld_ring).(cr_one)).
    { rewrite <- σ.(fa_map_eq). exact σ.(fa_rhom).(rhom_one). }
    transitivity (σ.(fa_inv) (σ.(fa_map) fL.(fld_ring).(cr_one))).
    + f_equal. exact (eq_sym Hmap1).
    + exact (σ.(fa_inv_l) fL.(fld_ring).(cr_one)).
Defined.

(** ** K-automorphism (Galois automorphism) *)

(** σ is a K-automorphism of E = (K ↪ L) if it fixes the image of K. *)

Definition IsKAuto (E : FieldExtension) (σ : FieldAuto E.(ext_fL)) : Prop :=
  forall k : E.(ext_base),
    σ.(fa_map) (E.(ext_emb).(rhom_map) k) = E.(ext_emb).(rhom_map) k.

(** The Galois group Gal(L/K): K-automorphisms of L. *)

Definition GaloisGroup (E : FieldExtension) : Type :=
  { σ : FieldAuto E.(ext_fL) | IsKAuto E σ }.

(** The identity is a K-automorphism. *)
Lemma id_is_kaut (E : FieldExtension) : IsKAuto E (id_auto E.(ext_fL)).
Proof.
  intros k. reflexivity.
Qed.

(** Composition of K-automorphisms is a K-automorphism. *)
Lemma comp_is_kaut (E : FieldExtension) (σ τ : FieldAuto E.(ext_fL))
    (hσ : IsKAuto E σ) (hτ : IsKAuto E τ) :
    IsKAuto E (comp_auto σ τ).
Proof.
  intros k. unfold comp_auto. cbn.
  rewrite (hτ k), (hσ k). reflexivity.
Qed.

(** Inverse of a K-automorphism is a K-automorphism. *)
Lemma inv_is_kaut (E : FieldExtension) (σ : FieldAuto E.(ext_fL))
    (hσ : IsKAuto E σ) :
    IsKAuto E (inv_auto σ).
Proof.
  intros k.
  change ((inv_auto σ).(fa_map) (E.(ext_emb).(rhom_map) k))
    with (σ.(fa_inv) (E.(ext_emb).(rhom_map) k)).
  (* σ fixes ι(k), so σ^{-1}(ι(k)) = σ^{-1}(σ(ι(k))) = ι(k) *)
  transitivity (σ.(fa_inv) (σ.(fa_map) (E.(ext_emb).(rhom_map) k))).
  + f_equal. exact (eq_sym (hσ k)).
  + exact (σ.(fa_inv_l) _).
Qed.

(** ** Subgroup predicate *)

(** A subset H ⊆ Gal(L/K) is a subgroup if it is closed under the group
    operations of Gal(L/K). *)

Record IsSubgroup (E : FieldExtension) (H : GaloisGroup E -> Prop) : Prop := {
  sg_id    : H (exist _ (id_auto E.(ext_fL)) (id_is_kaut E));
  sg_comp  : forall σ τ : GaloisGroup E,
               H σ -> H τ ->
               H (exist _ (comp_auto (proj1_sig σ) (proj1_sig τ))
                          (comp_is_kaut E _ _ (proj2_sig σ) (proj2_sig τ)));
  sg_inv   : forall σ : GaloisGroup E,
               H σ ->
               H (exist _ (inv_auto (proj1_sig σ))
                          (inv_is_kaut E _ (proj2_sig σ)));
}.

(** The full group Gal(L/K) is a subgroup of itself. *)
Definition full_subgroup (E : FieldExtension) :
    { H : GaloisGroup E -> Prop | IsSubgroup E H }.
Proof.
  exists (fun _ => True).
  constructor; intros; exact I.
Defined.

(** The trivial subgroup {id} is a subgroup. *)
Definition trivial_subgroup (E : FieldExtension) :
    { H : GaloisGroup E -> Prop | IsSubgroup E H }.
Proof.
  exists (fun σ => forall x, (proj1_sig σ).(fa_map) x = x).
  constructor.
  - (* sg_id: identity acts as identity *)
    intro x. reflexivity.
  - (* sg_comp: composition of two identity-acting automorphisms acts as identity *)
    intros σ τ hσ hτ x.
    change ((proj1_sig σ).(fa_map) ((proj1_sig τ).(fa_map) x) = x).
    rewrite (hτ x). exact (hσ x).
  - (* sg_inv: inverse of an identity-acting automorphism acts as identity *)
    intros σ hσ x.
    change ((proj1_sig σ).(fa_inv) x = x).
    transitivity ((proj1_sig σ).(fa_inv) ((proj1_sig σ).(fa_map) x)).
    + f_equal. symmetry. exact (hσ x).
    + exact ((proj1_sig σ).(fa_inv_l) x).
Qed.

(** ** Poset of subgroups *)

(** Subgroups of Gal(L/K) are ordered by inclusion. *)

Definition SubgroupPoset (E : FieldExtension) : Poset.
Proof.
  refine {|
    carrier    := { H : GaloisGroup E -> Prop | IsSubgroup E H };
    le         := fun H1 H2 => forall σ, proj1_sig H1 σ -> proj1_sig H2 σ;
    le_refl    := fun H σ Hσ => Hσ;
    le_trans   := fun H1 H2 H3 h12 h23 σ Hσ => h23 σ (h12 σ Hσ);
    le_antisym := _;
  |}.
  intros H1 H2 h12 h21.
  apply eq_sig_hprop. { intros x. apply proof_irrelevance. }
  apply functional_extensionality. intros σ.
  apply propositional_extensionality. split; [apply h12 | apply h21].
Defined.

Notation "'SubgrpPoset' E" := (SubgroupPoset E) (at level 9) : order_scope.
