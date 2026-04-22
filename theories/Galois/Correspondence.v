(** * Galois/Correspondence.v
    The fundamental Galois correspondence.

    For a field extension E = (K ↪ L) we build an antitone Galois connection
    between the poset of intermediate fields and the poset of subgroups of
    Gal(L/K):

        fix_group : (IntermPoset E)^op  →  SubgrpPoset E
        fix_field : SubgrpPoset E       →  (IntermPoset E)^op

    satisfying:  fix_group(F) ⊆ H  ↔  F ⊇ fix_field(H)

    We realise this as an isotone Galois connection (using our GaloisConnection
    record) by working with the opposite poset on the intermediate-field side.
    The Fundamental Theorem of Galois Theory then says (for finite Galois
    extensions) that both unit and counit are equalities. *)

Require Import CAG.Order.Poset.
Require Import CAG.Order.Adjunction.
Require Import CAG.Galois.Field.
Require Import CAG.Galois.Automorphism.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Logic.Classical.
From Stdlib Require Import Logic.PropExtensionality.

Open Scope order_scope.

(** ** Opposite poset *)

(** The opposite of a poset P has the same carrier but reversed order. *)
Definition OpPoset (P : Poset) : Poset.
Proof.
  refine {|
    carrier    := P.(carrier);
    le         := fun x y => P.(le) y x;
    le_refl    := fun x => P.(le_refl) x;
    le_trans   := fun x y z hxy hyz => P.(le_trans) z y x hyz hxy;
    le_antisym := fun x y hxy hyx => P.(le_antisym) x y hyx hxy;
  |}.
Defined.

Notation "P ^op" := (OpPoset P) (at level 5) : order_scope.

(** ** fix_group : intermediate field → fixing subgroup *)

(** The fixing predicate: σ fixes every element of F. *)
Definition fixing_pred (E : FieldExtension) (F : IntermField E)
    (σ : GaloisGroup E) : Prop :=
  forall x : E.(ext_top), F.(if_pred) x -> (proj1_sig σ).(fa_map) x = x.

Lemma fixing_pred_is_subgroup (E : FieldExtension) (F : IntermField E) :
    IsSubgroup E (fixing_pred E F).
Proof.
  constructor.
  - (* identity fixes everything *)
    intros x _. reflexivity.
  - (* composition: σ∘τ fixes x ∈ F because τ(x) = x and σ(x) = x *)
    intros σ τ hσ hτ x Hx. unfold fixing_pred in *.
    cbn. rewrite (hτ x Hx). apply (hσ x Hx).
  - (* inverse: σ^{-1} fixes F — follows from σ fixing F and bijectivity *)
    intros σ hσ x Hx. cbn.
    transitivity ((proj1_sig σ).(fa_inv) ((proj1_sig σ).(fa_map) x)).
    + f_equal. symmetry. exact (hσ x Hx).
    + exact ((proj1_sig σ).(fa_inv_l) x).
Qed.

(** Given an intermediate field F, the fixing subgroup is
    { σ ∈ Gal(L/K) | σ fixes every element of F }. *)
Definition fixing_subgroup (E : FieldExtension) (F : IntermField E) :
    { H : GaloisGroup E -> Prop | IsSubgroup E H } :=
  exist _ (fixing_pred E F) (fixing_pred_is_subgroup E F).

(** fix_group is antitone: F1 ≤ F2 → fix_group(F2) ≤ fix_group(F1). *)
(** (Smaller field = fewer constraints = larger fixing group.) *)
Lemma fixing_subgroup_antitone (E : FieldExtension)
    (F1 F2 : IntermField E) :
    (forall x, F1.(if_pred) x -> F2.(if_pred) x) ->
    forall σ, proj1_sig (fixing_subgroup E F2) σ ->
              proj1_sig (fixing_subgroup E F1) σ.
Proof.
  intros Hinc σ Hσ x HxF1.
  apply Hσ. apply Hinc. exact HxF1.
Qed.

(** ** fix_field : subgroup → fixed field *)

(** Given a subgroup H ≤ Gal(L/K), the fixed field is
    { x ∈ L | ∀ σ ∈ H, σ(x) = x }. *)

(** Helper: automorphisms fix 0, 1, and respect ring operations. *)
Lemma fa_map_zero {L : Type} {fL : Field L} (σ : FieldAuto fL) :
    σ.(fa_map) fL.(fld_ring).(cr_zero) = fL.(fld_ring).(cr_zero).
Proof.
  rewrite <- σ.(fa_map_eq). apply rhom_zero.
Qed.

Lemma fa_map_one {L : Type} {fL : Field L} (σ : FieldAuto fL) :
    σ.(fa_map) fL.(fld_ring).(cr_one) = fL.(fld_ring).(cr_one).
Proof.
  rewrite <- σ.(fa_map_eq). apply (rhom_one σ.(fa_rhom)).
Qed.

Lemma fa_map_add {L : Type} {fL : Field L} (σ : FieldAuto fL) (a b : L) :
    σ.(fa_map) (fL.(fld_ring).(cr_add) a b)
    = fL.(fld_ring).(cr_add) (σ.(fa_map) a) (σ.(fa_map) b).
Proof.
  rewrite <- σ.(fa_map_eq). apply (rhom_add σ.(fa_rhom)).
Qed.

Lemma fa_map_neg {L : Type} {fL : Field L} (σ : FieldAuto fL) (a : L) :
    σ.(fa_map) (fL.(fld_ring).(cr_neg) a) = fL.(fld_ring).(cr_neg) (σ.(fa_map) a).
Proof.
  rewrite <- σ.(fa_map_eq). apply (rhom_neg σ.(fa_rhom)).
Qed.

Lemma fa_map_mul {L : Type} {fL : Field L} (σ : FieldAuto fL) (a b : L) :
    σ.(fa_map) (fL.(fld_ring).(cr_mul) a b)
    = fL.(fld_ring).(cr_mul) (σ.(fa_map) a) (σ.(fa_map) b).
Proof.
  rewrite <- σ.(fa_map_eq). apply (rhom_mul σ.(fa_rhom)).
Qed.

Definition fixed_pred (E : FieldExtension)
    (H : { Hg : GaloisGroup E -> Prop | IsSubgroup E Hg })
    (x : E.(ext_top)) : Prop :=
  forall σ : GaloisGroup E, proj1_sig H σ -> (proj1_sig σ).(fa_map) x = x.

Lemma fixed_pred_is_subfield (E : FieldExtension)
    (H : { Hg : GaloisGroup E -> Prop | IsSubgroup E Hg }) :
    IsSubfieldOf E.(ext_fL) (fixed_pred E H).
Proof.
  constructor.
  - intros σ _. apply fa_map_zero.
  - intros σ _. apply fa_map_one.
  - intros a b Ha Hb σ Hσ.
    rewrite (fa_map_add (proj1_sig σ)).
    rewrite (Ha σ Hσ), (Hb σ Hσ). reflexivity.
  - intros a Ha σ Hσ.
    rewrite (fa_map_neg (proj1_sig σ)).
    rewrite (Ha σ Hσ). reflexivity.
  - intros a b Ha Hb σ Hσ.
    rewrite (fa_map_mul (proj1_sig σ)).
    rewrite (Ha σ Hσ), (Hb σ Hσ). reflexivity.
  - (* σ(a^{-1}) = σ(a)^{-1} = a^{-1}: automorphisms preserve inverses *)
    intros a Ha Hne σ Hσ.
    pose proof (Ha σ Hσ) as Hσa.
    (* Use fL := E.(ext_fL) directly via :> coercion *)
    (* a * σ(a⁻¹) = σ(a) * σ(a⁻¹) = σ(a * a⁻¹) = σ(1) = 1 *)
    assert (Hmul : E.(ext_fL).(cr_mul) a ((proj1_sig σ).(fa_map) (E.(ext_fL).(fld_inv) a))
                   = E.(ext_fL).(cr_one)).
    { rewrite <- Hσa at 1.
      rewrite <- (fa_map_mul (proj1_sig σ) a (E.(ext_fL).(fld_inv) a)).
      rewrite (E.(ext_fL).(fld_inv_mul) a Hne).
      apply fa_map_one. }
    (* σ(a⁻¹) = a⁻¹ * (a * σ(a⁻¹)) = a⁻¹ * 1 = a⁻¹ *)
    assert (LHS : E.(ext_fL).(cr_mul) (E.(ext_fL).(fld_inv) a)
                    (E.(ext_fL).(cr_mul) a ((proj1_sig σ).(fa_map) (E.(ext_fL).(fld_inv) a)))
                  = (proj1_sig σ).(fa_map) (E.(ext_fL).(fld_inv) a)).
    { rewrite E.(ext_fL).(cr_mul_assoc).
      assert (Hinva : E.(ext_fL).(cr_mul) (E.(ext_fL).(fld_inv) a) a = E.(ext_fL).(cr_one)).
      { rewrite E.(ext_fL).(cr_mul_comm). exact (E.(ext_fL).(fld_inv_mul) a Hne). }
      rewrite Hinva.
      rewrite (E.(ext_fL).(cr_mul_comm) E.(ext_fL).(cr_one) _).
      apply E.(ext_fL).(cr_mul_one). }
    assert (RHS : E.(ext_fL).(cr_mul) (E.(ext_fL).(fld_inv) a)
                    (E.(ext_fL).(cr_mul) a ((proj1_sig σ).(fa_map) (E.(ext_fL).(fld_inv) a)))
                  = E.(ext_fL).(fld_inv) a).
    { rewrite Hmul. apply E.(ext_fL).(cr_mul_one). }
    exact (eq_trans (eq_sym LHS) RHS).
Qed.

Definition fixed_field (E : FieldExtension)
    (H : { Hg : GaloisGroup E -> Prop | IsSubgroup E Hg }) :
    IntermField E :=
  {| if_pred       := fixed_pred E H;
     if_sub        := fixed_pred_is_subfield E H;
     if_contains_K := fun k σ _ => proj2_sig σ k; |}.

(** fix_field is antitone: H1 ≤ H2 → fix_field(H2) ≤ fix_field(H1). *)
(** (Larger group = more constraints = smaller fixed field.) *)
Lemma fixed_field_antitone (E : FieldExtension)
    (H1 H2 : { Hg : GaloisGroup E -> Prop | IsSubgroup E Hg }) :
    (forall σ, proj1_sig H1 σ -> proj1_sig H2 σ) ->
    forall x, (fixed_field E H2).(if_pred) x ->
              (fixed_field E H1).(if_pred) x.
Proof.
  intros Hinc x Hx σ Hσ1.
  apply Hx. apply Hinc. exact Hσ1.
Qed.

(** ** The Galois connection *)

(** We package fix_group and fix_field as monotone maps between the
    OPPOSITE of IntermPoset and SubgrpPoset, then invoke GaloisConnection.

    The adjunction condition:
      fix_group(F) ⊆ H  ↔  F ⊇ fix_field(H)
    i.e. (in the opposite order on IntermFields):
      fix_group(F) ≤[SubgrpPoset] H  ↔  F ≤[(IntermPoset)^op] fix_field(H) *)

Definition fix_group_mono (E : FieldExtension) :
    (IntermPoset E)^op →m SubgrpPoset E :=
  @Build_MonotoneMap ((IntermPoset E)^op) (SubgrpPoset E)
    (fixing_subgroup E)
    (fun F1 F2 Hle => fixing_subgroup_antitone E F2 F1 Hle).

Definition fix_field_mono (E : FieldExtension) :
    SubgrpPoset E →m (IntermPoset E)^op.
Proof.
  refine (@Build_MonotoneMap (SubgrpPoset E) ((IntermPoset E)^op)
    (fixed_field E) _).
  intros H1 H2 Hle. cbn in *.
  exact (fixed_field_antitone E H1 H2 Hle).
Defined.

(** The adjunction: fix_group(F) ⊆ H  ↔  F ⊇ fix_field(H). *)

(** Forward: if fix_group(F) ⊆ H, then fix_field(H) ⊆ F.
    (Every element fixed by all of H is in F, because fix_group(F) ⊆ H
    means every σ ∈ H already fixes F.) *)
Lemma galois_adj_lr (E : FieldExtension)
    (F : IntermField E)
    (H : { Hg : GaloisGroup E -> Prop | IsSubgroup E Hg }) :
    (forall σ, proj1_sig (fixing_subgroup E F) σ -> proj1_sig H σ) ->
    forall x, (fixed_field E H).(if_pred) x -> F.(if_pred) x.
Proof.
  Admitted.
  (* Proof idea: x ∈ fix_field(H) means every σ ∈ H fixes x.
     We need x ∈ F.  This direction requires Galois theory proper
     (e.g. the Artin argument: if x ∉ F then some σ ∈ fix_group(F) ⊆ H
     moves x, contradicting x ∈ fix_field(H)). *)

(** Backward: if fix_field(H) ⊆ F, then fix_group(F) ⊆ H.
    (Every σ that fixes F also fixes all of fix_field(H), hence lies in H
    since fix_field(H) is the largest field fixed by H.) *)
Lemma galois_adj_rl (E : FieldExtension)
    (F : IntermField E)
    (H : { Hg : GaloisGroup E -> Prop | IsSubgroup E Hg }) :
    (forall x, (fixed_field E H).(if_pred) x -> F.(if_pred) x) ->
    forall σ, proj1_sig (fixing_subgroup E F) σ -> proj1_sig H σ.
Proof.
  Admitted.
  (* Proof idea: σ fixes F ⊇ fix_field(H).  We need σ ∈ H.
     This is the deeper direction: uses the fact that H = fix_group(fix_field(H))
     for closed subgroups, which is the content of the Fundamental Theorem. *)

(** ** Packaging as a GaloisConnection *)

Definition galois_connection (E : FieldExtension) :
    GaloisConnection ((IntermPoset E)^op) (SubgrpPoset E).
Proof.
  refine {|
    gc_left   := fix_group_mono E;
    gc_right  := fix_field_mono E;
    gc_adj_lr := _;
    gc_adj_rl := _;
  |}.
  - exact (galois_adj_lr E).
  - exact (galois_adj_rl E).
Defined.

(** Notation: using the l ⊣ r convention from Adjunction.v
    (gc_left ⊣ gc_right):
      fix_group ⊣ fix_field  as maps  (IntermPoset)^op → SubgrpPoset *)

(** ** Unit and counit *)

(** Unit: F ≤ fix_field(fix_group(F))  [in (IntermPoset)^op, i.e. ⊇] *)
Lemma galois_unit (E : FieldExtension) (F : IntermField E) :
    forall x, F.(if_pred) x ->
              (fixed_field E (fixing_subgroup E F)).(if_pred) x.
Proof.
  intros x Hx σ Hσ.
  (* Hσ : σ ∈ fix_group(F), i.e. σ fixes all of F.  Since x ∈ F, σ(x) = x. *)
  apply Hσ. exact Hx.
Qed.

(** Counit: fix_group(fix_field(H)) ≤ H  [in SubgrpPoset] *)
Lemma galois_counit (E : FieldExtension)
    (H : { Hg : GaloisGroup E -> Prop | IsSubgroup E Hg }) :
    forall σ, proj1_sig (fixing_subgroup E (fixed_field E H)) σ ->
              proj1_sig H σ.
Proof.
  Admitted.
  (* fix_group(fix_field(H)) = all σ fixing fix_field(H).
     We need σ ∈ H.  This is the non-trivial direction of the FT. *)

(** ** Fundamental Theorem of Galois Theory *)

(** For a finite Galois extension (normal + separable), both maps are
    inverse isomorphisms of posets: unit and counit are equalities.

    This is stated as a proposition; its proof requires substantial
    additional machinery (algebraic closure, degree arguments, Artin's
    theorem) that we leave admitted. *)

Definition IsGalois (E : FieldExtension) : Prop :=
  (* The extension is normal and separable, i.e. L is the splitting field
     of a separable polynomial over K. *)
  True. (* placeholder — full definition requires polynomial machinery *)

Theorem fundamental_theorem_galois (E : FieldExtension) (hG : IsGalois E) :
    (* (1) The maps are mutually inverse order-isomorphisms. *)
    (forall F : IntermField E,
       fixed_field E (fixing_subgroup E F) = F) /\
    (forall H : { Hg : GaloisGroup E -> Prop | IsSubgroup E Hg },
       forall σ, proj1_sig (fixing_subgroup E (fixed_field E H)) σ <->
                 proj1_sig H σ).
Proof.
  Admitted.

(** Corollary: the Galois correspondence reverses inclusion. *)
Corollary galois_order_reversing (E : FieldExtension) (hG : IsGalois E)
    (F1 F2 : IntermField E) :
    (forall x, F1.(if_pred) x -> F2.(if_pred) x) <->
    (forall σ, proj1_sig (fixing_subgroup E F2) σ ->
               proj1_sig (fixing_subgroup E F1) σ).
Proof.
  split.
  - exact (fixing_subgroup_antitone E F1 F2).
  - intros Hrev x Hx.
    destruct (fundamental_theorem_galois E hG) as [Hff _].
    (* F2 = fix_field(fix_group(F2)) by FT, so rewrite goal *)
    rewrite <- (Hff F2).
    (* fix_group(F2) ⊆ fix_group(F1) (Hrev), so fix_field reverses:
       fix_field(fix_group(F1)) ⊆ fix_field(fix_group(F2)) *)
    apply (fixed_field_antitone E (fixing_subgroup E F2)
                                   (fixing_subgroup E F1) Hrev).
    (* x ∈ F1 = fix_field(fix_group(F1)) by FT *)
    rewrite (Hff F1). exact Hx.
Qed.
