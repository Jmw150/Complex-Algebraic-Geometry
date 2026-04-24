
(** * Group Actions — Basic Definitions and Structural Lemmas

    Formalizes Chapter 4 §1 of Dummit & Foote.

    Main content:
    - left group action
    - kernel, stabilizer, orbit
    - faithfulness and transitivity
    - permutation representation
    - orbit equivalence relation
    - orbit-stabilizer bijection (type-level) *)

From CAG Require Import Group.
From Stdlib Require Import List Arith.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(** ** 1.  Left group action *)
(* ------------------------------------------------------------------ *)

Record IsGroupAction {G A : Type} (sg : StrictGroup G) (act : G -> A -> A) : Prop :=
  mkGA
  {
    act_id  : forall a : A, act (se G sg) a = a;
    act_mul : forall (g h : G) (a : A),
                act (smul G sg g h) a = act g (act h a);
  }.

Arguments act_id  {G A sg act} _ _.
Arguments act_mul {G A sg act} _ _ _ _.

(** Convenience: the permutation attached to g. *)
Definition sigma_g {G A : Type} {sg : StrictGroup G} {act : G -> A -> A}
    (ga : IsGroupAction sg act) (g : G) : A -> A :=
  act g.

(** sigma_{g⁻¹} is the inverse of sigma_g. *)
Lemma sigma_inv_left {G A : Type} {sg : StrictGroup G} {act : G -> A -> A}
    (ga : IsGroupAction sg act) (g : G) (a : A) :
    sigma_g ga (sinv G sg g) (sigma_g ga g a) = a.
Proof.
  unfold sigma_g.
  rewrite <- (ga.(act_mul) (sinv G sg g) g a).
  rewrite (sinv_left G sg g).
  apply ga.(act_id).
Qed.

Lemma sigma_inv_right {G A : Type} {sg : StrictGroup G} {act : G -> A -> A}
    (ga : IsGroupAction sg act) (g : G) (a : A) :
    sigma_g ga g (sigma_g ga (sinv G sg g) a) = a.
Proof.
  unfold sigma_g.
  rewrite <- (ga.(act_mul) g (sinv G sg g) a).
  rewrite (sinv_right G sg g).
  apply ga.(act_id).
Qed.

(* ------------------------------------------------------------------ *)
(** ** 2.  Kernel, stabilizer, orbit *)
(* ------------------------------------------------------------------ *)

(** Kernel of the action: elements fixing every point. *)
Definition kernel_action {G A : Type} {sg : StrictGroup G} {act : G -> A -> A}
    (ga : IsGroupAction sg act) : G -> Prop :=
  fun g => forall a : A, act g a = a.

(** Stabilizer of a point a. *)
Definition stabilizer {G A : Type} {sg : StrictGroup G} {act : G -> A -> A}
    (ga : IsGroupAction sg act) (a : A) : G -> Prop :=
  fun g => act g a = a.

(** Orbit of a point a. *)
Definition orbit {G A : Type} {sg : StrictGroup G} {act : G -> A -> A}
    (ga : IsGroupAction sg act) (a : A) : A -> Prop :=
  fun b => exists g : G, act g a = b.

(** Faithful action: kernel is trivial. *)
Definition faithful_action {G A : Type} {sg : StrictGroup G} {act : G -> A -> A}
    (ga : IsGroupAction sg act) : Prop :=
  forall g : G, kernel_action ga g -> g = se G sg.

(** Transitive action: one orbit. *)
Definition transitive_action {G A : Type} {sg : StrictGroup G} {act : G -> A -> A}
    (ga : IsGroupAction sg act) : Prop :=
  forall a b : A, exists g : G, act g a = b.

(* ------------------------------------------------------------------ *)
(** ** 3.  Stabilizer is a subgroup *)
(* ------------------------------------------------------------------ *)

Lemma stabilizer_subgroup {G A : Type} {sg : StrictGroup G} {act : G -> A -> A}
    (ga : IsGroupAction sg act) (a : A) :
    is_subgroup (StrictGroup_to_Group sg) (stabilizer ga a).
Proof.
  unfold is_subgroup, stabilizer, contains_id, closed_under_mul, closed_under_inv.
  simpl.
  split; [| split].
  - (* identity fixes a *)
    apply ga.(act_id).
  - (* closed under mul *)
    intros g h Hg Hh.
    rewrite ga.(act_mul).
    rewrite Hh. exact Hg.
  - (* closed under inv *)
    intros g Hg.
    exists (sinv G sg g).
    split.
    + (* sinv g stabilizes a: act (g⁻¹) a = a. *)
      unfold stabilizer.
      assert (step : act (sinv G sg g) a = act (sinv G sg g) (act g a)).
      { rewrite Hg. reflexivity. }
      rewrite step, <- ga.(act_mul), sinv_left. apply ga.(act_id).
    + unfold is_inverse_of. simpl.
      split; [apply sinv_right | apply sinv_left].
Qed.

(* ------------------------------------------------------------------ *)
(** ** 4.  Kernel is a normal subgroup *)
(* ------------------------------------------------------------------ *)

Lemma kernel_subgroup {G A : Type} {sg : StrictGroup G} {act : G -> A -> A}
    (ga : IsGroupAction sg act) :
    is_subgroup (StrictGroup_to_Group sg) (kernel_action ga).
Proof.
  unfold is_subgroup, kernel_action, contains_id, closed_under_mul, closed_under_inv.
  simpl.
  split; [| split].
  - intro a. apply ga.(act_id).
  - intros g h Hg Hh a.
    rewrite ga.(act_mul), Hh, Hg. reflexivity.
  - intros g Hg.
    exists (sinv G sg g).
    split.
    + intro a.
      assert (step : act (sinv G sg g) a = act (sinv G sg g) (act g a)).
      { rewrite Hg. reflexivity. }
      rewrite step, <- ga.(act_mul), sinv_left. apply ga.(act_id).
    + unfold is_inverse_of. simpl. split; [apply sinv_right | apply sinv_left].
Qed.

Lemma kernel_normal {G A : Type} {sg : StrictGroup G} {act : G -> A -> A}
    (ga : IsGroupAction sg act) :
    is_normal_subgroup (StrictGroup_to_Group sg) (kernel_action ga).
Proof.
  unfold is_normal_subgroup.
  split.
  - exact (kernel_subgroup ga).
  - intros g n ginv Hn [Hgginv Hginvg] a. simpl.
    (* goal: kernel_action ga (g * n * ginv) *)
    (* = forall a, act (g * n * ginv) a = a *)
    (* act (g*n*ginv) a = act g (act n (act ginv a))
                        = act g (act ginv a)       [since Hn : ∀a, act n a = a]
                        = act (g*ginv) a            [← act_mul]
                        = act e a                   [g*ginv = e]
                        = a                         [act_id] *)
    rewrite !ga.(act_mul).
    rewrite (Hn (act ginv a)).
    assert (Hgginv' : smul G sg g ginv = se G sg) by exact Hgginv.
    rewrite <- ga.(act_mul), Hgginv'. apply ga.(act_id).
Qed.

(* ------------------------------------------------------------------ *)
(** ** 5.  Orbit equivalence relation *)
(* ------------------------------------------------------------------ *)

(** The action relation: a ~ b iff ∃ g, b = g · a. *)
Definition act_rel {G A : Type} {sg : StrictGroup G} {act : G -> A -> A}
    (ga : IsGroupAction sg act) (a b : A) : Prop :=
  exists g : G, act g a = b.

Lemma act_rel_refl {G A : Type} {sg : StrictGroup G} {act : G -> A -> A}
    (ga : IsGroupAction sg act) (a : A) : act_rel ga a a.
Proof.
  exists (se G sg). apply ga.(act_id).
Qed.

Lemma act_rel_sym {G A : Type} {sg : StrictGroup G} {act : G -> A -> A}
    (ga : IsGroupAction sg act) (a b : A) :
    act_rel ga a b -> act_rel ga b a.
Proof.
  intros [g Hg].
  exists (sinv G sg g).
  rewrite <- Hg.
  exact (sigma_inv_left ga g a).
Qed.

Lemma act_rel_trans {G A : Type} {sg : StrictGroup G} {act : G -> A -> A}
    (ga : IsGroupAction sg act) (a b c : A) :
    act_rel ga a b -> act_rel ga b c -> act_rel ga a c.
Proof.
  intros [g Hg] [h Hh].
  exists (smul G sg h g).
  rewrite ga.(act_mul), Hg. exact Hh.
Qed.

(** Orbit = equivalence class of a under act_rel. *)
Lemma orbit_eq_act_class {G A : Type} {sg : StrictGroup G} {act : G -> A -> A}
    (ga : IsGroupAction sg act) (a b : A) :
    orbit ga a b <-> act_rel ga a b.
Proof.
  unfold orbit, act_rel. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** 6.  Orbit-stabilizer bijection (type-level) *)
(* ------------------------------------------------------------------ *)

(** The map from left cosets of Stab(a) to Orbit(a):  g · Stab(a) ↦ g · a. *)
Definition coset_to_orbit {G A : Type} {sg : StrictGroup G} {act : G -> A -> A}
    (ga : IsGroupAction sg act) (a : A) (g : G) : A :=
  act g a.

(** Two cosets map to the same orbit point iff they lie in the same stabilizer coset. *)
Lemma coset_to_orbit_wd {G A : Type} {sg : StrictGroup G} {act : G -> A -> A}
    (ga : IsGroupAction sg act) (a : A) (g h : G) :
    act g a = act h a  <->
    stabilizer ga a (smul G sg (sinv G sg h) g).
Proof.
  unfold stabilizer.
  rewrite ga.(act_mul).
  (* goal: act g a = act h a <-> act (sinv h) (act g a) = a *)
  split.
  - intro Heq.
    (* act (sinv h) (act g a) = act (sinv h) (act h a) = act (sinv h * h) a = a *)
    rewrite Heq, <- ga.(act_mul), sinv_left. apply ga.(act_id).
  - intro Hstab.
    (* act h (act (sinv h) (act g a)) = act g a  [by act_mul + sinv_right + act_id]
       but also = act h a  [since act (sinv h) (act g a) = a by Hstab] *)
    assert (step : act h (act (sinv G sg h) (act g a)) = act g a).
    { rewrite <- ga.(act_mul), sinv_right. apply ga.(act_id). }
    rewrite Hstab in step.
    (* step : act h a = act g a *)
    exact (eq_sym step).
Qed.

(* ------------------------------------------------------------------ *)
(** ** 7.  Conjugation action of G on itself *)
(* ------------------------------------------------------------------ *)

(** G acts on itself by conjugation: g · x = g * x * g⁻¹. *)
Definition conj_act {G : Type} (sg : StrictGroup G) (g x : G) : G :=
  smul G sg (smul G sg g x) (sinv G sg g).

Lemma conj_act_is_action {G : Type} (sg : StrictGroup G) :
    IsGroupAction sg (conj_act sg).
Proof.
  constructor.
  - intro x. unfold conj_act.
    rewrite sid_left.
    (* goal: smul G sg x (sinv G sg (se G sg)) = x *)
    assert (Hinv_e : sinv G sg (se G sg) = se G sg).
    { symmetry. apply (unique_inverse sg (se G sg) (se G sg)).
      - apply sid_right.
      - apply sid_left. }
    rewrite Hinv_e. apply sid_right.
  - intros g h x. unfold conj_act.
    rewrite (inv_mul sg g h), !sassoc. reflexivity.
Qed.

(** Conjugacy class of x: its orbit under the conjugation action. *)
Definition conj_class {G : Type} (sg : StrictGroup G) (x : G) : G -> Prop :=
  orbit (conj_act_is_action sg) x.

(** Centralizer of x: its stabilizer under the conjugation action. *)
Definition centralizer {G : Type} (sg : StrictGroup G) (x : G) : G -> Prop :=
  stabilizer (conj_act_is_action sg) x.

Lemma centralizer_subgroup {G : Type} (sg : StrictGroup G) (x : G) :
    is_subgroup (StrictGroup_to_Group sg) (centralizer sg x).
Proof.
  exact (stabilizer_subgroup (conj_act_is_action sg) x).
Qed.

(** The centralizer of x is exactly {g | g*x = x*g}. *)
Lemma centralizer_commutes {G : Type} (sg : StrictGroup G) (x g : G) :
    centralizer sg x g  <->  smul G sg g x = smul G sg x g.
Proof.
  unfold centralizer, stabilizer, conj_act. simpl.
  split.
  - intro H.
    (* H: g*x*g⁻¹ = x  →  g*x = x*g *)
    apply (right_cancel sg (sinv G sg g)).
    (* goal: g*x * sinv g = x*g * sinv g *)
    rewrite H.
    (* goal: x = x*g * sinv g *)
    rewrite <- (sassoc G sg x g (sinv G sg g)), sinv_right, sid_right.
    reflexivity.
  - intro H.
    (* H: g*x = x*g  →  g*x*g⁻¹ = x *)
    rewrite H.
    (* goal: x*g * sinv g = x *)
    rewrite <- (sassoc G sg x g (sinv G sg g)), sinv_right, sid_right.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** 8.  Normalizer and block definitions *)
(* ------------------------------------------------------------------ *)

(** Normalizer of a subset S: { g | g S g⁻¹ = S }. *)
Definition normalizer {G : Type} (sg : StrictGroup G) (S : G -> Prop) : G -> Prop :=
  fun g =>
    (forall x : G, S x -> S (conj_act sg g x)) /\
    (forall x : G, S (conj_act sg g x) -> S x).

Lemma normalizer_subgroup {G : Type} (sg : StrictGroup G) (S : G -> Prop) :
    is_subgroup (StrictGroup_to_Group sg) (normalizer sg S).
Proof.
  (* The key facts: conj_act sg e = id and conj_act sg (g*h) = conj_act sg g ∘ conj_act sg h.
     Closure under mul and inv then follow componentwise. *)
  unfold is_subgroup, normalizer, contains_id, closed_under_mul, closed_under_inv.
  simpl.
  split; [| split].
  - (* identity: conj_act sg e x = x *)
    assert (Hconj_e : forall x, conj_act sg (se G sg) x = x).
    { intro x. unfold conj_act.
      rewrite (sid_left G sg x).
      assert (Hinv_e : sinv G sg (se G sg) = se G sg) by
        (symmetry; apply (unique_inverse sg (se G sg) (se G sg));
         apply sid_right; apply sid_left).
      rewrite Hinv_e. apply (sid_right G sg). }
    split; intros x Hx.
    + rewrite (Hconj_e x). exact Hx.
    + rewrite <- (Hconj_e x). exact Hx.
  - (* mul *)
    intros g h [Hg1 Hg2] [Hh1 Hh2].
    assert (Hconj_mul : forall x, conj_act sg (smul G sg g h) x =
                                   conj_act sg g (conj_act sg h x)).
    { intro x. unfold conj_act. rewrite (inv_mul sg g h), !sassoc. reflexivity. }
    split; intros x Hx.
    + rewrite (Hconj_mul x). apply Hg1. apply Hh1. exact Hx.
    + rewrite (Hconj_mul x) in Hx. apply Hh2. apply Hg2. exact Hx.
  - (* inv *)
    intros g [Hg1 Hg2].
    exists (sinv G sg g).
    split.
    + set (ga := conj_act_is_action sg).
      assert (Hconj_inv2 : forall x, conj_act sg g (conj_act sg (sinv G sg g) x) = x).
      { intro x.
        rewrite <- (ga.(act_mul) g (sinv G sg g) x), sinv_right.
        apply ga.(act_id). }
      assert (Hconj_inv3 : forall x, conj_act sg (sinv G sg g) (conj_act sg g x) = x).
      { intro x.
        rewrite <- (ga.(act_mul) (sinv G sg g) g x), sinv_left.
        apply ga.(act_id). }
      split; intros x Hx.
      * (* S x → S (conj_act (sinv g) x):
           Hg2 applied to (conj_act (sinv g) x):
           S (conj_act g (conj_act (sinv g) x)) → S (conj_act (sinv g) x)
           = S x → S (conj_act (sinv g) x)  [by Hconj_inv2] *)
        apply (Hg2 (conj_act sg (sinv G sg g) x)).
        rewrite (Hconj_inv2 x). exact Hx.
      * (* S (conj_act (sinv g) x) → S x:
           Hg1 applied to (conj_act (sinv g) x):
           S (conj_act (sinv g) x) → S (conj_act g (conj_act (sinv g) x)) = S x *)
        assert (H := Hg1 (conj_act sg (sinv G sg g) x) Hx).
        rewrite (Hconj_inv2 x) in H. exact H.
    + unfold is_inverse_of. simpl. split; [apply sinv_right | apply sinv_left].
Qed.

(* ------------------------------------------------------------------ *)
(** ** 9.  Double cosets *)
(* ------------------------------------------------------------------ *)

(** Double coset HxK = { h*x*k | h ∈ H, k ∈ K }. *)
Definition double_coset {G : Type} (sg : StrictGroup G)
    (H K : G -> Prop) (x : G) : G -> Prop :=
  fun g =>
    exists (h k : G), H h /\ K k /\ g = smul G sg (smul G sg h x) k.

(** Double cosets partition G (they are either equal or disjoint).
    The algebraic manipulations involve cancellation in H and K;
    admitted pending a cleaner coset infrastructure. *)
Lemma double_coset_eq_or_disj {G : Type} (sg : StrictGroup G)
    (H K : G -> Prop)
    (H_sub : is_subgroup (StrictGroup_to_Group sg) H)
    (K_sub : is_subgroup (StrictGroup_to_Group sg) K)
    (x y : G) :
    (exists z : G, double_coset sg H K x z /\ double_coset sg H K y z) ->
    forall w : G, double_coset sg H K x w <-> double_coset sg H K y w.
Proof.
  intros [z [[h1 [k1 [Hh1 [Hk1 Hz1]]]] [h2 [k2 [Hh2 [Hk2 Hz2]]]]]].
  (* z = h1*x*k1 = h2*y*k2, so x relates to y by inv h1 * h2 and k2 * inv k1 *)
  assert (Hz : smul G sg (smul G sg h1 x) k1 = smul G sg (smul G sg h2 y) k2).
  { rewrite <- Hz1, <- Hz2. reflexivity. }
  (* Helper: for any h,k and the coset equation, move HxK element to HyK *)
  assert (Hfwd : forall h k, H h -> K k ->
      smul G sg (smul G sg h x) k =
      smul G sg (smul G sg (smul G sg (smul G sg h (sinv G sg h1)) h2) y)
                (smul G sg (smul G sg k2 (sinv G sg k1)) k)).
  { intros h k Hh Hk.
    (* Insert identity: x = sinv_h1*(h1*x*k1)*sinv_k1, then substitute h1*x*k1 = h2*y*k2 *)
    assert (Hx : x = smul G sg (smul G sg (sinv G sg h1) (smul G sg (smul G sg h1 x) k1)) (sinv G sg k1)).
    { rewrite (sassoc G sg (sinv G sg h1) (smul G sg h1 x) k1).
      rewrite (sassoc G sg (sinv G sg h1) h1 x).
      rewrite (sinv_left G sg h1), (sid_left G sg x).
      rewrite <- (sassoc G sg x k1 (sinv G sg k1)).
      rewrite (sinv_right G sg k1), (sid_right G sg x). reflexivity. }
    rewrite Hx, Hz.
    repeat rewrite (sassoc G sg). reflexivity. }
  assert (Hbwd : forall h k, H h -> K k ->
      smul G sg (smul G sg h y) k =
      smul G sg (smul G sg (smul G sg (smul G sg h (sinv G sg h2)) h1) x)
                (smul G sg (smul G sg k1 (sinv G sg k2)) k)).
  { intros h k Hh Hk.
    assert (Hy : y = smul G sg (smul G sg (sinv G sg h2) (smul G sg (smul G sg h2 y) k2)) (sinv G sg k2)).
    { rewrite (sassoc G sg (sinv G sg h2) (smul G sg h2 y) k2).
      rewrite (sassoc G sg (sinv G sg h2) h2 y).
      rewrite (sinv_left G sg h2), (sid_left G sg y).
      rewrite <- (sassoc G sg y k2 (sinv G sg k2)).
      rewrite (sinv_right G sg k2), (sid_right G sg y). reflexivity. }
    rewrite Hy, <- Hz.
    repeat rewrite (sassoc G sg). reflexivity. }
  intros w. split.
  - intros [h [k [Hh [Hk Hw]]]]. subst w.
    refine (ex_intro _ (smul G sg (smul G sg h (sinv G sg h1)) h2)
           (ex_intro _ (smul G sg (smul G sg k2 (sinv G sg k1)) k) _)).
    repeat split.
    + apply (subgroup_closed_mul sg H H_sub).
      * apply (subgroup_closed_mul sg H H_sub).
        -- exact Hh.
        -- apply (subgroup_closed_sinv sg H H_sub). exact Hh1.
      * exact Hh2.
    + apply (subgroup_closed_mul sg K K_sub).
      * apply (subgroup_closed_mul sg K K_sub).
        -- exact Hk2.
        -- apply (subgroup_closed_sinv sg K K_sub). exact Hk1.
      * exact Hk.
    + exact (Hfwd h k Hh Hk).
  - intros [h [k [Hh [Hk Hw]]]]. subst w.
    refine (ex_intro _ (smul G sg (smul G sg h (sinv G sg h2)) h1)
           (ex_intro _ (smul G sg (smul G sg k1 (sinv G sg k2)) k) _)).
    repeat split.
    + apply (subgroup_closed_mul sg H H_sub).
      * apply (subgroup_closed_mul sg H H_sub).
        -- exact Hh.
        -- apply (subgroup_closed_sinv sg H H_sub). exact Hh2.
      * exact Hh1.
    + apply (subgroup_closed_mul sg K K_sub).
      * apply (subgroup_closed_mul sg K K_sub).
        -- exact Hk1.
        -- apply (subgroup_closed_sinv sg K K_sub). exact Hk2.
      * exact Hk.
    + exact (Hbwd h k Hh Hk).
Qed.

(* ------------------------------------------------------------------ *)
(** ** 10.  Permutation representation homomorphism *)
(* ------------------------------------------------------------------ *)

(** The permutation attached to each g is a bijection on A; the assignment g ↦ σ_g
    is a group homomorphism to Sym(A).  We state this at the level of function
    composition rather than building the full Sym(A) StrictGroup, which requires
    function extensionality already available in Group.v. *)

Lemma sigma_g_hom {G A : Type} {sg : StrictGroup G} {act : G -> A -> A}
    (ga : IsGroupAction sg act) (g h : G) (a : A) :
    sigma_g ga (smul G sg g h) a = sigma_g ga g (sigma_g ga h a).
Proof.
  unfold sigma_g. rewrite ga.(act_mul). reflexivity.
Qed.

Lemma sigma_id {G A : Type} {sg : StrictGroup G} {act : G -> A -> A}
    (ga : IsGroupAction sg act) (a : A) :
    sigma_g ga (se G sg) a = a.
Proof.
  unfold sigma_g. apply ga.(act_id).
Qed.
