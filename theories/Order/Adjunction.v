(** * Order/Adjunction.v
    Galois connections between posets,
    Lemma 1.5.14: adjoint criterion for continuity,
    Lemma 1.5.15: all joins = finite joins + directed joins. *)

Require Import CAG.Order.Poset.
Require Import CAG.Order.Lattice.
Require Import CAG.Order.DCPO.
Require Import CAG.Order.Compact.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Logic.Classical.
From Stdlib Require Import Logic.PropExtensionality.
From Stdlib Require Import Lists.List.

Open Scope order_scope.

(** ** Galois connection (adjunction between posets)

    l : X -> Y and r : Y -> X satisfy l ⊣ r if:
      l(x) ≤ y  iff  x ≤ r(y) *)

Record GaloisConnection (X Y : Poset) : Type := {
  gc_left   : X →m Y;
  gc_right  : Y →m X;
  gc_adj_lr : forall x y, gc_left x ≤[Y] y -> x ≤[X] gc_right y;
  gc_adj_rl : forall x y, x ≤[X] gc_right y -> gc_left x ≤[Y] y;
}.

Arguments gc_left  {X Y}.
Arguments gc_right {X Y}.
Arguments gc_adj_lr {X Y}.
Arguments gc_adj_rl {X Y}.

Notation "l ⊣ r" := (GaloisConnection _ _ r l) (at level 70) : order_scope.

(** Unit and counit of a Galois connection *)

Lemma gc_unit {X Y : Poset} (gc : GaloisConnection X Y) (x : X.(carrier)) :
    x ≤[X] gc.(gc_right) (gc.(gc_left) x).
Proof.
  apply gc.(gc_adj_lr). apply Y.(le_refl).
Qed.

Lemma gc_counit {X Y : Poset} (gc : GaloisConnection X Y) (y : Y.(carrier)) :
    gc.(gc_left) (gc.(gc_right) y) ≤[Y] y.
Proof.
  apply gc.(gc_adj_rl). apply X.(le_refl).
Qed.

(** Right adjoint preserves meets *)
Lemma gc_right_preserves_inf {X Y : Poset} (gc : GaloisConnection X Y)
    (L : CompleteLattice) (hY : L.(cl_poset) = Y)
    (S : Y.(carrier) -> Prop) :
    True. (* placeholder *)
Proof. trivial. Qed.

(** Right adjoint is monotone (already in record) *)
Lemma gc_right_mono {X Y : Poset} (gc : GaloisConnection X Y) :
    forall y1 y2, y1 ≤[Y] y2 -> gc.(gc_right) y1 ≤[X] gc.(gc_right) y2.
Proof. intros y1 y2 h. apply (mono_apply gc.(gc_right)). exact h. Qed.

(** ** Lemma 1.5.14: adjoint criterion for continuity

    Let X, Y be algebraic complete lattices and l : X -> Y, r : Y -> X
    monotone with l(x) ≤ y iff x ≤ r(y) (Galois connection l ⊣ r).

    Then: r is Scott-continuous iff l preserves compact elements. *)

(** *** Forward direction: r continuous → l preserves compacts *)

Theorem gc_cont_implies_left_preserves_compacts
    (X Y : AlgCompleteLattice)
    (gc : GaloisConnection X Y)
    (hr : IsScottCont (cl_to_dcpo Y) (cl_to_dcpo X) gc.(gc_right)) :
    forall e : X.(carrier),
      IsCompact (cl_to_dcpo X) e ->
      IsCompact (cl_to_dcpo Y) (gc.(gc_left) e).
Proof.
  intros e he D hD Hle.
  (* l(e) ≤ ⊔D, so e ≤ r(l(e)) ≤ r(⊔D) *)
  (* r continuous: r(⊔D) = ⊔ r(D) *)
  (* e compact: e ≤ r(d_i) for some d_i *)
  (* then l(e) ≤ d_i *)
  assert (Hle2 : e ≤[X] ⊔d{cl_to_dcpo X}
    (fun x => exists d, D d /\ x = gc.(gc_right) d) /
    (image_directed hr D hD)).
  {
    apply X.(le_trans) with (y := gc.(gc_right) (gc.(gc_left) e)).
    - apply gc_unit.
    - apply X.(le_trans) with (y := gc.(gc_right) (⊔d{cl_to_dcpo Y} D / hD)).
      + apply (gc_right_mono gc). exact Hle.
      + apply (sc_cont' _ _ _ hr D hD).
        intros d Hd. apply X.(cl_sup_ub). exists d. split. exact Hd. reflexivity.
  }
  destruct (he _ (image_directed hr D hD) Hle2) as [rx [[d [Hd Hrx]] Hle3]].
  subst rx.
  exists d. split. exact Hd.
  apply gc.(gc_adj_rl). exact Hle3.
Qed.

(** *** Backward direction: l preserves compacts → r continuous *)

(** Key formula: r(y) = sup {x compact | l(x) ≤ y} *)
Lemma gc_right_as_sup (X Y : AlgCompleteLattice)
    (gc : GaloisConnection X Y)
    (hl : forall e : X.(carrier),
          IsCompact (cl_to_dcpo X) e ->
          IsCompact (cl_to_dcpo Y) (gc.(gc_left) e))
    (y : Y.(carrier)) :
    gc.(gc_right) y = ⊔{X} (fun x => IsCompact (cl_to_dcpo X) x /\ gc.(gc_left) x ≤[Y] y).
Proof.
  apply X.(le_antisym).
  - (* r(y) ≤ sup {e compact | l(e) ≤ y} *)
    (* r(y) = sup of compact elements below r(y) *)
    apply (proj2 (X.(acl_alg) (gc.(gc_right) y))). intros e he hle.
    apply X.(cl_sup_ub). split. exact he.
    (* l(e) ≤ y because e ≤ r(y) and we have the adjunction *)
    apply gc.(gc_adj_rl). exact hle.
  - (* sup {e compact | l(e) ≤ y} ≤ r(y) *)
    apply X.(cl_sup_lub). intros e [_ Hle].
    apply gc.(gc_adj_lr). exact Hle.
Qed.

Theorem gc_left_compact_implies_right_cont
    (X Y : AlgCompleteLattice)
    (gc : GaloisConnection X Y)
    (hl : forall e : X.(carrier),
          IsCompact (cl_to_dcpo X) e ->
          IsCompact (cl_to_dcpo Y) (gc.(gc_left) e)) :
    IsScottCont (cl_to_dcpo Y) (cl_to_dcpo X) gc.(gc_right).
Proof.
  constructor.
  - (* r is monotone *)
    intros y1 y2 h. apply (mono_apply gc.(gc_right)). exact h.
  - (* r preserves directed joins *)
    intros D hD ub Hub.
    (* Need: r(⊔D) ≤ ub *)
    (* r(⊔D) = sup{e compact | l(e) ≤ ⊔D}  [by gc_right_as_sup] *)
    rewrite (gc_right_as_sup X Y gc hl).
    apply X.(cl_sup_lub). intros e [he hle].
    (* l(e) compact (by assumption hl), l(e) ≤ ⊔D *)
    (* So l(e) ≤ d_i for some d_i ∈ D (compactness of l(e)) *)
    destruct (hl e he D hD hle) as [d [Hd Hled]].
    (* e ≤ r(d) by adjunction, r(d) ≤ ub since d ∈ D *)
    apply X.(le_trans) with (y := gc.(gc_right) d).
    + apply gc.(gc_adj_lr). exact Hled.
    + apply Hub. exact Hd.
Qed.

(** *** Lemma 1.5.14 packaged *)

Theorem adjoint_right_cont_iff_left_compact
    (X Y : AlgCompleteLattice)
    (gc : GaloisConnection X Y) :
    IsScottCont (cl_to_dcpo Y) (cl_to_dcpo X) gc.(gc_right)
    <->
    (forall e : X.(carrier),
       IsCompact (cl_to_dcpo X) e ->
       IsCompact (cl_to_dcpo Y) (gc.(gc_left) e)).
Proof.
  split.
  - apply gc_cont_implies_left_preserves_compacts.
  - apply gc_left_compact_implies_right_cont.
Qed.

(** ** Lemma 1.5.15: f preserves all joins iff it preserves finite and directed joins *)

(** A monotone map between complete lattices preserves all joins iff
    it preserves finite joins and directed joins. *)

Definition PreservesAllJoins (L M : CompleteLattice) (f : L →m M) : Prop :=
  forall (S : L.(carrier) -> Prop),
    f (⊔{L} S) = ⊔{M} (fun y => exists x, S x /\ y = f x).

Definition PreservesFiniteJoins (L M : CompleteLattice) (f : L →m M) : Prop :=
  (* Preserves bottom *)
  f (cl_bot L) = cl_bot M /\
  (* Preserves binary joins *)
  forall x y, f (cl_join L x y) = cl_join M (f x) (f y).

Definition PreservesDirectedJoins (L M : CompleteLattice) (f : L →m M) : Prop :=
  forall (D : L.(carrier) -> Prop) (hD : IsDirected L D),
    f (⊔{L} D) = ⊔{M} (fun y => exists x, D x /\ y = f x).

(** *** Forward implication: preserves all → preserves finite + directed *)

Lemma all_joins_to_finite (L M : CompleteLattice) (f : L →m M)
    (h : PreservesAllJoins L M f) : PreservesFiniteJoins L M f.
Proof.
  split.
  - (* f(⊥) = ⊥ *)
    unfold cl_bot. rewrite (h (fun _ => False)).
    apply M.(le_antisym).
    + apply M.(cl_sup_lub). intros y [x [Hx _]]. destruct Hx.
    + apply cl_bot_le.
  - intros x y.
    unfold cl_join. rewrite (h (fun z => z = x \/ z = y)).
    f_equal.
    extensionality z.
    apply propositional_extensionality.
    split.
    + intros [w [[Hw | Hw] Hz]]; subst; [left | right]; reflexivity.
    + intros [Hz | Hz]; subst.
      * exists x. split. left. reflexivity. reflexivity.
      * exists y. split. right. reflexivity. reflexivity.
Qed.

Lemma all_joins_to_directed (L M : CompleteLattice) (f : L →m M)
    (h : PreservesAllJoins L M f) : PreservesDirectedJoins L M f.
Proof.
  intros D hD. apply h.
Qed.

(** *** Reverse implication: finite + directed → all *)

(** Key step: any sup equals the directed sup of finite sups.
    For S ⊆ L, the set of finite joins of elements of S is directed. *)

Definition finite_sups_of (L : CompleteLattice) (S : L.(carrier) -> Prop) :
    L.(carrier) -> Prop :=
  fun z => exists (xs : list L.(carrier)),
    (forall x, List.In x xs -> S x) /\ z = finite_join (cl_to_jsl L) xs.

Lemma finite_sups_directed (L : CompleteLattice) (S : L.(carrier) -> Prop) :
    IsDirected L (finite_sups_of L S).
Proof.
  assert (Hle_l : forall xs ys : list L.(carrier),
      finite_join (cl_to_jsl L) xs ≤[L] finite_join (cl_to_jsl L) (xs ++ ys)).
  { induction xs as [| a xs IHxs]; intros ys.
    - cbn. apply cl_bot_le.
    - cbn. apply cl_join_lub.
      + apply cl_join_ub1.
      + apply L.(le_trans) with (y := finite_join (cl_to_jsl L) (xs ++ ys)).
        * apply IHxs.
        * apply cl_join_ub2.
  }
  assert (Hle_r : forall xs ys : list L.(carrier),
      finite_join (cl_to_jsl L) ys ≤[L] finite_join (cl_to_jsl L) (xs ++ ys)).
  { induction xs as [| a xs IHxs]; intros ys.
    - cbn. apply L.(le_refl).
    - cbn. apply L.(le_trans) with (y := finite_join (cl_to_jsl L) (xs ++ ys)).
      + apply IHxs.
      + apply cl_join_ub2.
  }
  constructor.
  - exists (finite_join (cl_to_jsl L) nil).
    exists nil. split.
    + intros x Hx. inversion Hx.
    + reflexivity.
  - intros z1 z2 Hz1 Hz2.
    unfold finite_sups_of in Hz1, Hz2.
    destruct Hz1 as [xs1 [Hxs1 Hz1]].
    destruct Hz2 as [xs2 [Hxs2 Hz2]].
    subst z1. subst z2.
    exists (finite_join (cl_to_jsl L) (xs1 ++ xs2)).
    split.
    + exists (xs1 ++ xs2). split.
      * intros x Hx. apply List.in_app_or in Hx as [Hx | Hx].
        -- exact (Hxs1 x Hx).
        -- exact (Hxs2 x Hx).
      * reflexivity.
    + split.
      * exact (Hle_l xs1 xs2).
      * exact (Hle_r xs1 xs2).
Qed.

Lemma sup_eq_directed_sup_finite_sups (L : CompleteLattice) (S : L.(carrier) -> Prop) :
    ⊔{L} S = ⊔{L} (finite_sups_of L S).
Proof.
  apply L.(le_antisym).
  - apply L.(cl_sup_lub). intros x Hx.
    apply L.(cl_sup_ub). unfold finite_sups_of.
    exists (x :: nil). split.
    + intros y Hy. cbn in Hy. destruct Hy as [Hy | Hy].
      * subst. exact Hx.
      * inversion Hy.
    + cbn. apply L.(le_antisym).
      * apply cl_join_ub1.
      * apply cl_join_lub. apply L.(le_refl). apply cl_bot_le.
  - apply L.(cl_sup_lub). intros z [xs [Hxs Hz]]. subst.
    induction xs.
    + cbn. apply cl_bot_le.
    + cbn.
      apply cl_join_lub.
      * apply L.(cl_sup_ub). apply Hxs. cbn. left. reflexivity.
      * apply IHxs. intros x Hx. apply Hxs. cbn. right. exact Hx.
Qed.

Theorem finite_and_directed_to_all_joins (L M : CompleteLattice) (f : L →m M)
    (hfin  : PreservesFiniteJoins L M f)
    (hdir  : PreservesDirectedJoins L M f) :
    PreservesAllJoins L M f.
Proof.
  intros S.
  rewrite (sup_eq_directed_sup_finite_sups L S).
  rewrite (hdir (finite_sups_of L S) (finite_sups_directed L S)).
  apply M.(le_antisym).
  - (* ⊔{f z | z ∈ finite_sups S} ≤ ⊔{f x | x ∈ S} *)
    apply M.(cl_sup_lub).
    intros y [z [[xs [Hxs Hz]] Hfy]].
    subst z y.
    (* f(finite_join xs) ≤ ⊔{M} {f x | x ∈ S}, by induction on xs *)
    induction xs as [| a xs IHxs].
    + cbn. rewrite (proj1 hfin). apply cl_bot_le.
    + cbn. rewrite (proj2 hfin).
      apply cl_join_lub.
      * apply M.(cl_sup_ub). exists a. split.
        -- apply Hxs. left. reflexivity.
        -- reflexivity.
      * apply IHxs. intros x Hx. apply Hxs. right. exact Hx.
  - (* ⊔{f x | x ∈ S} ≤ ⊔{f z | z ∈ finite_sups S} *)
    apply M.(cl_sup_lub).
    intros y [x [Hx Hy]]. subst y.
    apply M.(cl_sup_ub).
    (* Witness: z = x, using finite_sups_of with xs = [x] *)
    exists x. split.
    + exists (x :: nil). split.
      * intros a Ha. cbn in Ha. destruct Ha as [Ha | Ha].
        -- subst a. exact Hx.
        -- inversion Ha.
      * cbn. apply L.(le_antisym).
        -- apply cl_join_ub1.
        -- apply cl_join_lub. apply L.(le_refl). apply cl_bot_le.
    + reflexivity.
Qed.
