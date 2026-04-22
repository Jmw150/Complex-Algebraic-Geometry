(** * Order/Compact.v
    Compact elements, algebraic DCPOs and algebraic complete lattices. *)

Require Import CAG.Order.Poset.
Require Import CAG.Order.Lattice.
Require Import CAG.Order.DCPO.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Logic.Classical.

Open Scope order_scope.

(** ** Compact element

    x is compact in DCPO X if: whenever x ≤ ⊔D for a directed D,
    then x ≤ d for some d ∈ D. *)

Definition IsCompact (X : DCPO) (x : X.(carrier)) : Prop :=
  forall (D : X.(carrier) -> Prop) (hD : IsDirected X D),
    x ≤[X] ⊔d{X} D / hD ->
    exists d, D d /\ x ≤[X] d.

(** Set of compact elements *)
Definition CompactElements (X : DCPO) : X.(carrier) -> Prop :=
  fun x => IsCompact X x.

Notation "X °" := (CompactElements X) (at level 5) : order_scope.

(** Bottom element (if it exists) is compact. *)
Lemma bot_compact (X : PointedDCPO) :
    IsCompact X.(pdcpo_dcpo) X.(pdcpo_bot).
Proof.
  intros D hD _.
  destruct (dir_inh _ _ hD) as [x Hx].
  exists x. split.
  - exact Hx.
  - apply X.(pdcpo_bot_le).
Qed.

(** If a directed join equals x and x is compact, there's a stage below x. *)
Lemma compact_below_directed (X : DCPO) (x : X.(carrier)) (hx : IsCompact X x)
    (D : X.(carrier) -> Prop) (hD : IsDirected X D) :
    x ≤[X] ⊔d{X} D / hD ->
    exists d, D d /\ x ≤[X] d.
Proof. apply hx. Qed.

(** ** Algebraic DCPO

    X is algebraic if every element is the directed join of compact
    elements below it. *)

Definition IsAlgebraic (X : DCPO) : Prop :=
  forall x : X.(carrier),
    (* The set of compact elements below x is directed *)
    IsDirected X (fun e => IsCompact X e /\ e ≤[X] x) /\
    (* x is the sup of compact elements below it *)
    forall ub, (forall e, IsCompact X e -> e ≤[X] x -> e ≤[X] ub) ->
               x ≤[X] ub.

(** ** Algebraic complete lattice *)

Record AlgCompleteLattice : Type := {
  acl_cl  :> CompleteLattice;
  acl_alg : IsAlgebraic (cl_to_dcpo acl_cl);
}.

(** In an algebraic CL, x = sup of compact elements below x. *)
Lemma acl_eq_compact_sup (L : AlgCompleteLattice) (x : L.(carrier)) :
    x = ⊔{L} (fun e => IsCompact (cl_to_dcpo L) e /\ e ≤[L] x).
Proof.
  apply L.(le_antisym).
  - (* x ≤ sup of compact elements below x, by algebraicity *)
    destruct (L.(acl_alg) x) as [_ Hlub].
    apply Hlub. intros e he hle. apply L.(cl_sup_ub). split; assumption.
  - apply L.(cl_sup_lub). intros e [_ He]. exact He.
Qed.

(** ** Compact element in a complete lattice *)

(** In the DCPO of a complete lattice, compactness can be stated more simply. *)
Lemma compact_cl_char (L : CompleteLattice) (x : L.(carrier)) :
    IsCompact (cl_to_dcpo L) x <->
    forall (D : L.(carrier) -> Prop) (hD : IsDirected L D),
      x ≤[L] ⊔{L} D ->
      exists d, D d /\ x ≤[L] d.
Proof.
  split.
  - intros Hc D hD Hle.
    exact (Hc D hD Hle).
  - intros H D hD Hle. exact (H D hD Hle).
Qed.

(** ** Principal compact approximation set *)

(** For x in X, the set of compact elements below x. *)
Definition compact_approx (X : DCPO) (x : X.(carrier)) : X.(carrier) -> Prop :=
  fun e => IsCompact X e /\ e ≤[X] x.

(** In an algebraic DCPO, compact_approx x is directed. *)
Lemma compact_approx_directed (X : DCPO) (hX : IsAlgebraic X) (x : X.(carrier)) :
    IsDirected X (compact_approx X x).
Proof.
  exact (proj1 (hX x)).
Qed.

(** In an algebraic DCPO, x = sup(compact_approx x). *)
Lemma compact_approx_sup (X : DCPO) (hX : IsAlgebraic X) (x : X.(carrier)) :
    forall ub, (forall e, IsCompact X e -> e ≤[X] x -> e ≤[X] ub) ->
               x ≤[X] ub.
Proof.
  exact (proj2 (hX x)).
Qed.

(** ** Compact elements are closed under finite joins (in a JSL) *)

(** In an algebraic complete lattice, the compact elements form a join-semilattice. *)
Lemma compact_join (L : AlgCompleteLattice) (x y : L.(carrier))
    (hx : IsCompact (cl_to_dcpo L) x)
    (hy : IsCompact (cl_to_dcpo L) y) :
    IsCompact (cl_to_dcpo L) (cl_join L x y).
Proof.
  intros D hD Hle.
  (* x ≤ x∨y ≤ ⊔D, so x compact gives x ≤ d1 ∈ D *)
  assert (Hx : x ≤[L] ⊔d{cl_to_dcpo L} D / hD).
  { apply L.(le_trans) with (y := cl_join L x y).
    - apply cl_join_ub1.
    - exact Hle. }
  assert (Hy : y ≤[L] ⊔d{cl_to_dcpo L} D / hD).
  { apply L.(le_trans) with (y := cl_join L x y).
    - apply cl_join_ub2.
    - exact Hle. }
  destruct (hx D hD Hx) as [d1 [Hd1 Hxd1]].
  destruct (hy D hD Hy) as [d2 [Hd2 Hyd2]].
  destruct (dir_upper _ _ hD d1 d2 Hd1 Hd2) as [d [Hd [Hd1d Hd2d]]].
  exists d. split. exact Hd.
  apply cl_join_lub.
  - apply L.(le_trans) with d1; assumption.
  - apply L.(le_trans) with d2; assumption.
Qed.

Lemma compact_bot (L : AlgCompleteLattice) :
    IsCompact (cl_to_dcpo L) (cl_bot L).
Proof.
  intros D hD _.
  destruct (dir_inh _ _ hD) as [x Hx].
  exists x. split. exact Hx. apply cl_bot_le.
Qed.
