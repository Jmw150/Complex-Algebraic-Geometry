(** * Order/Lattice.v
    Join-semilattices, complete lattices. *)

Require Import CAG.Order.Poset.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Logic.Classical.
From Stdlib Require Import Lists.List.

Open Scope order_scope.

(** ** Join-semilattice with bottom *)

Record JoinSemilattice : Type := {
  jsl_poset  :> Poset;
  jsl_bot    : jsl_poset.(carrier);
  jsl_join   : jsl_poset.(carrier) -> jsl_poset.(carrier) -> jsl_poset.(carrier);
  jsl_bot_le : forall x, jsl_bot ≤[jsl_poset] x;
  jsl_join_ub1 : forall x y, x ≤[jsl_poset] jsl_join x y;
  jsl_join_ub2 : forall x y, y ≤[jsl_poset] jsl_join x y;
  jsl_join_lub : forall x y z,
    x ≤[jsl_poset] z -> y ≤[jsl_poset] z -> jsl_join x y ≤[jsl_poset] z;
}.

Notation "⊥{ J }" := (jsl_bot J) (at level 0) : order_scope.
Notation "x ∨{ J } y" := (jsl_join J x y) (at level 50) : order_scope.

(** Join is idempotent *)
Lemma join_idem (J : JoinSemilattice) (x : J.(carrier)) :
    x ∨{J} x = x.
Proof.
  apply J.(le_antisym).
  - apply J.(jsl_join_lub); apply J.(le_refl).
  - apply J.(jsl_join_ub1).
Qed.

(** Join is commutative *)
Lemma join_comm (J : JoinSemilattice) (x y : J.(carrier)) :
    x ∨{J} y = y ∨{J} x.
Proof.
  apply J.(le_antisym);
  apply J.(jsl_join_lub);
  [ apply J.(jsl_join_ub2) | apply J.(jsl_join_ub1)
  | apply J.(jsl_join_ub2) | apply J.(jsl_join_ub1) ].
Qed.

(** Join is associative *)
Lemma join_assoc (J : JoinSemilattice) (x y z : J.(carrier)) :
    x ∨{J} (y ∨{J} z) = (x ∨{J} y) ∨{J} z.
Proof.
  apply J.(le_antisym); apply J.(jsl_join_lub).
  - apply J.(le_trans) with (y := x ∨{J} y).
    + apply J.(jsl_join_ub1).
    + apply J.(jsl_join_ub1).
  - apply J.(jsl_join_lub).
    + apply J.(le_trans) with (y := x ∨{J} y).
      * apply J.(jsl_join_ub2).
      * apply J.(jsl_join_ub1).
    + apply J.(jsl_join_ub2).
  - apply J.(jsl_join_lub).
    + apply J.(jsl_join_ub1).
    + apply J.(le_trans) with (y := y ∨{J} z).
      * apply J.(jsl_join_ub1).
      * apply J.(jsl_join_ub2).
  - apply J.(le_trans) with (y := y ∨{J} z).
    + apply J.(jsl_join_ub2).
    + apply J.(jsl_join_ub2).
Qed.

(** x ≤ y iff x ∨ y = y *)
Lemma le_iff_join (J : JoinSemilattice) (x y : J.(carrier)) :
    x ≤[J] y <-> x ∨{J} y = y.
Proof.
  split.
  - intros H.
    apply J.(le_antisym).
    + apply J.(jsl_join_lub); [ exact H | apply J.(le_refl) ].
    + apply J.(jsl_join_ub2).
  - intros H.
    rewrite <- H. apply J.(jsl_join_ub1).
Qed.

(** ** Finite join of a list *)

Fixpoint finite_join (J : JoinSemilattice) (xs : list J.(carrier)) : J.(carrier) :=
  match xs with
  | nil    => ⊥{J}
  | x :: rest => x ∨{J} finite_join J rest
  end.

(** ** Complete lattice *)

Record CompleteLattice : Type := {
  cl_poset  :> Poset;
  cl_sup    : forall (S : cl_poset.(carrier) -> Prop), cl_poset.(carrier);
  cl_sup_ub : forall (S : cl_poset.(carrier) -> Prop) x, S x -> x ≤[cl_poset] cl_sup S;
  cl_sup_lub : forall (S : cl_poset.(carrier) -> Prop) z,
    (forall x, S x -> x ≤[cl_poset] z) -> cl_sup S ≤[cl_poset] z;
}.

Notation "⊔{ L } S" := (cl_sup L S) (at level 9) : order_scope.

(** Infimum derived from supremum *)
Definition cl_inf (L : CompleteLattice) (S : L.(carrier) -> Prop) : L.(carrier) :=
  ⊔{L} (fun z => forall x, S x -> z ≤[L] x).

Notation "⊓{ L } S" := (cl_inf L S) (at level 9) : order_scope.

Lemma cl_inf_lb {L : CompleteLattice} (S : L.(carrier) -> Prop) (x : L.(carrier)) :
    S x -> ⊓{L} S ≤[L] x.
Proof.
  intros Hx. unfold cl_inf.
  apply L.(cl_sup_lub). intros z Hz. apply Hz. exact Hx.
Qed.

Lemma cl_inf_glb {L : CompleteLattice} (S : L.(carrier) -> Prop) (z : L.(carrier)) :
    (forall x, S x -> z ≤[L] x) -> z ≤[L] ⊓{L} S.
Proof.
  intros Hz. unfold cl_inf. apply L.(cl_sup_ub). exact Hz.
Qed.

(** Bottom and top of a complete lattice *)
Definition cl_bot (L : CompleteLattice) : L.(carrier) :=
  ⊔{L} (fun _ => False).

Definition cl_top (L : CompleteLattice) : L.(carrier) :=
  ⊔{L} (fun _ => True).

Lemma cl_bot_le {L : CompleteLattice} (x : L.(carrier)) :
    cl_bot L ≤[L] x.
Proof.
  unfold cl_bot. apply L.(cl_sup_lub). intros y Hy. destruct Hy.
Qed.

Lemma cl_top_ge {L : CompleteLattice} (x : L.(carrier)) :
    x ≤[L] cl_top L.
Proof.
  unfold cl_top. apply L.(cl_sup_ub). exact I.
Qed.

(** Binary join in a complete lattice *)
Definition cl_join (L : CompleteLattice) (x y : L.(carrier)) : L.(carrier) :=
  ⊔{L} (fun z => z = x \/ z = y).

Lemma cl_join_ub1 {L : CompleteLattice} (x y : L.(carrier)) :
    x ≤[L] cl_join L x y.
Proof. unfold cl_join. apply L.(cl_sup_ub). left. reflexivity. Qed.

Lemma cl_join_ub2 {L : CompleteLattice} (x y : L.(carrier)) :
    y ≤[L] cl_join L x y.
Proof. unfold cl_join. apply L.(cl_sup_ub). right. reflexivity. Qed.

Lemma cl_join_lub {L : CompleteLattice} (x y z : L.(carrier)) :
    x ≤[L] z -> y ≤[L] z -> cl_join L x y ≤[L] z.
Proof.
  intros Hx Hy. unfold cl_join.
  apply L.(cl_sup_lub). intros w [Hw | Hw]; subst; assumption.
Qed.

(** Every complete lattice is a join-semilattice *)
Definition cl_to_jsl (L : CompleteLattice) : JoinSemilattice := {|
  jsl_poset   := L;
  jsl_bot     := cl_bot L;
  jsl_join    := cl_join L;
  jsl_bot_le  := @cl_bot_le L;
  jsl_join_ub1 := fun x y => cl_join_ub1 x y;
  jsl_join_ub2 := fun x y => cl_join_ub2 x y;
  jsl_join_lub := fun x y z => cl_join_lub x y z;
|}.

(** ** Fixpoints — Knaster–Tarski *)

(** A monotone function on a complete lattice has a least fixed point. *)
Definition knaster_tarski_lfp (L : CompleteLattice) (f : L →m L) : L.(carrier) :=
  ⊓{L} (fun x => f x ≤[L] x).

Lemma knaster_tarski_lfp_fixed (L : CompleteLattice) (f : L →m L) :
    f (knaster_tarski_lfp L f) = knaster_tarski_lfp L f.
Proof.
  apply L.(le_antisym).
  - apply cl_inf_glb. intros x Hx.
    apply L.(le_trans) with (y := f x).
    + apply (mono_apply f). apply cl_inf_lb. exact Hx.
    + exact Hx.
  - apply cl_inf_lb.
    apply (mono_apply f). apply cl_inf_glb.
    intros x Hx. apply L.(le_trans) with (y := f x).
    + apply (mono_apply f). apply cl_inf_lb. exact Hx.
    + exact Hx.
Qed.

Lemma knaster_tarski_lfp_least (L : CompleteLattice) (f : L →m L) (x : L.(carrier)) :
    f x = x -> knaster_tarski_lfp L f ≤[L] x.
Proof.
  intros Hx. apply cl_inf_lb.
  rewrite Hx. apply L.(le_refl).
Qed.

Notation "μ{ L } f" := (knaster_tarski_lfp L f) (at level 9) : order_scope.
