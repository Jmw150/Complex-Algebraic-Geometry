(** * Order/Poset.v
    Posets, monotone maps, order isomorphisms.
    Base layer for domain theory. *)

From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Logic.Classical.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import micromega.Lia.

Declare Scope order_scope.
Open Scope order_scope.

(** ** Poset *)

Record Poset : Type := {
  carrier  :> Type;
  le       : carrier -> carrier -> Prop;
  le_refl  : forall x, le x x;
  le_trans : forall x y z, le x y -> le y z -> le x z;
  le_antisym : forall x y, le x y -> le y x -> x = y;
}.

Notation "x ≤[ P ] y" := (P.(le) x y) (at level 70) : order_scope.

(** ** Monotone map *)

Record MonotoneMap (P Q : Poset) : Type := {
  mmap    :> P.(carrier) -> Q.(carrier);
  mmap_mono : forall x y : P.(carrier), x ≤[P] y -> mmap x ≤[Q] mmap y;
}.

Notation "P →m Q" := (MonotoneMap P Q) (at level 60) : order_scope.

(** Helper for monotone map application *)
Lemma mono_apply {P Q : Poset} (f : P →m Q) {x y : P.(carrier)} :
    x ≤[P] y -> f x ≤[Q] f y.
Proof. destruct f as [fm fmono]. apply fmono. Qed.

(** Composition of monotone maps *)
Definition mmap_comp {P Q R : Poset} (g : Q →m R) (f : P →m Q) : P →m R.
Proof.
  refine {| mmap := fun x => g (f x); mmap_mono := _ |}.
  intros x y h.
  destruct g as [gmap gmono], f as [fmap fmono].
  apply gmono. apply fmono. exact h.
Defined.

Notation "g ∘m f" := (mmap_comp g f) (at level 40) : order_scope.

(** Identity monotone map *)
Definition mmap_id (P : Poset) : P →m P.
Proof.
  refine {| mmap := fun x => x; mmap_mono := _ |}.
  intros x y h. exact h.
Defined.

(** ** Order isomorphism *)

Record OrderIso (P Q : Poset) : Type := {
  iso_fwd  :> P →m Q;
  iso_bwd  : Q →m P;
  iso_inv1 : forall x, iso_bwd (iso_fwd x) = x;
  iso_inv2 : forall y, iso_fwd (iso_bwd y) = y;
}.

Notation "P ≅o Q" := (OrderIso P Q) (at level 70) : order_scope.

(** ** Basic lemmas *)

Lemma le_antisym_eq {P : Poset} {x y : P.(carrier)} :
    x ≤[P] y -> y ≤[P] x -> x = y.
Proof. apply P.(le_antisym). Qed.

Lemma mmap_eq {P Q : Poset} (f g : P →m Q) :
    (forall x, f x = g x) -> f = g.
Proof.
  intros H.
  destruct f as [ff fm], g as [gf gm]. cbn in H.
  assert (Hf : ff = gf) by (extensionality x; apply H).
  subst gf. f_equal. apply proof_irrelevance.
Qed.

(** ** Down-set (principal downward closure) *)

Definition down_set {P : Poset} (x : P.(carrier)) : P.(carrier) -> Prop :=
  fun y => y ≤[P] x.

Notation "x ↓" := (down_set x) (at level 5) : order_scope.

(** ** Upper and lower sets *)

Definition is_lower_set {P : Poset} (S : P.(carrier) -> Prop) : Prop :=
  forall x y, S x -> y ≤[P] x -> S y.

Definition is_upper_set {P : Poset} (S : P.(carrier) -> Prop) : Prop :=
  forall x y, S x -> x ≤[P] y -> S y.

(** ** Subposet *)

Definition SubPoset (P : Poset) (S : P.(carrier) -> Prop) : Poset.
Proof.
  refine {|
    carrier := { x : P.(carrier) | S x };
    le := fun a b => proj1_sig a ≤[P] proj1_sig b;
    le_refl := fun a => P.(le_refl) _;
    le_trans := fun a b c h1 h2 => P.(le_trans) _ _ _ h1 h2;
    le_antisym := _;
  |}.
  intros a b h1 h2.
  apply eq_sig_hprop.
  - intros x. apply proof_irrelevance.
  - apply P.(le_antisym); assumption.
Defined.

(** ** Nat as a poset *)

Definition NatPoset : Poset.
Proof.
  refine {| carrier := nat; le := Peano.le; le_refl := _; le_trans := _; le_antisym := _ |}.
  - intro n. apply Nat.le_refl.
  - intros. eapply Nat.le_trans; eassumption.
  - intros. apply Nat.le_antisymm; assumption.
Defined.

(** ** Bool as a poset (false ≤ true) *)

Definition BoolPoset : Poset.
Proof.
  refine {|
    carrier := bool;
    le := fun a b => a = false \/ b = true;
    le_refl := _;
    le_trans := _;
    le_antisym := _;
  |}.
  - intros a. destruct a; [right | left]; reflexivity.
  - intros a b c h1 h2.
    destruct h1 as [Ha | Hb].
    + left. exact Ha.
    + destruct h2 as [Hb' | Hc].
      * exfalso. rewrite Hb in Hb'. discriminate.
      * right. exact Hc.
  - intros a b h1 h2.
    destruct a, b; try reflexivity.
    + destruct h1 as [H|H]; congruence.
    + destruct h2 as [H|H]; congruence.
Defined.
