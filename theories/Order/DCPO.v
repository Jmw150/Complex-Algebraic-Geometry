(** * Order/DCPO.v
    Directed sets, directed-complete posets (dcpos),
    Scott-continuous maps, and the complete lattice → dcpo inclusion. *)

Require Import CAG.Order.Poset.
Require Import CAG.Order.Lattice.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Logic.Classical.
From Stdlib Require Import micromega.Lia.

Open Scope order_scope.

(** ** Directed subset *)

(** A nonempty subset D of a poset P is directed if every finite
    subset has an upper bound in D. We use the two-element closure condition. *)

Record IsDirected (P : Poset) (D : P.(carrier) -> Prop) : Prop := {
  dir_inh  : exists x, D x;
  dir_upper : forall x y, D x -> D y -> exists z, D z /\ x ≤[P] z /\ y ≤[P] z;
}.

(** ** Directed-complete poset *)

(** A DCPO is a poset with joins of all directed subsets. *)
Record DCPO : Type := {
  dcpo_poset :> Poset;
  dcpo_sup   : forall (D : dcpo_poset.(carrier) -> Prop),
                 IsDirected dcpo_poset D ->
                 dcpo_poset.(carrier);
  dcpo_sup_ub : forall (D : dcpo_poset.(carrier) -> Prop)
                       (hD : IsDirected dcpo_poset D) x,
                  D x -> x ≤[dcpo_poset] dcpo_sup D hD;
  dcpo_sup_lub : forall (D : dcpo_poset.(carrier) -> Prop)
                        (hD : IsDirected dcpo_poset D) z,
                   (forall x, D x -> x ≤[dcpo_poset] z) ->
                   dcpo_sup D hD ≤[dcpo_poset] z;
}.

Notation "⊔d{ X } D / hD" := (dcpo_sup X D hD)
  (at level 9, D at level 8, hD at level 8) : order_scope.

(** ** Bottom element *)

(** A pointed DCPO has a bottom element. *)
Record PointedDCPO : Type := {
  pdcpo_dcpo :> DCPO;
  pdcpo_bot  : pdcpo_dcpo.(carrier);
  pdcpo_bot_le : forall x, pdcpo_bot ≤[pdcpo_dcpo] x;
}.

(** ** Scott-continuous map *)

(** f : X -> Y between DCPOs is Scott-continuous if it is
    monotone and preserves directed suprema. *)

(** Simpler formulation of Scott continuity *)
Record IsScottCont (X Y : DCPO) (f : X.(carrier) -> Y.(carrier)) : Prop := {
  sc_mono'  : forall x y, x ≤[X] y -> f x ≤[Y] f y;
  sc_cont'  : forall (D : X.(carrier) -> Prop) (hD : IsDirected X D) (ub : Y.(carrier)),
                (forall x, D x -> f x ≤[Y] ub) ->
                f (⊔d{X} D / hD) ≤[Y] ub;
}.

(** For a Scott-continuous f, the image of a directed set is directed. *)
Lemma image_directed {X Y : DCPO} {f : X.(carrier) -> Y.(carrier)}
    (hf : IsScottCont X Y f) (D : X.(carrier) -> Prop) (hD : IsDirected X D) :
    IsDirected Y (fun y => exists x, D x /\ y = f x).
Proof.
  constructor.
  - destruct (dir_inh _ _ hD) as [x Hx].
    exists (f x). exists x. split; auto.
  - intros fy1 fy2 [x1 [Hx1 Hfy1]] [x2 [Hx2 Hfy2]].
    destruct (dir_upper _ _ hD x1 x2 Hx1 Hx2) as [z [Hz [Hx1z Hx2z]]].
    exists (f z). split.
    + exists z. auto.
    + split.
      * rewrite Hfy1. apply (sc_mono' _ _ _ hf). exact Hx1z.
      * rewrite Hfy2. apply (sc_mono' _ _ _ hf). exact Hx2z.
Qed.

(** ** Complete lattice as a DCPO *)

Definition cl_to_dcpo (L : CompleteLattice) : DCPO := {|
  dcpo_poset := L;
  dcpo_sup   := fun D _ => ⊔{L} D;
  dcpo_sup_ub := fun D _ x Hx => L.(cl_sup_ub) D x Hx;
  dcpo_sup_lub := fun D _ z Hz => L.(cl_sup_lub) D z Hz;
|}.

(** ** Fixpoints in DCPOs (least fixed point via ω-chain) *)

(** An ω-chain is a monotone sequence x_0 ≤ x_1 ≤ x_2 ≤ ... *)
Definition omega_chain (P : Poset) := { f : nat -> P.(carrier) |
  forall n, f n ≤[P] f (S n) }.

(** Any ω-chain is directed. *)
Lemma omega_chain_directed (X : DCPO) (c : omega_chain X) :
    IsDirected X (fun x => exists n, x = proj1_sig c n).
Proof.
  constructor.
  - (* Nonempty: c 0 is in the chain *)
    exists (proj1_sig c 0). exists 0. reflexivity.
  - (* Upper bound: given c m and c n, c (max m n) is above both *)
    intros x y [m Hm] [n Hn].
    (* Monotonicity lemma: i ≤ j → c i ≤ c j *)
    assert (Hmono : forall i j, i <= j -> proj1_sig c i ≤[X] proj1_sig c j).
    { intros i j Hij. induction j.
      - assert (i = 0) by lia. subst. apply X.(le_refl).
      - assert (i <= j \/ i = S j) as [Hlt | Heq] by lia.
        + apply X.(le_trans) with (proj1_sig c j).
          * apply IHj. exact Hlt.
          * exact (proj2_sig c j).
        + subst. apply X.(le_refl). }
    exists (proj1_sig c (Nat.max m n)).
    split.
    + exists (Nat.max m n). reflexivity.
    + split.
      * rewrite Hm. apply Hmono. lia.
      * rewrite Hn. apply Hmono. lia.
Qed.

(** ** Directed subset properties *)

Lemma directed_singleton {P : Poset} (x : P.(carrier)) :
    IsDirected P (fun y => y = x).
Proof.
  constructor.
  - exists x. reflexivity.
  - intros a b Ha Hb.
    exists x. rewrite Ha, Hb.
    split. reflexivity.
    split; apply P.(le_refl).
Qed.

Lemma directed_union {P : Poset} (D1 D2 : P.(carrier) -> Prop)
    (hD1 : IsDirected P D1) (hD2 : IsDirected P D2)
    (hcompat : forall x y, D1 x -> D2 y -> exists z, D1 z /\ D2 z /\ x ≤[P] z /\ y ≤[P] z) :
    IsDirected P (fun x => D1 x \/ D2 x).
Proof.
  constructor.
  - destruct (dir_inh _ _ hD1) as [x Hx]. exists x. left. exact Hx.
  - intros x y Hx Hy.
    destruct Hx as [Hx1 | Hx2], Hy as [Hy1 | Hy2].
    + destruct (dir_upper _ _ hD1 x y Hx1 Hy1) as [z [Hz [Hxz Hyz]]].
      exists z. split. left. exact Hz. split; assumption.
    + destruct (hcompat x y Hx1 Hy2) as [z [Hz1 [Hz2 [Hxz Hyz]]]].
      destruct (dir_upper _ _ hD1 x z Hx1 Hz1) as [w [Hw [Hxw Hzw]]].
      exists w. split. left. exact Hw.
      split. exact Hxw.
      apply P.(le_trans) with z. exact Hyz. exact Hzw.
    + destruct (hcompat y x Hy1 Hx2) as [z [Hz1 [Hz2 [Hyz Hxz]]]].
      destruct (dir_upper _ _ hD1 y z Hy1 Hz1) as [w [Hw [Hyw Hzw]]].
      exists w. split. left. exact Hw.
      split.
      * apply P.(le_trans) with z. exact Hxz. exact Hzw.
      * exact Hyw.
    + destruct (dir_upper _ _ hD2 x y Hx2 Hy2) as [z [Hz [Hxz Hyz]]].
      exists z. split. right. exact Hz. split; assumption.
Qed.

(** ** Monotone maps on DCPOs *)

(** A monotone map that is Scott-continuous. *)
Definition dcpo_cont_map (X Y : DCPO) (f : X.(carrier) -> Y.(carrier))
    (hf : IsScottCont X Y f) : X →m Y.
Proof.
  refine {| mmap := f; mmap_mono := _ |}.
  intros x y h. exact (sc_mono' _ _ _ hf x y h).
Defined.
