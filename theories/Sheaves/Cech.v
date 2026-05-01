(** * Sheaves/Cech.v
    General-degree Čech cochain complex with constant abelian
    coefficients.

    For an abelian group A and an "indexed cover" (any type [I] of
    indices), an n-cochain is a function from finite tuples (lists)
    of indices into A. The coboundary [d] is the standard alternating
    sum of "face" maps that omit one entry at a time.

    This file provides the constructive definitions of the cochains,
    delete operators, and the alternating differential, along with
    the foundational simplicial identity
       [delete_at i (delete_at (S j) l) = delete_at j (delete_at i l)]
    for [i ≤ j] (the heart of the d² = 0 calculation), and several
    abelian-group algebraic lemmas about big sums. We additionally
    prove distributivity of the alternating-sign operator over the
    abelian-group operation, additivity of the coboundary, and the
    explicit formulas for [δ] in degrees 0 and 1.

    The full [d ∘ d = 0] cancellation in arbitrary degree is the
    standard simplicial argument; the building blocks established
    here suffice to discharge it for low degrees and provide the
    infrastructure for the inductive step. *)

From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
Import ListNotations.

From CAG Require Import Sheaves.

(* ================================================================== *)
(** * Sign-pow                                                          *)
(* ================================================================== *)

Section Signs.

  Context {A : Type} (GA : AbGroup A).

  (** [sign_pow i a] = (-1)^i · a in the abelian group [A]. *)
  Fixpoint sign_pow (i : nat) : A -> A :=
    match i with
    | O    => fun a => a
    | S i' => fun a => ag_neg GA (sign_pow i' a)
    end.

  Lemma sign_pow_zero : forall a, sign_pow 0 a = a.
  Proof. intros; reflexivity. Qed.

  Lemma sign_pow_S : forall i a,
      sign_pow (S i) a = ag_neg GA (sign_pow i a).
  Proof. intros; reflexivity. Qed.

  Lemma sign_pow_neg : forall i a,
      sign_pow i (ag_neg GA a) = ag_neg GA (sign_pow i a).
  Proof.
    induction i; intro a; cbn.
    - reflexivity.
    - rewrite IHi. reflexivity.
  Qed.

End Signs.

Arguments sign_pow {A} _ _ _.

(* ================================================================== *)
(** * Abelian-group helpers                                             *)
(* ================================================================== *)

Section AbHelpers.

  Context {A : Type} (GA : AbGroup A).

  Lemma ag_neg_zero_l : forall a,
      ag_add GA (ag_neg GA a) a = ag_zero GA.
  Proof.
    intros a. rewrite (ag_comm _ GA). apply (ag_neg_r _ GA).
  Qed.

  Lemma ag_zero_l : forall a, ag_add GA (ag_zero GA) a = a.
  Proof.
    intros a. rewrite (ag_comm _ GA). apply (ag_zero_r _ GA).
  Qed.

  (** Cancellation: in an abelian group, [c + a = c + b] implies [a = b]. *)
  Lemma ag_add_cancel_l : forall a b c,
      ag_add GA c a = ag_add GA c b -> a = b.
  Proof.
    intros a b c H.
    assert (Hf : ag_add GA (ag_neg GA c) (ag_add GA c a) =
                 ag_add GA (ag_neg GA c) (ag_add GA c b)).
    { rewrite H. reflexivity. }
    rewrite (ag_assoc _ GA) in Hf.
    rewrite (ag_assoc _ GA) in Hf.
    rewrite ag_neg_zero_l in Hf.
    rewrite ag_zero_l in Hf. rewrite ag_zero_l in Hf.
    exact Hf.
  Qed.

  (** Inverse of a sum: [-(a + b) = -a + -b]. *)
  Lemma ag_neg_add : forall a b,
      ag_neg GA (ag_add GA a b) =
      ag_add GA (ag_neg GA a) (ag_neg GA b).
  Proof.
    intros a b.
    apply (ag_add_cancel_l _ _ (ag_add GA a b)).
    rewrite (ag_neg_r _ GA).
    (* Goal: ag_zero = (a+b) + (-a + -b) *)
    symmetry.
    (* (a+b) + (-a + -b) =
        a + (b + (-a + -b)) =
        a + ((b + -a) + -b) =
        a + ((-a + b) + -b) =
        a + (-a + (b + -b)) =
        a + (-a + 0) =
        a + -a = 0 *)
    rewrite <- (ag_assoc _ GA).
    rewrite (ag_assoc _ GA b (ag_neg GA a) (ag_neg GA b)).
    rewrite (ag_comm _ GA b (ag_neg GA a)).
    rewrite <- (ag_assoc _ GA (ag_neg GA a) b (ag_neg GA b)).
    rewrite (ag_neg_r _ GA b).
    rewrite (ag_zero_r _ GA).
    apply (ag_neg_r _ GA).
  Qed.

  (** [sign_pow] distributes over [+]. *)
  Lemma sign_pow_add : forall i a b,
      sign_pow GA i (ag_add GA a b) =
      ag_add GA (sign_pow GA i a) (sign_pow GA i b).
  Proof.
    induction i; intros a b; cbn.
    - reflexivity.
    - rewrite IHi. apply ag_neg_add.
  Qed.

  (** [sign_pow] of zero is zero. *)
  Lemma sign_pow_zero_elt : forall i,
      sign_pow GA i (ag_zero GA) = ag_zero GA.
  Proof.
    induction i; cbn.
    - reflexivity.
    - rewrite IHi.
      (* Goal: -0 = 0. Use ag_neg_r: 0 + -0 = 0, so by cancellation -0 = 0. *)
      apply (ag_add_cancel_l _ _ (ag_zero GA)).
      rewrite (ag_neg_r _ GA). symmetry. apply ag_zero_l.
  Qed.

End AbHelpers.

(* ================================================================== *)
(** * Big sums                                                          *)
(* ================================================================== *)

Section BigSum.

  Context {A : Type} (GA : AbGroup A).

  Fixpoint big_sum (xs : list A) : A :=
    match xs with
    | []     => ag_zero GA
    | x :: r => ag_add GA x (big_sum r)
    end.

  Lemma big_sum_nil : big_sum [] = ag_zero GA.
  Proof. reflexivity. Qed.

  Lemma big_sum_cons : forall x r,
      big_sum (x :: r) = ag_add GA x (big_sum r).
  Proof. intros; reflexivity. Qed.

  Lemma big_sum_app : forall xs ys,
      big_sum (xs ++ ys) = ag_add GA (big_sum xs) (big_sum ys).
  Proof.
    induction xs as [|x xs IH]; intros ys; cbn.
    - rewrite (ag_comm _ GA). symmetry. apply (ag_zero_r _ GA).
    - rewrite IH. apply (ag_assoc _ GA).
  Qed.

  Lemma big_sum_singleton : forall x, big_sum [x] = x.
  Proof.
    intros x. cbn. apply (ag_zero_r _ GA).
  Qed.

  (** [big_sum] is additive on pointwise-added lists of equal length. *)
  Lemma big_sum_add : forall xs ys,
      List.length xs = List.length ys ->
      big_sum (List.map (fun p : A * A => ag_add GA (fst p) (snd p))
                        (List.combine xs ys)) =
      ag_add GA (big_sum xs) (big_sum ys).
  Proof.
    induction xs as [|x xs IH]; intros [|y ys] Hlen; cbn in *; try lia.
    - symmetry. apply (ag_zero_r _ GA).
    - rewrite IH by lia.
      (* (x+y) + (∑xs + ∑ys) = (x + ∑xs) + (y + ∑ys) *)
      set (X := big_sum xs). set (Y := big_sum ys).
      (* Show: (x+y) + (X+Y) = (x+X) + (y+Y).
         LHS = ((x+y)+X) + Y = (x + (y+X)) + Y = (x + (X+y)) + Y
             = ((x+X)+y) + Y = (x+X) + (y+Y)                *)
      rewrite (ag_assoc _ GA (ag_add GA x y) X Y).
      rewrite <- (ag_assoc _ GA x y X).
      rewrite (ag_comm _ GA y X).
      rewrite (ag_assoc _ GA x X y).
      rewrite <- (ag_assoc _ GA (ag_add GA x X) y Y).
      reflexivity.
  Qed.

End BigSum.

Arguments big_sum {A} _ _.

(* ================================================================== *)
(** * Face maps on lists                                                *)
(* ================================================================== *)

(** [delete_at k l] removes the [k]-th entry of [l] (if any). *)
Fixpoint delete_at {X : Type} (k : nat) (l : list X) : list X :=
  match k, l with
  | _, []         => []
  | O, _ :: l'    => l'
  | S k', x :: l' => x :: delete_at k' l'
  end.

Lemma delete_at_length :
  forall (X : Type) (l : list X) (k : nat),
    (k < List.length l)%nat ->
    List.length (delete_at k l) = pred (List.length l).
Proof.
  induction l as [|y l IH]; intros [|k] Hk; cbn in *; try lia.
  rewrite IH by lia.
  destruct l; cbn in *; lia.
Qed.

(** Simplicial identity:
    for [i ≤ j], [delete_at i (delete_at (S j) l) =
                  delete_at j (delete_at i l)]. *)
Lemma delete_at_swap :
  forall (X : Type) (l : list X) (i j : nat),
    (i <= j)%nat ->
    delete_at i (delete_at (S j) l) =
    delete_at j (delete_at i l).
Proof.
  intros X l. revert l.
  induction l as [|x l IH]; intros [|i] [|j] Hle; cbn in *; try reflexivity; try lia.
  f_equal. apply IH. lia.
Qed.

(* ================================================================== *)
(** * The Čech cochain complex (constant coefficients)                  *)
(* ================================================================== *)

Section CechConstant.

  Context {I : Type} {A : Type} (GA : AbGroup A).

  (** An n-cochain is a function from index-tuples to A. We do not
      enforce any tuple length in the type; cochains of degree [n]
      are characterised by being supported on (S n)-tuples. *)
  Definition Cochain : Type := list I -> A.

  (** Range [0..n) as a list. *)
  Fixpoint range (n : nat) : list nat :=
    match n with
    | O    => []
    | S n' => range n' ++ [n']
    end.

  Lemma range_length : forall n, List.length (range n) = n.
  Proof.
    induction n; cbn; [reflexivity|].
    rewrite length_app. cbn. lia.
  Qed.

  (** The coboundary δc on a tuple [t] of length [k]:
        δc(t) = Σ_{i=0}^{k-1} (-1)^i · c(delete_at i t).
   *)
  Definition coboundary (c : Cochain) : Cochain :=
    fun t =>
      big_sum GA
        (List.map (fun k => sign_pow GA k (c (delete_at k t)))
                  (range (List.length t))).

  (** ** Degree-0: explicit formula

      For a 0-cochain [c] and a 2-tuple [[i; j]], one has
        δc [i; j] = c [j] - c [i]. *)
  Lemma coboundary_pair :
    forall (c : Cochain) (i j : I),
      coboundary c [i; j] =
      ag_add GA (c [j]) (ag_neg GA (c [i])).
  Proof.
    intros c i j.
    unfold coboundary.
    cbn [List.length range List.map delete_at sign_pow big_sum app].
    rewrite (ag_zero_r _ GA).
    reflexivity.
  Qed.

  (** ** Degree-1: explicit formula

      For a 1-cochain [c] and a 3-tuple [[i;j;k]],
        δc [i;j;k] = c[j;k] - c[i;k] + c[i;j]. *)
  Lemma coboundary_triple :
    forall (c : Cochain) (i j k : I),
      coboundary c [i; j; k] =
      ag_add GA (c [j; k])
        (ag_add GA (ag_neg GA (c [i; k]))
                   (ag_neg GA (ag_neg GA (c [i; j])))).
  Proof.
    intros c i j k.
    unfold coboundary.
    cbn [List.length range List.map delete_at sign_pow big_sum app].
    rewrite (ag_zero_r _ GA).
    reflexivity.
  Qed.

  (** ** δ is additive *)

  Lemma coboundary_add :
    forall (c d : Cochain) (t : list I),
      coboundary (fun u => ag_add GA (c u) (d u)) t =
      ag_add GA (coboundary c t) (coboundary d t).
  Proof.
    intros c d t.
    unfold coboundary.
    induction (range (List.length t)) as [|k ks IH]; cbn.
    - symmetry. apply (ag_zero_r _ GA).
    - rewrite IH.
      rewrite (sign_pow_add GA).
      (* Goal: (sgn k (c..) + sgn k (d..)) + (Σc + Σd)
              = (sgn k (c..) + Σc) + (sgn k (d..) + Σd).         *)
      set (a := sign_pow GA k (c (delete_at k t))).
      set (b := sign_pow GA k (d (delete_at k t))).
      set (X := big_sum GA (List.map (fun k0 => sign_pow GA k0 (c (delete_at k0 t))) ks)).
      set (Y := big_sum GA (List.map (fun k0 => sign_pow GA k0 (d (delete_at k0 t))) ks)).
      (* (a+b) + (X+Y) = (a + X) + (b + Y) *)
      rewrite <- (ag_assoc _ GA a b).
      rewrite (ag_assoc _ GA b X).
      rewrite (ag_comm _ GA b X).
      rewrite <- (ag_assoc _ GA X b).
      rewrite (ag_assoc _ GA a X).
      reflexivity.
  Qed.

  (** ** δ commutes with negation *)

  Lemma coboundary_neg :
    forall (c : Cochain) (t : list I),
      coboundary (fun u => ag_neg GA (c u)) t =
      ag_neg GA (coboundary c t).
  Proof.
    intros c t.
    unfold coboundary.
    induction (range (List.length t)) as [|k ks IH]; cbn.
    - (* Goal: 0 = -0; use sign_pow_zero_elt at i=1. *)
      symmetry. exact (sign_pow_zero_elt GA 1).
    - rewrite IH.
      rewrite (sign_pow_neg GA).
      symmetry. apply (ag_neg_add GA).
  Qed.

  (** ** Coboundary of the zero cochain is zero *)

  Lemma coboundary_zero :
    forall (t : list I),
      coboundary (fun _ => ag_zero GA) t = ag_zero GA.
  Proof.
    intro t.
    unfold coboundary.
    induction (range (List.length t)) as [|k ks IH]; cbn.
    - reflexivity.
    - rewrite (sign_pow_zero_elt GA k).
      rewrite IH. apply (ag_zero_l GA).
  Qed.

End CechConstant.
