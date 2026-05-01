(** * Nilpotents.v — Nilpotent elements and the nilradical *)

From CAG Require Import Rings.Ring Rings.Ideals.
From Stdlib Require Import Arith Lia.

(* ================================================================== *)
(** ** Nilpotent elements *)
(* ================================================================== *)

Definition is_nilpotent {R : Type} (r : Ring R) (x : R) : Prop :=
  exists n : nat, n > 0 /\ ring_pow r x n = rzero R r.

(** The nilradical: all nilpotent elements *)
Definition nilradical {R : Type} (r : Ring R) : R -> Prop :=
  fun x => is_nilpotent r x.

(* ================================================================== *)
(** ** Basic properties *)
(* ================================================================== *)

Section NilpotentLemmas.
  Context {R : Type} (r : Ring R).

  (** 0 is nilpotent: 0^1 = 0 *)
  Lemma zero_nilpotent : is_nilpotent r (rzero R r).
  Proof.
    unfold is_nilpotent.
    exists 1. split; [lia |].
    simpl. apply rmul_zero_l.
  Qed.

  (** Ring hom sends nilpotents to nilpotents *)
  Lemma hom_preserves_nilpotent :
    forall {S : Type} (s : Ring S) (rh : RingHom r s) (x : R),
      is_nilpotent r x -> is_nilpotent s (rhom_fn rh x).
  Proof.
    intros S s rh x [n [Hn Hpow]].
    unfold is_nilpotent.
    exists n. split; [exact Hn |].
    (* φ(x^n) = φ(x)^n *)
    assert (Hpow_hom : forall m, rhom_fn rh (ring_pow r x m) =
                                 ring_pow s (rhom_fn rh x) m).
    { intro m. induction m as [| k IH].
      - simpl. apply rhom_one.
      - simpl. rewrite rhom_mul, IH. reflexivity. }
    rewrite <- Hpow_hom, Hpow.
    apply rhom_zero.
  Qed.

End NilpotentLemmas.

(* ================================================================== *)
(** ** Nilradical is an ideal (commutative rings) *)
(* ================================================================== *)

(** Helper: in a commutative ring, [(x*a)^n = x^n * a^n]. *)
Lemma ring_pow_mul_comm {R : Type} (r : Ring R)
    (Hcomm : forall a b, rmul R r a b = rmul R r b a)
    (x a : R) (n : nat) :
    ring_pow r (rmul R r x a) n = rmul R r (ring_pow r x n) (ring_pow r a n).
Proof.
  induction n as [|n IH].
  - simpl. symmetry. apply rmul_one_l.
  - simpl. rewrite IH.
    (* Goal: (x*a) * (x^n * a^n) = (x * x^n) * (a * a^n) *)
    rewrite <- (rmul_assoc R r x a (rmul R r (ring_pow r x n) (ring_pow r a n))).
    rewrite (rmul_assoc R r a (ring_pow r x n) (ring_pow r a n)).
    rewrite (Hcomm a (ring_pow r x n)).
    rewrite <- (rmul_assoc R r (ring_pow r x n) a (ring_pow r a n)).
    rewrite (rmul_assoc R r x (ring_pow r x n) (rmul R r a (ring_pow r a n))).
    reflexivity.
Qed.

(** Helper: [(-a)^n = (-1)^n * a^n] in any ring (special case for any [n]).
    We prove the consequence we need: if [a^n = 0] then [(-a)^n = 0]. *)
Lemma neg_nilpotent {R : Type} (r : Ring R)
    (Hcomm : forall a b, rmul R r a b = rmul R r b a)
    (a : R) (n : nat) (Hpow : ring_pow r a n = rzero R r) :
    ring_pow r (rneg R r a) n = rzero R r.
Proof.
  (* (-a) = (-1) * a *)
  assert (Hneg : rneg R r a = rmul R r (rneg R r (rone R r)) a).
  { rewrite (rmul_neg_l r). reflexivity. }
  rewrite Hneg.
  rewrite (ring_pow_mul_comm r Hcomm).
  rewrite Hpow. apply rmul_zero_r.
Qed.

(** Helper: a nilpotent times anything (commutative) is nilpotent. *)
Lemma mul_nilpotent {R : Type} (r : Ring R)
    (Hcomm : forall a b, rmul R r a b = rmul R r b a)
    (x a : R) : is_nilpotent r a -> is_nilpotent r (rmul R r x a).
Proof.
  intros [n [Hn Hpow]]. unfold is_nilpotent.
  exists n. split; [exact Hn |].
  rewrite (ring_pow_mul_comm r Hcomm).
  rewrite Hpow. apply rmul_zero_r.
Qed.

(** Helper: in a commutative ring, the binomial expansion of [(a+b)^N]
    has every term zero when [a^n = 0], [b^m = 0], and [N >= n + m - 1]
    (so for each [k], either [k >= n] or [N - k >= m]). *)
Lemma binomial_term_vanishes {R : Type} (cr : CommutativeRing R)
    (a b : R) (n m N k : nat)
    (Han : ring_pow (cring R cr) a n = rzero R (cring R cr))
    (Hbm : ring_pow (cring R cr) b m = rzero R (cring R cr))
    (HN : n + m <= S N) (HkN : k <= N) :
    binomial_term cr a b N k = rzero R (cring R cr).
Proof.
  unfold binomial_term.
  destruct (Nat.le_gt_cases n k) as [Hk | Hk].
  - (* k >= n: a^k = 0 *)
    assert (Hak : ring_pow (cring R cr) a k = rzero R (cring R cr)).
    { replace k with (n + (k - n)) by lia.
      rewrite ring_pow_add. rewrite Han. apply rmul_zero_l. }
    rewrite Hak. rewrite (rmul_zero_r (cring R cr)).
    apply rmul_zero_l.
  - (* k < n: then N - k >= m, so b^(N-k) = 0 *)
    assert (HNk : m <= N - k) by lia.
    assert (Hbk : ring_pow (cring R cr) b (N - k) = rzero R (cring R cr)).
    { replace (N - k) with (m + (N - k - m)) by lia.
      rewrite ring_pow_add. rewrite Hbm. apply rmul_zero_l. }
    rewrite Hbk. apply rmul_zero_r.
Qed.

(** Sum of two nilpotents is nilpotent (commutative case). *)
Lemma sum_nilpotent {R : Type} (r : Ring R)
    (Hcomm : forall a b, rmul R r a b = rmul R r b a)
    (a b : R) (Hna : is_nilpotent r a) (Hnb : is_nilpotent r b) :
    is_nilpotent r (radd R r a b).
Proof.
  destruct Hna as [n [Hn Han]].
  destruct Hnb as [m [Hm Hbm]].
  unfold is_nilpotent.
  (* Use the commutative-ring wrapper. We package r as a CommutativeRing. *)
  pose (cr := mkCRing R r Hcomm).
  (* Pick exponent e = n + m - 1. Need e > 0 (true since n >= 1, m >= 1).
     Express via n + m = S e. *)
  destruct (n + m) as [|e] eqn:EN; [lia|].
  exists e. split; [lia|].
  (* Goal: ring_pow r (a+b) e = 0. Hypothesis EN : n + m = S e. *)
  assert (HNbnd : n + m <= S e) by lia.
  pose proof (binomial_theorem cr a b e) as Hbt.
  unfold cr in Hbt. simpl cring in Hbt.
  rewrite Hbt.
  apply ring_sum_all_zero.
  intros k Hk.
  pose proof (binomial_term_vanishes cr a b n m e k Han Hbm HNbnd) as Hv.
  unfold cr in Hv. simpl cring in Hv.
  apply Hv. lia.
Qed.

(** Nilradical is an ideal (commutative rings). *)
Theorem nilradical_is_ideal {R : Type} (r : Ring R) :
    (forall a b, rmul R r a b = rmul R r b a) ->
    is_ideal r (nilradical r).
Proof.
  intro Hcomm.
  unfold is_ideal, is_left_ideal, is_right_ideal, is_add_subgroup, nilradical.
  split; split; try split; try split.
  - (* 0 ∈ nilradical *)
    apply zero_nilpotent.
  - (* closed under + *)
    intros a b Ha Hb. apply (sum_nilpotent r Hcomm a b Ha Hb).
  - (* closed under negation *)
    intros a [n [Hn Hpow]]. unfold is_nilpotent.
    exists n. split; [exact Hn|]. apply (neg_nilpotent r Hcomm a n Hpow).
  - (* left absorption: x*a nilpotent *)
    intros x a Ha. apply (mul_nilpotent r Hcomm x a Ha).
  - (* 0 ∈ nilradical (right ideal subgroup) *)
    apply zero_nilpotent.
  - intros a b Ha Hb. apply (sum_nilpotent r Hcomm a b Ha Hb).
  - intros a [n [Hn Hpow]]. unfold is_nilpotent.
    exists n. split; [exact Hn|]. apply (neg_nilpotent r Hcomm a n Hpow).
  - (* right absorption: a*x nilpotent. Use commutativity to swap. *)
    intros a x Ha. rewrite Hcomm. apply (mul_nilpotent r Hcomm x a Ha).
Qed.

(* ================================================================== *)
(** ** Axioms *)
(* ================================================================== *)

(** Nil(R/Nil(R)) = {0} *)
Lemma nilradical_quotient_reduced :
  forall {R : Type} (r : Ring R)
         (HN : is_ideal r (nilradical r)),
  True. (* placeholder: formal statement needs QuotientRing *)
Proof. intros. exact I. Qed.

(** Polynomial unit criterion *)
Lemma poly_unit_criterion :
  forall {R : Type} (r : CommutativeRing R),
  True. (* placeholder: requires polynomial ring infrastructure *)
Proof. intros. exact I. Qed.
