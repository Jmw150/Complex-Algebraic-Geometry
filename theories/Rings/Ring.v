(** * Ring.v — Core ring infrastructure

    Defines Ring, CommutativeRing, RingHom, ring_pow, is_subring,
    and derived lemmas. *)

From Stdlib Require Import Arith Lia.

(* ================================================================== *)
(** ** Ring record *)
(* ================================================================== *)

Record Ring (R : Type) : Type := mkRing {
  radd : R -> R -> R;
  rmul : R -> R -> R;
  rzero : R;
  rone  : R;
  rneg  : R -> R;

  radd_assoc  : forall a b c, radd a (radd b c) = radd (radd a b) c;
  radd_comm   : forall a b,   radd a b = radd b a;
  radd_zero_r : forall a,     radd a rzero = a;
  radd_neg_r  : forall a,     radd a (rneg a) = rzero;
  rmul_assoc  : forall a b c, rmul a (rmul b c) = rmul (rmul a b) c;
  rmul_one_r  : forall a,     rmul a rone = a;
  rmul_one_l  : forall a,     rmul rone a = a;
  rmul_distrib_l : forall a b c, rmul a (radd b c) = radd (rmul a b) (rmul a c);
  rmul_distrib_r : forall a b c, rmul (radd a b) c = radd (rmul a c) (rmul b c);
}.

(* Helper: in any Ring, x+x=x => x=0 *)
Lemma ring_cancel_add_self {R : Type} (r : Ring R) (x : R)
    (Hx : radd R r x x = x) : x = rzero R r.
Proof.
  assert (H0 : radd R r x (rneg R r x) = rzero R r) by apply radd_neg_r.
  rewrite <- H0.
  rewrite <- Hx at 2.
  rewrite <- radd_assoc.
  rewrite H0.
  symmetry. apply radd_zero_r.
Qed.

(* ================================================================== *)
(** ** CommutativeRing *)
(* ================================================================== *)

Record CommutativeRing (R : Type) : Type := mkCRing {
  cring :> Ring R;
  rmul_comm : forall a b, rmul R cring a b = rmul R cring b a;
}.

(* ================================================================== *)
(** ** Subtraction *)
(* ================================================================== *)

Definition ring_sub {R : Type} (r : Ring R) (a b : R) : R :=
  radd R r a (rneg R r b).

(* ================================================================== *)
(** ** Derived lemmas *)
(* ================================================================== *)

Section RingLemmas.
  Context {R : Type} (r : Ring R).

  (** 0 + a = a *)
  Lemma radd_zero_l : forall a, radd R r (rzero R r) a = a.
  Proof.
    intro a.
    rewrite (radd_comm R r (rzero R r) a).
    apply radd_zero_r.
  Qed.

  (** -a + a = 0 *)
  Lemma radd_neg_l : forall a, radd R r (rneg R r a) a = rzero R r.
  Proof.
    intro a.
    rewrite (radd_comm R r (rneg R r a) a).
    apply radd_neg_r.
  Qed.

  (** 0 * a = 0 *)
  Lemma rmul_zero_l : forall a, rmul R r (rzero R r) a = rzero R r.
  Proof.
    intro a.
    apply ring_cancel_add_self.
    rewrite <- (rmul_distrib_r R r (rzero R r) (rzero R r) a).
    rewrite (radd_zero_r R r (rzero R r)).
    reflexivity.
  Qed.

  (** a * 0 = 0 *)
  Lemma rmul_zero_r : forall a, rmul R r a (rzero R r) = rzero R r.
  Proof.
    intro a.
    apply ring_cancel_add_self.
    rewrite <- (rmul_distrib_l R r a (rzero R r) (rzero R r)).
    rewrite (radd_zero_r R r (rzero R r)).
    reflexivity.
  Qed.

  (** (-1) * a = -a *)
  Lemma rmul_neg_l : forall a, rmul R r (rneg R r (rone R r)) a = rneg R r a.
  Proof.
    intro a.
    (* (-1)*a + a = ((-1) + 1)*a = 0*a = 0, so (-1)*a = -a *)
    assert (Hsum : radd R r (rmul R r (rneg R r (rone R r)) a) a = rzero R r).
    { rewrite <- (rmul_one_l R r a) at 2.
      rewrite <- rmul_distrib_r.
      rewrite radd_neg_l. apply rmul_zero_l. }
    assert (step : radd R r
                     (radd R r (rmul R r (rneg R r (rone R r)) a) a)
                     (rneg R r a) = rneg R r a).
    { rewrite Hsum. apply radd_zero_l. }
    rewrite <- radd_assoc in step.
    rewrite radd_neg_r in step.
    rewrite radd_zero_r in step.
    exact step.
  Qed.

  (** a * (-1) = -a *)
  Lemma rmul_neg_r : forall a, rmul R r a (rneg R r (rone R r)) = rneg R r a.
  Proof.
    intro a.
    assert (Hsum : radd R r (rmul R r a (rneg R r (rone R r))) a = rzero R r).
    { rewrite <- (rmul_one_r R r a) at 2.
      rewrite <- rmul_distrib_l.
      rewrite radd_neg_l. apply rmul_zero_r. }
    assert (step : radd R r
                     (radd R r (rmul R r a (rneg R r (rone R r))) a)
                     (rneg R r a) = rneg R r a).
    { rewrite Hsum. apply radd_zero_l. }
    rewrite <- radd_assoc in step.
    rewrite radd_neg_r in step.
    rewrite radd_zero_r in step.
    exact step.
  Qed.

  (** Negation is involutive *)
  Lemma rneg_neg : forall a, rneg R r (rneg R r a) = a.
  Proof.
    intro a.
    (* --a = 0 + --a = (a + -a) + --a = a + (-a + --a) = a + 0 = a *)
    rewrite <- (radd_zero_l (rneg R r (rneg R r a))).
    rewrite <- (radd_neg_r R r a).
    rewrite <- radd_assoc.
    rewrite (radd_neg_r R r (rneg R r a)).
    apply radd_zero_r.
  Qed.

End RingLemmas.

(** Inverse uniqueness for addition (outside section to avoid scope issues). *)
Lemma radd_inv_uniq {R : Type} (r : Ring R) (a b : R) :
    radd R r a b = rzero R r -> b = rneg R r a.
Proof.
  intro Hab.
  pose proof (radd_neg_l r a) as Hna.  (* radd (-a) a = 0 *)
  pose proof (radd_assoc R r (rneg R r a) a b) as Hassoc.
  (* Hassoc: radd (-a) (radd a b) = radd (radd (-a) a) b *)
  rewrite Hna in Hassoc.
  (* Hassoc: radd (-a) (radd a b) = radd 0 b *)
  rewrite Hab in Hassoc.
  (* Hassoc: radd (-a) 0 = radd 0 b *)
  rewrite (radd_zero_r R r) in Hassoc.
  rewrite (radd_zero_l r b) in Hassoc.
  symmetry. exact Hassoc.
Qed.

(** -(a + b) = -a + -b *)
Lemma rneg_add {R : Type} (r : Ring R) (a b : R) :
    rneg R r (radd R r a b) = radd R r (rneg R r a) (rneg R r b).
Proof.
  symmetry. apply (radd_inv_uniq r).
  rewrite <- (radd_assoc R r a b (radd R r (rneg R r a) (rneg R r b))).
  rewrite (radd_assoc R r b (rneg R r a) (rneg R r b)).
  rewrite (radd_comm R r b (rneg R r a)).
  rewrite <- (radd_assoc R r (rneg R r a) b (rneg R r b)).
  rewrite (radd_neg_r R r b).
  rewrite (radd_zero_r R r).
  apply (radd_neg_r R r).
Qed.

(** (-a) * b = -(a * b) *)
Lemma rmul_neg_l_full {R : Type} (r : Ring R) (a b : R) :
    rmul R r (rneg R r a) b = rneg R r (rmul R r a b).
Proof.
  apply (radd_inv_uniq r).
  rewrite <- (rmul_distrib_r R r a (rneg R r a) b).
  rewrite (radd_neg_r R r a). apply (rmul_zero_l r).
Qed.

(** a * (-b) = -(a * b) *)
Lemma rmul_neg_r_full {R : Type} (r : Ring R) (a b : R) :
    rmul R r a (rneg R r b) = rneg R r (rmul R r a b).
Proof.
  apply (radd_inv_uniq r).
  rewrite <- (rmul_distrib_l R r a b (rneg R r b)).
  rewrite (radd_neg_r R r b). apply (rmul_zero_r r).
Qed.

(** (-a) * (-b) = a * b *)
Lemma rmul_neg_neg {R : Type} (r : Ring R) (a b : R) :
    rmul R r (rneg R r a) (rneg R r b) = rmul R r a b.
Proof.
  rewrite (rmul_neg_l_full r), (rmul_neg_r_full r), (rneg_neg r).
  reflexivity.
Qed.

(** Additive cancellation: a + b = a + c → b = c. *)
Lemma radd_cancel_l {R : Type} (r : Ring R) (a b c : R) :
    radd R r a b = radd R r a c -> b = c.
Proof.
  intro Habc.
  assert (Habc' : radd R r (rneg R r a) (radd R r a b) =
                  radd R r (rneg R r a) (radd R r a c)).
  { rewrite Habc. reflexivity. }
  rewrite (radd_assoc R r) in Habc'.
  rewrite (radd_assoc R r (rneg R r a) a c) in Habc'.
  rewrite (radd_neg_l r a) in Habc'.
  rewrite (radd_zero_l r b) in Habc'.
  rewrite (radd_zero_l r c) in Habc'.
  exact Habc'.
Qed.

Lemma radd_cancel_r {R : Type} (r : Ring R) (a b c : R) :
    radd R r b a = radd R r c a -> b = c.
Proof.
  intro Habc.
  apply (radd_cancel_l r a).
  rewrite (radd_comm R r a b), (radd_comm R r a c). exact Habc.
Qed.

(* ================================================================== *)
(** ** Ring power *)
(* ================================================================== *)

Fixpoint ring_pow {R : Type} (r : Ring R) (a : R) (n : nat) : R :=
  match n with
  | O    => rone R r
  | S k  => rmul R r a (ring_pow r a k)
  end.

(** Basic identities for [ring_pow]. *)
Lemma ring_pow_zero {R : Type} (r : Ring R) (a : R) :
    ring_pow r a 0 = rone R r.
Proof. reflexivity. Qed.

Lemma ring_pow_one {R : Type} (r : Ring R) (a : R) :
    ring_pow r a 1 = a.
Proof. simpl. apply rmul_one_r. Qed.

(** [a^(n+m) = a^n · a^m]. Holds in any ring (powers of [a] commute among
    themselves by associativity). *)
Lemma ring_pow_add {R : Type} (r : Ring R) (a : R) (n m : nat) :
    ring_pow r a (n + m) = rmul R r (ring_pow r a n) (ring_pow r a m).
Proof.
  induction n as [|n IH].
  - simpl. symmetry. apply rmul_one_l.
  - simpl. rewrite IH. apply rmul_assoc.
Qed.

(** A power of [b] commutes with [b] itself. *)
Lemma ring_pow_comm_self {R : Type} (r : Ring R) (b : R) (k : nat) :
    rmul R r (ring_pow r b k) b = rmul R r b (ring_pow r b k).
Proof.
  induction k as [|k IH].
  - simpl. rewrite rmul_one_l, rmul_one_r. reflexivity.
  - simpl ring_pow.
    rewrite <- rmul_assoc. rewrite IH.
    rewrite rmul_assoc. reflexivity.
Qed.

(** [(a*b)^n = a^n * b^n] in a commutative ring. *)
Section RingPowMul.
  Context {R : Type} (cr : CommutativeRing R).
  Notation r := (cring R cr).

  Lemma ring_pow_mul_distrib : forall (a b : R) (n : nat),
      ring_pow r (rmul R r a b) n =
      rmul R r (ring_pow r a n) (ring_pow r b n).
  Proof.
    intros a b n. induction n as [|n IH].
    - simpl. symmetry. apply rmul_one_l.
    - simpl. rewrite IH.
      (* Goal: a*b * (a^n * b^n) = (a * a^n) * (b * b^n). *)
      rewrite <- (rmul_assoc R r a b (rmul R r (ring_pow r a n) (ring_pow r b n))).
      rewrite (rmul_assoc R r b (ring_pow r a n) (ring_pow r b n)).
      rewrite (rmul_comm R cr b (ring_pow r a n)).
      rewrite <- (rmul_assoc R r (ring_pow r a n) b (ring_pow r b n)).
      rewrite (rmul_assoc R r a (ring_pow r a n) (rmul R r b (ring_pow r b n))).
      reflexivity.
  Qed.

End RingPowMul.

(** [a^(n·m) = (a^n)^m]. *)
Lemma ring_pow_mul {R : Type} (r : Ring R) (a : R) (n m : nat) :
    ring_pow r a (n * m) = ring_pow r (ring_pow r a n) m.
Proof.
  induction m as [|m IH]; [rewrite Nat.mul_0_r; reflexivity|].
  rewrite Nat.mul_succ_r.
  rewrite ring_pow_add.
  rewrite IH.
  simpl ring_pow.
  apply ring_pow_comm_self.
Qed.

(* ================================================================== *)
(** ** Finite ring sums *)
(* ================================================================== *)

(** [ring_sum r f n] computes [f 0 + f 1 + ... + f (n-1)] in [r]. *)
Fixpoint ring_sum {R : Type} (r : Ring R) (f : nat -> R) (n : nat) : R :=
  match n with
  | O   => rzero R r
  | S k => radd R r (ring_sum r f k) (f k)
  end.

Lemma ring_sum_ext {R : Type} (r : Ring R) (f g : nat -> R) (n : nat) :
    (forall k, k < n -> f k = g k) -> ring_sum r f n = ring_sum r g n.
Proof.
  induction n as [|n IH]; intro Heq; [reflexivity|].
  simpl. rewrite IH by (intros; apply Heq; lia).
  rewrite (Heq n) by lia. reflexivity.
Qed.

Lemma ring_sum_mul_l {R : Type} (r : Ring R) (x : R) (f : nat -> R) (n : nat) :
    rmul R r x (ring_sum r f n) = ring_sum r (fun k => rmul R r x (f k)) n.
Proof.
  induction n as [|n IH]; simpl.
  - apply rmul_zero_r.
  - rewrite rmul_distrib_l. rewrite IH. reflexivity.
Qed.

Lemma ring_sum_mul_r {R : Type} (r : Ring R) (x : R) (f : nat -> R) (n : nat) :
    rmul R r (ring_sum r f n) x = ring_sum r (fun k => rmul R r (f k) x) n.
Proof.
  induction n as [|n IH]; simpl.
  - apply rmul_zero_l.
  - rewrite rmul_distrib_r. rewrite IH. reflexivity.
Qed.

Lemma ring_sum_zero_fn {R : Type} (r : Ring R) (n : nat) :
    ring_sum r (fun _ => rzero R r) n = rzero R r.
Proof.
  induction n as [|n IH]; [reflexivity|].
  simpl. rewrite IH. apply radd_zero_r.
Qed.

Lemma ring_sum_add {R : Type} (r : Ring R) (f g : nat -> R) (n : nat) :
    ring_sum r (fun k => radd R r (f k) (g k)) n =
    radd R r (ring_sum r f n) (ring_sum r g n).
Proof.
  induction n as [|n IH]; simpl.
  - symmetry. apply radd_zero_r.
  - rewrite IH.
    rewrite <- (radd_assoc R r (ring_sum r f n) (ring_sum r g n) (radd R r (f n) (g n))).
    rewrite (radd_assoc R r (ring_sum r g n) (f n) (g n)).
    rewrite (radd_comm R r (ring_sum r g n) (f n)).
    rewrite <- (radd_assoc R r (f n) (ring_sum r g n) (g n)).
    rewrite (radd_assoc R r (ring_sum r f n) (f n) (radd R r (ring_sum r g n) (g n))).
    reflexivity.
Qed.

(** Index shift: [sum_{k=0..n+1} f k = f 0 + sum_{k=0..n} f (S k)]. *)
Lemma ring_sum_shift {R : Type} (r : Ring R) (f : nat -> R) (n : nat) :
    ring_sum r f (S n) = radd R r (f 0) (ring_sum r (fun k => f (S k)) n).
Proof.
  induction n as [|n IH].
  - simpl. rewrite radd_zero_l, radd_zero_r. reflexivity.
  - change (ring_sum r f (S (S n))) with (radd R r (ring_sum r f (S n)) (f (S n))).
    rewrite IH.
    change (ring_sum r (fun k : nat => f (S k)) (S n))
      with (radd R r (ring_sum r (fun k : nat => f (S k)) n) (f (S n))).
    symmetry. apply radd_assoc.
Qed.

(** Extending a sum by a zero term doesn't change its value. *)
Lemma ring_sum_extend_zero {R : Type} (r : Ring R) (f : nat -> R) (n : nat) :
    f n = rzero R r ->
    ring_sum r f (S n) = ring_sum r f n.
Proof.
  intros Hf. simpl. rewrite Hf. apply radd_zero_r.
Qed.

(** A sum of zero terms is zero. *)
Lemma ring_sum_all_zero {R : Type} (r : Ring R) (f : nat -> R) (n : nat) :
    (forall k, k < n -> f k = rzero R r) ->
    ring_sum r f n = rzero R r.
Proof.
  intro Hf.
  rewrite (ring_sum_ext r f (fun _ => rzero R r) n) by (intros; apply Hf; assumption).
  apply ring_sum_zero_fn.
Qed.

(* ================================================================== *)
(** ** Binomial coefficients (Pascal's triangle) *)
(* ================================================================== *)

Fixpoint binomial (n k : nat) : nat :=
  match n, k with
  | _,    0   => 1
  | 0,    S _ => 0
  | S n', S k' => binomial n' k' + binomial n' (S k')
  end.

Lemma binomial_zero_r : forall n, binomial n 0 = 1.
Proof. intro n; destruct n; reflexivity. Qed.

Lemma binomial_zero_l : forall k, binomial 0 (S k) = 0.
Proof. intro; reflexivity. Qed.

Lemma binomial_succ_succ : forall n k,
    binomial (S n) (S k) = binomial n k + binomial n (S k).
Proof. intros; reflexivity. Qed.

Lemma binomial_gt : forall n k, n < k -> binomial n k = 0.
Proof.
  induction n as [|n IH]; intros k Hlt.
  - destruct k; [lia | reflexivity].
  - destruct k; [lia |].
    simpl. rewrite IH by lia. rewrite IH by lia. reflexivity.
Qed.

Lemma binomial_n_n : forall n, binomial n n = 1.
Proof.
  induction n as [|n IH]; [reflexivity|].
  simpl. rewrite IH. rewrite binomial_gt by lia. reflexivity.
Qed.

(* ================================================================== *)
(** ** Embedding [nat] into a ring *)
(* ================================================================== *)

Fixpoint ring_of_nat {R : Type} (r : Ring R) (n : nat) : R :=
  match n with
  | O   => rzero R r
  | S k => radd R r (rone R r) (ring_of_nat r k)
  end.

Lemma ring_of_nat_zero {R : Type} (r : Ring R) :
    ring_of_nat r 0 = rzero R r.
Proof. reflexivity. Qed.

Lemma ring_of_nat_one {R : Type} (r : Ring R) :
    ring_of_nat r 1 = rone R r.
Proof. simpl. apply radd_zero_r. Qed.

Lemma ring_of_nat_add {R : Type} (r : Ring R) : forall n m,
    ring_of_nat r (n + m) = radd R r (ring_of_nat r n) (ring_of_nat r m).
Proof.
  induction n as [|n IH]; intro m.
  - simpl. symmetry. apply radd_zero_l.
  - simpl. rewrite IH. apply radd_assoc.
Qed.

(* ================================================================== *)
(** ** Binomial theorem in a commutative ring *)
(* ================================================================== *)

Section BinomialTheorem.
  Context {R : Type} (cr : CommutativeRing R).
  Notation r := (cring R cr).

  (** The k-th term of the binomial expansion of [(a+b)^n]:
      [binomial n k * a^k * b^(n-k)]. *)
  Definition binomial_term (a b : R) (n k : nat) : R :=
    rmul R r (rmul R r (ring_of_nat r (binomial n k)) (ring_pow r a k))
              (ring_pow r b (n - k)).

  Lemma a_mul_binomial_term : forall (a b : R) (n k : nat),
      rmul R r a (binomial_term a b n k) =
      rmul R r (rmul R r (ring_of_nat r (binomial n k)) (ring_pow r a (S k)))
                (ring_pow r b (n - k)).
  Proof.
    intros a b n k. unfold binomial_term.
    rewrite (rmul_assoc R r a _ _). f_equal.
    rewrite (rmul_assoc R r a (ring_of_nat r (binomial n k)) (ring_pow r a k)).
    rewrite (rmul_comm R cr a (ring_of_nat r (binomial n k))).
    rewrite <- (rmul_assoc R r (ring_of_nat r (binomial n k)) a (ring_pow r a k)).
    reflexivity.
  Qed.

  Lemma b_mul_binomial_term : forall (a b : R) (n k : nat),
      rmul R r b (binomial_term a b n k) =
      rmul R r (rmul R r (ring_of_nat r (binomial n k)) (ring_pow r a k))
                (ring_pow r b (S (n - k))).
  Proof.
    intros a b n k. unfold binomial_term.
    rewrite (rmul_assoc R r b _ _).
    rewrite (rmul_comm R cr b (rmul R r (ring_of_nat r (binomial n k)) (ring_pow r a k))).
    rewrite <- (rmul_assoc R r (rmul R r (ring_of_nat r (binomial n k)) (ring_pow r a k)) b (ring_pow r b (n - k))).
    reflexivity.
  Qed.

  Lemma binomial_term_zero_idx : forall (a b : R) (n : nat),
      binomial_term a b n 0 = ring_pow r b n.
  Proof.
    intros a b n. unfold binomial_term.
    rewrite binomial_zero_r.
    rewrite ring_of_nat_one.
    rewrite Nat.sub_0_r.
    simpl ring_pow. rewrite rmul_one_r, rmul_one_l. reflexivity.
  Qed.

  Lemma binomial_term_diag : forall (a b : R) (n : nat),
      binomial_term a b n n = ring_pow r a n.
  Proof.
    intros a b n. unfold binomial_term.
    rewrite binomial_n_n. rewrite Nat.sub_diag.
    rewrite ring_of_nat_one.
    simpl ring_pow. rewrite rmul_one_r, rmul_one_l. reflexivity.
  Qed.

  (** Sum decomposition lemma used in the binomial theorem proof.
      Peels off [b^(S n)] from a sum where the b-exponent is [S(n-k)],
      converting to a sum where the binomial index is [S k]. *)
  Lemma binomial_sum_b_decomp : forall (a b : R) (n : nat),
      ring_sum r (fun k => rmul R r (rmul R r (ring_of_nat r (binomial n k)) (ring_pow r a k))
                                     (ring_pow r b (S (n - k)))) (S n) =
      radd R r (ring_pow r b (S n))
             (ring_sum r (fun k => rmul R r (rmul R r (ring_of_nat r (binomial n (S k))) (ring_pow r a (S k)))
                                              (ring_pow r b (n - k))) (S n)).
  Proof.
    intros a b n.
    rewrite ring_sum_shift. cbv beta.
    rewrite Nat.sub_0_r.
    rewrite binomial_zero_r, ring_of_nat_one. simpl ring_pow.
    rewrite rmul_one_r, rmul_one_l.
    f_equal.
    rewrite (ring_sum_extend_zero r _ n).
    2: {
      rewrite (binomial_gt n (S n)) by lia.
      rewrite ring_of_nat_zero.
      rewrite (rmul_zero_l r). apply (rmul_zero_l r).
    }
    apply ring_sum_ext.
    intros k Hk.
    replace (n - k) with (S (n - S k)) by lia.
    reflexivity.
  Qed.

  (** **The binomial theorem**, in a commutative ring:
      [(a + b)^n = sum_{k=0..n} C(n, k) * a^k * b^(n-k)]. *)
  Theorem binomial_theorem : forall (a b : R) (n : nat),
      ring_pow r (radd R r a b) n =
      ring_sum r (fun k => binomial_term a b n k) (S n).
  Proof.
    intros a b n.
    induction n as [|n IH].
    - simpl. unfold binomial_term. simpl.
      rewrite radd_zero_l, radd_zero_r, rmul_one_l, rmul_one_l. reflexivity.
    - simpl ring_pow.
      rewrite IH.
      rewrite rmul_distrib_r.
      rewrite !ring_sum_mul_l.
      rewrite (ring_sum_ext r (fun k => rmul R r a (binomial_term a b n k))
                              (fun k => rmul R r (rmul R r (ring_of_nat r (binomial n k)) (ring_pow r a (S k))) (ring_pow r b (n - k))))
        by (intros; apply a_mul_binomial_term).
      rewrite (ring_sum_ext r (fun k => rmul R r b (binomial_term a b n k))
                              (fun k => rmul R r (rmul R r (ring_of_nat r (binomial n k)) (ring_pow r a k)) (ring_pow r b (S (n - k)))))
        by (intros; apply b_mul_binomial_term).
      rewrite (ring_sum_shift r (fun k => binomial_term a b (S n) k) (S n)). cbv beta.
      rewrite binomial_term_zero_idx.
      rewrite (ring_sum_ext r (fun k => binomial_term a b (S n) (S k))
                              (fun k => radd R r
                                  (rmul R r (rmul R r (ring_of_nat r (binomial n k)) (ring_pow r a (S k))) (ring_pow r b (n - k)))
                                  (rmul R r (rmul R r (ring_of_nat r (binomial n (S k))) (ring_pow r a (S k))) (ring_pow r b (n - k))))).
      2: {
        intros k Hk. unfold binomial_term.
        rewrite binomial_succ_succ. rewrite ring_of_nat_add.
        change (S n - S k) with (n - k).
        rewrite (rmul_distrib_r R r (ring_of_nat r (binomial n k)) (ring_of_nat r (binomial n (S k))) (ring_pow r a (S k))).
        rewrite rmul_distrib_r. reflexivity.
      }
      rewrite ring_sum_add.
      rewrite (binomial_sum_b_decomp a b n).
      rewrite (radd_assoc R r
                 (ring_sum r (fun k => rmul R r (rmul R r (ring_of_nat r (binomial n k)) (ring_pow r a (S k))) (ring_pow r b (n - k))) (S n))
                 (ring_pow r b (S n))
                 (ring_sum r (fun k => rmul R r (rmul R r (ring_of_nat r (binomial n (S k))) (ring_pow r a (S k))) (ring_pow r b (n - k))) (S n))).
      rewrite (radd_comm R r
                 (ring_sum r (fun k => rmul R r (rmul R r (ring_of_nat r (binomial n k)) (ring_pow r a (S k))) (ring_pow r b (n - k))) (S n))
                 (ring_pow r b (S n))).
      rewrite <- (radd_assoc R r
                 (ring_pow r b (S n))
                 (ring_sum r (fun k => rmul R r (rmul R r (ring_of_nat r (binomial n k)) (ring_pow r a (S k))) (ring_pow r b (n - k))) (S n))
                 (ring_sum r (fun k => rmul R r (rmul R r (ring_of_nat r (binomial n (S k))) (ring_pow r a (S k))) (ring_pow r b (n - k))) (S n))).
      reflexivity.
  Qed.

End BinomialTheorem.

(* ================================================================== *)
(** ** Subring predicate *)
(* ================================================================== *)

Definition is_subring {R : Type} (r : Ring R) (S : R -> Prop) : Prop :=
  S (rzero R r) /\
  S (rone R r)  /\
  (forall a b, S a -> S b -> S (radd R r a b)) /\
  (forall a b, S a -> S b -> S (rmul R r a b)) /\
  (forall a,   S a -> S (rneg R r a)).

(* ================================================================== *)
(** ** Ring homomorphism *)
(* ================================================================== *)

Record RingHom {R S : Type} (r : Ring R) (s : Ring S) : Type := mkRHom {
  rhom_fn  : R -> S;
  rhom_add : forall a b, rhom_fn (radd R r a b) = radd S s (rhom_fn a) (rhom_fn b);
  rhom_mul : forall a b, rhom_fn (rmul R r a b) = rmul S s (rhom_fn a) (rhom_fn b);
  rhom_one : rhom_fn (rone R r) = rone S s;
}.

Arguments rhom_fn  {R S r s} _ _.
Arguments rhom_add {R S r s} _ _ _.
Arguments rhom_mul {R S r s} _ _ _.
Arguments rhom_one {R S r s} _.

(** Derived: φ(0) = 0 *)
Lemma rhom_zero : forall {R S : Type} (r : Ring R) (s : Ring S)
    (rh : RingHom r s),
    rhom_fn rh (rzero R r) = rzero S s.
Proof.
  intros R S r s rh.
  apply ring_cancel_add_self.
  rewrite <- rhom_add.
  rewrite radd_zero_r.
  reflexivity.
Qed.

(** Derived: φ(-a) = -φ(a) *)
Lemma rhom_neg : forall {R S : Type} (r : Ring R) (s : Ring S)
    (rh : RingHom r s) (a : R),
    rhom_fn rh (rneg R r a) = rneg S s (rhom_fn rh a).
Proof.
  intros R S r s rh a.
  (* φ(-a) + φ(a) = φ(-a + a) = φ(0) = 0, so φ(-a) = -φ(a) *)
  assert (Hsum : radd S s (rhom_fn rh (rneg R r a)) (rhom_fn rh a) = rzero S s).
  { rewrite <- rhom_add. rewrite radd_neg_l. apply rhom_zero. }
  assert (step : radd S s
                   (radd S s (rhom_fn rh (rneg R r a)) (rhom_fn rh a))
                   (rneg S s (rhom_fn rh a)) = rneg S s (rhom_fn rh a)).
  { rewrite Hsum. apply radd_zero_l. }
  rewrite <- radd_assoc in step.
  rewrite radd_neg_r in step.
  rewrite radd_zero_r in step.
  exact step.
Qed.
