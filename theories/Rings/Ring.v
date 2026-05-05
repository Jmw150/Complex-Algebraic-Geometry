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

  (** Additive left cancellation. *)
  Lemma radd_cancel_l : forall a b c,
      radd R r a b = radd R r a c -> b = c.
  Proof.
    intros a b c H.
    assert (H' : radd R r (rneg R r a) (radd R r a b) =
                radd R r (rneg R r a) (radd R r a c)).
    { rewrite H. reflexivity. }
    rewrite (radd_assoc R r (rneg R r a) a b) in H'.
    rewrite (radd_assoc R r (rneg R r a) a c) in H'.
    rewrite radd_neg_l in H'.
    rewrite (radd_zero_l b) in H'.
    rewrite (radd_zero_l c) in H'.
    exact H'.
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

  (** Negation distributes over addition. *)
  Lemma rneg_add : forall a b,
      rneg R r (radd R r a b) =
      radd R r (rneg R r a) (rneg R r b).
  Proof.
    intros a b.
    apply (radd_cancel_l (radd R r a b)).
    rewrite (radd_neg_r R r (radd R r a b)).
    rewrite (radd_assoc R r (radd R r a b) (rneg R r a) (rneg R r b)).
    assert (H : radd R r (radd R r a b) (rneg R r a) = b).
    { rewrite <- (radd_assoc R r a b (rneg R r a)).
      rewrite (radd_comm R r b (rneg R r a)).
      rewrite (radd_assoc R r a (rneg R r a) b).
      rewrite radd_neg_r. apply radd_zero_l. }
    rewrite H. symmetry. apply radd_neg_r.
  Qed.

  (** Multiplication by a negated left factor. *)
  Lemma rmul_neg_l_full : forall a b,
      rmul R r (rneg R r a) b = rneg R r (rmul R r a b).
  Proof.
    intros a b.
    apply (radd_cancel_l (rmul R r a b)).
    rewrite <- (rmul_distrib_r R r a (rneg R r a) b).
    rewrite radd_neg_r.
    rewrite rmul_zero_l.
    symmetry. apply radd_neg_r.
  Qed.

  (** Multiplication by a negated right factor. *)
  Lemma rmul_neg_r_full : forall a b,
      rmul R r a (rneg R r b) = rneg R r (rmul R r a b).
  Proof.
    intros a b.
    apply (radd_cancel_l (rmul R r a b)).
    rewrite <- (rmul_distrib_l R r a b (rneg R r b)).
    rewrite radd_neg_r.
    rewrite rmul_zero_r.
    symmetry. apply radd_neg_r.
  Qed.

End RingLemmas.

(* ================================================================== *)
(** ** Ring power *)
(* ================================================================== *)

Fixpoint ring_pow {R : Type} (r : Ring R) (a : R) (n : nat) : R :=
  match n with
  | O    => rone R r
  | S k  => rmul R r a (ring_pow r a k)
  end.

Lemma ring_pow_add {R : Type} (r : Ring R) :
  forall (a : R) (n m : nat),
    ring_pow r a (n + m) =
    rmul R r (ring_pow r a n) (ring_pow r a m).
Proof.
  intros a n m.
  induction n as [|n IH].
  - simpl. symmetry. apply rmul_one_l.
  - simpl. rewrite IH. apply rmul_assoc.
Qed.

Lemma ring_pow_mul_distrib {R : Type} (cr : CommutativeRing R) :
  forall (a b : R) (n : nat),
    ring_pow (cring R cr) (rmul R (cring R cr) a b) n =
    rmul R (cring R cr)
      (ring_pow (cring R cr) a n)
      (ring_pow (cring R cr) b n).
Proof.
  intros a b n.
  induction n as [|n IH].
  - simpl. symmetry. apply rmul_one_l.
  - simpl. rewrite IH.
    rewrite <- (rmul_assoc R (cring R cr) a b
      (rmul R (cring R cr)
        (ring_pow (cring R cr) a n)
        (ring_pow (cring R cr) b n))).
    rewrite (rmul_assoc R (cring R cr) b
      (ring_pow (cring R cr) a n)
      (ring_pow (cring R cr) b n)).
    rewrite (rmul_comm R cr b (ring_pow (cring R cr) a n)).
    rewrite <- (rmul_assoc R (cring R cr)
      (ring_pow (cring R cr) a n) b
      (ring_pow (cring R cr) b n)).
    rewrite (rmul_assoc R (cring R cr) a
      (ring_pow (cring R cr) a n)
      (rmul R (cring R cr) b (ring_pow (cring R cr) b n))).
    reflexivity.
Qed.

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
