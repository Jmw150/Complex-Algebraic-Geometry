(** * Domains/Divisibility.v — Integral domains, divisibility, and units

    Formalizes the basic theory of divisibility in commutative rings
    and integral domains.

    Reference: Dummit & Foote §8.1–8.2. *)

From CAG Require Import Rings.Ring.
From Stdlib Require Import Arith Lia.

(* ================================================================== *)
(** ** Integral domains *)
(* ================================================================== *)

(** An integral domain: commutative ring with 1 ≠ 0 and no zero divisors.
    We store the underlying Ring explicitly to avoid coercion issues. *)
Record IntegralDomain (R : Type) : Type := mkID {
  id_r          : Ring R;
  id_comm       : forall a b : R, rmul R id_r a b = rmul R id_r b a;
  id_nontrivial : rone R id_r <> rzero R id_r;
  id_no_zero_div : forall a b : R,
    rmul R id_r a b = rzero R id_r ->
    a = rzero R id_r \/ b = rzero R id_r;
}.

Arguments id_r           {R} _.
Arguments id_comm        {R} _ _ _.
Arguments id_nontrivial  {R} _.
Arguments id_no_zero_div {R} _ _ _.

(* ================================================================== *)
(** ** Divisibility — section with explicit Ring R *)
(* ================================================================== *)

Section Divisibility.
  (** We work with explicit r : Ring R to enable clean rewrites *)
  Context {R : Type} (r : Ring R).
  Context (Hcomm : forall a b : R, rmul R r a b = rmul R r b a).

  (** a divides b: ∃ c, b = a * c *)
  Definition divides (a b : R) : Prop :=
    exists c : R, b = rmul R r a c.

  (** Every element divides zero *)
  Lemma divides_zero : forall a : R, divides a (rzero R r).
  Proof.
    intro a. unfold divides.
    exists (rzero R r). symmetry. apply rmul_zero_r.
  Qed.

  (** Zero divides only zero *)
  Lemma zero_divides : forall a : R,
      divides (rzero R r) a -> a = rzero R r.
  Proof.
    intros a [c Hc]. rewrite Hc. apply rmul_zero_l.
  Qed.

  (** One divides everything *)
  Lemma one_divides : forall a : R, divides (rone R r) a.
  Proof.
    intro a. exists a. symmetry. apply rmul_one_l.
  Qed.

  (** Divisibility is reflexive *)
  Lemma divides_refl : forall a : R, divides a a.
  Proof.
    intro a. exists (rone R r). symmetry. apply rmul_one_r.
  Qed.

  (** Divisibility is transitive *)
  Lemma divides_trans : forall a b c : R,
      divides a b -> divides b c -> divides a c.
  Proof.
    intros a b c [x Hx] [y Hy].
    exists (rmul R r x y).
    rewrite Hy, Hx.
    symmetry. apply rmul_assoc.
  Qed.

  (** If a divides b and c, then a divides b + c *)
  Lemma divides_add : forall a b c : R,
      divides a b -> divides a c -> divides a (radd R r b c).
  Proof.
    intros a b c [x Hx] [y Hy].
    exists (radd R r x y).
    rewrite Hx, Hy. symmetry. apply rmul_distrib_l.
  Qed.

  (** If a divides b, then a divides x*b for any x *)
  Lemma divides_mul_l : forall a b x : R,
      divides a b -> divides a (rmul R r x b).
  Proof.
    intros a b x [c Hc].
    exists (rmul R r x c).
    rewrite Hc.
    rewrite rmul_assoc, (Hcomm x a).
    symmetry. apply rmul_assoc.
  Qed.

  Lemma divides_mul_r : forall a b x : R,
      divides a b -> divides a (rmul R r b x).
  Proof.
    intros a b x [c Hc].
    exists (rmul R r c x).
    rewrite Hc. symmetry. apply rmul_assoc.
  Qed.

  (** Divisibility and negation *)
  Lemma divides_neg : forall a b : R,
      divides a b -> divides a (rneg R r b).
  Proof.
    intros a b [c Hc].
    exists (rneg R r c). rewrite Hc. symmetry.
    assert (H : radd R r (rmul R r a (rneg R r c)) (rmul R r a c) = rzero R r).
    { rewrite <- rmul_distrib_l. rewrite radd_neg_l. apply rmul_zero_r. }
    assert (step : radd R r
                     (radd R r (rmul R r a (rneg R r c)) (rmul R r a c))
                     (rneg R r (rmul R r a c)) = rneg R r (rmul R r a c)).
    { rewrite H. apply radd_zero_l. }
    rewrite <- radd_assoc in step.
    rewrite radd_neg_r in step.
    rewrite radd_zero_r in step.
    exact step.
  Qed.

End Divisibility.

(** Expose divides for an IntegralDomain *)
Definition id_divides {R : Type} (d : IntegralDomain R) :=
  @divides R (id_r d).

(* ================================================================== *)
(** ** Units — section with explicit Ring R *)
(* ================================================================== *)

Section Units.
  Context {R : Type} (r : Ring R).
  Context (Hcomm : forall a b : R, rmul R r a b = rmul R r b a).
  Context (Hnontrivial : rone R r <> rzero R r).
  Context (Hno_zero_div : forall a b : R,
    rmul R r a b = rzero R r -> a = rzero R r \/ b = rzero R r).

  (** a is a unit if it has a multiplicative inverse *)
  Definition is_unit (a : R) : Prop :=
    exists b : R,
      rmul R r a b = rone R r /\ rmul R r b a = rone R r.

  (** 1 is a unit *)
  Lemma unit_one : is_unit (rone R r).
  Proof.
    unfold is_unit. exists (rone R r). split; apply rmul_one_r.
  Qed.

  (** Units divide everything *)
  Lemma unit_divides_all : forall a : R,
      is_unit a -> forall b, divides r a b.
  Proof.
    intros a [inv [Hinvr Hinvl]] b.
    unfold divides. exists (rmul R r inv b).
    (* b = a * (inv * b) = (a * inv) * b = 1 * b = b *)
    symmetry.
    transitivity (rmul R r (rmul R r a inv) b).
    + exact (rmul_assoc R r a inv b).
    + rewrite Hinvr. apply rmul_one_l.
  Qed.

  (** a is a unit iff a | 1 *)
  Lemma unit_iff_divides_one : forall a : R,
      is_unit a <-> divides r a (rone R r).
  Proof.
    intro a. split.
    - intro Hu. apply unit_divides_all. exact Hu.
    - intros [b Hb]. unfold is_unit.
      exists b. split.
      + exact (eq_sym Hb).
      + rewrite (Hcomm b a). exact (eq_sym Hb).
  Qed.

  (** Products of units are units *)
  Lemma unit_mul : forall a b : R,
      is_unit a -> is_unit b -> is_unit (rmul R r a b).
  Proof.
    intros a b [ainv [Har Hal]] [binv [Hbr Hbl]].
    unfold is_unit.
    exists (rmul R r binv ainv). split.
    - (* (a*b)*(binv*ainv) = ((a*b)*binv)*ainv = (a*(b*binv))*ainv = (a*1)*ainv = a*ainv = 1 *)
      transitivity (rmul R r (rmul R r (rmul R r a b) binv) ainv).
      + exact (rmul_assoc R r (rmul R r a b) binv ainv).
      + rewrite <- (rmul_assoc R r a b binv), Hbr, rmul_one_r, Har. reflexivity.
    - (* (binv*ainv)*(a*b) = ((binv*ainv)*a)*b = (binv*(ainv*a))*b = (binv*1)*b = binv*b = 1 *)
      transitivity (rmul R r (rmul R r (rmul R r binv ainv) a) b).
      + exact (rmul_assoc R r (rmul R r binv ainv) a b).
      + rewrite <- (rmul_assoc R r binv ainv a), Hal, rmul_one_r, Hbl. reflexivity.
  Qed.

  Lemma zero_not_unit : ~ is_unit (rzero R r).
  Proof.
    intros [b [Hb _]].
    apply Hnontrivial. rewrite <- Hb. apply rmul_zero_l.
  Qed.

  (** Cancellation: if a ≠ 0 and a*b = a*c, then b = c *)
  Lemma mul_cancel_l : forall a b c : R,
      a <> rzero R r ->
      rmul R r a b = rmul R r a c ->
      b = c.
  Proof.
    intros a b c Ha Heq.
    assert (H : rmul R r a (radd R r b (rneg R r c)) = rzero R r).
    { rewrite rmul_distrib_l, Heq.
      assert (Hn : rmul R r a (rneg R r c) = rneg R r (rmul R r a c)).
      { assert (Hsum : radd R r (rmul R r a (rneg R r c)) (rmul R r a c) = rzero R r).
        { rewrite <- rmul_distrib_l. rewrite radd_neg_l. apply rmul_zero_r. }
        assert (step : radd R r
                         (radd R r (rmul R r a (rneg R r c)) (rmul R r a c))
                         (rneg R r (rmul R r a c)) = rneg R r (rmul R r a c)).
        { rewrite Hsum. apply radd_zero_l. }
        rewrite <- radd_assoc in step.
        rewrite radd_neg_r in step.
        rewrite radd_zero_r in step.
        exact step. }
      rewrite Hn. apply radd_neg_r. }
    destruct (Hno_zero_div a (radd R r b (rneg R r c)) H) as [Ha' | Hbc].
    - contradiction.
    - assert (Hstep : radd R r (radd R r b (rneg R r c)) c = c).
      { rewrite Hbc. apply radd_zero_l. }
      rewrite <- radd_assoc in Hstep.
      rewrite radd_neg_l in Hstep.
      rewrite radd_zero_r in Hstep.
      exact Hstep.
  Qed.

End Units.

(** Wrappers for IntegralDomain *)
Definition id_is_unit {R : Type} (d : IntegralDomain R) :=
  @is_unit R (id_r d).

Definition id_unit_mul {R : Type} (d : IntegralDomain R) :=
  @unit_mul R (id_r d).

Definition id_zero_not_unit {R : Type} (d : IntegralDomain R) :=
  zero_not_unit (id_r d) (id_nontrivial d).

Definition id_mul_cancel {R : Type} (d : IntegralDomain R) :=
  mul_cancel_l (id_r d) (id_no_zero_div d).

(* ================================================================== *)
(** ** Building IntegralDomains from CommutativeRings *)
(* ================================================================== *)

Definition mkIDfromCRing {R : Type} (cr : CommutativeRing R)
    (Hnontrivial : rone R cr <> rzero R cr)
    (Hnozero : forall a b : R,
        rmul R cr a b = rzero R cr ->
        a = rzero R cr \/ b = rzero R cr)
    : IntegralDomain R :=
  mkID R cr (rmul_comm R cr) Hnontrivial Hnozero.
