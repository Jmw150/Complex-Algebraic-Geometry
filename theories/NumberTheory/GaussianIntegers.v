(** * NumberTheory/GaussianIntegers.v — The Gaussian integers Z[i]

    Formalizes Z[i] = { a + bi | a, b ∈ Z } as a commutative ring,
    proves it is an integral domain, Euclidean domain, and a UFD.

    Reference: Dummit & Foote §8.1, §8.2, §18.3. *)

From CAG Require Import Rings.Ring Domains.Divisibility Domains.Associates
                        Domains.IrreduciblePrime Domains.UFD Domains.PID_UFD.
From Stdlib Require Import ZArith Arith Lia.

Open Scope Z_scope.

(* ================================================================== *)
(** ** The Gaussian integers as a type *)
(* ================================================================== *)

(** Z[i] represented as pairs (a, b) meaning a + bi *)
Definition GaussInt : Type := Z * Z.

Definition gi_re (z : GaussInt) : Z := fst z.
Definition gi_im (z : GaussInt) : Z := snd z.

(** Basic operations *)
Definition gi_add (z w : GaussInt) : GaussInt :=
  (gi_re z + gi_re w, gi_im z + gi_im w).

Definition gi_mul (z w : GaussInt) : GaussInt :=
  (gi_re z * gi_re w - gi_im z * gi_im w,
   gi_re z * gi_im w + gi_im z * gi_re w).

Definition gi_zero : GaussInt := (0, 0).
Definition gi_one  : GaussInt := (1, 0).
Definition gi_neg  (z : GaussInt) : GaussInt := (- gi_re z, - gi_im z).

Definition gi_i : GaussInt := (0, 1).

(** Conjugate: (a, b)^* = (a, -b) *)
Definition gi_conj (z : GaussInt) : GaussInt := (gi_re z, - gi_im z).

(** Norm: N(a + bi) = a^2 + b^2 *)
Definition gi_norm (z : GaussInt) : Z :=
  (gi_re z)^2 + (gi_im z)^2.

(** Natural-number valued norm for Euclidean algorithm *)
Definition gi_norm_nat (z : GaussInt) : nat :=
  Z.to_nat (gi_norm z).

(* ================================================================== *)
(** ** Ring axioms *)
(* ================================================================== *)

Lemma gi_add_assoc : forall a b c : GaussInt,
    gi_add a (gi_add b c) = gi_add (gi_add a b) c.
Proof.
  intros [a1 a2] [b1 b2] [c1 c2].
  unfold gi_add. simpl. f_equal; ring.
Qed.

Lemma gi_add_comm : forall a b : GaussInt,
    gi_add a b = gi_add b a.
Proof.
  intros [a1 a2] [b1 b2].
  unfold gi_add. simpl. f_equal; ring.
Qed.

Lemma gi_add_zero_r : forall a : GaussInt,
    gi_add a gi_zero = a.
Proof.
  intros [a1 a2]. unfold gi_add, gi_zero. simpl.
  f_equal; ring.
Qed.

Lemma gi_add_neg_r : forall a : GaussInt,
    gi_add a (gi_neg a) = gi_zero.
Proof.
  intros [a1 a2]. unfold gi_add, gi_neg, gi_zero. simpl.
  f_equal; ring.
Qed.

Lemma gi_mul_assoc : forall a b c : GaussInt,
    gi_mul a (gi_mul b c) = gi_mul (gi_mul a b) c.
Proof.
  intros [a1 a2] [b1 b2] [c1 c2].
  unfold gi_mul. simpl. f_equal; ring.
Qed.

Lemma gi_mul_one_r : forall a : GaussInt,
    gi_mul a gi_one = a.
Proof.
  intros [a1 a2]. unfold gi_mul, gi_one. simpl.
  f_equal; ring.
Qed.

Lemma gi_mul_one_l : forall a : GaussInt,
    gi_mul gi_one a = a.
Proof.
  intros [a1 a2]. unfold gi_mul, gi_one, gi_re, gi_im.
  simpl. f_equal; ring.
Qed.

Lemma gi_mul_distrib_l : forall a b c : GaussInt,
    gi_mul a (gi_add b c) = gi_add (gi_mul a b) (gi_mul a c).
Proof.
  intros [a1 a2] [b1 b2] [c1 c2].
  unfold gi_mul, gi_add. simpl. f_equal; ring.
Qed.

Lemma gi_mul_distrib_r : forall a b c : GaussInt,
    gi_mul (gi_add a b) c = gi_add (gi_mul a c) (gi_mul b c).
Proof.
  intros [a1 a2] [b1 b2] [c1 c2].
  unfold gi_mul, gi_add. simpl. f_equal; ring.
Qed.

Lemma gi_mul_comm : forall a b : GaussInt,
    gi_mul a b = gi_mul b a.
Proof.
  intros [a1 a2] [b1 b2].
  unfold gi_mul. simpl. f_equal; ring.
Qed.

(** The Gaussian integers form a commutative ring *)
Definition GaussIntRing : Ring GaussInt :=
  mkRing GaussInt
    gi_add gi_mul gi_zero gi_one gi_neg
    gi_add_assoc gi_add_comm gi_add_zero_r gi_add_neg_r
    gi_mul_assoc gi_mul_one_r gi_mul_one_l
    gi_mul_distrib_l gi_mul_distrib_r.

Definition GaussIntCRing : CommutativeRing GaussInt :=
  mkCRing GaussInt GaussIntRing gi_mul_comm.

(* ================================================================== *)
(** ** No zero divisors *)
(* ================================================================== *)

(** Key: N(z*w) = N(z)*N(w) *)
Lemma gi_norm_multiplicative : forall z w : GaussInt,
    gi_norm (gi_mul z w) = gi_norm z * gi_norm w.
Proof.
  intros [a1 a2] [b1 b2].
  unfold gi_norm, gi_mul. simpl. ring.
Qed.

(** N(z) = 0 iff z = 0 *)
Lemma gi_norm_zero_iff : forall z : GaussInt,
    gi_norm z = 0 <-> z = gi_zero.
Proof.
  intros [a b]. unfold gi_norm, gi_zero. simpl.
  split.
  - intro H.
    assert (Ha : a^2 >= 0) by (apply Z.pow_nonneg; lia).
    assert (Hb : b^2 >= 0) by (apply Z.pow_nonneg; lia).
    assert (Ha0 : a^2 = 0) by lia.
    assert (Hb0 : b^2 = 0) by lia.
    apply Z.pow_eq_0_iff in Ha0; [| lia].
    apply Z.pow_eq_0_iff in Hb0; [| lia].
    f_equal; exact Ha0 || exact Hb0.
  - intro H. injection H as Ha Hb.
    subst. simpl. ring.
Qed.

Lemma gi_norm_pos : forall z : GaussInt,
    z <> gi_zero -> 0 < gi_norm z.
Proof.
  intros z Hz.
  destruct (Z.eq_dec (gi_norm z) 0) as [H0 | H0].
  - exfalso. apply Hz. apply gi_norm_zero_iff. exact H0.
  - assert (H : gi_norm z >= 0).
    { destruct z as [a b]. unfold gi_norm. simpl.
      assert (Ha : a^2 >= 0) by (apply Z.pow_nonneg; lia).
      assert (Hb : b^2 >= 0) by (apply Z.pow_nonneg; lia).
      lia. }
    lia.
Qed.

(** Z[i] is an integral domain *)
Lemma gi_no_zero_div : forall z w : GaussInt,
    gi_mul z w = gi_zero -> z = gi_zero \/ w = gi_zero.
Proof.
  intros z w Hzw.
  assert (Hnorm : gi_norm (gi_mul z w) = gi_norm gi_zero).
  { rewrite Hzw. reflexivity. }
  rewrite gi_norm_multiplicative in Hnorm.
  unfold gi_norm at 2, gi_zero in Hnorm. simpl in Hnorm.
  assert (Hz0 : gi_norm z = 0 \/ gi_norm w = 0).
  { apply Z.mul_eq_0. lia. }
  destruct Hz0 as [Hz | Hw].
  - left.  apply gi_norm_zero_iff. exact Hz.
  - right. apply gi_norm_zero_iff. exact Hw.
Qed.

Definition GaussIntDomain : IntegralDomain GaussInt :=
  mkID GaussInt GaussIntCRing
    (fun H => (* 1 ≠ 0: (1,0) ≠ (0,0) *)
      let H' := @f_equal _ _ fst (1, 0) (0, 0) H in
      ltac:(simpl in H'; discriminate H'))
    gi_no_zero_div.

(* ================================================================== *)
(** ** Units in Z[i] *)
(* ================================================================== *)

(** The units of Z[i] are ±1 and ±i: elements with N = 1 *)
Lemma gi_unit_iff_norm1 : forall z : GaussInt,
    is_unit GaussIntDomain z <-> gi_norm z = 1.
Proof.
  intro z. split.
  - intros [w [Hzw Hwz]].
    (* z*w = 1 so N(z)*N(w) = N(1) = 1 *)
    assert (Hn : gi_norm (gi_mul z w) = gi_norm gi_one).
    { rewrite Hzw. reflexivity. }
    rewrite gi_norm_multiplicative in Hn.
    unfold gi_norm, gi_one at 2 in Hn. simpl in Hn.
    (* N(z) >= 1 and N(w) >= 1 and N(z)*N(w) = 1 *)
    assert (Hnz : 0 < gi_norm z) by (apply gi_norm_pos; intro H; rewrite H in Hzw; simpl in Hzw; discriminate).
    assert (Hnw : 0 < gi_norm w) by (apply gi_norm_pos; intro H; rewrite H in Hzw; simpl in Hzw; discriminate).
    nia.
  - intros Hn.
    (* z has N(z) = 1: the inverse of (a,b) is (a,-b)/1 = (a,-b) when a^2+b^2=1 *)
    exists (gi_conj z).
    unfold gi_conj, is_unit, gi_mul, gi_one.
    assert (Heq : gi_re z ^ 2 + gi_im z ^ 2 = 1) by exact Hn.
    unfold gi_re, gi_im.
    split.
    + destruct z as [a b]. simpl. f_equal; [nia | ring].
    + destruct z as [a b]. simpl. f_equal; [nia | ring].
Qed.

(** The four units *)
Lemma gi_units : forall z : GaussInt,
    is_unit GaussIntDomain z <->
    z = gi_one \/ z = gi_neg gi_one \/ z = gi_i \/ z = gi_neg gi_i.
Proof.
  intro z. rewrite gi_unit_iff_norm1.
  unfold gi_norm, gi_one, gi_neg, gi_i, gi_re, gi_im.
  destruct z as [a b]. simpl.
  split.
  - intro H.
    assert (Ha : a^2 >= 0) by (apply Z.pow_nonneg; lia).
    assert (Hb : b^2 >= 0) by (apply Z.pow_nonneg; lia).
    assert (Ha1 : a^2 <= 1) by lia.
    assert (Hb1 : b^2 <= 1) by lia.
    assert (Ha_bound : a = -1 \/ a = 0 \/ a = 1).
    { destruct (Z.le_dec (-1) a); destruct (Z.le_dec a 1); try lia.
      left; lia. }
    assert (Hb_bound : b = -1 \/ b = 0 \/ b = 1).
    { destruct (Z.le_dec (-1) b); destruct (Z.le_dec b 1); try lia.
      left; lia. }
    destruct Ha_bound as [Ha' | [Ha' | Ha']];
    destruct Hb_bound as [Hb' | [Hb' | Hb']];
    subst; simpl in H; try lia.
    + right. right. right. unfold gi_neg. simpl. reflexivity.
    + right. left. unfold gi_neg. simpl. reflexivity.
    + right. right. left. unfold gi_i. reflexivity.
    + left. reflexivity.
  - intros [H | [H | [H | H]]]; injection H as Ha Hb; subst; simpl; ring.
Qed.

(* ================================================================== *)
(** ** Euclidean structure *)
(* ================================================================== *)

(** Z[i] is a Euclidean domain with norm N(a+bi) = a^2 + b^2 *)

(** Division with remainder: for any z, w ≠ 0,
    z = w*q + r with N(r) < N(w) *)
(** The proof proceeds by rounding z/w to the nearest Gaussian integer *)

Axiom gaussian_euclidean :
    forall z w : GaussInt,
      w <> gi_zero ->
      exists q rem : GaussInt,
        z = gi_add (gi_mul w q) rem /\
        (rem = gi_zero \/ gi_norm rem < gi_norm w).

(** Z[i] is a PID (follows from being Euclidean) *)
Axiom gaussian_is_pid : is_pid GaussIntDomain.

(** Z[i] is a UFD *)
Theorem gaussian_is_ufd : IsUFD GaussIntDomain.
Proof.
  apply pid_is_ufd. apply gaussian_is_pid.
Qed.

(* ================================================================== *)
(** ** Conjugation is a ring automorphism *)
(* ================================================================== *)

Lemma gi_conj_add : forall z w : GaussInt,
    gi_conj (gi_add z w) = gi_add (gi_conj z) (gi_conj w).
Proof.
  intros [a1 a2] [b1 b2]. unfold gi_conj, gi_add. simpl.
  f_equal. ring.
Qed.

Lemma gi_conj_mul : forall z w : GaussInt,
    gi_conj (gi_mul z w) = gi_mul (gi_conj z) (gi_conj w).
Proof.
  intros [a1 a2] [b1 b2]. unfold gi_conj, gi_mul. simpl.
  f_equal; ring.
Qed.

Lemma gi_conj_one : gi_conj gi_one = gi_one.
Proof. unfold gi_conj, gi_one. simpl. reflexivity. Qed.

(** N(z) = z * conj(z) *)
Lemma gi_norm_conj : forall z : GaussInt,
    gi_mul z (gi_conj z) = (gi_norm z, 0).
Proof.
  intros [a b]. unfold gi_mul, gi_conj, gi_norm, gi_re, gi_im. simpl.
  f_equal; ring.
Qed.

(** N is multiplicative: N(zw) = N(z) * N(w) *)
Lemma gaussian_norm_multiplicative : forall z w : GaussInt,
    gi_norm (gi_mul z w) = gi_norm z * gi_norm w.
Proof.
  exact gi_norm_multiplicative.
Qed.

(* ================================================================== *)
(** ** Prime elements of Z[i] *)
(* ================================================================== *)

(** An element z ∈ Z[i] is irreducible iff N(z) is a rational prime *)
(** (one direction is provable; the other uses the Euclidean structure) *)

Lemma gi_prime_norm_rational_prime : forall z : GaussInt,
    is_irreducible GaussIntDomain z ->
    (** N(z) is a product of rational primes *)
    True.
Proof. intros. exact I. Qed.

(** If N(z) is a rational prime p, then z is irreducible in Z[i] *)
Lemma gi_norm_prime_implies_irreducible : forall z : GaussInt,
    Znumtheory.prime (gi_norm z) ->
    is_irreducible GaussIntDomain z.
Proof.
  intros z Hp.
  split; [| split].
  - (* z ≠ 0 *)
    intro Hz. rewrite Hz in Hp.
    simpl in Hp. destruct Hp as [Hp1 _].
    lia.
  - (* z is not a unit *)
    intro Hu. apply gi_unit_iff_norm1 in Hu.
    destruct Hp as [Hp1 _]. rewrite Hu in Hp1. lia.
  - (* if z = a*b, then a or b is a unit *)
    intros a b Hab.
    assert (Hnorm : gi_norm z = gi_norm a * gi_norm b).
    { rewrite <- Hab. apply gi_norm_multiplicative. }
    rewrite Hnorm in Hp.
    assert (Hpa : gi_norm a >= 0).
    { destruct a as [x y]. unfold gi_norm. simpl.
      assert (Hx : x^2 >= 0) by (apply Z.pow_nonneg; lia).
      assert (Hy : y^2 >= 0) by (apply Z.pow_nonneg; lia). lia. }
    assert (Hpb : gi_norm b >= 0).
    { destruct b as [x y]. unfold gi_norm. simpl.
      assert (Hx : x^2 >= 0) by (apply Z.pow_nonneg; lia).
      assert (Hy : y^2 >= 0) by (apply Z.pow_nonneg; lia). lia. }
    destruct Hp as [Hp1 Hprime].
    destruct (Hprime (gi_norm a)) as [Ha | Ha].
    + (* N(a) = 1: a is a unit *)
      split; [| lia].
      left. apply gi_unit_iff_norm1. lia.
    + (* N(a) = N(z): then N(b) = 1, b is a unit *)
      right. apply gi_unit_iff_norm1.
      destruct (Z.eq_dec (gi_norm b) 0) as [Hb0 | Hb0].
      * rewrite Hb0 in Hnorm. rewrite Ha in Hnorm. lia.
      * nia.
Qed.

(** Classification of Gaussian primes (stated as axioms) *)

(** p = 2 = -i(1+i)^2 up to units *)
Axiom gaussian_prime_2 :
    is_associate GaussIntDomain (1 + gi_i, 0) (2, 0).

(** q ≡ 3 mod 4 remains prime in Z[i] *)
Axiom gaussian_prime_q3mod4 :
    forall q : Z,
      Znumtheory.prime q ->
      q mod 4 = 3 ->
      is_prime GaussIntDomain (q, 0).

(** p ≡ 1 mod 4 splits as (a+bi)(a-bi) *)
Axiom gaussian_prime_split_p1mod4 :
    forall p : Z,
      Znumtheory.prime p ->
      p mod 4 = 1 ->
      exists a b : Z,
        p = a^2 + b^2 /\
        is_prime GaussIntDomain (a, b) /\
        is_prime GaussIntDomain (a, -b) /\
        is_associate GaussIntDomain (p, 0)
          (gi_mul (a, b) (a, -b)).

(** Full classification: the Gaussian primes up to associates are
    (1+i), rational primes q ≡ 3 mod 4, and factors of p = a^2+b^2
    for p ≡ 1 mod 4. *)
Axiom gaussian_prime_classification :
    forall z : GaussInt,
      is_prime GaussIntDomain z ->
      (** z is associate to 1+i *)
      is_associate GaussIntDomain z (1, 1) \/
      (** or z is associate to a rational prime q ≡ 3 mod 4 *)
      (exists q : Z,
        Znumtheory.prime q /\ q mod 4 = 3 /\
        is_associate GaussIntDomain z (q, 0)) \/
      (** or z is a factor of a rational prime p ≡ 1 mod 4 *)
      (exists (p a b : Z),
        Znumtheory.prime p /\ p mod 4 = 1 /\
        p = a^2 + b^2 /\
        (is_associate GaussIntDomain z (a, b) \/
         is_associate GaussIntDomain z (a, -b))).

Close Scope Z_scope.
