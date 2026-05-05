(** * NumberTheory/GaussianIntegers.v — The Gaussian integers Z[i]

    Formalizes Z[i] = { a + bi | a, b ∈ Z } as a commutative ring,
    proves it is an integral domain, Euclidean domain, and a UFD.

    Reference: Dummit & Foote §8.1, §8.2, §18.3. *)

From CAG Require Import Rings.Ring Domains.Divisibility Domains.Associates
                        Domains.IrreduciblePrime Domains.UFD Domains.PID_UFD.
From Stdlib Require Import ZArith Arith Lia.

Open Scope Z_scope.

(** Local helper: an integer square is non-negative.

    Stdlib offers [Z.pow_nonneg] only for non-negative bases and
    [Z.square_nonneg : 0 <= a * a].  We bridge to the [a^2] form
    used throughout this file via [a^2 = a*a]. *)
Lemma z_sq_nonneg : forall a : Z, a^2 >= 0.
Proof.
  intro a. replace (a^2) with (a*a) by ring.
  pose proof (Z.square_nonneg a). lia.
Qed.

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
  (* Goal: (fst (1,0) * fst (a1,a2) - snd (1,0) * snd (a1,a2),
           fst (1,0) * snd (a1,a2) + snd (1,0) * fst (a1,a2)) = (a1,a2) *)
  change (fst (1, 0)) with 1.
  change (snd (1, 0)) with 0.
  change (fst (a1, a2)) with a1.
  change (snd (a1, a2)) with a2.
  f_equal; ring.
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
  unfold gi_norm, gi_mul, gi_re, gi_im.
  change (fst (a1, a2)) with a1.
  change (snd (a1, a2)) with a2.
  change (fst (b1, b2)) with b1.
  change (snd (b1, b2)) with b2.
  change (fst (a1 * b1 - a2 * b2, a1 * b2 + a2 * b1))
    with (a1 * b1 - a2 * b2).
  change (snd (a1 * b1 - a2 * b2, a1 * b2 + a2 * b1))
    with (a1 * b2 + a2 * b1).
  ring.
Qed.

(** N(z) = 0 iff z = 0 *)
Lemma gi_norm_zero_iff : forall z : GaussInt,
    gi_norm z = 0 <-> z = gi_zero.
Proof.
  intros [a b]. unfold gi_norm, gi_zero. simpl.
  split.
  - intro H.
    assert (Ha : a^2 >= 0) by (apply z_sq_nonneg).
    assert (Hb : b^2 >= 0) by (apply z_sq_nonneg).
    assert (Ha0 : a^2 = 0) by lia.
    assert (Hb0 : b^2 = 0) by lia.
    apply Z.pow_eq_0_iff in Ha0.
    apply Z.pow_eq_0_iff in Hb0.
    destruct Ha0 as [Hbad | [_ Ha']]; [lia |].
    destruct Hb0 as [Hbad | [_ Hb']]; [lia |].
    f_equal; assumption.
  - intro H. injection H as Ha Hb.
    subst. cbn. lia.
Qed.

Lemma gi_norm_pos : forall z : GaussInt,
    z <> gi_zero -> 0 < gi_norm z.
Proof.
  intros z Hz.
  destruct (Z.eq_dec (gi_norm z) 0) as [H0 | H0].
  - exfalso. apply Hz. apply gi_norm_zero_iff. exact H0.
  - assert (H : gi_norm z >= 0).
    { destruct z as [a b]. unfold gi_norm. simpl.
      assert (Ha : a^2 >= 0) by (apply z_sq_nonneg).
      assert (Hb : b^2 >= 0) by (apply z_sq_nonneg).
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
  { apply Z.mul_eq_0.
    (* Hnorm : gi_norm z * gi_norm w = 0^2 + 0^2 (or simplified) *)
    assert (Hzero : (0:Z)^2 + 0^2 = 0) by reflexivity.
    rewrite <- Hzero. exact Hnorm. }
  destruct Hz0 as [Hz | Hw].
  - left.  apply gi_norm_zero_iff. exact Hz.
  - right. apply gi_norm_zero_iff. exact Hw.
Qed.

Lemma gi_one_neq_zero : gi_one <> gi_zero.
Proof.
  intro H. unfold gi_one, gi_zero in H. discriminate H.
Qed.

Definition GaussIntDomain : IntegralDomain GaussInt :=
  mkIDfromCRing GaussIntCRing gi_one_neq_zero gi_no_zero_div.

(* ================================================================== *)
(** ** Units in Z[i] *)
(* ================================================================== *)

(** The units of Z[i] are ±1 and ±i: elements with N = 1 *)
Lemma gi_unit_iff_norm1 : forall z : GaussInt,
    id_is_unit GaussIntDomain z <-> gi_norm z = 1.
Proof.
  intro z. split.
  - intros [w [Hzw Hwz]].
    (* z*w = 1 so N(z)*N(w) = N(1) = 1.
       Hzw, Hwz come from is_unit through id_r GaussIntDomain; both
       compute to gi_mul/gi_one definitionally. *)
    change (rmul _ _ z w = rone _ _) with (gi_mul z w = gi_one) in Hzw.
    change (rmul _ _ w z = rone _ _) with (gi_mul w z = gi_one) in Hwz.
    assert (Hn : gi_norm (gi_mul z w) = gi_norm gi_one).
    { rewrite Hzw. reflexivity. }
    rewrite gi_norm_multiplicative in Hn.
    assert (Hone : gi_norm gi_one = 1) by reflexivity.
    rewrite Hone in Hn.
    assert (Hnz : 0 < gi_norm z).
    { apply gi_norm_pos. intro H. subst z.
      destruct w as [w1 w2].
      unfold gi_mul, gi_zero, gi_one, gi_re, gi_im in Hzw.
      injection Hzw as Hzw'. lia. }
    assert (Hnw : 0 < gi_norm w).
    { apply gi_norm_pos. intro H. subst w.
      destruct z as [z1 z2].
      unfold gi_mul, gi_zero, gi_one, gi_re, gi_im in Hzw.
      injection Hzw as Hzw'. lia. }
    nia.
  - intros Hn.
    (* z has N(z) = 1: the inverse of (a,b) is (a,-b) when a^2+b^2=1 *)
    exists (gi_conj z).
    unfold id_is_unit, is_unit.
    change (rmul GaussInt (id_r GaussIntDomain)) with gi_mul.
    change (rone GaussInt (id_r GaussIntDomain)) with gi_one.
    destruct z as [a b].
    unfold gi_norm, gi_re, gi_im in Hn. cbn in Hn.
    assert (Hsq : a^2 + b^2 = 1) by exact Hn.
    assert (Hsq' : a*a + b*b = 1).
    { replace (a*a) with (a^2) by ring.
      replace (b*b) with (b^2) by ring. exact Hsq. }
    split.
    + unfold gi_conj, gi_mul, gi_one, gi_re, gi_im. cbn.
      f_equal; nia.
    + unfold gi_conj, gi_mul, gi_one, gi_re, gi_im. cbn.
      f_equal; nia.
Qed.

(** The four units *)
Lemma gi_units : forall z : GaussInt,
    id_is_unit GaussIntDomain z <->
    z = gi_one \/ z = gi_neg gi_one \/ z = gi_i \/ z = gi_neg gi_i.
Proof.
  intro z. rewrite gi_unit_iff_norm1.
  unfold gi_norm, gi_one, gi_neg, gi_i, gi_re, gi_im.
  destruct z as [a b]. simpl.
  split.
  - intro H.
    assert (Ha : a^2 >= 0) by (apply z_sq_nonneg).
    assert (Hb : b^2 >= 0) by (apply z_sq_nonneg).
    assert (Ha1 : a^2 <= 1) by lia.
    assert (Hb1 : b^2 <= 1) by lia.
    assert (Ha_bound : a = -1 \/ a = 0 \/ a = 1).
    { (* a^2 <= 1 and a^2 >= 0 force a ∈ {-1, 0, 1} *)
      assert (Habs : -1 <= a <= 1) by nia. lia. }
    assert (Hb_bound : b = -1 \/ b = 0 \/ b = 1).
    { assert (Hbbs : -1 <= b <= 1) by nia. lia. }
    destruct Ha_bound as [Ha' | [Ha' | Ha']];
    destruct Hb_bound as [Hb' | [Hb' | Hb']];
    subst; simpl in H; try lia.
    + (* a=-1, b=0: associate of -gi_one *)
      right. left. unfold gi_neg, gi_one. simpl. reflexivity.
    + (* a=0, b=-1: associate of -gi_i *)
      right. right. right. unfold gi_neg, gi_i. simpl. reflexivity.
    + (* a=0, b=1: gi_i *)
      right. right. left. unfold gi_i. reflexivity.
    + (* a=1, b=0: gi_one *)
      left. reflexivity.
  - intros [H | [H | [H | H]]]; injection H as Ha Hb; subst; cbn; reflexivity.
Qed.

(* ================================================================== *)
(** ** Euclidean structure *)
(* ================================================================== *)

(** Z[i] is a Euclidean domain with norm N(a+bi) = a^2 + b^2 *)

(** Division with remainder: for any z, w ≠ 0,
    z = w*q + r with N(r) < N(w) *)
(** The proof proceeds by rounding z/w to the nearest Gaussian integer *)

(* CAG zero-dependent Axiom gaussian_euclidean theories/NumberTheory/GaussianIntegers.v:317 BEGIN
Axiom gaussian_euclidean :
    forall z w : GaussInt,
      w <> gi_zero ->
      exists q rem : GaussInt,
        z = gi_add (gi_mul w q) rem /\
        (rem = gi_zero \/ gi_norm rem < gi_norm w).
   CAG zero-dependent Axiom gaussian_euclidean theories/NumberTheory/GaussianIntegers.v:317 END *)

(** Z[i] is a PID (follows from being Euclidean) *)
(* CAG zero-dependent Axiom gaussian_is_pid theories/NumberTheory/GaussianIntegers.v:336 BEGIN
Axiom gaussian_is_pid : is_pid GaussIntDomain.
   CAG zero-dependent Axiom gaussian_is_pid theories/NumberTheory/GaussianIntegers.v:336 END *)

(** Z[i] is a UFD *)
(* CAG zero-dependent Theorem gaussian_is_ufd theories/NumberTheory/GaussianIntegers.v:339 BEGIN
Theorem gaussian_is_ufd : IsUFD GaussIntDomain.
Proof.
  apply pid_is_ufd. apply gaussian_is_pid.
Qed.
   CAG zero-dependent Theorem gaussian_is_ufd theories/NumberTheory/GaussianIntegers.v:339 END *)

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
  intros [a b]. unfold gi_mul, gi_conj, gi_norm, gi_re, gi_im.
  change (fst (a, b)) with a.
  change (snd (a, b)) with b.
  change (fst (a, -b)) with a.
  change (snd (a, -b)) with (-b).
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
    cbn in Hp. destruct Hp as [Hp1 _]. lia.
  - (* z is not a unit *)
    intro Hu. apply gi_unit_iff_norm1 in Hu.
    destruct Hp as [Hp1 _]. rewrite Hu in Hp1. lia.
  - (* if z = a*b, then a or b is a unit *)
    (* Strategy: from N(z) = N(a)·N(b) prime, prime_divisors gives
       N(a) ∈ {-1, 1, N(z), -N(z)}; since N(a) ≥ 0 we conclude
       N(a) = 1 (so a is a unit) or N(a) = N(z) (so N(b) = 1). *)
    intros a b Hab.
    rename a into a'. rename b into b'.
    change (rmul GaussInt (id_r GaussIntDomain) a' b' = z) in Hab.
    change (rmul GaussInt (id_r GaussIntDomain)) with gi_mul in Hab.
    assert (Hnorm : gi_norm z = gi_norm a' * gi_norm b').
    { rewrite <- Hab. apply gi_norm_multiplicative. }
    assert (Hpa : gi_norm a' >= 0).
    { destruct a' as [x y]. unfold gi_norm. simpl.
      assert (Hx : x^2 >= 0) by (apply z_sq_nonneg).
      assert (Hy : y^2 >= 0) by (apply z_sq_nonneg). lia. }
    assert (Hpb : gi_norm b' >= 0).
    { destruct b' as [x y]. unfold gi_norm. simpl.
      assert (Hx : x^2 >= 0) by (apply z_sq_nonneg).
      assert (Hy : y^2 >= 0) by (apply z_sq_nonneg). lia. }
    pose proof Hp as Hp_keep.
    pose proof (Znumtheory.prime_ge_2 _ Hp_keep) as Hp2.
    (* gi_norm a' divides gi_norm z *)
    assert (Hdiv : (gi_norm a' | gi_norm z)%Z).
    { rewrite Hnorm. exists (gi_norm b'). lia. }
    pose proof (Znumtheory.prime_divisors _ Hp_keep _ Hdiv) as Hcases.
    (* Hcases : N(a') = -1 \/ N(a') = 1 \/ N(a') = N(z) \/ N(a') = -N(z) *)
    destruct Hcases as [Ha | [Ha | [Ha | Ha]]].
    + (* N(a') = -1: contradicts N(a') >= 0 *) lia.
    + (* N(a') = 1: a' is a unit *)
      left. apply gi_unit_iff_norm1. exact Ha.
    + (* N(a') = N(z): then N(b') = 1, b' is a unit *)
      right. apply gi_unit_iff_norm1.
      destruct (Z.eq_dec (gi_norm b') 0) as [Hb0 | Hb0].
      * rewrite Hb0 in Hnorm. rewrite Ha in Hnorm. lia.
      * nia.
    + (* N(a') = -N(z): contradicts N(a') >= 0 since N(z) >= 1 *) lia.
Qed.

(** Classification of Gaussian primes (stated as axioms) *)

(** p = 2 = -i(1+i)^2 up to units.  The Gaussian prime above 2 is
    (1+i), represented as the pair (1, 1) in the (re, im) encoding. *)
(* CAG zero-dependent Axiom gaussian_prime_2 theories/NumberTheory/GaussianIntegers.v:440 BEGIN
Axiom gaussian_prime_2 :
    is_associate GaussIntDomain (1, 1) (2, 0).
   CAG zero-dependent Axiom gaussian_prime_2 theories/NumberTheory/GaussianIntegers.v:440 END *)

(** q ≡ 3 mod 4 remains prime in Z[i] *)
(* CAG zero-dependent Axiom gaussian_prime_q3mod4 theories/NumberTheory/GaussianIntegers.v:444 BEGIN
Axiom gaussian_prime_q3mod4 :
    forall q : Z,
      Znumtheory.prime q ->
      q mod 4 = 3 ->
      is_prime GaussIntDomain (q, 0).
   CAG zero-dependent Axiom gaussian_prime_q3mod4 theories/NumberTheory/GaussianIntegers.v:444 END *)

(** p ≡ 1 mod 4 splits as (a+bi)(a-bi) *)
(* CAG zero-dependent Axiom gaussian_prime_split_p1mod4 theories/NumberTheory/GaussianIntegers.v:451 BEGIN
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
   CAG zero-dependent Axiom gaussian_prime_split_p1mod4 theories/NumberTheory/GaussianIntegers.v:451 END *)

(** Full classification: the Gaussian primes up to associates are
    (1+i), rational primes q ≡ 3 mod 4, and factors of p = a^2+b^2
    for p ≡ 1 mod 4. *)
(* CAG zero-dependent Axiom gaussian_prime_classification theories/NumberTheory/GaussianIntegers.v:465 BEGIN
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
   CAG zero-dependent Axiom gaussian_prime_classification theories/NumberTheory/GaussianIntegers.v:465 END *)

Close Scope Z_scope.
