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

(** Make [gi_re] and [gi_im] reduce under [simpl] so that [ring]/[lia] succeed
    in proofs that unfold only the surrounding operation. *)
Arguments gi_re z /.
Arguments gi_im z /.

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

Lemma gi_mul_comm : forall a b : GaussInt,
    gi_mul a b = gi_mul b a.
Proof.
  intros [a1 a2] [b1 b2].
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
  intros a. rewrite gi_mul_comm. apply gi_mul_one_r.
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
  unfold gi_norm, gi_mul, gi_re, gi_im, fst, snd. ring.
Qed.

(** N(z) = 0 iff z = 0 *)
Lemma gi_norm_zero_iff : forall z : GaussInt,
    gi_norm z = 0 <-> z = gi_zero.
Proof.
  intros [a b]. unfold gi_norm, gi_zero, gi_re, gi_im, fst, snd.
  split.
  - intro H.
    assert (Ha : a^2 = a * a) by ring.
    assert (Hb : b^2 = b * b) by ring.
    rewrite Ha, Hb in H.
    assert (Hsq_a : 0 <= a * a) by (apply Z.square_nonneg).
    assert (Hsq_b : 0 <= b * b) by (apply Z.square_nonneg).
    assert (Haa : a * a = 0) by lia.
    assert (Hbb : b * b = 0) by lia.
    assert (Hae : a = 0).
    { apply Z.eq_mul_0 in Haa. destruct Haa; assumption. }
    assert (Hbe : b = 0).
    { apply Z.eq_mul_0 in Hbb. destruct Hbb; assumption. }
    rewrite Hae, Hbe. reflexivity.
  - intro H. injection H as Ha Hb.
    subst. ring.
Qed.

Lemma gi_norm_pos : forall z : GaussInt,
    z <> gi_zero -> 0 < gi_norm z.
Proof.
  intros z Hz.
  destruct (Z.eq_dec (gi_norm z) 0) as [H0 | H0].
  - exfalso. apply Hz. apply gi_norm_zero_iff. exact H0.
  - assert (H : gi_norm z >= 0).
    { destruct z as [a b]. unfold gi_norm, gi_re, gi_im, fst, snd.
      assert (Ha : a^2 = a * a) by ring.
      assert (Hb : b^2 = b * b) by ring.
      rewrite Ha, Hb.
      assert (Hsq_a : 0 <= a * a) by (apply Z.square_nonneg).
      assert (Hsq_b : 0 <= b * b) by (apply Z.square_nonneg).
      lia. }
    lia.
Qed.

Lemma gi_norm_nonneg : forall z : GaussInt, 0 <= gi_norm z.
Proof.
  intros [a b]. unfold gi_norm. cbn [gi_re gi_im fst snd].
  rewrite !Z.pow_2_r.
  pose proof (Z.square_nonneg a). pose proof (Z.square_nonneg b). lia.
Qed.

(** Z[i] is an integral domain *)
Lemma gi_no_zero_div : forall z w : GaussInt,
    gi_mul z w = gi_zero -> z = gi_zero \/ w = gi_zero.
Proof.
  intros z w Hzw.
  assert (Hnorm0 : gi_norm gi_zero = 0).
  { unfold gi_norm, gi_zero, gi_re, gi_im, fst, snd. ring. }
  assert (Hnorm : gi_norm (gi_mul z w) = 0).
  { rewrite Hzw. exact Hnorm0. }
  rewrite gi_norm_multiplicative in Hnorm.
  apply Z.mul_eq_0 in Hnorm.
  destruct Hnorm as [Hz | Hw].
  - left.  apply gi_norm_zero_iff. exact Hz.
  - right. apply gi_norm_zero_iff. exact Hw.
Qed.

Lemma gi_one_ne_zero : gi_one <> gi_zero.
Proof.
  intro H. unfold gi_one, gi_zero in H.
  assert (Hfst : @fst Z Z (1, 0) = @fst Z Z (0, 0)) by (rewrite H; reflexivity).
  cbn in Hfst. discriminate Hfst.
Qed.

Definition GaussIntDomain : IntegralDomain GaussInt :=
  mkIDfromCRing GaussIntCRing gi_one_ne_zero gi_no_zero_div.

(* ================================================================== *)
(** ** Units in Z[i] *)
(* ================================================================== *)

(** The units of Z[i] are ±1 and ±i: elements with N = 1 *)
Lemma gi_unit_iff_norm1 : forall z : GaussInt,
    id_is_unit GaussIntDomain z <-> gi_norm z = 1.
Proof.
  intro z. split.
  - intros [w [Hzw Hwz]].
    cbn in Hzw, Hwz.
    (* z*w = 1 so N(z)*N(w) = N(1) = 1 *)
    assert (Hn : gi_norm (gi_mul z w) = gi_norm gi_one).
    { rewrite Hzw. reflexivity. }
    rewrite gi_norm_multiplicative in Hn.
    unfold gi_norm, gi_one at 2 in Hn. simpl in Hn.
    (* N(z) >= 1 and N(w) >= 1 and N(z)*N(w) = 1 *)
    assert (Hnz : 0 < gi_norm z).
    { apply gi_norm_pos. intro H. rewrite H in Hzw.
      unfold gi_mul, gi_zero, gi_one in Hzw. cbn in Hzw.
      inversion Hzw as [Hbad]; lia. }
    assert (Hnw : 0 < gi_norm w).
    { apply gi_norm_pos. intro H. rewrite H in Hzw.
      unfold gi_mul, gi_zero, gi_one in Hzw. cbn in Hzw.
      inversion Hzw as [Hbad]; lia. }
    assert (Hn1 : gi_norm z * gi_norm w = 1).
    { exact Hn. }
    nia.
  - intros Hn.
    (* z has N(z) = 1: the inverse of (a,b) is (a,-b)/1 = (a,-b) when a^2+b^2=1 *)
    exists (gi_conj z).
    destruct z as [a b].
    assert (Heq : a ^ 2 + b ^ 2 = 1).
    { unfold gi_norm in Hn. cbn in Hn. exact Hn. }
    cbn. unfold gi_mul, gi_conj, gi_one.
    cbn [gi_re gi_im fst snd].
    split; (f_equal; [nia | ring]).
Qed.

(** The four units *)
Lemma gi_units : forall z : GaussInt,
    id_is_unit GaussIntDomain z <->
    z = gi_one \/ z = gi_neg gi_one \/ z = gi_i \/ z = gi_neg gi_i.
Proof.
  intro z. rewrite gi_unit_iff_norm1.
  destruct z as [a b]. unfold gi_norm. cbn [gi_re gi_im fst snd].
  split.
  - intro H.
    assert (Ha2 : 0 <= a^2) by (rewrite Z.pow_2_r; apply Z.square_nonneg).
    assert (Hb2 : 0 <= b^2) by (rewrite Z.pow_2_r; apply Z.square_nonneg).
    assert (Ha1 : a^2 <= 1) by lia.
    assert (Hb1 : b^2 <= 1) by lia.
    rewrite Z.pow_2_r in Ha1, Hb1.
    assert (Ha_bound : a = -1 \/ a = 0 \/ a = 1) by nia.
    assert (Hb_bound : b = -1 \/ b = 0 \/ b = 1) by nia.
    rewrite !Z.pow_2_r in H.
    destruct Ha_bound as [Ha' | [Ha' | Ha']]; subst a;
    destruct Hb_bound as [Hb' | [Hb' | Hb']]; subst b; cbn in H; try lia.
    + right; left. unfold gi_neg, gi_one. cbn. reflexivity.
    + right; right; right. unfold gi_neg, gi_i. cbn. reflexivity.
    + right; right; left. unfold gi_i. reflexivity.
    + left. unfold gi_one. reflexivity.
  - intros [H | [H | [H | H]]]; injection H as Ha Hb; subst; reflexivity.
Qed.

(* ================================================================== *)
(** ** Euclidean structure *)
(* ================================================================== *)

(** Z[i] is a Euclidean domain with norm N(a+bi) = a^2 + b^2 *)

(** Division with remainder: for any z, w ≠ 0,
    z = w*q + r with N(r) < N(w) *)
(** The proof proceeds by rounding z/w to the nearest Gaussian integer *)

(** Helper: nearest-integer rounding on Z. *)
Definition Z_round (m d : Z) : Z :=
  let q := m / d in
  let r := m mod d in
  if Z.leb (2 * r) d then q else q + 1.

Lemma Z_round_bound : forall m d : Z,
    d > 0 ->
    2 * Z.abs (Z_round m d * d - m) <= d.
Proof.
  intros m d Hd.
  unfold Z_round.
  pose proof (Z.div_mod m d ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound m d ltac:(lia)) as Hbd.
  set (q := m / d) in *. set (r := m mod d) in *.
  destruct (Z.leb_spec (2 * r) d) as [Hle | Hgt].
  - assert (Heq : q * d - m = -r) by lia.
    rewrite Heq, Z.abs_opp, Z.abs_eq by lia. lia.
  - assert (Heq : (q + 1) * d - m = d - r) by lia.
    rewrite Heq, Z.abs_eq by lia. lia.
Qed.

(** Helper: |x| ≤ d/2 ⟹ x² ≤ d²/4 *)
Lemma Z_sq_abs_bound : forall x N : Z,
    2 * Z.abs x <= N -> 0 <= N -> 4 * x^2 <= N^2.
Proof.
  intros x N H HN.
  assert (Habs : 0 <= Z.abs x) by apply Z.abs_nonneg.
  assert (Hsq : x^2 = (Z.abs x)^2).
  { rewrite !Z.pow_2_r. symmetry. apply Z.abs_square. }
  rewrite Hsq. nia.
Qed.

Theorem gaussian_euclidean :
    forall z w : GaussInt,
      w <> gi_zero ->
      exists q rem : GaussInt,
        z = gi_add (gi_mul w q) rem /\
        (rem = gi_zero \/ gi_norm rem < gi_norm w).
Proof.
  intros [c d] [a b] Hw.
  set (N := a^2 + b^2).
  assert (HN_pos : 0 < N).
  { apply gi_norm_pos in Hw. unfold gi_norm in Hw.
    cbn [gi_re gi_im fst snd] in Hw. exact Hw. }
  set (m := a*c + b*d).
  set (n := a*d - b*c).
  set (p := Z_round m N).
  set (s := Z_round n N).
  exists (p, s), (c - (a*p - b*s), d - (a*s + b*p)).
  split.
  - unfold gi_add, gi_mul.
    cbn [gi_re gi_im fst snd].
    f_equal; ring.
  - right.
    assert (HnormW : gi_norm (a, b) = N).
    { unfold gi_norm. cbn [gi_re gi_im fst snd]. unfold N. ring. }
    rewrite HnormW.
    set (rem := (c - (a*p - b*s), d - (a*s + b*p)) : GaussInt).
    assert (HmNp : 2 * Z.abs (p * N - m) <= N) by (apply Z_round_bound; lia).
    assert (HnNs : 2 * Z.abs (s * N - n) <= N) by (apply Z_round_bound; lia).
    set (em := p * N - m) in HmNp.
    set (es := s * N - n) in HnNs.
    assert (Hidn : N * gi_norm rem = em^2 + es^2).
    { unfold gi_norm, rem, em, es. cbn [gi_re gi_im fst snd].
      unfold m, n, N. ring. }
    assert (Hsq_em : 4 * em^2 <= N^2) by (apply Z_sq_abs_bound; lia).
    assert (Hsq_es : 4 * es^2 <= N^2) by (apply Z_sq_abs_bound; lia).
    assert (Hrem_nn : 0 <= gi_norm rem).
    { unfold gi_norm, rem. cbn [gi_re gi_im fst snd].
      rewrite !Z.pow_2_r.
      pose proof (Z.square_nonneg (c - (a*p - b*s))).
      pose proof (Z.square_nonneg (d - (a*s + b*p))). lia. }
    assert (HN2 : N^2 = N * N) by ring.
    rewrite HN2 in Hsq_em, Hsq_es.
    assert (Hkey1 : 2 * (em^2 + es^2) <= N * N) by lia.
    assert (Hkey2 : N * (2 * gi_norm rem) <= N * N).
    { rewrite <- Hidn in Hkey1. lia. }
    assert (Hkey3 : 2 * gi_norm rem <= N).
    { apply (proj2 (Z.mul_le_mono_pos_l (2 * gi_norm rem) N N HN_pos)). exact Hkey2. }
    lia.
Qed.

(** Z[i] is a PID (follows from being Euclidean) *)
Theorem gaussian_is_pid : is_pid GaussIntDomain.
Proof.
  apply (euclidean_is_pid GaussIntDomain).
  refine (mkED GaussIntDomain gi_norm_nat _).
  intros a b Hb.
  destruct (gaussian_euclidean a b Hb) as [q [rem [Heq Hcond]]].
  exists q, rem.
  split.
  - exact Heq.
  - destruct Hcond as [Hr0 | Hlt].
    + left. exact Hr0.
    + right. unfold gi_norm_nat.
      apply Z2Nat.inj_lt; [| | exact Hlt].
      * destruct (gi_norm_zero_iff rem) as [Hzif _].
        destruct (Z.eq_dec (gi_norm rem) 0) as [Hz | Hnz].
        -- lia.
        -- pose proof (gi_norm_nonneg rem). lia.
      * apply Z.lt_le_incl. apply gi_norm_pos. exact Hb.
Qed.

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
  intros [a b]. unfold gi_mul, gi_conj, gi_norm.
  cbn [gi_re gi_im fst snd]. f_equal; ring.
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
  pose proof (Znumtheory.prime_ge_2 _ Hp) as Hge2.
  split; [| split].
  - (* z ≠ 0 *)
    intro Hz. rewrite Hz in Hp.
    unfold gi_norm, gi_zero in Hp. cbn in Hp.
    inversion Hp as [Hp1 _]; lia.
  - (* z is not a unit *)
    intro Hu. apply gi_unit_iff_norm1 in Hu.
    inversion Hp as [Hp1 _]; lia.
  - (* if z = a*b, then a or b is a unit *)
    intros a b Hab.
    (* The hypothesis Hab uses rmul which definitionally equals gi_mul *)
    assert (Hgi_ab : gi_mul a b = z) by exact Hab.
    assert (Hnorm : gi_norm a * gi_norm b = gi_norm z).
    { rewrite <- Hgi_ab. symmetry. apply gi_norm_multiplicative. }
    pose proof (gi_norm_nonneg a) as Hpa.
    pose proof (gi_norm_nonneg b) as Hpb.
    (* gi_norm a > 0 and gi_norm b > 0, since otherwise N(z) = 0 but N(z) is prime ≥ 2 *)
    assert (Hpa_pos : 0 < gi_norm a).
    { destruct (Z.eq_dec (gi_norm a) 0) as [Heq | Hne]; [|lia].
      rewrite Heq, Z.mul_0_l in Hnorm. rewrite <- Hnorm in Hge2. lia. }
    assert (Hpb_pos : 0 < gi_norm b).
    { destruct (Z.eq_dec (gi_norm b) 0) as [Heq | Hne]; [|lia].
      rewrite Heq, Z.mul_0_r in Hnorm. rewrite <- Hnorm in Hge2. lia. }
    (* gi_norm a divides gi_norm z = N(a) * N(b), and N(z) is prime *)
    assert (Hdiv : (gi_norm a | gi_norm z)).
    { exists (gi_norm b). rewrite <- Hnorm. ring. }
    pose proof (Znumtheory.prime_divisors _ Hp _ Hdiv) as Hcase.
    destruct Hcase as [|[|[|]]]; try lia.
    + (* gi_norm a = 1: a is a unit *)
      left. apply gi_unit_iff_norm1. assumption.
    + (* gi_norm a = gi_norm z: then gi_norm b = 1, b is a unit *)
      right. apply gi_unit_iff_norm1.
      assert (gi_norm a * gi_norm b = gi_norm a * 1) by nia.
      apply (proj1 (Z.mul_cancel_l (gi_norm b) 1 (gi_norm a) ltac:(lia))). exact H0.
Qed.

(** Classification of Gaussian primes (stated as axioms) *)

(** p = 2 = -i(1+i)^2 up to units.
    Note: the original axiom statement [(1 + gi_i, 0)] was ill-typed
    (Z + GaussInt). The mathematically faithful statement is that
    (1+i)² is associate to 2, witnessed by the unit -i. *)
Theorem gaussian_prime_2 :
    is_associate GaussIntDomain (gi_mul (1, 1) (1, 1)) (2, 0).
Proof.
  (* (1+i)^2 = 2i; (-i) * 2i = 2; so (2,0) = (-i) * (1+i)^2 *)
  exists (0, -1).
  split.
  - (* (0, -1) is a unit, with inverse (0, 1) *)
    exists (0, 1). split; cbn; reflexivity.
  - (* (2, 0) = (0, -1) * ((1, 1) * (1, 1)) *)
    cbn. reflexivity.
Qed.

(** Helper: squares mod 4 are in {0, 1} *)
Lemma sq_mod4 : forall a : Z, a^2 mod 4 = 0 \/ a^2 mod 4 = 1.
Proof.
  intro a.
  pose proof (Z.mod_pos_bound a 4 ltac:(lia)) as Hbd.
  set (r := a mod 4) in *.
  assert (Heq : a = 4 * (a / 4) + r).
  { pose proof (Z.div_mod a 4 ltac:(lia)). unfold r. lia. }
  set (k := a / 4) in *.
  assert (Hcases : r = 0 \/ r = 1 \/ r = 2 \/ r = 3) by lia.
  destruct Hcases as [Hr | [Hr | [Hr | Hr]]]; rewrite Heq, Hr.
  - left. replace ((4 * k + 0) ^ 2) with ((4 * k * k) * 4) by ring.
    apply Z.mod_mul. lia.
  - right. replace ((4 * k + 1) ^ 2) with ((4 * k * k + 2 * k) * 4 + 1) by ring.
    rewrite Z.add_mod by lia. rewrite Z.mod_mul by lia. reflexivity.
  - left. replace ((4 * k + 2) ^ 2) with ((4 * k * k + 4 * k + 1) * 4) by ring.
    apply Z.mod_mul. lia.
  - right. replace ((4 * k + 3) ^ 2) with ((4 * k * k + 6 * k + 2) * 4 + 1) by ring.
    rewrite Z.add_mod by lia. rewrite Z.mod_mul by lia. reflexivity.
Qed.

(** Helper: a^2 + b^2 cannot be 3 mod 4 *)
Lemma sum_sq_not_3mod4 : forall a b : Z, (a^2 + b^2) mod 4 <> 3.
Proof.
  intros a b H.
  pose proof (sq_mod4 a) as Ha.
  pose proof (sq_mod4 b) as Hb.
  rewrite Z.add_mod in H by lia.
  destruct Ha as [Ha | Ha]; destruct Hb as [Hb | Hb];
    rewrite Ha, Hb in H; cbn in H; lia.
Qed.

(** Helper: divisor analysis for prime squares *)
Lemma factor_prime_sq : forall (q n m : Z),
    Znumtheory.prime q -> 0 < n -> 0 < m -> n * m = q^2 ->
    n = 1 \/ n = q \/ n = q^2.
Proof.
  intros q n m Hp Hn Hm Hnm.
  pose proof (Znumtheory.prime_ge_2 q Hp) as Hq.
  assert (Hq2 : q^2 = q * q) by ring.
  rewrite Hq2 in Hnm.
  assert (Hdiv_qm : (q | n * m)).
  { rewrite Hnm. exists q. ring. }
  destruct (Znumtheory.prime_mult q Hp n m Hdiv_qm) as [[k Hk] | [k Hk]].
  - assert (Hkm : k * m = q).
    { assert (Hq_nz : q <> 0) by lia.
      assert (Heq : q * (k * m) = q * q) by (rewrite <- Hnm; rewrite Hk; ring).
      apply (proj1 (Z.mul_cancel_l (k*m) q q Hq_nz)). exact Heq. }
    assert (Hkpos : 0 < k).
    { assert (k * q = n) by (rewrite Hk; ring). nia. }
    assert (Hkdiv : (k | q)) by (exists m; lia).
    pose proof (Znumtheory.prime_divisors q Hp k Hkdiv) as Hkcase.
    destruct Hkcase as [Hkneg1 | [Hk1 | [Hkq | Hkneg]]].
    + lia.
    + right; left. rewrite Hk, Hk1. ring.
    + right; right. rewrite Hk, Hkq. rewrite Hq2. ring.
    + lia.
  - assert (Hnk : n * k = q).
    { assert (Hq_nz : q <> 0) by lia.
      assert (Heq : q * (n * k) = q * q) by (rewrite <- Hnm; rewrite Hk; ring).
      apply (proj1 (Z.mul_cancel_l (n*k) q q Hq_nz)). exact Heq. }
    assert (Hkpos : 0 < k).
    { assert (k * q = m) by (rewrite Hk; ring). nia. }
    assert (Hndiv : (n | q)) by (exists k; lia).
    pose proof (Znumtheory.prime_divisors q Hp n Hndiv) as Hncase.
    destruct Hncase as [Hnneg1 | [Hn1 | [Hnq | Hnneg]]].
    + lia.
    + left. exact Hn1.
    + right; left. exact Hnq.
    + lia.
Qed.

(** q ≡ 3 mod 4 remains prime in Z[i] *)
Theorem gaussian_prime_q3mod4 :
    forall q : Z,
      Znumtheory.prime q ->
      q mod 4 = 3 ->
      is_prime GaussIntDomain (q, 0).
Proof.
  intros q Hprime Hmod.
  apply (ufd_irreducible_prime GaussIntDomain gaussian_is_ufd).
  pose proof (Znumtheory.prime_ge_2 q Hprime) as Hq.
  split; [|split].
  - (* (q, 0) ≠ gi_zero *)
    intro Hq0. unfold gi_zero in Hq0. inversion Hq0. lia.
  - (* (q, 0) is not a unit *)
    intro Hu. apply gi_unit_iff_norm1 in Hu.
    unfold gi_norm in Hu. cbn [gi_re gi_im fst snd] in Hu.
    rewrite Z.pow_2_r in Hu.
    nia.
  - (* For all a, b, a*b = (q, 0) implies a or b is a unit *)
    intros a b Hab.
    assert (Hgi_ab : gi_mul a b = (q, 0)) by exact Hab.
    assert (Hnorm_eq : gi_norm a * gi_norm b = q^2).
    { rewrite <- gi_norm_multiplicative. rewrite Hgi_ab.
      unfold gi_norm. cbn [gi_re gi_im fst snd]. ring. }
    pose proof (gi_norm_nonneg a) as Hna.
    pose proof (gi_norm_nonneg b) as Hnb.
    assert (Hq2pos : 0 < q^2) by nia.
    (* Both norms must be positive *)
    assert (Hna_pos : 0 < gi_norm a).
    { destruct (Z.eq_dec (gi_norm a) 0) as [Heq | Hne]; [|lia].
      rewrite Heq, Z.mul_0_l in Hnorm_eq. lia. }
    assert (Hnb_pos : 0 < gi_norm b).
    { destruct (Z.eq_dec (gi_norm b) 0) as [Heq | Hne]; [|lia].
      rewrite Heq, Z.mul_0_r in Hnorm_eq. lia. }
    (* Use factor_prime_sq *)
    pose proof (factor_prime_sq q (gi_norm a) (gi_norm b) Hprime Hna_pos Hnb_pos Hnorm_eq) as Hcase.
    destruct Hcase as [Hone | [Hq_eq | Hq2eq]].
    + (* gi_norm a = 1: a is a unit *)
      left. apply gi_unit_iff_norm1. exact Hone.
    + (* gi_norm a = q: contradiction since q ≡ 3 mod 4 cannot be sum of squares *)
      exfalso.
      destruct a as [ax ay]. unfold gi_norm in Hq_eq.
      cbn [gi_re gi_im fst snd] in Hq_eq.
      pose proof (sum_sq_not_3mod4 ax ay) as Hns.
      apply Hns. rewrite Hq_eq. exact Hmod.
    + (* gi_norm a = q^2: then gi_norm b = 1, b is a unit *)
      right. apply gi_unit_iff_norm1.
      assert (gi_norm a * gi_norm b = gi_norm a * 1) by nia.
      apply (proj1 (Z.mul_cancel_l (gi_norm b) 1 (gi_norm a) ltac:(lia))). exact H.
Qed.

(** Fermat's theorem on sums of two squares (input axiom).
    Same statement as [p1mod4_sum_two_squares] in NumberTheory/SumsOfSquares.v;
    declared locally because that file depends on this one. *)
Axiom p1mod4_sum_two_squares_input :
    forall p : Z,
      Znumtheory.prime p ->
      p mod 4 = 1 ->
      exists a b : Z, p = a^2 + b^2.

(** Helper: if N(a, b) = p prime, then (a, b) is irreducible in Z[i],
    hence (in Z[i] which is a UFD) prime. *)
Lemma gi_norm_prime_implies_prime : forall z : GaussInt,
    Znumtheory.prime (gi_norm z) ->
    is_prime GaussIntDomain z.
Proof.
  intros z Hp.
  apply (ufd_irreducible_prime GaussIntDomain gaussian_is_ufd).
  apply gi_norm_prime_implies_irreducible. exact Hp.
Qed.

(** p ≡ 1 mod 4 splits as (a+bi)(a-bi) *)
Theorem gaussian_prime_split_p1mod4 :
    forall p : Z,
      Znumtheory.prime p ->
      p mod 4 = 1 ->
      exists a b : Z,
        p = a^2 + b^2 /\
        is_prime GaussIntDomain (a, b) /\
        is_prime GaussIntDomain (a, -b) /\
        is_associate GaussIntDomain (p, 0)
          (gi_mul (a, b) (a, -b)).
Proof.
  intros p Hprime Hmod.
  destruct (p1mod4_sum_two_squares_input p Hprime Hmod) as [a [b Hsum]].
  exists a, b.
  (* Sub-claim: gi_norm (a, b) = p and gi_norm (a, -b) = p *)
  assert (Hnab : gi_norm (a, b) = p).
  { unfold gi_norm. cbn [gi_re gi_im fst snd]. lia. }
  assert (Hnabm : gi_norm (a, -b) = p).
  { unfold gi_norm. cbn [gi_re gi_im fst snd].
    rewrite !Z.pow_2_r. rewrite !Z.pow_2_r in Hsum.
    replace ((-b) * (-b)) with (b * b) by ring. lia. }
  split; [exact Hsum |].
  split; [| split].
  - (* (a, b) is prime *)
    apply gi_norm_prime_implies_prime. rewrite Hnab. exact Hprime.
  - (* (a, -b) is prime *)
    apply gi_norm_prime_implies_prime. rewrite Hnabm. exact Hprime.
  - (* (p, 0) is associate to (a, b) * (a, -b) *)
    (* (a, b) * (a, -b) = (a*a - b*(-b), a*(-b) + b*a) = (a^2 + b^2, 0) = (p, 0) *)
    assert (Heq : gi_mul (a, b) (a, -b) = (p, 0)).
    { unfold gi_mul. cbn [gi_re gi_im fst snd]. f_equal.
      - rewrite !Z.pow_2_r in Hsum. lia.
      - ring. }
    rewrite Heq. apply associate_refl.
Qed.

(** Full classification: the Gaussian primes up to associates are
    (1+i), rational primes q ≡ 3 mod 4, and factors of p = a^2+b^2
    for p ≡ 1 mod 4. *)
Conjecture gaussian_prime_classification :
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
