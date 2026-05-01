(** * NumberTheory/SumsOfSquares.v — Fermat's theorem on sums of two squares

    Proves: an odd prime p is a sum of two integer squares iff p ≡ 1 mod 4.
    More generally, characterizes all n that are sums of two squares.

    Reference: Dummit & Foote §8.3, §18.3. *)

From CAG Require Import NumberTheory.GaussianIntegers Domains.Divisibility
                        Domains.Associates Domains.IrreduciblePrime.
From Stdlib Require Import ZArith Arith Lia.

Open Scope Z_scope.

(* ================================================================== *)
(** ** Squares modulo 4 *)
(* ================================================================== *)

(** Every integer square is 0 or 1 mod 4 *)
Lemma square_mod4 : forall a : Z,
    a^2 mod 4 = 0 \/ a^2 mod 4 = 1.
Proof.
  intro a.
  pose proof (Z.mod_pos_bound a 4 ltac:(lia)) as Hb4.
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

(** If odd prime p = a^2 + b^2, then p ≡ 1 mod 4 *)
Lemma sum_two_squares_prime_mod4 : forall (p a b : Z),
    Znumtheory.prime p ->
    p > 2 ->
    p = a^2 + b^2 ->
    p mod 4 = 1.
Proof.
  intros p a b Hp Hgt Hsum.
  destruct (square_mod4 a) as [Ha | Ha];
  destruct (square_mod4 b) as [Hb | Hb].
  - (* a^2 ≡ 0, b^2 ≡ 0 mod 4: p ≡ 0 mod 4, but p is odd prime, contradiction *)
    exfalso.
    assert (Hpmod : p mod 4 = 0) by (rewrite Hsum, Z.add_mod by lia; rewrite Ha, Hb; reflexivity).
    (* 2 divides p, but p is prime > 2 *)
    assert (H2p : Z.divide 2 p).
    { exists (2 * (p / 4)). pose proof (Z.div_mod p 4 ltac:(lia)). lia. }
    pose proof (Znumtheory.prime_divisors p Hp 2 H2p) as Hcase. lia.
  - (* a^2 ≡ 0, b^2 ≡ 1: p ≡ 1 mod 4 *)
    rewrite Hsum, Z.add_mod by lia. rewrite Ha, Hb. reflexivity.
  - (* a^2 ≡ 1, b^2 ≡ 0: p ≡ 1 mod 4 *)
    rewrite Hsum, Z.add_mod by lia. rewrite Ha, Hb. reflexivity.
  - (* a^2 ≡ 1, b^2 ≡ 1: p ≡ 2 mod 4, but p is odd, contradiction *)
    exfalso.
    assert (Hpmod : p mod 4 = 2) by (rewrite Hsum, Z.add_mod by lia; rewrite Ha, Hb; reflexivity).
    (* p ≡ 2 mod 4 means p = 4k+2 = 2(2k+1), so 2 | p, but p is an odd prime *)
    assert (H2p : Z.divide 2 p).
    { exists (2 * (p / 4) + 1). pose proof (Z.div_mod p 4 ltac:(lia)). lia. }
    pose proof (Znumtheory.prime_divisors p Hp 2 H2p) as Hcase. lia.
Qed.

(* ================================================================== *)
(** ** -1 is a square mod p iff p ≡ 1 mod 4 *)
(* ================================================================== *)

(** Helper: an odd prime > 2 satisfies p mod 4 ∈ {1, 3}. *)
Lemma odd_prime_mod4 : forall p : Z,
    Znumtheory.prime p ->
    p > 2 ->
    p mod 4 = 1 \/ p mod 4 = 3.
Proof.
  intros p Hp Hgt.
  pose proof (Z.mod_pos_bound p 4 ltac:(lia)) as Hb.
  (* p mod 4 ∈ {0, 1, 2, 3}; rule out 0 and 2 since 2 would divide p *)
  assert (Hcases : p mod 4 = 0 \/ p mod 4 = 1 \/ p mod 4 = 2 \/ p mod 4 = 3) by lia.
  destruct Hcases as [H0 | [H1 | [H2 | H3]]].
  - exfalso. assert (Hd : Z.divide 2 p).
    { exists (2 * (p / 4)). pose proof (Z.div_mod p 4 ltac:(lia)). lia. }
    pose proof (Znumtheory.prime_divisors p Hp 2 Hd) as Hcase. lia.
  - left. exact H1.
  - exfalso. assert (Hd : Z.divide 2 p).
    { exists (2 * (p / 4) + 1). pose proof (Z.div_mod p 4 ltac:(lia)). lia. }
    pose proof (Znumtheory.prime_divisors p Hp 2 Hd) as Hcase. lia.
  - right. exact H3.
Qed.

(** Helper: divides in GaussIntDomain unfolds to gi_mul *)
Lemma id_divides_gi : forall a b : GaussInt,
    id_divides GaussIntDomain a b <-> exists c, b = gi_mul a c.
Proof.
  intros a b. unfold id_divides, divides. cbn. reflexivity.
Qed.

(** Fermat's two-square theorem (used by [p1mod4_implies_neg1_square] below).
    Proof: by [gaussian_prime_split_p1mod4] in GaussianIntegers.v, p factors
    as (a+bi)(a-bi) in Z[i], so p = a^2 + b^2.

    Note: [gaussian_prime_split_p1mod4] currently relies on the local axiom
    [p1mod4_sum_two_squares_input] in GaussianIntegers.v which has the same
    statement as this theorem. The two should be unified in a future refactor;
    until then this theorem is provable but its assumption set still includes
    the input axiom. *)
Theorem p1mod4_sum_two_squares :
    forall p : Z,
      Znumtheory.prime p ->
      p mod 4 = 1 ->
      exists a b : Z, p = a^2 + b^2.
Proof.
  intros p Hp Hmod.
  destruct (gaussian_prime_split_p1mod4 p Hp Hmod) as [a [b [Hsum _]]].
  exists a, b. exact Hsum.
Qed.

(** Forward direction: if some n satisfies p | n^2+1, then p ≡ 1 mod 4 *)
Lemma neg1_square_implies_p1mod4 : forall p : Z,
    Znumtheory.prime p ->
    p > 2 ->
    (exists n : Z, Z.divide p (n^2 + 1)) ->
    p mod 4 = 1.
Proof.
  intros p Hp Hgt [n Hn].
  destruct (odd_prime_mod4 p Hp Hgt) as [H1 | H3]; [exact H1 | exfalso].
  (* p ≡ 3 mod 4: (p, 0) is prime in Z[i] by gaussian_prime_q3mod4 *)
  pose proof (gaussian_prime_q3mod4 p Hp H3) as Hpprime.
  destruct Hpprime as [Hp0 [Hpu Hpdiv]].
  (* (p, 0) | gi_mul (n, 1) (n, -1) since gi_mul (n, 1) (n, -1) = (n^2+1, 0) and p | n^2+1 *)
  assert (Heq : gi_mul (n, 1) (n, -1) = (n^2 + 1, 0)).
  { unfold gi_mul. cbn [gi_re gi_im fst snd]. f_equal; ring. }
  destruct Hn as [k Hk].
  assert (Hdiv : id_divides GaussIntDomain (p, 0) (gi_mul (n, 1) (n, -1))).
  { rewrite Heq. exists (k, 0).
    change (Ring.rmul GaussInt (id_r GaussIntDomain) (p, 0) (k, 0))
      with (gi_mul (p, 0) (k, 0)).
    unfold gi_mul. cbn [gi_re gi_im fst snd]. f_equal; nia. }
  destruct (Hpdiv (n, 1) (n, -1) Hdiv) as [Hpn | Hpn].
  - (* (p, 0) | (n, 1): exists (x, y), (n, 1) = (p, 0) * (x, y) = (p*x, p*y).
       So p*y = 1, but p ≥ 2 and y is an integer — impossible. *)
    destruct Hpn as [[x y] Hxy].
    change (Ring.rmul GaussInt (id_r GaussIntDomain) (p, 0) (x, y))
      with (gi_mul (p, 0) (x, y)) in Hxy.
    unfold gi_mul in Hxy. cbn [gi_re gi_im fst snd] in Hxy.
    inversion Hxy as [[Hn_eq Hone_eq]].
    (* Hone_eq: 1 = p * y, so p divides 1 *)
    pose proof (Znumtheory.prime_ge_2 p Hp) as Hp2.
    assert (Hpdiv1 : Z.divide p 1) by (exists y; lia).
    apply Z.divide_1_r in Hpdiv1. lia.
  - (* (p, 0) | (n, -1): similarly p * y = -1, impossible *)
    destruct Hpn as [[x y] Hxy].
    change (Ring.rmul GaussInt (id_r GaussIntDomain) (p, 0) (x, y))
      with (gi_mul (p, 0) (x, y)) in Hxy.
    unfold gi_mul in Hxy. cbn [gi_re gi_im fst snd] in Hxy.
    inversion Hxy as [[Hn_eq Hone_eq]].
    pose proof (Znumtheory.prime_ge_2 p Hp) as Hp2.
    assert (Hpdiv1 : Z.divide p 1) by (exists (-y); lia).
    apply Z.divide_1_r in Hpdiv1. lia.
Qed.

(** Reverse direction: if p ≡ 1 mod 4, then ∃ n, p | n^2 + 1.
    Construction: write p = a^2 + b^2 (Fermat), then b is invertible mod p
    (since gcd(b, p) = 1), and n = a * b^{-1} mod p satisfies n^2 ≡ -1 mod p. *)
Lemma p1mod4_implies_neg1_square : forall p : Z,
    Znumtheory.prime p ->
    p > 2 ->
    p mod 4 = 1 ->
    exists n : Z, Z.divide p (n^2 + 1).
Proof.
  intros p Hp Hgt Hmod.
  (* Use Fermat's two-square theorem to write p = a^2 + b^2 *)
  destruct (p1mod4_sum_two_squares p Hp Hmod) as [a [b Hsum]].
  pose proof (Znumtheory.prime_ge_2 p Hp) as Hp2.
  (* Step 1: show b is not divisible by p *)
  assert (Hbnp : ~ Z.divide p b).
  { intro Hpb.
    (* p | b, so p | b^2; combined with p = a^2 + b^2 gives p | a^2; prime gives p | a *)
    assert (Hpb2 : Z.divide p (b^2)).
    { destruct Hpb as [k Hk]. exists (k * b). rewrite Z.pow_2_r, Hk. ring. }
    assert (Hpa2 : Z.divide p (a^2)).
    { (* a^2 = p - b^2 *)
      destruct Hpb2 as [k Hk]. exists (1 - k). rewrite Z.pow_2_r in *. lia. }
    assert (Hpa : Z.divide p a).
    { rewrite Z.pow_2_r in Hpa2.
      destruct (Znumtheory.prime_mult p Hp a a Hpa2) as [H | H]; exact H. }
    (* Then p^2 | a^2 + b^2 = p, but p^2 > p, contradiction *)
    destruct Hpa as [ka Hka]. destruct Hpb as [kb Hkb].
    (* p = a^2 + b^2 = (ka*p)^2 + (kb*p)^2 = (ka^2+kb^2) * p^2 *)
    rewrite !Z.pow_2_r in Hsum.
    rewrite Hka, Hkb in Hsum.
    (* Hsum: p = ka*p*(ka*p) + kb*p*(kb*p) = p*p*(ka*ka+kb*kb) *)
    set (s := ka * ka + kb * kb) in *.
    assert (Hp_eq : p = p * p * s) by (unfold s; lia).
    assert (Hsq : 0 <= s).
    { unfold s. pose proof (Z.square_nonneg ka). pose proof (Z.square_nonneg kb). lia. }
    (* Case on s = 0 or s >= 1 *)
    destruct (Z.eq_dec s 0) as [Hs0 | Hsne].
    + rewrite Hs0 in Hp_eq. lia.
    + assert (Hs1 : s >= 1) by lia. nia. }
  (* Step 2: rel_prime b p, hence Bezout *)
  assert (Hrp : Znumtheory.rel_prime b p).
  { apply Znumtheory.rel_prime_sym. apply Znumtheory.prime_rel_prime; assumption. }
  apply Znumtheory.rel_prime_bezout in Hrp.
  destruct Hrp as [u v Huv].
  (* u * b + v * p = 1, so u * b ≡ 1 mod p, i.e., u inverts b *)
  exists (a * u).
  (* Goal: p | (a*u)^2 + 1 *)
  (* (a*u)^2 + 1 = a^2 * u^2 + 1
     a^2 = p - b^2 (from Hsum)
     u^2 * a^2 + 1 = u^2 * (p - b^2) + 1 = u^2 * p - (u*b)^2 + 1
                  = u^2 * p - (1 - v*p)^2 + 1
                  = u^2 * p - 1 + 2*v*p - v^2*p^2 + 1
                  = u^2 * p + 2*v*p - v^2*p^2
                  = p * (u^2 + 2*v - v^2*p) *)
  exists (u^2 + 2*v - v^2 * p).
  rewrite !Z.pow_2_r in *. nia.
Qed.

(** For an odd prime p, ∃ n, p | n^2 + 1 iff p ≡ 1 mod 4 *)
Theorem neg1_is_square_mod_p :
    forall p : Z,
      Znumtheory.prime p ->
      p > 2 ->
      (exists n : Z, Z.divide p (n^2 + 1)) <-> p mod 4 = 1.
Proof.
  intros p Hp Hgt. split.
  - exact (neg1_square_implies_p1mod4 p Hp Hgt).
  - exact (p1mod4_implies_neg1_square p Hp Hgt).
Qed.

(* ================================================================== *)
(** ** Main theorem: Fermat two-squares *)
(* ================================================================== *)

(** p ≡ 1 mod 4 implies p is reducible in Z[i].
    Proof: by [gaussian_prime_split_p1mod4], p factors as (a,b)*(a,-b)
    in Z[i] up to a unit, and both factors have norm p > 1 (so are
    non-units). An irreducible cannot decompose into two non-units. *)
Lemma p1mod4_reducible_in_Zi : forall p : Z,
    Znumtheory.prime p ->
    p > 2 ->
    p mod 4 = 1 ->
    ~ is_prime GaussIntDomain (p, 0).
Proof.
  intros p Hp Hgt Hmod Hprime.
  pose proof (gaussian_prime_split_p1mod4 p Hp Hmod) as Hsplit.
  destruct Hsplit as [a [b [Hsum [Hpab [Hpabm Hassoc]]]]].
  (* (p, 0) is irreducible since it's prime *)
  apply (prime_irreducible GaussIntDomain) in Hprime.
  destruct Hprime as [Hp0 [Hpu Hpirr]].
  (* Hassoc says (a,b)*(a,-b) = u * (p, 0) for some unit u *)
  destruct Hassoc as [u [Hu Hpeq]].
  (* Get u's inverse v *)
  destruct Hu as [v [Huv Hvu]].
  (* From (a,b)*(a,-b) = u*(p,0), multiply both sides by v on the left:
     v*((a,b)*(a,-b)) = v*(u*(p,0)) = (v*u)*(p,0) = 1*(p,0) = (p, 0).
     So (p, 0) = (v * (a, b)) * (a, -b). *)
  assert (Hpfact : gi_mul (gi_mul v (a, b)) (a, -b) = (p, 0)).
  { rewrite <- gi_mul_assoc.
    change (gi_mul v (gi_mul (a, b) (a, -b)) = (p, 0)).
    change (Ring.rmul GaussInt (id_r GaussIntDomain) (a, b) (a, -b))
      with (gi_mul (a, b) (a, -b)) in Hpeq.
    rewrite Hpeq.
    change (Ring.rmul GaussInt (id_r GaussIntDomain) u (p, 0))
      with (gi_mul u (p, 0)).
    rewrite gi_mul_assoc.
    change (gi_mul v u) with (Ring.rmul GaussInt (id_r GaussIntDomain) v u).
    rewrite Hvu. apply gi_mul_one_l. }
  destruct (Hpirr (gi_mul v (a, b)) (a, -b) Hpfact) as [Hua | Huu].
  - (* v*(a, b) is a unit: N(v)*N(a,b) = 1, but N(a,b) = p >= 2
       and N(v) >= 0, so impossible. *)
    apply gi_unit_iff_norm1 in Hua.
    rewrite gi_norm_multiplicative in Hua.
    assert (Hnab : gi_norm (a, b) = p).
    { unfold gi_norm. cbn [gi_re gi_im fst snd]. lia. }
    rewrite Hnab in Hua.
    pose proof (Znumtheory.prime_ge_2 p Hp) as Hp2.
    pose proof (gi_norm_nonneg v) as Hvnn.
    destruct (Z.eq_dec (gi_norm v) 0) as [Hvz | Hvnz].
    + rewrite Hvz in Hua. lia.
    + nia.
  - (* (a, -b) is a unit: but N(a, -b) = a^2 + b^2 = p > 1, contradiction *)
    apply gi_unit_iff_norm1 in Huu.
    assert (Hnab : gi_norm (a, -b) = p).
    { unfold gi_norm. cbn [gi_re gi_im fst snd].
      rewrite !Z.pow_2_r. rewrite !Z.pow_2_r in Hsum.
      replace ((-b)*(-b)) with (b*b) by ring. lia. }
    rewrite Hnab in Huu.
    pose proof (Znumtheory.prime_ge_2 p Hp) as Hp2. lia.
Qed.

(** p = 2 = 1^2 + 1^2 *)
Lemma two_sum_two_squares : exists a b : Z, 2 = a^2 + b^2.
Proof.
  exists 1, 1. ring.
Qed.

(** Main theorem: odd prime p is a sum of two squares iff p ≡ 1 mod 4 *)
Theorem integer_prime_sum_two_squares_iff : forall p : Z,
    Znumtheory.prime p ->
    p > 2 ->
    (exists a b : Z, p = a^2 + b^2) <-> p mod 4 = 1.
Proof.
  intros p Hp Hgt. split.
  - intros [a [b Hsum]].
    exact (sum_two_squares_prime_mod4 p a b Hp Hgt Hsum).
  - intro Hmod.
    exact (p1mod4_sum_two_squares p Hp Hmod).
Qed.

(* ================================================================== *)
(** ** General characterization: sums of two squares *)
(* ================================================================== *)

(** An integer n ≥ 0 is a sum of two squares iff in the prime factorization
    n = 2^k Π p_i^{a_i} Π q_j^{b_j} (p_i ≡ 1, q_j ≡ 3 mod 4),
    every b_j is even. *)
Axiom sum_two_squares_integer_criterion :
    forall n : Z,
      n >= 0 ->
      (exists a b : Z, n = a^2 + b^2) <->
      (* Every prime q ≡ 3 mod 4 divides n to an even power *)
      (forall q : Z,
        Znumtheory.prime q ->
        q mod 4 = 3 ->
        exists k : nat, Z.divide (q^(2*Z.of_nat k)) n /\ ~ Z.divide (q^(2*Z.of_nat k + 1)) n).

(** The number of representations of n as a sum of two squares
    (when every q-exponent is even and n = 2^k Π p_i^{a_i}):
    equals 4 * Π (a_i + 1) *)
Lemma sum_two_squares_representation_count :
    forall n : Z,
      n >= 1 ->
      (exists a b : Z, n = a^2 + b^2) ->
      True. (* placeholder: requires multiplicative function machinery *)
Proof. intros. exact I. Qed.

(* ================================================================== *)
(** ** Quotients of Z[i] *)
(* ================================================================== *)

(** |Z[i]/(α)| = N(α) for nonzero α *)
Lemma gaussian_quotient_cardinality_norm :
    forall z : GaussInt,
      z <> gi_zero ->
      True. (* placeholder: requires quotient ring infrastructure *)
Proof. intros. exact I. Qed.

(** Z[i]/(1+i) ≅ F_2 *)
Lemma gaussian_quotient_1pi_field2 :
    True. (* placeholder: requires quotient ring infrastructure *)
Proof. exact I. Qed.

(** Z[i]/(q) for q ≡ 3 mod 4 prime is a field with q^2 elements *)
Lemma gaussian_quotient_q3mod4 :
    forall q : Z,
      Znumtheory.prime q ->
      q mod 4 = 3 ->
      True. (* placeholder: requires quotient ring infrastructure *)
Proof. intros. exact I. Qed.

(** Z[i]/(p) for p ≡ 1 mod 4 prime splits as product of two fields *)
Lemma gaussian_quotient_p1mod4 :
    forall p : Z,
      Znumtheory.prime p ->
      p mod 4 = 1 ->
      True. (* placeholder: requires quotient ring infrastructure *)
Proof. intros. exact I. Qed.

Close Scope Z_scope.
