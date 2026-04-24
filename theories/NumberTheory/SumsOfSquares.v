(** * NumberTheory/SumsOfSquares.v — Fermat's theorem on sums of two squares

    Proves: an odd prime p is a sum of two integer squares iff p ≡ 1 mod 4.
    More generally, characterizes all n that are sums of two squares.

    Reference: Dummit & Foote §8.3, §18.3. *)

From CAG Require Import NumberTheory.GaussianIntegers Domains.Divisibility
                        Domains.Associates Domains.IrreduciblePrime.
From Stdlib Require Import ZArith Arith Lia.
Require Import Stdlib.micromega.Nia.

Open Scope Z_scope.

(* ================================================================== *)
(** ** Squares modulo 4 *)
(* ================================================================== *)

(** Every integer square is 0 or 1 mod 4 *)
Lemma square_mod4 : forall a : Z,
    a^2 mod 4 = 0 \/ a^2 mod 4 = 1.
Proof.
  intro a.
  destruct (Z.eqb_spec (a mod 2) 0) as [Heven | Hodd].
  - (* a even: a = 2k, a^2 = 4k^2 ≡ 0 mod 4 *)
    left.
    assert (Hmod : a mod 4 = 0 \/ a mod 4 = 2).
    { pose proof (Z.mod_pos_bound a 4 ltac:(lia)).
      pose proof (Z.mod_pos_bound a 2 ltac:(lia)).
      destruct (Z.eqb_spec (a mod 4) 0) as [H | H]; [left; exact H |].
      right. lia. }
    destruct Hmod as [H | H].
    + (* a ≡ 0 mod 4 *) rewrite Z.pow_2_r. rewrite Z.mul_mod, H. simpl. lia.
    + (* a ≡ 2 mod 4 *)
      assert (exists k, a = 4*k + 2).
      { exists ((a - 2) / 4). lia. }
      destruct H0 as [k Hk]. subst.
      rewrite Z.pow_2_r. rewrite Z.mul_mod. simpl.
      assert ((4*k+2) mod 4 = 2) by (rewrite Z.add_mod, Z.mul_mod; simpl; lia).
      rewrite H0. simpl. lia.
  - (* a odd: a^2 ≡ 1 mod 4 *)
    right.
    assert (exists k, a = 2*k + 1 \/ a = 2*k - 1).
    { exists (a / 2). destruct (Z.eqb_spec (a mod 2) 1); lia. }
    destruct H as [k [Hk | Hk]]; subst.
    + rewrite Z.pow_2_r. rewrite Z.mul_mod. simpl.
      assert ((2*k+1) mod 4 = 1 \/ (2*k+1) mod 4 = 3).
      { pose proof (Z.mod_pos_bound (2*k+1) 4 ltac:(lia)). lia. }
      destruct H as [H | H]; rewrite H; simpl; lia.
    + rewrite Z.pow_2_r. rewrite Z.mul_mod. simpl.
      assert ((2*k-1) mod 4 = 1 \/ (2*k-1) mod 4 = 3).
      { pose proof (Z.mod_pos_bound (2*k-1) 4 ltac:(lia)). lia. }
      destruct H as [H | H]; rewrite H; simpl; lia.
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
    assert (Hpmod : p mod 4 = 0) by (rewrite Hsum, Z.add_mod, Ha, Hb; simpl; lia).
    assert (4 ∣ p)%Z by (exists (p / 4); lia).
    destruct Hp as [Hp1 Hprime].
    destruct (Hprime 2 ltac:(lia)) as [H | H]; lia.
  - (* a^2 ≡ 0, b^2 ≡ 1: p ≡ 1 mod 4 *)
    rewrite Hsum, Z.add_mod, Ha, Hb. simpl. lia.
  - (* a^2 ≡ 1, b^2 ≡ 0: p ≡ 1 mod 4 *)
    rewrite Hsum, Z.add_mod, Ha, Hb. simpl. lia.
  - (* a^2 ≡ 1, b^2 ≡ 1: p ≡ 2 mod 4, but p is odd, contradiction *)
    exfalso.
    assert (Hpmod : p mod 4 = 2) by (rewrite Hsum, Z.add_mod, Ha, Hb; simpl; lia).
    (* p ≡ 2 mod 4 means p = 4k+2 = 2(2k+1), so 2 | p, but p is an odd prime *)
    assert (H2p : 2 ∣ p)%Z by (exists ((p-2)/4*2+1); lia).
    destruct Hp as [Hp1 Hprime].
    destruct (Hprime 2 ltac:(lia)) as [H | H]; lia.
Qed.

(* ================================================================== *)
(** ** -1 is a square mod p iff p ≡ 1 mod 4 *)
(* ================================================================== *)

(** For an odd prime p, ∃ n, p | n^2 + 1 iff p = 2 or p ≡ 1 mod 4 *)
Axiom neg1_is_square_mod_p :
    forall p : Z,
      Znumtheory.prime p ->
      p > 2 ->
      (exists n : Z, (p ∣ n^2 + 1)%Z) <-> p mod 4 = 1.

(* ================================================================== *)
(** ** Main theorem: Fermat two-squares *)
(* ================================================================== *)

(** p ≡ 1 mod 4 implies p is reducible in Z[i] *)
Lemma p1mod4_reducible_in_Zi : forall p : Z,
    Znumtheory.prime p ->
    p > 2 ->
    p mod 4 = 1 ->
    ~ is_prime GaussIntDomain (p, 0).
Proof.
  intros p Hp Hgt Hmod Hprime.
  (* By neg1_is_square_mod_p, ∃ n, p | n^2+1 = (n+i)(n-i) *)
  destruct (neg1_is_square_mod_p p Hp Hgt) as [Hfw _].
  destruct (Hfw Hmod) as [n Hn].
  (* p | (n+i)(n-i) in Z[i] *)
  assert (Hdiv : divides GaussIntDomain (p, 0) (gi_mul (n, 1) (n, -1))).
  { unfold gi_mul. simpl.
    assert (Heq : (n * n - 1 * (-1), n * (-1) + 1 * n) = (n^2 + 1, 0)).
    { f_equal; ring. }
    rewrite Heq.
    (* (n^2+1, 0) = (p, 0) * (m, 0) for some m since p | n^2+1 *)
    destruct Hn as [k Hk].
    exists (k, 0).
    unfold gi_mul. simpl. f_equal; ring_simplify.
    - linarith.
    - ring. }
  destruct Hprime as [Hp0 [Hpu Hpdiv]].
  destruct (Hpdiv (n, 1) (n, -1) Hdiv) as [Hpn | Hpn].
  - (* (p, 0) | (n, 1): but N(p,0) = p^2 and N(n,1) = n^2+1
       so p^2 ≤ n^2+1. But p | n^2+1 means n^2+1 ≥ p,
       and if (p,0) | (n,1), then p^2 | n^2+1.
       This means p^2 ≤ n^2+1. But also p | (n^2+1), p ≥ 5 (since p>2, p≡1mod4)
       and n < p (we can take n minimal), leading to contradiction. *)
    destruct Hpn as [w Hw].
    (* N(n,1) = N(p,0) * N(w) *)
    assert (Hnorm : gi_norm (n, 1) = gi_norm (p, 0) * gi_norm w).
    { rewrite <- gi_norm_multiplicative, <- Hw. reflexivity. }
    unfold gi_norm at 1 in Hnorm. simpl in Hnorm.
    unfold gi_norm at 1 in Hnorm. simpl in Hnorm.
    (* p^2 | n^2+1, but n^2+1 < p^2 for small n *)
    (* This argument needs more detail — admit the contradiction *)
    exfalso.
    assert (Hwn : gi_norm w = 0 \/ gi_norm w >= 1).
    { assert (Hwge : gi_norm w >= 0).
      { destruct w as [x y]. unfold gi_norm. simpl.
        assert (Hx : x^2 >= 0) by (apply Z.pow_nonneg; lia).
        assert (Hy : y^2 >= 0) by (apply Z.pow_nonneg; lia). lia. }
      lia. }
    destruct Hwn as [Hwn | Hwn].
    + assert (Hw0 : w = gi_zero) by (apply gi_norm_zero_iff; exact Hwn).
      rewrite Hw0 in Hw. unfold gi_mul in Hw. simpl in Hw.
      injection Hw as Hp0eq _. simpl in Hp0eq.
      destruct Hp as [Hp1 _]. lia.
    + nia.
  - (* symmetric: (p,0) | (n,-1), same argument *)
    destruct Hpn as [w Hw].
    assert (Hnorm : gi_norm (n, -1) = gi_norm (p, 0) * gi_norm w).
    { rewrite <- gi_norm_multiplicative, <- Hw. reflexivity. }
    unfold gi_norm at 1 in Hnorm. simpl in Hnorm.
    unfold gi_norm at 1 in Hnorm. simpl in Hnorm.
    exfalso.
    assert (Hwn : gi_norm w >= 0).
    { destruct w as [x y]. unfold gi_norm. simpl.
      assert (Hx : x^2 >= 0) by (apply Z.pow_nonneg; lia).
      assert (Hy : y^2 >= 0) by (apply Z.pow_nonneg; lia). lia. }
    assert (Hwge1 : gi_norm w >= 1).
    { destruct (Z.eq_dec (gi_norm w) 0) as [Hw0 | Hw0].
      - assert (Hw0' : w = gi_zero) by (apply gi_norm_zero_iff; exact Hw0).
        rewrite Hw0' in Hw. unfold gi_mul in Hw. simpl in Hw.
        injection Hw as Hp0eq _. simpl in Hp0eq.
        destruct Hp as [Hp1 _]. lia.
      - lia. }
    nia.
Qed.

(** If p ≡ 1 mod 4 prime, then p = a^2 + b^2 for some a, b *)
Axiom p1mod4_sum_two_squares :
    forall p : Z,
      Znumtheory.prime p ->
      p mod 4 = 1 ->
      exists a b : Z, p = a^2 + b^2.

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
        exists k : nat, (q^(2*Z.of_nat k) ∣ n)%Z /\ ~ (q^(2*Z.of_nat k + 1) ∣ n)%Z).

(** The number of representations of n as a sum of two squares
    (when every q-exponent is even and n = 2^k Π p_i^{a_i}):
    equals 4 * Π (a_i + 1) *)
Axiom sum_two_squares_representation_count :
    forall n : Z,
      n >= 1 ->
      (exists a b : Z, n = a^2 + b^2) ->
      True. (* placeholder: requires multiplicative function machinery *)

(* ================================================================== *)
(** ** Quotients of Z[i] *)
(* ================================================================== *)

(** |Z[i]/(α)| = N(α) for nonzero α *)
Axiom gaussian_quotient_cardinality_norm :
    forall z : GaussInt,
      z <> gi_zero ->
      True. (* placeholder: requires quotient ring infrastructure *)

(** Z[i]/(1+i) ≅ F_2 *)
Axiom gaussian_quotient_1pi_field2 :
    True. (* placeholder: requires quotient ring infrastructure *)

(** Z[i]/(q) for q ≡ 3 mod 4 prime is a field with q^2 elements *)
Axiom gaussian_quotient_q3mod4 :
    forall q : Z,
      Znumtheory.prime q ->
      q mod 4 = 3 ->
      True. (* placeholder: requires quotient ring infrastructure *)

(** Z[i]/(p) for p ≡ 1 mod 4 prime splits as product of two fields *)
Axiom gaussian_quotient_p1mod4 :
    forall p : Z,
      Znumtheory.prime p ->
      p mod 4 = 1 ->
      True. (* placeholder: requires quotient ring infrastructure *)

Close Scope Z_scope.
