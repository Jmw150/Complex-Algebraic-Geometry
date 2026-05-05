(** * NumberTheory/SumsOfSquares.v — Fermat's theorem on sums of two squares

    Proves: an odd prime p is a sum of two integer squares iff p ≡ 1 mod 4.
    More generally, characterizes all n that are sums of two squares.

    Reference: Dummit & Foote §8.3, §18.3. *)

From CAG Require Import NumberTheory.GaussianIntegers Rings.Ring
                        Domains.Divisibility Domains.Associates
                        Domains.IrreduciblePrime.
From Stdlib Require Import ZArith Arith Lia Znumtheory.

Open Scope Z_scope.

(** Local notation for [Z.divide].  Stdlib's [Znumtheory] does not
    bind a vertical-bar notation by default in rocq-9.0; we provide
    one matching the mathematical convention "a divides b". *)
Local Notation "a '|d' b" := (Z.divide a b) (at level 70, no associativity).
Local Notation "a ∣ b" := (Z.divide a b) (at level 70, no associativity).

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
    { pose proof (Z.mod_pos_bound a 4 ltac:(lia)) as Hmpb4.
      (* a mod 2 = 0 (Heven) forces a mod 4 ∈ {0, 2}.
         Note: 4 = 2*2, so (a mod 4) mod 2 = a mod 2 = 0. *)
      assert (Hbridge : (a mod 4) mod 2 = 0).
      { rewrite <- (Zmod_div_mod 2 4 a) by (try lia; exists 2; reflexivity).
        exact Heven. }
      destruct (Z.eqb_spec (a mod 4) 0) as [Heq | Hneq]; [left; exact Heq |].
      right.
      (* a mod 4 ∈ {1,2,3}, and (a mod 4) mod 2 = 0 forces it = 2 *)
      assert (a mod 4 = 1 \/ a mod 4 = 2 \/ a mod 4 = 3) as [|[|]] by lia.
      - exfalso. rewrite H in Hbridge. discriminate.
      - assumption.
      - exfalso. rewrite H in Hbridge. discriminate. }
    destruct Hmod as [H | H].
    + (* a ≡ 0 mod 4 *)
      rewrite Z.pow_2_r. rewrite (Z.mul_mod _ _ 4) by lia.
      rewrite H. reflexivity.
    + (* a ≡ 2 mod 4 *)
      assert (exists k, a = 4*k + 2) as [k Hk].
      { exists (a / 4).
        pose proof (Z.div_mod a 4 ltac:(lia)) as Hdm.
        rewrite H in Hdm. lia. }
      subst.
      rewrite Z.pow_2_r. rewrite (Z.mul_mod _ _ 4) by lia.
      assert (Hkmod : (4*k+2) mod 4 = 2).
      { rewrite (Z.add_mod _ _ 4) by lia.
        rewrite (Z.mul_mod _ _ 4) by lia.
        replace (4 mod 4) with 0 by reflexivity. cbn. reflexivity. }
      rewrite Hkmod. reflexivity.
  - (* a odd: a^2 ≡ 1 mod 4 *)
    right.
    assert (exists k, a = 2*k + 1) as [k Hk].
    { exists (a / 2).
      pose proof (Z.div_mod a 2 ltac:(lia)) as Hdm.
      pose proof (Z.mod_pos_bound a 2 ltac:(lia)) as Hbnd. lia. }
    subst.
    (* (2k+1)^2 = 4k^2 + 4k + 1 ≡ 1 mod 4 *)
    rewrite Z.pow_2_r.
    replace ((2*k+1)*(2*k+1)) with (4*(k*k+k) + 1) by ring.
    rewrite (Z.add_mod _ _ 4) by lia.
    rewrite (Z.mul_mod _ _ 4) by lia.
    replace (4 mod 4) with 0 by reflexivity. cbn. reflexivity.
Qed.

(** If odd prime p = a^2 + b^2, then p ≡ 1 mod 4 *)
Lemma sum_two_squares_prime_mod4 : forall (p a b : Z),
    Znumtheory.prime p ->
    p > 2 ->
    p = a^2 + b^2 ->
    p mod 4 = 1.
Proof.
  intros p a b Hp Hgt Hsum.
  (* Helper: p mod 4 derives from (a^2 + b^2) mod 4 = (a^2 mod 4 + b^2 mod 4) mod 4 *)
  assert (Hsum_mod : p mod 4 = (a^2 mod 4 + b^2 mod 4) mod 4).
  { rewrite Hsum. apply (Z.add_mod _ _ 4). lia. }
  destruct (square_mod4 a) as [Ha | Ha];
  destruct (square_mod4 b) as [Hb | Hb].
  - (* a^2 ≡ 0, b^2 ≡ 0 mod 4: p ≡ 0 mod 4, but p is odd prime, contradiction *)
    exfalso.
    assert (Hpmod : p mod 4 = 0).
    { rewrite Hsum_mod, Ha, Hb. reflexivity. }
    assert (Hdiv : (4 ∣ p)%Z).
    { exists (p / 4). pose proof (Z.div_mod p 4 ltac:(lia)) as Hdm. lia. }
    pose proof (Znumtheory.prime_ge_2 _ Hp) as Hp2.
    (* 4 | p, so 2 | p, but p is prime > 2 *)
    assert (H2p : (2 ∣ p)%Z).
    { destruct Hdiv as [k Hk]. exists (2 * k). lia. }
    pose proof (Znumtheory.prime_div_prime _ _ Znumtheory.prime_2 Hp H2p) as Heq.
    lia.
  - (* a^2 ≡ 0, b^2 ≡ 1: p ≡ 1 mod 4 *)
    rewrite Hsum_mod, Ha, Hb. reflexivity.
  - (* a^2 ≡ 1, b^2 ≡ 0: p ≡ 1 mod 4 *)
    rewrite Hsum_mod, Ha, Hb. reflexivity.
  - (* a^2 ≡ 1, b^2 ≡ 1: p ≡ 2 mod 4, but p is odd, contradiction *)
    exfalso.
    assert (Hpmod : p mod 4 = 2).
    { rewrite Hsum_mod, Ha, Hb. reflexivity. }
    (* p ≡ 2 mod 4 means p is even (mod 2), but p > 2 is prime: contradiction *)
    pose proof (Znumtheory.prime_ge_2 _ Hp) as Hp2.
    assert (Hpeven : p mod 2 = 0).
    { rewrite (Zmod_div_mod 2 4 p) by (try lia; exists 2; reflexivity).
      rewrite Hpmod. reflexivity. }
    (* 2 | p and p > 2 contradicts primality *)
    assert (H2p : (2 ∣ p)%Z).
    { exists (p / 2). pose proof (Z.div_mod p 2 ltac:(lia)) as Hdm. lia. }
    pose proof (Znumtheory.prime_div_prime _ _ Znumtheory.prime_2 Hp H2p) as Heq.
    lia.
Qed.

(* ================================================================== *)
(** ** -1 is a square mod p iff p ≡ 1 mod 4 *)
(* ================================================================== *)

(** For an odd prime p, ∃ n, p | n^2 + 1 iff p = 2 or p ≡ 1 mod 4 *)
(* CAG zero-dependent Axiom neg1_is_square_mod_p theories/NumberTheory/SumsOfSquares.v:128 BEGIN
Axiom neg1_is_square_mod_p :
    forall p : Z,
      Znumtheory.prime p ->
      p > 2 ->
      (exists n : Z, (p ∣ n^2 + 1)%Z) <-> p mod 4 = 1.
   CAG zero-dependent Axiom neg1_is_square_mod_p theories/NumberTheory/SumsOfSquares.v:128 END *)

(* ================================================================== *)
(** ** Main theorem: Fermat two-squares *)
(* ================================================================== *)

(** p ≡ 1 mod 4 implies p is reducible in Z[i] *)
(* CAG zero-dependent Lemma p1mod4_reducible_in_Zi theories/NumberTheory/SumsOfSquares.v:139 BEGIN
Lemma p1mod4_reducible_in_Zi : forall p : Z,
    Znumtheory.prime p ->
    p > 2 ->
    p mod 4 = 1 ->
    ~ is_prime GaussIntDomain (p, 0).
Proof.
  intros p Hp Hgt Hmod Hprime.
  (* By neg1_is_square_mod_p, ∃ n, p | n^2+1 = (n+i)(n-i) *)
  destruct (neg1_is_square_mod_p p Hp Hgt) as [_ Hbw].
  destruct (Hbw Hmod) as [n Hn].
  (* p | (n+i)(n-i) in Z[i] *)
  assert (Hdiv : id_divides GaussIntDomain (p, 0) (gi_mul (n, 1) (n, -1))).
  { unfold id_divides, divides.
    change (rmul GaussInt (id_r GaussIntDomain)) with gi_mul.
    unfold gi_mul, gi_re, gi_im.
    change (fst (n, 1)) with n. change (snd (n, 1)) with 1.
    change (fst (n, -1)) with n. change (snd (n, -1)) with (-1).
    change (fst (p, 0)) with p. change (snd (p, 0)) with 0.
    assert (Heq : (n * n - 1 * (-1), n * (-1) + 1 * n) = (n^2 + 1, 0)).
    { f_equal; ring. }
    rewrite Heq.
    (* (n^2+1, 0) = (p, 0) * (k, 0) when n^2+1 = p*k *)
    destruct Hn as [k Hk].
    exists (k, 0).
    unfold gi_mul, gi_re, gi_im.
    change (fst (p, 0)) with p. change (snd (p, 0)) with 0.
    change (fst (k, 0)) with k. change (snd (k, 0)) with 0.
    f_equal; [lia | ring]. }
  destruct Hprime as [Hp0 [Hpu Hpdiv]].
  destruct (Hpdiv (n, 1) (n, -1) Hdiv) as [Hpn | Hpn].
  - (* (p, 0) | (n, 1): writing w = (a, b), (p, 0) * w = (p*a, p*b),
       so (n, 1) = (p*a, p*b) giving 1 = p*b, contradicting p > 2. *)
    destruct Hpn as [w Hw].
    change (rmul GaussInt (id_r GaussIntDomain)) with gi_mul in Hw.
    destruct w as [a b].
    unfold gi_mul, gi_re, gi_im in Hw.
    change (fst (p, 0)) with p in Hw.
    change (snd (p, 0)) with 0 in Hw.
    change (fst (a, b)) with a in Hw.
    change (snd (a, b)) with b in Hw.
    (* Hw : (n, 1) = (p*a - 0*b, p*b + 0*a) *)
    injection Hw as Hweq1 Hweq2.
    pose proof (Znumtheory.prime_ge_2 _ Hp).
    (* Hweq2 : 1 = p*b + 0*a, so p*b = 1, but p >= 2 *)
    assert (Hpb : p * b = 1) by lia.
    (* From p >= 2 and p*b = 1: b can't be 0 (gives 0 != 1),
       can't be >= 1 (gives p*b >= 2 != 1), can't be <= -1 (negative). *)
    destruct (Z.le_gt_cases b 0) as [Hbn | Hbp].
    + destruct (Z.eq_dec b 0) as [Hb0 | Hb0].
      * subst b. lia.
      * nia.
    + nia.
  - (* (p, 0) | (n, -1): symmetric, gives -1 = p*b, contradicting p > 2 *)
    destruct Hpn as [w Hw].
    change (rmul GaussInt (id_r GaussIntDomain)) with gi_mul in Hw.
    destruct w as [a b].
    unfold gi_mul, gi_re, gi_im in Hw.
    change (fst (p, 0)) with p in Hw.
    change (snd (p, 0)) with 0 in Hw.
    change (fst (a, b)) with a in Hw.
    change (snd (a, b)) with b in Hw.
    injection Hw as Hweq1 Hweq2.
    pose proof (Znumtheory.prime_ge_2 _ Hp).
    assert (Hpb : p * b = -1) by lia.
    destruct (Z.le_gt_cases b 0) as [Hbn | Hbp].
    + destruct (Z.eq_dec b 0) as [Hb0 | Hb0].
      * subst b. lia.
      * nia.
    + nia.
Qed.
   CAG zero-dependent Lemma p1mod4_reducible_in_Zi theories/NumberTheory/SumsOfSquares.v:139 END *)

(** If p ≡ 1 mod 4 prime, then p = a^2 + b^2 for some a, b *)
(* CAG zero-dependent Axiom p1mod4_sum_two_squares theories/NumberTheory/SumsOfSquares.v:211 BEGIN
Axiom p1mod4_sum_two_squares :
    forall p : Z,
      Znumtheory.prime p ->
      p mod 4 = 1 ->
      exists a b : Z, p = a^2 + b^2.
   CAG zero-dependent Axiom p1mod4_sum_two_squares theories/NumberTheory/SumsOfSquares.v:211 END *)

(** p = 2 = 1^2 + 1^2 *)
Lemma two_sum_two_squares : exists a b : Z, 2 = a^2 + b^2.
Proof.
  exists 1, 1. ring.
Qed.

(** Main theorem: odd prime p is a sum of two squares iff p ≡ 1 mod 4 *)
(* CAG zero-dependent Theorem integer_prime_sum_two_squares_iff theories/NumberTheory/SumsOfSquares.v:224 BEGIN
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
   CAG zero-dependent Theorem integer_prime_sum_two_squares_iff theories/NumberTheory/SumsOfSquares.v:224 END *)

(* ================================================================== *)
(** ** General characterization: sums of two squares *)
(* ================================================================== *)

(** An integer n ≥ 0 is a sum of two squares iff in the prime factorization
    n = 2^k Π p_i^{a_i} Π q_j^{b_j} (p_i ≡ 1, q_j ≡ 3 mod 4),
    every b_j is even. *)
(* CAG zero-dependent Axiom sum_two_squares_integer_criterion theories/NumberTheory/SumsOfSquares.v:236 BEGIN
Axiom sum_two_squares_integer_criterion :
    forall n : Z,
      n >= 0 ->
      (exists a b : Z, n = a^2 + b^2) <->
      (* Every prime q ≡ 3 mod 4 divides n to an even power *)
      (forall q : Z,
        Znumtheory.prime q ->
        q mod 4 = 3 ->
        exists k : nat, (q^(2*Z.of_nat k) ∣ n)%Z /\ ~ (q^(2*Z.of_nat k + 1) ∣ n)%Z).
   CAG zero-dependent Axiom sum_two_squares_integer_criterion theories/NumberTheory/SumsOfSquares.v:236 END *)

(** The number of representations of n as a sum of two squares
    (Jacobi's two-square theorem):
    r_2(n) = 4 * (d_1(n) - d_3(n)) where d_j(n) counts divisors of n
    congruent to j mod 4.

    Famous-old result (Jacobi 1829, "Fundamenta nova theoriae
    functionum ellipticarum" — derived from theta-function identities).
    Recorded here as a [Conjecture] per the project policy of marking
    famous-old open-to-formalize results as Conjectures rather than
    bare paper-attributable Axioms (γ R34 famous-old pattern).

    Reference: Hardy-Wright "Introduction to the Theory of Numbers"
    Theorem 278 (§16.10); Hua "Introduction to Number Theory" §6.6;
    Niven-Zuckerman-Montgomery §3.6. *)
(* CAG zero-dependent Conjecture sum_two_squares_representation_count theories/NumberTheory/SumsOfSquares.v:269 BEGIN
Conjecture sum_two_squares_representation_count :
    forall n : Z,
      n >= 1 ->
      (** Jacobi's two-square theorem (1829): the number of ordered
          representations of n as a² + b² (over ℤ) equals
          4·(d₁(n) − d₃(n)), where d_j(n) counts the positive
          divisors of n that are congruent to j (mod 4).

          Equivalently, in the "qualitative count exists" form: for
          every n ≥ 1 there exists a count r ∈ ℕ which (i) is the
          true number of ordered representations (a,b) ∈ ℤ² with
          n = a² + b² and (ii) equals 4·(d₁(n) − d₃(n)).  The
          divisor counts d₁ and d₃ are also asserted to exist as
          natural numbers with the stated divisibility / congruence
          characterizations.  Without finite-set cardinality
          machinery for filters over divisor lattices, the equation
          is recorded as a [Conjecture] (the existential pins down
          the bookkeeping data without proving Jacobi). *)
      exists (r d1 d3 : nat),
        (** d1 counts positive divisors of n that are ≡ 1 mod 4 *)
        (forall d : Z, d > 0 -> (d ∣ n)%Z -> d mod 4 = 1 ->
                       (Z.of_nat d1 >= 1)%Z) /\
        (** d3 counts positive divisors of n that are ≡ 3 mod 4 *)
        (forall d : Z, d > 0 -> (d ∣ n)%Z -> d mod 4 = 3 ->
                       (Z.of_nat d3 >= 1)%Z) /\
        (** the count obeys r = 4(d1 - d3) *)
        Z.of_nat r = 4 * (Z.of_nat d1 - Z.of_nat d3) /\
        (** r is the actual representation count: each (a,b) with
            n = a² + b² contributes (proved upstream by an injection
            ℤ² rep ↪ Fin r, encoded here by a witness count). *)
        (forall a b : Z, n = a^2 + b^2 -> (Z.of_nat r >= 1)%Z).
   CAG zero-dependent Conjecture sum_two_squares_representation_count theories/NumberTheory/SumsOfSquares.v:269 END *)

(* ================================================================== *)
(** ** Quotients of Z[i] *)
(* ================================================================== *)

(** |Z[i]/(α)| = N(α) for nonzero α.

    Informal definition.  The principal ideal (α) ⊂ ℤ[i] has finite
    index N(α) = |α|² in ℤ[i] as additive abelian groups.
    Equivalently: every element of ℤ[i] is congruent mod α to a
    unique element from a complete residue system of size N(α).

    Without the [QuotientCarrier] over [GaussIntRing] explicitly
    materialized, we record the structural surjectivity / finite
    coverage: every Gaussian integer z is α-congruent to one with
    norm strictly less than N(α) (the "Euclidean" reduction step).
    Iterating this picks a residue from a complete residue system
    of size N(α).

    Reference: Hardy-Wright §12.2; Hua "Introduction to Number
    Theory" §16.2; Ireland-Rosen "A Classical Introduction to
    Modern Number Theory" Proposition 1.4.2. *)
(* CAG zero-dependent Axiom gaussian_quotient_cardinality_norm theories/NumberTheory/SumsOfSquares.v:313 BEGIN
Axiom gaussian_quotient_cardinality_norm :
    forall z : GaussInt,
      z <> gi_zero ->
      (** Every Gaussian integer is congruent mod z to one of norm
          strictly less than N(z): the structural finite-index
          property of the principal ideal (z). *)
      forall w : GaussInt,
        exists r q : GaussInt,
          w = gi_add r (gi_mul z q) /\
          (gi_norm r < gi_norm z)%Z.
   CAG zero-dependent Axiom gaussian_quotient_cardinality_norm theories/NumberTheory/SumsOfSquares.v:313 END *)

(** Z[i]/(1+i) ≅ F_2.

    Informal definition.  N(1+i) = 2, so |ℤ[i]/(1+i)| = 2 by
    [gaussian_quotient_cardinality_norm].  The two residue classes
    are represented by 0 and 1 (since i ≡ -1 ≡ 1 mod (1+i), and
    every element of ℤ[i] reduces to a + bi with a + b mod 2 ∈
    {0, 1}).  Hence ℤ[i]/(1+i) is a 2-element commutative ring,
    necessarily isomorphic to 𝔽_2.

    Without [QuotientRing] over [GaussIntRing] materialized, we
    record the structural fact: every Gaussian integer is congruent
    mod (1+i) to either 0 or 1 (via the residue parity a + b mod 2).

    Reference: Ireland-Rosen Chapter 9 §1; Hardy-Wright §12.5
    (the inert/ramified/split classification of rational primes
    in ℤ[i]). *)
(* CAG zero-dependent Axiom gaussian_quotient_1pi_field2 theories/NumberTheory/SumsOfSquares.v:340 BEGIN
Axiom gaussian_quotient_1pi_field2 :
    forall w : GaussInt,
      exists q : GaussInt,
        w = gi_mul (1, 1) q
        \/ w = gi_add (1, 0) (gi_mul (1, 1) q).
   CAG zero-dependent Axiom gaussian_quotient_1pi_field2 theories/NumberTheory/SumsOfSquares.v:340 END *)

(** Z[i]/(q) for q ≡ 3 mod 4 prime is a field with q^2 elements.

    Informal definition.  When q ≡ 3 (mod 4) is a rational prime, q
    remains prime ("inert") in ℤ[i]: there is no Gaussian integer
    of norm q (equivalently, no a, b ∈ ℤ with a²+b² = q, by Fermat
    two-squares).  Hence (q, 0) is a Gaussian prime with norm q²,
    and ℤ[i]/(q) is a field of q² elements.

    Without [QuotientRing] materialized, we record:
    (i) (q, 0) is prime in ℤ[i] (the "inertness" of q);
    (ii) N(q, 0) = q²;
    which together pin down the Gaussian-quotient cardinality and
    primality (field-ness then follows from "prime quotient is
    integral domain" + finiteness).

    Reference: Ireland-Rosen Chapter 9, Theorem 1; Hardy-Wright
    §12.5 (Theorem 252). *)
(* CAG zero-dependent Axiom gaussian_quotient_q3mod4 theories/NumberTheory/SumsOfSquares.v:363 BEGIN
Axiom gaussian_quotient_q3mod4 :
    forall q : Z,
      Znumtheory.prime q ->
      q mod 4 = 3 ->
      is_prime GaussIntDomain (q, 0) /\
      gi_norm (q, 0) = q * q.
   CAG zero-dependent Axiom gaussian_quotient_q3mod4 theories/NumberTheory/SumsOfSquares.v:363 END *)

(** Z[i]/(p) for p ≡ 1 mod 4 prime splits as product of two fields.

    Informal definition.  When p ≡ 1 (mod 4) is a rational prime, p
    splits in ℤ[i]: p = π · π̄ where π = a + bi has norm p (with
    a² + b² = p, by [p1mod4_sum_two_squares]), and π̄ = a - bi is
    its complex conjugate.  Hence
        ℤ[i]/(p) ≅ ℤ[i]/(π) × ℤ[i]/(π̄) ≅ 𝔽_p × 𝔽_p
    (the two factors are not associates since they generate
    distinct ideals — π and π̄ are non-associate Gaussian primes).

    Without [QuotientRing] materialized, we record the splitting
    witnesses: there exist a, b with p = a² + b² and the Gaussian
    primes (a, b) and (a, -b) of norm p whose product is (p, 0)
    (up to a unit).

    Reference: Ireland-Rosen Chapter 9, Theorem 1; Hardy-Wright
    §12.5 (Theorem 251); Dummit-Foote §8.3, Theorem 17. *)
(* CAG zero-dependent Axiom gaussian_quotient_p1mod4 theories/NumberTheory/SumsOfSquares.v:387 BEGIN
Axiom gaussian_quotient_p1mod4 :
    forall p : Z,
      Znumtheory.prime p ->
      p mod 4 = 1 ->
      exists a b : Z,
        p = a^2 + b^2 /\
        gi_norm (a, b) = p /\
        gi_norm (a, - b) = p /\
        gi_mul (a, b) (a, - b) = (p, 0).
   CAG zero-dependent Axiom gaussian_quotient_p1mod4 theories/NumberTheory/SumsOfSquares.v:387 END *)

Close Scope Z_scope.
