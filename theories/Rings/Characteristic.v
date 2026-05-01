(** * Characteristic.v — Ring characteristic *)

From CAG Require Import Rings.Ring.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Logic.ClassicalEpsilon Logic.ConstructiveEpsilon.

(* ================================================================== *)
(** ** n-fold addition *)
(* ================================================================== *)

Fixpoint ring_nsmul {R : Type} (r : Ring R) (n : nat) (a : R) : R :=
  match n with
  | O    => rzero R r
  | S k  => radd R r a (ring_nsmul r k a)
  end.

(* ================================================================== *)
(** ** Characteristic predicate *)
(* ================================================================== *)

Definition char_prop {R : Type} (r : Ring R) (n : nat) : Prop :=
  n > 0 /\ ring_nsmul r n (rone R r) = rzero R r.

(* ================================================================== *)
(** ** Characteristic (constructive via classical epsilon) *)
(* ================================================================== *)

(** Smallest [n > 0] with [n * 1 = 0], or [0] if no such [n]. *)
Definition characteristic {R : Type} (r : Ring R) : nat :=
  match excluded_middle_informative (exists n, char_prop r n) with
  | left Hex =>
      proj1_sig
        (epsilon_smallest
           (char_prop r)
           (fun n => excluded_middle_informative (char_prop r n))
           Hex)
  | right _ => 0
  end.

Lemma characteristic_spec : forall {R : Type} (r : Ring R),
    (characteristic r = 0 /\
     forall n, n > 0 -> ring_nsmul r n (rone R r) <> rzero R r)
    \/
    (characteristic r > 0 /\
     ring_nsmul r (characteristic r) (rone R r) = rzero R r /\
     forall m, 0 < m -> m < characteristic r ->
       ring_nsmul r m (rone R r) <> rzero R r).
Proof.
  intros R r. unfold characteristic.
  destruct (excluded_middle_informative (exists n, char_prop r n)) as [Hex|Hno].
  - right.
    destruct (epsilon_smallest (char_prop r)
                (fun n => excluded_middle_informative (char_prop r n)) Hex)
      as [c [[Hcgt Hcz] Hcmin]] eqn:E.
    simpl. split; [exact Hcgt | split; [exact Hcz |]].
    intros m Hm0 HmC Heq.
    assert (Hcm : char_prop r m) by (split; assumption).
    pose proof (Hcmin m Hcm) as Hle. lia.
  - left. split; [reflexivity |].
    intros n Hn Heq.
    apply Hno. exists n. split; assumption.
Qed.

(* ================================================================== *)
(** ** Basic lemmas about ring_nsmul *)
(* ================================================================== *)

Section NSmulLemmas.
  Context {R : Type} (r : Ring R).

  (** n * 0 = 0 *)
  Lemma ring_nsmul_zero : forall n, ring_nsmul r n (rzero R r) = rzero R r.
  Proof.
    intro n. induction n as [| k IH].
    - reflexivity.
    - simpl. rewrite IH. apply radd_zero_r.
  Qed.

  (** n * (a + b) = n*a + n*b *)
  Lemma ring_nsmul_add : forall n a b,
      ring_nsmul r n (radd R r a b) =
      radd R r (ring_nsmul r n a) (ring_nsmul r n b).
  Proof.
    intro n. induction n as [| k IH].
    - intros a b. simpl. symmetry. apply radd_zero_r.
    - intros a b. simpl.
      rewrite IH.
      (* (a+b) + (k*a + k*b) = a + k*a + (b + k*b) *)
      rewrite <- radd_assoc.
      rewrite <- radd_assoc.
      f_equal.
      rewrite radd_assoc.
      rewrite radd_assoc.
      f_equal.
      apply radd_comm.
  Qed.

  (** Distributivity: a * (n*b) = n * (a*b) *)
  Lemma ring_nsmul_mul_r : forall n a b,
      rmul R r a (ring_nsmul r n b) = ring_nsmul r n (rmul R r a b).
  Proof.
    intros n a b. induction n as [| k IH].
    - simpl. apply rmul_zero_r.
    - simpl. rewrite rmul_distrib_l. f_equal. exact IH.
  Qed.

  (** Distributivity: (n*a) * b = n * (a*b) *)
  Lemma ring_nsmul_mul_l : forall n a b,
      rmul R r (ring_nsmul r n a) b = ring_nsmul r n (rmul R r a b).
  Proof.
    intros n a b. induction n as [| k IH].
    - simpl. apply rmul_zero_l.
    - simpl. rewrite rmul_distrib_r. f_equal. exact IH.
  Qed.

  (** Additivity in n: (n+m)*a = n*a + m*a *)
  Lemma ring_nsmul_plus : forall n m a,
      ring_nsmul r (n + m) a = radd R r (ring_nsmul r n a) (ring_nsmul r m a).
  Proof.
    intros n m a. induction n as [| k IH].
    - simpl. rewrite radd_comm. symmetry. apply radd_zero_r.
    - simpl. rewrite IH. apply radd_assoc.
  Qed.

End NSmulLemmas.

(* ================================================================== *)
(** ** Multiplicativity of [ring_nsmul ... 1] in the index *)
(* ================================================================== *)

Lemma ring_nsmul_index_mul {R : Type} (r : Ring R) :
    forall n m,
      ring_nsmul r (n * m) (rone R r) =
      rmul R r (ring_nsmul r n (rone R r)) (ring_nsmul r m (rone R r)).
Proof.
  intros n m. induction n as [| k IH].
  - simpl. symmetry. apply rmul_zero_l.
  - simpl. rewrite ring_nsmul_plus.
    rewrite IH.
    rewrite rmul_distrib_r.
    rewrite rmul_one_l.
    reflexivity.
Qed.

(* ================================================================== *)
(** ** Integral-domain char is 0 or prime (axiom; corrected R19 β) *)
(* ================================================================== *)

(** HISTORY (β R19, 2026-05-01).  The original statement of this axiom
    quantified over a [CommutativeRing] and required only the
    no-zero-divisors hypothesis [Hnzd]:

      forall {R : Type} (r : CommutativeRing R),
        (forall a b, a * b = 0 -> a = 0 \/ b = 0) ->
        characteristic (cring r) = 0 \/
        (exists p, characteristic (cring r) = p /\ 2 <= p /\
                   forall n, 2 <= n -> n < p -> ~ Nat.divide n p).

    This form is FALSE-AS-STATED (γ R22 FALSE-AS-STATED triage,
    REFACTOR_PLAN.org).  Counterexample: the trivial ring
    [{0}] (where [1 = 0]).  There [a * b = 0] always, so [Hnzd]
    holds vacuously; yet [ring_nsmul 1 (rone) = rone = rzero], so
    [characteristic = 1], satisfying neither disjunct of the
    conclusion ([c = 0] is false, and the prime branch needs [2 <= c]).

    Following β R9's [gl_adjoint_hom] pattern, we replace the false
    statement with the mathematically correct form, which adds an
    explicit nontriviality hypothesis [rone <> rzero] — exactly the
    [id_nontrivial] field of the project's [IntegralDomain] record
    in [theories/Domains/Divisibility.v:17].  The historical false
    shape above is preserved in this comment as documented history,
    not as an active assumption.

    The corrected axiom matches the standard textbook statement
    (Dummit & Foote §8.1, Hungerford §III.1): for a *nontrivial*
    integral domain, the characteristic is 0 or prime.  The
    project has no in-tree consumers of this axiom (verified by
    [grep -r integral_domain_char_zero_or_prime theories/]), so the
    statement strengthening introduces no caller cascades. *)
Axiom integral_domain_char_zero_or_prime :
  forall {R : Type} (r : CommutativeRing R),
    rone R (cring R r) <> rzero R (cring R r) ->
    (forall a b, rmul R (cring R r) a b = rzero R (cring R r) ->
                 a = rzero R (cring R r) \/ b = rzero R (cring R r)) ->
    characteristic (cring R r) = 0 \/
    (exists p, characteristic (cring R r) = p /\ 2 <= p /\
               forall n, 2 <= n -> n < p -> ~ Nat.divide n p).

(* ================================================================== *)
(** ** Bridging [ring_of_nat] and [ring_nsmul ... 1] *)
(* ================================================================== *)

Lemma ring_of_nat_eq_nsmul {R : Type} (r : Ring R) :
    forall n, ring_of_nat r n = ring_nsmul r n (rone R r).
Proof.
  induction n as [|n IH]; [reflexivity|].
  simpl. rewrite IH. reflexivity.
Qed.

(** Multiplicativity of [ring_of_nat] in the index. *)
Lemma ring_of_nat_mul {R : Type} (r : Ring R) :
    forall n m,
      ring_of_nat r (n * m) =
      rmul R r (ring_of_nat r n) (ring_of_nat r m).
Proof.
  intros n m.
  rewrite !ring_of_nat_eq_nsmul. apply ring_nsmul_index_mul.
Qed.

(* ================================================================== *)
(** ** Prime divisibility of binomial coefficients (axiom — Lucas/Kummer) *)
(* ================================================================== *)

(** Standard number-theoretic fact: if [p] is prime (no proper divisors in
    [[2, p)]), then [p | binomial p k] for [0 < k < p].  Proved classically
    via [k * binomial p k = p * binomial (p-1) (k-1)] plus Euclid's lemma;
    a substantial nat-theoretic development that we leave as an axiom here. *)
Axiom p_div_binomial_p_k :
  forall (p k : nat),
    (forall n, 2 <= n -> n < p -> ~ Nat.divide n p) ->
    0 < k -> k < p ->
    Nat.divide p (binomial p k).

(* ================================================================== *)
(** ** Freshman's dream *)
(* ================================================================== *)

(** In characteristic p (any commutative ring), [(a+b)^p = a^p + b^p]. *)
Theorem freshmans_dream_char_p :
  forall {R : Type} (r : CommutativeRing R) (p : nat)
         (Hchar : characteristic (cring R r) = p)
         (Hp : p > 0)
         (Hprime : forall n, 2 <= n -> n < p -> ~ Nat.divide n p)
         (a b : R),
    ring_pow (cring R r) (radd R (cring R r) a b) p =
    radd R (cring R r) (ring_pow (cring R r) a p) (ring_pow (cring R r) b p).
Proof.
  intros R cr p Hchar Hp Hprime a b.
  set (rr := cring R cr) in *.
  (* In char p, ring_of_nat rr p = 0. *)
  assert (Hp_zero : ring_of_nat rr p = rzero R rr).
  { rewrite ring_of_nat_eq_nsmul.
    destruct (characteristic_spec rr) as [[Hc0 _] | [_ [Hcz _]]].
    - rewrite Hchar in Hc0. lia.
    - rewrite Hchar in Hcz. exact Hcz. }
  (* For 0 < k < p, ring_of_nat rr (binomial p k) = 0. *)
  assert (Hbinom_zero : forall k, 0 < k -> k < p ->
            ring_of_nat rr (binomial p k) = rzero R rr).
  { intros k Hk1 Hk2.
    destruct (p_div_binomial_p_k p k Hprime Hk1 Hk2) as [m Hm].
    rewrite Hm. rewrite ring_of_nat_mul.
    rewrite Hp_zero. apply (rmul_zero_r rr). }
  (* Therefore, for 0 < k < p, binomial_term cr a b p k = 0. *)
  assert (Hterm_zero : forall k, 0 < k -> k < p ->
            binomial_term cr a b p k = rzero R rr).
  { intros k Hk1 Hk2. unfold binomial_term. fold rr.
    rewrite (Hbinom_zero k Hk1 Hk2).
    rewrite (rmul_zero_l rr). apply (rmul_zero_l rr). }
  (* Apply binomial theorem. *)
  destruct p as [|p']; [lia|].
  unfold rr in *.
  rewrite (binomial_theorem cr a b (S p')).
  (* Goal: ring_sum cr (fun k => bt cr a b (S p') k) (S (S p')) =
          ring_pow cr a (S p') + ring_pow cr b (S p'). *)
  (* Manually unfold the outermost ring_sum (peel off k = S p' term). *)
  change (ring_sum cr (fun k => binomial_term cr a b (S p') k) (S (S p')))
    with (radd R cr (ring_sum cr (fun k => binomial_term cr a b (S p') k) (S p'))
                    (binomial_term cr a b (S p') (S p'))).
  rewrite (binomial_term_diag cr).
  (* Now: (ring_sum (S p') + a^(S p')) = a^(S p') + b^(S p'). *)
  rewrite (ring_sum_shift cr (fun k => binomial_term cr a b (S p') k) p').
  cbv beta.
  rewrite (binomial_term_zero_idx cr).
  rewrite (ring_sum_all_zero cr (fun k => binomial_term cr a b (S p') (S k)) p').
  2: { intros k Hk. apply Hterm_zero; lia. }
  rewrite (radd_zero_r R cr).
  apply (radd_comm R cr).
Qed.
