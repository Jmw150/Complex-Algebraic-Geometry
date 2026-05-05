(** * Characteristic.v — Ring characteristic *)

From CAG Require Import Rings.Ring.
From Stdlib Require Import Arith Lia.

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
(** ** Characteristic (axiomatic) *)
(* ================================================================== *)

(* CAG zero-dependent Axiom characteristic theories/Rings/Characteristic.v:27 BEGIN
(* CAG zero-dependent Axiom characteristic theories/Rings/Characteristic.v:27 BEGIN
Axiom characteristic : forall {R : Type} (r : Ring R), nat.
   CAG zero-dependent Axiom characteristic theories/Rings/Characteristic.v:27 END *)
   CAG zero-dependent Axiom characteristic theories/Rings/Characteristic.v:27 END *)

(* CAG zero-dependent Axiom characteristic_spec theories/Rings/Characteristic.v:29 BEGIN
Axiom characteristic_spec : forall {R : Type} (r : Ring R),
    (characteristic r = 0 /\
     forall n, n > 0 -> ring_nsmul r n (rone R r) <> rzero R r)
    \/
    (characteristic r > 0 /\
     ring_nsmul r (characteristic r) (rone R r) = rzero R r /\
     forall m, 0 < m -> m < characteristic r ->
       ring_nsmul r m (rone R r) <> rzero R r).
   CAG zero-dependent Axiom characteristic_spec theories/Rings/Characteristic.v:29 END *)

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

End NSmulLemmas.

(* ================================================================== *)
(** ** Axioms about characteristic *)
(* ================================================================== *)

(** In a commutative ring with no zero divisors, char is 0 or prime. *)
(* CAG zero-dependent Axiom integral_domain_char_zero_or_prime theories/Rings/Characteristic.v:79 BEGIN
Axiom integral_domain_char_zero_or_prime :
  forall {R : Type} (r : CommutativeRing R),
    (forall a b, rmul R (cring R r) a b = rzero R (cring R r) ->
                 a = rzero R (cring R r) \/ b = rzero R (cring R r)) ->
    characteristic (cring R r) = 0 \/
    (exists p, characteristic (cring R r) = p /\ 2 <= p /\
               forall n, 2 <= n -> n < p -> ~ Nat.divide n p).
   CAG zero-dependent Axiom integral_domain_char_zero_or_prime theories/Rings/Characteristic.v:79 END *)

(** Freshman's dream: in characteristic p, (a+b)^p = a^p + b^p. *)
(* CAG zero-dependent Axiom freshmans_dream_char_p theories/Rings/Characteristic.v:88 BEGIN
Axiom freshmans_dream_char_p :
  forall {R : Type} (r : CommutativeRing R) (p : nat)
         (Hchar : characteristic (cring R r) = p)
         (Hp : p > 0)
         (Hprime : forall n, 2 <= n -> n < p -> ~ Nat.divide n p)
         (a b : R),
    ring_pow (cring R r) (radd R (cring R r) a b) p =
    radd R (cring R r) (ring_pow (cring R r) a p) (ring_pow (cring R r) b p).
   CAG zero-dependent Axiom freshmans_dream_char_p theories/Rings/Characteristic.v:88 END *)
