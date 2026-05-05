(** * NumberTheory/ZPID.v — Z as an Integral Domain and PID

    Wraps Stdlib's [Z] arithmetic as the project-level [IntegralDomain] and
    provides a PID instance via the Euclidean algorithm (using [Z.quot]
    and [Z.rem]). Also exposes Bezout-style helpers over the project's
    [divides] predicate.

    Reference: Stdlib.ZArith, Stdlib.Znumtheory; Dummit & Foote §8.1. *)

From CAG Require Import Rings.Ring Rings.Ideals
                        Domains.Divisibility Domains.PID_UFD.
From Stdlib Require Import ZArith Znumtheory Lia.

Open Scope Z_scope.

(* ================================================================== *)
(** ** Z as a Ring *)
(* ================================================================== *)

(** Wrap [Z]'s arithmetic operations into the project's [Ring] structure. *)
Definition Z_Ring : Ring Z :=
  mkRing Z
    Z.add Z.mul 0 1 Z.opp
    Z.add_assoc Z.add_comm Z.add_0_r Z.add_opp_diag_r
    Z.mul_assoc Z.mul_1_r Z.mul_1_l
    Z.mul_add_distr_l Z.mul_add_distr_r.

Definition Z_CRing : CommutativeRing Z :=
  mkCRing Z Z_Ring Z.mul_comm.

(* ================================================================== *)
(** ** Z as an Integral Domain *)
(* ================================================================== *)

Lemma Z_one_ne_zero : (1 : Z) <> 0.
Proof. discriminate. Qed.

Lemma Z_no_zero_div : forall a b : Z,
    a * b = 0 -> a = 0 \/ b = 0.
Proof.
  intros a b H. apply Z.mul_eq_0 in H. exact H.
Qed.

Definition Z_IntegralDomain : IntegralDomain Z :=
  mkIDfromCRing Z_CRing Z_one_ne_zero Z_no_zero_div.

(* ================================================================== *)
(** ** The two notions of divisibility coincide *)
(* ================================================================== *)

(** The project's [divides] predicate (instantiated at [Z_Ring])
    coincides with [Z.divide], up to swapping factor order. *)

Lemma Z_divides_iff : forall a b : Z,
    divides Z_Ring a b <-> Z.divide a b.
Proof.
  intros a b. unfold divides. split.
  - intros [c Hc]. cbn in Hc. exists c. lia.
  - intros [c Hc]. exists c. cbn. lia.
Qed.

Lemma id_divides_Z_iff : forall a b : Z,
    id_divides Z_IntegralDomain a b <-> Z.divide a b.
Proof.
  intros a b. unfold id_divides. apply Z_divides_iff.
Qed.

(* ================================================================== *)
(** ** Z is a Euclidean Domain *)
(* ================================================================== *)

(** We use [Z.quot] / [Z.rem] (truncated division) so that
    [|rem| < |b|] regardless of sign. *)
Definition Z_norm (a : Z) : nat := Z.to_nat (Z.abs a).

Lemma Z_norm_lt_iff : forall r b : Z,
    Z.abs r < Z.abs b -> (Z_norm r < Z_norm b)%nat.
Proof.
  intros r b Hlt. unfold Z_norm.
  pose proof (Z.abs_nonneg r) as Hr.
  pose proof (Z.abs_nonneg b) as Hb.
  apply Z2Nat.inj_lt; lia.
Qed.

Definition Z_division : forall a b : Z,
    b <> rzero Z (id_r Z_IntegralDomain) ->
    exists q rem : Z,
      a = radd Z (id_r Z_IntegralDomain)
            (rmul Z (id_r Z_IntegralDomain) b q) rem /\
      (rem = rzero Z (id_r Z_IntegralDomain) \/
       (Z_norm rem < Z_norm b)%nat).
Proof.
  intros a b Hb.
  cbn in Hb |- *.
  exists (Z.quot a b), (Z.rem a b).
  pose proof (Z.quot_rem a b Hb) as Hqr.
  split.
  - exact Hqr.
  - destruct (Z.eq_dec (Z.rem a b) 0) as [Hr0 | Hrne].
    + left. exact Hr0.
    + right. apply Z_norm_lt_iff. apply Z.rem_bound_abs. exact Hb.
Qed.

Definition Z_EuclideanDomain : EuclideanDomain Z_IntegralDomain :=
  mkED Z_IntegralDomain Z_norm Z_division.

(* ================================================================== *)
(** ** Z is a PID *)
(* ================================================================== *)

(** Every Euclidean domain is a PID; in particular, Z is a PID.
    The proof goes via [euclidean_is_pid] from Domains.PID_UFD,
    which constructs the principal generator of an ideal as the element
    of minimum (Euclidean) norm in the ideal. *)
(* CAG zero-dependent Theorem Z_is_pid theories/NumberTheory/ZPID.v:115 BEGIN
Theorem Z_is_pid : is_pid Z_IntegralDomain.
Proof.
  apply (euclidean_is_pid Z_IntegralDomain). exact Z_EuclideanDomain.
Qed.
   CAG zero-dependent Theorem Z_is_pid theories/NumberTheory/ZPID.v:115 END *)

(* ================================================================== *)
(** ** Bezout via Stdlib's Zis_gcd *)
(* ================================================================== *)

(** A direct Bezout helper: for any [a, b], there exist [u, v, d]
    with [u*a + v*b = d] and [d] is a gcd of [a] and [b]. *)
Lemma Z_bezout : forall a b : Z,
    exists u v d : Z,
      u * a + v * b = d /\ Zis_gcd a b d.
Proof.
  intros a b.
  pose proof (Zgcd_is_gcd a b) as Hg.
  pose proof (Zis_gcd_bezout a b (Z.gcd a b) Hg) as [u v Heq].
  exists u, v, (Z.gcd a b). split; assumption.
Qed.

Close Scope Z_scope.
