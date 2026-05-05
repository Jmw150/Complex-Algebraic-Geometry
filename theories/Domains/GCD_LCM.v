(** * Domains/GCD_LCM.v — GCDs and LCMs in integral domains

    Formalizes greatest common divisors and least common multiples.

    Reference: Dummit & Foote §8.3. *)

From CAG Require Import Rings.Ring Domains.Divisibility Domains.Associates
                        Domains.IrreduciblePrime Domains.UFD.
From Stdlib Require Import Arith Lia List Classical.
Import ListNotations.

(* ================================================================== *)
(** ** Greatest common divisors *)
(* ================================================================== *)

Section GCD.
  Context {R : Type} (d : IntegralDomain R).

  Let r : Ring R := id_r d.
  Let comm : forall a b : R, rmul R r a b = rmul R r b a := id_comm d.

  (** d is a gcd of a and b if:
      - d | a
      - d | b
      - for any c, c | a and c | b implies c | d *)
  Definition is_gcd (g a b : R) : Prop :=
    divides r g a /\
    divides r g b /\
    forall c : R, divides r c a -> divides r c b -> divides r c g.

  (** lcm of a and b: l is an lcm if:
      - a | l
      - b | l
      - for any c, a | c and b | c implies l | c *)
  Definition is_lcm (l a b : R) : Prop :=
    divides r a l /\
    divides r b l /\
    forall c : R, divides r a c -> divides r b c -> divides r l c.

  (** GCD is unique up to associates *)
  Lemma gcd_unique_up_to_associate : forall g1 g2 a b : R,
      is_gcd g1 a b -> is_gcd g2 a b ->
      is_associate d g1 g2.
  Proof.
    intros g1 g2 a b [Hg1a [Hg1b Hg1min]] [Hg2a [Hg2b Hg2min]].
    pose proof (Hg1min g2 Hg2a Hg2b) as Hg1g2.
    pose proof (Hg2min g1 Hg1a Hg1b) as Hg2g1.
    destruct (classic (g1 = rzero R r)) as [Hg10 | Hg10].
    - rewrite Hg10 in Hg2g1.
      pose proof (zero_divides r g2 Hg2g1) as Hg20.
      rewrite Hg10, Hg20. apply associate_refl.
    - apply (associated_iff_mutual_divides d g1 g2 Hg10).
      split; [exact Hg2g1 | exact Hg1g2].
  Qed.

  (** LCM is unique up to associates *)
  Lemma lcm_unique_up_to_associate : forall l1 l2 a b : R,
      is_lcm l1 a b -> is_lcm l2 a b ->
      is_associate d l1 l2.
  Proof.
    intros l1 l2 a b [Hal1 [Hbl1 Hl1min]] [Hal2 [Hbl2 Hl2min]].
    pose proof (Hl2min l1 Hal1 Hbl1) as Hl1l2.
    pose proof (Hl1min l2 Hal2 Hbl2) as Hl2l1.
    destruct (classic (l1 = rzero R r)) as [Hl10 | Hl10].
    - rewrite Hl10 in Hl2l1.
      pose proof (zero_divides r l2 Hl2l1) as Hl20.
      rewrite Hl10, Hl20. apply associate_refl.
    - apply (associated_iff_mutual_divides d l1 l2 Hl10).
      split; [exact Hl2l1 | exact Hl1l2].
  Qed.

  (** gcd(a, 0) = a (up to associates) *)
  Lemma gcd_zero_r : forall a : R, is_gcd a a (rzero R r).
  Proof.
    intro a. unfold is_gcd. split; [| split].
    - apply divides_refl.
    - apply divides_zero.
    - intros c Hca _. exact Hca.
  Qed.

  (** gcd(0, b) = b *)
  Lemma gcd_zero_l : forall b : R, is_gcd b (rzero R r) b.
  Proof.
    intro b. unfold is_gcd. split; [| split].
    - apply divides_zero.
    - apply divides_refl.
    - intros c _ Hcb. exact Hcb.
  Qed.

  (** gcd of units: gcd(u, b) = 1 when u is a unit *)
  Lemma gcd_unit_l : forall u b : R,
      is_unit r u ->
      is_gcd (rone R r) u b.
  Proof.
    intros u b Hu. unfold is_gcd. split; [| split].
    - apply unit_divides_all. exact (unit_one r).
    - apply unit_divides_all. exact (unit_one r).
    - intros c Hcu _.
      apply (divides_trans r c u (rone R r) Hcu).
      apply (proj1 (unit_iff_divides_one r comm u)). exact Hu.
  Qed.

  (** lcm(a, 0) = 0 *)
  Lemma lcm_zero_r : forall a : R, is_lcm (rzero R r) a (rzero R r).
  Proof.
    intro a. unfold is_lcm. split; [| split].
    - apply divides_zero.
    - apply divides_refl.
    - intros c _ Hc0. exact Hc0.
  Qed.

  (** UFD: GCD exists from factorizations *)
  (** The general proof that every UFD has GCDs is given as an axiom,
      as the full proof requires manipulating prime-exponent vectors. *)
(* CAG zero-dependent Axiom ufd_gcd_exists theories/Domains/GCD_LCM.v:104 BEGIN
  Axiom ufd_gcd_exists : forall (H : IsUFD d) (a b : R),
      a <> rzero R r -> b <> rzero R r ->
      exists g : R, is_gcd g a b.
   CAG zero-dependent Axiom ufd_gcd_exists theories/Domains/GCD_LCM.v:104 END *)

(* CAG zero-dependent Axiom ufd_lcm_exists theories/Domains/GCD_LCM.v:108 BEGIN
  Axiom ufd_lcm_exists : forall (H : IsUFD d) (a b : R),
      a <> rzero R r -> b <> rzero R r ->
      exists l : R, is_lcm l a b.
   CAG zero-dependent Axiom ufd_lcm_exists theories/Domains/GCD_LCM.v:108 END *)

  (** GCD * LCM = a * b (up to associates) in a UFD *)
(* CAG zero-dependent Axiom ufd_gcd_lcm_product theories/Domains/GCD_LCM.v:113 BEGIN
  Axiom ufd_gcd_lcm_product : forall (H : IsUFD d) (a b g l : R),
      is_gcd g a b ->
      is_lcm l a b ->
      is_associate d (rmul R r g l) (rmul R r a b).
   CAG zero-dependent Axiom ufd_gcd_lcm_product theories/Domains/GCD_LCM.v:113 END *)

End GCD.

Arguments is_gcd {R} d g a b.
Arguments is_lcm {R} d l a b.
