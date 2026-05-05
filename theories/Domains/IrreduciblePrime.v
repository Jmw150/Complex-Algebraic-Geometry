(** * Domains/IrreduciblePrime.v — Irreducibles and prime elements

    Formalizes irreducible elements, prime elements, and the
    relationship between them.

    Reference: Dummit & Foote §8.1–8.3. *)

From CAG Require Import Rings.Ring Domains.Divisibility Domains.Associates.
From Stdlib Require Import Arith Lia.

(* ================================================================== *)
(** ** Irreducible elements *)
(* ================================================================== *)

Section IrrPrime.
  Context {R : Type} (d : IntegralDomain R).

  Let r    : Ring R                                       := id_r d.
  Let comm : forall a b : R, rmul R r a b = rmul R r b a  := id_comm d.

  (** p is irreducible if:
      - p is nonzero and not a unit
      - whenever p = a*b, either a or b is a unit *)
  Definition is_irreducible (p : R) : Prop :=
    p <> rzero R r /\
    ~ is_unit r p /\
    forall a b : R,
      rmul R r a b = p ->
      is_unit r a \/ is_unit r b.

  (** p is prime if:
      - p is nonzero and not a unit
      - p | a*b implies p | a or p | b *)
  Definition is_prime (p : R) : Prop :=
    p <> rzero R r /\
    ~ is_unit r p /\
    forall a b : R,
      divides r p (rmul R r a b) ->
      divides r p a \/ divides r p b.

  (** In any integral domain, prime implies irreducible *)
  Theorem prime_irreducible : forall p : R,
      is_prime p -> is_irreducible p.
  Proof.
    intros p [Hp0 [Hpu Hprime]].
    split; [exact Hp0 | split; [exact Hpu |]].
    intros a b Hab.
    (* p = a*b, so p | a*b *)
    assert (Hdiv : divides r p (rmul R r a b)).
    { exists (rone R r). rewrite Hab. symmetry. apply rmul_one_r. }
    destruct (Hprime a b Hdiv) as [[c Hc] | [c Hc]].
    - (* p | a: a = p*c. Then p = a*b = (p*c)*b = p*(c*b).
         Cancel p: c*b = 1. So b is a unit. *)
      right.
      assert (Hpcb : rmul R r p (rmul R r c b) = p).
      { transitivity (rmul R r (rmul R r p c) b).
        + exact (rmul_assoc R r p c b).
        + rewrite <- Hc. exact Hab. }
      assert (Hcb1 : rmul R r c b = rone R r).
      { apply (mul_cancel_l r (id_no_zero_div d) p).
        - exact Hp0.
        - rewrite rmul_one_r. exact Hpcb. }
      (* b is a unit with left-inverse c; commutativity gives full unit *)
      unfold is_unit. exists c. split.
      + rewrite (comm b c). exact Hcb1.
      + exact Hcb1.
    - (* p | b: b = p*c. Then p = a*b = a*(p*c) = p*(a*c) (comm).
         Cancel p: a*c = 1. So a is a unit. *)
      left.
      assert (Hpac : rmul R r p (rmul R r a c) = p).
      { (* p*(a*c) = (p*a)*c = (a*p)*c = a*(p*c) = a*b = p *)
        transitivity (rmul R r (rmul R r p a) c).
        - exact (rmul_assoc R r p a c).
        - rewrite (comm p a).
          transitivity (rmul R r a (rmul R r p c)).
          + exact (eq_sym (rmul_assoc R r a p c)).
          + rewrite <- Hc. exact Hab. }
      assert (Hac1 : rmul R r a c = rone R r).
      { apply (mul_cancel_l r (id_no_zero_div d) p).
        - exact Hp0.
        - rewrite rmul_one_r. exact Hpac. }
      unfold is_unit. exists c. split.
      + exact Hac1.
      + rewrite (comm c a). exact Hac1.
  Qed.

  (** Associated irreducibles divide each other *)
  Lemma associate_irreducibles_divide : forall p q : R,
      is_irreducible p -> is_irreducible q ->
      is_associate d p q ->
      divides r p q /\ divides r q p.
  Proof.
    intros p q Hp Hq Hassoc.
    split.
    - destruct Hassoc as [u [Hu Hq']].
      exists u. rewrite Hq'. apply comm.
    - apply associate_sym in Hassoc.
      destruct Hassoc as [u [Hu Hp']].
      exists u. rewrite Hp'. apply comm.
  Qed.

  (** If irreducible p divides q, then they are associates *)
  Lemma irreducible_dvd_implies_associate : forall p q : R,
      is_irreducible p -> is_irreducible q ->
      divides r p q ->
      is_associate d p q.
  Proof.
    intros p q [Hp0 [Hpu Hpirr]] [Hq0 [Hqu Hqirr]] [c Hc].
    (* q = p*c; since q is irreducible, p or c is a unit.
       p is not a unit, so c is a unit. Then p and q are associates. *)
    assert (Hcase : is_unit r p \/ is_unit r c).
    { apply Hqirr. exact (eq_sym Hc). }
    destruct Hcase as [Hup | Huc].
    - contradiction.
    - unfold is_associate. exists c.
      split; [exact Huc |].
      rewrite Hc. apply comm.
  Qed.

  (** Associatedness preserves primality *)
  Lemma prime_associate_prime : forall p q : R,
      is_prime p -> is_associate d p q -> is_prime q.
  Proof.
    intros p q [Hp0 [Hpu Hprime]] Hassoc.
    assert (Hdivs : divides r p q /\ divides r q p).
    { apply associated_iff_mutual_divides.
      exact Hp0.
      exact Hassoc. }
    destruct Hdivs as [_ Hqdivp].
    split.
    - intro Hq0.
      apply Hp0.
      apply zero_divides with (r := r).
      rewrite <- Hq0.
      exact Hqdivp.
    - split.
      + intros Hqu.
        apply Hpu.
        destruct (associate_sym d p q Hassoc) as [u [Hu Hp]].
        rewrite Hp.
        apply unit_mul; assumption.
      + intros a b Hqab.
        assert (Hpab : divides r p (rmul R r a b)).
        { apply (proj2 (associate_divides_iff d p q (rmul R r a b) Hassoc)).
          exact Hqab. }
        destruct (Hprime a b Hpab) as [Hpa | Hpb].
        * left.
          apply (proj1 (associate_divides_iff d p q a Hassoc)).
          exact Hpa.
        * right.
          apply (proj1 (associate_divides_iff d p q b Hassoc)).
          exact Hpb.
  Qed.

End IrrPrime.

Arguments is_irreducible {R} d p.
Arguments is_prime {R} d p.
