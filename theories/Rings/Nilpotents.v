(** * Nilpotents.v — Nilpotent elements and the nilradical *)

From CAG Require Import Rings.Ring Rings.Ideals.
From Stdlib Require Import Arith Lia.

(* ================================================================== *)
(** ** Nilpotent elements *)
(* ================================================================== *)

Definition is_nilpotent {R : Type} (r : Ring R) (x : R) : Prop :=
  exists n : nat, n > 0 /\ ring_pow r x n = rzero R r.

(** The nilradical: all nilpotent elements *)
Definition nilradical {R : Type} (r : Ring R) : R -> Prop :=
  fun x => is_nilpotent r x.

(* ================================================================== *)
(** ** Basic properties *)
(* ================================================================== *)

Section NilpotentLemmas.
  Context {R : Type} (r : Ring R).

  (** 0 is nilpotent: 0^1 = 0 *)
  Lemma zero_nilpotent : is_nilpotent r (rzero R r).
  Proof.
    unfold is_nilpotent.
    exists 1. split; [lia |].
    simpl. apply rmul_zero_l.
  Qed.

  (** Ring hom sends nilpotents to nilpotents *)
  Lemma hom_preserves_nilpotent :
    forall {S : Type} (s : Ring S) (rh : RingHom r s) (x : R),
      is_nilpotent r x -> is_nilpotent s (rhom_fn rh x).
  Proof.
    intros S s rh x [n [Hn Hpow]].
    unfold is_nilpotent.
    exists n. split; [exact Hn |].
    (* φ(x^n) = φ(x)^n *)
    assert (Hpow_hom : forall m, rhom_fn rh (ring_pow r x m) =
                                 ring_pow s (rhom_fn rh x) m).
    { intro m. induction m as [| k IH].
      - simpl. apply rhom_one.
      - simpl. rewrite rhom_mul, IH. reflexivity. }
    rewrite <- Hpow_hom, Hpow.
    apply rhom_zero.
  Qed.

  (** Nilradical is an ideal (for commutative rings — admitted for general) *)
(* CAG zero-dependent Admitted nilradical_is_ideal theories/Rings/Nilpotents.v:60 BEGIN
  Lemma nilradical_is_ideal (Hcomm : forall a b, rmul R r a b = rmul R r b a) :
      is_ideal r (nilradical r).
  Proof.
    unfold is_ideal, is_left_ideal, is_right_ideal, is_add_subgroup, nilradical.
    split; split; try split; try split.
    - (* 0 nilpotent *)
      apply zero_nilpotent.
    - (* sum of nilpotents is nilpotent (commutative case) *)
      intros a b [m [Hm Hxm]] [n [Hn Hyn]].
      unfold is_nilpotent. Admitted.
   CAG zero-dependent Admitted nilradical_is_ideal theories/Rings/Nilpotents.v:60 END *)

End NilpotentLemmas.

(* ================================================================== *)
(** ** Axioms *)
(* ================================================================== *)

(** Nil(R/Nil(R)) = {0}.

    Informal statement: the quotient R/Nil(R) is reduced (has no nonzero
    nilpotents).  Equivalently, every nilpotent element of R lies in
    Nil(R) — i.e. Nil(R) is "saturated" under taking nilpotents.
    Without quotient-ring infrastructure, we encode this directly:
    if x ∈ R has a power x^n that lies in Nil(R), then x already lies
    in Nil(R).

    Reference: Atiyah-Macdonald, Introduction to Commutative Algebra
    (1969) Proposition 1.7; Eisenbud, Commutative Algebra with a View
    Toward Algebraic Geometry (1995) §2.1. *)
(* CAG zero-dependent Conjecture nilradical_quotient_reduced theories/Rings/Nilpotents.v:82 BEGIN
Conjecture nilradical_quotient_reduced :
  forall {R : Type} (r : Ring R)
         (HN : is_ideal r (nilradical r))
         (x : R) (n : nat),
    n > 0 ->
    is_nilpotent r (ring_pow r x n) ->
    is_nilpotent r x.
   CAG zero-dependent Conjecture nilradical_quotient_reduced theories/Rings/Nilpotents.v:82 END *)

(** Polynomial unit criterion.

    Informal statement: in R[x], a polynomial f(x) = a_0 + a_1 x + ... +
    a_n x^n is a unit iff a_0 is a unit in R and a_1, ..., a_n are
    nilpotent in R.  In particular, this gives a complete description
    of the units in the polynomial ring.

    Stated abstractly via an auxiliary "is unit in R[x]" predicate
    with the corresponding coefficient-side characterization, pending
    a formal polynomial ring construction.

    Reference: Atiyah-Macdonald, Introduction to Commutative Algebra
    (1969) Exercise 1.2(ii) / Chapter 1 §1; Lang, Algebra (3rd ed.)
    Chapter IV §1 Exercise 4. *)
(* CAG zero-dependent Conjecture poly_unit_criterion theories/Rings/Nilpotents.v:104 BEGIN
Conjecture poly_unit_criterion :
  forall {R : Type} (r : CommutativeRing R)
         (a0 : R) (coeffs : list R)
         (is_unit_in_R    : R -> Prop)
         (is_unit_in_RofX : R -> list R -> Prop),
    is_unit_in_RofX a0 coeffs <->
    (is_unit_in_R a0 /\
     forall a, List.In a coeffs -> is_nilpotent (cring R r) a).
   CAG zero-dependent Conjecture poly_unit_criterion theories/Rings/Nilpotents.v:104 END *)
