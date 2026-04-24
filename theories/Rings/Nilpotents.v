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

End NilpotentLemmas.

(* ================================================================== *)
(** ** Axioms *)
(* ================================================================== *)

(** Nil(R/Nil(R)) = {0} *)
Axiom nilradical_quotient_reduced :
  forall {R : Type} (r : Ring R)
         (HN : is_ideal r (nilradical r)),
  True. (* placeholder: formal statement needs QuotientRing *)

(** Polynomial unit criterion *)
Axiom poly_unit_criterion :
  forall {R : Type} (r : CommutativeRing R),
  True. (* placeholder: requires polynomial ring infrastructure *)
