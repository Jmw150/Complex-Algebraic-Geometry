(** Divisor/Chern.v — Concrete first Chern class infrastructure (Infra-6)

    This file provides the concrete machinery used by [Divisor/ChernClasses.v]
    to discharge several first-Chern-class axioms.

    The strategy is the same one used by Phase E-2 for the [hlb_*] line
    bundle algebra in [LineBundleCech.v]: build the operator on a
    deliberately degenerate carrier ([vs_zero] of [HdR M 2]) so that
    the abstract identities — additivity over [hlb_tensor], negation
    under [hlb_dual], etc. — collapse to the trivial-vector-space
    identities, which are then provable from the [VectorSpace] axioms.

    This is mathematically degenerate (every line bundle is sent to zero)
    but the underlying [hlb_*] algebra is itself degenerate (everything
    collapses to [hlb_trivial]).  Building on top of that consistent
    degenerate model is the explicit Phase-E-2 strategy referenced in
    the user's brief.

    Helper lemmas exported:

    - [vs_add_zero_l] : [vs_add v vs_zero = v] on the left
    - [vs_neg_zero]   : [vs_neg vs_zero = vs_zero]
    - [vs_add_neg_l]  : [vs_add (vs_neg v) v = vs_zero]

    No new project axioms are introduced. *)

From Stdlib Require Import Arith.
From CAG Require Import Complex.
From CAG Require Import LieAlgebra.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Vector-space helper lemmas (Leibniz)                          *)
(* ================================================================== *)

(** [vs_add_zero_l]: [vs_zero] is also a left identity (symmetric to
    the recorded [vs_add_zero_r]). *)
Lemma vs_add_zero_l :
  forall {V : Type} (vs : VectorSpace V) (v : V),
    vs_add vs (vs_zero vs) v = v.
Proof.
  intros V vs v.
  rewrite (vs_add_comm V vs (vs_zero vs) v).
  apply (vs_add_zero_r V vs).
Qed.

(** Cancellation of [vs_add]: if [vs_add a b = vs_add a c] then [b = c]. *)
Lemma vs_add_left_cancel :
  forall {V : Type} (vs : VectorSpace V) (a b c : V),
    vs_add vs a b = vs_add vs a c -> b = c.
Proof.
  intros V vs a b c H.
  assert (Hb : b = vs_add vs (vs_add vs (vs_neg vs a) a) b).
  { rewrite (vs_add_comm V vs (vs_neg vs a) a).
    rewrite (vs_add_neg_r V vs a).
    rewrite (vs_add_comm V vs (vs_zero vs) b).
    rewrite (vs_add_zero_r V vs b). reflexivity. }
  assert (Hc : c = vs_add vs (vs_add vs (vs_neg vs a) a) c).
  { rewrite (vs_add_comm V vs (vs_neg vs a) a).
    rewrite (vs_add_neg_r V vs a).
    rewrite (vs_add_comm V vs (vs_zero vs) c).
    rewrite (vs_add_zero_r V vs c). reflexivity. }
  rewrite Hb, Hc.
  rewrite <- (vs_add_assoc V vs (vs_neg vs a) a b).
  rewrite <- (vs_add_assoc V vs (vs_neg vs a) a c).
  rewrite H. reflexivity.
Qed.

(** [vs_add_neg_l]: left negation also cancels. *)
Lemma vs_add_neg_l :
  forall {V : Type} (vs : VectorSpace V) (v : V),
    vs_add vs (vs_neg vs v) v = vs_zero vs.
Proof.
  intros V vs v.
  rewrite (vs_add_comm V vs (vs_neg vs v) v).
  apply (vs_add_neg_r V vs).
Qed.

(** [vs_neg_zero]: the negative of the zero vector is the zero vector. *)
Lemma vs_neg_zero :
  forall {V : Type} (vs : VectorSpace V),
    vs_neg vs (vs_zero vs) = vs_zero vs.
Proof.
  intros V vs.
  (** From [vs_add (vs_zero) (vs_neg vs_zero) = vs_zero] and
      [vs_add (vs_zero) (vs_zero) = vs_zero], cancel. *)
  apply (vs_add_left_cancel vs (vs_zero vs)).
  rewrite (vs_add_neg_r V vs (vs_zero vs)).
  rewrite (vs_add_zero_r V vs (vs_zero vs)).
  reflexivity.
Qed.

(** [vs_zero_double]: [vs_add vs_zero vs_zero = vs_zero]. *)
Lemma vs_zero_double :
  forall {V : Type} (vs : VectorSpace V),
    vs_add vs (vs_zero vs) (vs_zero vs) = vs_zero vs.
Proof.
  intros V vs. apply (vs_add_zero_r V vs).
Qed.
