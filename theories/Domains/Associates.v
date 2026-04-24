(** * Domains/Associates.v — Associate elements in integral domains

    Two elements are associates if they differ by multiplication by a unit.

    Reference: Dummit & Foote §8.1. *)

From CAG Require Import Rings.Ring Domains.Divisibility.
From Stdlib Require Import Arith Lia.

(* ================================================================== *)
(** ** Associate elements *)
(* ================================================================== *)

Section Associates.
  Context {R : Type} (d : IntegralDomain R).

  Let r   : Ring R                                      := id_r d.
  Let comm : forall a b : R, rmul R r a b = rmul R r b a := id_comm d.

  (** a and b are associates if ∃ unit u, b = u * a *)
  Definition is_associate (a b : R) : Prop :=
    exists u : R, is_unit r u /\ b = rmul R r u a.

  (** Associates is reflexive (u = 1) *)
  Lemma associate_refl : forall a : R, is_associate a a.
  Proof.
    intro a. unfold is_associate.
    exists (rone R r). split.
    - apply unit_one.
    - symmetry. apply rmul_one_l.
  Qed.

  (** Associates is symmetric *)
  Lemma associate_sym : forall a b : R,
      is_associate a b -> is_associate b a.
  Proof.
    intros a b [u [[uinv [Hur Hul]] Hb]].
    unfold is_associate.
    exists uinv. split.
    - unfold is_unit. exists u. split; [exact Hul | exact Hur].
    - (* a = uinv * b = uinv * (u * a) = (uinv * u) * a = 1 * a = a *)
      rewrite Hb. symmetry.
      transitivity (rmul R r (rmul R r uinv u) a).
      + exact (rmul_assoc R r uinv u a).
      + rewrite Hul. apply rmul_one_l.
  Qed.

  (** Associates is transitive *)
  Lemma associate_trans : forall a b c : R,
      is_associate a b -> is_associate b c -> is_associate a c.
  Proof.
    intros a b c [u [Hu Hb]] [v [Hv Hc]].
    unfold is_associate.
    exists (rmul R r v u). split.
    - apply unit_mul; assumption.
    - rewrite Hc, Hb.
      (* Goal: v * (u * a) = (v * u) * a *)
      apply rmul_assoc.
  Qed.

  (** a and b are associates iff each divides the other (when a ≠ 0) *)
  Lemma associated_iff_mutual_divides : forall a b : R,
      a <> rzero R r ->
      (is_associate a b <->
       divides r a b /\ divides r b a).
  Proof.
    intros a b Ha. split.
    - intros [u [Hu Hb]]. split.
      + (* a | b: b = u * a, so b = a * u (comm) *)
        exists u. rewrite Hb. apply comm.
      + (* b | a: b = u*a, a = uinv*b = (u*a)*uinv = (a*u)*uinv = a*(u*uinv) = a*1 = a *)
        destruct Hu as [uinv [Hur Hul]].
        exists uinv. rewrite Hb. symmetry.
        (* Goal: (u*a)*uinv = a *)
        rewrite (comm u a).
        (* Goal: (a*u)*uinv = a *)
        transitivity (rmul R r a (rmul R r u uinv)).
        * exact (eq_sym (rmul_assoc R r a u uinv)).
        * rewrite Hur. apply rmul_one_r.
    - intros [[c Hbc] [e Hae]].
      (* b = a*c, a = b*e *)
      assert (Hb0 : b <> rzero R r).
      { intro Hb. rewrite Hb in Hae.
        rewrite rmul_zero_l in Hae. exact (Ha Hae). }
      (* e*c = 1 by cancellation: b*(e*c) = (b*e)*c = a*c = b = b*1 *)
      assert (Hec : rmul R r e c = rone R r).
      { apply (mul_cancel_l r (id_no_zero_div d) b).
        - exact Hb0.
        - rewrite rmul_one_r.
          (* Goal: b * (e * c) = b *)
          (* b*(e*c) = (b*e)*c = a*c = b *)
          transitivity (rmul R r (rmul R r b e) c).
          + exact (rmul_assoc R r b e c).
          + rewrite <- Hae, <- Hbc. reflexivity. }
      unfold is_associate. exists c. split.
      + unfold is_unit. exists e. split.
        * rewrite (comm c e). exact Hec.
        * exact Hec.
      + rewrite Hbc. apply id_comm.
  Qed.

  (** Associates iff unit multiple: alternative formulation *)
  Lemma associated_iff_unit_mul : forall a b : R,
      is_associate a b <->
      exists u : R, is_unit r u /\ b = rmul R r u a.
  Proof.
    intros a b. unfold is_associate. tauto.
  Qed.

  (** If a is associate to b then a and b have the same divisors *)
  Lemma associate_divides_iff : forall a b c : R,
      is_associate a b ->
      (divides r a c <-> divides r b c).
  Proof.
    intros a b c [u [Hu Hb]]. split.
    - intros [x Hx].
      destruct Hu as [uinv [Hur Hul]].
      exists (rmul R r uinv x).
      rewrite Hx, Hb.
      (* Goal: a*x = (u*a)*(uinv*x)
         Strategy: (u*a)*(uinv*x) = (a*u)*(uinv*x) [comm]
                                   = a*(u*(uinv*x)) [assoc backward]
                                   = a*((u*uinv)*x) [assoc forward]
                                   = a*(1*x)        [Hur]
                                   = a*x            [rmul_one_l] *)
      rewrite (comm u a).
      symmetry.
      transitivity (rmul R r a (rmul R r u (rmul R r uinv x))).
      + exact (eq_sym (rmul_assoc R r a u (rmul R r uinv x))).
      + f_equal.
        transitivity (rmul R r (rmul R r u uinv) x).
        * exact (rmul_assoc R r u uinv x).
        * rewrite Hur. apply rmul_one_l.
    - intros [x Hx].
      exists (rmul R r u x).
      rewrite Hx, Hb.
      (* Goal: (u*a)*x = a*(u*x)
         (u*a)*x = (a*u)*x [comm] = a*(u*x) [assoc backward] *)
      rewrite (comm u a).
      exact (eq_sym (rmul_assoc R r a u x)).
  Qed.

End Associates.

Arguments is_associate {R} d a b.
