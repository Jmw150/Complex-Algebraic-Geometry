(** * ATT/Theory.v
    An algebraic theory is a signature together with a set of axioms. *)

Require Import CAG.ATT.Signature.
Require Import CAG.ATT.Syntax.
From Stdlib Require Import Lists.List.
Import ListNotations.

Set Universe Polymorphism.

(** ** Algebraic theory *)

Record Theory : Type := {
  th_sig  : Signature;
  th_ax   : list (TheoryAxiom th_sig);
}.


(** Shorthand: provable equality in a theory. *)
Definition Eq (Th : Theory) (Γ : list Th.(th_sig).(sg_ty))
    (t1 t2 : Term Th.(th_sig)) (τ : Th.(th_sig).(sg_ty)) : Prop :=
  ThEq Th.(th_sig) Th.(th_ax) Γ t1 t2 τ.

(** Examples are in ATT/Examples/ to avoid universe issues. *)
