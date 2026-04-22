(** * AxTheory/Theory.v
    An Ax-theory is an algebraic signature together with a list of
    Ax-axioms (equations between Ax-terms). *)

Require Import CAG.ATT.Signature.
Require Import CAG.AxTheory.Syntax.
From Stdlib Require Import Lists.List.
Import ListNotations.

Set Universe Polymorphism.

(** ** Ax-theory *)

Record AxTheory : Type := {
  ax_sig : Signature;
  ax_ax  : list (AxAxiom ax_sig);
}.


(** Shorthand: provable equality in an Ax-theory. *)
Definition AxEq (Th : AxTheory) (Γ : list (AxType Th.(ax_sig)))
    (M N : AxTerm Th.(ax_sig)) (α : AxType Th.(ax_sig)) : Prop :=
  AxThEq Th.(ax_sig) Th.(ax_ax) Γ M N α.

(** Every algebraic theory gives rise to an Ax-theory with the same
    signature and no extra axioms (the structural axioms beta/eta are
    built into AxThEq). *)
Require Import CAG.ATT.Theory.

Definition AlgToAx (Th : Theory) : AxTheory := {|
  ax_sig := Th.(th_sig);
  ax_ax  := [];   (* Algebraic axioms are not directly liftable without coercion;
                     we leave ax_ax empty and note that full lifting is in
                     GeneratedFunctionalTheory.v *)
|}.
