(* Some experiments with coinduction *)

From Stdlib Require Import List.
Import ListNotations.

CoInductive Stream : Set := Seq : nat -> Stream -> Stream.

CoInductive stream (A : Type) :=
  | Cons : A -> stream A -> stream A.

Inductive Digit : Type :=
| D0 | D1 | D2 | D3 | D4 | D5 | D6 | D7 | D8 | D9.


(* 0.[Digit][Digit]... *)
Definition Decimal := stream Digit.

CoFixpoint ones : Decimal := Cons Digit D1 ones.

Fixpoint take {A : Type} (n : nat) (s : stream A) : list A :=
  match n with
  | O => nil
  | S n' =>
      match s with
      | Cons _ x xs => cons x (take n' xs)
      end
  end.

(*
Definition hd (x: Stream) := let (a,s) := x in a.
Definition tl (x: Stream) := let (a,s) := x in s.

CoFixpoint ones : stream nat :=
  Cons nat 1 ones.
*)

Lemma take_ones :
  forall n, take n ones = repeat D1 n.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

