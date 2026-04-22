(** * ATT/Signature.v
    Algebraic signature: sorts and function symbols with arities. *)

From Stdlib Require Import Lists.List.
Import ListNotations.

Set Universe Polymorphism.

(** ** Algebraic signature

    An algebraic signature Sg consists of:
    - a type [sg_ty]  of sorts / base types
    - a type [sg_fun] of function symbols
    - a function [sg_dom] assigning a list of argument sorts to each function symbol
    - a function [sg_cod] assigning a result sort to each function symbol *)

Record Signature : Type := {
  sg_ty  : Type;
  sg_fun : Type;
  sg_dom : sg_fun -> list sg_ty;
  sg_cod : sg_fun -> sg_ty;
}.

(** ** Examples *)

(** The empty signature: no sorts, no function symbols. *)
Definition EmptySig : Signature := {|
  sg_ty  := Empty_set;
  sg_fun := Empty_set;
  sg_dom := fun f => match f with end;
  sg_cod := fun f => match f with end;
|}.

(** A single-sort signature with a list of function symbols,
    given by their arity as a number (so dom f = list of n copies of the one sort). *)
Definition UnarySig (funs : Type) (arity : funs -> nat) : Signature.
Proof.
  refine {|
    sg_ty  := unit;
    sg_fun := funs;
    sg_dom := fun f => List.repeat tt (arity f);
    sg_cod := fun _ => tt;
  |}.
Defined.
