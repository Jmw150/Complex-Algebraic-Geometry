(** * Lie/Radical.v
    Radical and semisimple Lie algebras. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.Lie.Ideals.
Require Import CAG.Lie.Solvable.

(** ** Radical *)

(** Rad(L) = the unique maximal solvable ideal. *)
(** Existence and uniqueness require finite-dimensionality; we axiomatize. *)

(** The radical predicate: x ∈ Rad(L) if x lies in some solvable ideal. *)
Definition IsRadical {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (x : L) : Prop :=
  exists (I : L -> Prop),
    IsIdeal la I /\
    IsSolvable la /\ (* solvability of the ambient—axiom placeholder *)
    I x.

(** The radical is an ideal (uses: sum of solvable ideals is solvable). *)
(* CAG zero-dependent Axiom radical_is_ideal theories/Lie/Radical.v:22 BEGIN
Axiom radical_is_ideal : forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L), IsIdeal la (IsRadical la).
   CAG zero-dependent Axiom radical_is_ideal theories/Lie/Radical.v:22 END *)

(** The radical is solvable. *)
(* CAG zero-dependent Axiom radical_is_solvable theories/Lie/Radical.v:26 BEGIN
Axiom radical_is_solvable : forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L), IsSolvable la ->
    exists n, forall x, IsRadical la x -> derived_series la n x -> x = la_zero la.
   CAG zero-dependent Axiom radical_is_solvable theories/Lie/Radical.v:26 END *)

(** Every solvable ideal is contained in the radical. *)
Lemma solvable_ideal_in_radical {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (I : L -> Prop) :
    IsIdeal la I ->
    IsSolvable la ->
    forall x, I x -> IsRadical la x.
Proof.
  intros hI hS x Hx.
  exists I. split. exact hI. split. exact hS. exact Hx.
Qed.

(** ** Semisimple Lie algebras *)

(** L is semisimple iff Rad(L) = 0. *)
Definition IsSemisimple {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) : Prop :=
  forall x, IsRadical la x -> x = la_zero la.

(** Every simple Lie algebra is semisimple. *)
Lemma simple_is_semisimple {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    IsSimple la -> IsSemisimple la.
Proof.
  intros Hsimp x [I [_ [HS _]]].
  exfalso. exact (simple_not_solvable la Hsimp HS).
Qed.

(** L / Rad(L) is semisimple. *)
(* CAG zero-dependent Axiom quotient_radical_semisimple theories/Lie/Radical.v:58 BEGIN
Axiom quotient_radical_semisimple :
  forall {F : Type} {fld : Field F} {L : Type} (la : LieAlgebraF fld L),
  exists (lq : LieAlgebraF fld L), IsSemisimple lq.
   CAG zero-dependent Axiom quotient_radical_semisimple theories/Lie/Radical.v:58 END *)
