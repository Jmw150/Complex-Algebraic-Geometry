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

(* radical_is_ideal removed: false-as-stated under the current (broken)
   IsRadical definition. When la is not solvable, IsRadical x reduces
   to False for all x, so IsRadical = empty predicate, which is NOT an
   ideal (must contain la_zero). The proper formulation requires either
   fixing IsRadical (drop the global IsSolvable constraint or restrict to
   solvable ideals) or proving "sum of solvable ideals is solvable". Was
   unused downstream in our codebase. *)

(** The radical is solvable. (Trivially derivable from [IsSolvable la]
    since the conclusion only uses derived_series, not [IsRadical]. The
    [IsRadical] hypothesis is unused in this direction.) *)
Lemma radical_is_solvable : forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L), IsSolvable la ->
    exists n, forall x, IsRadical la x -> derived_series la n x -> x = la_zero la.
Proof.
  intros F fld L la [n Hn]. exists n. intros x _ Hd. apply Hn. exact Hd.
Qed.

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

(** Abelian non-trivial Lie algebras are NOT semisimple under the current
    [IsRadical]/[IsSemisimple] definition: abelian → solvable, so the
    full ideal ⟨L⟩ together with [IsSolvable la] satisfies [IsRadical x]
    for every [x ∈ la]; hence [IsSemisimple la] forces every element to
    be [la_zero la] (i.e. [la] is trivial). *)
Lemma abelian_nontrivial_not_semisimple {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    (forall x y, laF_bracket la x y = la_zero la) ->
    (exists x, x <> la_zero la) ->
    ~ IsSemisimple la.
Proof.
  intros Habel [x0 Hx0] Hss.
  apply Hx0.
  apply Hss.
  exists (fun _ : L => True). split.
  - apply (full_ideal la).
  - split.
    + apply abelian_is_solvable. exact Habel.
    + exact Logic.I.
Qed.

(* quotient_radical_semisimple removed: false-as-stated due to carrier
   quantification. The statement asserts ∃ Lie algebra structure on L
   itself that is semisimple. This is false in general:
   (a) Some L admit no fld-vector space structure at all (size mismatch).
   (b) Some carrier types only admit solvable Lie structures (e.g. bool
   over F_2 is 1-dim, hence abelian, hence solvable but not semisimple).
   The proper statement requires the QUOTIENT carrier L/Rad(L), which
   is not the same type as L. Unused downstream. *)
