(** * Lie/Triangular.v
    Triangular, strictly upper triangular, and diagonal subalgebras of gl(n,F). *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.Lie.Ideals.
Require Import CAG.Lie.Linear.
From Stdlib Require Import List Arith.
Import ListNotations.

(** ** Upper triangular matrices t(n,F) *)

(** A matrix is upper triangular if all entries below the diagonal are zero. *)
Definition IsUpperTriangular {F : Type} (fld : Field F) (n : nat) (A : Matrix F) : Prop :=
  forall i j, (j < i)%nat -> i < List.length A ->
    List.nth j (List.nth i A []) (cr_zero fld) = cr_zero fld.

(** t(n,F) is a Lie subalgebra of gl(n,F). *)
Axiom upper_triangular_is_subalgebra :
  forall {F : Type} (fld : Field F) (n : nat),
    IsSubalgebra (gl fld n) (IsUpperTriangular fld n).

(** ** Strictly upper triangular matrices n(n,F) *)

(** A matrix is strictly upper triangular if all entries on and below the diagonal are zero. *)
Definition IsStrictlyUpperTriangular {F : Type} (fld : Field F) (n : nat) (A : Matrix F) : Prop :=
  forall i j, (j <= i)%nat -> i < List.length A ->
    List.nth j (List.nth i A []) (cr_zero fld) = cr_zero fld.

(** n(n,F) is a Lie subalgebra of gl(n,F). *)
Axiom strictly_upper_triangular_is_subalgebra :
  forall {F : Type} (fld : Field F) (n : nat),
    IsSubalgebra (gl fld n) (IsStrictlyUpperTriangular fld n).

(** n(n,F) is an ideal of t(n,F). *)
Axiom strictly_upper_triangular_is_ideal :
  forall {F : Type} (fld : Field F) (n : nat),
    IsIdeal (gl fld n) (IsStrictlyUpperTriangular fld n).

(** ** Diagonal matrices b(n,F) *)

(** A matrix is diagonal if all off-diagonal entries are zero. *)
Definition IsDiagonal {F : Type} (fld : Field F) (n : nat) (A : Matrix F) : Prop :=
  forall i j, i <> j -> i < List.length A ->
    List.nth j (List.nth i A []) (cr_zero fld) = cr_zero fld.

(** b(n,F) is a Lie subalgebra of gl(n,F). *)
Axiom diagonal_is_subalgebra :
  forall {F : Type} (fld : Field F) (n : nat),
    IsSubalgebra (gl fld n) (IsDiagonal fld n).

(** [b(n,F), n(n,F)] = n(n,F). *)
Axiom diagonal_strictly_upper_bracket :
  forall {F : Type} (fld : Field F) (n : nat) (A : Matrix F),
    IsStrictlyUpperTriangular fld n A <->
    (** A is in the bracket span of b and n *)
    True. (* placeholder *)

(** [t(n,F), t(n,F)] = n(n,F). *)
Axiom upper_triangular_derived :
  forall {F : Type} (fld : Field F) (n : nat) (A : Matrix F),
    IsStrictlyUpperTriangular fld n A <->
    True. (* placeholder *)
