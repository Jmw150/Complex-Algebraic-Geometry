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
(* CAG zero-dependent Axiom upper_triangular_is_subalgebra theories/Lie/Triangular.v:19 BEGIN
Axiom upper_triangular_is_subalgebra :
  forall {F : Type} (fld : Field F) (n : nat),
    IsSubalgebra (gl fld n) (IsUpperTriangular fld n).
   CAG zero-dependent Axiom upper_triangular_is_subalgebra theories/Lie/Triangular.v:19 END *)

(** ** Strictly upper triangular matrices n(n,F) *)

(** A matrix is strictly upper triangular if all entries on and below the diagonal are zero. *)
Definition IsStrictlyUpperTriangular {F : Type} (fld : Field F) (n : nat) (A : Matrix F) : Prop :=
  forall i j, (j <= i)%nat -> i < List.length A ->
    List.nth j (List.nth i A []) (cr_zero fld) = cr_zero fld.

(** n(n,F) is a Lie subalgebra of gl(n,F). *)
(* CAG zero-dependent Axiom strictly_upper_triangular_is_subalgebra theories/Lie/Triangular.v:31 BEGIN
Axiom strictly_upper_triangular_is_subalgebra :
  forall {F : Type} (fld : Field F) (n : nat),
    IsSubalgebra (gl fld n) (IsStrictlyUpperTriangular fld n).
   CAG zero-dependent Axiom strictly_upper_triangular_is_subalgebra theories/Lie/Triangular.v:31 END *)

(** n(n,F) is an ideal of t(n,F). *)
(* CAG zero-dependent Axiom strictly_upper_triangular_is_ideal theories/Lie/Triangular.v:36 BEGIN
Axiom strictly_upper_triangular_is_ideal :
  forall {F : Type} (fld : Field F) (n : nat),
    IsIdeal (gl fld n) (IsStrictlyUpperTriangular fld n).
   CAG zero-dependent Axiom strictly_upper_triangular_is_ideal theories/Lie/Triangular.v:36 END *)

(** ** Diagonal matrices b(n,F) *)

(** A matrix is diagonal if all off-diagonal entries are zero. *)
Definition IsDiagonal {F : Type} (fld : Field F) (n : nat) (A : Matrix F) : Prop :=
  forall i j, i <> j -> i < List.length A ->
    List.nth j (List.nth i A []) (cr_zero fld) = cr_zero fld.

(** b(n,F) is a Lie subalgebra of gl(n,F). *)
(* CAG zero-dependent Axiom diagonal_is_subalgebra theories/Lie/Triangular.v:48 BEGIN
Axiom diagonal_is_subalgebra :
  forall {F : Type} (fld : Field F) (n : nat),
    IsSubalgebra (gl fld n) (IsDiagonal fld n).
   CAG zero-dependent Axiom diagonal_is_subalgebra theories/Lie/Triangular.v:48 END *)

(** [b(n,F), n(n,F)] = n(n,F): the bracket of a diagonal matrix with a
    strictly upper-triangular matrix lies in n(n,F), and every element of
    n(n,F) is realized this way.

    Stated as a Conjecture pending bracket-span infrastructure for matrix
    Lie algebras. Reference: Humphreys §1.2. *)
(* CAG zero-dependent Conjecture diagonal_strictly_upper_bracket theories/Lie/Triangular.v:66 BEGIN
Conjecture diagonal_strictly_upper_bracket :
  forall {F : Type} (fld : Field F) (n : nat) (A : Matrix F),
    IsStrictlyUpperTriangular fld n A <->
    exists (D N : Matrix F),
      IsDiagonal fld n D /\ IsStrictlyUpperTriangular fld n N /\
      A = mat_bracket fld D N.
   CAG zero-dependent Conjecture diagonal_strictly_upper_bracket theories/Lie/Triangular.v:66 END *)

(** [t(n,F), t(n,F)] = n(n,F): the derived algebra of upper-triangular
    matrices equals strictly-upper-triangular matrices.

    Stated as a Conjecture for the same reason. Reference: Humphreys §1.2. *)
(* CAG zero-dependent Conjecture upper_triangular_derived theories/Lie/Triangular.v:77 BEGIN
Conjecture upper_triangular_derived :
  forall {F : Type} (fld : Field F) (n : nat) (A : Matrix F),
    IsStrictlyUpperTriangular fld n A <->
    exists (B C : Matrix F),
      IsUpperTriangular fld n B /\ IsUpperTriangular fld n C /\
      A = mat_bracket fld B C.
   CAG zero-dependent Conjecture upper_triangular_derived theories/Lie/Triangular.v:77 END *)
