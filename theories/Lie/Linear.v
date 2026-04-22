(** * Lie/Linear.v
    General linear Lie algebra gl(V), matrix units, Jacobi for commutator. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
From Stdlib Require Import List Arith Bool.
Import ListNotations.

(** ** Endomorphisms as square matrices over F *)

(** We represent n×n matrices as lists of lists of F. *)
Definition Matrix (F : Type) := list (list F).

(** Zero matrix. *)
Definition mat_zero {F : Type} (fld : Field F) (n : nat) : Matrix F :=
  List.repeat (List.repeat (cr_zero fld) n) n.

(** Matrix addition. *)
Definition mat_add {F : Type} (fld : Field F) (A B : Matrix F) : Matrix F :=
  List.map (fun '(r1, r2) =>
    List.map (fun '(a, b) => cr_add fld a b) (List.combine r1 r2))
  (List.combine A B).

(** Scalar multiplication. *)
Definition mat_scale {F : Type} (fld : Field F) (c : F) (A : Matrix F) : Matrix F :=
  List.map (fun row => List.map (fun a => cr_mul fld c a) row) A.

(** Negation. *)
Definition mat_neg {F : Type} (fld : Field F) (A : Matrix F) : Matrix F :=
  mat_scale fld (cr_neg fld (cr_one fld)) A.

(** Matrix multiplication (n×n). *)
Definition mat_mul {F : Type} (fld : Field F) (A B : Matrix F) : Matrix F :=
  List.map (fun row_A =>
    List.map (fun col_idx =>
      List.fold_left (fun acc '(a, row_B) =>
        cr_add fld acc (cr_mul fld a (List.nth col_idx row_B (cr_zero fld))))
        (List.combine row_A A) (cr_zero fld))
      (List.seq 0 (List.length row_A)))
  A.

(** The commutator [A,B] = AB - BA. *)
Definition mat_bracket {F : Type} (fld : Field F) (A B : Matrix F) : Matrix F :=
  mat_add fld (mat_mul fld A B)
              (mat_neg fld (mat_mul fld B A)).

(** ** gl(n, F) as a Lie algebra *)

(** The gl(n,F) Lie algebra on n×n matrices. *)
Definition gl_vs {F : Type} (fld : Field F) (n : nat) : VectorSpaceF fld (Matrix F).
Proof.
  refine {|
    vsF_add   := mat_add fld;
    vsF_zero  := mat_zero fld n;
    vsF_neg   := mat_neg fld;
    vsF_scale := mat_scale fld;
  |}.
  all: admit.
Admitted.

Definition gl {F : Type} (fld : Field F) (n : nat) : LieAlgebraF fld (Matrix F).
Proof.
  refine {|
    laF_vs      := gl_vs fld n;
    laF_bracket := mat_bracket fld;
  |}.
  all: admit.
Admitted.

(** ** Matrix units *)

(** e_{ij} : the matrix with 1 at position (i,j) and 0 elsewhere. *)
Definition mat_unit {F : Type} (fld : Field F) (n i j : nat) : Matrix F :=
  List.map (fun r =>
    List.map (fun c =>
      if Nat.eqb r i && Nat.eqb c j then cr_one fld else cr_zero fld)
    (List.seq 0 n))
  (List.seq 0 n).

(** Multiplication of matrix units: e_{ij} * e_{kl} = δ_{jk} * e_{il}. *)
Lemma mat_unit_mul {F : Type} (fld : Field F) (n i j k l : nat) :
    mat_mul fld (mat_unit fld n i j) (mat_unit fld n k l) =
    if Nat.eqb j k then mat_unit fld n i l else mat_zero fld n.
Proof. Admitted.

(** Bracket of matrix units: [e_{ij}, e_{kl}] = δ_{jk}*e_{il} - δ_{li}*e_{kj}. *)
Lemma mat_unit_bracket {F : Type} (fld : Field F) (n i j k l : nat) :
    mat_bracket fld (mat_unit fld n i j) (mat_unit fld n k l) =
    mat_add fld
      (if Nat.eqb j k then mat_unit fld n i l else mat_zero fld n)
      (if Nat.eqb l i then mat_neg fld (mat_unit fld n k j) else mat_zero fld n).
Proof. Admitted.

(** Jacobi identity for the commutator bracket. *)
Lemma mat_bracket_jacobi {F : Type} (fld : Field F) (A B C : Matrix F) :
    mat_add fld
      (mat_add fld
         (mat_bracket fld A (mat_bracket fld B C))
         (mat_bracket fld B (mat_bracket fld C A)))
      (mat_bracket fld C (mat_bracket fld A B))
    = mat_zero fld 0.
Proof. Admitted.
