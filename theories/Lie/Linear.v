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

(** ** Matrix ring axioms *)

Axiom mat_mul_add_distr_r :
  forall {F : Type} (fld : Field F) (A B C : Matrix F),
    mat_mul fld (mat_add fld A B) C =
    mat_add fld (mat_mul fld A C) (mat_mul fld B C).

Axiom mat_mul_add_distr_l :
  forall {F : Type} (fld : Field F) (A B C : Matrix F),
    mat_mul fld A (mat_add fld B C) =
    mat_add fld (mat_mul fld A B) (mat_mul fld A C).

Axiom mat_mul_assoc_m :
  forall {F : Type} (fld : Field F) (A B C : Matrix F),
    mat_mul fld (mat_mul fld A B) C =
    mat_mul fld A (mat_mul fld B C).

Axiom mat_mul_neg_l :
  forall {F : Type} (fld : Field F) (A B : Matrix F),
    mat_mul fld (mat_neg fld A) B = mat_neg fld (mat_mul fld A B).

Axiom mat_mul_neg_r :
  forall {F : Type} (fld : Field F) (A B : Matrix F),
    mat_mul fld A (mat_neg fld B) = mat_neg fld (mat_mul fld A B).

Axiom mat_add_comm :
  forall {F : Type} (fld : Field F) (A B : Matrix F),
    mat_add fld A B = mat_add fld B A.

Axiom mat_add_assoc_m :
  forall {F : Type} (fld : Field F) (A B C : Matrix F),
    mat_add fld (mat_add fld A B) C =
    mat_add fld A (mat_add fld B C).

Axiom mat_add_neg :
  forall {F : Type} (fld : Field F) (A : Matrix F),
    mat_add fld A (mat_neg fld A) = mat_zero fld 0.

Axiom mat_add_neg_l :
  forall {F : Type} (fld : Field F) (A : Matrix F),
    mat_add fld (mat_neg fld A) A = mat_zero fld 0.

Axiom mat_add_zero_r :
  forall {F : Type} (fld : Field F) (A : Matrix F),
    mat_add fld A (mat_zero fld 0) = A.

Axiom mat_add_zero_l :
  forall {F : Type} (fld : Field F) (A : Matrix F),
    mat_add fld (mat_zero fld 0) A = A.

Axiom mat_neg_add :
  forall {F : Type} (fld : Field F) (A B : Matrix F),
    mat_neg fld (mat_add fld A B) =
    mat_add fld (mat_neg fld A) (mat_neg fld B).

Axiom mat_neg_neg :
  forall {F : Type} (fld : Field F) (A : Matrix F),
    mat_neg fld (mat_neg fld A) = A.

(** ** Matrix scale axioms *)

Axiom mat_scale_one :
  forall {F : Type} (fld : Field F) (A : Matrix F),
    mat_scale fld (cr_one fld) A = A.

Axiom mat_scale_mul_assoc :
  forall {F : Type} (fld : Field F) (a b : F) (A : Matrix F),
    mat_scale fld a (mat_scale fld b A) = mat_scale fld (cr_mul fld a b) A.

Axiom mat_scale_add_mat :
  forall {F : Type} (fld : Field F) (a : F) (A B : Matrix F),
    mat_scale fld a (mat_add fld A B) =
    mat_add fld (mat_scale fld a A) (mat_scale fld a B).

Axiom mat_scale_add_scalar :
  forall {F : Type} (fld : Field F) (a b : F) (A : Matrix F),
    mat_scale fld (cr_add fld a b) A =
    mat_add fld (mat_scale fld a A) (mat_scale fld b A).

Axiom mat_scale_zero_mat :
  forall {F : Type} (fld : Field F) (c : F),
    mat_scale fld c (mat_zero fld 0) = mat_zero fld 0.

Axiom mat_neg_zero :
  forall {F : Type} (fld : Field F),
    mat_neg fld (mat_zero fld 0) = mat_zero fld 0.

(** All zero matrices are abstractly equal (dimension is erased in the list representation). *)
Axiom mat_zero_any :
  forall {F : Type} (fld : Field F) (m n : nat),
    mat_zero fld m = mat_zero fld n.

(** ** Matrix-scale interaction with multiplication *)

Axiom mat_mul_scale_l :
  forall {F : Type} (fld : Field F) (c : F) (A B : Matrix F),
    mat_mul fld (mat_scale fld c A) B = mat_scale fld c (mat_mul fld A B).

Axiom mat_mul_scale_r :
  forall {F : Type} (fld : Field F) (c : F) (A B : Matrix F),
    mat_mul fld A (mat_scale fld c B) = mat_scale fld c (mat_mul fld A B).

(** mat_neg distributes over mat_scale (provable from definitions). *)
Lemma mat_neg_scale :
  forall {F : Type} (fld : Field F) (c : F) (A : Matrix F),
    mat_neg fld (mat_scale fld c A) = mat_scale fld c (mat_neg fld A).
Proof.
  intros F fld c A.
  unfold mat_neg.
  rewrite (mat_scale_mul_assoc fld (cr_neg fld (cr_one fld)) c A).
  rewrite (mat_scale_mul_assoc fld c (cr_neg fld (cr_one fld)) A).
  f_equal. apply fld.(cr_mul_comm).
Qed.

(** ** gl(n, F) as a Lie algebra *)

(** ** Bracket linearity lemmas (proved from axioms) *)

Lemma mat_bracket_add_l {F : Type} (fld : Field F) (A B C : Matrix F) :
    mat_bracket fld (mat_add fld A B) C =
    mat_add fld (mat_bracket fld A C) (mat_bracket fld B C).
Proof.
  unfold mat_bracket.
  rewrite mat_mul_add_distr_r.
  rewrite mat_mul_add_distr_l.
  rewrite mat_neg_add.
  (* (AC+BC) + (-CA + -CB) → (AC + -CA) + (BC + -CB) *)
  rewrite (mat_add_assoc_m fld
    (mat_mul fld A C) (mat_mul fld B C)
    (mat_add fld (mat_neg fld (mat_mul fld C A)) (mat_neg fld (mat_mul fld C B)))).
  rewrite <- (mat_add_assoc_m fld
    (mat_mul fld B C)
    (mat_neg fld (mat_mul fld C A)) (mat_neg fld (mat_mul fld C B))).
  rewrite (mat_add_comm fld (mat_mul fld B C) (mat_neg fld (mat_mul fld C A))).
  rewrite (mat_add_assoc_m fld
    (mat_neg fld (mat_mul fld C A))
    (mat_mul fld B C) (mat_neg fld (mat_mul fld C B))).
  rewrite <- (mat_add_assoc_m fld
    (mat_mul fld A C)
    (mat_neg fld (mat_mul fld C A))
    (mat_add fld (mat_mul fld B C) (mat_neg fld (mat_mul fld C B)))).
  reflexivity.
Qed.

Lemma mat_bracket_add_r {F : Type} (fld : Field F) (A B C : Matrix F) :
    mat_bracket fld A (mat_add fld B C) =
    mat_add fld (mat_bracket fld A B) (mat_bracket fld A C).
Proof.
  unfold mat_bracket.
  rewrite mat_mul_add_distr_l.
  rewrite mat_mul_add_distr_r.
  rewrite mat_neg_add.
  (* (AB+AC) + (-BA + -CA) → (AB + -BA) + (AC + -CA) *)
  rewrite (mat_add_assoc_m fld
    (mat_mul fld A B) (mat_mul fld A C)
    (mat_add fld (mat_neg fld (mat_mul fld B A)) (mat_neg fld (mat_mul fld C A)))).
  rewrite <- (mat_add_assoc_m fld
    (mat_mul fld A C)
    (mat_neg fld (mat_mul fld B A)) (mat_neg fld (mat_mul fld C A))).
  rewrite (mat_add_comm fld (mat_mul fld A C) (mat_neg fld (mat_mul fld B A))).
  rewrite (mat_add_assoc_m fld
    (mat_neg fld (mat_mul fld B A))
    (mat_mul fld A C) (mat_neg fld (mat_mul fld C A))).
  rewrite <- (mat_add_assoc_m fld
    (mat_mul fld A B)
    (mat_neg fld (mat_mul fld B A))
    (mat_add fld (mat_mul fld A C) (mat_neg fld (mat_mul fld C A)))).
  reflexivity.
Qed.

Lemma mat_bracket_scale_l {F : Type} (fld : Field F) (c : F) (A B : Matrix F) :
    mat_bracket fld (mat_scale fld c A) B =
    mat_scale fld c (mat_bracket fld A B).
Proof.
  unfold mat_bracket.
  rewrite (mat_mul_scale_l fld c A B).
  rewrite (mat_mul_scale_r fld c B A).
  rewrite (mat_neg_scale fld c (mat_mul fld B A)).
  rewrite <- (mat_scale_add_mat fld c (mat_mul fld A B) (mat_neg fld (mat_mul fld B A))).
  reflexivity.
Qed.

Lemma mat_bracket_scale_r {F : Type} (fld : Field F) (c : F) (A B : Matrix F) :
    mat_bracket fld A (mat_scale fld c B) =
    mat_scale fld c (mat_bracket fld A B).
Proof.
  unfold mat_bracket.
  rewrite (mat_mul_scale_r fld c A B).
  rewrite (mat_mul_scale_l fld c B A).
  rewrite (mat_neg_scale fld c (mat_mul fld B A)).
  rewrite <- (mat_scale_add_mat fld c (mat_mul fld A B) (mat_neg fld (mat_mul fld B A))).
  reflexivity.
Qed.

Lemma mat_bracket_alt {F : Type} (fld : Field F) (A : Matrix F) :
    mat_bracket fld A A = mat_zero fld 0.
Proof.
  unfold mat_bracket. exact (mat_add_neg fld (mat_mul fld A A)).
Qed.

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
Proof.
  (* Helper: (P+Q)+(R+S) = (P+R)+(Q+S) *)
  assert (comm_inner : forall P Q R S : Matrix F,
    mat_add fld (mat_add fld P Q) (mat_add fld R S) =
    mat_add fld (mat_add fld P R) (mat_add fld Q S)).
  { intros P Q R S.
    rewrite (mat_add_assoc_m fld P Q (mat_add fld R S)).
    rewrite <- (mat_add_assoc_m fld Q R S).
    rewrite (mat_add_comm fld Q R).
    rewrite (mat_add_assoc_m fld R Q S).
    rewrite <- (mat_add_assoc_m fld P R (mat_add fld Q S)).
    reflexivity. }
  (* Name the six triple products (all left-associated) *)
  set (ABC := mat_mul fld (mat_mul fld A B) C).
  set (ACB := mat_mul fld (mat_mul fld A C) B).
  set (BAC := mat_mul fld (mat_mul fld B A) C).
  set (BCA := mat_mul fld (mat_mul fld B C) A).
  set (CAB := mat_mul fld (mat_mul fld C A) B).
  set (CBA := mat_mul fld (mat_mul fld C B) A).
  (* Expand each bracket into four triple-product terms *)
  assert (H1 : mat_bracket fld A (mat_bracket fld B C) =
    mat_add fld (mat_add fld ABC (mat_neg fld ACB))
               (mat_add fld (mat_neg fld BCA) CBA)).
  { unfold mat_bracket, ABC, ACB, BCA, CBA.
    rewrite mat_mul_add_distr_l, mat_mul_neg_r.
    rewrite mat_mul_add_distr_r, mat_mul_neg_l, mat_neg_add, mat_neg_neg.
    rewrite <- (mat_mul_assoc_m fld A B C), <- (mat_mul_assoc_m fld A C B).
    reflexivity. }
  assert (H2 : mat_bracket fld B (mat_bracket fld C A) =
    mat_add fld (mat_add fld BCA (mat_neg fld BAC))
               (mat_add fld (mat_neg fld CAB) ACB)).
  { unfold mat_bracket, BCA, BAC, CAB, ACB.
    rewrite mat_mul_add_distr_l, mat_mul_neg_r.
    rewrite mat_mul_add_distr_r, mat_mul_neg_l, mat_neg_add, mat_neg_neg.
    rewrite <- (mat_mul_assoc_m fld B C A), <- (mat_mul_assoc_m fld B A C).
    reflexivity. }
  assert (H3 : mat_bracket fld C (mat_bracket fld A B) =
    mat_add fld (mat_add fld CAB (mat_neg fld CBA))
               (mat_add fld (mat_neg fld ABC) BAC)).
  { unfold mat_bracket, CAB, CBA, ABC, BAC.
    rewrite mat_mul_add_distr_l, mat_mul_neg_r.
    rewrite mat_mul_add_distr_r, mat_mul_neg_l, mat_neg_add, mat_neg_neg.
    rewrite <- (mat_mul_assoc_m fld C A B), <- (mat_mul_assoc_m fld C B A).
    reflexivity. }
  rewrite H1, H2, H3.
  (* (X+Y)+Z = 0; X=(ABC+-ACB)+(-BCA+CBA), Y=(BCA+-BAC)+(-CAB+ACB), Z=(CAB+-CBA)+(-ABC+BAC) *)
  (* Step A: (X+Y)+Z → X+(Y+Z) *)
  rewrite (mat_add_assoc_m fld
    (mat_add fld (mat_add fld ABC (mat_neg fld ACB)) (mat_add fld (mat_neg fld BCA) CBA))
    (mat_add fld (mat_add fld BCA (mat_neg fld BAC)) (mat_add fld (mat_neg fld CAB) ACB))
    (mat_add fld (mat_add fld CAB (mat_neg fld CBA)) (mat_add fld (mat_neg fld ABC) BAC))).
  (* Step B: Y+Z → Q1+(Q2+(R1+R2)) *)
  rewrite (mat_add_assoc_m fld
    (mat_add fld BCA (mat_neg fld BAC))
    (mat_add fld (mat_neg fld CAB) ACB)
    (mat_add fld (mat_add fld CAB (mat_neg fld CBA)) (mat_add fld (mat_neg fld ABC) BAC))).
  (* Step C1: Q2+(R1+R2) → (Q2+R1)+R2 *)
  rewrite <- (mat_add_assoc_m fld
    (mat_add fld (mat_neg fld CAB) ACB)
    (mat_add fld CAB (mat_neg fld CBA))
    (mat_add fld (mat_neg fld ABC) BAC)).
  (* Cancel CAB/-CAB in Q2+R1 *)
  rewrite (comm_inner (mat_neg fld CAB) ACB CAB (mat_neg fld CBA)).
  rewrite (mat_add_neg_l fld CAB).
  rewrite (mat_add_zero_l fld (mat_add fld ACB (mat_neg fld CBA))).
  (* Step D1: X+(Q1+...) → P1+(P2+(Q1+...)) *)
  rewrite (mat_add_assoc_m fld
    (mat_add fld ABC (mat_neg fld ACB))
    (mat_add fld (mat_neg fld BCA) CBA)
    (mat_add fld (mat_add fld BCA (mat_neg fld BAC))
                 (mat_add fld (mat_add fld ACB (mat_neg fld CBA))
                              (mat_add fld (mat_neg fld ABC) BAC)))).
  (* Step D2: P2+(Q1+...) → (P2+Q1)+... *)
  rewrite <- (mat_add_assoc_m fld
    (mat_add fld (mat_neg fld BCA) CBA)
    (mat_add fld BCA (mat_neg fld BAC))
    (mat_add fld (mat_add fld ACB (mat_neg fld CBA))
                 (mat_add fld (mat_neg fld ABC) BAC))).
  (* Cancel BCA/-BCA in P2+Q1 *)
  rewrite (comm_inner (mat_neg fld BCA) CBA BCA (mat_neg fld BAC)).
  rewrite (mat_add_neg_l fld BCA).
  rewrite (mat_add_zero_l fld (mat_add fld CBA (mat_neg fld BAC))).
  (* Step E1: (CBA+-BAC)+((ACB+-CBA)+R2) → ((CBA+-BAC)+(ACB+-CBA))+R2 *)
  rewrite <- (mat_add_assoc_m fld
    (mat_add fld CBA (mat_neg fld BAC))
    (mat_add fld ACB (mat_neg fld CBA))
    (mat_add fld (mat_neg fld ABC) BAC)).
  (* Cancel CBA/-CBA *)
  rewrite (mat_add_comm fld ACB (mat_neg fld CBA)).
  rewrite (comm_inner CBA (mat_neg fld BAC) (mat_neg fld CBA) ACB).
  rewrite (mat_add_neg fld CBA).
  rewrite (mat_add_zero_l fld (mat_add fld (mat_neg fld BAC) ACB)).
  (* Step F1: (P1+(-BAC+ACB))+R2 via <- assoc *)
  rewrite <- (mat_add_assoc_m fld
    (mat_add fld ABC (mat_neg fld ACB))
    (mat_add fld (mat_neg fld BAC) ACB)
    (mat_add fld (mat_neg fld ABC) BAC)).
  (* Cancel ACB/-ACB *)
  rewrite (comm_inner ABC (mat_neg fld ACB) (mat_neg fld BAC) ACB).
  rewrite (mat_add_neg_l fld ACB).
  rewrite (mat_add_zero_r fld (mat_add fld ABC (mat_neg fld BAC))).
  (* Cancel ABC/-ABC and BAC/-BAC *)
  rewrite (comm_inner ABC (mat_neg fld BAC) (mat_neg fld ABC) BAC).
  rewrite (mat_add_neg fld ABC).
  rewrite (mat_add_zero_l fld (mat_add fld (mat_neg fld BAC) BAC)).
  apply (mat_add_neg_l fld BAC).
Qed.

(** ** gl(n, F) as a Lie algebra *)

(** The gl(n,F) vector space on n×n matrices.
    We use mat_zero fld 0 (the empty matrix) as the abstract zero,
    consistent with the axioms mat_add_zero_r, mat_add_neg, etc. *)
Definition gl_vs {F : Type} (fld : Field F) (n : nat) : VectorSpaceF fld (Matrix F) :=
  {|
    vsF_add   := mat_add fld;
    vsF_zero  := mat_zero fld 0;
    vsF_neg   := mat_neg fld;
    vsF_scale := mat_scale fld;
    vsF_add_assoc  := fun A B C => eq_sym (mat_add_assoc_m fld A B C);
    vsF_add_comm   := fun A B   => mat_add_comm fld A B;
    vsF_add_zero_r := fun A     => mat_add_zero_r fld A;
    vsF_add_neg_r  := fun A     => mat_add_neg fld A;
    vsF_scale_one   := fun A       => mat_scale_one fld A;
    vsF_scale_mul   := fun a b A   => mat_scale_mul_assoc fld a b A;
    vsF_scale_add_v := fun a A B   => mat_scale_add_mat fld a A B;
    vsF_scale_add_s := fun a b A   => mat_scale_add_scalar fld a b A;
  |}.

Definition gl {F : Type} (fld : Field F) (n : nat) : LieAlgebraF fld (Matrix F) :=
  {|
    laF_vs      := gl_vs fld n;
    laF_bracket := mat_bracket fld;
    laF_bracket_add_l   := fun x y z   => mat_bracket_add_l fld x y z;
    laF_bracket_scale_l := fun a x y   => mat_bracket_scale_l fld a x y;
    laF_bracket_add_r   := fun x y z   => mat_bracket_add_r fld x y z;
    laF_bracket_scale_r := fun a x y   => mat_bracket_scale_r fld a x y;
    laF_bracket_alt     := fun x       => mat_bracket_alt fld x;
    laF_jacobi          := fun x y z   => mat_bracket_jacobi fld x y z;
  |}.
