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

(* CAG zero-dependent Axiom mat_mul_add_distr_r theories/Lie/Linear.v:49 BEGIN
Axiom mat_mul_add_distr_r :
  forall {F : Type} (fld : Field F) (A B C : Matrix F),
    mat_mul fld (mat_add fld A B) C =
    mat_add fld (mat_mul fld A C) (mat_mul fld B C).
   CAG zero-dependent Axiom mat_mul_add_distr_r theories/Lie/Linear.v:49 END *)

(* CAG zero-dependent Axiom mat_mul_add_distr_l theories/Lie/Linear.v:54 BEGIN
Axiom mat_mul_add_distr_l :
  forall {F : Type} (fld : Field F) (A B C : Matrix F),
    mat_mul fld A (mat_add fld B C) =
    mat_add fld (mat_mul fld A B) (mat_mul fld A C).
   CAG zero-dependent Axiom mat_mul_add_distr_l theories/Lie/Linear.v:54 END *)

(* CAG zero-dependent Axiom mat_mul_assoc_m theories/Lie/Linear.v:59 BEGIN
Axiom mat_mul_assoc_m :
  forall {F : Type} (fld : Field F) (A B C : Matrix F),
    mat_mul fld (mat_mul fld A B) C =
    mat_mul fld A (mat_mul fld B C).
   CAG zero-dependent Axiom mat_mul_assoc_m theories/Lie/Linear.v:59 END *)

(* CAG zero-dependent Axiom mat_mul_neg_l theories/Lie/Linear.v:64 BEGIN
Axiom mat_mul_neg_l :
  forall {F : Type} (fld : Field F) (A B : Matrix F),
    mat_mul fld (mat_neg fld A) B = mat_neg fld (mat_mul fld A B).
   CAG zero-dependent Axiom mat_mul_neg_l theories/Lie/Linear.v:64 END *)

(* CAG zero-dependent Axiom mat_mul_neg_r theories/Lie/Linear.v:68 BEGIN
Axiom mat_mul_neg_r :
  forall {F : Type} (fld : Field F) (A B : Matrix F),
    mat_mul fld A (mat_neg fld B) = mat_neg fld (mat_mul fld A B).
   CAG zero-dependent Axiom mat_mul_neg_r theories/Lie/Linear.v:68 END *)

(* CAG zero-dependent Axiom mat_add_comm theories/Lie/Linear.v:72 BEGIN
Axiom mat_add_comm :
  forall {F : Type} (fld : Field F) (A B : Matrix F),
    mat_add fld A B = mat_add fld B A.
   CAG zero-dependent Axiom mat_add_comm theories/Lie/Linear.v:72 END *)

(* CAG zero-dependent Axiom mat_add_assoc_m theories/Lie/Linear.v:76 BEGIN
Axiom mat_add_assoc_m :
  forall {F : Type} (fld : Field F) (A B C : Matrix F),
    mat_add fld (mat_add fld A B) C =
    mat_add fld A (mat_add fld B C).
   CAG zero-dependent Axiom mat_add_assoc_m theories/Lie/Linear.v:76 END *)

(* CAG zero-dependent Axiom mat_add_neg theories/Lie/Linear.v:81 BEGIN
Axiom mat_add_neg :
  forall {F : Type} (fld : Field F) (A : Matrix F),
    mat_add fld A (mat_neg fld A) = mat_zero fld 0.
   CAG zero-dependent Axiom mat_add_neg theories/Lie/Linear.v:81 END *)

(* CAG zero-dependent Axiom mat_add_neg_l theories/Lie/Linear.v:85 BEGIN
Axiom mat_add_neg_l :
  forall {F : Type} (fld : Field F) (A : Matrix F),
    mat_add fld (mat_neg fld A) A = mat_zero fld 0.
   CAG zero-dependent Axiom mat_add_neg_l theories/Lie/Linear.v:85 END *)

(* CAG zero-dependent Axiom mat_add_zero_r theories/Lie/Linear.v:89 BEGIN
Axiom mat_add_zero_r :
  forall {F : Type} (fld : Field F) (A : Matrix F),
    mat_add fld A (mat_zero fld 0) = A.
   CAG zero-dependent Axiom mat_add_zero_r theories/Lie/Linear.v:89 END *)

(* CAG zero-dependent Axiom mat_add_zero_l theories/Lie/Linear.v:93 BEGIN
Axiom mat_add_zero_l :
  forall {F : Type} (fld : Field F) (A : Matrix F),
    mat_add fld (mat_zero fld 0) A = A.
   CAG zero-dependent Axiom mat_add_zero_l theories/Lie/Linear.v:93 END *)

(* CAG zero-dependent Axiom mat_neg_add theories/Lie/Linear.v:97 BEGIN
Axiom mat_neg_add :
  forall {F : Type} (fld : Field F) (A B : Matrix F),
    mat_neg fld (mat_add fld A B) =
    mat_add fld (mat_neg fld A) (mat_neg fld B).
   CAG zero-dependent Axiom mat_neg_add theories/Lie/Linear.v:97 END *)

(* CAG zero-dependent Axiom mat_neg_neg theories/Lie/Linear.v:102 BEGIN
Axiom mat_neg_neg :
  forall {F : Type} (fld : Field F) (A : Matrix F),
    mat_neg fld (mat_neg fld A) = A.
   CAG zero-dependent Axiom mat_neg_neg theories/Lie/Linear.v:102 END *)

(** ** Matrix scale axioms *)

(* CAG zero-dependent Axiom mat_scale_one theories/Lie/Linear.v:108 BEGIN
Axiom mat_scale_one :
  forall {F : Type} (fld : Field F) (A : Matrix F),
    mat_scale fld (cr_one fld) A = A.
   CAG zero-dependent Axiom mat_scale_one theories/Lie/Linear.v:108 END *)

(* CAG zero-dependent Axiom mat_scale_mul_assoc theories/Lie/Linear.v:112 BEGIN
Axiom mat_scale_mul_assoc :
  forall {F : Type} (fld : Field F) (a b : F) (A : Matrix F),
    mat_scale fld a (mat_scale fld b A) = mat_scale fld (cr_mul fld a b) A.
   CAG zero-dependent Axiom mat_scale_mul_assoc theories/Lie/Linear.v:112 END *)

(* CAG zero-dependent Axiom mat_scale_add_mat theories/Lie/Linear.v:116 BEGIN
Axiom mat_scale_add_mat :
  forall {F : Type} (fld : Field F) (a : F) (A B : Matrix F),
    mat_scale fld a (mat_add fld A B) =
    mat_add fld (mat_scale fld a A) (mat_scale fld a B).
   CAG zero-dependent Axiom mat_scale_add_mat theories/Lie/Linear.v:116 END *)

(* CAG zero-dependent Axiom mat_scale_add_scalar theories/Lie/Linear.v:121 BEGIN
Axiom mat_scale_add_scalar :
  forall {F : Type} (fld : Field F) (a b : F) (A : Matrix F),
    mat_scale fld (cr_add fld a b) A =
    mat_add fld (mat_scale fld a A) (mat_scale fld b A).
   CAG zero-dependent Axiom mat_scale_add_scalar theories/Lie/Linear.v:121 END *)

(* CAG zero-dependent Axiom mat_scale_zero_mat theories/Lie/Linear.v:126 BEGIN
Axiom mat_scale_zero_mat :
  forall {F : Type} (fld : Field F) (c : F),
    mat_scale fld c (mat_zero fld 0) = mat_zero fld 0.
   CAG zero-dependent Axiom mat_scale_zero_mat theories/Lie/Linear.v:126 END *)


(* CAG zero-dependent Axiom mat_neg_zero theories/Lie/Linear.v:131 BEGIN
Axiom mat_neg_zero :
  forall {F : Type} (fld : Field F),
    mat_neg fld (mat_zero fld 0) = mat_zero fld 0.
   CAG zero-dependent Axiom mat_neg_zero theories/Lie/Linear.v:131 END *)


(** All zero matrices are abstractly equal (dimension is erased in the list representation). *)
(* CAG zero-dependent Axiom mat_zero_any theories/Lie/Linear.v:141 BEGIN
Axiom mat_zero_any :
  forall {F : Type} (fld : Field F) (m n : nat),
    mat_zero fld m = mat_zero fld n.
   CAG zero-dependent Axiom mat_zero_any theories/Lie/Linear.v:141 END *)

(** ** Matrix-scale interaction with multiplication *)

(* CAG zero-dependent Axiom mat_mul_scale_l theories/Lie/Linear.v:147 BEGIN
Axiom mat_mul_scale_l :
  forall {F : Type} (fld : Field F) (c : F) (A B : Matrix F),
    mat_mul fld (mat_scale fld c A) B = mat_scale fld c (mat_mul fld A B).
   CAG zero-dependent Axiom mat_mul_scale_l theories/Lie/Linear.v:147 END *)

(* CAG zero-dependent Axiom mat_mul_scale_r theories/Lie/Linear.v:151 BEGIN
Axiom mat_mul_scale_r :
  forall {F : Type} (fld : Field F) (c : F) (A B : Matrix F),
    mat_mul fld A (mat_scale fld c B) = mat_scale fld c (mat_mul fld A B).
   CAG zero-dependent Axiom mat_mul_scale_r theories/Lie/Linear.v:151 END *)

(** mat_neg distributes over mat_scale (provable from definitions). *)
(* CAG zero-dependent Lemma mat_neg_scale theories/Lie/Linear.v:156 BEGIN
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
   CAG zero-dependent Lemma mat_neg_scale theories/Lie/Linear.v:156 END *)

(** ** gl(n, F) as a Lie algebra *)

(** ** Bracket linearity lemmas (proved from axioms) *)

(* CAG zero-dependent Lemma mat_bracket_add_l theories/Lie/Linear.v:171 BEGIN
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
   CAG zero-dependent Lemma mat_bracket_add_l theories/Lie/Linear.v:171 END *)

(* CAG zero-dependent Lemma mat_bracket_add_r theories/Lie/Linear.v:197 BEGIN
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
   CAG zero-dependent Lemma mat_bracket_add_r theories/Lie/Linear.v:197 END *)

(* CAG zero-dependent Lemma mat_bracket_scale_l theories/Lie/Linear.v:223 BEGIN
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
   CAG zero-dependent Lemma mat_bracket_scale_l theories/Lie/Linear.v:223 END *)

(* CAG zero-dependent Lemma mat_bracket_scale_r theories/Lie/Linear.v:235 BEGIN
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
   CAG zero-dependent Lemma mat_bracket_scale_r theories/Lie/Linear.v:235 END *)

(* CAG zero-dependent Lemma mat_bracket_alt theories/Lie/Linear.v:247 BEGIN
Lemma mat_bracket_alt {F : Type} (fld : Field F) (A : Matrix F) :
    mat_bracket fld A A = mat_zero fld 0.
Proof.
  unfold mat_bracket. exact (mat_add_neg fld (mat_mul fld A A)).
Qed.
   CAG zero-dependent Lemma mat_bracket_alt theories/Lie/Linear.v:247 END *)

(** ** Matrix units *)

(** e_{ij} : the matrix with 1 at position (i,j) and 0 elsewhere. *)
Definition mat_unit {F : Type} (fld : Field F) (n i j : nat) : Matrix F :=
  List.map (fun r =>
    List.map (fun c =>
      if Nat.eqb r i && Nat.eqb c j then cr_one fld else cr_zero fld)
    (List.seq 0 n))
  (List.seq 0 n).

(** Multiplication of matrix units: e_{ij} * e_{kl} = δ_{jk} * e_{il}. *)
(* CAG zero-dependent Admitted mat_unit_mul theories/Lie/Linear.v:261 BEGIN
Lemma mat_unit_mul {F : Type} (fld : Field F) (n i j k l : nat) :
    mat_mul fld (mat_unit fld n i j) (mat_unit fld n k l) =
    if Nat.eqb j k then mat_unit fld n i l else mat_zero fld n.
Proof. Admitted.
   CAG zero-dependent Admitted mat_unit_mul theories/Lie/Linear.v:261 END *)

(** Bracket of matrix units: [e_{ij}, e_{kl}] = δ_{jk}*e_{il} - δ_{li}*e_{kj}. *)
(* CAG zero-dependent Admitted mat_unit_bracket theories/Lie/Linear.v:277 BEGIN
Lemma mat_unit_bracket {F : Type} (fld : Field F) (n i j k l : nat) :
    mat_bracket fld (mat_unit fld n i j) (mat_unit fld n k l) =
    mat_add fld
      (if Nat.eqb j k then mat_unit fld n i l else mat_zero fld n)
      (if Nat.eqb l i then mat_neg fld (mat_unit fld n k j) else mat_zero fld n).
Proof. Admitted.
   CAG zero-dependent Admitted mat_unit_bracket theories/Lie/Linear.v:277 END *)

(** Jacobi identity for the commutator bracket. *)
(* CAG zero-dependent Lemma mat_bracket_jacobi theories/Lie/Linear.v:282 BEGIN
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
   CAG zero-dependent Lemma mat_bracket_jacobi theories/Lie/Linear.v:282 END *)

(** ** gl(n, F) as a Lie algebra *)

(** The gl(n,F) vector space on n×n matrices.
    We use mat_zero fld 0 (the empty matrix) as the abstract zero,
    consistent with the axioms mat_add_zero_r, mat_add_neg, etc. *)
(* CAG zero-dependent Definition gl_vs theories/Lie/Linear.v:402 BEGIN
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
   CAG zero-dependent Definition gl_vs theories/Lie/Linear.v:402 END *)

(* CAG zero-dependent Definition gl theories/Lie/Linear.v:418 BEGIN
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
   CAG zero-dependent Definition gl theories/Lie/Linear.v:418 END *)
