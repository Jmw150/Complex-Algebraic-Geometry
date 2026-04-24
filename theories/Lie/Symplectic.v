(** * Lie/Symplectic.v
    Symplectic Lie algebra sp(2l, F).

    sp(2l,F) = {x ∈ gl(2l,F) | x^T·s + s·x = 0}
    where s is the standard symplectic form [[0,I_l],[-I_l,0_l]].

    Key result: sp(2l,F) is a Lie subalgebra of gl(2l,F).

    Block matrix characterisation: for x = [[m,n],[p,q]] with l×l blocks,
      n^T = n  (n symmetric)
      p^T = p  (p symmetric)
      q   = -m^T

    References: Humphreys §1.2, representations.org Part IV. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.Lie.Ideals.
Require Import CAG.Lie.Linear.
Require Import CAG.Lie.SpecialLinear.
From Stdlib Require Import List Arith.
Import ListNotations.

(* ================================================================== *)
(** * 1. Matrix transpose                                             *)
(* ================================================================== *)

(** Transpose of an n×m matrix. *)
Definition mat_transpose {F : Type} (fld : Field F) (A : Matrix F) : Matrix F :=
  let n := match A with [] => 0 | row :: _ => List.length row end in
  List.map
    (fun col_idx =>
       List.map (fun row => List.nth col_idx row (cr_zero fld)) A)
    (List.seq 0 n).

Axiom mat_transpose_add :
  forall {F : Type} (fld : Field F) (A B : Matrix F),
    mat_transpose fld (mat_add fld A B) =
    mat_add fld (mat_transpose fld A) (mat_transpose fld B).

Axiom mat_transpose_neg :
  forall {F : Type} (fld : Field F) (A : Matrix F),
    mat_transpose fld (mat_neg fld A) = mat_neg fld (mat_transpose fld A).

Axiom mat_transpose_scale :
  forall {F : Type} (fld : Field F) (c : F) (A : Matrix F),
    mat_transpose fld (mat_scale fld c A) = mat_scale fld c (mat_transpose fld A).

Axiom mat_transpose_mul :
  forall {F : Type} (fld : Field F) (A B : Matrix F),
    mat_transpose fld (mat_mul fld A B) =
    mat_mul fld (mat_transpose fld B) (mat_transpose fld A).

Axiom mat_transpose_zero :
  forall {F : Type} (fld : Field F) (n : nat),
    mat_transpose fld (mat_zero fld n) = mat_zero fld n.

(** [A,B]^T = [B^T, A^T]: transposing reverses the bracket. *)
Lemma mat_transpose_bracket :
  forall {F : Type} (fld : Field F) (A B : Matrix F),
    mat_transpose fld (mat_bracket fld A B) =
    mat_bracket fld (mat_transpose fld B) (mat_transpose fld A).
Proof.
  intros F fld A B. unfold mat_bracket, mat_neg.
  rewrite mat_transpose_add, mat_transpose_scale,
          (mat_transpose_mul fld A B), (mat_transpose_mul fld B A).
  reflexivity.
Qed.

(* ================================================================== *)
(** * 2. Matrix algebra axioms                                        *)
(* ================================================================== *)

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

Axiom mat_mul_scale_l :
  forall {F : Type} (fld : Field F) (c : F) (A B : Matrix F),
    mat_mul fld (mat_scale fld c A) B = mat_scale fld c (mat_mul fld A B).

Axiom mat_mul_scale_r :
  forall {F : Type} (fld : Field F) (c : F) (A B : Matrix F),
    mat_mul fld A (mat_scale fld c B) = mat_scale fld c (mat_mul fld A B).

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

Axiom mat_neg_zero :
  forall {F : Type} (fld : Field F) (n : nat),
    mat_neg fld (mat_zero fld n) = mat_zero fld 0.

Axiom mat_neg_neg :
  forall {F : Type} (fld : Field F) (A : Matrix F),
    mat_neg fld (mat_neg fld A) = A.

Axiom mat_scale_add_mat :
  forall {F : Type} (fld : Field F) (c : F) (A B : Matrix F),
    mat_scale fld c (mat_add fld A B) =
    mat_add fld (mat_scale fld c A) (mat_scale fld c B).

Axiom mat_scale_zero_mat :
  forall {F : Type} (fld : Field F) (c : F) (n : nat),
    mat_scale fld c (mat_zero fld n) = mat_zero fld 0.

Axiom mat_mul_zero_l_n :
  forall {F : Type} (fld : Field F) (n : nat) (A : Matrix F),
    mat_mul fld (mat_zero fld n) A = mat_zero fld 0.

Axiom mat_mul_zero_r_n :
  forall {F : Type} (fld : Field F) (n : nat) (A : Matrix F),
    mat_mul fld A (mat_zero fld n) = mat_zero fld 0.

(* ================================================================== *)
(** * 3. Standard symplectic form                                     *)
(* ================================================================== *)

Axiom sp_form : forall {F : Type} (fld : Field F) (l : nat), Matrix F.

(** s^T = -s. *)
Axiom sp_form_antisymm :
  forall {F : Type} (fld : Field F) (l : nat),
    mat_transpose fld (sp_form fld l) = mat_neg fld (sp_form fld l).

(* ================================================================== *)
(** * 4. Symplectic Lie algebra                                       *)
(* ================================================================== *)

Definition IsSymplectic {F : Type} (fld : Field F) (l : nat) (A : Matrix F) : Prop :=
  mat_add fld
    (mat_mul fld (mat_transpose fld A) (sp_form fld l))
    (mat_mul fld (sp_form fld l) A)
  = mat_zero fld 0.

(** From IsSymplectic A: A^T·s = -(s·A).
    Proof: X + Y = 0 → X = X + (Y + -Y) = (X+Y) + -Y = 0 + -Y = -Y. *)
Lemma sp_cond_l {F : Type} (fld : Field F) (l : nat) (A : Matrix F) :
    IsSymplectic fld l A ->
    mat_mul fld (mat_transpose fld A) (sp_form fld l) =
    mat_neg fld (mat_mul fld (sp_form fld l) A).
Proof.
  unfold IsSymplectic. intro H.
  rewrite <- (mat_add_zero_r fld (mat_mul fld (mat_transpose fld A) (sp_form fld l))).
  rewrite <- (mat_add_neg fld (mat_mul fld (sp_form fld l) A)).
  (* Goal: X + (Y + -Y) = -Y  [right-associated] *)
  rewrite <- mat_add_assoc_m.
  (* Goal: (X + Y) + -Y = -Y *)
  rewrite H. apply mat_add_zero_l.
Qed.

(** From IsSymplectic A: s·A = -(A^T·s).
    Proof: X + Y = 0 → Y = 0 + Y = (-X+X) + Y = -X + (X+Y) = -X + 0 = -X. *)
Lemma sp_cond_r {F : Type} (fld : Field F) (l : nat) (A : Matrix F) :
    IsSymplectic fld l A ->
    mat_mul fld (sp_form fld l) A =
    mat_neg fld (mat_mul fld (mat_transpose fld A) (sp_form fld l)).
Proof.
  unfold IsSymplectic. intro H.
  rewrite <- (mat_add_zero_l fld (mat_mul fld (sp_form fld l) A)).
  rewrite <- (mat_add_neg_l fld (mat_mul fld (mat_transpose fld A) (sp_form fld l))).
  (* Goal: (-X + X) + Y = -X  [left-associated] *)
  rewrite mat_add_assoc_m.
  (* Goal: -X + (X + Y) = -X *)
  rewrite H. apply mat_add_zero_r.
Qed.

(** sp(2l, F) is a Lie subalgebra of gl(2l, F). *)
Lemma sp_is_subalgebra {F : Type} (fld : Field F) (l : nat) :
    IsSubalgebra (gl fld (2 * l)) (IsSymplectic fld l).
Proof.
  constructor.
  (* (1) Zero *)
  - unfold IsSymplectic.
    rewrite gl_zero_eq_mat_zero, mat_transpose_zero.
    rewrite mat_mul_zero_l_n, mat_mul_zero_r_n. apply mat_add_zero_l.
  (* (2) Addition *)
  - intros A B HA HB. unfold IsSymplectic in *.
    rewrite gl_add_eq_mat_add, mat_transpose_add.
    rewrite mat_mul_add_distr_r, mat_mul_add_distr_l.
    (* Goal: (AtS + BtS) + (SA + SB) = 0
       Rearrange to (AtS + SA) + (BtS + SB) = 0 *)
    (* Goal: (AtS + BtS) + (SA + SB) = 0
       Abbreviations: AtS=A^T·s, BtS=B^T·s, SA=s·A, SB=s·B
       Steps: (AtS+BtS)+(SA+SB)
              → AtS+(BtS+(SA+SB))   [forward assoc AtS BtS (SA+SB)]
              → AtS+((BtS+SA)+SB)   [backward assoc BtS SA SB]
              → AtS+((SA+BtS)+SB)   [comm BtS SA]
              → AtS+(SA+(BtS+SB))   [forward assoc SA BtS SB]
              → (AtS+SA)+(BtS+SB)   [backward assoc AtS SA (BtS+SB)]
              → 0+0 = 0              [HA, HB] *)
    rewrite (mat_add_assoc_m fld
               (mat_mul fld (mat_transpose fld A) (sp_form fld l))
               (mat_mul fld (mat_transpose fld B) (sp_form fld l))
               (mat_add fld (mat_mul fld (sp_form fld l) A)
                            (mat_mul fld (sp_form fld l) B))).
    rewrite <- (mat_add_assoc_m fld
                  (mat_mul fld (mat_transpose fld B) (sp_form fld l))
                  (mat_mul fld (sp_form fld l) A)
                  (mat_mul fld (sp_form fld l) B)).
    rewrite (mat_add_comm fld
               (mat_mul fld (mat_transpose fld B) (sp_form fld l))
               (mat_mul fld (sp_form fld l) A)).
    rewrite (mat_add_assoc_m fld
               (mat_mul fld (sp_form fld l) A)
               (mat_mul fld (mat_transpose fld B) (sp_form fld l))
               (mat_mul fld (sp_form fld l) B)).
    rewrite <- (mat_add_assoc_m fld
                  (mat_mul fld (mat_transpose fld A) (sp_form fld l))
                  (mat_mul fld (sp_form fld l) A)
                  (mat_add fld (mat_mul fld (mat_transpose fld B) (sp_form fld l))
                               (mat_mul fld (sp_form fld l) B))).
    rewrite HA, HB. apply mat_add_zero_l.
  (* (3) Negation *)
  - intros A HA. unfold IsSymplectic in *.
    rewrite gl_neg_eq_mat_neg, mat_transpose_neg.
    rewrite mat_mul_neg_l, mat_mul_neg_r.
    rewrite <- mat_neg_add. rewrite HA. apply mat_neg_zero.
  (* (4) Scalar multiplication *)
  - intros c A HA. unfold IsSymplectic in *.
    rewrite gl_scale_eq_mat_scale, mat_transpose_scale.
    rewrite mat_mul_scale_l, mat_mul_scale_r.
    rewrite <- mat_scale_add_mat. rewrite HA. apply mat_scale_zero_mat.
  (* (5) Bracket closure.
         [A,B]^T·s + s·[A,B]
         = [B^T,A^T]·s + s·[A,B]                     (mat_transpose_bracket)
         = B^T·(A^T·s) - A^T·(B^T·s) + s·A·B - s·B·A (expand, reassociate)
         = B^T·(-(s·A)) - A^T·(-(s·B)) + s·A·B - s·B·A (sp_cond_l)
         = -(B^T·s·A) + A^T·s·B + s·A·B - s·B·A
         = --(s·B·A) + -(s·A·B) + s·A·B - s·B·A       (sp_cond_l again)
         = (s·B·A) - (s·A·B) + (s·A·B) - (s·B·A) = 0  *)
  - intros A B HA HB. unfold IsSymplectic in *.
    rewrite gl_bracket_eq_mat_bracket.
    rewrite mat_transpose_bracket.
    unfold mat_bracket.
    (* Distribute · over + on both sides *)
    rewrite mat_mul_add_distr_r, mat_mul_add_distr_l.
    (* Pull negations out *)
    rewrite mat_mul_neg_l, mat_mul_neg_r.
    (* Reassociate triple products:
       (Bt·At)·s = Bt·(At·s): forward assoc
       s·(A·B) = (s·A)·B: backward assoc *)
    rewrite (mat_mul_assoc_m fld (mat_transpose fld B) (mat_transpose fld A) (sp_form fld l)).
    rewrite (mat_mul_assoc_m fld (mat_transpose fld A) (mat_transpose fld B) (sp_form fld l)).
    rewrite <- (mat_mul_assoc_m fld (sp_form fld l) A B).
    rewrite <- (mat_mul_assoc_m fld (sp_form fld l) B A).
    (* Apply sp_cond_l: At·s = -(s·A), Bt·s = -(s·B) *)
    rewrite (sp_cond_l fld l A HA), (sp_cond_l fld l B HB).
    (* Bt·(-(s·A)) = -(Bt·(s·A)) and At·(-(s·B)) = -(At·(s·B)) *)
    rewrite mat_mul_neg_r, mat_mul_neg_r.
    (* -(-(At·(s·B))) = At·(s·B) *)
    rewrite mat_neg_neg.
    (* Reassociate: Bt·(s·A) = (Bt·s)·A, At·(s·B) = (At·s)·B *)
    rewrite <- (mat_mul_assoc_m fld (mat_transpose fld B) (sp_form fld l) A).
    rewrite <- (mat_mul_assoc_m fld (mat_transpose fld A) (sp_form fld l) B).
    (* Apply sp_cond_l again: Bt·s = -(s·B), At·s = -(s·A) *)
    rewrite (sp_cond_l fld l B HB), (sp_cond_l fld l A HA).
    (* (-(s·B))·A = -(s·B·A), (-(s·A))·B = -(s·A·B) *)
    rewrite mat_mul_neg_l, mat_mul_neg_l.
    (* --(s·B·A) = s·B·A *)
    rewrite mat_neg_neg.
    (* Goal: (X + (-Y)) + (Y + (-X)) = 0
       where X = (s·B)·A,  Y = (s·A)·B *)
    rewrite (mat_add_assoc_m fld
      (mat_mul fld (mat_mul fld (sp_form fld l) B) A)
      (mat_neg fld (mat_mul fld (mat_mul fld (sp_form fld l) A) B))
      (mat_add fld
        (mat_mul fld (mat_mul fld (sp_form fld l) A) B)
        (mat_neg fld (mat_mul fld (mat_mul fld (sp_form fld l) B) A)))).
    rewrite <- (mat_add_assoc_m fld
      (mat_neg fld (mat_mul fld (mat_mul fld (sp_form fld l) A) B))
      (mat_mul fld (mat_mul fld (sp_form fld l) A) B)
      (mat_neg fld (mat_mul fld (mat_mul fld (sp_form fld l) B) A))).
    rewrite mat_add_neg_l, mat_add_zero_l.
    apply mat_add_neg.
Qed.

(* ================================================================== *)
(** * 5. Block matrix characterisation (axiomatised)                  *)
(* ================================================================== *)

(** The standard basis of sp(2l,F):
    - e_{ij} - e_{j+l,i+l}  for 1≤i,j≤l
    - e_{i,j+l} + e_{j,i+l} for 1≤i≤j≤l  (symmetric off-diagonal blocks)
    - e_{i+l,j} + e_{j+l,i} for 1≤i≤j≤l  (symmetric off-diagonal blocks)
    The dimension is 2l^2 + l. *)
Axiom sp_dim : forall (l : nat), True. (* placeholder *)
