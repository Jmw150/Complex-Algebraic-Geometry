(** * Lie/Orthogonal.v
    Orthogonal Lie algebras B_l and D_l.

    o(V, f) = {x ∈ gl(V) | f(xv,w) + f(v,xw) = 0 for all v,w}
    In matrix form: x^T·s + s·x = 0
    where s is a symmetric (not symplectic) matrix.

    B_l: odd-dimensional orthogonal algebra o(2l+1, F)
      Defined using s = [[1,0,0],[0,0,I],[0,I,0]] on R^{2l+1}.

    D_l: even-dimensional orthogonal algebra o(2l, F)
      Defined using s = [[0,I],[I,0]] on R^{2l}.

    Both are Lie subalgebras of gl(n,F).

    References: Humphreys §1.2, representations.org Part V. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.Lie.Ideals.
Require Import CAG.Lie.Linear.
Require Import CAG.Lie.SpecialLinear.
Require Import CAG.Lie.Symplectic.
From Stdlib Require Import List Arith.
Import ListNotations.

(* ================================================================== *)
(** * 1. General orthogonal Lie algebra                               *)
(* ================================================================== *)

(** The orthogonal condition relative to a symmetric form s:
      x^T·s + s·x = 0.
    Note this is the SAME algebraic condition as the symplectic condition
    (IsSymplectic), but applied with a symmetric rather than antisymmetric
    bilinear form matrix. *)

Definition IsOrthogonal {F : Type} (fld : Field F) (s : Matrix F) (A : Matrix F) : Prop :=
  mat_add fld
    (mat_mul fld (mat_transpose fld A) s)
    (mat_mul fld s A)
  = mat_zero fld 0.

(** The orthogonal condition implies A^T·s = -(s·A). *)
Lemma orth_cond_l {F : Type} (fld : Field F) (s A : Matrix F) :
    IsOrthogonal fld s A ->
    mat_mul fld (mat_transpose fld A) s = mat_neg fld (mat_mul fld s A).
Proof.
  unfold IsOrthogonal. intro H.
  rewrite <- (mat_add_zero_r fld (mat_mul fld (mat_transpose fld A) s)).
  rewrite <- (mat_add_neg fld (mat_mul fld s A)).
  rewrite <- mat_add_assoc_m, H. apply mat_add_zero_l.
Qed.

(** The orthogonal condition implies s·A = -(A^T·s). *)
Lemma orth_cond_r {F : Type} (fld : Field F) (s A : Matrix F) :
    IsOrthogonal fld s A ->
    mat_mul fld s A = mat_neg fld (mat_mul fld (mat_transpose fld A) s).
Proof.
  unfold IsOrthogonal. intro H.
  rewrite <- (mat_add_zero_l fld (mat_mul fld s A)).
  rewrite <- (mat_add_neg_l fld (mat_mul fld (mat_transpose fld A) s)).
  rewrite mat_add_assoc_m, H. apply mat_add_zero_r.
Qed.

(** o(n, s, F) is a Lie subalgebra of gl(n, F) for ANY symmetric form matrix s.
    The proof is identical to the symplectic case (same algebraic condition). *)
Lemma orth_is_subalgebra {F : Type} (fld : Field F) (n : nat) (s : Matrix F) :
    IsSubalgebra (gl fld n) (IsOrthogonal fld s).
Proof.
  constructor.
  (* (1) Zero *)
  - unfold IsOrthogonal.
    rewrite gl_zero_eq_mat_zero, mat_transpose_zero.
    rewrite mat_mul_zero_l_n, mat_mul_zero_r_n. apply mat_add_zero_l.
  (* (2) Addition *)
  - intros A B HA HB. unfold IsOrthogonal in *.
    rewrite gl_add_eq_mat_add, mat_transpose_add.
    rewrite mat_mul_add_distr_r, mat_mul_add_distr_l.
    rewrite (mat_add_assoc_m fld
               (mat_mul fld (mat_transpose fld A) s)
               (mat_mul fld (mat_transpose fld B) s)
               (mat_add fld (mat_mul fld s A) (mat_mul fld s B))).
    rewrite <- (mat_add_assoc_m fld
                  (mat_mul fld (mat_transpose fld B) s)
                  (mat_mul fld s A)
                  (mat_mul fld s B)).
    rewrite (mat_add_comm fld (mat_mul fld (mat_transpose fld B) s) (mat_mul fld s A)).
    rewrite (mat_add_assoc_m fld (mat_mul fld s A) (mat_mul fld (mat_transpose fld B) s) (mat_mul fld s B)).
    rewrite <- (mat_add_assoc_m fld
                  (mat_mul fld (mat_transpose fld A) s)
                  (mat_mul fld s A)
                  (mat_add fld (mat_mul fld (mat_transpose fld B) s) (mat_mul fld s B))).
    rewrite HA, HB. apply mat_add_zero_l.
  (* (3) Negation *)
  - intros A HA. unfold IsOrthogonal in *.
    rewrite gl_neg_eq_mat_neg, mat_transpose_neg.
    rewrite mat_mul_neg_l, mat_mul_neg_r.
    rewrite <- mat_neg_add. rewrite HA. apply mat_neg_zero.
  (* (4) Scalar multiplication *)
  - intros c A HA. unfold IsOrthogonal in *.
    rewrite gl_scale_eq_mat_scale, mat_transpose_scale.
    rewrite mat_mul_scale_l, mat_mul_scale_r.
    rewrite <- mat_scale_add_mat. rewrite HA. apply mat_scale_zero_mat.
  (* (5) Bracket closure — same calculation as sp, with general s. *)
  - intros A B HA HB. unfold IsOrthogonal in *.
    rewrite gl_bracket_eq_mat_bracket.
    rewrite mat_transpose_bracket.
    unfold mat_bracket.
    rewrite mat_mul_add_distr_r, mat_mul_add_distr_l.
    rewrite mat_mul_neg_l, mat_mul_neg_r.
    rewrite (mat_mul_assoc_m fld (mat_transpose fld B) (mat_transpose fld A) s).
    rewrite (mat_mul_assoc_m fld (mat_transpose fld A) (mat_transpose fld B) s).
    rewrite <- (mat_mul_assoc_m fld s A B).
    rewrite <- (mat_mul_assoc_m fld s B A).
    rewrite (orth_cond_l fld s A HA), (orth_cond_l fld s B HB).
    rewrite mat_mul_neg_r, mat_mul_neg_r.
    rewrite mat_neg_neg.
    rewrite <- (mat_mul_assoc_m fld (mat_transpose fld B) s A).
    rewrite <- (mat_mul_assoc_m fld (mat_transpose fld A) s B).
    rewrite (orth_cond_l fld s B HB), (orth_cond_l fld s A HA).
    rewrite mat_mul_neg_l, mat_mul_neg_l.
    rewrite mat_neg_neg.
    rewrite (mat_add_assoc_m fld
      (mat_mul fld (mat_mul fld s B) A)
      (mat_neg fld (mat_mul fld (mat_mul fld s A) B))
      (mat_add fld
        (mat_mul fld (mat_mul fld s A) B)
        (mat_neg fld (mat_mul fld (mat_mul fld s B) A)))).
    rewrite <- (mat_add_assoc_m fld
      (mat_neg fld (mat_mul fld (mat_mul fld s A) B))
      (mat_mul fld (mat_mul fld s A) B)
      (mat_neg fld (mat_mul fld (mat_mul fld s B) A))).
    rewrite mat_add_neg_l, mat_add_zero_l.
    apply mat_add_neg.
Qed.

(* ================================================================== *)
(** * 2. Standard orthogonal form matrices                            *)
(* ================================================================== *)

(** The B_l form matrix: s = [[1,0,0],[0,0,I_l],[0,I_l,0]] on F^{2l+1}. *)
Axiom bl_form : forall {F : Type} (fld : Field F) (l : nat), Matrix F.

(** The D_l form matrix: s = [[0,I_l],[I_l,0]] on F^{2l}. *)
Axiom dl_form : forall {F : Type} (fld : Field F) (l : nat), Matrix F.

(** Both forms are symmetric: s^T = s. *)
Axiom bl_form_symm :
  forall {F : Type} (fld : Field F) (l : nat),
    mat_transpose fld (bl_form fld l) = bl_form fld l.

Axiom dl_form_symm :
  forall {F : Type} (fld : Field F) (l : nat),
    mat_transpose fld (dl_form fld l) = dl_form fld l.

(* ================================================================== *)
(** * 3. B_l = o(2l+1, F)                                            *)
(* ================================================================== *)

Definition IsBl {F : Type} (fld : Field F) (l : nat) (A : Matrix F) : Prop :=
  IsOrthogonal fld (bl_form fld l) A.

Lemma bl_is_subalgebra {F : Type} (fld : Field F) (l : nat) :
    IsSubalgebra (gl fld (2 * l + 1)) (IsBl fld l).
Proof.
  unfold IsBl. apply orth_is_subalgebra.
Qed.

(* ================================================================== *)
(** * 4. D_l = o(2l, F)                                              *)
(* ================================================================== *)

Definition IsDl {F : Type} (fld : Field F) (l : nat) (A : Matrix F) : Prop :=
  IsOrthogonal fld (dl_form fld l) A.

Lemma dl_is_subalgebra {F : Type} (fld : Field F) (l : nat) :
    IsSubalgebra (gl fld (2 * l)) (IsDl fld l).
Proof.
  unfold IsDl. apply orth_is_subalgebra.
Qed.

(* ================================================================== *)
(** * 5. Block matrix characterisation (axiomatised)                  *)
(* ================================================================== *)

(** For B_l with x = [[a,b,c],[d,m,n],[e,p,q]] (blocks of sizes 1,l,l):
    IsOrthogonal bl_form x is equivalent to:
      a = 0, c = -b^T, e = -d^T
      n^T = -n, p^T = -p, q = -m^T. *)
Axiom bl_block_char : forall {F : Type} (fld : Field F) (l : nat) (A : Matrix F),
    IsBl fld l A -> True. (* placeholder *)

(** For D_l with x = [[m,n],[p,q]] (l×l blocks):
    IsOrthogonal dl_form x is equivalent to:
      n^T = -n, p^T = -p, q = -m^T. *)
Axiom dl_block_char : forall {F : Type} (fld : Field F) (l : nat) (A : Matrix F),
    IsDl fld l A -> True. (* placeholder *)
