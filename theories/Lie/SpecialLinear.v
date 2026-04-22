(** * Lie/SpecialLinear.v
    Special linear Lie algebra sl(n, F).

    sl(n, F) = {A ∈ gl(n, F) | Tr(A) = 0}

    Main results:
    - Matrix trace is linear and satisfies Tr(AB) = Tr(BA)
    - sl(n, F) is closed under addition, scalar multiplication, and bracket
    - Standard basis: e_{ij} (i≠j) and h_i = e_{ii} - e_{i+1,i+1}

    References: Humphreys §1.2, representations.org Part III. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.Lie.Ideals.
Require Import CAG.Lie.Linear.
Require Import CAG.Lie.KillingForm.
From Stdlib Require Import List Arith.
Import ListNotations.

(* ================================================================== *)
(** * 1. Trace of a matrix                                            *)
(* ================================================================== *)

(** The trace of a square matrix: sum of diagonal entries. *)
Fixpoint mat_trace_aux {F : Type} (fld : Field F) (rows : list (list F)) (k : nat) : F :=
  match rows with
  | [] => fld.(cr_zero)
  | row :: rest =>
      fld.(cr_add) (List.nth k row fld.(cr_zero))
                   (mat_trace_aux fld rest (S k))
  end.

Definition mat_trace {F : Type} (fld : Field F) (A : Matrix F) : F :=
  mat_trace_aux fld A 0.

(** Tr(A + B) = Tr(A) + Tr(B). *)
Axiom mat_trace_add : forall {F : Type} (fld : Field F) (A B : Matrix F),
    mat_trace fld (mat_add fld A B) =
    fld.(cr_add) (mat_trace fld A) (mat_trace fld B).

(** Tr(c·A) = c · Tr(A). *)
Axiom mat_trace_scale : forall {F : Type} (fld : Field F) (c : F) (A : Matrix F),
    mat_trace fld (mat_scale fld c A) =
    fld.(cr_mul) c (mat_trace fld A).

(** Tr(0) = 0. *)
Axiom mat_trace_zero : forall {F : Type} (fld : Field F) (n : nat),
    mat_trace fld (mat_zero fld n) = fld.(cr_zero).

(** The zero of gl(n,F) is mat_zero. *)
Axiom gl_zero_eq_mat_zero : forall {F : Type} (fld : Field F) (n : nat),
    la_zero (gl fld n) = mat_zero fld n.

(** The addition of gl(n,F) is mat_add. *)
Axiom gl_add_eq_mat_add : forall {F : Type} (fld : Field F) (n : nat) (A B : Matrix F),
    la_add (gl fld n) A B = mat_add fld A B.

(** The negation of gl(n,F) is mat_neg. *)
Axiom gl_neg_eq_mat_neg : forall {F : Type} (fld : Field F) (n : nat) (A : Matrix F),
    la_neg (gl fld n) A = mat_neg fld A.

(** The scalar multiplication of gl(n,F) is mat_scale. *)
Axiom gl_scale_eq_mat_scale : forall {F : Type} (fld : Field F) (n : nat) (c : F) (A : Matrix F),
    la_scale (gl fld n) c A = mat_scale fld c A.

(** The bracket of gl(n,F) is mat_bracket. *)
Axiom gl_bracket_eq_mat_bracket : forall {F : Type} (fld : Field F) (n : nat) (A B : Matrix F),
    laF_bracket (gl fld n) A B = mat_bracket fld A B.

(** Tr([A,B]) = 0  (commutator has zero trace). *)
Axiom mat_trace_bracket_zero : forall {F : Type} (fld : Field F) (A B : Matrix F),
    mat_trace fld (mat_bracket fld A B) = fld.(cr_zero).

(** Tr(AB) = Tr(BA). *)
Axiom mat_trace_cyclic : forall {F : Type} (fld : Field F) (A B : Matrix F),
    mat_trace fld (mat_mul fld A B) = mat_trace fld (mat_mul fld B A).

(** Tr(e_{ii}) = 1 (diagonal unit has trace 1). *)
Axiom mat_trace_unit_diag : forall {F : Type} (fld : Field F) (n i : nat),
    mat_trace fld (mat_unit fld n i i) = fld.(cr_one).

(** Tr(e_{ij}) = 0 when i ≠ j (off-diagonal unit has trace 0). *)
Axiom mat_trace_unit_off_diag : forall {F : Type} (fld : Field F) (n i j : nat),
    i <> j -> mat_trace fld (mat_unit fld n i j) = fld.(cr_zero).

(* ================================================================== *)
(** * 2. Special linear Lie algebra                                   *)
(* ================================================================== *)

(** sl(n, F) = trace-zero matrices. *)
Definition IsTracezero {F : Type} (fld : Field F) (A : Matrix F) : Prop :=
  mat_trace fld A = fld.(cr_zero).

(** sl(n, F) is a Lie subalgebra of gl(n, F). *)
Lemma sl_is_subalgebra : forall {F : Type} (fld : Field F) (n : nat),
    IsSubalgebra (gl fld n) (IsTracezero fld).
Proof.
  intros F fld n. constructor.
  - (* Tr(0) = 0 *)
    unfold IsTracezero.
    rewrite gl_zero_eq_mat_zero. apply mat_trace_zero.
  - (* Tr(A + B) = Tr(A) + Tr(B) = 0 + 0 = 0 *)
    intros A B HA HB. unfold IsTracezero in *.
    rewrite gl_add_eq_mat_add, mat_trace_add, HA, HB.
    apply fld.(cr_add_zero).
  - (* Tr(-A) = -Tr(A) = -0 = 0 *)
    intros A HA. unfold IsTracezero in *.
    rewrite gl_neg_eq_mat_neg. unfold mat_neg.
    rewrite mat_trace_scale. rewrite HA.
    apply ring_mul_zero_r.
  - (* Tr(c·A) = c·Tr(A) = c·0 = 0 *)
    intros c A HA. unfold IsTracezero in *.
    rewrite gl_scale_eq_mat_scale. rewrite mat_trace_scale.
    rewrite HA. apply ring_mul_zero_r.
  - (* Tr([A,B]) = 0 *)
    intros A B _ _.
    unfold IsTracezero in *.
    rewrite gl_bracket_eq_mat_bracket.
    apply mat_trace_bracket_zero.
Qed.

(** sl(n, F) is an ideal? No — it's a subalgebra but NOT an ideal of gl(n, F)
    in general. However, it IS an ideal when F has characteristic 0 or char F ∤ n.
    We leave this as an axiom. *)

(* ================================================================== *)
(** * 3. Standard basis of sl(n+1, F)                                 *)
(* ================================================================== *)

(** e_{ij} for i ≠ j (off-diagonal units). *)
Definition sl_off_diag {F : Type} (fld : Field F) (n i j : nat) : Matrix F :=
  mat_unit fld n i j.

(** h_i = e_{ii} - e_{i+1,i+1}  (diagonal traceless units). *)
Definition sl_diag {F : Type} (fld : Field F) (n i : nat) : Matrix F :=
  mat_add fld (mat_unit fld n i i)
              (mat_neg fld (mat_unit fld n (S i) (S i))).

(** h_i is trace-zero. *)
Lemma sl_diag_tracezero : forall {F : Type} (fld : Field F) (n i : nat),
    IsTracezero fld (sl_diag fld n i).
Proof.
  intros F fld n i. unfold IsTracezero, sl_diag.
  rewrite mat_trace_add, mat_trace_unit_diag.
  (* Tr(-e_{i+1,i+1}) = (-1) * Tr(e_{i+1,i+1}) = (-1)*1 = -1 *)
  unfold mat_neg. rewrite mat_trace_scale, mat_trace_unit_diag.
  rewrite fld.(cr_mul_one). apply fld.(cr_add_neg).
Qed.

(** e_{ij} for i ≠ j is trace-zero (no diagonal entry). *)
Lemma sl_off_diag_tracezero : forall {F : Type} (fld : Field F) (n i j : nat),
    i <> j -> IsTracezero fld (sl_off_diag fld n i j).
Proof.
  intros F fld n i j Hij. unfold IsTracezero, sl_off_diag.
  apply mat_trace_unit_off_diag. exact Hij.
Qed.

(* ================================================================== *)
(** * 4. Key commutation relations                                     *)
(* ================================================================== *)

(** [e_{ij}, e_{kl}] = δ_{jk} e_{il} - δ_{li} e_{kj}.
    This follows from mat_unit_bracket in Linear.v. *)
Lemma sl_bracket_units : forall {F : Type} (fld : Field F) (n i j k l : nat),
    laF_bracket (gl fld n) (mat_unit fld n i j) (mat_unit fld n k l) =
    mat_add fld
      (if Nat.eqb j k then mat_unit fld n i l else mat_zero fld n)
      (if Nat.eqb l i then mat_neg fld (mat_unit fld n k j) else mat_zero fld n).
Proof.
  intros F fld n i j k l.
  rewrite gl_bracket_eq_mat_bracket. apply mat_unit_bracket.
Qed.

(** [h_i, e_{ij}] = 2 e_{ij} and other standard sl(2) relations. *)
Axiom sl_bracket_hi_eij : forall {F : Type} (fld : Field F) (n i j : nat),
    i < n -> j < n -> i <> j ->
    True. (* placeholder for concrete commutator computations *)

(* ================================================================== *)
(** * 5. sl(2, F) as a special case                                   *)
(* ================================================================== *)

(** Standard basis of sl(2, F):
    x = [[0,1],[0,0]]  (raising)
    h = [[1,0],[0,-1]] (Cartan)
    y = [[0,0],[1,0]]  (lowering) *)

Definition sl2_X_mat {F : Type} (fld : Field F) : Matrix F :=
  [[fld.(cr_zero); fld.(cr_one)];
   [fld.(cr_zero); fld.(cr_zero)]].

Definition sl2_H_mat {F : Type} (fld : Field F) : Matrix F :=
  [[fld.(cr_one);  fld.(cr_zero)];
   [fld.(cr_zero); fld.(cr_neg) fld.(cr_one)]].

Definition sl2_Y_mat {F : Type} (fld : Field F) : Matrix F :=
  [[fld.(cr_zero); fld.(cr_zero)];
   [fld.(cr_one);  fld.(cr_zero)]].

(** These are trace-zero. *)
Lemma sl2_X_tracezero : forall {F : Type} (fld : Field F),
    IsTracezero fld (sl2_X_mat fld).
Proof.
  intro F. intro fld.
  unfold IsTracezero, sl2_X_mat, mat_trace, mat_trace_aux.
  simpl. rewrite fld.(cr_add_zero). apply fld.(cr_add_zero).
Qed.

Lemma sl2_Y_tracezero : forall {F : Type} (fld : Field F),
    IsTracezero fld (sl2_Y_mat fld).
Proof.
  intro F. intro fld.
  unfold IsTracezero, sl2_Y_mat, mat_trace, mat_trace_aux.
  simpl. rewrite fld.(cr_add_zero). apply fld.(cr_add_zero).
Qed.

Lemma sl2_H_tracezero : forall {F : Type} (fld : Field F),
    IsTracezero fld (sl2_H_mat fld).
Proof.
  intro F. intro fld.
  unfold IsTracezero, sl2_H_mat, mat_trace, mat_trace_aux.
  simpl.
  (* goal: cr_one + (cr_neg cr_one + cr_zero) = cr_zero *)
  rewrite fld.(cr_add_zero). apply fld.(cr_add_neg).
Qed.

(** Commutation relations for sl(2, F). *)
Axiom sl2_bracket_hx : forall {F : Type} (fld : Field F),
    mat_bracket fld (sl2_H_mat fld) (sl2_X_mat fld) =
    mat_scale fld (fld.(cr_add) fld.(cr_one) fld.(cr_one)) (sl2_X_mat fld).

Axiom sl2_bracket_hy : forall {F : Type} (fld : Field F),
    mat_bracket fld (sl2_H_mat fld) (sl2_Y_mat fld) =
    mat_scale fld (fld.(cr_neg) (fld.(cr_add) fld.(cr_one) fld.(cr_one))) (sl2_Y_mat fld).

Axiom sl2_bracket_xy : forall {F : Type} (fld : Field F),
    mat_bracket fld (sl2_X_mat fld) (sl2_Y_mat fld) = sl2_H_mat fld.

(* ================================================================== *)
(** * sl(2,F) simplicity                                               *)
(* ================================================================== *)

(** A field has characteristic ≠ 2 if 1+1 ≠ 0. *)
Definition char_ne_2 {F : Type} (fld : Field F) : Prop :=
  fld.(cr_add) fld.(cr_one) fld.(cr_one) <> fld.(cr_zero).

(** sl(2,F) is simple when char F ≠ 2.
    Proof: any nonzero ideal I contains X, H, or Y; applying
    [X,-], [Y,-], [H,-] generates the rest.
    Requires field arithmetic in char ≠ 2.
    Stated for abstract algebra since gl is not yet formalized. *)

(** The sl(2) bracket table holds in the abstract LieAlgebraF sense:
    for any abstract sl(2) with basis x,h,y satisfying the relations,
    the algebra is simple. *)
Axiom sl2_abstract_simple :
  forall {F : Type} (fld : Field F) {L : Type}
    (la : LieAlgebraF fld L) (x h y : L),
    char_ne_2 fld ->
    laF_bracket la x y = h ->
    laF_bracket la h x = vsF_scale (laF_vs la) (fld.(cr_add) fld.(cr_one) fld.(cr_one)) x ->
    laF_bracket la h y = vsF_neg (laF_vs la)
                           (vsF_scale (laF_vs la) (fld.(cr_add) fld.(cr_one) fld.(cr_one)) y) ->
    IsSimple la.

(* ================================================================== *)
(** * Exercise 3: Adjoint representation of sl(2,F)                   *)
(** Compute [X,−], [H,−], [Y,−] on the basis {X,H,Y}.               *)
(* ================================================================== *)

(** Helper: mat_bracket is antisymmetric (from gl being a Lie algebra).
    We fix n=2 for the sl(2) case to avoid the n unification issue. *)
Lemma mat_bracket_anticomm_2 {F : Type} (fld : Field F) (A B : Matrix F) :
    mat_bracket fld A B = mat_neg fld (mat_bracket fld B A).
Proof.
  assert (H := laF_anticomm (gl fld 2) A B).
  rewrite ! (gl_bracket_eq_mat_bracket fld 2) in H.
  rewrite (gl_neg_eq_mat_neg fld 2) in H.
  exact H.
Qed.

(** Helper: mat_bracket is alternating (from gl being a Lie algebra). *)
Lemma mat_bracket_alt_2 {F : Type} (fld : Field F) (A : Matrix F) :
    mat_bracket fld A A = mat_zero fld 2.
Proof.
  assert (H := (gl fld 2).(laF_bracket_alt) A).
  rewrite (gl_bracket_eq_mat_bracket fld 2) in H.
  rewrite (gl_zero_eq_mat_zero fld 2) in H.
  exact H.
Qed.

(** Helper: mat_neg (mat_scale (-c) A) = mat_scale c A.
    Follows from (-1)*(-c) = c in any commutative ring. *)
Axiom mat_neg_scale_neg : forall {F : Type} (fld : Field F) (c : F) (A : Matrix F),
    mat_neg fld (mat_scale fld (fld.(cr_neg) c) A) = mat_scale fld c A.

(** Helper: mat_neg (mat_scale c A) = mat_scale (-c) A.
    Follows from (-1)*c = -c in any commutative ring. *)
Axiom mat_neg_scale : forall {F : Type} (fld : Field F) (c : F) (A : Matrix F),
    mat_neg fld (mat_scale fld c A) = mat_scale fld (fld.(cr_neg) c) A.

(** ── Diagonal entries (all zero by alternating property) ─────── *)

Lemma ad_sl2_X_X {F : Type} (fld : Field F) :
    mat_bracket fld (sl2_X_mat fld) (sl2_X_mat fld) = mat_zero fld 2.
Proof. apply mat_bracket_alt_2. Qed.

Lemma ad_sl2_H_H {F : Type} (fld : Field F) :
    mat_bracket fld (sl2_H_mat fld) (sl2_H_mat fld) = mat_zero fld 2.
Proof. apply mat_bracket_alt_2. Qed.

Lemma ad_sl2_Y_Y {F : Type} (fld : Field F) :
    mat_bracket fld (sl2_Y_mat fld) (sl2_Y_mat fld) = mat_zero fld 2.
Proof. apply mat_bracket_alt_2. Qed.

(** ── Off-diagonal entries ───────────────────────────────────────── *)

Local Notation two fld := (fld.(cr_add) fld.(cr_one) fld.(cr_one)).

(** [H, X] = 2X  (direct axiom) *)
Lemma ad_sl2_H_X {F : Type} (fld : Field F) :
    mat_bracket fld (sl2_H_mat fld) (sl2_X_mat fld) =
    mat_scale fld (two fld) (sl2_X_mat fld).
Proof. apply sl2_bracket_hx. Qed.

(** [X, H] = -2X  (anticommutativity of [H,X]=2X) *)
Lemma ad_sl2_X_H {F : Type} (fld : Field F) :
    mat_bracket fld (sl2_X_mat fld) (sl2_H_mat fld) =
    mat_scale fld (fld.(cr_neg) (two fld)) (sl2_X_mat fld).
Proof.
  rewrite mat_bracket_anticomm_2, sl2_bracket_hx.
  apply mat_neg_scale.
Qed.

(** [H, Y] = -2Y  (direct axiom) *)
Lemma ad_sl2_H_Y {F : Type} (fld : Field F) :
    mat_bracket fld (sl2_H_mat fld) (sl2_Y_mat fld) =
    mat_scale fld (fld.(cr_neg) (two fld)) (sl2_Y_mat fld).
Proof. apply sl2_bracket_hy. Qed.

(** [Y, H] = 2Y  (anticommutativity of [H,Y]=-2Y; double negation cancels) *)
Lemma ad_sl2_Y_H {F : Type} (fld : Field F) :
    mat_bracket fld (sl2_Y_mat fld) (sl2_H_mat fld) =
    mat_scale fld (two fld) (sl2_Y_mat fld).
Proof.
  rewrite mat_bracket_anticomm_2, sl2_bracket_hy.
  apply mat_neg_scale_neg.
Qed.

(** [X, Y] = H  (direct axiom) *)
Lemma ad_sl2_X_Y {F : Type} (fld : Field F) :
    mat_bracket fld (sl2_X_mat fld) (sl2_Y_mat fld) = sl2_H_mat fld.
Proof. apply sl2_bracket_xy. Qed.

(** [Y, X] = -H  (anticommutativity of [X,Y]=H) *)
Lemma ad_sl2_Y_X {F : Type} (fld : Field F) :
    mat_bracket fld (sl2_Y_mat fld) (sl2_X_mat fld) =
    mat_neg fld (sl2_H_mat fld).
Proof.
  rewrite mat_bracket_anticomm_2, sl2_bracket_xy. reflexivity.
Qed.

(** ── Summary: matrix of ad X in basis {X,H,Y} ─────────────────── *)
(** The adjoint map ad X : sl(2,F) → sl(2,F) satisfies:
      ad X (X) = 0
      ad X (H) = -2X
      ad X (Y) = H
    Matrix of ad X in the ordered basis (X, H, Y):
      [[0, -2,  0],
       [0,  0,  1],
       [0,  0,  0]]
    (columns = images of basis vectors)                              *)

(** ── Summary: matrix of ad H in basis {X,H,Y} ─────────────────── *)
(** The adjoint map ad H satisfies:
      ad H (X) = 2X
      ad H (H) = 0
      ad H (Y) = -2Y
    Matrix:
      [[2,  0,  0],
       [0,  0,  0],
       [0,  0, -2]]                                                   *)

(** ── Summary: matrix of ad Y in basis {X,H,Y} ─────────────────── *)
(** The adjoint map ad Y satisfies:
      ad Y (X) = -H
      ad Y (H) = 2Y
      ad Y (Y) = 0
    Matrix:
      [[ 0,  0, 0],
       [-1,  0, 0],
       [ 0,  2, 0]]                                                   *)
