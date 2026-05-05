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
Require Import CAG.Lie.Semisimple.
Require Import CAG.Lie.Solvable.
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
(* CAG zero-dependent Axiom mat_trace_add theories/Lie/SpecialLinear.v:40 BEGIN
Axiom mat_trace_add : forall {F : Type} (fld : Field F) (A B : Matrix F),
    mat_trace fld (mat_add fld A B) =
    fld.(cr_add) (mat_trace fld A) (mat_trace fld B).
   CAG zero-dependent Axiom mat_trace_add theories/Lie/SpecialLinear.v:40 END *)

(** Tr(c·A) = c · Tr(A). *)
(* CAG zero-dependent Axiom mat_trace_scale theories/Lie/SpecialLinear.v:45 BEGIN
Axiom mat_trace_scale : forall {F : Type} (fld : Field F) (c : F) (A : Matrix F),
    mat_trace fld (mat_scale fld c A) =
    fld.(cr_mul) c (mat_trace fld A).
   CAG zero-dependent Axiom mat_trace_scale theories/Lie/SpecialLinear.v:45 END *)

(** Tr(0) = 0. *)
(* CAG zero-dependent Axiom mat_trace_zero theories/Lie/SpecialLinear.v:50 BEGIN
Axiom mat_trace_zero : forall {F : Type} (fld : Field F) (n : nat),
    mat_trace fld (mat_zero fld n) = fld.(cr_zero).
   CAG zero-dependent Axiom mat_trace_zero theories/Lie/SpecialLinear.v:50 END *)

(** The zero of gl(n,F) is mat_zero. *)
(* CAG zero-dependent Lemma gl_zero_eq_mat_zero theories/Lie/SpecialLinear.v:54 BEGIN
Lemma gl_zero_eq_mat_zero : forall {F : Type} (fld : Field F) (n : nat),
    la_zero (gl fld n) = mat_zero fld n.
Proof. intros F fld n. simpl. apply mat_zero_any. Qed.
   CAG zero-dependent Lemma gl_zero_eq_mat_zero theories/Lie/SpecialLinear.v:54 END *)

(** The addition of gl(n,F) is mat_add. *)
(* CAG zero-dependent Lemma gl_add_eq_mat_add theories/Lie/SpecialLinear.v:59 BEGIN
Lemma gl_add_eq_mat_add : forall {F : Type} (fld : Field F) (n : nat) (A B : Matrix F),
    la_add (gl fld n) A B = mat_add fld A B.
Proof. intros. reflexivity. Qed.
   CAG zero-dependent Lemma gl_add_eq_mat_add theories/Lie/SpecialLinear.v:59 END *)

(** The negation of gl(n,F) is mat_neg. *)
(* CAG zero-dependent Lemma gl_neg_eq_mat_neg theories/Lie/SpecialLinear.v:64 BEGIN
Lemma gl_neg_eq_mat_neg : forall {F : Type} (fld : Field F) (n : nat) (A : Matrix F),
    la_neg (gl fld n) A = mat_neg fld A.
Proof. intros. reflexivity. Qed.
   CAG zero-dependent Lemma gl_neg_eq_mat_neg theories/Lie/SpecialLinear.v:64 END *)

(** The scalar multiplication of gl(n,F) is mat_scale. *)
(* CAG zero-dependent Lemma gl_scale_eq_mat_scale theories/Lie/SpecialLinear.v:69 BEGIN
Lemma gl_scale_eq_mat_scale : forall {F : Type} (fld : Field F) (n : nat) (c : F) (A : Matrix F),
    la_scale (gl fld n) c A = mat_scale fld c A.
Proof. intros. reflexivity. Qed.
   CAG zero-dependent Lemma gl_scale_eq_mat_scale theories/Lie/SpecialLinear.v:69 END *)

(** The bracket of gl(n,F) is mat_bracket. *)
(* CAG zero-dependent Lemma gl_bracket_eq_mat_bracket theories/Lie/SpecialLinear.v:74 BEGIN
Lemma gl_bracket_eq_mat_bracket : forall {F : Type} (fld : Field F) (n : nat) (A B : Matrix F),
    laF_bracket (gl fld n) A B = mat_bracket fld A B.
Proof. intros. reflexivity. Qed.
   CAG zero-dependent Lemma gl_bracket_eq_mat_bracket theories/Lie/SpecialLinear.v:74 END *)

(** Tr([A,B]) = 0  (commutator has zero trace). *)
(* CAG zero-dependent Axiom mat_trace_bracket_zero theories/Lie/SpecialLinear.v:79 BEGIN
Axiom mat_trace_bracket_zero : forall {F : Type} (fld : Field F) (A B : Matrix F),
    mat_trace fld (mat_bracket fld A B) = fld.(cr_zero).
   CAG zero-dependent Axiom mat_trace_bracket_zero theories/Lie/SpecialLinear.v:79 END *)

(** Tr(AB) = Tr(BA). *)
(* CAG zero-dependent Axiom mat_trace_cyclic theories/Lie/SpecialLinear.v:83 BEGIN
Axiom mat_trace_cyclic : forall {F : Type} (fld : Field F) (A B : Matrix F),
    mat_trace fld (mat_mul fld A B) = mat_trace fld (mat_mul fld B A).
   CAG zero-dependent Axiom mat_trace_cyclic theories/Lie/SpecialLinear.v:83 END *)

(** Tr(e_{ii}) = 1 (diagonal unit has trace 1). *)
(* CAG zero-dependent Axiom mat_trace_unit_diag theories/Lie/SpecialLinear.v:89 BEGIN
Axiom mat_trace_unit_diag : forall {F : Type} (fld : Field F) (n i : nat),
    mat_trace fld (mat_unit fld n i i) = fld.(cr_one).
   CAG zero-dependent Axiom mat_trace_unit_diag theories/Lie/SpecialLinear.v:89 END *)

(** Tr(e_{ij}) = 0 when i ≠ j (off-diagonal unit has trace 0). *)
(* CAG zero-dependent Axiom mat_trace_unit_off_diag theories/Lie/SpecialLinear.v:93 BEGIN
Axiom mat_trace_unit_off_diag : forall {F : Type} (fld : Field F) (n i j : nat),
    i <> j -> mat_trace fld (mat_unit fld n i j) = fld.(cr_zero).
   CAG zero-dependent Axiom mat_trace_unit_off_diag theories/Lie/SpecialLinear.v:93 END *)

(* ================================================================== *)
(** * 2. Special linear Lie algebra                                   *)
(* ================================================================== *)

(** sl(n, F) = trace-zero matrices. *)
Definition IsTracezero {F : Type} (fld : Field F) (A : Matrix F) : Prop :=
  mat_trace fld A = fld.(cr_zero).

(** sl(n, F) is a Lie subalgebra of gl(n, F). *)
(* CAG zero-dependent Lemma sl_is_subalgebra theories/Lie/SpecialLinear.v:109 BEGIN
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
   CAG zero-dependent Lemma sl_is_subalgebra theories/Lie/SpecialLinear.v:109 END *)

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
(* CAG zero-dependent Lemma sl_diag_tracezero theories/Lie/SpecialLinear.v:150 BEGIN
Lemma sl_diag_tracezero : forall {F : Type} (fld : Field F) (n i : nat),
    IsTracezero fld (sl_diag fld n i).
Proof.
  intros F fld n i. unfold IsTracezero, sl_diag.
  rewrite mat_trace_add, mat_trace_unit_diag.
  (* Tr(-e_{i+1,i+1}) = (-1) * Tr(e_{i+1,i+1}) = (-1)*1 = -1 *)
  unfold mat_neg. rewrite mat_trace_scale, mat_trace_unit_diag.
  rewrite fld.(cr_mul_one). apply fld.(cr_add_neg).
Qed.
   CAG zero-dependent Lemma sl_diag_tracezero theories/Lie/SpecialLinear.v:150 END *)

(** e_{ij} for i ≠ j is trace-zero (no diagonal entry). *)
(* CAG zero-dependent Lemma sl_off_diag_tracezero theories/Lie/SpecialLinear.v:161 BEGIN
Lemma sl_off_diag_tracezero : forall {F : Type} (fld : Field F) (n i j : nat),
    i <> j -> IsTracezero fld (sl_off_diag fld n i j).
Proof.
  intros F fld n i j Hij. unfold IsTracezero, sl_off_diag.
  apply mat_trace_unit_off_diag. exact Hij.
Qed.
   CAG zero-dependent Lemma sl_off_diag_tracezero theories/Lie/SpecialLinear.v:161 END *)

(* ================================================================== *)
(** * 4. Key commutation relations                                     *)
(* ================================================================== *)

(** [e_{ij}, e_{kl}] = δ_{jk} e_{il} - δ_{li} e_{kj}.
    This follows from mat_unit_bracket in Linear.v. *)
(* CAG zero-dependent Lemma sl_bracket_units theories/Lie/SpecialLinear.v:174 BEGIN
Lemma sl_bracket_units : forall {F : Type} (fld : Field F) (n i j k l : nat),
    laF_bracket (gl fld n) (mat_unit fld n i j) (mat_unit fld n k l) =
    mat_add fld
      (if Nat.eqb j k then mat_unit fld n i l else mat_zero fld n)
      (if Nat.eqb l i then mat_neg fld (mat_unit fld n k j) else mat_zero fld n).
Proof.
  intros F fld n i j k l.
  rewrite gl_bracket_eq_mat_bracket. apply mat_unit_bracket.
Qed.
   CAG zero-dependent Lemma sl_bracket_units theories/Lie/SpecialLinear.v:174 END *)

(** [h_i, e_{ij}] = (a_i - a_j) e_{ij} where h_i = e_{ii} - e_{i+1,i+1}.
    For sl(n), the diagonal generators h_i act on the off-diagonal e_{ij}
    as scalar multiplication by 1 if i=k, -1 if i=k+1 etc.

    Stated as a Conjecture pending the definition of `mat_diag_unit`
    (the matrix h_k = e_{kk} - e_{k+1,k+1}). Reference: Humphreys §1.2,
    sl(n,F) basis. *)
(* CAG zero-dependent Conjecture sl_bracket_hi_eij theories/Lie/SpecialLinear.v:191 BEGIN
Conjecture sl_bracket_hi_eij : forall {F : Type} (fld : Field F) (n i j : nat),
    i < n -> j < n -> i <> j ->
    laF_bracket (gl fld n)
      (mat_add fld (mat_unit fld n i i)
                   (mat_neg fld (mat_unit fld n j j)))
      (mat_unit fld n i j) =
    mat_scale fld (fld.(cr_add) fld.(cr_one) fld.(cr_one)) (mat_unit fld n i j).
   CAG zero-dependent Conjecture sl_bracket_hi_eij theories/Lie/SpecialLinear.v:191 END *)

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
(* CAG zero-dependent Axiom sl2_bracket_hx theories/Lie/SpecialLinear.v:260 BEGIN
Axiom sl2_bracket_hx : forall {F : Type} (fld : Field F),
    mat_bracket fld (sl2_H_mat fld) (sl2_X_mat fld) =
    mat_scale fld (fld.(cr_add) fld.(cr_one) fld.(cr_one)) (sl2_X_mat fld).
   CAG zero-dependent Axiom sl2_bracket_hx theories/Lie/SpecialLinear.v:260 END *)

(* CAG zero-dependent Axiom sl2_bracket_hy theories/Lie/SpecialLinear.v:264 BEGIN
Axiom sl2_bracket_hy : forall {F : Type} (fld : Field F),
    mat_bracket fld (sl2_H_mat fld) (sl2_Y_mat fld) =
    mat_scale fld (fld.(cr_neg) (fld.(cr_add) fld.(cr_one) fld.(cr_one))) (sl2_Y_mat fld).
   CAG zero-dependent Axiom sl2_bracket_hy theories/Lie/SpecialLinear.v:264 END *)

(* CAG zero-dependent Axiom sl2_bracket_xy theories/Lie/SpecialLinear.v:268 BEGIN
Axiom sl2_bracket_xy : forall {F : Type} (fld : Field F),
    mat_bracket fld (sl2_X_mat fld) (sl2_Y_mat fld) = sl2_H_mat fld.
   CAG zero-dependent Axiom sl2_bracket_xy theories/Lie/SpecialLinear.v:268 END *)

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
(* CAG zero-dependent Axiom sl2_abstract_simple theories/Lie/SpecialLinear.v:273 BEGIN
Axiom sl2_abstract_simple :
  forall {F : Type} (fld : Field F) {L : Type}
    (la : LieAlgebraF fld L) (x h y : L),
    char_ne_2 fld ->
    laF_bracket la x y = h ->
    laF_bracket la h x = vsF_scale (laF_vs la) (fld.(cr_add) fld.(cr_one) fld.(cr_one)) x ->
    laF_bracket la h y = vsF_neg (laF_vs la)
                           (vsF_scale (laF_vs la) (fld.(cr_add) fld.(cr_one) fld.(cr_one)) y) ->
    IsSimple la.
   CAG zero-dependent Axiom sl2_abstract_simple theories/Lie/SpecialLinear.v:273 END *)

(* ================================================================== *)
(** * Exercise 3: Adjoint representation of sl(2,F)                   *)
(** Compute [X,−], [H,−], [Y,−] on the basis {X,H,Y}.               *)
(* ================================================================== *)

(** Helper: mat_bracket is antisymmetric (from gl being a Lie algebra).
    We fix n=2 for the sl(2) case to avoid the n unification issue. *)
(* CAG zero-dependent Lemma mat_bracket_anticomm_2 theories/Lie/SpecialLinear.v:307 BEGIN
Lemma mat_bracket_anticomm_2 {F : Type} (fld : Field F) (A B : Matrix F) :
    mat_bracket fld A B = mat_neg fld (mat_bracket fld B A).
Proof.
  assert (H := laF_anticomm (gl fld 2) A B).
  rewrite ! (gl_bracket_eq_mat_bracket fld 2) in H.
  rewrite (gl_neg_eq_mat_neg fld 2) in H.
  exact H.
Qed.
   CAG zero-dependent Lemma mat_bracket_anticomm_2 theories/Lie/SpecialLinear.v:307 END *)

(** Helper: mat_bracket is alternating (from gl being a Lie algebra). *)
(* CAG zero-dependent Lemma mat_bracket_alt_2 theories/Lie/SpecialLinear.v:317 BEGIN
Lemma mat_bracket_alt_2 {F : Type} (fld : Field F) (A : Matrix F) :
    mat_bracket fld A A = mat_zero fld 2.
Proof.
  assert (H := (gl fld 2).(laF_bracket_alt) A).
  rewrite (gl_bracket_eq_mat_bracket fld 2) in H.
  rewrite (gl_zero_eq_mat_zero fld 2) in H.
  exact H.
Qed.
   CAG zero-dependent Lemma mat_bracket_alt_2 theories/Lie/SpecialLinear.v:317 END *)

(** Helper: mat_neg (mat_scale (-c) A) = mat_scale c A.
    Follows from (-1)*(-c) = c in any commutative ring. *)
(* CAG zero-dependent Axiom mat_neg_scale_neg theories/Lie/SpecialLinear.v:318 BEGIN
Axiom mat_neg_scale_neg : forall {F : Type} (fld : Field F) (c : F) (A : Matrix F),
    mat_neg fld (mat_scale fld (fld.(cr_neg) c) A) = mat_scale fld c A.
   CAG zero-dependent Axiom mat_neg_scale_neg theories/Lie/SpecialLinear.v:318 END *)

(** Helper: mat_neg (mat_scale c A) = mat_scale (-c) A.
    Follows from (-1)*c = -c in any commutative ring. *)
(* CAG zero-dependent Axiom mat_neg_scale theories/Lie/SpecialLinear.v:323 BEGIN
Axiom mat_neg_scale : forall {F : Type} (fld : Field F) (c : F) (A : Matrix F),
    mat_neg fld (mat_scale fld c A) = mat_scale fld (fld.(cr_neg) c) A.
   CAG zero-dependent Axiom mat_neg_scale theories/Lie/SpecialLinear.v:323 END *)

(** ── Diagonal entries (all zero by alternating property) ─────── *)

(* CAG zero-dependent Lemma ad_sl2_X_X theories/Lie/SpecialLinear.v:342 BEGIN
Lemma ad_sl2_X_X {F : Type} (fld : Field F) :
    mat_bracket fld (sl2_X_mat fld) (sl2_X_mat fld) = mat_zero fld 2.
Proof. apply mat_bracket_alt_2. Qed.
   CAG zero-dependent Lemma ad_sl2_X_X theories/Lie/SpecialLinear.v:342 END *)

(* CAG zero-dependent Lemma ad_sl2_H_H theories/Lie/SpecialLinear.v:346 BEGIN
Lemma ad_sl2_H_H {F : Type} (fld : Field F) :
    mat_bracket fld (sl2_H_mat fld) (sl2_H_mat fld) = mat_zero fld 2.
Proof. apply mat_bracket_alt_2. Qed.
   CAG zero-dependent Lemma ad_sl2_H_H theories/Lie/SpecialLinear.v:346 END *)

(* CAG zero-dependent Lemma ad_sl2_Y_Y theories/Lie/SpecialLinear.v:350 BEGIN
Lemma ad_sl2_Y_Y {F : Type} (fld : Field F) :
    mat_bracket fld (sl2_Y_mat fld) (sl2_Y_mat fld) = mat_zero fld 2.
Proof. apply mat_bracket_alt_2. Qed.
   CAG zero-dependent Lemma ad_sl2_Y_Y theories/Lie/SpecialLinear.v:350 END *)

(** ── Off-diagonal entries ───────────────────────────────────────── *)

Local Notation two fld := (fld.(cr_add) fld.(cr_one) fld.(cr_one)).

(** [H, X] = 2X  (direct axiom) *)
(* CAG zero-dependent Lemma ad_sl2_H_X theories/Lie/SpecialLinear.v:359 BEGIN
Lemma ad_sl2_H_X {F : Type} (fld : Field F) :
    mat_bracket fld (sl2_H_mat fld) (sl2_X_mat fld) =
    mat_scale fld (two fld) (sl2_X_mat fld).
Proof. apply sl2_bracket_hx. Qed.
   CAG zero-dependent Lemma ad_sl2_H_X theories/Lie/SpecialLinear.v:359 END *)

(** [X, H] = -2X  (anticommutativity of [H,X]=2X) *)
(* CAG zero-dependent Lemma ad_sl2_X_H theories/Lie/SpecialLinear.v:351 BEGIN
Lemma ad_sl2_X_H {F : Type} (fld : Field F) :
    mat_bracket fld (sl2_X_mat fld) (sl2_H_mat fld) =
    mat_scale fld (fld.(cr_neg) (two fld)) (sl2_X_mat fld).
Proof.
  rewrite mat_bracket_anticomm_2, sl2_bracket_hx.
  apply mat_neg_scale.
Qed.
   CAG zero-dependent Lemma ad_sl2_X_H theories/Lie/SpecialLinear.v:351 END *)

(** [H, Y] = -2Y  (direct axiom) *)
(* CAG zero-dependent Lemma ad_sl2_H_Y theories/Lie/SpecialLinear.v:376 BEGIN
Lemma ad_sl2_H_Y {F : Type} (fld : Field F) :
    mat_bracket fld (sl2_H_mat fld) (sl2_Y_mat fld) =
    mat_scale fld (fld.(cr_neg) (two fld)) (sl2_Y_mat fld).
Proof. apply sl2_bracket_hy. Qed.
   CAG zero-dependent Lemma ad_sl2_H_Y theories/Lie/SpecialLinear.v:376 END *)

(** [Y, H] = 2Y  (anticommutativity of [H,Y]=-2Y; double negation cancels) *)
(* CAG zero-dependent Lemma ad_sl2_Y_H theories/Lie/SpecialLinear.v:366 BEGIN
Lemma ad_sl2_Y_H {F : Type} (fld : Field F) :
    mat_bracket fld (sl2_Y_mat fld) (sl2_H_mat fld) =
    mat_scale fld (two fld) (sl2_Y_mat fld).
Proof.
  rewrite mat_bracket_anticomm_2, sl2_bracket_hy.
  apply mat_neg_scale_neg.
Qed.
   CAG zero-dependent Lemma ad_sl2_Y_H theories/Lie/SpecialLinear.v:366 END *)

(** [X, Y] = H  (direct axiom) *)
(* CAG zero-dependent Lemma ad_sl2_X_Y theories/Lie/SpecialLinear.v:393 BEGIN
Lemma ad_sl2_X_Y {F : Type} (fld : Field F) :
    mat_bracket fld (sl2_X_mat fld) (sl2_Y_mat fld) = sl2_H_mat fld.
Proof. apply sl2_bracket_xy. Qed.
   CAG zero-dependent Lemma ad_sl2_X_Y theories/Lie/SpecialLinear.v:393 END *)

(** [Y, X] = -H  (anticommutativity of [X,Y]=H) *)
(* CAG zero-dependent Lemma ad_sl2_Y_X theories/Lie/SpecialLinear.v:398 BEGIN
Lemma ad_sl2_Y_X {F : Type} (fld : Field F) :
    mat_bracket fld (sl2_Y_mat fld) (sl2_X_mat fld) =
    mat_neg fld (sl2_H_mat fld).
Proof.
  rewrite mat_bracket_anticomm_2, sl2_bracket_xy. reflexivity.
Qed.
   CAG zero-dependent Lemma ad_sl2_Y_X theories/Lie/SpecialLinear.v:398 END *)

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

(* ================================================================== *)
(** * Exercise 2.2: [gl(n,F), gl(n,F)] = sl(n,F)                      *)
(* ================================================================== *)

Require Import CAG.Lie.Solvable.

(** sl(n,F) is an ideal of gl(n,F) (not just a subalgebra).
    For any A ∈ gl, B ∈ sl: Tr([A,B]) = 0 by mat_trace_bracket_zero. *)
(* CAG zero-dependent Lemma sl_is_ideal theories/Lie/SpecialLinear.v:444 BEGIN
Lemma sl_is_ideal : forall {F : Type} (fld : Field F) (n : nat),
    IsIdeal (gl fld n) (IsTracezero fld).
Proof.
  intros F fld n. constructor.
  - (* zero *)
    unfold IsTracezero.
    rewrite gl_zero_eq_mat_zero. apply mat_trace_zero.
  - (* add *)
    intros A B HA HB. unfold IsTracezero in *.
    rewrite gl_add_eq_mat_add, mat_trace_add, HA, HB.
    apply fld.(cr_add_zero).
  - (* neg *)
    intros A HA. unfold IsTracezero in *.
    rewrite gl_neg_eq_mat_neg. unfold mat_neg.
    rewrite mat_trace_scale. rewrite HA. apply ring_mul_zero_r.
  - (* scale *)
    intros c A HA. unfold IsTracezero in *.
    rewrite gl_scale_eq_mat_scale, mat_trace_scale, HA.
    apply ring_mul_zero_r.
  - (* bracket_l: for any B ∈ gl and A ∈ sl, Tr([B,A]) = 0 *)
    intros B A _.
    unfold IsTracezero.
    rewrite gl_bracket_eq_mat_bracket.
    apply mat_trace_bracket_zero.
Qed.
   CAG zero-dependent Lemma sl_is_ideal theories/Lie/SpecialLinear.v:444 END *)

(** Forward inclusion: IsDerivedAlg (gl n) ⊆ IsTracezero.
    Proof: IsTracezero is a subalgebra containing all brackets (by
    mat_trace_bracket_zero), so by definition of IsDerivedAlg every
    element of the derived algebra is traceless. *)
(* CAG zero-dependent Lemma gl_derived_sub_sl theories/Lie/SpecialLinear.v:474 BEGIN
Lemma gl_derived_sub_sl : forall {F : Type} (fld : Field F) (n : nat) (A : Matrix F),
    IsDerivedAlg (gl fld n) A -> IsTracezero fld A.
Proof.
  intros F fld n A Hderiv.
  apply Hderiv.
  - apply sl_is_subalgebra.
  - intros X Y. unfold IsTracezero.
    rewrite gl_bracket_eq_mat_bracket.
    apply mat_trace_bracket_zero.
Qed.
   CAG zero-dependent Lemma gl_derived_sub_sl theories/Lie/SpecialLinear.v:474 END *)

(** Backward inclusion: IsTracezero ⊆ IsDerivedAlg (gl n).
    Every traceless matrix is a linear combination of commutators:
    - e_{ij} = [e_{ij}, e_{jj}] for i ≠ j
    - h_i = e_{ii} - e_{i+1,i+1} = [e_{i,i+1}, e_{i+1,i}]
    The spanning argument requires finite-dimensionality.
    Stated as an axiom pending a full finite-dimensional framework. *)
(* CAG zero-dependent Axiom gl_sl_sub_derived theories/Lie/SpecialLinear.v:473 BEGIN
Axiom gl_sl_sub_derived : forall {F : Type} (fld : Field F) (n : nat) (A : Matrix F),
    IsTracezero fld A -> IsDerivedAlg (gl fld n) A.
   CAG zero-dependent Axiom gl_sl_sub_derived theories/Lie/SpecialLinear.v:473 END *)

(** Main theorem: [gl(n,F), gl(n,F)] = sl(n,F).  (Exercise 2.2) *)
(* CAG zero-dependent Theorem gl_derived_eq_sl theories/Lie/SpecialLinear.v:477 BEGIN
Theorem gl_derived_eq_sl : forall {F : Type} (fld : Field F) (n : nat) (A : Matrix F),
    IsDerivedAlg (gl fld n) A <-> IsTracezero fld A.
Proof.
  intros F fld n A. split.
  - apply gl_derived_sub_sl.
  - apply gl_sl_sub_derived.
Qed.
   CAG zero-dependent Theorem gl_derived_eq_sl theories/Lie/SpecialLinear.v:477 END *)

(* ================================================================== *)
(** * 5. Compatibility of abstract Jordan decomposition with matrices   *)
(* ================================================================== *)

(** mat_mul_inv: axiomatized matrix inverse (requires non-singularity). *)
(* CAG zero-dependent Axiom mat_mul_inv theories/Lie/SpecialLinear.v:490 BEGIN
Axiom mat_mul_inv : forall {F : Type} (fld : Field F) (n : nat), Matrix F -> Matrix F.
   CAG zero-dependent Axiom mat_mul_inv theories/Lie/SpecialLinear.v:490 END *)

(** mat_pow: iterated matrix multiplication. *)
Fixpoint mat_pow {F : Type} (fld : Field F) (A : Matrix F) (k : nat) : Matrix F :=
  match k with
  | O   => mat_unit fld (List.length A) 0 0  (* identity — placeholder *)
  | S k => mat_mul fld A (mat_pow fld A k)
  end.

(** A matrix D is diagonal if all off-diagonal entries are zero. *)
Definition IsDiagonalMatrix {F : Type} (fld : Field F) (D : Matrix F) : Prop :=
  forall i j, i <> j -> i < List.length D ->
    List.nth j (List.nth i D []) fld.(cr_zero) = fld.(cr_zero).

(** A matrix A ∈ gl(n,F) is diagonalizable (semisimple as a matrix)
    if it is similar to a diagonal matrix over F. *)
(* CAG zero-dependent Definition IsMatDiagonalizable theories/Lie/SpecialLinear.v:506 BEGIN
Definition IsMatDiagonalizable {F : Type} (fld : Field F) (n : nat) (A : Matrix F) : Prop :=
  exists (P D : Matrix F),
    mat_mul fld P (mat_mul fld D (mat_mul_inv fld n P)) = A /\
    IsDiagonalMatrix fld D.
   CAG zero-dependent Definition IsMatDiagonalizable theories/Lie/SpecialLinear.v:506 END *)

(** A matrix N ∈ gl(n,F) is nilpotent as a matrix if N^k = 0 for some k. *)
Definition IsMatNilpotent {F : Type} (fld : Field F) (n : nat) (N : Matrix F) : Prop :=
  exists k : nat, mat_pow fld N k = mat_zero fld n.

(** Classical Jordan decomposition for matrices: every A ∈ gl(n,F) (over an
    algebraically closed field) has a unique decomposition A = S + N where
    - S is diagonalizable (semisimple)
    - N is nilpotent
    - SN = NS
    Axiomatized: requires eigenvalue theory over algebraically closed fields. *)
(* CAG zero-dependent Axiom mat_jordan_decomp theories/Lie/SpecialLinear.v:514 BEGIN
Axiom mat_jordan_decomp :
  forall {F : Type} (fld : Field F) (n : nat) (A : Matrix F),
    exists (S N : Matrix F),
      A = mat_add fld S N /\
      IsMatDiagonalizable fld n S /\
      IsMatNilpotent fld n N /\
      mat_mul fld S N = mat_mul fld N S.
   CAG zero-dependent Axiom mat_jordan_decomp theories/Lie/SpecialLinear.v:514 END *)

(** Compatibility: the abstract Jordan decomposition in sl(n,F) (from Semisimple.v)
    agrees with the classical matrix Jordan decomposition.

    Specifically: if x ∈ sl(n,F) has abstract Jordan parts (s, n) as in
    abstract_jordan, then s is the diagonalizable part and n is the nilpotent
    part of the classical matrix Jordan decomposition of x.

    Axiomatized: requires the isomorphism ad : sl(n,F) → ad(sl(n,F)) ⊆ End(sl)
    and compatibility of ad-semisimple with matrix-semisimple. *)
(* CAG zero-dependent Axiom sl_jordan_agrees_matrix theories/Lie/SpecialLinear.v:531 BEGIN
Axiom sl_jordan_agrees_matrix :
  forall {F : Type} (fld : Field F) (n : nat) (x s nu : Matrix F),
    IsTracezero fld x ->
    x = mat_add fld s nu ->
    IsAdNilpotent (gl fld n) nu ->
    laF_bracket (gl fld n) s nu = mat_zero fld n ->
    (** s is the diagonalizable part of x *)
    IsMatDiagonalizable fld n s /\
    (** nu is the nilpotent part of x *)
    IsMatNilpotent fld n nu.
   CAG zero-dependent Axiom sl_jordan_agrees_matrix theories/Lie/SpecialLinear.v:531 END *)
