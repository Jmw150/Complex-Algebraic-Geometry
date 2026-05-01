(** * LinAlg/Matrix2.v
    Concrete 2x2 matrices over a field F as 4-tuples.

    Layout: M = (a, b, c, d) represents the matrix
        [a  b]
        [c  d]

    This is needed for [G1] in DecisionProblems/OpenProblems.v: build
    SL(2, F) as a concrete MatrixGroup so that the Horowitz n=2
    boundary becomes formally accessible. *)

Require Import CAG.Galois.Field.
From Stdlib Require Import Ring Setoid.

Section Matrix2.
  Context {F : Type} (fld : Field F).

  Local Lemma m2_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring m2_ring : m2_ring_theory.

  Definition Mat2 : Type := F * F * F * F.

  Definition mat2_a (M : Mat2) : F := let '(a, _, _, _) := M in a.
  Definition mat2_b (M : Mat2) : F := let '(_, b, _, _) := M in b.
  Definition mat2_c (M : Mat2) : F := let '(_, _, c, _) := M in c.
  Definition mat2_d (M : Mat2) : F := let '(_, _, _, d) := M in d.

  Definition mat2_mk (a b c d : F) : Mat2 := (a, b, c, d).

  Definition mat2_id : Mat2 :=
    mat2_mk (cr_one fld) (cr_zero fld) (cr_zero fld) (cr_one fld).

  Definition mat2_zero : Mat2 :=
    mat2_mk (cr_zero fld) (cr_zero fld) (cr_zero fld) (cr_zero fld).

  Definition mat2_mul (M N : Mat2) : Mat2 :=
    let '(a, b, c, d) := M in
    let '(a', b', c', d') := N in
    mat2_mk
      (cr_add fld (cr_mul fld a a') (cr_mul fld b c'))
      (cr_add fld (cr_mul fld a b') (cr_mul fld b d'))
      (cr_add fld (cr_mul fld c a') (cr_mul fld d c'))
      (cr_add fld (cr_mul fld c b') (cr_mul fld d d')).

  Definition mat2_add (M N : Mat2) : Mat2 :=
    let '(a, b, c, d) := M in
    let '(a', b', c', d') := N in
    mat2_mk (cr_add fld a a') (cr_add fld b b')
            (cr_add fld c c') (cr_add fld d d').

  Definition mat2_neg (M : Mat2) : Mat2 :=
    let '(a, b, c, d) := M in
    mat2_mk (cr_neg fld a) (cr_neg fld b) (cr_neg fld c) (cr_neg fld d).

  Definition mat2_scale (k : F) (M : Mat2) : Mat2 :=
    let '(a, b, c, d) := M in
    mat2_mk (cr_mul fld k a) (cr_mul fld k b)
            (cr_mul fld k c) (cr_mul fld k d).

  Definition mat2_det (M : Mat2) : F :=
    let '(a, b, c, d) := M in
    cr_sub fld (cr_mul fld a d) (cr_mul fld b c).

  Definition mat2_trace (M : Mat2) : F :=
    let '(a, _, _, d) := M in cr_add fld a d.

  (** Adjugate (cofactor transpose). *)
  Definition mat2_adj (M : Mat2) : Mat2 :=
    let '(a, b, c, d) := M in
    mat2_mk d (cr_neg fld b) (cr_neg fld c) a.

  (** Inverse: only valid when det ≠ 0. *)
  Definition mat2_inv (M : Mat2) : Mat2 :=
    let det := mat2_det M in
    let inv_det := fld.(fld_inv) det in
    mat2_scale inv_det (mat2_adj M).

  (* ============================================================ *)
  (** ** Basic algebraic facts                                      *)
  (* ============================================================ *)

  Lemma mat2_mul_id_l : forall M, mat2_mul mat2_id M = M.
  Proof.
    intros [[[a b] c] d]. unfold mat2_mul, mat2_id, mat2_mk.
    apply f_equal2; [apply f_equal2; [apply f_equal2|]|]; ring.
  Qed.

  Lemma mat2_mul_id_r : forall M, mat2_mul M mat2_id = M.
  Proof.
    intros [[[a b] c] d]. unfold mat2_mul, mat2_id, mat2_mk.
    apply f_equal2; [apply f_equal2; [apply f_equal2|]|]; ring.
  Qed.

  Lemma mat2_mul_assoc : forall M N P,
      mat2_mul M (mat2_mul N P) = mat2_mul (mat2_mul M N) P.
  Proof.
    intros [[[a1 b1] c1] d1] [[[a2 b2] c2] d2] [[[a3 b3] c3] d3].
    unfold mat2_mul, mat2_mk.
    apply f_equal2; [apply f_equal2; [apply f_equal2|]|]; ring.
  Qed.

  Lemma mat2_det_id : mat2_det mat2_id = cr_one fld.
  Proof. unfold mat2_det, mat2_id, mat2_mk. ring. Qed.

  Lemma mat2_det_mul : forall M N,
      mat2_det (mat2_mul M N) = cr_mul fld (mat2_det M) (mat2_det N).
  Proof.
    intros [[[a1 b1] c1] d1] [[[a2 b2] c2] d2].
    unfold mat2_det, mat2_mul, mat2_mk. ring.
  Qed.

  Lemma mat2_trace_id : mat2_trace mat2_id =
                       cr_add fld (cr_one fld) (cr_one fld).
  Proof. unfold mat2_trace, mat2_id, mat2_mk. reflexivity. Qed.

  (** Trace cyclicity. *)
  Lemma mat2_trace_cyclic : forall M N,
      mat2_trace (mat2_mul M N) = mat2_trace (mat2_mul N M).
  Proof.
    intros [[[a1 b1] c1] d1] [[[a2 b2] c2] d2].
    unfold mat2_trace, mat2_mul, mat2_mk. ring.
  Qed.

  (** Adjugate-times-matrix = det · I. *)
  Lemma mat2_adj_mul : forall M,
      mat2_mul (mat2_adj M) M = mat2_scale (mat2_det M) mat2_id.
  Proof.
    intros [[[a b] c] d].
    unfold mat2_adj, mat2_mul, mat2_det, mat2_scale, mat2_id, mat2_mk.
    apply f_equal2; [apply f_equal2; [apply f_equal2|]|]; ring.
  Qed.

  Lemma mat2_mul_adj : forall M,
      mat2_mul M (mat2_adj M) = mat2_scale (mat2_det M) mat2_id.
  Proof.
    intros [[[a b] c] d].
    unfold mat2_adj, mat2_mul, mat2_det, mat2_scale, mat2_id, mat2_mk.
    apply f_equal2; [apply f_equal2; [apply f_equal2|]|]; ring.
  Qed.

  (** When det M = 1, the adjugate is the inverse. *)
  Lemma mat2_adj_is_inv_det1 : forall M,
      mat2_det M = cr_one fld ->
      mat2_mul M (mat2_adj M) = mat2_id.
  Proof.
    intros M HM. rewrite mat2_mul_adj, HM.
    unfold mat2_scale, mat2_id, mat2_mk.
    apply f_equal2; [apply f_equal2; [apply f_equal2|]|]; ring.
  Qed.

  Lemma mat2_adj_is_inv_det1_l : forall M,
      mat2_det M = cr_one fld ->
      mat2_mul (mat2_adj M) M = mat2_id.
  Proof.
    intros M HM. rewrite mat2_adj_mul, HM.
    unfold mat2_scale, mat2_id, mat2_mk.
    apply f_equal2; [apply f_equal2; [apply f_equal2|]|]; ring.
  Qed.

  (** Adjugate of a det-1 matrix has det 1 too. *)
  Lemma mat2_det_adj_det1 : forall M,
      mat2_det M = cr_one fld ->
      mat2_det (mat2_adj M) = cr_one fld.
  Proof.
    intros [[[a b] c] d] HM.
    unfold mat2_det, mat2_adj, mat2_mk in *. cbn in *.
    rewrite <- HM. ring.
  Qed.

End Matrix2.

Arguments Mat2 _ : clear implicits.
Arguments mat2_mk {F} _ _ _ _.
Arguments mat2_id {F} _.
Arguments mat2_zero {F} _.
Arguments mat2_mul {F} _ _ _.
Arguments mat2_add {F} _ _ _.
Arguments mat2_neg {F} _ _.
Arguments mat2_scale {F} _ _ _.
Arguments mat2_det {F} _ _.
Arguments mat2_trace {F} _ _.
Arguments mat2_adj {F} _ _.
Arguments mat2_inv {F} _ _.
