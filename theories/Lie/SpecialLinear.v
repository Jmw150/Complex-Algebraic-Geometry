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
From Stdlib Require Import List Arith Bool Lia.
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

(** Helper: nth k of (combine r1 r2 |> map cr_add) = cr_add (nth k r1) (nth k r2),
    when |r1| = |r2|. *)
Lemma nth_map_add_combine :
  forall {F : Type} (fld : Field F) (r1 r2 : list F) (k : nat),
    List.length r1 = List.length r2 ->
    List.nth k (List.map (fun '(a, b) => cr_add fld a b) (List.combine r1 r2)) (cr_zero fld) =
    cr_add fld (List.nth k r1 (cr_zero fld)) (List.nth k r2 (cr_zero fld)).
Proof.
  intros F fld r1. induction r1 as [|x r1 IH]; intros r2 k Hlen.
  - destruct r2; [|discriminate]. simpl. destruct k; rewrite cr_add_zero; reflexivity.
  - destruct r2 as [|y r2]; [discriminate|]. simpl in *. injection Hlen as Hlen.
    destruct k as [|k']; [reflexivity|]. apply IH. exact Hlen.
Qed.

(** Helper: trace_aux distributes over mat_add when same length and uniform row length. *)
Lemma mat_trace_aux_add :
  forall {F : Type} (fld : Field F) (As Bs : Matrix F) (k : nat),
    List.length As = List.length Bs ->
    (forall ra rb, List.In (ra, rb) (List.combine As Bs) ->
                   List.length ra = List.length rb) ->
    mat_trace_aux fld (mat_add fld As Bs) k =
    cr_add fld (mat_trace_aux fld As k) (mat_trace_aux fld Bs k).
Proof.
  intros F fld As. unfold mat_add. induction As as [|rA As IH]; intros Bs k Hlen Hrows.
  - destruct Bs; [|discriminate]. simpl. rewrite cr_add_zero. reflexivity.
  - destruct Bs as [|rB Bs]; [discriminate|]. simpl in Hlen. injection Hlen as Hlen.
    simpl.
    rewrite IH; [|exact Hlen|].
    + assert (Hrlen : List.length rA = List.length rB).
      { apply Hrows. left. reflexivity. }
      rewrite (nth_map_add_combine fld rA rB k Hrlen).
      set (a := List.nth k rA (cr_zero fld)).
      set (b := List.nth k rB (cr_zero fld)).
      set (sA := mat_trace_aux fld As (S k)).
      set (sB := mat_trace_aux fld Bs (S k)).
      (* (a + b) + (sA + sB) = (a + sA) + (b + sB) *)
      rewrite <- (cr_add_assoc fld a b (cr_add fld sA sB)).
      rewrite (cr_add_assoc fld b sA sB).
      rewrite (cr_add_comm fld b sA).
      rewrite <- (cr_add_assoc fld sA b sB).
      rewrite (cr_add_assoc fld a sA (cr_add fld b sB)).
      reflexivity.
    + intros ra rb Hin. apply Hrows. right. exact Hin.
Qed.

(** Tr(A + B) = Tr(A) + Tr(B). Strengthened with [Mat_wf] hypotheses
    (Task M.1, 2026-04-30): the original unhypothesised statement was
    FALSE for mismatched shapes (mat_add truncates via List.combine).
    Discharged 2026-05-01 (Task M.1, α R2): real lemma now,
    via [mat_trace_aux_add] helper. *)
Lemma mat_trace_add : forall {F : Type} (fld : Field F) (n : nat) (A B : Matrix F),
    Mat_wf n n A -> Mat_wf n n B ->
    mat_trace fld (mat_add fld A B) =
    fld.(cr_add) (mat_trace fld A) (mat_trace fld B).
Proof.
  intros F fld n A B [HlenA HrowA] [HlenB HrowB].
  unfold mat_trace.
  apply mat_trace_aux_add.
  - rewrite HlenA, HlenB. reflexivity.
  - intros ra rb Hin.
    pose proof (List.in_combine_l _ _ _ _ Hin) as Hra.
    pose proof (List.in_combine_r _ _ _ _ Hin) as Hrb.
    rewrite (HrowA _ Hra), (HrowB _ Hrb). reflexivity.
Qed.

(** Helper: nth of a scaled list is the scaled nth. *)
Lemma nth_map_scale : forall {F : Type} (fld : Field F) (c : F)
    (row : list F) (k : nat),
    List.nth k (List.map (fun x => cr_mul fld c x) row) (cr_zero fld) =
    cr_mul fld c (List.nth k row (cr_zero fld)).
Proof.
  intros F fld c row. induction row as [|x row IH]; intro k.
  - simpl. destruct k; rewrite cr_mul_zero_r; reflexivity.
  - destruct k as [|k']; simpl.
    + reflexivity.
    + apply IH.
Qed.

(** Helper: trace_aux of a scaled matrix. *)
Lemma mat_trace_aux_scale : forall {F : Type} (fld : Field F) (c : F)
    (rows : list (list F)) (k : nat),
    mat_trace_aux fld (List.map (fun row => List.map (fun x => cr_mul fld c x) row) rows) k =
    cr_mul fld c (mat_trace_aux fld rows k).
Proof.
  intros F fld c rows. induction rows as [|row rest IH]; intro k.
  - simpl. rewrite cr_mul_zero_r. reflexivity.
  - simpl. rewrite IH. rewrite nth_map_scale.
    rewrite cr_distrib. reflexivity.
Qed.

(** Tr(c·A) = c · Tr(A). *)
Lemma mat_trace_scale : forall {F : Type} (fld : Field F) (c : F) (A : Matrix F),
    mat_trace fld (mat_scale fld c A) =
    fld.(cr_mul) c (mat_trace fld A).
Proof.
  intros. unfold mat_trace, mat_scale. apply mat_trace_aux_scale.
Qed.

(** Helper: nth of a repeated zero list is zero. *)
Lemma nth_repeat_zero : forall {F : Type} (fld : Field F) (m j : nat),
    List.nth j (List.repeat fld.(cr_zero) m) fld.(cr_zero) = fld.(cr_zero).
Proof.
  intros F fld m. induction m as [|m IH]; intro j.
  - destruct j; reflexivity.
  - destruct j as [|j']; [reflexivity | apply IH].
Qed.

(** Helper: trace of a list of all-zero rows is zero. *)
Lemma mat_trace_aux_zeros : forall {F : Type} (fld : Field F) (k m j : nat),
    mat_trace_aux fld (List.repeat (List.repeat fld.(cr_zero) m) k) j = fld.(cr_zero).
Proof.
  intros F fld k m. induction k as [|k IH]; intro j.
  - reflexivity.
  - simpl. rewrite IH.
    rewrite (cr_add_zero fld).
    apply nth_repeat_zero.
Qed.

(** Tr(0) = 0. *)
Lemma mat_trace_zero : forall {F : Type} (fld : Field F) (n : nat),
    mat_trace fld (mat_zero fld n) = fld.(cr_zero).
Proof.
  intros. unfold mat_trace, mat_zero. apply mat_trace_aux_zeros.
Qed.

(** REFACTOR (Task M.1, 2026-04-30): These bridge lemmas now project
    out of the sigma-typed carrier [GLMat fld n = { A | Mat_wf n n A }].
    Each is a definitional equality (matches [gl_zero / gl_add / ...]
    via the [exist _ ...] pattern), so all proofs are [reflexivity]. *)

(** [proj1_sig (la_zero (gl fld n)) = mat_zero fld n] — discharged
    (was Admitted in the pre-M.0 codebase). *)
Lemma gl_zero_eq_mat_zero : forall {F : Type} (fld : Field F) (n : nat),
    proj1_sig (la_zero (gl fld n)) = mat_zero fld n.
Proof. intros. reflexivity. Qed.

(** Addition projects to [mat_add]. *)
Lemma gl_add_eq_mat_add : forall {F : Type} (fld : Field F) (n : nat) (A B : GLMat fld n),
    proj1_sig (la_add (gl fld n) A B) = mat_add fld (proj1_sig A) (proj1_sig B).
Proof. intros. reflexivity. Qed.

(** Negation projects to [mat_neg]. *)
Lemma gl_neg_eq_mat_neg : forall {F : Type} (fld : Field F) (n : nat) (A : GLMat fld n),
    proj1_sig (la_neg (gl fld n) A) = mat_neg fld (proj1_sig A).
Proof. intros. reflexivity. Qed.

(** Scalar multiplication projects to [mat_scale]. *)
Lemma gl_scale_eq_mat_scale : forall {F : Type} (fld : Field F) (n : nat) (c : F) (A : GLMat fld n),
    proj1_sig (la_scale (gl fld n) c A) = mat_scale fld c (proj1_sig A).
Proof. intros. reflexivity. Qed.

(** The bracket projects to [mat_bracket]. *)
Lemma gl_bracket_eq_mat_bracket : forall {F : Type} (fld : Field F) (n : nat) (A B : GLMat fld n),
    proj1_sig (laF_bracket (gl fld n) A B) = mat_bracket fld (proj1_sig A) (proj1_sig B).
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(** ** Helpers for [mat_trace_cyclic] (Task M.1.next, 2026-05-01)        *)
(* ================================================================== *)

(** A start-offset cumulative sum that mirrors the recursion of
    [mat_trace_aux].  Reads [f start], [f (S start)], ..., [f (start+n-1)]
    and returns the right-associated sum
    [f start + (f (S start) + (... + (f (start+n-1) + 0)))]. *)
Fixpoint sum_seq_aux {F : Type} (fld : Field F) (f : nat -> F) (start n : nat) : F :=
  match n with
  | O => cr_zero fld
  | S k => cr_add fld (f start) (sum_seq_aux fld f (S start) k)
  end.

(** Sum starting at 0. *)
Definition sum_seq {F : Type} (fld : Field F) (f : nat -> F) (n : nat) : F :=
  sum_seq_aux fld f 0 n.

(** Extensionality. *)
Lemma sum_seq_aux_ext :
  forall {F : Type} (fld : Field F) (f g : nat -> F) (start n : nat),
    (forall i, start <= i < start + n -> f i = g i) ->
    sum_seq_aux fld f start n = sum_seq_aux fld g start n.
Proof.
  intros F fld f g start n. revert start.
  induction n as [|n IH]; intros start Hext; [reflexivity|].
  simpl. f_equal.
  - apply Hext. lia.
  - apply IH. intros i Hi. apply Hext. lia.
Qed.

Lemma sum_seq_ext :
  forall {F : Type} (fld : Field F) (f g : nat -> F) (n : nat),
    (forall i, i < n -> f i = g i) ->
    sum_seq fld f n = sum_seq fld g n.
Proof.
  intros F fld f g n Hext. unfold sum_seq.
  apply sum_seq_aux_ext. intros i Hi. apply Hext. lia.
Qed.

(** Sum of constant zero is zero. *)
Lemma sum_seq_aux_zero :
  forall {F : Type} (fld : Field F) (start n : nat),
    sum_seq_aux fld (fun _ => cr_zero fld) start n = cr_zero fld.
Proof.
  intros F fld start n. revert start.
  induction n as [|n IH]; intro start; [reflexivity|].
  simpl. rewrite IH. apply cr_add_zero.
Qed.

Lemma sum_seq_zero :
  forall {F : Type} (fld : Field F) (n : nat),
    sum_seq fld (fun _ => cr_zero fld) n = cr_zero fld.
Proof. intros. unfold sum_seq. apply sum_seq_aux_zero. Qed.

(** Sum is additive in [f]. *)
Lemma sum_seq_aux_add :
  forall {F : Type} (fld : Field F) (f g : nat -> F) (start n : nat),
    sum_seq_aux fld (fun i => cr_add fld (f i) (g i)) start n =
    cr_add fld (sum_seq_aux fld f start n) (sum_seq_aux fld g start n).
Proof.
  intros F fld f g start n. revert start.
  induction n as [|n IH]; intro start.
  - simpl. rewrite cr_add_zero. reflexivity.
  - simpl. rewrite IH.
    set (a := f start). set (b := g start).
    set (sf := sum_seq_aux fld f (S start) n).
    set (sg := sum_seq_aux fld g (S start) n).
    (* (a + b) + (sf + sg) = (a + sf) + (b + sg) *)
    rewrite <- (cr_add_assoc fld a b (cr_add fld sf sg)).
    rewrite (cr_add_assoc fld b sf sg).
    rewrite (cr_add_comm fld b sf).
    rewrite <- (cr_add_assoc fld sf b sg).
    rewrite (cr_add_assoc fld a sf (cr_add fld b sg)).
    reflexivity.
Qed.

Lemma sum_seq_add :
  forall {F : Type} (fld : Field F) (f g : nat -> F) (n : nat),
    sum_seq fld (fun i => cr_add fld (f i) (g i)) n =
    cr_add fld (sum_seq fld f n) (sum_seq fld g n).
Proof. intros. unfold sum_seq. apply sum_seq_aux_add. Qed.

(** Re-indexing: shift the start by 1 by re-indexing [f]. *)
Lemma sum_seq_aux_shift :
  forall {F : Type} (fld : Field F) (f : nat -> F) (start n : nat),
    sum_seq_aux fld f (S start) n = sum_seq_aux fld (fun i => f (S i)) start n.
Proof.
  intros F fld f start n. revert start f.
  induction n as [|n IH]; intros start f; [reflexivity|].
  simpl. f_equal. apply IH.
Qed.

(** Reduce sum_seq_aux to sum_seq via shifting. *)
Lemma sum_seq_aux_as_sum_seq :
  forall {F : Type} (fld : Field F) (f : nat -> F) (start n : nat),
    sum_seq_aux fld f start n = sum_seq fld (fun i => f (start + i)) n.
Proof.
  intros F fld f start n. revert start f.
  induction n as [|n IH]; intros start f; [reflexivity|].
  simpl. unfold sum_seq. simpl.
  rewrite Nat.add_0_r. f_equal.
  rewrite (IH (S start) f).
  unfold sum_seq.
  rewrite sum_seq_aux_shift.
  apply sum_seq_aux_ext. intros i _. f_equal. lia.
Qed.

(** Single-step accumulator: pull the [n]-th term out. *)
Lemma sum_seq_S :
  forall {F : Type} (fld : Field F) (f : nat -> F) (n : nat),
    sum_seq fld f (S n) =
    cr_add fld (sum_seq fld f n) (f n).
Proof.
  intros F fld f n. unfold sum_seq.
  revert f. induction n as [|n IH]; intro f.
  - simpl. rewrite (cr_add_zero fld). rewrite (cr_add_zero_l fld).
    reflexivity.
  - change (sum_seq_aux fld f 0 (S (S n)))
      with (cr_add fld (f 0) (sum_seq_aux fld f 1 (S n))).
    rewrite sum_seq_aux_shift.
    change (sum_seq_aux fld f 0 (S n))
      with (cr_add fld (f 0) (sum_seq_aux fld f 1 n)).
    rewrite sum_seq_aux_shift.
    rewrite (IH (fun i => f (S i))).
    rewrite <- (cr_add_assoc fld (f 0) _ _).
    reflexivity.
Qed.

(** Fubini: swap order of summation over a rectangle. *)
Lemma sum_seq_swap :
  forall {F : Type} (fld : Field F) (f : nat -> nat -> F) (n m : nat),
    sum_seq fld (fun i => sum_seq fld (fun j => f i j) m) n =
    sum_seq fld (fun j => sum_seq fld (fun i => f i j) n) m.
Proof.
  intros F fld f n m. revert f m.
  induction n as [|n IH]; intros f m.
  - (* n = 0: LHS = 0; RHS = sum_seq (fun _ => 0) m = 0. *)
    unfold sum_seq at 1. simpl.
    symmetry. apply sum_seq_zero.
  - (* sum_seq (S n) f = sum_seq n f + f n *)
    rewrite (sum_seq_S fld _ n).
    rewrite (IH (fun i => f i) m).
    rewrite <- (sum_seq_add fld
                 (fun j => sum_seq fld (fun i => f i j) n)
                 (fun j => f n j) m).
    apply sum_seq_ext. intros j Hj.
    rewrite (sum_seq_S fld (fun i => f i j) n). reflexivity.
Qed.

(** Trace_aux as sum_seq_aux: the [k]-th iterate reads the [(start+k)]-th
    column entry of the [k]-th row. *)
Lemma mat_trace_aux_as_sum_seq :
  forall {F : Type} (fld : Field F) (M : Matrix F) (start : nat),
    mat_trace_aux fld M start =
    sum_seq fld (fun i => List.nth (start + i) (List.nth i M []) (cr_zero fld))
            (List.length M).
Proof.
  intros F fld M. induction M as [|row M IH]; intro start.
  - reflexivity.
  - cbn [List.length mat_trace_aux]. unfold sum_seq. simpl sum_seq_aux. cbv beta.
    rewrite Nat.add_0_r. simpl List.nth at 1. f_equal.
    rewrite (IH (S start)).
    unfold sum_seq.
    rewrite sum_seq_aux_shift.
    apply sum_seq_aux_ext. intros i _. cbv beta.
    replace (start + S i) with (S start + i) by lia.
    reflexivity.
Qed.

(** Trace as sum_seq with start=0. *)
Lemma mat_trace_as_sum_seq :
  forall {F : Type} (fld : Field F) (M : Matrix F),
    mat_trace fld M =
    sum_seq fld (fun i => List.nth i (List.nth i M []) (cr_zero fld))
            (List.length M).
Proof.
  intros F fld M. unfold mat_trace.
  rewrite (mat_trace_aux_as_sum_seq fld M 0).
  apply sum_seq_ext. intros i _. simpl. reflexivity.
Qed.

(** Fold_left expressed via sum_seq_aux: when we fold a (combine row B) for
    a [c]-column dot-product starting at accumulator [init], the result is
    [init + sum_{j in [0, min(|row|,|B|))} (nth j row · nth col_idx (nth j B))]. *)
Lemma fold_left_dot_init :
  forall {F : Type} (fld : Field F) (row : list F) (B : list (list F))
         (col_idx : nat) (init : F),
    fold_left (fun acc '(a, row_B) =>
        cr_add fld acc (cr_mul fld a (List.nth col_idx row_B (cr_zero fld))))
      (List.combine row B) init =
    cr_add fld init
      (sum_seq fld
        (fun j => cr_mul fld (List.nth j row (cr_zero fld))
                              (List.nth col_idx (List.nth j B []) (cr_zero fld)))
        (Nat.min (List.length row) (List.length B))).
Proof.
  intros F fld row B col_idx init.
  revert row B init.
  induction row as [|x row IH]; intros B init.
  - simpl List.combine. simpl fold_left. simpl List.length.
    simpl Nat.min. unfold sum_seq. simpl sum_seq_aux.
    rewrite (cr_add_zero fld). reflexivity.
  - destruct B as [|row_B B'].
    + (* combine (x::row) [] = [] *)
      simpl List.combine. simpl fold_left.
      simpl List.length. rewrite Nat.min_0_r.
      unfold sum_seq. simpl sum_seq_aux. rewrite (cr_add_zero fld). reflexivity.
    + simpl List.length. simpl List.combine. simpl fold_left.
      simpl Nat.min.
      rewrite IH.
      unfold sum_seq. simpl sum_seq_aux.
      simpl List.nth at 1 2.
      cbv beta.
      rewrite (cr_add_assoc fld init _ _).
      f_equal.
      rewrite sum_seq_aux_shift.
      apply sum_seq_aux_ext. intros j _. cbv beta. simpl List.nth.
      reflexivity.
Qed.

(** Specialised to the [init = 0] case used by [mat_mul]. *)
Lemma fold_left_dot_as_sum_seq :
  forall {F : Type} (fld : Field F) (row : list F) (B : list (list F))
         (col_idx : nat),
    fold_left (fun acc '(a, row_B) =>
        cr_add fld acc (cr_mul fld a (List.nth col_idx row_B (cr_zero fld))))
      (List.combine row B) (cr_zero fld) =
    sum_seq fld
      (fun j => cr_mul fld (List.nth j row (cr_zero fld))
                            (List.nth col_idx (List.nth j B []) (cr_zero fld)))
      (Nat.min (List.length row) (List.length B)).
Proof.
  intros F fld row B col_idx.
  rewrite (fold_left_dot_init fld row B col_idx (cr_zero fld)).
  apply (cr_add_zero_l fld).
Qed.

(** The (r,c) entry of [mat_mul A B] as a sum over j of A[r,j] · B[j,c],
    for square n×n matrices. *)
Lemma mat_mul_entry_sum :
  forall {F : Type} (fld : Field F) (n : nat) (A B : Matrix F)
         (r c : nat),
    Mat_wf n n A -> Mat_wf n n B ->
    r < n -> c < n ->
    List.nth c (List.nth r (mat_mul fld A B) []) (cr_zero fld) =
    sum_seq fld
      (fun j => cr_mul fld (List.nth j (List.nth r A []) (cr_zero fld))
                            (List.nth c (List.nth j B []) (cr_zero fld)))
      n.
Proof.
  intros F fld n A B r c [HlenA HrowA] [HlenB HrowB] Hr Hc.
  rewrite (mat_mul_row fld A B r); [|lia].
  (* Row of mat_mul: map (fun col_idx => fold_left ...) (seq 0 |row_r|) *)
  assert (HrowAr : List.length (List.nth r A []) = n).
  { apply HrowA. apply List.nth_In. lia. }
  rewrite HrowAr.
  (* Get nth c of (map ... (seq 0 n)). *)
  set (gf := fun col_idx =>
    List.fold_left (fun acc '(a, row_B) =>
      cr_add fld acc (cr_mul fld a (List.nth col_idx row_B (cr_zero fld))))
      (List.combine (List.nth r A []) B) (cr_zero fld)).
  assert (Hlen : c < List.length (List.map gf (List.seq 0 n))).
  { rewrite List.length_map, List.length_seq. exact Hc. }
  rewrite (List.nth_indep _ _ (gf 0) Hlen).
  rewrite (List.map_nth gf (List.seq 0 n) 0 c).
  rewrite List.seq_nth by exact Hc. simpl.
  unfold gf.
  rewrite (fold_left_dot_as_sum_seq fld (List.nth r A []) B c).
  rewrite HrowAr, HlenB. rewrite Nat.min_id. reflexivity.
Qed.

(** Now: the [r]-th diagonal entry of mat_mul A B, in the form needed for trace. *)
Lemma mat_mul_diag_sum :
  forall {F : Type} (fld : Field F) (n : nat) (A B : Matrix F) (r : nat),
    Mat_wf n n A -> Mat_wf n n B -> r < n ->
    List.nth r (List.nth r (mat_mul fld A B) []) (cr_zero fld) =
    sum_seq fld
      (fun j => cr_mul fld (List.nth j (List.nth r A []) (cr_zero fld))
                            (List.nth r (List.nth j B []) (cr_zero fld)))
      n.
Proof.
  intros F fld n A B r HA HB Hr.
  apply (mat_mul_entry_sum fld n A B r r HA HB Hr Hr).
Qed.

(** Tr(AB) as a double sum [Σ_i Σ_j A[i,j] · B[j,i]]. *)
Lemma mat_trace_mul_double_sum :
  forall {F : Type} (fld : Field F) (n : nat) (A B : Matrix F),
    Mat_wf n n A -> Mat_wf n n B ->
    mat_trace fld (mat_mul fld A B) =
    sum_seq fld (fun i =>
      sum_seq fld (fun j =>
        cr_mul fld (List.nth j (List.nth i A []) (cr_zero fld))
                    (List.nth i (List.nth j B []) (cr_zero fld)))
      n) n.
Proof.
  intros F fld n A B HA HB.
  rewrite (mat_trace_as_sum_seq fld (mat_mul fld A B)).
  assert (Hlen : List.length (mat_mul fld A B) = n).
  { rewrite length_mat_mul. apply HA. }
  rewrite Hlen.
  apply sum_seq_ext. intros i Hi.
  apply (mat_mul_diag_sum fld n A B i HA HB Hi).
Qed.

(** Tr(AB) = Tr(BA). Strengthened with [Mat_wf] hypotheses
    (Task M.1, 2026-04-30): the cyclic property requires square matrices
    of matching dimension.
    Discharged 2026-05-01 (Task M.1.next, β R4): real lemma now,
    via the [sum_seq] / [sum_seq_swap] / [mat_mul_entry_sum] helpers.
    Both sides equal [Σ_i Σ_j A[i,j] · B[j,i]] up to commutativity of
    multiplication and an index swap. *)
Lemma mat_trace_cyclic : forall {F : Type} (fld : Field F) (n : nat) (A B : Matrix F),
    Mat_wf n n A -> Mat_wf n n B ->
    mat_trace fld (mat_mul fld A B) = mat_trace fld (mat_mul fld B A).
Proof.
  intros F fld n A B HA HB.
  rewrite (mat_trace_mul_double_sum fld n A B HA HB).
  rewrite (mat_trace_mul_double_sum fld n B A HB HA).
  (* LHS = Σ_i Σ_j A[i,j] · B[j,i].
     RHS = Σ_i Σ_j B[i,j] · A[j,i].
     Swap i↔j on RHS, then commute the product. *)
  rewrite (sum_seq_swap fld
             (fun i j => cr_mul fld (List.nth j (List.nth i B []) (cr_zero fld))
                                     (List.nth i (List.nth j A []) (cr_zero fld)))
             n n).
  apply sum_seq_ext. intros i _.
  apply sum_seq_ext. intros j _.
  apply cr_mul_comm.
Qed.

(** Tr([A,B]) = 0  (commutator has zero trace). Now Mat_wf-guarded. *)
Lemma mat_trace_bracket_zero : forall {F : Type} (fld : Field F) (n : nat) (A B : Matrix F),
    Mat_wf n n A -> Mat_wf n n B ->
    mat_trace fld (mat_bracket fld A B) = fld.(cr_zero).
Proof.
  intros F fld n A B HA HB. unfold mat_bracket, mat_neg.
  rewrite (mat_trace_add fld n (mat_mul fld A B) _).
  - rewrite mat_trace_scale.
    rewrite (mat_trace_cyclic fld n B A HB HA).
    rewrite cr_neg_mul_l, cr_one_mul.
    apply cr_add_neg.
  - apply mat_mul_wf; assumption.
  - apply mat_scale_wf. apply mat_mul_wf; assumption.
Qed.

(* mat_trace_unit_diag axiom removed: was FALSE-as-stated for i ≥ n
   (trace = 0 since mat_unit fld n i i is the zero matrix in that case).
   Replaced by the proven version `mat_trace_unit_diag_lt` below with the
   necessary `i < n` hypothesis. *)

(** Helper: trace_aux of a sequence of rows that are all zero at the
    relevant diagonal entry is 0.  The k-th row is at index `start + k`
    (matching mat_trace_aux's k counter). *)
Lemma mat_trace_aux_seq_off : forall {F : Type} (fld : Field F)
    (i j start n N : nat),
    i <> j ->
    mat_trace_aux fld
      (List.map (fun r =>
        List.map (fun c => if Nat.eqb r i && Nat.eqb c j
                           then cr_one fld else cr_zero fld)
                 (List.seq 0 N))
        (List.seq start n))
      start
    = cr_zero fld.
Proof.
  intros F fld i j start n N Hij.
  revert start.
  induction n as [|n IH]; intro start.
  - reflexivity.
  - simpl. rewrite IH.
    rewrite cr_add_zero.
    set (f := fun c => if Nat.eqb start i && Nat.eqb c j
                       then cr_one fld else cr_zero fld).
    assert (Hfval : forall c, f c = cr_zero fld \/ (c = j /\ f c = cr_one fld /\ start = i)).
    { intro c. unfold f.
      destruct (Nat.eqb start i) eqn:Eri; destruct (Nat.eqb c j) eqn:Ecj; simpl;
        try (left; reflexivity).
      apply Nat.eqb_eq in Eri, Ecj. subst.
      right. split; [reflexivity|]. split; reflexivity. }
    destruct (Nat.ltb start N) eqn:HltN.
    + apply Nat.ltb_lt in HltN.
      assert (Hlen : start < List.length (List.map f (List.seq 0 N))).
      { rewrite List.length_map, List.length_seq. exact HltN. }
      rewrite (List.nth_indep _ _ (f 0) Hlen).
      rewrite (List.map_nth f (List.seq 0 N) 0 start).
      rewrite List.seq_nth by exact HltN. simpl.
      destruct (Hfval start) as [Hz | [_ [_ Hsi]]].
      * exact Hz.
      * subst start. unfold f. rewrite Nat.eqb_refl. simpl.
        replace (Nat.eqb i j) with false; [reflexivity|].
        symmetry. apply Nat.eqb_neq. exact Hij.
    + apply Nat.ltb_ge in HltN.
      rewrite List.nth_overflow; [reflexivity|].
      rewrite List.length_map, List.length_seq. exact HltN.
Qed.

(** Tr(e_{ij}) = 0 when i ≠ j (off-diagonal unit has trace 0). *)
Lemma mat_trace_unit_off_diag : forall {F : Type} (fld : Field F) (n i j : nat),
    i <> j -> mat_trace fld (mat_unit fld n i j) = fld.(cr_zero).
Proof.
  intros F fld n i j Hij.
  unfold mat_trace, mat_unit.
  apply mat_trace_aux_seq_off. exact Hij.
Qed.

(** Helper: trace_aux of a sequence of rows with i strictly outside the
    row range [start..start+n-1] is 0. *)
Lemma mat_trace_aux_seq_no_diag : forall {F : Type} (fld : Field F)
    (i start n N : nat),
    (i < start \/ start + n <= i) ->
    mat_trace_aux fld
      (List.map (fun r =>
        List.map (fun c => if Nat.eqb r i && Nat.eqb c i
                           then cr_one fld else cr_zero fld)
                 (List.seq 0 N))
        (List.seq start n))
      start
    = cr_zero fld.
Proof.
  intros F fld i start n N. revert start.
  induction n as [|n IH]; intros start Hout.
  - reflexivity.
  - simpl. rewrite IH.
    + rewrite cr_add_zero.
      (* Goal: nth start (map (fun c => if start=i ∧ c=i then 1 else 0) (seq 0 N)) 0 = 0 *)
      assert (Hsi : start <> i).
      { destruct Hout as [Hs | Hs]; lia. }
      destruct (Nat.ltb start N) eqn:HltN.
      * apply Nat.ltb_lt in HltN.
        set (f := fun c => if Nat.eqb start i && Nat.eqb c i
                           then cr_one fld else cr_zero fld).
        assert (Hlen : start < List.length (List.map f (List.seq 0 N))).
        { rewrite List.length_map, List.length_seq. exact HltN. }
        rewrite (List.nth_indep _ _ (f 0) Hlen).
        rewrite (List.map_nth f (List.seq 0 N) 0 start).
        rewrite List.seq_nth by exact HltN. simpl.
        unfold f. replace (Nat.eqb start i) with false; [reflexivity|].
        symmetry. apply Nat.eqb_neq. exact Hsi.
      * apply Nat.ltb_ge in HltN.
        rewrite List.nth_overflow; [reflexivity|].
        rewrite List.length_map, List.length_seq. exact HltN.
    + destruct Hout as [Hs | Hs]; [left; lia | right; lia].
Qed.

(** Helper: trace_aux of unit-diagonal pattern equals 1 when i is in the
    row range [start..start+n-1] AND i < N. *)
Lemma mat_trace_aux_seq_diag : forall {F : Type} (fld : Field F)
    (i start n N : nat),
    start <= i < start + n -> i < N ->
    mat_trace_aux fld
      (List.map (fun r =>
        List.map (fun c => if Nat.eqb r i && Nat.eqb c i
                           then cr_one fld else cr_zero fld)
                 (List.seq 0 N))
        (List.seq start n))
      start
    = cr_one fld.
Proof.
  intros F fld i start n N. revert start.
  induction n as [|n IH]; intros start Hin HiN.
  - lia.
  - simpl.
    destruct (Nat.eq_dec start i) as [Heq | Hne].
    + (* start = i: diagonal entry = 1, rest's trace = 0 (i not in [S i..S i + n - 1]) *)
      subst start.
      rewrite (mat_trace_aux_seq_no_diag fld i (S i) n N).
      * rewrite cr_add_zero.
        (* Goal: nth i (map (fun c => if i=i ∧ c=i then 1 else 0) (seq 0 N)) 0 = 1 *)
        set (f := fun c => if Nat.eqb i i && Nat.eqb c i
                           then cr_one fld else cr_zero fld).
        assert (Hlen : i < List.length (List.map f (List.seq 0 N))).
        { rewrite List.length_map, List.length_seq. exact HiN. }
        rewrite (List.nth_indep _ _ (f 0) Hlen).
        rewrite (List.map_nth f (List.seq 0 N) 0 i).
        rewrite List.seq_nth by exact HiN. simpl.
        unfold f. rewrite !Nat.eqb_refl. reflexivity.
      * left. lia.
    + (* start < i (since start <= i and start ≠ i): diagonal entry = 0,
         use IH on [S start..S start + n - 1]. *)
      assert (Hsi : start < i) by lia.
      rewrite IH; [|lia|exact HiN].
      (* Goal: 0 + 1 = 1, after first nth = 0 *)
      assert (Hzero : List.nth start (List.map (fun c =>
        if Nat.eqb start i && Nat.eqb c i then cr_one fld else cr_zero fld)
        (List.seq 0 N)) (cr_zero fld) = cr_zero fld).
      { destruct (Nat.ltb start N) eqn:HltN.
        - apply Nat.ltb_lt in HltN.
          set (f := fun c => if Nat.eqb start i && Nat.eqb c i
                             then cr_one fld else cr_zero fld).
          assert (Hlen : start < List.length (List.map f (List.seq 0 N))).
          { rewrite List.length_map, List.length_seq. exact HltN. }
          rewrite (List.nth_indep _ _ (f 0) Hlen).
          rewrite (List.map_nth f (List.seq 0 N) 0 start).
          rewrite List.seq_nth by exact HltN. simpl.
          unfold f. replace (Nat.eqb start i) with false; [reflexivity|].
          symmetry. apply Nat.eqb_neq. exact Hne.
        - apply Nat.ltb_ge in HltN.
          rewrite List.nth_overflow; [reflexivity|].
          rewrite List.length_map, List.length_seq. exact HltN. }
      rewrite Hzero. apply ring_add_zero_l.
Qed.

(** Tr(e_{ii}) = 1 when i < n (proven version with bound). *)
Lemma mat_trace_unit_diag_lt : forall {F : Type} (fld : Field F) (n i : nat),
    i < n -> mat_trace fld (mat_unit fld n i i) = fld.(cr_one).
Proof.
  intros F fld n i Hi. unfold mat_trace, mat_unit.
  apply mat_trace_aux_seq_diag; lia.
Qed.

(* ================================================================== *)
(** * 2. Special linear Lie algebra                                   *)
(* ================================================================== *)

(** sl(n, F) = trace-zero matrices.  Predicate on bare [Matrix F]
    (used by the basis-element lemmas like [sl_diag_tracezero]). *)
Definition IsTracezero {F : Type} (fld : Field F) (A : Matrix F) : Prop :=
  mat_trace fld A = fld.(cr_zero).

(** Lifted predicate: trace-zero condition on a [GLMat fld n] sigma-element.
    REFACTOR (Task M.1): the [IsSubalgebra (gl fld n) ...] form requires
    a predicate on [GLMat fld n], not raw [Matrix F]. *)
Definition IsTracezeroGL {F : Type} (fld : Field F) (n : nat)
    (A : GLMat fld n) : Prop :=
  IsTracezero fld (proj1_sig A).

(** sl(n, F) is a Lie subalgebra of gl(n, F). *)
Lemma sl_is_subalgebra : forall {F : Type} (fld : Field F) (n : nat),
    IsSubalgebra (gl fld n) (IsTracezeroGL fld n).
Proof.
  intros F fld n. constructor.
  - (* Tr(0) = 0 *)
    unfold IsTracezeroGL, IsTracezero.
    rewrite gl_zero_eq_mat_zero. apply mat_trace_zero.
  - (* Tr(A + B) = Tr(A) + Tr(B) = 0 + 0 = 0 *)
    intros A B HA HB. unfold IsTracezeroGL, IsTracezero in *.
    rewrite gl_add_eq_mat_add.
    rewrite (mat_trace_add fld n _ _ (proj2_sig A) (proj2_sig B)).
    rewrite HA, HB.
    apply fld.(cr_add_zero).
  - (* Tr(-A) = -Tr(A) = -0 = 0 *)
    intros A HA. unfold IsTracezeroGL, IsTracezero in *.
    rewrite gl_neg_eq_mat_neg. unfold mat_neg.
    rewrite mat_trace_scale. rewrite HA.
    apply ring_mul_zero_r.
  - (* Tr(c·A) = c·Tr(A) = c·0 = 0 *)
    intros c A HA. unfold IsTracezeroGL, IsTracezero in *.
    rewrite gl_scale_eq_mat_scale. rewrite mat_trace_scale.
    rewrite HA. apply ring_mul_zero_r.
  - (* Tr([A,B]) = 0 *)
    intros A B _ _.
    unfold IsTracezeroGL, IsTracezero in *.
    rewrite gl_bracket_eq_mat_bracket.
    apply (mat_trace_bracket_zero fld n _ _ (proj2_sig A) (proj2_sig B)).
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

(** h_i is trace-zero (with bound S i < n; otherwise mat_unit fld n (S i) (S i)
    is the zero matrix and the statement is degenerate). *)
Lemma sl_diag_tracezero : forall {F : Type} (fld : Field F) (n i : nat),
    S i < n -> IsTracezero fld (sl_diag fld n i).
Proof.
  intros F fld n i Hbnd. unfold IsTracezero, sl_diag.
  rewrite (mat_trace_add fld n _ _
             (mat_unit_wf fld n i i)
             (mat_neg_wf fld n n _ (mat_unit_wf fld n (S i) (S i)))),
          (mat_trace_unit_diag_lt fld n i (Nat.lt_succ_l _ _ Hbnd)).
  unfold mat_neg.
  rewrite mat_trace_scale, (mat_trace_unit_diag_lt fld n (S i) Hbnd).
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
    This follows from mat_unit_bracket in Linear.v.
    REFACTOR (Task M.1): now stated at the projection level — the bracket
    is taken inside [gl fld n] (between sigma-wrapped matrix units) and
    its [proj1_sig] equals the explicit matrix expression. *)
Lemma sl_bracket_units : forall {F : Type} (fld : Field F) (n i j k l : nat),
    proj1_sig (laF_bracket (gl fld n)
                 (exist _ (mat_unit fld n i j) (mat_unit_wf fld n i j))
                 (exist _ (mat_unit fld n k l) (mat_unit_wf fld n k l))) =
    mat_add fld
      (if Nat.eqb j k then mat_unit fld n i l else mat_zero fld n)
      (if Nat.eqb l i then mat_neg fld (mat_unit fld n k j) else mat_zero fld n).
Proof.
  intros F fld n i j k l.
  rewrite gl_bracket_eq_mat_bracket. simpl. apply mat_unit_bracket.
Qed.

(** [h_i, e_{ij}] = 2 e_{ij} and other standard sl(2) relations. *)
Lemma sl_bracket_hi_eij : forall {F : Type} (fld : Field F) (n i j : nat),
    i < n -> j < n -> i <> j ->
    True. (* placeholder for concrete commutator computations *)
Proof. intros. exact I. Qed.

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

(** Commutation relations for sl(2, F) — proved below after the 2x2 helpers. *)

(** Helper: explicit form of mat_mul for 2x2 matrices.
    Both sides should be definitionally equal. *)
Lemma mat_mul_2x2 : forall {F : Type} (fld : Field F) (a b c d e f g h : F),
    mat_mul fld
      [[a; b]; [c; d]]
      [[e; f]; [g; h]] =
    [[cr_add fld (cr_add fld (cr_zero fld) (cr_mul fld a e)) (cr_mul fld b g);
      cr_add fld (cr_add fld (cr_zero fld) (cr_mul fld a f)) (cr_mul fld b h)];
     [cr_add fld (cr_add fld (cr_zero fld) (cr_mul fld c e)) (cr_mul fld d g);
      cr_add fld (cr_add fld (cr_zero fld) (cr_mul fld c f)) (cr_mul fld d h)]].
Proof. intros. reflexivity. Qed.

(** Helper: mat_neg of an explicit 2x2 matrix. *)
Lemma mat_neg_2x2 : forall {F : Type} (fld : Field F) (a b c d : F),
    mat_neg fld [[a; b]; [c; d]] =
    [[cr_mul fld (cr_neg fld (cr_one fld)) a;
      cr_mul fld (cr_neg fld (cr_one fld)) b];
     [cr_mul fld (cr_neg fld (cr_one fld)) c;
      cr_mul fld (cr_neg fld (cr_one fld)) d]].
Proof. intros. reflexivity. Qed.

(** Helper: mat_add of two explicit 2x2 matrices. *)
Lemma mat_add_2x2 : forall {F : Type} (fld : Field F) (a1 b1 c1 d1 a2 b2 c2 d2 : F),
    mat_add fld
      [[a1; b1]; [c1; d1]]
      [[a2; b2]; [c2; d2]] =
    [[cr_add fld a1 a2; cr_add fld b1 b2];
     [cr_add fld c1 c2; cr_add fld d1 d2]].
Proof. intros. reflexivity. Qed.

(** Helper: mat_scale of an explicit 2x2 matrix. *)
Lemma mat_scale_2x2 : forall {F : Type} (fld : Field F) (c a b d e : F),
    mat_scale fld c [[a; b]; [d; e]] =
    [[cr_mul fld c a; cr_mul fld c b]; [cr_mul fld c d; cr_mul fld c e]].
Proof. intros. reflexivity. Qed.

(** A "ring-zero" simplifier that repeatedly applies basic ring identities. *)
Ltac ring_simplify_zero fld :=
  repeat (
    rewrite ?(cr_mul_zero_l fld) ||
    rewrite ?(cr_mul_zero_r fld) ||
    rewrite ?(cr_add_zero fld) ||
    rewrite ?(cr_add_zero_l fld) ||
    rewrite ?(cr_mul_one fld) ||
    rewrite ?(cr_one_mul fld)).

Lemma sl2_bracket_xy : forall {F : Type} (fld : Field F),
    mat_bracket fld (sl2_X_mat fld) (sl2_Y_mat fld) = sl2_H_mat fld.
Proof.
  intros F fld. unfold mat_bracket, sl2_X_mat, sl2_Y_mat, sl2_H_mat.
  rewrite (mat_mul_2x2 fld).
  rewrite (mat_mul_2x2 fld).
  rewrite (mat_neg_2x2 fld).
  rewrite (mat_add_2x2 fld).
  repeat f_equal; ring_simplify_zero fld; reflexivity.
Qed.

(** Helper: -1 * -1 = 1 in any field (rewrite version). *)
Lemma cr_neg_one_sq {F : Type} (fld : Field F) :
  cr_mul fld (cr_neg fld (cr_one fld)) (cr_neg fld (cr_one fld)) = cr_one fld.
Proof.
  rewrite (cr_neg_mul_neg fld). apply (cr_mul_one fld).
Qed.

(** [H, X] = 2X.
    Each entry of the result reduces with ring identities; entry (0,1) needs
    the additional fact (-1)*(-1) = 1 from [cr_neg_one_sq]. *)
Lemma sl2_bracket_hx : forall {F : Type} (fld : Field F),
    mat_bracket fld (sl2_H_mat fld) (sl2_X_mat fld) =
    mat_scale fld (fld.(cr_add) fld.(cr_one) fld.(cr_one)) (sl2_X_mat fld).
Proof.
  intros F fld. unfold mat_bracket, sl2_H_mat, sl2_X_mat.
  rewrite (mat_mul_2x2 fld).
  rewrite (mat_mul_2x2 fld).
  rewrite (mat_neg_2x2 fld).
  rewrite (mat_add_2x2 fld).
  rewrite (mat_scale_2x2 fld).
  (* Goal: explicit 2x2 list equality. Decompose with f_equal and solve each entry. *)
  match goal with |- ?L = ?R => assert (Hgoal : L = R); [|exact Hgoal] end.
  f_equal.
  - (* Row 0: [entry00; entry01] = [(1+1)*0; (1+1)*1] *)
    f_equal.
    + (* (0,0) *) ring_simplify_zero fld. reflexivity.
    + f_equal. (* (0,1) *)
      ring_simplify_zero fld.
      rewrite (cr_neg_one_sq fld). reflexivity.
  - f_equal.
    f_equal.
    + (* (1,0) *) ring_simplify_zero fld. reflexivity.
    + f_equal. (* (1,1) *)
      ring_simplify_zero fld. reflexivity.
Qed.

(** Helper: -1 * 1 = -1 in any field (rewrite version). *)
Lemma cr_neg_one_mul_one {F : Type} (fld : Field F) :
  cr_mul fld (cr_neg fld (cr_one fld)) (cr_one fld) = cr_neg fld (cr_one fld).
Proof. apply (cr_mul_one fld). Qed.

(** [H, Y] = -2Y. *)
Lemma sl2_bracket_hy : forall {F : Type} (fld : Field F),
    mat_bracket fld (sl2_H_mat fld) (sl2_Y_mat fld) =
    mat_scale fld (fld.(cr_neg) (fld.(cr_add) fld.(cr_one) fld.(cr_one))) (sl2_Y_mat fld).
Proof.
  intros F fld. unfold mat_bracket, sl2_H_mat, sl2_Y_mat.
  rewrite (mat_mul_2x2 fld).
  rewrite (mat_mul_2x2 fld).
  rewrite (mat_neg_2x2 fld).
  rewrite (mat_add_2x2 fld).
  rewrite (mat_scale_2x2 fld).
  f_equal.
  - (* Row 0 *)
    f_equal.
    + (* (0,0) *) ring_simplify_zero fld. reflexivity.
    + f_equal. (* (0,1) *) ring_simplify_zero fld. reflexivity.
  - f_equal.
    f_equal.
    + (* (1,0): cr_add (cr_neg cr_one) (cr_neg cr_one) = cr_neg (cr_add cr_one cr_one) *)
      ring_simplify_zero fld.
      rewrite (cr_neg_add fld). reflexivity.
    + f_equal. (* (1,1) *) ring_simplify_zero fld. reflexivity.
Qed.

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

(* sl2_abstract_simple removed: was a real theorem (sl(2) is simple when
   char ≠ 2) but never referenced anywhere in the codebase. The proof
   would require a substantial argument tracking ideals through the
   adjoint action of {x, h, y}; left to future work. *)

(* ================================================================== *)
(** * Exercise 3: Adjoint representation of sl(2,F)                   *)
(** Compute [X,−], [H,−], [Y,−] on the basis {X,H,Y}.               *)
(* ================================================================== *)

(** Helper: mat_bracket is antisymmetric (from gl being a Lie algebra).
    REFACTOR (Task M.1): now takes [Mat_wf 2 2] hypotheses since the gl
    Lie algebra is now built over the sigma type [GLMat fld 2]. We
    reflect through the sigma-projection. *)
Lemma mat_bracket_anticomm_2 {F : Type} (fld : Field F) (A B : Matrix F) :
    Mat_wf 2 2 A -> Mat_wf 2 2 B ->
    mat_bracket fld A B = mat_neg fld (mat_bracket fld B A).
Proof.
  intros HA HB.
  pose (sA := exist (Mat_wf 2 2) A HA).
  pose (sB := exist (Mat_wf 2 2) B HB).
  assert (H := laF_anticomm (gl fld 2) sA sB).
  apply (f_equal (@proj1_sig _ _)) in H.
  rewrite (gl_bracket_eq_mat_bracket fld 2 sA sB) in H.
  rewrite (gl_neg_eq_mat_neg fld 2) in H.
  rewrite (gl_bracket_eq_mat_bracket fld 2 sB sA) in H.
  exact H.
Qed.

(** Helper: mat_bracket is alternating (from gl being a Lie algebra). *)
Lemma mat_bracket_alt_2 {F : Type} (fld : Field F) (A : Matrix F) :
    Mat_wf 2 2 A ->
    mat_bracket fld A A = mat_zero fld 2.
Proof.
  intros HA.
  pose (sA := exist (Mat_wf 2 2) A HA).
  assert (H := (gl fld 2).(laF_bracket_alt) sA).
  apply (f_equal (@proj1_sig _ _)) in H.
  rewrite (gl_bracket_eq_mat_bracket fld 2 sA sA) in H.
  rewrite (gl_zero_eq_mat_zero fld 2) in H.
  exact H.
Qed.

(** Helper: mat_neg (mat_scale (-c) A) = mat_scale c A.
    Follows from (-1)*(-c) = c in any commutative ring. *)
Lemma mat_neg_scale_neg : forall {F : Type} (fld : Field F) (c : F) (A : Matrix F),
    mat_neg fld (mat_scale fld (fld.(cr_neg) c) A) = mat_scale fld c A.
Proof.
  intros F fld c A. unfold mat_neg.
  rewrite mat_scale_mul_assoc.
  f_equal. rewrite cr_neg_mul_l. rewrite cr_one_mul. apply cr_neg_neg.
Qed.

(** Helper: mat_neg (mat_scale c A) = mat_scale (-c) A.
    Follows from (-1)*c = -c in any commutative ring. *)
Lemma mat_neg_scale_eq : forall {F : Type} (fld : Field F) (c : F) (A : Matrix F),
    mat_neg fld (mat_scale fld c A) = mat_scale fld (fld.(cr_neg) c) A.
Proof.
  intros F fld c A. unfold mat_neg.
  rewrite mat_scale_mul_assoc.
  f_equal. rewrite cr_neg_mul_l. rewrite cr_one_mul. reflexivity.
Qed.

(** ── Diagonal entries (all zero by alternating property) ─────── *)

(** Local helpers: the standard 2×2 sl(2) basis matrices are trivially
    well-formed (lists of length 2 of lists of length 2). *)
Lemma sl2_X_mat_wf {F : Type} (fld : Field F) : Mat_wf 2 2 (sl2_X_mat fld).
Proof.
  unfold Mat_wf, sl2_X_mat. split; [reflexivity|].
  intros row Hin. simpl in Hin.
  destruct Hin as [<- | [<- | []]]; reflexivity.
Qed.

Lemma sl2_H_mat_wf {F : Type} (fld : Field F) : Mat_wf 2 2 (sl2_H_mat fld).
Proof.
  unfold Mat_wf, sl2_H_mat. split; [reflexivity|].
  intros row Hin. simpl in Hin.
  destruct Hin as [<- | [<- | []]]; reflexivity.
Qed.

Lemma sl2_Y_mat_wf {F : Type} (fld : Field F) : Mat_wf 2 2 (sl2_Y_mat fld).
Proof.
  unfold Mat_wf, sl2_Y_mat. split; [reflexivity|].
  intros row Hin. simpl in Hin.
  destruct Hin as [<- | [<- | []]]; reflexivity.
Qed.

Lemma ad_sl2_X_X {F : Type} (fld : Field F) :
    mat_bracket fld (sl2_X_mat fld) (sl2_X_mat fld) = mat_zero fld 2.
Proof. apply mat_bracket_alt_2. apply sl2_X_mat_wf. Qed.

Lemma ad_sl2_H_H {F : Type} (fld : Field F) :
    mat_bracket fld (sl2_H_mat fld) (sl2_H_mat fld) = mat_zero fld 2.
Proof. apply mat_bracket_alt_2. apply sl2_H_mat_wf. Qed.

Lemma ad_sl2_Y_Y {F : Type} (fld : Field F) :
    mat_bracket fld (sl2_Y_mat fld) (sl2_Y_mat fld) = mat_zero fld 2.
Proof. apply mat_bracket_alt_2. apply sl2_Y_mat_wf. Qed.

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
  rewrite (mat_bracket_anticomm_2 fld _ _
             (sl2_X_mat_wf fld) (sl2_H_mat_wf fld)),
          sl2_bracket_hx.
  apply mat_neg_scale_eq.
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
  rewrite (mat_bracket_anticomm_2 fld _ _
             (sl2_Y_mat_wf fld) (sl2_H_mat_wf fld)),
          sl2_bracket_hy.
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
  rewrite (mat_bracket_anticomm_2 fld _ _
             (sl2_Y_mat_wf fld) (sl2_X_mat_wf fld)),
          sl2_bracket_xy. reflexivity.
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

(* ================================================================== *)
(** * Exercise 2.2: [gl(n,F), gl(n,F)] = sl(n,F)                      *)
(* ================================================================== *)

Require Import CAG.Lie.Solvable.

(** sl(n,F) is an ideal of gl(n,F) (not just a subalgebra).
    For any A ∈ gl, B ∈ sl: Tr([A,B]) = 0 by mat_trace_bracket_zero. *)
Lemma sl_is_ideal : forall {F : Type} (fld : Field F) (n : nat),
    IsIdeal (gl fld n) (IsTracezeroGL fld n).
Proof.
  intros F fld n. constructor.
  - (* zero *)
    unfold IsTracezeroGL, IsTracezero.
    rewrite gl_zero_eq_mat_zero. apply mat_trace_zero.
  - (* add *)
    intros A B HA HB. unfold IsTracezeroGL, IsTracezero in *.
    rewrite gl_add_eq_mat_add.
    rewrite (mat_trace_add fld n _ _ (proj2_sig A) (proj2_sig B)).
    rewrite HA, HB.
    apply fld.(cr_add_zero).
  - (* neg *)
    intros A HA. unfold IsTracezeroGL, IsTracezero in *.
    rewrite gl_neg_eq_mat_neg. unfold mat_neg.
    rewrite mat_trace_scale. rewrite HA. apply ring_mul_zero_r.
  - (* scale *)
    intros c A HA. unfold IsTracezeroGL, IsTracezero in *.
    rewrite gl_scale_eq_mat_scale, mat_trace_scale, HA.
    apply ring_mul_zero_r.
  - (* bracket_l: for any B ∈ gl and A ∈ sl, Tr([B,A]) = 0 *)
    intros B A _.
    unfold IsTracezeroGL, IsTracezero.
    rewrite gl_bracket_eq_mat_bracket.
    apply (mat_trace_bracket_zero fld n _ _ (proj2_sig B) (proj2_sig A)).
Qed.

(** Forward inclusion: IsDerivedAlg (gl n) ⊆ IsTracezeroGL.
    Proof: IsTracezeroGL is a subalgebra containing all brackets (by
    mat_trace_bracket_zero), so by definition of IsDerivedAlg every
    element of the derived algebra is traceless. *)
Lemma gl_derived_sub_sl : forall {F : Type} (fld : Field F) (n : nat) (A : GLMat fld n),
    IsDerivedAlg (gl fld n) A -> IsTracezeroGL fld n A.
Proof.
  intros F fld n A Hderiv.
  apply Hderiv.
  - apply sl_is_subalgebra.
  - intros X Y. unfold IsTracezeroGL, IsTracezero.
    rewrite gl_bracket_eq_mat_bracket.
    apply (mat_trace_bracket_zero fld n _ _ (proj2_sig X) (proj2_sig Y)).
Qed.

(** Backward inclusion: IsTracezeroGL ⊆ IsDerivedAlg (gl n).
    Every traceless matrix is a linear combination of commutators:
    - e_{ij} = [e_{ij}, e_{jj}] for i ≠ j
    - h_i = e_{ii} - e_{i+1,i+1} = [e_{i,i+1}, e_{i+1,i}]

    PAPER-ATTRIBUTED AXIOM (Humphreys §1.2, Exercise 2.2). The proof
    requires finite-dimensional spanning infrastructure that we do
    not currently have at the [Matrix F = list (list F)] level:
    1. A canonical decomposition  A = Σ_{i,j∈[0..n)} A[i,j] · e_{ij}
       for any [Mat_wf n n A], and a proof that this finite sum
       reproduces the original list-of-lists representation.
    2. A sum-induction principle to push membership in a subalgebra
       through finite linear combinations.
    3. The traceless condition then folds the diagonal into [h_i]'s
       (the (n-1) generators of the Cartan-modulo-trace subspace),
       and each [e_{ij}] / [h_i] is a single matrix-unit bracket via
       [mat_unit_bracket] in [Linear.v].

    Each of (1)–(2) is a multi-day refactor (constructive finite-dim
    bases over the list representation). Documented status as of
    Round β R4 / 2026-05-01: deferred to a future spanning-infra task
    (analogous to Task DG-style structural lifts). *)
Axiom gl_sl_sub_derived : forall {F : Type} (fld : Field F) (n : nat) (A : GLMat fld n),
    IsTracezeroGL fld n A -> IsDerivedAlg (gl fld n) A.

(** Main theorem: [gl(n,F), gl(n,F)] = sl(n,F).  (Exercise 2.2) *)
Theorem gl_derived_eq_sl : forall {F : Type} (fld : Field F) (n : nat) (A : GLMat fld n),
    IsDerivedAlg (gl fld n) A <-> IsTracezeroGL fld n A.
Proof.
  intros F fld n A. split.
  - apply gl_derived_sub_sl.
  - apply gl_sl_sub_derived.
Qed.

(* ================================================================== *)
(** * 5. Compatibility of abstract Jordan decomposition with matrices   *)
(* ================================================================== *)

(** mat_mul_inv: placeholder matrix-inverse function. With no behavioral
    axioms (and no current downstream use beyond [IsMatDiagonalizable],
    which is itself unused), we provide the identity function as default.
    A real inverse would require non-singularity tracking. *)
Definition mat_mul_inv {F : Type} (_ : Field F) (_ : nat) (A : Matrix F) : Matrix F := A.

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
Definition IsMatDiagonalizable {F : Type} (fld : Field F) (n : nat) (A : Matrix F) : Prop :=
  exists (P D : Matrix F),
    mat_mul fld P (mat_mul fld D (mat_mul_inv fld n P)) = A /\
    IsDiagonalMatrix fld D.

(** A matrix N ∈ gl(n,F) is nilpotent as a matrix if N^k = 0 for some k. *)
Definition IsMatNilpotent {F : Type} (fld : Field F) (n : nat) (N : Matrix F) : Prop :=
  exists k : nat, mat_pow fld N k = mat_zero fld n.

(* mat_jordan_decomp removed: false-as-stated. The statement claimed
   every A ∈ gl(n,F) has a Jordan decomposition over F, but this requires
   F algebraically closed. Counterexample F = R: A = [[0,-1],[1,0]] has
   eigenvalues ±i ∉ R, no diagonal form. The axiom was unused downstream. *)

(* sl_jordan_agrees_matrix removed: false-as-stated for non-alg-closed F.
   For x = [[0,-1],[1,0]] over R, trace 0 (in sl(2,R)), take s = x, nu = 0;
   hypothesis (x = s + nu, nu ad-nilpotent, [s,nu] = 0) is satisfied,
   but conclusion (s diagonalizable over R) fails. Was unused downstream. *)
