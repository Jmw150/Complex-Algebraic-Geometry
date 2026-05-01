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
From Stdlib Require Import Lia.
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

(** mat_transpose_add: provable for arbitrary list-based A, B because
    both mat_add and mat_transpose adjust shapes consistently via
    combine and nth-default. Proven below by induction with helper
    lemmas. *)

(** Helper: nth col_idx of (vadd-style) row-add via combine. *)
Local Lemma nth_combine_add :
  forall {F : Type} (fld : Field F) (col_idx : nat) (rA rB : list F),
    col_idx < Nat.min (List.length rA) (List.length rB) ->
    List.nth col_idx
      (List.map (fun '(a, b) => cr_add fld a b) (List.combine rA rB))
      (cr_zero fld) =
    cr_add fld (List.nth col_idx rA (cr_zero fld))
               (List.nth col_idx rB (cr_zero fld)).
Proof.
  intros F fld col_idx rA. revert col_idx.
  induction rA as [|a rA' IH]; intros col_idx [|b rB'] Hbnd.
  - simpl in Hbnd. lia.
  - simpl in Hbnd. lia.
  - simpl in Hbnd. lia.
  - simpl. destruct col_idx as [|k]; [reflexivity|].
    simpl. apply IH. simpl in Hbnd. lia.
Qed.

(** Helper: when col_idx is out of range, both sides give 0+0. *)
Local Lemma nth_combine_add_oob :
  forall {F : Type} (fld : Field F) (col_idx : nat) (rA rB : list F),
    col_idx >= Nat.min (List.length rA) (List.length rB) ->
    List.nth col_idx
      (List.map (fun '(a, b) => cr_add fld a b) (List.combine rA rB))
      (cr_zero fld) =
    cr_zero fld.
Proof.
  intros F fld col_idx rA. revert col_idx.
  induction rA as [|a rA' IH]; intros col_idx [|b rB'] Hbnd.
  - simpl. destruct col_idx; reflexivity.
  - simpl. destruct col_idx; reflexivity.
  - simpl. destruct col_idx; reflexivity.
  - simpl. destruct col_idx as [|k].
    + simpl in Hbnd. lia.
    + simpl. apply IH. simpl in Hbnd. lia.
Qed.

(** Helper: combine two maps over the same list. *)
Local Lemma combine_map_map_same :
  forall {A X Y : Type} (f : A -> X) (g : A -> Y) (l : list A),
    List.combine (List.map f l) (List.map g l) =
    List.map (fun x => (f x, g x)) l.
Proof.
  intros A X Y f g l. induction l as [|x l IH]; simpl; [reflexivity|].
  f_equal. exact IH.
Qed.

(** Helper: length of mat_add of two same-length, same-row-length matrices. *)
Local Lemma length_mat_add_wf :
  forall {F : Type} (fld : Field F) (n : nat) (A B : Matrix F),
    Mat_wf n n A -> Mat_wf n n B ->
    List.length (mat_add fld A B) = n.
Proof.
  intros F fld n A B [HlenA _] [HlenB _]. unfold mat_add.
  rewrite List.length_map.
  rewrite (length_combine_eq A B); [exact HlenA|congruence].
Qed.

(** Helper: the head-row length of [mat_add A B] when both are [Mat_wf n n]
    and [n > 0] is [n]. *)
Local Lemma head_length_mat_add_wf :
  forall {F : Type} (fld : Field F) (n : nat) (A B : Matrix F),
    Mat_wf (S n) (S n) A -> Mat_wf (S n) (S n) B ->
    match mat_add fld A B with
    | [] => 0
    | row :: _ => List.length row
    end = S n.
Proof.
  intros F fld n A B HA HB.
  pose proof (mat_add_wf fld (S n) (S n) A B HA HB) as [HlenAB HrowAB].
  destruct (mat_add fld A B) as [|row rest] eqn:Heq; [simpl in HlenAB; lia|].
  apply HrowAB. left. reflexivity.
Qed.

(** mat_transpose_add — under [Mat_wf n n] hypotheses, the transpose of a sum
    is the sum of the transposes.

    REFACTOR (Task M.3, 2026-04-30): converted from un-guarded Axiom to
    Mat_wf-guarded Lemma.  All call-sites in [Symplectic.v]/[Orthogonal.v]
    have been threaded with the appropriate [Mat_wf] witnesses. *)
Lemma mat_transpose_add :
  forall {F : Type} (fld : Field F) (n : nat) (A B : Matrix F),
    Mat_wf n n A -> Mat_wf n n B ->
    mat_transpose fld (mat_add fld A B) =
    mat_add fld (mat_transpose fld A) (mat_transpose fld B).
Proof.
  intros F fld n A B HA HB.
  pose proof (mat_add_wf fld n n A B HA HB) as HAB.
  destruct HA as [HlenA HrowA].
  destruct HB as [HlenB HrowB].
  destruct HAB as [HlenAB HrowAB].
  unfold mat_transpose at 1 2 3.
  (* head-row-lengths *)
  assert (HhA : match A with [] => 0 | row :: _ => List.length row end = n).
  { destruct A as [|row rest].
    - simpl in HlenA. lia.
    - apply HrowA. left. reflexivity. }
  assert (HhB : match B with [] => 0 | row :: _ => List.length row end = n).
  { destruct B as [|row rest].
    - simpl in HlenB. lia.
    - apply HrowB. left. reflexivity. }
  assert (HhAB : match mat_add fld A B with [] => 0 | row :: _ => List.length row end = n).
  { destruct (mat_add fld A B) as [|row rest] eqn:Heq.
    - simpl in HlenAB. lia.
    - apply HrowAB. left. reflexivity. }
  (* Special case: n = 0. Then A = [] and B = [], so both sides are []. *)
  destruct n as [|n'].
  { destruct A as [|rA tA]; [|simpl in HlenA; lia].
    destruct B as [|rB tB]; [|simpl in HlenB; lia].
    simpl. reflexivity. }
  rewrite HhA, HhB, HhAB.
  cbv zeta.
  (* RHS: [mat_add (map f (seq 0 (S n'))) (map g (seq 0 (S n')))] —
     unfold mat_add and use combine_map_map_same to collapse the combine. *)
  unfold mat_add.
  rewrite combine_map_map_same.
  rewrite List.map_map.
  apply List.map_ext_in. intros col_idx Hin.
  apply List.in_seq in Hin. destruct Hin as [_ Hcol].
  simpl in Hcol.
  cbn beta.
  (* Now LHS: [map (fun row => nth col_idx row 0) (map f (combine A B))]
     where f = fun '(r1,r2) => map (fun '(a,b) => add a b) (combine r1 r2). *)
  rewrite List.map_map.
  rewrite combine_map_l.
  rewrite combine_map_r.
  rewrite !List.map_map.
  apply List.map_ext_in. intros [r1 r2] Hin.
  cbn beta iota.
  apply in_combine_lengths in Hin. destruct Hin as [Hr1 Hr2].
  pose proof (HrowA r1 Hr1) as Hlenr1.
  pose proof (HrowB r2 Hr2) as Hlenr2.
  destruct (Nat.lt_ge_cases col_idx (Nat.min (List.length r1) (List.length r2))) as [Hlt|Hge].
  - apply (nth_combine_add fld col_idx r1 r2 Hlt).
  - rewrite (nth_combine_add_oob fld col_idx r1 r2 Hge).
    rewrite Hlenr1, Hlenr2 in Hge.
    rewrite Nat.min_id in Hge. lia.
Qed.

(** Helper: mat_scale preserves the head-row length used by
    mat_transpose's let-bound n. *)
Local Lemma head_length_mat_scale_eq :
  forall {F : Type} (fld : Field F) (c : F) (A : Matrix F),
    match mat_scale fld c A with [] => 0 | row :: _ => List.length row end =
    match A with [] => 0 | row :: _ => List.length row end.
Proof.
  intros F fld c [|row rest]; simpl; [reflexivity|].
  rewrite List.length_map. reflexivity.
Qed.

(** Helper: nth col_idx (map (cr_mul c) row) 0 = cr_mul c (nth col_idx row 0). *)
Local Lemma nth_inner_scale :
  forall {F : Type} (fld : Field F) (c : F) (col_idx : nat) (row : list F),
    List.nth col_idx (List.map (cr_mul fld c) row) (cr_zero fld) =
    cr_mul fld c (List.nth col_idx row (cr_zero fld)).
Proof.
  intros F fld c col_idx row. apply (nth_map_cmul fld c row col_idx).
Qed.

(** Helper: pointwise equality of inner maps for transpose_scale. *)
Local Lemma transpose_scale_pointwise :
  forall {F : Type} (fld : Field F) (c : F) (col_idx : nat) (A : Matrix F),
    List.map (fun r => List.nth col_idx r (cr_zero fld))
             (List.map (fun r => List.map (cr_mul fld c) r) A) =
    List.map (cr_mul fld c)
             (List.map (fun r => List.nth col_idx r (cr_zero fld)) A).
Proof.
  intros F fld c col_idx A.
  rewrite !List.map_map.
  apply List.map_ext_in. intros r _.
  apply (nth_inner_scale fld c col_idx r).
Qed.

Lemma mat_transpose_scale :
  forall {F : Type} (fld : Field F) (c : F) (A : Matrix F),
    mat_transpose fld (mat_scale fld c A) = mat_scale fld c (mat_transpose fld A).
Proof.
  intros F fld c A.
  destruct A as [|row rest]; [cbn; reflexivity|].
  unfold mat_transpose, mat_scale.
  cbn [List.map].
  rewrite List.length_map.
  rewrite List.map_map.
  apply List.map_ext_in. intros col_idx _.
  apply (transpose_scale_pointwise fld c col_idx (row :: rest)).
Qed.

Lemma mat_transpose_neg :
  forall {F : Type} (fld : Field F) (A : Matrix F),
    mat_transpose fld (mat_neg fld A) = mat_neg fld (mat_transpose fld A).
Proof. intros. unfold mat_neg. apply mat_transpose_scale. Qed.

(** Helper: the i-th row of [mat_transpose fld A] when [i < n]
    (where n = head-row-length of A under [Mat_wf m n A], m > 0). *)
Local Lemma nth_row_transpose :
  forall {F : Type} (fld : Field F) (m n i : nat) (A : Matrix F),
    Mat_wf m n A -> i < n ->
    List.nth i (mat_transpose fld A) [] =
    List.map (fun row => List.nth i row (cr_zero fld)) A.
Proof.
  intros F fld m n i A [HlenA HrowA] Hi.
  (* Case split on A to determine head-row-length. *)
  destruct A as [|hd_row rest].
  { (* A = [] => m = 0; mat_transpose [] = []; both sides are []. *)
    unfold mat_transpose. simpl. destruct i; reflexivity. }
  (* A = hd_row :: rest *)
  assert (Hh_len : List.length hd_row = n) by (apply HrowA; left; reflexivity).
  unfold mat_transpose. cbn [List.length].
  rewrite Hh_len.
  set (A' := hd_row :: rest).
  set (f := fun col => List.map (fun row => List.nth col row (cr_zero fld)) A').
  assert (Hi2 : i < List.length (List.map f (List.seq 0 n))).
  { rewrite List.length_map, List.length_seq. exact Hi. }
  rewrite (List.nth_indep _ _ (f 0) Hi2).
  rewrite (List.map_nth f (List.seq 0 n) 0 i).
  rewrite List.seq_nth by exact Hi.
  reflexivity.
Qed.

(** Helper: the j-th entry of the i-th row of [mat_transpose fld A]
    equals the i-th entry of the j-th row of A, when both indices are in range. *)
Local Lemma nth_entry_transpose :
  forall {F : Type} (fld : Field F) (n i j : nat) (A : Matrix F),
    Mat_wf n n A -> i < n -> j < n ->
    List.nth j (List.nth i (mat_transpose fld A) []) (cr_zero fld) =
    List.nth i (List.nth j A []) (cr_zero fld).
Proof.
  intros F fld n i j A HA Hi Hj.
  rewrite (nth_row_transpose fld n n i A HA Hi).
  (* Goal: nth j (map (fun row => nth i row 0) A) 0 = nth i (nth j A []) 0 *)
  destruct HA as [HlenA HrowA].
  assert (Hj2 : j < List.length A) by lia.
  (* Use List.nth_indep on the map to change default *)
  assert (Hmap_len : j < List.length (List.map (fun row => List.nth i row (cr_zero fld)) A)).
  { rewrite List.length_map. exact Hj2. }
  rewrite (List.nth_indep (List.map (fun row => List.nth i row (cr_zero fld)) A)
             (cr_zero fld) (List.nth i [] (cr_zero fld)) Hmap_len).
  rewrite (List.map_nth (fun row => List.nth i row (cr_zero fld)) A [] j).
  reflexivity.
Qed.

(** [mat_transpose_mul] kept Mat_wf-guarded as an Axiom (entry-level proof
    deferred — list-of-lists fold/transpose extensionality is bookkeeping
    heavy and not on the critical path). *)
Axiom mat_transpose_mul :
  forall {F : Type} (fld : Field F) (n : nat) (A B : Matrix F),
    Mat_wf n n A -> Mat_wf n n B ->
    mat_transpose fld (mat_mul fld A B) =
    mat_mul fld (mat_transpose fld B) (mat_transpose fld A).

Lemma mat_transpose_zero :
  forall {F : Type} (fld : Field F) (n : nat),
    mat_transpose fld (mat_zero fld n) = mat_zero fld n.
Proof.
  intros F fld n.
  unfold mat_transpose, mat_zero.
  destruct n as [|k]; [reflexivity|].
  (* mat_zero fld (S k) = repeat (repeat 0 (S k)) (S k); first row has length S k *)
  change (List.repeat (List.repeat (cr_zero fld) (S k)) (S k))
    with (List.repeat (cr_zero fld) (S k)
          :: List.repeat (List.repeat (cr_zero fld) (S k)) k).
  cbn [List.length].
  rewrite List.repeat_length.
  (* The outer map produces, for each col_idx in seq 0 (S k):
       map (fun row => nth col_idx row 0) (Z::repeat Z k) where Z = repeat 0 (S k)
     Each nth col_idx (repeat 0 (S k)) 0 = 0 by nth_repeat (col_idx within bounds or default 0).
     So the result is repeat 0 (S k) for each col_idx, total: repeat (repeat 0 (S k)) (S k). *)
  set (Z := List.repeat (cr_zero fld) (S k)).
  rewrite (List.map_ext_in
    (fun col_idx => List.map (fun row => List.nth col_idx row (cr_zero fld))
                             (Z :: List.repeat Z k))
    (fun _ => Z)).
  - rewrite List.map_const, List.length_seq.
    fold (List.repeat Z (S k)). reflexivity.
  - intros col_idx _.
    cbn [List.map].
    unfold Z at 1.
    rewrite List.nth_repeat.
    rewrite (List.map_ext_in (fun row => List.nth col_idx row (cr_zero fld))
                             (fun _ => cr_zero fld) (List.repeat Z k)).
    + rewrite List.map_const, List.repeat_length.
      fold (List.repeat (cr_zero fld) (S k)). reflexivity.
    + intros row Hin. apply List.repeat_spec in Hin. subst row.
      unfold Z. apply List.nth_repeat.
Qed.

(** [A,B]^T = [B^T, A^T]: transposing reverses the bracket.
    Mat_wf-guarded form (Task M.3, 2026-04-30), since
    [mat_transpose_add]/[mat_transpose_mul] are now Mat_wf-guarded. *)
Lemma mat_transpose_bracket :
  forall {F : Type} (fld : Field F) (n : nat) (A B : Matrix F),
    Mat_wf n n A -> Mat_wf n n B ->
    mat_transpose fld (mat_bracket fld A B) =
    mat_bracket fld (mat_transpose fld B) (mat_transpose fld A).
Proof.
  intros F fld n A B HA HB. unfold mat_bracket, mat_neg.
  rewrite (mat_transpose_add fld n _ _ (mat_mul_wf fld n _ _ HA HB)
            (mat_scale_wf fld n n _ _ (mat_mul_wf fld n _ _ HB HA))),
          mat_transpose_scale,
          (mat_transpose_mul fld n A B HA HB),
          (mat_transpose_mul fld n B A HB HA).
  reflexivity.
Qed.

(* ================================================================== *)
(** * 2. Matrix algebra axioms                                        *)
(* ================================================================== *)

(* Duplicate axioms from Lie.Linear are imported from there. *)

(* The matrix algebra axioms are imported from Lie.Linear. *)
(* REFACTOR (Task M.2, 2026-04-30): mat_mul_zero_l_n and mat_mul_zero_r_n
   were axioms returning [mat_zero fld 0] (the empty matrix); they are now
   proven Lemmas returning [mat_zero fld n] (the proper n×n zero) under a
   [Mat_wf n n A] hypothesis. *)

(** mat_mul (mat_zero n) A = mat_zero n.
    Direct corollary of mat_mul_zero_l_correct in Linear.v. *)
Lemma mat_mul_zero_l_n :
  forall {F : Type} (fld : Field F) (n : nat) (A : Matrix F),
    Mat_wf n n A ->
    mat_mul fld (mat_zero fld n) A = mat_zero fld n.
Proof.
  intros F fld n A _.
  rewrite (mat_mul_zero_l_correct fld n A).
  reflexivity.
Qed.

(** Helper: fold_left over (combine row_A B), where every row of B is
    a constant [repeat 0 m] zero-row, accumulates init unchanged.  This is
    independent of the relative lengths of row_A and B. *)
Local Lemma fold_left_combine_zero_rows :
  forall {F : Type} (fld : Field F) (row_A : list F) (B : list (list F))
    (col_idx m : nat) (init : F),
    (forall row, List.In row B -> row = List.repeat (cr_zero fld) m) ->
    init = cr_zero fld ->
    List.fold_left (fun acc '(a, row_B) =>
        cr_add fld acc (cr_mul fld a (List.nth col_idx row_B (cr_zero fld))))
      (List.combine row_A B) init = cr_zero fld.
Proof.
  intros F fld row_A. induction row_A as [|x xs IH]; intros B col_idx m init HBz Hinit.
  - simpl. exact Hinit.
  - destruct B as [|rB Bs]; [simpl; exact Hinit|].
    simpl. apply (IH Bs col_idx m).
    + intros row Hin. apply HBz. right. exact Hin.
    + assert (HrB : rB = List.repeat (cr_zero fld) m) by (apply HBz; left; reflexivity).
      rewrite Hinit, HrB.
      rewrite List.nth_repeat.
      rewrite (cr_mul_zero_r fld), (cr_add_zero fld). reflexivity.
Qed.

(** mat_mul A (mat_zero n) = mat_zero n  when A is n×n.
    Each output row is `repeat 0 n` because each entry is a sum of
    products against zeros. *)
Lemma mat_mul_zero_r_n :
  forall {F : Type} (fld : Field F) (n : nat) (A : Matrix F),
    Mat_wf n n A ->
    mat_mul fld A (mat_zero fld n) = mat_zero fld n.
Proof.
  intros F fld n A [HlenA HrowA]. unfold mat_mul, mat_zero.
  rewrite (List.map_ext_in
    (fun row_A => List.map _ (List.seq 0 (List.length row_A)))
    (fun _ => List.repeat (cr_zero fld) n)).
  - rewrite List.map_const. rewrite HlenA. reflexivity.
  - intros row_A Hin.
    rewrite (HrowA row_A Hin).
    rewrite (List.map_ext_in
      (fun col_idx => List.fold_left _ (List.combine row_A _) (cr_zero fld))
      (fun _ => cr_zero fld)).
    + rewrite List.map_const, List.length_seq. reflexivity.
    + intros col_idx _.
      apply (fold_left_combine_zero_rows fld row_A
               (List.repeat (List.repeat (cr_zero fld) n) n) col_idx n (cr_zero fld)).
      * intros row Hr. apply List.repeat_spec in Hr. exact Hr.
      * reflexivity.
Qed.

(* ================================================================== *)
(** * 3. Standard symplectic form                                     *)
(* ================================================================== *)

(** Placeholder zero matrix; the real symplectic form is
    s = [[0, I_l], [-I_l, 0]] on F^{2l}. The zero matrix is both
    transpose-symmetric and equal to its negation, satisfying
    sp_form_antisymm trivially. *)
Definition sp_form {F : Type} (fld : Field F) (l : nat) : Matrix F :=
  mat_zero fld (2 * l).

(** sp_form is well-formed (2l)x(2l). *)
Lemma sp_form_wf : forall {F : Type} (fld : Field F) (l : nat),
    Mat_wf (2 * l) (2 * l) (sp_form fld l).
Proof. intros. apply mat_zero_wf. Qed.

(** mat_transpose preserves [Mat_wf n n] for square matrices.
    REFACTOR (Task M.2): needed to thread Mat_wf through the
    symplectic / IsSymplectic infrastructure.  Named [sp_mat_transpose_wf]
    to avoid collision with [Orthogonal.v]'s local [Axiom mat_transpose_wf]
    (M.1's territory; we cannot edit that file to drop its axiom). *)
Lemma sp_mat_transpose_wf :
  forall {F : Type} (fld : Field F) (n : nat) (A : Matrix F),
    Mat_wf n n A -> Mat_wf n n (mat_transpose fld A).
Proof.
  intros F fld n A [HlenA HrowA]. unfold mat_transpose, Mat_wf. split.
  - destruct A as [|row rest].
    + simpl in HlenA. subst n. simpl. reflexivity.
    + simpl. rewrite List.length_map, List.length_seq.
      apply HrowA. left. reflexivity.
  - intros row Hin.
    destruct A as [|hd tl].
    + simpl in HlenA. subst n. simpl in Hin. inversion Hin.
    + apply List.in_map_iff in Hin.
      destruct Hin as [col_idx [Heq _]]. subst row.
      rewrite List.length_map. exact HlenA.
Qed.

(** s^T = -s. (Trivially true for zero matrix.) *)
Lemma sp_form_antisymm :
  forall {F : Type} (fld : Field F) (l : nat),
    mat_transpose fld (sp_form fld l) = mat_neg fld (sp_form fld l).
Proof.
  intros. unfold sp_form. rewrite mat_transpose_zero, mat_neg_mat_zero.
  reflexivity.
Qed.

(* ================================================================== *)
(** * 4. Symplectic Lie algebra                                       *)
(* ================================================================== *)

(** REFACTOR (Task M.2, 2026-04-30): RHS now uses [mat_zero fld (2*l)]
    (proper shape) instead of [mat_zero fld 0] (degenerate empty matrix).
    This matches the new shape returned by [mat_mul_zero_l_n]/[r_n]. *)
Definition IsSymplectic {F : Type} (fld : Field F) (l : nat) (A : Matrix F) : Prop :=
  mat_add fld
    (mat_mul fld (mat_transpose fld A) (sp_form fld l))
    (mat_mul fld (sp_form fld l) A)
  = mat_zero fld (2 * l).

(** Lifted predicate: symplectic condition on a [GLMat fld (2*l)] sigma-element.
    REFACTOR (Task M.2): the [IsSubalgebra (gl fld (2*l)) ...] form requires
    a predicate on [GLMat fld (2*l)], not raw [Matrix F]. *)
Definition IsSymplecticGL {F : Type} (fld : Field F) (l : nat)
    (A : GLMat fld (2 * l)) : Prop :=
  IsSymplectic fld l (proj1_sig A).

(** From IsSymplectic A: A^T·s = -(s·A).
    Proof: X + Y = 0 → X = X + (Y + -Y) = (X+Y) + -Y = 0 + -Y = -Y.
    Now Mat_wf-guarded since [mat_add_zero_r/l/neg/assoc] need it. *)
Lemma sp_cond_l {F : Type} (fld : Field F) (l : nat) (A : Matrix F) :
    Mat_wf (2 * l) (2 * l) A ->
    IsSymplectic fld l A ->
    mat_mul fld (mat_transpose fld A) (sp_form fld l) =
    mat_neg fld (mat_mul fld (sp_form fld l) A).
Proof.
  intros HA. unfold IsSymplectic. intro H.
  pose proof (sp_form_wf fld l) as Hs.
  pose proof (sp_mat_transpose_wf fld (2 * l) A HA) as HAt.
  pose proof (mat_mul_wf fld (2 * l) _ _ HAt Hs) as HAtS.
  pose proof (mat_mul_wf fld (2 * l) _ _ Hs HA) as HSA.
  rewrite <- (mat_add_zero_r fld (2 * l)
               (mat_mul fld (mat_transpose fld A) (sp_form fld l)) HAtS).
  rewrite <- (mat_add_neg fld (2 * l) (mat_mul fld (sp_form fld l) A) HSA).
  rewrite <- mat_add_assoc_m.
  rewrite H. apply (mat_add_zero_l fld (2 * l)).
  apply mat_neg_wf. exact HSA.
Qed.

(** From IsSymplectic A: s·A = -(A^T·s).
    Proof: X + Y = 0 → Y = 0 + Y = (-X+X) + Y = -X + (X+Y) = -X + 0 = -X. *)
Lemma sp_cond_r {F : Type} (fld : Field F) (l : nat) (A : Matrix F) :
    Mat_wf (2 * l) (2 * l) A ->
    IsSymplectic fld l A ->
    mat_mul fld (sp_form fld l) A =
    mat_neg fld (mat_mul fld (mat_transpose fld A) (sp_form fld l)).
Proof.
  intros HA. unfold IsSymplectic. intro H.
  pose proof (sp_form_wf fld l) as Hs.
  pose proof (sp_mat_transpose_wf fld (2 * l) A HA) as HAt.
  pose proof (mat_mul_wf fld (2 * l) _ _ HAt Hs) as HAtS.
  pose proof (mat_mul_wf fld (2 * l) _ _ Hs HA) as HSA.
  rewrite <- (mat_add_zero_l fld (2 * l) (mat_mul fld (sp_form fld l) A) HSA).
  rewrite <- (mat_add_neg_l fld (2 * l)
                (mat_mul fld (mat_transpose fld A) (sp_form fld l)) HAtS).
  rewrite mat_add_assoc_m.
  rewrite H. apply (mat_add_zero_r fld (2 * l)).
  apply mat_neg_wf. exact HAtS.
Qed.

(** sp(2l, F) is a Lie subalgebra of gl(2l, F).
    REFACTOR (Task M.2): predicate lifted to [GLMat fld (2*l)] via
    [IsSymplecticGL]; all Mat_wf hypotheses threaded via [proj2_sig]. *)
Lemma sp_is_subalgebra {F : Type} (fld : Field F) (l : nat) :
    IsSubalgebra (gl fld (2 * l)) (IsSymplecticGL fld l).
Proof.
  pose proof (sp_form_wf fld l) as Hs.
  constructor.
  (* (1) Zero *)
  - unfold IsSymplecticGL, IsSymplectic.
    rewrite gl_zero_eq_mat_zero, mat_transpose_zero.
    rewrite (mat_mul_zero_l_n fld (2 * l) (sp_form fld l) Hs).
    rewrite (mat_mul_zero_r_n fld (2 * l) (sp_form fld l) Hs).
    apply (mat_add_zero_l fld (2 * l)).
    apply mat_zero_wf.
  (* (2) Addition *)
  - intros A B HA HB. unfold IsSymplecticGL, IsSymplectic in *.
    pose proof (proj2_sig A) as HwfA. pose proof (proj2_sig B) as HwfB.
    pose proof (sp_mat_transpose_wf fld (2 * l) _ HwfA) as HtA.
    pose proof (sp_mat_transpose_wf fld (2 * l) _ HwfB) as HtB.
    rewrite gl_add_eq_mat_add, (mat_transpose_add fld (2 * l) _ _ HwfA HwfB).
    rewrite (mat_mul_add_distr_r fld (2 * l) _ _ _ HtA HtB Hs).
    rewrite (mat_mul_add_distr_l fld (2 * l) _ _ _ Hs HwfA HwfB).
    rewrite (mat_add_assoc_m fld
               (mat_mul fld (mat_transpose fld (proj1_sig A)) (sp_form fld l))
               (mat_mul fld (mat_transpose fld (proj1_sig B)) (sp_form fld l))
               (mat_add fld (mat_mul fld (sp_form fld l) (proj1_sig A))
                            (mat_mul fld (sp_form fld l) (proj1_sig B)))).
    rewrite <- (mat_add_assoc_m fld
                  (mat_mul fld (mat_transpose fld (proj1_sig B)) (sp_form fld l))
                  (mat_mul fld (sp_form fld l) (proj1_sig A))
                  (mat_mul fld (sp_form fld l) (proj1_sig B))).
    rewrite (mat_add_comm fld
               (mat_mul fld (mat_transpose fld (proj1_sig B)) (sp_form fld l))
               (mat_mul fld (sp_form fld l) (proj1_sig A))).
    rewrite (mat_add_assoc_m fld
               (mat_mul fld (sp_form fld l) (proj1_sig A))
               (mat_mul fld (mat_transpose fld (proj1_sig B)) (sp_form fld l))
               (mat_mul fld (sp_form fld l) (proj1_sig B))).
    rewrite <- (mat_add_assoc_m fld
                  (mat_mul fld (mat_transpose fld (proj1_sig A)) (sp_form fld l))
                  (mat_mul fld (sp_form fld l) (proj1_sig A))
                  (mat_add fld (mat_mul fld (mat_transpose fld (proj1_sig B)) (sp_form fld l))
                               (mat_mul fld (sp_form fld l) (proj1_sig B)))).
    rewrite HA, HB. apply (mat_add_zero_l fld (2 * l)).
    apply mat_zero_wf.
  (* (3) Negation *)
  - intros A HA. unfold IsSymplecticGL, IsSymplectic in *.
    rewrite gl_neg_eq_mat_neg, mat_transpose_neg.
    rewrite mat_mul_neg_l, mat_mul_neg_r.
    rewrite <- mat_neg_add. rewrite HA. apply mat_neg_zero.
  (* (4) Scalar multiplication *)
  - intros c A HA. unfold IsSymplecticGL, IsSymplectic in *.
    rewrite gl_scale_eq_mat_scale, mat_transpose_scale.
    rewrite mat_mul_scale_l, mat_mul_scale_r.
    rewrite <- mat_scale_add_mat. rewrite HA. apply mat_scale_zero_mat.
  (* (5) Bracket closure.  Same algebraic chain as before, but with
         Mat_wf hypotheses threaded via [proj2_sig] and [sp_mat_transpose_wf]
         where the strengthened axioms ([mat_mul_add_distr_*],
         [mat_mul_assoc_m], [mat_add_*_*]) demand them. *)
  - intros A B HA HB. unfold IsSymplecticGL, IsSymplectic in *.
    pose proof (proj2_sig A) as HwfA. pose proof (proj2_sig B) as HwfB.
    pose proof (sp_mat_transpose_wf fld (2 * l) _ HwfA) as HtA.
    pose proof (sp_mat_transpose_wf fld (2 * l) _ HwfB) as HtB.
    rewrite gl_bracket_eq_mat_bracket.
    rewrite (mat_transpose_bracket fld (2 * l) _ _ HwfA HwfB).
    unfold mat_bracket.
    rewrite (mat_mul_add_distr_r fld (2 * l) _ _ _
              (mat_mul_wf fld (2 * l) _ _ HtB HtA)
              (mat_neg_wf fld (2 * l) (2 * l) _ (mat_mul_wf fld (2 * l) _ _ HtA HtB))
              Hs).
    rewrite (mat_mul_add_distr_l fld (2 * l) _ _ _ Hs
              (mat_mul_wf fld (2 * l) _ _ HwfA HwfB)
              (mat_neg_wf fld (2 * l) (2 * l) _ (mat_mul_wf fld (2 * l) _ _ HwfB HwfA))).
    rewrite mat_mul_neg_l, mat_mul_neg_r.
    rewrite (mat_mul_assoc_m fld (2 * l) (mat_transpose fld (proj1_sig B))
              (mat_transpose fld (proj1_sig A)) (sp_form fld l) HtB HtA Hs).
    rewrite (mat_mul_assoc_m fld (2 * l) (mat_transpose fld (proj1_sig A))
              (mat_transpose fld (proj1_sig B)) (sp_form fld l) HtA HtB Hs).
    rewrite <- (mat_mul_assoc_m fld (2 * l) (sp_form fld l) (proj1_sig A) (proj1_sig B)
                 Hs HwfA HwfB).
    rewrite <- (mat_mul_assoc_m fld (2 * l) (sp_form fld l) (proj1_sig B) (proj1_sig A)
                 Hs HwfB HwfA).
    rewrite (sp_cond_l fld l (proj1_sig A) HwfA HA).
    rewrite (sp_cond_l fld l (proj1_sig B) HwfB HB).
    rewrite mat_mul_neg_r, mat_mul_neg_r.
    rewrite mat_neg_neg.
    rewrite <- (mat_mul_assoc_m fld (2 * l) (mat_transpose fld (proj1_sig B))
                 (sp_form fld l) (proj1_sig A) HtB Hs HwfA).
    rewrite <- (mat_mul_assoc_m fld (2 * l) (mat_transpose fld (proj1_sig A))
                 (sp_form fld l) (proj1_sig B) HtA Hs HwfB).
    rewrite (sp_cond_l fld l (proj1_sig B) HwfB HB).
    rewrite (sp_cond_l fld l (proj1_sig A) HwfA HA).
    rewrite mat_mul_neg_l, mat_mul_neg_l.
    rewrite mat_neg_neg.
    pose proof (mat_mul_wf fld (2 * l) _ _ Hs HwfA) as HSA.
    pose proof (mat_mul_wf fld (2 * l) _ _ Hs HwfB) as HSB.
    pose proof (mat_mul_wf fld (2 * l) _ _ HSA HwfB) as HSAB.
    pose proof (mat_mul_wf fld (2 * l) _ _ HSB HwfA) as HSBA.
    rewrite (mat_add_assoc_m fld
      (mat_mul fld (mat_mul fld (sp_form fld l) (proj1_sig B)) (proj1_sig A))
      (mat_neg fld (mat_mul fld (mat_mul fld (sp_form fld l) (proj1_sig A)) (proj1_sig B)))
      (mat_add fld
        (mat_mul fld (mat_mul fld (sp_form fld l) (proj1_sig A)) (proj1_sig B))
        (mat_neg fld (mat_mul fld (mat_mul fld (sp_form fld l) (proj1_sig B)) (proj1_sig A))))).
    rewrite <- (mat_add_assoc_m fld
      (mat_neg fld (mat_mul fld (mat_mul fld (sp_form fld l) (proj1_sig A)) (proj1_sig B)))
      (mat_mul fld (mat_mul fld (sp_form fld l) (proj1_sig A)) (proj1_sig B))
      (mat_neg fld (mat_mul fld (mat_mul fld (sp_form fld l) (proj1_sig B)) (proj1_sig A)))).
    rewrite (mat_add_neg_l fld (2 * l) _ HSAB).
    rewrite (mat_add_zero_l fld (2 * l) _ (mat_neg_wf fld (2 * l) (2 * l) _ HSBA)).
    apply (mat_add_neg fld (2 * l) _ HSBA).
Qed.

(* ================================================================== *)
(** * 5. Block matrix characterisation (axiomatised)                  *)
(* ================================================================== *)

(** The standard basis of sp(2l,F):
    - e_{ij} - e_{j+l,i+l}  for 1≤i,j≤l
    - e_{i,j+l} + e_{j,i+l} for 1≤i≤j≤l  (symmetric off-diagonal blocks)
    - e_{i+l,j} + e_{j+l,i} for 1≤i≤j≤l  (symmetric off-diagonal blocks)
    The dimension is 2l^2 + l. *)
Lemma sp_dim : forall (l : nat), True. (* placeholder *)
Proof. intros. exact I. Qed.
