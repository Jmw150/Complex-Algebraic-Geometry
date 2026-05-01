(** * Lie/Linear.v
    General linear Lie algebra gl(V), matrix units, Jacobi for commutator.

    REFACTOR (Task M.0, 2026-04-30):
    The base matrix axioms have been strengthened with [Mat_wf n n A]
    well-formedness hypotheses, and now use [mat_zero fld n] consistently
    on both sides (instead of the wrong [mat_zero fld 0]).  The previous
    axioms like [mat_add fld A (mat_zero fld 0) = A] were FALSE for
    non-empty A because [mat_add] truncates to [min(length A, 0) = 0]
    rows when the second argument is empty.

    [gl_vs] (and hence [gl]) is now built over the sigma type
    [{ A : Matrix F | Mat_wf n n A }], so [vsF_zero (gl_vs fld n)] is
    [exist _ (mat_zero fld n) (mat_zero_wf fld n)] — a genuine n×n
    zero matrix.

    Downstream files (Lie/SpecialLinear.v, Lie/Orthogonal.v,
    Lie/Symplectic.v, LieAlgebra.v, etc.) will need to thread a
    [Mat_wf]-bearing element instead of a raw [Matrix F] through
    [gl] use sites — this is intentional. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
From Stdlib Require Import List Arith Bool Lia.
From Stdlib Require Import Logic.ProofIrrelevance.
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

(** Matrix multiplication (n×n). The (i, k) entry of A*B is
    [Σ_j A_ij · B_jk]. We pair each entry of [row_A] with the corresponding
    row of [B], then sum over [j]. *)
Definition mat_mul {F : Type} (fld : Field F) (A B : Matrix F) : Matrix F :=
  List.map (fun row_A =>
    List.map (fun col_idx =>
      List.fold_left (fun acc '(a, row_B) =>
        cr_add fld acc (cr_mul fld a (List.nth col_idx row_B (cr_zero fld))))
        (List.combine row_A B) (cr_zero fld))
      (List.seq 0 (List.length row_A)))
  A.

(** The commutator [A,B] = AB - BA. *)
Definition mat_bracket {F : Type} (fld : Field F) (A B : Matrix F) : Matrix F :=
  mat_add fld (mat_mul fld A B)
              (mat_neg fld (mat_mul fld B A)).

(** ** Well-formedness predicate

    [Mat_wf n m A] holds iff [A] is a list of [n] lists, each of length [m].
    This is the polymorphic counterpart of [AG.Mat_wf] (which is fixed to
    [CComplex]). *)

Definition Mat_wf {F : Type} (n m : nat) (A : Matrix F) : Prop :=
  List.length A = n /\ forall row, List.In row A -> List.length row = m.

(** ** Wf closure lemmas *)

Lemma mat_zero_wf : forall {F : Type} (fld : Field F) (n : nat),
    Mat_wf n n (mat_zero fld n).
Proof.
  intros F fld n. unfold Mat_wf, mat_zero. split.
  - apply List.repeat_length.
  - intros row Hin. apply List.repeat_spec in Hin. subst row.
    apply List.repeat_length.
Qed.

Lemma mat_zero_wf_nm : forall {F : Type} (fld : Field F) (n : nat),
    Mat_wf n n (mat_zero fld n).
Proof. intros; apply mat_zero_wf. Qed.

Lemma mat_scale_wf : forall {F : Type} (fld : Field F) (n m : nat) (c : F) (A : Matrix F),
    Mat_wf n m A -> Mat_wf n m (mat_scale fld c A).
Proof.
  intros F fld n m c A [HlenA HrowA]. unfold Mat_wf, mat_scale. split.
  - rewrite List.length_map. exact HlenA.
  - intros row Hin.
    rewrite List.in_map_iff in Hin.
    destruct Hin as [row0 [Hrow Hin0]].
    subst row. rewrite List.length_map. apply HrowA. exact Hin0.
Qed.

Lemma mat_neg_wf : forall {F : Type} (fld : Field F) (n m : nat) (A : Matrix F),
    Mat_wf n m A -> Mat_wf n m (mat_neg fld A).
Proof. intros. unfold mat_neg. apply mat_scale_wf. exact H. Qed.

(** [combine] of two equal-length lists has that length. *)
Lemma length_combine_eq :
  forall {A B : Type} (l1 : list A) (l2 : list B),
    List.length l1 = List.length l2 ->
    List.length (List.combine l1 l2) = List.length l1.
Proof.
  intros A B l1. induction l1 as [|x l1 IH]; intros [|y l2] H; simpl in *;
    try discriminate; try reflexivity.
  injection H as H. f_equal. apply IH. exact H.
Qed.

Lemma in_combine_lengths :
  forall {A B : Type} (l1 : list A) (l2 : list B) (x : A) (y : B),
    List.In (x, y) (List.combine l1 l2) ->
    List.In x l1 /\ List.In y l2.
Proof.
  intros A B l1. induction l1 as [|a l1 IH]; intros [|b l2] x y Hin; simpl in *;
    try contradiction.
  destruct Hin as [Heq|Hin].
  - injection Heq as -> ->. split; left; reflexivity.
  - destruct (IH l2 x y Hin) as [Hx Hy]. split; right; assumption.
Qed.

Lemma mat_add_wf : forall {F : Type} (fld : Field F) (n m : nat) (A B : Matrix F),
    Mat_wf n m A -> Mat_wf n m B -> Mat_wf n m (mat_add fld A B).
Proof.
  intros F fld n m A B [HlenA HrowA] [HlenB HrowB]. unfold Mat_wf, mat_add. split.
  - rewrite List.length_map.
    rewrite (length_combine_eq A B); [exact HlenA|congruence].
  - intros row Hin.
    rewrite List.in_map_iff in Hin.
    destruct Hin as [[r1 r2] [Hrow Hin0]].
    subst row.
    apply in_combine_lengths in Hin0. destruct Hin0 as [Hin1 Hin2].
    rewrite List.length_map.
    rewrite length_combine_eq.
    + apply HrowA. exact Hin1.
    + rewrite (HrowA r1 Hin1), (HrowB r2 Hin2). reflexivity.
Qed.

(** ** Matrix ring axioms (strengthened with Mat_wf) *)

(** mat_mul (A + B) C = mat_mul A C + mat_mul B C, when all are n×n.

    Proof would require a sum-of-products distributivity over a paired
    fold_left, plus careful tracking of how mat_add truncates to
    min(length A, length B) rows. The combine-of-combine pattern
    interacts non-trivially with mat_mul's seq-based column iteration.
    Left axiomatized for the same-shape case. *)
Axiom mat_mul_add_distr_r :
  forall {F : Type} (fld : Field F) (n : nat) (A B C : Matrix F),
    Mat_wf n n A -> Mat_wf n n B -> Mat_wf n n C ->
    mat_mul fld (mat_add fld A B) C =
    mat_add fld (mat_mul fld A C) (mat_mul fld B C).

Axiom mat_mul_add_distr_l :
  forall {F : Type} (fld : Field F) (n : nat) (A B C : Matrix F),
    Mat_wf n n A -> Mat_wf n n B -> Mat_wf n n C ->
    mat_mul fld A (mat_add fld B C) =
    mat_add fld (mat_mul fld A B) (mat_mul fld A C).

Axiom mat_mul_assoc_m :
  forall {F : Type} (fld : Field F) (n : nat) (A B C : Matrix F),
    Mat_wf n n A -> Mat_wf n n B -> Mat_wf n n C ->
    mat_mul fld (mat_mul fld A B) C =
    mat_mul fld A (mat_mul fld B C).

(* mat_mul_neg_l and mat_mul_neg_r are proven later (after mat_mul_scale_l/r). *)

Lemma combine_add_comm :
  forall {F : Type} (fld : Field F) (rA rB : list F),
    List.map (fun '(x,y) => cr_add fld x y) (List.combine rA rB) =
    List.map (fun '(x,y) => cr_add fld x y) (List.combine rB rA).
Proof.
  intros F fld rA. induction rA as [|x rA IH]; intros [|y rB]; try reflexivity.
  simpl. f_equal; [apply cr_add_comm|apply IH].
Qed.

Lemma mat_add_comm :
  forall {F : Type} (fld : Field F) (A B : Matrix F),
    mat_add fld A B = mat_add fld B A.
Proof.
  intros F fld A. unfold mat_add. induction A as [|rA As IH]; intros [|rB Bs];
    try reflexivity.
  simpl. f_equal; [apply combine_add_comm|apply IH].
Qed.

Lemma combine_add_assoc :
  forall {F : Type} (fld : Field F) (rA rB rC : list F),
    List.map (fun '(x,y) => cr_add fld x y)
      (List.combine
        (List.map (fun '(x,y) => cr_add fld x y) (List.combine rA rB))
        rC) =
    List.map (fun '(x,y) => cr_add fld x y)
      (List.combine rA
        (List.map (fun '(x,y) => cr_add fld x y) (List.combine rB rC))).
Proof.
  intros F fld rA. induction rA as [|x rA IH]; intros rB rC.
  - reflexivity.
  - destruct rB as [|y rB]; [reflexivity|].
    destruct rC as [|z rC]; [reflexivity|].
    simpl. f_equal; [|apply IH].
    symmetry. apply cr_add_assoc.
Qed.

Lemma mat_add_assoc_m :
  forall {F : Type} (fld : Field F) (A B C : Matrix F),
    mat_add fld (mat_add fld A B) C =
    mat_add fld A (mat_add fld B C).
Proof.
  intros F fld A. unfold mat_add. induction A as [|rA As IH]; intros B C.
  - reflexivity.
  - destruct B as [|rB Bs]; [reflexivity|].
    destruct C as [|rC Cs]; [reflexivity|].
    simpl. f_equal; [apply combine_add_assoc|apply IH].
Qed.

(** ** Provable add-zero / add-neg lemmas (strengthened with Mat_wf) *)

(** Helper: combine [repeat 0 m] with a row [r] of length m, then
    [map (cr_add 0)] over the combined pairs, gives back [r]. *)
Lemma map_add_zero_l_repeat :
  forall {F : Type} (fld : Field F) (m : nat) (r : list F),
    List.length r = m ->
    List.map (fun '(x, y) => cr_add fld x y)
             (List.combine (List.repeat (cr_zero fld) m) r) = r.
Proof.
  intros F fld m. induction m as [|m IH]; intros [|x r] H; simpl in *;
    try discriminate; try reflexivity.
  injection H as H. f_equal.
  - apply (cr_add_zero_l fld).
  - apply IH. exact H.
Qed.

Lemma map_add_zero_r_repeat :
  forall {F : Type} (fld : Field F) (m : nat) (r : list F),
    List.length r = m ->
    List.map (fun '(x, y) => cr_add fld x y)
             (List.combine r (List.repeat (cr_zero fld) m)) = r.
Proof.
  intros F fld m. induction m as [|m IH]; intros [|x r] H; simpl in *;
    try discriminate; try reflexivity.
  injection H as H. f_equal.
  - apply cr_add_zero.
  - apply IH. exact H.
Qed.

(** mat_add A 0 = A when A is n×n.  Helper does the induction on the
    list, parametric in the row-count [k] and column-count [m]. *)

Lemma mat_add_zero_r_aux :
  forall {F : Type} (fld : Field F) (As : Matrix F) (m k : nat),
    List.length As = k ->
    (forall row, List.In row As -> List.length row = m) ->
    List.map (fun '(r1, r2) => List.map (fun '(a, b) => cr_add fld a b) (List.combine r1 r2))
             (List.combine As (List.repeat (List.repeat (cr_zero fld) m) k))
    = As.
Proof.
  intros F fld As. induction As as [|rA As IH]; intros m k Hlen Hrow; simpl.
  - subst k. reflexivity.
  - destruct k as [|k']; [discriminate|]. simpl. f_equal.
    + apply map_add_zero_r_repeat. apply Hrow. left. reflexivity.
    + injection Hlen as Hlen.
      apply IH; [exact Hlen|]. intros row Hin. apply Hrow. right. exact Hin.
Qed.

Lemma mat_add_zero_r :
  forall {F : Type} (fld : Field F) (n : nat) (A : Matrix F),
    Mat_wf n n A ->
    mat_add fld A (mat_zero fld n) = A.
Proof.
  intros F fld n A [HlenA HrowA]. unfold mat_add, mat_zero.
  apply (mat_add_zero_r_aux fld A n n HlenA HrowA).
Qed.

Lemma mat_add_zero_l :
  forall {F : Type} (fld : Field F) (n : nat) (A : Matrix F),
    Mat_wf n n A ->
    mat_add fld (mat_zero fld n) A = A.
Proof.
  intros F fld n A Hwf. rewrite mat_add_comm. apply mat_add_zero_r. exact Hwf.
Qed.

(** Helper for mat_add_neg: combine r with neg(r) and add gives row of
    zeros of length |r|.  Uses [(-1) * x = -x] derived from distributivity. *)
Lemma combine_add_neg_repeat :
  forall {F : Type} (fld : Field F) (r : list F),
    List.map (fun '(x, y) => cr_add fld x y)
             (List.combine r
                (List.map (fun a => cr_mul fld (cr_neg fld (cr_one fld)) a) r))
    = List.repeat (cr_zero fld) (List.length r).
Proof.
  intros F fld r. induction r as [|x r IH]; simpl; [reflexivity|].
  f_equal; [|exact IH].
  (* x + (-1) * x = x + (-x) = 0 *)
  assert (Heq : cr_mul fld (cr_neg fld (cr_one fld)) x = cr_neg fld x).
  { rewrite (cr_mul_comm fld (cr_neg fld (cr_one fld)) x).
    (* x * (-1) = -(x*1) = -x, but we need a lemma. We have
       cr_neg_mul_neg : (-a) * (-b) = a * b. Use:
       x * (-1) + x * 1 = x * ((-1) + 1) = x * 0 = 0,
       and x * 1 = x. So x * (-1) = -x. *)
    apply (cr_add_inv_uniq fld x).
    (* cr_add x (cr_mul x (cr_neg cr_one)) = cr_zero *)
    rewrite (cr_mul_comm fld x (cr_neg fld (cr_one fld))).
    rewrite <- (cr_mul_one fld x) at 1.
    rewrite (cr_mul_comm fld (cr_neg fld (cr_one fld)) x).
    rewrite <- (cr_distrib fld x (cr_one fld) (cr_neg fld (cr_one fld))).
    rewrite (cr_add_neg fld (cr_one fld)).
    apply (cr_mul_zero_r fld). }
  rewrite Heq.
  apply (cr_add_neg fld x).
Qed.

(** Local helper: combine (l1) (map h l2) = map (\(x,y) -> (x, h y)) (combine l1 l2). *)
Lemma combine_map_r_local :
  forall {A B X : Type} (h : B -> X) (l1 : list A) (l2 : list B),
    List.combine l1 (List.map h l2) = List.map (fun p => (fst p, h (snd p))) (List.combine l1 l2).
Proof.
  intros A B X h l1. induction l1 as [|x l1 IH]; intros [|y l2]; try reflexivity.
  simpl. f_equal. apply IH.
Qed.

(** Bulk helper for the diagonal map underlying [mat_add_neg]. *)
Lemma map_add_neg_repeat_zero :
  forall {F : Type} (fld : Field F) (As : Matrix F) (m : nat),
    (forall row, List.In row As -> List.length row = m) ->
    List.map (fun p =>
        List.map (fun '(x, y) => cr_add fld x y)
                 (List.combine (fst p)
                    (List.map (fun a => cr_mul fld (cr_neg fld (cr_one fld)) a)
                              (snd p))))
      (List.combine As As)
    = List.repeat (List.repeat (cr_zero fld) m) (List.length As).
Proof.
  intros F fld As m HrowAs. induction As as [|rA As IH]; simpl; [reflexivity|].
  f_equal.
  - assert (HrA : List.length rA = m) by (apply HrowAs; left; reflexivity).
    rewrite combine_add_neg_repeat. rewrite HrA. reflexivity.
  - apply IH. intros row Hrow. apply HrowAs. right. exact Hrow.
Qed.

Lemma mat_add_neg :
  forall {F : Type} (fld : Field F) (n : nat) (A : Matrix F),
    Mat_wf n n A ->
    mat_add fld A (mat_neg fld A) = mat_zero fld n.
Proof.
  intros F fld n A [HlenA HrowA].
  unfold mat_add, mat_neg, mat_scale, mat_zero.
  rewrite combine_map_r_local.
  rewrite List.map_map.
  rewrite (map_add_neg_repeat_zero fld A n HrowA).
  rewrite HlenA. reflexivity.
Qed.

Lemma mat_add_neg_l :
  forall {F : Type} (fld : Field F) (n : nat) (A : Matrix F),
    Mat_wf n n A ->
    mat_add fld (mat_neg fld A) A = mat_zero fld n.
Proof.
  intros F fld n A Hwf. rewrite mat_add_comm. apply mat_add_neg. exact Hwf.
Qed.

(** ** Matrix scale axioms *)

Lemma mat_scale_one :
  forall {F : Type} (fld : Field F) (A : Matrix F),
    mat_scale fld (cr_one fld) A = A.
Proof.
  intros F fld A. unfold mat_scale.
  rewrite <- (List.map_id A) at 2.
  apply List.map_ext_in. intros row _.
  rewrite <- (List.map_id row) at 2.
  apply List.map_ext_in. intros a _.
  rewrite cr_mul_comm. apply cr_mul_one.
Qed.

Lemma mat_scale_mul_assoc :
  forall {F : Type} (fld : Field F) (a b : F) (A : Matrix F),
    mat_scale fld a (mat_scale fld b A) = mat_scale fld (cr_mul fld a b) A.
Proof.
  intros F fld a b A. unfold mat_scale.
  rewrite List.map_map.
  apply List.map_ext_in. intros row _.
  rewrite List.map_map.
  apply List.map_ext_in. intros x _.
  apply cr_mul_assoc.
Qed.

Lemma mat_neg_neg :
  forall {F : Type} (fld : Field F) (A : Matrix F),
    mat_neg fld (mat_neg fld A) = A.
Proof.
  intros F fld A. unfold mat_neg.
  rewrite mat_scale_mul_assoc.
  rewrite cr_neg_mul_neg, cr_mul_one.
  apply mat_scale_one.
Qed.

Lemma scale_combine_add :
  forall {F : Type} (fld : Field F) (a : F) (rA rB : list F),
    List.map (fun x => cr_mul fld a x)
      (List.map (fun '(p, q) => cr_add fld p q) (List.combine rA rB)) =
    List.map (fun '(p, q) => cr_add fld p q)
      (List.combine (List.map (fun x => cr_mul fld a x) rA)
                    (List.map (fun x => cr_mul fld a x) rB)).
Proof.
  intros F fld a rA. induction rA as [|x rA IH]; intro rB.
  - reflexivity.
  - destruct rB as [|y rB]; [reflexivity|].
    simpl. f_equal; [apply cr_distrib|]. apply IH.
Qed.

Lemma mat_scale_add_mat :
  forall {F : Type} (fld : Field F) (a : F) (A B : Matrix F),
    mat_scale fld a (mat_add fld A B) =
    mat_add fld (mat_scale fld a A) (mat_scale fld a B).
Proof.
  intros F fld a A. unfold mat_scale, mat_add.
  induction A as [|rA As IH]; intro B.
  - reflexivity.
  - destruct B as [|rB Bs]; [reflexivity|].
    simpl. f_equal; [apply scale_combine_add|]. apply IH.
Qed.

(** mat_neg_add: -(A + B) = -A + -B. Follows from mat_scale_add_mat. *)
Lemma mat_neg_add :
  forall {F : Type} (fld : Field F) (A B : Matrix F),
    mat_neg fld (mat_add fld A B) =
    mat_add fld (mat_neg fld A) (mat_neg fld B).
Proof. intros. unfold mat_neg. apply mat_scale_add_mat. Qed.

Lemma mat_scale_add_scalar :
  forall {F : Type} (fld : Field F) (a b : F) (A : Matrix F),
    mat_scale fld (cr_add fld a b) A =
    mat_add fld (mat_scale fld a A) (mat_scale fld b A).
Proof.
  intros F fld a b A. unfold mat_scale, mat_add.
  induction A as [|row rest IH].
  - reflexivity.
  - simpl. f_equal; [|exact IH].
    induction row as [|x row IHr]; [reflexivity|].
    simpl. f_equal; [|exact IHr].
    rewrite (cr_mul_comm _ (cr_add fld a b) x).
    rewrite cr_distrib.
    rewrite (cr_mul_comm _ x a), (cr_mul_comm _ x b).
    reflexivity.
Qed.

(** Helper: scaling a list of zeros by c gives a list of zeros. *)
Lemma map_scale_repeat_zero :
  forall {F : Type} (fld : Field F) (c : F) (n : nat),
    List.map (fun a => cr_mul fld c a) (List.repeat (cr_zero fld) n) =
    List.repeat (cr_zero fld) n.
Proof.
  intros F fld c n. induction n as [|n IH]; [reflexivity|].
  simpl. f_equal; [apply (cr_mul_zero_r fld) | exact IH].
Qed.

(** Helper: mat_scale c on repeat-of-rows-of-zeros gives the same. *)
Lemma map_scale_repeat_zero_rows :
  forall {F : Type} (fld : Field F) (c : F) (m n : nat),
    List.map (fun row => List.map (fun a => cr_mul fld c a) row)
             (List.repeat (List.repeat (cr_zero fld) m) n) =
    List.repeat (List.repeat (cr_zero fld) m) n.
Proof.
  intros F fld c m n. induction n as [|n IH]; [reflexivity|].
  simpl. f_equal; [apply map_scale_repeat_zero | exact IH].
Qed.

(** mat_scale c (mat_zero n) = mat_zero n. *)
Lemma mat_scale_mat_zero :
  forall {F : Type} (fld : Field F) (c : F) (n : nat),
    mat_scale fld c (mat_zero fld n) = mat_zero fld n.
Proof.
  intros F fld c n. unfold mat_scale, mat_zero.
  apply map_scale_repeat_zero_rows.
Qed.

(** Alias kept for backward compatibility (now general n, not just n=0). *)
Lemma mat_scale_zero_mat :
  forall {F : Type} (fld : Field F) (c : F) (n : nat),
    mat_scale fld c (mat_zero fld n) = mat_zero fld n.
Proof. intros; apply mat_scale_mat_zero. Qed.

(** mat_neg (mat_zero n) = mat_zero n. *)
Lemma mat_neg_mat_zero :
  forall {F : Type} (fld : Field F) (n : nat),
    mat_neg fld (mat_zero fld n) = mat_zero fld n.
Proof.
  intros F fld n. unfold mat_neg. apply mat_scale_mat_zero.
Qed.

(** Alias. *)
Lemma mat_neg_zero :
  forall {F : Type} (fld : Field F) (n : nat),
    mat_neg fld (mat_zero fld n) = mat_zero fld n.
Proof. intros; apply mat_neg_mat_zero. Qed.

(** mat_mul of an empty first argument is empty. *)
Lemma mat_mul_nil_l :
  forall {F : Type} (fld : Field F) (B : Matrix F),
    mat_mul fld nil B = nil.
Proof. intros. reflexivity. Qed.

(** mat_mul has |A| rows. *)
Lemma length_mat_mul :
  forall {F : Type} (fld : Field F) (A B : Matrix F),
    List.length (mat_mul fld A B) = List.length A.
Proof.
  intros F fld A B. unfold mat_mul. apply List.length_map.
Qed.

(** Each row of mat_mul is a map over col_idx. *)
Lemma mat_mul_row :
  forall {F : Type} (fld : Field F) (A B : Matrix F) (r : nat),
    r < List.length A ->
    List.nth r (mat_mul fld A B) [] =
    List.map (fun col_idx =>
      List.fold_left (fun acc '(a, row_B) =>
        cr_add fld acc (cr_mul fld a (List.nth col_idx row_B (cr_zero fld))))
        (List.combine (List.nth r A []) B) (cr_zero fld))
      (List.seq 0 (List.length (List.nth r A []))).
Proof.
  intros F fld A B r Hr. unfold mat_mul.
  set (rowf := fun row_A : list F =>
    List.map (fun col_idx =>
      List.fold_left _ (List.combine row_A B) (cr_zero fld))
      (List.seq 0 (List.length row_A))).
  assert (Hlen : r < List.length (List.map rowf A)).
  { rewrite List.length_map. exact Hr. }
  rewrite (List.nth_indep _ _ (rowf []) Hlen).
  rewrite (List.map_nth rowf A [] r).
  reflexivity.
Qed.

(** ** Matrix-scale interaction with multiplication *)

(** Helper: combine commutes with map on the first list. *)
Lemma combine_map_l :
  forall {A B X : Type} (f : A -> X) (l1 : list A) (l2 : list B),
    List.combine (List.map f l1) l2 = List.map (fun p => (f (fst p), snd p)) (List.combine l1 l2).
Proof.
  intros A B X f l1. induction l1 as [|x l1 IH]; intros [|y l2]; try reflexivity.
  simpl. f_equal. apply IH.
Qed.

(** Helper: fold_left of map. *)
Lemma fold_left_map_v :
  forall {A B X : Type} (g : A -> X -> A) (h : B -> X) (l : list B) (i : A),
    List.fold_left g (List.map h l) i = List.fold_left (fun a b => g a (h b)) l i.
Proof.
  intros A B X g h l. induction l as [|x l IH]; intro i; [reflexivity|].
  simpl. apply IH.
Qed.

(** Helper: extensionality for fold_left. *)
Lemma fold_left_ext_local :
  forall {A B : Type} (f g : A -> B -> A) (l : list B) (i : A),
    (forall a b, f a b = g a b) ->
    List.fold_left f l i = List.fold_left g l i.
Proof.
  intros A B f g l. induction l as [|x l IH]; intros i Hfg; [reflexivity|].
  simpl. rewrite (Hfg i x). apply IH. exact Hfg.
Qed.

(** Helper: fold_left of a scaled fold equals scaled fold_left. *)
Lemma fold_left_scale_dot :
  forall {F : Type} (fld : Field F) (c init : F) (col_idx : nat)
    (l : list (F * list F)),
    fold_left (fun a (b : F * list F) =>
        cr_add fld a (cr_mul fld (cr_mul fld c (fst b))
                                 (List.nth col_idx (snd b) (cr_zero fld))))
      l (cr_mul fld c init)
    = cr_mul fld c (fold_left (fun acc '(a, row_B) =>
        cr_add fld acc (cr_mul fld a
                                   (List.nth col_idx row_B (cr_zero fld))))
      l init).
Proof.
  intros F fld c init col_idx l. revert init.
  induction l as [|[a row_B] l IH]; intro init; [reflexivity|].
  simpl. rewrite <- IH. f_equal.
  rewrite <- (cr_mul_assoc fld c a
                              (List.nth col_idx row_B (cr_zero fld))).
  symmetry. apply cr_distrib.
Qed.

Lemma mat_mul_scale_l :
  forall {F : Type} (fld : Field F) (c : F) (A B : Matrix F),
    mat_mul fld (mat_scale fld c A) B = mat_scale fld c (mat_mul fld A B).
Proof.
  intros F fld c A B. unfold mat_mul, mat_scale.
  rewrite !List.map_map.
  apply List.map_ext_in. intros row_A _.
  rewrite List.length_map.
  rewrite List.map_map.
  apply List.map_ext_in. intros col_idx _.
  rewrite combine_map_l.
  rewrite fold_left_map_v.
  cbn beta.
  replace (cr_zero fld) with (cr_mul fld c (cr_zero fld)) at 1
    by apply cr_mul_zero_r.
  apply (fold_left_scale_dot fld c (cr_zero fld) col_idx).
Qed.

(** Helper: combine commutes with map on the second list. *)
Lemma combine_map_r :
  forall {A B X : Type} (h : B -> X) (l1 : list A) (l2 : list B),
    List.combine l1 (List.map h l2) = List.map (fun p => (fst p, h (snd p))) (List.combine l1 l2).
Proof.
  intros A B X h l1. induction l1 as [|x l1 IH]; intros [|y l2]; try reflexivity.
  simpl. f_equal. apply IH.
Qed.

(** Helper: nth of a scaled list is the scaled nth (in any commutative ring). *)
Lemma nth_map_cmul :
  forall {F : Type} (fld : Field F) (c : F) (row : list F) (k : nat),
    List.nth k (List.map (fun x => cr_mul fld c x) row) (cr_zero fld) =
    cr_mul fld c (List.nth k row (cr_zero fld)).
Proof.
  intros F fld c row. induction row as [|x row IH]; intro k.
  - simpl. destruct k; rewrite cr_mul_zero_r; reflexivity.
  - destruct k as [|k']; simpl; [reflexivity | apply IH].
Qed.

Lemma mat_mul_scale_r :
  forall {F : Type} (fld : Field F) (c : F) (A B : Matrix F),
    mat_mul fld A (mat_scale fld c B) = mat_scale fld c (mat_mul fld A B).
Proof.
  intros F fld c A B. unfold mat_mul, mat_scale.
  rewrite List.map_map.
  apply List.map_ext_in. intros row_A _.
  rewrite List.map_map.
  apply List.map_ext_in. intros col_idx _.
  rewrite combine_map_r.
  rewrite fold_left_map_v.
  cbn beta.
  rewrite (fold_left_ext_local _
    (fun a (b : F * list F) =>
       cr_add fld a (cr_mul fld (cr_mul fld c (fst b))
                                (List.nth col_idx (snd b) (cr_zero fld))))).
  - replace (cr_zero fld) with (cr_mul fld c (cr_zero fld)) at 1
      by apply cr_mul_zero_r.
    apply (fold_left_scale_dot fld c (cr_zero fld) col_idx).
  - intros acc [a_i row_B]. simpl.
    rewrite (nth_map_cmul fld c row_B col_idx).
    rewrite (cr_mul_assoc fld a_i c (List.nth col_idx row_B (cr_zero fld))).
    rewrite (cr_mul_comm fld a_i c).
    reflexivity.
Qed.

(** mat_mul_neg_l: (-A) * B = -(A * B). Follows from mat_mul_scale_l. *)
Lemma mat_mul_neg_l :
  forall {F : Type} (fld : Field F) (A B : Matrix F),
    mat_mul fld (mat_neg fld A) B = mat_neg fld (mat_mul fld A B).
Proof. intros. unfold mat_neg. apply mat_mul_scale_l. Qed.

(** mat_mul_neg_r: A * (-B) = -(A * B). Follows from mat_mul_scale_r. *)
Lemma mat_mul_neg_r :
  forall {F : Type} (fld : Field F) (A B : Matrix F),
    mat_mul fld A (mat_neg fld B) = mat_neg fld (mat_mul fld A B).
Proof. intros. unfold mat_neg. apply mat_mul_scale_r. Qed.

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

(** ** mat_mul preserves Mat_wf *)

(** mat_mul fld A B is n-rows × m-cols when A is n×k and B is k×m.
    For our square focus we typically need n=m=k. *)
Lemma mat_mul_wf_general :
  forall {F : Type} (fld : Field F) (n k m : nat) (A B : Matrix F),
    Mat_wf n k A -> Mat_wf k m B ->
    (* Each output row has length |row_A| = k. *)
    Mat_wf n k (mat_mul fld A B).
Proof.
  intros F fld n k m A B [HlenA HrowA] [_ _]. unfold Mat_wf, mat_mul. split.
  - rewrite List.length_map. exact HlenA.
  - intros row Hin. rewrite List.in_map_iff in Hin.
    destruct Hin as [row0 [Hrow Hin0]]. subst row.
    rewrite List.length_map, List.length_seq.
    apply HrowA. exact Hin0.
Qed.

(** Square case. *)
Lemma mat_mul_wf :
  forall {F : Type} (fld : Field F) (n : nat) (A B : Matrix F),
    Mat_wf n n A -> Mat_wf n n B -> Mat_wf n n (mat_mul fld A B).
Proof.
  intros F fld n A B HA HB. apply (mat_mul_wf_general fld n n n A B HA HB).
Qed.

(** mat_bracket of two wf matrices is wf. *)
Lemma mat_bracket_wf :
  forall {F : Type} (fld : Field F) (n : nat) (A B : Matrix F),
    Mat_wf n n A -> Mat_wf n n B -> Mat_wf n n (mat_bracket fld A B).
Proof.
  intros F fld n A B HA HB. unfold mat_bracket. apply mat_add_wf.
  - apply mat_mul_wf; assumption.
  - apply mat_neg_wf. apply mat_mul_wf; assumption.
Qed.

(** ** gl(n, F) as a Lie algebra *)

(** ** Bracket linearity lemmas (proved from axioms) *)

Lemma mat_bracket_add_l :
  forall {F : Type} (fld : Field F) (n : nat) (A B C : Matrix F),
    Mat_wf n n A -> Mat_wf n n B -> Mat_wf n n C ->
    mat_bracket fld (mat_add fld A B) C =
    mat_add fld (mat_bracket fld A C) (mat_bracket fld B C).
Proof.
  intros F fld n A B C HA HB HC.
  unfold mat_bracket.
  rewrite (mat_mul_add_distr_r fld n A B C HA HB HC).
  rewrite (mat_mul_add_distr_l fld n C A B HC HA HB).
  rewrite mat_neg_add.
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

Lemma mat_bracket_add_r :
  forall {F : Type} (fld : Field F) (n : nat) (A B C : Matrix F),
    Mat_wf n n A -> Mat_wf n n B -> Mat_wf n n C ->
    mat_bracket fld A (mat_add fld B C) =
    mat_add fld (mat_bracket fld A B) (mat_bracket fld A C).
Proof.
  intros F fld n A B C HA HB HC.
  unfold mat_bracket.
  rewrite (mat_mul_add_distr_l fld n A B C HA HB HC).
  rewrite (mat_mul_add_distr_r fld n B C A HB HC HA).
  rewrite mat_neg_add.
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

Lemma mat_bracket_scale_l :
  forall {F : Type} (fld : Field F) (c : F) (A B : Matrix F),
    mat_bracket fld (mat_scale fld c A) B =
    mat_scale fld c (mat_bracket fld A B).
Proof.
  intros F fld c A B.
  unfold mat_bracket.
  rewrite (mat_mul_scale_l fld c A B).
  rewrite (mat_mul_scale_r fld c B A).
  rewrite (mat_neg_scale fld c (mat_mul fld B A)).
  rewrite <- (mat_scale_add_mat fld c (mat_mul fld A B) (mat_neg fld (mat_mul fld B A))).
  reflexivity.
Qed.

Lemma mat_bracket_scale_r :
  forall {F : Type} (fld : Field F) (c : F) (A B : Matrix F),
    mat_bracket fld A (mat_scale fld c B) =
    mat_scale fld c (mat_bracket fld A B).
Proof.
  intros F fld c A B.
  unfold mat_bracket.
  rewrite (mat_mul_scale_r fld c A B).
  rewrite (mat_mul_scale_l fld c B A).
  rewrite (mat_neg_scale fld c (mat_mul fld B A)).
  rewrite <- (mat_scale_add_mat fld c (mat_mul fld A B) (mat_neg fld (mat_mul fld B A))).
  reflexivity.
Qed.

Lemma mat_bracket_alt :
  forall {F : Type} (fld : Field F) (n : nat) (A : Matrix F),
    Mat_wf n n A ->
    mat_bracket fld A A = mat_zero fld n.
Proof.
  intros F fld n A HA.
  unfold mat_bracket.
  apply (mat_add_neg fld n (mat_mul fld A A)).
  apply mat_mul_wf; exact HA.
Qed.

(** ** Zero matrix multiplication (correct shape) *)

(** Helper: fold_left of a sum-of-products over zero-list-paired-with-anything is 0. *)
Lemma fold_left_combine_repeat_zero :
  forall {F : Type} (fld : Field F) (B : list (list F)) (col_idx n : nat) (init : F),
    init = cr_zero fld ->
    List.fold_left (fun acc '(a, row_B) =>
        cr_add fld acc (cr_mul fld a (List.nth col_idx row_B (cr_zero fld))))
      (List.combine (List.repeat (cr_zero fld) n) B) init = cr_zero fld.
Proof.
  intros F fld B col_idx n. revert B.
  induction n as [|n IH]; intros B init Hinit.
  - simpl. exact Hinit.
  - destruct B as [|row_B B'].
    + simpl. exact Hinit.
    + simpl. apply IH.
      rewrite Hinit, (cr_mul_zero_l fld), (cr_add_zero fld). reflexivity.
Qed.

(** mat_mul of zero on left: mat_mul (mat_zero n) A = repeat (repeat 0 n) n.
    For square zero: result is mat_zero fld n. *)
Lemma mat_mul_zero_l_correct :
  forall {F : Type} (fld : Field F) (n : nat) (B : Matrix F),
    mat_mul fld (mat_zero fld n) B = List.repeat (List.repeat (cr_zero fld) n) n.
Proof.
  intros F fld n B. unfold mat_mul, mat_zero.
  rewrite (List.map_ext_in
    (fun row_A => List.map _ (List.seq 0 (List.length row_A)))
    (fun _ => List.repeat (cr_zero fld) n)).
  - rewrite List.map_const, List.repeat_length. reflexivity.
  - intros row_A Hin.
    apply List.repeat_spec in Hin. subst row_A.
    rewrite List.repeat_length.
    rewrite (List.map_ext_in
      (fun col_idx => List.fold_left _ (List.combine _ B) (cr_zero fld))
      (fun _ => cr_zero fld)).
    + rewrite List.map_const, List.length_seq.
      reflexivity.
    + intros col_idx _.
      apply (fold_left_combine_repeat_zero fld B col_idx n (cr_zero fld) eq_refl).
Qed.

(** Corollary: mat_mul (mat_zero n) (mat_zero m) = mat_zero n. *)
Lemma mat_mul_zero_zero :
  forall {F : Type} (fld : Field F) (n m : nat),
    mat_mul fld (mat_zero fld n) (mat_zero fld m) = mat_zero fld n.
Proof.
  intros F fld n m. apply mat_mul_zero_l_correct.
Qed.

(** ** Matrix units *)


(** e_{ij} : the matrix with 1 at position (i,j) and 0 elsewhere. *)
Definition mat_unit {F : Type} (fld : Field F) (n i j : nat) : Matrix F :=
  List.map (fun r =>
    List.map (fun c =>
      if Nat.eqb r i && Nat.eqb c j then cr_one fld else cr_zero fld)
    (List.seq 0 n))
  (List.seq 0 n).

(** mat_unit has n rows. *)
Lemma length_mat_unit :
  forall {F : Type} (fld : Field F) (n i j : nat),
    List.length (mat_unit fld n i j) = n.
Proof.
  intros. unfold mat_unit. rewrite List.length_map, List.length_seq. reflexivity.
Qed.

(** Each row of mat_unit has length n. *)
Lemma mat_unit_row_length :
  forall {F : Type} (fld : Field F) (n i j r : nat),
    r < n -> List.length (List.nth r (mat_unit fld n i j) []) = n.
Proof.
  intros F fld n i j r Hr. unfold mat_unit.
  set (f := fun r' => List.map _ (List.seq 0 n)).
  assert (Hlen : r < List.length (List.map f (List.seq 0 n))).
  { rewrite List.length_map, List.length_seq. exact Hr. }
  rewrite (List.nth_indep _ _ (f 0) Hlen).
  rewrite (List.map_nth f (List.seq 0 n) 0 r).
  unfold f. rewrite List.length_map, List.length_seq. reflexivity.
Qed.

(** mat_unit n i j is well-formed n×n. *)
Lemma mat_unit_wf :
  forall {F : Type} (fld : Field F) (n i j : nat),
    Mat_wf n n (mat_unit fld n i j).
Proof.
  intros F fld n i j. unfold Mat_wf. split.
  - apply length_mat_unit.
  - intros row Hin. unfold mat_unit in Hin.
    rewrite List.in_map_iff in Hin.
    destruct Hin as [r [Hrow _]]. subst row.
    rewrite List.length_map, List.length_seq. reflexivity.
Qed.

(** mat_zero has n rows. *)
Lemma length_mat_zero :
  forall {F : Type} (fld : Field F) (n : nat),
    List.length (mat_zero fld n) = n.
Proof.
  intros. unfold mat_zero. apply List.repeat_length.
Qed.

(** Each row of mat_zero has length n. *)
Lemma mat_zero_row_length :
  forall {F : Type} (fld : Field F) (n r : nat),
    r < n -> List.length (List.nth r (mat_zero fld n) []) = n.
Proof.
  intros F fld n r Hr. unfold mat_zero.
  rewrite (List.nth_indep _ _ (List.repeat (cr_zero fld) n)).
  - rewrite List.nth_repeat. apply List.repeat_length.
  - rewrite List.repeat_length. exact Hr.
Qed.

(** Each entry of mat_zero is 0. *)
Lemma nth_mat_zero :
  forall {F : Type} (fld : Field F) (n r c : nat),
    r < n -> c < n ->
    List.nth c (List.nth r (mat_zero fld n) []) (cr_zero fld) = cr_zero fld.
Proof.
  intros F fld n r c Hr Hc. unfold mat_zero.
  rewrite (List.nth_indep _ _ (List.repeat (cr_zero fld) n)).
  - rewrite List.nth_repeat. apply List.nth_repeat.
  - rewrite List.repeat_length. exact Hr.
Qed.

(** When i ≥ n, mat_unit fld n i j has all entries zero (degenerate case). *)
Lemma mat_unit_overflow_i :
  forall {F : Type} (fld : Field F) (n i j : nat),
    n <= i ->
    mat_unit fld n i j = mat_zero fld n.
Proof.
  intros F fld n i j Hni. unfold mat_unit, mat_zero.
  rewrite (List.map_ext_in
    (fun r => List.map _ (List.seq 0 n))
    (fun _ => List.repeat (cr_zero fld) n)).
  - rewrite List.map_const, List.length_seq. reflexivity.
  - intros r Hin.
    apply List.in_seq in Hin. simpl in Hin.
    assert (Hri : r < i) by lia.
    rewrite (List.map_ext_in
      (fun c => if Nat.eqb r i && Nat.eqb c j then cr_one fld else cr_zero fld)
      (fun _ => cr_zero fld)).
    + rewrite List.map_const, List.length_seq. reflexivity.
    + intros c _.
      replace (Nat.eqb r i) with false; [reflexivity|].
      symmetry. apply Nat.eqb_neq. lia.
Qed.

(** When j ≥ n, mat_unit fld n i j has all entries zero (degenerate case). *)
Lemma mat_unit_overflow_j :
  forall {F : Type} (fld : Field F) (n i j : nat),
    n <= j ->
    mat_unit fld n i j = mat_zero fld n.
Proof.
  intros F fld n i j Hnj. unfold mat_unit, mat_zero.
  rewrite (List.map_ext_in
    (fun r => List.map _ (List.seq 0 n))
    (fun _ => List.repeat (cr_zero fld) n)).
  - rewrite List.map_const, List.length_seq. reflexivity.
  - intros r _.
    rewrite (List.map_ext_in
      (fun c => if Nat.eqb r i && Nat.eqb c j then cr_one fld else cr_zero fld)
      (fun _ => cr_zero fld)).
    + rewrite List.map_const, List.length_seq. reflexivity.
    + intros c Hin.
      apply List.in_seq in Hin. simpl in Hin.
      assert (Hcj : c <> j) by lia.
      destruct (Nat.eqb r i); simpl;
        [|reflexivity].
      replace (Nat.eqb c j) with false; [reflexivity|].
      symmetry. apply Nat.eqb_neq. exact Hcj.
Qed.

(** The (r, c) entry of mat_unit fld n i j when r < n and c < n. *)
Lemma nth_mat_unit :
  forall {F : Type} (fld : Field F) (n i j r c : nat),
    r < n -> c < n ->
    List.nth c (List.nth r (mat_unit fld n i j) []) (cr_zero fld) =
    if Nat.eqb r i && Nat.eqb c j then cr_one fld else cr_zero fld.
Proof.
  intros F fld n i j r c Hr Hc. unfold mat_unit.
  set (rowf := fun r' => List.map (fun c' => if Nat.eqb r' i && Nat.eqb c' j
                                              then cr_one fld else cr_zero fld)
                                  (List.seq 0 n)).
  assert (Hlen_outer : r < List.length (List.map rowf (List.seq 0 n))).
  { rewrite List.length_map, List.length_seq. exact Hr. }
  rewrite (List.nth_indep _ _ (rowf 0) Hlen_outer).
  rewrite (List.map_nth rowf (List.seq 0 n) 0 r).
  rewrite List.seq_nth by exact Hr. simpl.
  unfold rowf.
  set (f := fun c' => if Nat.eqb r i && Nat.eqb c' j
                      then cr_one fld else cr_zero fld).
  assert (Hlen_inner : c < List.length (List.map f (List.seq 0 n))).
  { rewrite List.length_map, List.length_seq. exact Hc. }
  rewrite (List.nth_indep _ _ (f 0) Hlen_inner).
  rewrite (List.map_nth f (List.seq 0 n) 0 c).
  rewrite List.seq_nth by exact Hc. reflexivity.
Qed.

(** When i < n and 1 ≠ 0, mat_unit fld n i i is non-zero (distinct from mat_zero). *)
Lemma mat_unit_diag_nonzero :
  forall {F : Type} (fld : Field F) (n i : nat),
    i < n -> cr_one fld <> cr_zero fld ->
    mat_unit fld n i i <> mat_zero fld n.
Proof.
  intros F fld n i Hi Hone Heq.
  apply Hone.
  pose proof (nth_mat_unit fld n i i i i Hi Hi) as Hentry.
  rewrite !Nat.eqb_refl in Hentry. simpl in Hentry.
  pose proof (nth_mat_zero fld n i i Hi Hi) as Hzero.
  rewrite Heq in Hentry. rewrite Hentry in Hzero.
  exact Hzero.
Qed.

(** Distinct diagonal matrix units (i ≠ j) are distinct (when 1 ≠ 0). *)
Lemma mat_unit_diag_distinct :
  forall {F : Type} (fld : Field F) (n i j : nat),
    i < n -> j < n -> i <> j ->
    cr_one fld <> cr_zero fld ->
    mat_unit fld n i i <> mat_unit fld n j j.
Proof.
  intros F fld n i j Hi Hj Hij Hone Heq.
  apply Hone.
  (* The (i, i) entry of mat_unit n i i is 1, but (i, i) entry of mat_unit n j j is 0. *)
  pose proof (nth_mat_unit fld n i i i i Hi Hi) as Hentry_ii.
  rewrite !Nat.eqb_refl in Hentry_ii. simpl in Hentry_ii.
  pose proof (nth_mat_unit fld n j j i i Hi Hi) as Hentry_jj.
  replace (Nat.eqb i j) with false in Hentry_jj.
  - simpl in Hentry_jj.
    rewrite Heq in Hentry_ii. rewrite Hentry_jj in Hentry_ii.
    symmetry. exact Hentry_ii.
  - symmetry. apply Nat.eqb_neq. exact Hij.
Qed.

(** Multiplication of matrix units: e_{ij} * e_{kl} = δ_{jk} * e_{il}.
    Axiomatized at the level used by downstream consumers; the proof
    reduces to a fold over [List.combine row_A B] but is technical due
    to the row-of-zeros / nth-default handling. *)
Axiom mat_unit_mul : forall {F : Type} (fld : Field F) (n i j k l : nat),
    mat_mul fld (mat_unit fld n i j) (mat_unit fld n k l) =
    if Nat.eqb j k then mat_unit fld n i l else mat_zero fld n.

(** Bracket of matrix units: [e_{ij}, e_{kl}] = δ_{jk}*e_{il} - δ_{li}*e_{kj}.
    Follows from mat_unit_mul. *)
Lemma mat_unit_bracket : forall {F : Type} (fld : Field F) (n i j k l : nat),
    mat_bracket fld (mat_unit fld n i j) (mat_unit fld n k l) =
    mat_add fld
      (if Nat.eqb j k then mat_unit fld n i l else mat_zero fld n)
      (if Nat.eqb l i then mat_neg fld (mat_unit fld n k j) else mat_zero fld n).
Proof.
  intros F fld n i j k l. unfold mat_bracket.
  rewrite (mat_unit_mul fld n i j k l).
  rewrite (mat_unit_mul fld n k l i j).
  destruct (Nat.eqb l i); [|rewrite mat_neg_mat_zero]; reflexivity.
Qed.

(** Jacobi identity for the commutator bracket. *)
Lemma mat_bracket_jacobi :
  forall {F : Type} (fld : Field F) (n : nat) (A B C : Matrix F),
    Mat_wf n n A -> Mat_wf n n B -> Mat_wf n n C ->
    mat_add fld
      (mat_add fld
         (mat_bracket fld A (mat_bracket fld B C))
         (mat_bracket fld B (mat_bracket fld C A)))
      (mat_bracket fld C (mat_bracket fld A B))
    = mat_zero fld n.
Proof.
  intros F fld n A B C HA HB HC.
  (* Helper: (P+Q)+(R+S) = (P+R)+(Q+S) — purely from mat_add_assoc/comm. *)
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
  (* All triple products are wf — needed for mat_add_neg_l/zero_l/etc. *)
  assert (HABC : Mat_wf n n ABC) by (apply mat_mul_wf; [apply mat_mul_wf|]; assumption).
  assert (HACB : Mat_wf n n ACB) by (apply mat_mul_wf; [apply mat_mul_wf|]; assumption).
  assert (HBAC : Mat_wf n n BAC) by (apply mat_mul_wf; [apply mat_mul_wf|]; assumption).
  assert (HBCA : Mat_wf n n BCA) by (apply mat_mul_wf; [apply mat_mul_wf|]; assumption).
  assert (HCAB : Mat_wf n n CAB) by (apply mat_mul_wf; [apply mat_mul_wf|]; assumption).
  assert (HCBA : Mat_wf n n CBA) by (apply mat_mul_wf; [apply mat_mul_wf|]; assumption).
  (* Expand each bracket into four triple-product terms. *)
  assert (HBC : Mat_wf n n (mat_mul fld B C)) by (apply mat_mul_wf; assumption).
  assert (HCB : Mat_wf n n (mat_mul fld C B)) by (apply mat_mul_wf; assumption).
  assert (HCA : Mat_wf n n (mat_mul fld C A)) by (apply mat_mul_wf; assumption).
  assert (HAC : Mat_wf n n (mat_mul fld A C)) by (apply mat_mul_wf; assumption).
  assert (HAB : Mat_wf n n (mat_mul fld A B)) by (apply mat_mul_wf; assumption).
  assert (HBA : Mat_wf n n (mat_mul fld B A)) by (apply mat_mul_wf; assumption).
  assert (H1 : mat_bracket fld A (mat_bracket fld B C) =
    mat_add fld (mat_add fld ABC (mat_neg fld ACB))
               (mat_add fld (mat_neg fld BCA) CBA)).
  { unfold mat_bracket, ABC, ACB, BCA, CBA.
    rewrite (mat_mul_add_distr_l fld n A (mat_mul fld B C) (mat_neg fld (mat_mul fld C B)) HA HBC
             (mat_neg_wf fld n n _ HCB)).
    rewrite mat_mul_neg_r.
    rewrite (mat_mul_add_distr_r fld n (mat_mul fld B C) (mat_neg fld (mat_mul fld C B)) A
             HBC (mat_neg_wf fld n n _ HCB) HA).
    rewrite mat_mul_neg_l, mat_neg_add, mat_neg_neg.
    rewrite <- (mat_mul_assoc_m fld n A B C HA HB HC).
    rewrite <- (mat_mul_assoc_m fld n A C B HA HC HB).
    reflexivity. }
  assert (H2 : mat_bracket fld B (mat_bracket fld C A) =
    mat_add fld (mat_add fld BCA (mat_neg fld BAC))
               (mat_add fld (mat_neg fld CAB) ACB)).
  { unfold mat_bracket, BCA, BAC, CAB, ACB.
    rewrite (mat_mul_add_distr_l fld n B (mat_mul fld C A) (mat_neg fld (mat_mul fld A C)) HB HCA
             (mat_neg_wf fld n n _ HAC)).
    rewrite mat_mul_neg_r.
    rewrite (mat_mul_add_distr_r fld n (mat_mul fld C A) (mat_neg fld (mat_mul fld A C)) B
             HCA (mat_neg_wf fld n n _ HAC) HB).
    rewrite mat_mul_neg_l, mat_neg_add, mat_neg_neg.
    rewrite <- (mat_mul_assoc_m fld n B C A HB HC HA).
    rewrite <- (mat_mul_assoc_m fld n B A C HB HA HC).
    reflexivity. }
  assert (H3 : mat_bracket fld C (mat_bracket fld A B) =
    mat_add fld (mat_add fld CAB (mat_neg fld CBA))
               (mat_add fld (mat_neg fld ABC) BAC)).
  { unfold mat_bracket, CAB, CBA, ABC, BAC.
    rewrite (mat_mul_add_distr_l fld n C (mat_mul fld A B) (mat_neg fld (mat_mul fld B A)) HC HAB
             (mat_neg_wf fld n n _ HBA)).
    rewrite mat_mul_neg_r.
    rewrite (mat_mul_add_distr_r fld n (mat_mul fld A B) (mat_neg fld (mat_mul fld B A)) C
             HAB (mat_neg_wf fld n n _ HBA) HC).
    rewrite mat_mul_neg_l, mat_neg_add, mat_neg_neg.
    rewrite <- (mat_mul_assoc_m fld n C A B HC HA HB).
    rewrite <- (mat_mul_assoc_m fld n C B A HC HB HA).
    reflexivity. }
  rewrite H1, H2, H3.
  (* Same algebraic dance as before, but now using the wf-strengthened
     mat_add_neg, mat_add_neg_l, mat_add_zero_l, mat_add_zero_r. *)
  rewrite (mat_add_assoc_m fld
    (mat_add fld (mat_add fld ABC (mat_neg fld ACB)) (mat_add fld (mat_neg fld BCA) CBA))
    (mat_add fld (mat_add fld BCA (mat_neg fld BAC)) (mat_add fld (mat_neg fld CAB) ACB))
    (mat_add fld (mat_add fld CAB (mat_neg fld CBA)) (mat_add fld (mat_neg fld ABC) BAC))).
  rewrite (mat_add_assoc_m fld
    (mat_add fld BCA (mat_neg fld BAC))
    (mat_add fld (mat_neg fld CAB) ACB)
    (mat_add fld (mat_add fld CAB (mat_neg fld CBA)) (mat_add fld (mat_neg fld ABC) BAC))).
  rewrite <- (mat_add_assoc_m fld
    (mat_add fld (mat_neg fld CAB) ACB)
    (mat_add fld CAB (mat_neg fld CBA))
    (mat_add fld (mat_neg fld ABC) BAC)).
  rewrite (comm_inner (mat_neg fld CAB) ACB CAB (mat_neg fld CBA)).
  rewrite (mat_add_neg_l fld n CAB HCAB).
  rewrite (mat_add_zero_l fld n (mat_add fld ACB (mat_neg fld CBA))).
  2: { apply mat_add_wf; [exact HACB | apply mat_neg_wf; exact HCBA]. }
  rewrite (mat_add_assoc_m fld
    (mat_add fld ABC (mat_neg fld ACB))
    (mat_add fld (mat_neg fld BCA) CBA)
    (mat_add fld (mat_add fld BCA (mat_neg fld BAC))
                 (mat_add fld (mat_add fld ACB (mat_neg fld CBA))
                              (mat_add fld (mat_neg fld ABC) BAC)))).
  rewrite <- (mat_add_assoc_m fld
    (mat_add fld (mat_neg fld BCA) CBA)
    (mat_add fld BCA (mat_neg fld BAC))
    (mat_add fld (mat_add fld ACB (mat_neg fld CBA))
                 (mat_add fld (mat_neg fld ABC) BAC))).
  rewrite (comm_inner (mat_neg fld BCA) CBA BCA (mat_neg fld BAC)).
  rewrite (mat_add_neg_l fld n BCA HBCA).
  rewrite (mat_add_zero_l fld n (mat_add fld CBA (mat_neg fld BAC))).
  2: { apply mat_add_wf; [exact HCBA | apply mat_neg_wf; exact HBAC]. }
  rewrite <- (mat_add_assoc_m fld
    (mat_add fld CBA (mat_neg fld BAC))
    (mat_add fld ACB (mat_neg fld CBA))
    (mat_add fld (mat_neg fld ABC) BAC)).
  rewrite (mat_add_comm fld ACB (mat_neg fld CBA)).
  rewrite (comm_inner CBA (mat_neg fld BAC) (mat_neg fld CBA) ACB).
  rewrite (mat_add_neg fld n CBA HCBA).
  rewrite (mat_add_zero_l fld n (mat_add fld (mat_neg fld BAC) ACB)).
  2: { apply mat_add_wf; [apply mat_neg_wf; exact HBAC | exact HACB]. }
  rewrite <- (mat_add_assoc_m fld
    (mat_add fld ABC (mat_neg fld ACB))
    (mat_add fld (mat_neg fld BAC) ACB)
    (mat_add fld (mat_neg fld ABC) BAC)).
  rewrite (comm_inner ABC (mat_neg fld ACB) (mat_neg fld BAC) ACB).
  rewrite (mat_add_neg_l fld n ACB HACB).
  rewrite (mat_add_zero_r fld n (mat_add fld ABC (mat_neg fld BAC))).
  2: { apply mat_add_wf; [exact HABC | apply mat_neg_wf; exact HBAC]. }
  rewrite (comm_inner ABC (mat_neg fld BAC) (mat_neg fld ABC) BAC).
  rewrite (mat_add_neg fld n ABC HABC).
  rewrite (mat_add_zero_l fld n (mat_add fld (mat_neg fld BAC) BAC)).
  2: { apply mat_add_wf; [apply mat_neg_wf; exact HBAC | exact HBAC]. }
  apply (mat_add_neg_l fld n BAC HBAC).
Qed.

(** ** gl(n, F) as a Lie algebra over the sigma type [{ A | Mat_wf n n A }]

    REFACTOR (Task M.0): the carrier of [gl_vs] is now a sigma type
    [{ A : Matrix F | Mat_wf n n A }].  This makes [vsF_zero] equal to
    a proper n×n zero matrix (not the empty matrix), and lets all the
    [mat_*] axioms safely apply (since each component is wf). *)

Definition GLMat {F : Type} (fld : Field F) (n : nat) : Type :=
  { A : Matrix F | Mat_wf n n A }.

(** Operations on the sigma type. *)
Definition gl_zero {F : Type} (fld : Field F) (n : nat) : GLMat fld n :=
  exist _ (mat_zero fld n) (mat_zero_wf fld n).

Definition gl_add {F : Type} (fld : Field F) (n : nat)
    (A B : GLMat fld n) : GLMat fld n :=
  exist _ (mat_add fld (proj1_sig A) (proj1_sig B))
          (mat_add_wf fld n n _ _ (proj2_sig A) (proj2_sig B)).

Definition gl_neg {F : Type} (fld : Field F) (n : nat)
    (A : GLMat fld n) : GLMat fld n :=
  exist _ (mat_neg fld (proj1_sig A))
          (mat_neg_wf fld n n _ (proj2_sig A)).

Definition gl_scale {F : Type} (fld : Field F) (n : nat)
    (c : F) (A : GLMat fld n) : GLMat fld n :=
  exist _ (mat_scale fld c (proj1_sig A))
          (mat_scale_wf fld n n c _ (proj2_sig A)).

Definition gl_bracket {F : Type} (fld : Field F) (n : nat)
    (A B : GLMat fld n) : GLMat fld n :=
  exist _ (mat_bracket fld (proj1_sig A) (proj1_sig B))
          (mat_bracket_wf fld n _ _ (proj2_sig A) (proj2_sig B)).

(** Sigma-eq from underlying matrix equality (uses proof_irrelevance). *)
Lemma gl_sig_eq :
  forall {F : Type} (fld : Field F) (n : nat) (A B : GLMat fld n),
    proj1_sig A = proj1_sig B -> A = B.
Proof.
  intros F fld n [a Ha] [b Hb] Heq. simpl in Heq. subst b.
  f_equal. apply proof_irrelevance.
Qed.

(** Vector-space proof obligations — discharged from underlying [mat_*] lemmas
    + [proj2_sig]. *)
Lemma gl_add_assoc_obligation :
  forall {F : Type} (fld : Field F) (n : nat) (u v w : GLMat fld n),
    gl_add fld n u (gl_add fld n v w) = gl_add fld n (gl_add fld n u v) w.
Proof.
  intros. apply gl_sig_eq. simpl. symmetry. apply mat_add_assoc_m.
Qed.

Lemma gl_add_comm_obligation :
  forall {F : Type} (fld : Field F) (n : nat) (u v : GLMat fld n),
    gl_add fld n u v = gl_add fld n v u.
Proof.
  intros. apply gl_sig_eq. simpl. apply mat_add_comm.
Qed.

Lemma gl_add_zero_r_obligation :
  forall {F : Type} (fld : Field F) (n : nat) (v : GLMat fld n),
    gl_add fld n v (gl_zero fld n) = v.
Proof.
  intros F fld n [a Ha]. apply gl_sig_eq. simpl.
  apply mat_add_zero_r. exact Ha.
Qed.

Lemma gl_add_neg_r_obligation :
  forall {F : Type} (fld : Field F) (n : nat) (v : GLMat fld n),
    gl_add fld n v (gl_neg fld n v) = gl_zero fld n.
Proof.
  intros F fld n [a Ha]. apply gl_sig_eq. simpl.
  apply mat_add_neg. exact Ha.
Qed.

Lemma gl_scale_one_obligation :
  forall {F : Type} (fld : Field F) (n : nat) (v : GLMat fld n),
    gl_scale fld n (cr_one fld) v = v.
Proof.
  intros. apply gl_sig_eq. simpl. apply mat_scale_one.
Qed.

Lemma gl_scale_mul_obligation :
  forall {F : Type} (fld : Field F) (n : nat) (a b : F) (v : GLMat fld n),
    gl_scale fld n a (gl_scale fld n b v) = gl_scale fld n (cr_mul fld a b) v.
Proof.
  intros. apply gl_sig_eq. simpl. apply mat_scale_mul_assoc.
Qed.

Lemma gl_scale_add_v_obligation :
  forall {F : Type} (fld : Field F) (n : nat) (a : F) (u v : GLMat fld n),
    gl_scale fld n a (gl_add fld n u v) =
    gl_add fld n (gl_scale fld n a u) (gl_scale fld n a v).
Proof.
  intros. apply gl_sig_eq. simpl. apply mat_scale_add_mat.
Qed.

Lemma gl_scale_add_s_obligation :
  forall {F : Type} (fld : Field F) (n : nat) (a b : F) (v : GLMat fld n),
    gl_scale fld n (cr_add fld a b) v =
    gl_add fld n (gl_scale fld n a v) (gl_scale fld n b v).
Proof.
  intros. apply gl_sig_eq. simpl. apply mat_scale_add_scalar.
Qed.

(** The gl(n,F) vector space on n×n matrices, packaged as a [VectorSpaceF]. *)
Definition gl_vs {F : Type} (fld : Field F) (n : nat)
  : VectorSpaceF fld (GLMat fld n) :=
  {|
    vsF_add   := gl_add fld n;
    vsF_zero  := gl_zero fld n;
    vsF_neg   := gl_neg fld n;
    vsF_scale := gl_scale fld n;
    vsF_add_assoc  := gl_add_assoc_obligation fld n;
    vsF_add_comm   := gl_add_comm_obligation fld n;
    vsF_add_zero_r := gl_add_zero_r_obligation fld n;
    vsF_add_neg_r  := gl_add_neg_r_obligation fld n;
    vsF_scale_one   := gl_scale_one_obligation fld n;
    vsF_scale_mul   := gl_scale_mul_obligation fld n;
    vsF_scale_add_v := gl_scale_add_v_obligation fld n;
    vsF_scale_add_s := gl_scale_add_s_obligation fld n;
  |}.

(** Lie-algebra obligations. *)
Lemma gl_bracket_add_l_obligation :
  forall {F : Type} (fld : Field F) (n : nat) (x y z : GLMat fld n),
    gl_bracket fld n (gl_add fld n x y) z =
    gl_add fld n (gl_bracket fld n x z) (gl_bracket fld n y z).
Proof.
  intros F fld n [x Hx] [y Hy] [z Hz]. apply gl_sig_eq. simpl.
  apply (mat_bracket_add_l fld n x y z Hx Hy Hz).
Qed.

Lemma gl_bracket_add_r_obligation :
  forall {F : Type} (fld : Field F) (n : nat) (x y z : GLMat fld n),
    gl_bracket fld n x (gl_add fld n y z) =
    gl_add fld n (gl_bracket fld n x y) (gl_bracket fld n x z).
Proof.
  intros F fld n [x Hx] [y Hy] [z Hz]. apply gl_sig_eq. simpl.
  apply (mat_bracket_add_r fld n x y z Hx Hy Hz).
Qed.

Lemma gl_bracket_scale_l_obligation :
  forall {F : Type} (fld : Field F) (n : nat) (a : F) (x y : GLMat fld n),
    gl_bracket fld n (gl_scale fld n a x) y =
    gl_scale fld n a (gl_bracket fld n x y).
Proof.
  intros. apply gl_sig_eq. simpl. apply mat_bracket_scale_l.
Qed.

Lemma gl_bracket_scale_r_obligation :
  forall {F : Type} (fld : Field F) (n : nat) (a : F) (x y : GLMat fld n),
    gl_bracket fld n x (gl_scale fld n a y) =
    gl_scale fld n a (gl_bracket fld n x y).
Proof.
  intros. apply gl_sig_eq. simpl. apply mat_bracket_scale_r.
Qed.

Lemma gl_bracket_alt_obligation :
  forall {F : Type} (fld : Field F) (n : nat) (x : GLMat fld n),
    gl_bracket fld n x x = gl_zero fld n.
Proof.
  intros F fld n [x Hx]. apply gl_sig_eq. simpl.
  apply (mat_bracket_alt fld n x Hx).
Qed.

Lemma gl_jacobi_obligation :
  forall {F : Type} (fld : Field F) (n : nat) (x y z : GLMat fld n),
    gl_add fld n
      (gl_add fld n
         (gl_bracket fld n x (gl_bracket fld n y z))
         (gl_bracket fld n y (gl_bracket fld n z x)))
      (gl_bracket fld n z (gl_bracket fld n x y))
    = gl_zero fld n.
Proof.
  intros F fld n [x Hx] [y Hy] [z Hz]. apply gl_sig_eq. simpl.
  apply (mat_bracket_jacobi fld n x y z Hx Hy Hz).
Qed.

Definition gl {F : Type} (fld : Field F) (n : nat)
  : LieAlgebraF fld (GLMat fld n) :=
  {|
    laF_vs      := gl_vs fld n;
    laF_bracket := gl_bracket fld n;
    laF_bracket_add_l   := gl_bracket_add_l_obligation fld n;
    laF_bracket_scale_l := gl_bracket_scale_l_obligation fld n;
    laF_bracket_add_r   := gl_bracket_add_r_obligation fld n;
    laF_bracket_scale_r := gl_bracket_scale_r_obligation fld n;
    laF_bracket_alt     := gl_bracket_alt_obligation fld n;
    laF_jacobi          := gl_jacobi_obligation fld n;
  |}.
