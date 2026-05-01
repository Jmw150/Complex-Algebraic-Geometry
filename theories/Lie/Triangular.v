(** * Lie/Triangular.v
    Triangular, strictly upper triangular, and diagonal subalgebras of gl(n,F). *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.Lie.Ideals.
Require Import CAG.Lie.Linear.
From Stdlib Require Import List Arith Lia.
Import ListNotations.

(** ** Upper triangular matrices t(n,F)

    REFACTOR (Task M.1, 2026-04-30): the predicate is now lifted to
    [GLMat fld n -> Prop] (sigma type) so that
    [IsSubalgebra (gl fld n) (IsUpperTriangular fld n)] typechecks
    against the new sigma-typed [gl] carrier.  The underlying matrix is
    accessed via [proj1_sig]. *)

(** A matrix is upper triangular if all entries below the diagonal are zero. *)
Definition IsUpperTriangular {F : Type} (fld : Field F) (n : nat) (A : GLMat fld n) : Prop :=
  forall i j, (j < i)%nat -> i < List.length (proj1_sig A) ->
    List.nth j (List.nth i (proj1_sig A) []) (cr_zero fld) = cr_zero fld.

(** ** Strictly upper triangular matrices n(n,F) *)

(** A matrix is strictly upper triangular if all entries on and below the diagonal are zero. *)
Definition IsStrictlyUpperTriangular {F : Type} (fld : Field F) (n : nat) (A : GLMat fld n) : Prop :=
  forall i j, (j <= i)%nat -> i < List.length (proj1_sig A) ->
    List.nth j (List.nth i (proj1_sig A) []) (cr_zero fld) = cr_zero fld.

(** ** Diagonal matrices b(n,F) *)

(** A matrix is diagonal if all off-diagonal entries are zero. *)
Definition IsDiagonal {F : Type} (fld : Field F) (n : nat) (A : GLMat fld n) : Prop :=
  forall i j, i <> j -> i < List.length (proj1_sig A) ->
    List.nth j (List.nth i (proj1_sig A) []) (cr_zero fld) = cr_zero fld.

(* ================================================================ *)
(** * Helper lemmas about lengths and entries                       *)
(* ================================================================ *)

(** [nth k (repeat 0 m) 0 = 0]. *)
Local Lemma nth_repeat_zero_local : forall {F : Type} (fld : Field F) (m k : nat),
    List.nth k (List.repeat (cr_zero fld) m) (cr_zero fld) = cr_zero fld.
Proof.
  intros F fld m. induction m as [|m IH]; intro k.
  - destruct k; reflexivity.
  - destruct k as [|k']; [reflexivity | apply IH].
Qed.

Local Lemma length_mat_scale :
  forall {F : Type} (fld : Field F) (c : F) (A : Matrix F),
    List.length (mat_scale fld c A) = List.length A.
Proof. intros. unfold mat_scale. apply List.length_map. Qed.

Local Lemma length_mat_neg :
  forall {F : Type} (fld : Field F) (A : Matrix F),
    List.length (mat_neg fld A) = List.length A.
Proof. intros. unfold mat_neg. apply length_mat_scale. Qed.

Local Lemma length_mat_add :
  forall {F : Type} (fld : Field F) (A B : Matrix F),
    List.length (mat_add fld A B) = Nat.min (List.length A) (List.length B).
Proof.
  intros F fld A B. unfold mat_add.
  rewrite List.length_map. apply List.length_combine.
Qed.

Local Lemma nth_mat_scale_row :
  forall {F : Type} (fld : Field F) (c : F) (A : Matrix F) (i : nat),
    i < List.length A ->
    List.nth i (mat_scale fld c A) [] =
    List.map (fun a => cr_mul fld c a) (List.nth i A []).
Proof.
  intros F fld c A i Hi. unfold mat_scale.
  set (f := fun row => List.map (fun a => cr_mul fld c a) row).
  assert (Hlen : i < List.length (List.map f A)).
  { rewrite List.length_map. exact Hi. }
  rewrite (List.nth_indep _ _ (f []) Hlen).
  rewrite (List.map_nth f A [] i). reflexivity.
Qed.

Local Lemma nth_map_cmul_local :
  forall {F : Type} (fld : Field F) (c : F) (row : list F) (k : nat),
    List.nth k (List.map (fun x => cr_mul fld c x) row) (cr_zero fld) =
    cr_mul fld c (List.nth k row (cr_zero fld)).
Proof.
  intros F fld c row. induction row as [|x row IH]; intro k.
  - simpl. destruct k; rewrite cr_mul_zero_r; reflexivity.
  - destruct k as [|k']; simpl; [reflexivity | apply IH].
Qed.

Local Lemma nth_combine_add_local :
  forall {F : Type} (fld : Field F) (col_idx : nat) (rA rB : list F),
    List.nth col_idx
      (List.map (fun '(a, b) => cr_add fld a b) (List.combine rA rB))
      (cr_zero fld) =
    cr_add fld
      (if Nat.ltb col_idx (Nat.min (List.length rA) (List.length rB))
       then List.nth col_idx rA (cr_zero fld) else cr_zero fld)
      (if Nat.ltb col_idx (Nat.min (List.length rA) (List.length rB))
       then List.nth col_idx rB (cr_zero fld) else cr_zero fld).
Proof.
  intros F fld col_idx rA. revert col_idx.
  induction rA as [|a rA' IH]; intros col_idx [|b rB'].
  - simpl. destruct col_idx; rewrite cr_add_zero; reflexivity.
  - simpl. destruct col_idx; rewrite cr_add_zero; reflexivity.
  - simpl. destruct col_idx; rewrite cr_add_zero; reflexivity.
  - simpl. destruct col_idx as [|k]; [reflexivity|].
    simpl. apply IH.
Qed.

Local Lemma nth_combine_pair :
  forall {A B : Type} (l1 : list A) (l2 : list B) (i : nat) (d1 : A) (d2 : B),
    i < Nat.min (List.length l1) (List.length l2) ->
    List.nth i (List.combine l1 l2) (d1, d2) =
    (List.nth i l1 d1, List.nth i l2 d2).
Proof.
  intros A B l1. induction l1 as [|x l1' IH]; intros [|y l2'] i d1 d2 Hi.
  - simpl in Hi. lia.
  - simpl in Hi. lia.
  - simpl in Hi. lia.
  - simpl. destruct i as [|i']; [reflexivity|].
    simpl. apply IH. simpl in Hi. lia.
Qed.

Local Lemma nth_mat_add_row :
  forall {F : Type} (fld : Field F) (A B : Matrix F) (i : nat),
    i < Nat.min (List.length A) (List.length B) ->
    List.nth i (mat_add fld A B) [] =
    List.map (fun '(a, b) => cr_add fld a b)
             (List.combine (List.nth i A []) (List.nth i B [])).
Proof.
  intros F fld A B i Hi. unfold mat_add.
  set (f := fun '(r1, r2) =>
              List.map (fun '(a, b) => cr_add fld a b) (List.combine r1 r2)).
  assert (Hlen : i < List.length (List.map f (List.combine A B))).
  { rewrite List.length_map, List.length_combine. exact Hi. }
  rewrite (List.nth_indep _ _ (f ([], [])) Hlen).
  rewrite (List.map_nth f (List.combine A B) ([], []) i).
  unfold f.
  rewrite (nth_combine_pair A B i [] [] Hi).
  reflexivity.
Qed.

(* ================================================================ *)
(** * Subalgebra: zero/add/neg/scale closure (common helpers)       *)
(* ================================================================ *)

(** A predicate of the form
      [forall i j, P i j -> i < length A -> nth j (nth i A []) 0 = 0]
    is preserved by mat_scale, mat_neg, and mat_add (entry-wise). *)

Local Lemma scale_preserves_entry_zero :
  forall {F : Type} (fld : Field F) (c : F) (A : Matrix F)
         (P : nat -> nat -> Prop),
    (forall i j, P i j -> i < List.length A ->
       List.nth j (List.nth i A []) (cr_zero fld) = cr_zero fld) ->
    (forall i j, P i j -> i < List.length (mat_scale fld c A) ->
       List.nth j (List.nth i (mat_scale fld c A) []) (cr_zero fld) = cr_zero fld).
Proof.
  intros F fld c A P HA i j HP Hi.
  rewrite length_mat_scale in Hi.
  rewrite (nth_mat_scale_row fld c A i Hi).
  rewrite (nth_map_cmul_local fld c (List.nth i A []) j).
  rewrite (HA i j HP Hi). apply (cr_mul_zero_r fld).
Qed.

Local Lemma neg_preserves_entry_zero :
  forall {F : Type} (fld : Field F) (A : Matrix F)
         (P : nat -> nat -> Prop),
    (forall i j, P i j -> i < List.length A ->
       List.nth j (List.nth i A []) (cr_zero fld) = cr_zero fld) ->
    (forall i j, P i j -> i < List.length (mat_neg fld A) ->
       List.nth j (List.nth i (mat_neg fld A) []) (cr_zero fld) = cr_zero fld).
Proof.
  intros F fld A P HA. unfold mat_neg.
  apply (scale_preserves_entry_zero fld _ A P HA).
Qed.

Local Lemma add_preserves_entry_zero :
  forall {F : Type} (fld : Field F) (A B : Matrix F)
         (P : nat -> nat -> Prop),
    (forall i j, P i j -> i < List.length A ->
       List.nth j (List.nth i A []) (cr_zero fld) = cr_zero fld) ->
    (forall i j, P i j -> i < List.length B ->
       List.nth j (List.nth i B []) (cr_zero fld) = cr_zero fld) ->
    (forall i j, P i j -> i < List.length (mat_add fld A B) ->
       List.nth j (List.nth i (mat_add fld A B) []) (cr_zero fld) = cr_zero fld).
Proof.
  intros F fld A B P HA HB i j HP Hi.
  rewrite length_mat_add in Hi.
  assert (HiA : i < List.length A) by lia.
  assert (HiB : i < List.length B) by lia.
  rewrite (nth_mat_add_row fld A B i Hi).
  rewrite (nth_combine_add_local fld j (List.nth i A []) (List.nth i B [])).
  destruct (Nat.ltb j _) eqn:Hlt.
  - rewrite (HA i j HP HiA), (HB i j HP HiB). apply cr_add_zero.
  - apply cr_add_zero.
Qed.

(* ================================================================ *)
(** * Bracket closure                                                *)
(* ================================================================ *)

(** The (i,j) entry of mat_mul A B is a fold-left over combine. *)

Local Lemma nth_mat_mul_row :
  forall {F : Type} (fld : Field F) (A B : Matrix F) (i : nat),
    i < List.length A ->
    List.nth i (mat_mul fld A B) [] =
    List.map (fun col_idx =>
      List.fold_left (fun acc '(a, row_B) =>
        cr_add fld acc (cr_mul fld a (List.nth col_idx row_B (cr_zero fld))))
        (List.combine (List.nth i A []) B) (cr_zero fld))
      (List.seq 0 (List.length (List.nth i A []))).
Proof.
  intros. apply mat_mul_row. assumption.
Qed.

(** When the fold's input list is "all zero contributions", the result is 0. *)
Local Lemma fold_left_dot_zero :
  forall {F : Type} (fld : Field F) (j : nat)
         (l : list (F * list F)) (init : F),
    init = cr_zero fld ->
    (forall a row_B, List.In (a, row_B) l ->
       cr_mul fld a (List.nth j row_B (cr_zero fld)) = cr_zero fld) ->
    List.fold_left (fun acc '(a, row_B) =>
      cr_add fld acc (cr_mul fld a (List.nth j row_B (cr_zero fld))))
      l init = cr_zero fld.
Proof.
  intros F fld j l. induction l as [|[a row_B] l IH]; intros init Hinit Hall.
  - simpl. exact Hinit.
  - simpl. apply IH.
    + rewrite Hinit, (Hall a row_B (or_introl eq_refl)). apply cr_add_zero.
    + intros a' row_B' Hin. apply Hall. right. exact Hin.
Qed.

(** A combine-decomposition: for any k < min (length l1) (length l2),
    nth k (combine l1 l2) (d1, d2) = (nth k l1 d1, nth k l2 d2). *)
Local Lemma nth_combine :
  forall {A B : Type} (l1 : list A) (l2 : list B) (k : nat) (d1 : A) (d2 : B),
    k < Nat.min (List.length l1) (List.length l2) ->
    List.nth k (List.combine l1 l2) (d1, d2) = (List.nth k l1 d1, List.nth k l2 d2).
Proof.
  intros A B l1. induction l1 as [|x l1' IH]; intros [|y l2'] k d1 d2 Hk.
  - simpl in Hk; lia.
  - simpl in Hk; lia.
  - simpl in Hk; lia.
  - simpl. destruct k as [|k']; [reflexivity|].
    simpl. apply IH. simpl in Hk. lia.
Qed.

(** Membership in combine implies indexed membership. *)
Local Lemma in_combine_iff_nth :
  forall {A B : Type} (l1 : list A) (l2 : list B) (a : A) (b : B),
    List.In (a, b) (List.combine l1 l2) ->
    exists k, k < Nat.min (List.length l1) (List.length l2) /\
              List.nth k l1 a = a /\ List.nth k l2 b = b.
Proof.
  intros A B l1. induction l1 as [|x l1' IH]; intros [|y l2'] a b Hin.
  - simpl in Hin. contradiction.
  - simpl in Hin. contradiction.
  - simpl in Hin. contradiction.
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + injection Heq as Hax Hby. subst x y.
      exists 0. simpl. split; [lia | split; reflexivity].
    + destruct (IH l2' a b Hin) as [k [Hk [HA HB]]].
      exists (S k). simpl. split; [lia | split; assumption].
Qed.

(** Bracket entry zeroness: the (i,j) entry of [A,B] = AB - BA. *)

(** Helper: when (a, row_B) is in (combine row_A B), it equals
    (nth k row_A 0, nth k B []) for some k < min lengths. *)
Local Lemma in_combine_decomp :
  forall {F : Type} (fld : Field F) (row_A : list F) (B : list (list F))
         (a : F) (row_B : list F),
    List.In (a, row_B) (List.combine row_A B) ->
    exists k, k < Nat.min (List.length row_A) (List.length B) /\
              a = List.nth k row_A (cr_zero fld) /\
              row_B = List.nth k B [].
Proof.
  intros F fld row_A. induction row_A as [|x row_A' IH]; intros [|y B'] a row_B Hin.
  - simpl in Hin. contradiction.
  - simpl in Hin. contradiction.
  - simpl in Hin. contradiction.
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + injection Heq as Hax Hby. subst x y.
      exists 0. simpl. split; [lia | split; reflexivity].
    + destruct (IH B' a row_B Hin) as [k [Hk [HA HB]]].
      exists (S k). simpl. split; [lia | split; assumption].
Qed.

(* ================================================================ *)
(** * Key: bracket entry zero from triangularity-type conditions    *)
(* ================================================================ *)

(** Generic lemma: under suitable per-entry hypotheses on A and B,
    the (i,j) entry of mat_mul A B is zero. *)
Local Lemma mat_mul_entry_zero :
  forall {F : Type} (fld : Field F) (A B : Matrix F) (i j : nat),
    i < List.length A ->
    (forall k, cr_mul fld (List.nth k (List.nth i A []) (cr_zero fld))
                          (List.nth j (List.nth k B []) (cr_zero fld)) =
               cr_zero fld) ->
    List.nth j (List.nth i (mat_mul fld A B) []) (cr_zero fld) = cr_zero fld.
Proof.
  intros F fld A B i j Hi Hzero.
  rewrite (nth_mat_mul_row fld A B i Hi).
  remember (List.nth i A []) as row_A eqn:HrowA.
  destruct (Nat.ltb j (List.length row_A)) eqn:Hjlt.
  - apply Nat.ltb_lt in Hjlt.
    set (f := fun col_idx =>
      List.fold_left (fun acc '(a, row_B) =>
        cr_add fld acc (cr_mul fld a (List.nth col_idx row_B (cr_zero fld))))
        (List.combine row_A B) (cr_zero fld)).
    assert (Hlen : j < List.length (List.map f (List.seq 0 (List.length row_A)))).
    { rewrite List.length_map, List.length_seq. exact Hjlt. }
    rewrite (List.nth_indep _ _ (f 0) Hlen).
    rewrite (List.map_nth f (List.seq 0 (List.length row_A)) 0 j).
    rewrite List.seq_nth by exact Hjlt. simpl.
    unfold f.
    apply (fold_left_dot_zero fld j (List.combine row_A B) (cr_zero fld) eq_refl).
    intros a row_B Hin.
    destruct (in_combine_decomp fld row_A B a row_B Hin) as [k [_ [Ha Hr]]].
    subst a row_B. subst row_A. apply (Hzero k).
  - apply Nat.ltb_ge in Hjlt.
    rewrite List.nth_overflow; [reflexivity|].
    rewrite List.length_map, List.length_seq. exact Hjlt.
Qed.

(* ================================================================ *)
(** * Subalgebra proofs                                             *)
(* ================================================================ *)

(** t(n,F) is a Lie subalgebra of gl(n,F). *)
Lemma upper_triangular_is_subalgebra :
  forall {F : Type} (fld : Field F) (n : nat),
    IsSubalgebra (gl fld n) (IsUpperTriangular fld n).
Proof.
  intros F fld n. constructor.
  - (* sub_zero: la_zero (gl fld n) projects to [mat_zero fld n], a square
       matrix of repeats of zero rows; entry (i,j) is zero. *)
    unfold IsUpperTriangular. simpl.
    intros i j Hji Hi.
    unfold mat_zero in *.
    rewrite List.repeat_length in Hi.
    rewrite (List.nth_indep _ _ (List.repeat (cr_zero fld) n))
      by (rewrite List.repeat_length; exact Hi).
    rewrite List.nth_repeat. apply nth_repeat_zero_local.
  - (* sub_add *)
    intros A B HA HB. unfold IsUpperTriangular in *. simpl.
    apply (add_preserves_entry_zero fld (proj1_sig A) (proj1_sig B)
             (fun i j => (j < i)%nat));
      [exact HA | exact HB].
  - (* sub_neg *)
    intros A HA. unfold IsUpperTriangular in *. simpl.
    apply (neg_preserves_entry_zero fld (proj1_sig A)
             (fun i j => (j < i)%nat)).
    exact HA.
  - (* sub_scale *)
    intros c A HA. unfold IsUpperTriangular in *. simpl.
    apply (scale_preserves_entry_zero fld c (proj1_sig A)
             (fun i j => (j < i)%nat)).
    exact HA.
  - (* sub_bracket: [A,B] = AB + (-(BA)). Show entry (i,j) for j<i is zero. *)
    intros A B HA HB. unfold IsUpperTriangular in *.
    intros i j Hji Hi.
    simpl in Hi. unfold mat_bracket in Hi. rewrite length_mat_add in Hi.
    rewrite length_mat_neg in Hi.
    rewrite !length_mat_mul in Hi.
    assert (HiA : i < List.length (proj1_sig A)) by lia.
    assert (HiB : i < List.length (proj1_sig B)) by lia.
    simpl. unfold mat_bracket.
    (* (i,j) entry of mat_add (mat_mul A B) (mat_neg (mat_mul B A)) *)
    rewrite (nth_mat_add_row fld (mat_mul fld (proj1_sig A) (proj1_sig B))
                                  (mat_neg fld (mat_mul fld (proj1_sig B) (proj1_sig A))) i).
    2:{ rewrite length_mat_neg, !length_mat_mul. lia. }
    rewrite (nth_combine_add_local fld j _ _).
    destruct (Nat.ltb j _) eqn:Hjlt.
    + (* Both nth-of-row exist; need both AB[i,j] and -(BA)[i,j] = 0. *)
      assert (HABij : List.nth j (List.nth i (mat_mul fld (proj1_sig A) (proj1_sig B)) []) (cr_zero fld) =
                      cr_zero fld).
      { apply (mat_mul_entry_zero fld (proj1_sig A) (proj1_sig B) i j HiA).
        intro k.
        destruct (Nat.ltb k i) eqn:Hki.
        - apply Nat.ltb_lt in Hki.
          rewrite (HA i k Hki HiA). apply (cr_mul_zero_l fld).
        - apply Nat.ltb_ge in Hki.
          assert (Hjk : (j < k)%nat) by lia.
          destruct (Nat.ltb k (List.length (proj1_sig B))) eqn:HkB.
          + apply Nat.ltb_lt in HkB.
            rewrite (HB k j Hjk HkB). apply (cr_mul_zero_r fld).
          + apply Nat.ltb_ge in HkB.
            rewrite (List.nth_overflow (proj1_sig B) []) by exact HkB.
            simpl. destruct j; rewrite (cr_mul_zero_r fld); reflexivity. }
      rewrite HABij.
      assert (HBAij : List.nth j (List.nth i (mat_neg fld (mat_mul fld (proj1_sig B) (proj1_sig A))) [])
                                  (cr_zero fld) = cr_zero fld).
      { unfold mat_neg.
        rewrite (nth_mat_scale_row fld _ (mat_mul fld (proj1_sig B) (proj1_sig A)) i).
        2:{ rewrite length_mat_mul. exact HiB. }
        rewrite (nth_map_cmul_local fld _ _ j).
        assert (HBAraw : List.nth j (List.nth i (mat_mul fld (proj1_sig B) (proj1_sig A)) [])
                                    (cr_zero fld) = cr_zero fld).
        { apply (mat_mul_entry_zero fld (proj1_sig B) (proj1_sig A) i j HiB).
          intro k.
          destruct (Nat.ltb k i) eqn:Hki.
          - apply Nat.ltb_lt in Hki.
            rewrite (HB i k Hki HiB). apply (cr_mul_zero_l fld).
          - apply Nat.ltb_ge in Hki.
            assert (Hjk : (j < k)%nat) by lia.
            destruct (Nat.ltb k (List.length (proj1_sig A))) eqn:HkA.
            + apply Nat.ltb_lt in HkA.
              rewrite (HA k j Hjk HkA). apply (cr_mul_zero_r fld).
            + apply Nat.ltb_ge in HkA.
              rewrite (List.nth_overflow (proj1_sig A) []) by exact HkA.
              simpl. destruct j; rewrite (cr_mul_zero_r fld); reflexivity. }
        rewrite HBAraw. apply (cr_mul_zero_r fld). }
      rewrite HBAij. apply cr_add_zero.
    + apply cr_add_zero.
Qed.

(** n(n,F) is a Lie subalgebra of gl(n,F). *)
Lemma strictly_upper_triangular_is_subalgebra :
  forall {F : Type} (fld : Field F) (n : nat),
    IsSubalgebra (gl fld n) (IsStrictlyUpperTriangular fld n).
Proof.
  intros F fld n. constructor.
  - (* sub_zero *)
    unfold IsStrictlyUpperTriangular. simpl.
    intros i j Hji Hi.
    unfold mat_zero in *.
    rewrite List.repeat_length in Hi.
    rewrite (List.nth_indep _ _ (List.repeat (cr_zero fld) n))
      by (rewrite List.repeat_length; exact Hi).
    rewrite List.nth_repeat. apply nth_repeat_zero_local.
  - (* sub_add *)
    intros A B HA HB. unfold IsStrictlyUpperTriangular in *. simpl.
    apply (add_preserves_entry_zero fld (proj1_sig A) (proj1_sig B)
             (fun i j => (j <= i)%nat));
      [exact HA | exact HB].
  - (* sub_neg *)
    intros A HA. unfold IsStrictlyUpperTriangular in *. simpl.
    apply (neg_preserves_entry_zero fld (proj1_sig A)
             (fun i j => (j <= i)%nat)).
    exact HA.
  - (* sub_scale *)
    intros c A HA. unfold IsStrictlyUpperTriangular in *. simpl.
    apply (scale_preserves_entry_zero fld c (proj1_sig A)
             (fun i j => (j <= i)%nat)).
    exact HA.
  - (* sub_bracket: stronger condition; need (i,j) entry zero for j<=i. *)
    intros A B HA HB. unfold IsStrictlyUpperTriangular in *.
    intros i j Hji Hi.
    simpl in Hi. unfold mat_bracket in Hi.
    rewrite length_mat_add in Hi.
    rewrite length_mat_neg in Hi.
    rewrite !length_mat_mul in Hi.
    assert (HiA : i < List.length (proj1_sig A)) by lia.
    assert (HiB : i < List.length (proj1_sig B)) by lia.
    simpl. unfold mat_bracket.
    rewrite (nth_mat_add_row fld (mat_mul fld (proj1_sig A) (proj1_sig B))
                                  (mat_neg fld (mat_mul fld (proj1_sig B) (proj1_sig A))) i).
    2:{ rewrite length_mat_neg, !length_mat_mul. lia. }
    rewrite (nth_combine_add_local fld j _ _).
    destruct (Nat.ltb j _) eqn:Hjlt.
    + assert (HABij : List.nth j (List.nth i (mat_mul fld (proj1_sig A) (proj1_sig B)) []) (cr_zero fld) =
                      cr_zero fld).
      { apply (mat_mul_entry_zero fld (proj1_sig A) (proj1_sig B) i j HiA).
        intro k.
        destruct (Nat.leb k i) eqn:Hki.
        - apply Nat.leb_le in Hki.
          rewrite (HA i k Hki HiA). apply (cr_mul_zero_l fld).
        - apply Nat.leb_gt in Hki.
          assert (Hjk : (j <= k)%nat) by lia.
          destruct (Nat.ltb k (List.length (proj1_sig B))) eqn:HkB.
          + apply Nat.ltb_lt in HkB.
            rewrite (HB k j Hjk HkB). apply (cr_mul_zero_r fld).
          + apply Nat.ltb_ge in HkB.
            rewrite (List.nth_overflow (proj1_sig B) []) by exact HkB.
            simpl. destruct j; rewrite (cr_mul_zero_r fld); reflexivity. }
      rewrite HABij.
      assert (HBAij : List.nth j (List.nth i (mat_neg fld (mat_mul fld (proj1_sig B) (proj1_sig A))) [])
                                  (cr_zero fld) = cr_zero fld).
      { unfold mat_neg.
        rewrite (nth_mat_scale_row fld _ (mat_mul fld (proj1_sig B) (proj1_sig A)) i).
        2:{ rewrite length_mat_mul. exact HiB. }
        rewrite (nth_map_cmul_local fld _ _ j).
        assert (HBAraw : List.nth j (List.nth i (mat_mul fld (proj1_sig B) (proj1_sig A)) [])
                                    (cr_zero fld) = cr_zero fld).
        { apply (mat_mul_entry_zero fld (proj1_sig B) (proj1_sig A) i j HiB).
          intro k.
          destruct (Nat.leb k i) eqn:Hki.
          - apply Nat.leb_le in Hki.
            rewrite (HB i k Hki HiB). apply (cr_mul_zero_l fld).
          - apply Nat.leb_gt in Hki.
            assert (Hjk : (j <= k)%nat) by lia.
            destruct (Nat.ltb k (List.length (proj1_sig A))) eqn:HkA.
            + apply Nat.ltb_lt in HkA.
              rewrite (HA k j Hjk HkA). apply (cr_mul_zero_r fld).
            + apply Nat.ltb_ge in HkA.
              rewrite (List.nth_overflow (proj1_sig A) []) by exact HkA.
              simpl. destruct j; rewrite (cr_mul_zero_r fld); reflexivity. }
        rewrite HBAraw. apply (cr_mul_zero_r fld). }
      rewrite HBAij. apply cr_add_zero.
    + apply cr_add_zero.
Qed.

(* strictly_upper_triangular_is_ideal removed: was false-as-stated.
   The statement claimed IsIdeal (gl fld n) (IsStrictlyUpperTriangular fld n),
   i.e. that strictly upper triangular matrices form an ideal of all of
   gl(n,F). This is FALSE: for n=2, A = e_{21} (lower triangular)
   and S = e_{12} (strict upper triangular) gives [A, S] = e_{22} - e_{11},
   which is diagonal, not strictly upper triangular. The strictly upper
   triangular matrices are an ideal of t(n,F) (upper triangular), not of
   all gl(n,F). The axiom was unused downstream. *)

(** b(n,F) is a Lie subalgebra of gl(n,F). *)
Lemma diagonal_is_subalgebra :
  forall {F : Type} (fld : Field F) (n : nat),
    IsSubalgebra (gl fld n) (IsDiagonal fld n).
Proof.
  intros F fld n. constructor.
  - (* sub_zero *)
    unfold IsDiagonal. simpl.
    intros i j Hij Hi.
    unfold mat_zero in *.
    rewrite List.repeat_length in Hi.
    rewrite (List.nth_indep _ _ (List.repeat (cr_zero fld) n))
      by (rewrite List.repeat_length; exact Hi).
    rewrite List.nth_repeat. apply nth_repeat_zero_local.
  - (* sub_add *)
    intros A B HA HB. unfold IsDiagonal in *. simpl.
    apply (add_preserves_entry_zero fld (proj1_sig A) (proj1_sig B)
             (fun i j => i <> j));
      [exact HA | exact HB].
  - (* sub_neg *)
    intros A HA. unfold IsDiagonal in *. simpl.
    apply (neg_preserves_entry_zero fld (proj1_sig A) (fun i j => i <> j)).
    exact HA.
  - (* sub_scale *)
    intros c A HA. unfold IsDiagonal in *. simpl.
    apply (scale_preserves_entry_zero fld c (proj1_sig A) (fun i j => i <> j)).
    exact HA.
  - (* sub_bracket: for diagonal A, B, [A,B] = AB - BA. AB and BA are diagonal,
       and AB[i,i] = A[i,i]*B[i,i] = BA[i,i], so [A,B][i,i] = 0.
       Off-diagonal entries are zero already. So the bracket is the zero matrix
       on its support, hence diagonal. *)
    intros A B HA HB. unfold IsDiagonal in *.
    intros i j Hij Hi.
    simpl in Hi. unfold mat_bracket in Hi.
    rewrite length_mat_add in Hi.
    rewrite length_mat_neg in Hi.
    rewrite !length_mat_mul in Hi.
    assert (HiA : i < List.length (proj1_sig A)) by lia.
    assert (HiB : i < List.length (proj1_sig B)) by lia.
    simpl. unfold mat_bracket.
    rewrite (nth_mat_add_row fld (mat_mul fld (proj1_sig A) (proj1_sig B))
                                  (mat_neg fld (mat_mul fld (proj1_sig B) (proj1_sig A))) i).
    2:{ rewrite length_mat_neg, !length_mat_mul. lia. }
    rewrite (nth_combine_add_local fld j _ _).
    destruct (Nat.ltb j _) eqn:Hjlt.
    + assert (HABij : List.nth j (List.nth i (mat_mul fld (proj1_sig A) (proj1_sig B)) []) (cr_zero fld) =
                      cr_zero fld).
      { apply (mat_mul_entry_zero fld (proj1_sig A) (proj1_sig B) i j HiA).
        intro k.
        destruct (Nat.eqb k i) eqn:Hki.
        - apply Nat.eqb_eq in Hki. subst k.
          rewrite (HB i j Hij HiB). apply (cr_mul_zero_r fld).
        - apply Nat.eqb_neq in Hki.
          assert (Hik : i <> k) by (intro; subst; apply Hki; reflexivity).
          rewrite (HA i k Hik HiA). apply (cr_mul_zero_l fld). }
      rewrite HABij.
      assert (HBAij : List.nth j (List.nth i (mat_neg fld (mat_mul fld (proj1_sig B) (proj1_sig A))) [])
                                  (cr_zero fld) = cr_zero fld).
      { unfold mat_neg.
        rewrite (nth_mat_scale_row fld _ (mat_mul fld (proj1_sig B) (proj1_sig A)) i).
        2:{ rewrite length_mat_mul. exact HiB. }
        rewrite (nth_map_cmul_local fld _ _ j).
        assert (HBAraw : List.nth j (List.nth i (mat_mul fld (proj1_sig B) (proj1_sig A)) [])
                                    (cr_zero fld) = cr_zero fld).
        { apply (mat_mul_entry_zero fld (proj1_sig B) (proj1_sig A) i j HiB).
          intro k.
          destruct (Nat.eqb k i) eqn:Hki.
          - apply Nat.eqb_eq in Hki. subst k.
            rewrite (HA i j Hij HiA). apply (cr_mul_zero_r fld).
          - apply Nat.eqb_neq in Hki.
            assert (Hik : i <> k) by (intro; subst; apply Hki; reflexivity).
            rewrite (HB i k Hik HiB). apply (cr_mul_zero_l fld). }
        rewrite HBAraw. apply (cr_mul_zero_r fld). }
      rewrite HBAij. apply cr_add_zero.
    + apply cr_add_zero.
Qed.

(* diagonal_strictly_upper_bracket and upper_triangular_derived axioms
   removed: were unsound placeholders ([... <-> True] makes the reverse
   direction assert every matrix is strictly upper triangular). Not used. *)
