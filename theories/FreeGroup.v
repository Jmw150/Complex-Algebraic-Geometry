
(** Free Groups and the Word Problem

    We define the free group F_n on n generators, give a computable
    reduction to normal form, and implement a verified decision
    procedure for word equality.  The normal-form functions extract
    directly to OCaml via [Extraction].
*)

From Stdlib Require Import List Arith Bool Lia ProofIrrelevance.
Set Warnings "-warn-library-file-stdlib-vector".
From Stdlib Require Import Fin.
Set Warnings "+warn-library-file-stdlib-vector".
Import ListNotations.

From CAG Require Import Group.

(* ------------------------------------------------------------------ *)
(** * 1. Alphabet                                                       *)
(* ------------------------------------------------------------------ *)

(** A [Letter n] is a generator index together with a sign:
    [true]  = the generator itself,
    [false] = its formal inverse. *)
Definition Letter (n : nat) : Type := Fin.t n * bool.

(** Flip the sign to get the formal inverse of a letter. *)
Definition letter_inv {n : nat} (l : Letter n) : Letter n :=
  (fst l, negb (snd l)).

(** Decidable equality on [Letter n]. *)
Lemma letter_eq_dec : forall {n : nat} (x y : Letter n), {x = y} + {x <> y}.
Proof.
  intros n [i b] [j c].
  destruct (Fin.eq_dec i j) as [Hij | Hij].
  - destruct (Bool.bool_dec b c) as [Hbc | Hbc].
    + left. subst. reflexivity.
    + right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
Qed.

(** Lemmas about [letter_inv]. *)
Lemma letter_inv_involutive : forall {n : nat} (l : Letter n),
  letter_inv (letter_inv l) = l.
Proof.
  intros n [i b]. unfold letter_inv. simpl.
  rewrite Bool.negb_involutive. reflexivity.
Qed.

Lemma letter_inv_neq : forall {n : nat} (l : Letter n),
  letter_inv l <> l.
Proof.
  intros n [i b]. unfold letter_inv. simpl.
  intro H. inversion H.
  destruct b; discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(** * 2. Words                                                          *)
(* ------------------------------------------------------------------ *)

Definition Word (n : nat) : Type := list (Letter n).

(* ------------------------------------------------------------------ *)
(** * 3. Reduction to normal form                                       *)
(* ------------------------------------------------------------------ *)

(** [cancel_step w] finds the leftmost adjacent cancellable pair
    (a letter followed immediately by its inverse) and removes it.
    Returns [None] if the word is already reduced. *)
Fixpoint cancel_step {n : nat} (w : Word n) : option (Word n) :=
  match w with
  | []      => None
  | [_]     => None
  | x :: ((y :: rest) as tail) =>
      if letter_eq_dec y (letter_inv x)
      then Some rest
      else
        match cancel_step tail with
        | None    => None
        | Some w' => Some (x :: w')
        end
  end.

(** Specification lemmas keep [cancel_step] folded in hypotheses. *)
Lemma cancel_step_cancel : forall {n} (x y : Letter n) (rest : Word n),
  y = letter_inv x ->
  cancel_step (x :: y :: rest) = Some rest.
Proof.
  intros n x y rest H. simpl.
  destruct (letter_eq_dec y (letter_inv x)) as [|Hne]; [reflexivity|].
  contradiction.
Qed.

Lemma cancel_step_recurse : forall {n} (x y : Letter n) (rest : Word n),
  y <> letter_inv x ->
  cancel_step (x :: y :: rest) =
    match cancel_step (y :: rest) with
    | None    => None
    | Some w' => Some (x :: w')
    end.
Proof.
  intros n x y rest H. simpl.
  destruct (letter_eq_dec y (letter_inv x)) as [Heq|]; [contradiction|reflexivity].
Qed.

Lemma cancel_step_shortens : forall {n : nat} (w w' : Word n),
  cancel_step w = Some w' ->
  length w' + 2 = length w.
Proof.
  intros n w.
  induction w as [| x tail IH]; intros w' H.
  - discriminate.
  - destruct tail as [| y rest].
    + discriminate.
    + destruct (letter_eq_dec y (letter_inv x)) as [Heq | Hne].
      * rewrite cancel_step_cancel in H by exact Heq.
        injection H as <-. simpl. lia.
      * rewrite cancel_step_recurse in H by exact Hne.
        destruct (cancel_step (y :: rest)) as [w''|] eqn:Hcs.
        -- injection H as <-. simpl.
           pose proof (IH w'' eq_refl) as Hlen. simpl in Hlen. lia.
        -- discriminate.
Qed.

(** [reduce_aux fuel w] iterates [cancel_step] for at most [fuel]
    steps.  Setting [fuel = length w] always suffices because each
    step removes exactly two letters. *)
Fixpoint reduce_aux {n : nat} (fuel : nat) (w : Word n) : Word n :=
  match fuel with
  | O    => w
  | S k  =>
      match cancel_step w with
      | None    => w
      | Some w' => reduce_aux k w'
      end
  end.

Definition reduce {n : nat} (w : Word n) : Word n :=
  reduce_aux (length w) w.

(** A word is [reduced] when [cancel_step] finds nothing to cancel. *)
Definition reduced {n : nat} (w : Word n) : Prop :=
  cancel_step w = None.

(** The empty word is already reduced. *)
Lemma nil_reduced : forall {n : nat}, @reduced n [].
Proof. intros n. unfold reduced. reflexivity. Qed.

(** Helper: if [cancel_step w = None] then [reduce_aux] does nothing. *)
Lemma reduce_aux_none : forall {n : nat} (fuel : nat) (w : Word n),
  cancel_step w = None -> reduce_aux fuel w = w.
Proof.
  induction fuel as [| k IH]; intros w H.
  - reflexivity.
  - simpl. rewrite H. reflexivity.
Qed.

(** Helper: if [length w <= fuel] then [reduce_aux fuel w] is reduced. *)
Lemma reduce_aux_reduces : forall {n : nat} (fuel : nat) (w : Word n),
  (length w <= fuel)%nat -> reduced (reduce_aux fuel w).
Proof.
  induction fuel as [| k IH]; intros w Hlen.
  - (* length w = 0, so w = nil *)
    destruct w as [| x xs].
    + unfold reduced. reflexivity.
    + simpl in Hlen. lia.
  - simpl. unfold reduced.
    destruct (cancel_step w) as [w'|] eqn:Hcs.
    + apply IH.
      apply cancel_step_shortens in Hcs. lia.
    + exact Hcs.
Qed.

Lemma reduce_is_reduced : forall {n : nat} (w : Word n),
  reduced (reduce w).
Proof.
  intros n w. unfold reduce.
  apply reduce_aux_reduces. lia.
Qed.

Lemma reduce_idempotent : forall {n : nat} (w : Word n),
  reduce (reduce w) = reduce w.
Proof.
  intros n w.
  unfold reduce at 1.
  apply reduce_aux_none.
  apply reduce_is_reduced.
Qed.

(** If [cancel_step u = Some u'], the leftmost cancellation also applies
    when [v] is appended: [cancel_step (u ++ v) = Some (u' ++ v)]. *)
Lemma cancel_step_app_l : forall {n : nat} (u u' v : Word n),
  cancel_step u = Some u' ->
  cancel_step (u ++ v) = Some (u' ++ v).
Proof.
  intros n u.
  induction u as [| x [| y rest] IHu]; intros u' v Hcs.
  - discriminate.
  - discriminate.
  - (* u = x :: y :: rest *)
    destruct (letter_eq_dec y (letter_inv x)) as [Heq | Hne].
    + (* front pair cancels: u' = rest, goal is cancel_step (x::y::(rest++v)) = Some (rest++v) *)
      rewrite cancel_step_cancel in Hcs by exact Heq.
      injection Hcs as <-.
      apply cancel_step_cancel. exact Heq.
    + (* no cancel at front: u' = x :: w'', recurse into y :: rest *)
      rewrite cancel_step_recurse in Hcs by exact Hne.
      destruct (cancel_step (y :: rest)) as [w''|] eqn:Hcs2; [| discriminate].
      injection Hcs as <-.
      (* eqn:Hcs2 substituted cancel_step(y::rest) → Some w'' in IHu,
         so IHu now needs eq_refl : Some w'' = Some w'' *)
      pose proof (IHu w'' v eq_refl) as Happ.
      (* Happ : cancel_step ((y :: rest) ++ v) = Some (w'' ++ v) *)
      change (cancel_step (x :: y :: (rest ++ v)) = Some (x :: (w'' ++ v))).
      rewrite cancel_step_recurse by exact Hne.
      rewrite <- List.app_comm_cons in Happ.
      rewrite Happ. reflexivity.
Qed.

(** [reduce_aux fuel w] gives the same result for any fuel >= length w.
    Proof: extra fuel past the length does nothing (word is already reduced). *)
Lemma reduce_aux_extra_fuel : forall {n : nat} (fuel : nat) (w : Word n) (k : nat),
  (length w <= fuel)%nat ->
  reduce_aux (fuel + k) w = reduce_aux fuel w.
Proof.
  induction fuel as [| f IH]; intros w k Hlen.
  - (* fuel = 0, so w = [] and reduce_aux k [] = [] = reduce_aux 0 [] *)
    destruct w; [| simpl in Hlen; lia].
    rewrite reduce_aux_none by reflexivity. reflexivity.
  - simpl. destruct (cancel_step w) as [w'|] eqn:Hcs.
    + apply cancel_step_shortens in Hcs as Hshort.
      rewrite IH by lia. reflexivity.
    + reflexivity.
Qed.

(** Corollary: any fuel >= length w gives the same reduced word. *)
Lemma reduce_aux_sufficient : forall {n : nat} (w : Word n) k,
  (length w <= k)%nat -> reduce_aux k w = reduce w.
Proof.
  intros n w k Hlen. unfold reduce.
  replace k with (length w + (k - length w)) by lia.
  apply reduce_aux_extra_fuel. lia.
Qed.

(** One [cancel_step] in [u] gives the same [reduce] result on [u ++ v]. *)
Lemma reduce_cancel_step_app : forall {n : nat} (u u' v : Word n),
  cancel_step u = Some u' ->
  reduce (u ++ v) = reduce (u' ++ v).
Proof.
  intros n u u' v Hcs.
  apply cancel_step_shortens in Hcs as Hshort.  (* length u' + 2 = length u *)
  apply cancel_step_app_l with (v := v) in Hcs as Hcs_app.
  (* cancel_step (u ++ v) = Some (u' ++ v) *)
  unfold reduce at 1.
  destruct (length (u ++ v)) as [| k] eqn:Hluv.
  { rewrite List.length_app in Hluv. lia. }
  simpl. rewrite Hcs_app.
  apply reduce_aux_sufficient.
  rewrite List.length_app.
  rewrite List.length_app in Hluv.
  lia.
Qed.

(** Reducing inside [u] before appending [v] doesn't change the final normal form. *)
Lemma reduce_aux_app_l : forall {n : nat} (fuel : nat) (u v : Word n),
  (length u <= fuel)%nat ->
  reduce (reduce_aux fuel u ++ v) = reduce (u ++ v).
Proof.
  induction fuel as [| k IH]; intros u v Hlen.
  - destruct u; [reflexivity | simpl in Hlen; lia].
  - simpl. destruct (cancel_step u) as [u'|] eqn:Hcs.
    + apply cancel_step_shortens in Hcs as Hshort.
      rewrite IH by lia.
      symmetry. apply reduce_cancel_step_app. exact Hcs.
    + reflexivity.
Qed.

Lemma reduce_app_reduce_l : forall {n : nat} (u v : Word n),
  reduce (reduce u ++ v) = reduce (u ++ v).
Proof.
  intros n u v. unfold reduce at 2.
  apply reduce_aux_app_l. lia.
Qed.

(** Helper: inserting [a; letter_inv a] into a reduced prefix preserves
    the [cancel_step] result: the pair cancels leaving [us ++ v]. *)
Lemma cancel_step_reduced_insert : forall {n : nat} (us : Word n) (a : Letter n) (v : Word n),
  cancel_step us = None ->
  cancel_step (us ++ [a; letter_inv a] ++ v) = Some (us ++ v).
Proof.
  intros n us.
  induction us as [| x us' IH]; intros a v Hred.
  - (* us = [] *)
    cbn [List.app]. apply cancel_step_cancel. reflexivity.
  - destruct us' as [| y rest].
    + (* us = [x] *)
      cbn [List.app].
      destruct (letter_eq_dec a (letter_inv x)) as [Heq | Hne].
      * rewrite (cancel_step_cancel x a (letter_inv a :: v) Heq).
        rewrite Heq, letter_inv_involutive. reflexivity.
      * rewrite (cancel_step_recurse x a (letter_inv a :: v) Hne).
        rewrite (cancel_step_cancel a (letter_inv a) v eq_refl). reflexivity.
    + (* us = x :: y :: rest *)
      assert (Hne : y <> letter_inv x).
      { intro Heq.
        rewrite cancel_step_cancel in Hred by exact Heq. discriminate. }
      assert (Hred' : cancel_step (y :: rest) = None).
      { rewrite cancel_step_recurse in Hred by exact Hne.
        destruct (cancel_step (y :: rest)); [discriminate | reflexivity]. }
      specialize (IH a v Hred').
      change ((y :: rest) ++ [a; letter_inv a] ++ v) with (y :: rest ++ [a; letter_inv a] ++ v) in IH.
      change ((y :: rest) ++ v) with (y :: rest ++ v) in IH.
      change ((x :: y :: rest) ++ [a; letter_inv a] ++ v) with (x :: y :: rest ++ [a; letter_inv a] ++ v).
      change ((x :: y :: rest) ++ v) with (x :: y :: rest ++ v).
      rewrite (cancel_step_recurse x y (rest ++ [a; letter_inv a] ++ v) Hne).
      rewrite IH. reflexivity.
Qed.

(** Inserting a cancellable pair anywhere in [u] does not change [reduce]. *)
Lemma reduce_insert_cancel_aux : forall {n : nat} (fuel : nat) (u : Word n) (a : Letter n) (v : Word n),
  (length u <= fuel)%nat ->
  reduce (u ++ [a; letter_inv a] ++ v) = reduce (u ++ v).
Proof.
  induction fuel as [| k IH]; intros u a v Hlen.
  - (* fuel = 0, so u = [] *)
    destruct u as [| x rest]; [| simpl in Hlen; lia].
    (* goal reduces definitionally to: reduce (a :: letter_inv a :: v) = reduce v *)
    exact (reduce_cancel_step_app [a; letter_inv a] [] v
             (cancel_step_cancel a (letter_inv a) [] eq_refl)).
  - destruct (cancel_step u) as [u'|] eqn:Hcs.
    + (* cancel in u: step u to u' on both sides *)
      pose proof (cancel_step_shortens u u' Hcs) as Hshort.
      pose proof (reduce_cancel_step_app u u' ([a; letter_inv a] ++ v) Hcs) as Hl.
      assert (Hlen' : (length u' <= k)%nat) by lia.
      pose proof (IH u' a v Hlen') as Hmid.
      pose proof (reduce_cancel_step_app u u' v Hcs) as Hr.
      rewrite Hl, Hmid, <- Hr. reflexivity.
    + (* u already reduced: insert cancels via cancel_step_reduced_insert *)
      pose proof (cancel_step_reduced_insert u a v Hcs) as Hcsi.
      pose proof (reduce_cancel_step_app _ _ [] Hcsi) as H.
      rewrite List.app_nil_r in H. rewrite List.app_nil_r in H.
      exact H.
Qed.

Lemma reduce_insert_cancel : forall {n : nat} (u : Word n) (a : Letter n) (v : Word n),
  reduce (u ++ [a; letter_inv a] ++ v) = reduce (u ++ v).
Proof.
  intros n u a v. apply reduce_insert_cancel_aux with (fuel := length u). lia.
Qed.

(** Decompose a [cancel_step] into its underlying adjacent-pair cancellation. *)
Lemma cancel_step_split : forall {n : nat} (v v' : Word n),
  cancel_step v = Some v' ->
  exists (prefix : Word n) (a : Letter n) (suffix : Word n),
    v = prefix ++ [a; letter_inv a] ++ suffix /\
    v' = prefix ++ suffix.
Proof.
  intros n v.
  induction v as [| x rest IH]; intros v' Hcs.
  - discriminate.
  - destruct rest as [| y rest'].
    + discriminate.
    + destruct (letter_eq_dec y (letter_inv x)) as [Heq | Hne].
      * rewrite cancel_step_cancel in Hcs by exact Heq.
        injection Hcs as <-.
        exists [], x, rest'. split.
        -- rewrite Heq. reflexivity.
        -- reflexivity.
      * rewrite cancel_step_recurse in Hcs by exact Hne.
        case_eq (cancel_step (y :: rest')); [intros w'' Hcs2 | intro Hcs2].
        -- rewrite Hcs2 in Hcs. injection Hcs as <-.
           destruct (IH w'' Hcs2) as [prefix [a [suffix [Hv Hw'']]]].
           exists (x :: prefix), a, suffix. split.
           ++ simpl. f_equal. exact Hv.
           ++ simpl. f_equal. exact Hw''.
        -- rewrite Hcs2 in Hcs. discriminate.
Qed.

(** A [cancel_step] in [v] preserves [reduce (u ++ v)]. *)
Lemma reduce_cancel_step_app_r : forall {n : nat} (u v v' : Word n),
  cancel_step v = Some v' ->
  reduce (u ++ v) = reduce (u ++ v').
Proof.
  intros n u v v' Hcs.
  destruct (cancel_step_split v v' Hcs) as [prefix [a [suffix [Hv Hv']]]].
  subst v v'.
  exact (eq_trans
           (eq_trans
              (f_equal reduce (List.app_assoc u prefix ([a; letter_inv a] ++ suffix)))
              (reduce_insert_cancel (u ++ prefix) a suffix))
           (eq_sym (f_equal reduce (List.app_assoc u prefix suffix)))).
Qed.

(** Reducing inside [v] before appending to [u] doesn't change the normal form. *)
Lemma reduce_aux_app_r : forall {n : nat} (fuel : nat) (u v : Word n),
  (length v <= fuel)%nat ->
  reduce (u ++ reduce_aux fuel v) = reduce (u ++ v).
Proof.
  induction fuel as [| k IH]; intros u v Hlen.
  - destruct v as [| x rest]; [reflexivity | simpl in Hlen; lia].
  - simpl. destruct (cancel_step v) as [v'|] eqn:Hcs.
    + apply cancel_step_shortens in Hcs as Hshort.
      rewrite IH by lia.
      symmetry. apply reduce_cancel_step_app_r. exact Hcs.
    + reflexivity.
Qed.

Lemma reduce_app_reduce_r : forall {n : nat} (u v : Word n),
  reduce (u ++ reduce v) = reduce (u ++ v).
Proof.
  intros n u v. unfold reduce at 2.
  apply reduce_aux_app_r. lia.
Qed.

(* ------------------------------------------------------------------ *)
(** * 4. Free group operations                                          *)
(* ------------------------------------------------------------------ *)

(** Concatenate then reduce. *)
Definition free_mul {n : nat} (u v : Word n) : Word n :=
  reduce (u ++ v).

(** Reverse and flip every letter. *)
Definition free_inv {n : nat} (w : Word n) : Word n :=
  List.map letter_inv (List.rev w).

(** [free_inv] is an involution on words. *)
Lemma free_inv_involutive : forall {n : nat} (w : Word n),
  free_inv (free_inv w) = w.
Proof.
  intros n w. unfold free_inv.
  (* map letter_inv (rev (map letter_inv (rev w))) *)
  rewrite <- List.map_rev.      (* = map letter_inv (map letter_inv (rev (rev w))) *)
  rewrite List.rev_involutive.  (* = map letter_inv (map letter_inv w) *)
  rewrite List.map_map.         (* = map (letter_inv ∘ letter_inv) w *)
  rewrite (List.map_ext _ id).
  - apply List.map_id.
  - intros l. apply letter_inv_involutive.
Qed.

(** [free_inv] distributes over append (reversed). *)
Lemma free_inv_app : forall {n : nat} (u v : Word n),
  free_inv (u ++ v) = free_inv v ++ free_inv u.
Proof.
  intros n u v. unfold free_inv.
  rewrite List.rev_app_distr, List.map_app.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * 5. StrictGroup axioms for the free group                          *)
(* ------------------------------------------------------------------ *)

(** -- Identity laws are cheap: reduce respects [[] ++ w = w] etc. -- *)

Lemma free_id_right : forall {n : nat} (w : Word n),
  free_mul w [] = reduce w.
Proof.
  intros n w. unfold free_mul.
  rewrite List.app_nil_r. reflexivity.
Qed.

Lemma free_id_left : forall {n : nat} (w : Word n),
  free_mul [] w = reduce w.
Proof.
  intros n w. unfold free_mul. reflexivity.
Qed.

(** For any reduced word, [reduce w = w]. *)
Lemma reduce_self : forall {n : nat} (w : Word n),
  reduced w -> reduce w = w.
Proof.
  intros n w Hr. unfold reduce. apply reduce_aux_none. exact Hr.
Qed.

Lemma reduce_nil : @reduce 0 [] = [].
Proof. reflexivity. Qed.

(** Helper: if [cancel_step (u ++ v) = None] then [cancel_step u = None]. *)
Lemma cancel_step_app_none : forall {n} (u v : Word n),
  cancel_step (u ++ v) = None -> cancel_step u = None.
Proof.
  intros n u v H.
  destruct (cancel_step u) as [u'|] eqn:Hu.
  - exfalso.
    apply cancel_step_app_l with (v := v) in Hu.
    rewrite H in Hu. discriminate.
  - reflexivity.
Qed.

(** Helper: if [cancel_step (u ++ v) = None] then [cancel_step v = None]. *)
Lemma cancel_step_none_suffix : forall {n} (u v : Word n),
  cancel_step (u ++ v) = None -> cancel_step v = None.
Proof.
  intros n u.
  induction u as [| x u' IHu]; intros v H.
  - simpl in H. exact H.
  - cbn [List.app] in H.
    destruct (u' ++ v) as [| y rest] eqn:Huv.
    + apply List.app_eq_nil in Huv. destruct Huv as [_ ->].
      reflexivity.
    + destruct (letter_eq_dec y (letter_inv x)) as [Heq | Hne].
      * rewrite cancel_step_cancel in H by exact Heq. discriminate.
      * rewrite cancel_step_recurse in H by exact Hne.
        destruct (cancel_step (y :: rest)) as [w'|] eqn:Hcs.
        -- discriminate.
        -- apply IHu. rewrite Huv. exact Hcs.
Qed.

(** Helper: if [cancel_step (prefix ++ [x; y]) = None] then [y ≠ letter_inv x]. *)
Lemma cancel_step_none_last_pair : forall {n} (prefix : Word n) (x y : Letter n),
  cancel_step (prefix ++ [x; y]) = None -> y <> letter_inv x.
Proof.
  intros n prefix.
  induction prefix as [| a prefix' IH]; intros x y H.
  - cbn [List.app] in H.
    destruct (letter_eq_dec y (letter_inv x)) as [Heq | Hne].
    + rewrite cancel_step_cancel in H by exact Heq. discriminate.
    + exact Hne.
  - apply IH.
    apply cancel_step_none_suffix with (u := [a]).
    cbn [List.app]. exact H.
Qed.

(** [map letter_inv] preserves reducedness. *)
Lemma cancel_step_none_map_inv : forall {n} (w : Word n),
  cancel_step w = None -> cancel_step (List.map letter_inv w) = None.
Proof.
  intros n w.
  induction w as [| x w' IH]; intro H.
  - reflexivity.
  - destruct w' as [| y rest].
    + reflexivity.
    + destruct (letter_eq_dec y (letter_inv x)) as [Heq | Hne].
      * rewrite cancel_step_cancel in H by exact Heq. discriminate.
      * rewrite cancel_step_recurse in H by exact Hne.
        destruct (cancel_step (y :: rest)) as [w''|] eqn:Hcs.
        -- discriminate.
        -- cbn [List.map].
           assert (Hne' : letter_inv y <> x).
           { intro Heq'. apply Hne.
             apply (f_equal letter_inv) in Heq'.
             rewrite letter_inv_involutive in Heq'. exact Heq'. }
           rewrite cancel_step_recurse by (rewrite letter_inv_involutive; exact Hne').
           cbn [List.map] in IH.
           rewrite (IH eq_refl). reflexivity.
Qed.

(** [rev] preserves reducedness. *)
Lemma cancel_step_none_rev : forall {n} (w : Word n),
  cancel_step w = None -> cancel_step (List.rev w) = None.
Proof.
  intros n w.
  induction w as [| x w' IH] using List.rev_ind; intro H.
  - reflexivity.
  - rewrite List.rev_app_distr. cbn [List.rev List.app].
    assert (Hw' : cancel_step w' = None).
    { apply cancel_step_app_none with (v := [x]). exact H. }
    specialize (IH Hw') as Hrev.
    destruct (List.rev w') as [| y rest] eqn:Hrevw'.
    + reflexivity.
    + assert (Hne : x <> letter_inv y).
      { apply cancel_step_none_last_pair with (prefix := List.rev rest).
        assert (Heqw' : w' = List.rev rest ++ [y]).
        { rewrite <- (List.rev_involutive w'), Hrevw'. reflexivity. }
        rewrite Heqw' in H. rewrite <- List.app_assoc in H. simpl in H. exact H. }
      assert (Hne' : y <> letter_inv x).
      { intro Heq'. apply Hne.
        apply (f_equal letter_inv) in Heq'.
        rewrite letter_inv_involutive in Heq'. exact (eq_sym Heq'). }
      rewrite cancel_step_recurse by exact Hne'.
      rewrite Hrev. reflexivity.
Qed.

(** The inverse of a reduced word is reduced. *)
Lemma free_inv_reduced : forall {n} (w : Word n),
  reduced w -> reduced (free_inv w).
Proof.
  intros n w Hr. unfold reduced, free_inv.
  apply cancel_step_none_map_inv.
  apply cancel_step_none_rev.
  exact Hr.
Qed.

(** -- Helpers for inverse laws -- *)

(** Appending a zero-reducing word does not change the normal form. *)
Lemma reduce_r_zero : forall {n : nat} (u A : Word n),
  reduce A = [] ->
  reduce (u ++ A) = reduce u.
Proof.
  intros n u A HA.
  rewrite <- reduce_app_reduce_r.
  rewrite HA. rewrite List.app_nil_r. reflexivity.
Qed.

(** A zero-reducing middle segment can be erased. *)
Lemma reduce_mid_zero : forall {n : nat} (u A v : Word n),
  reduce A = [] ->
  reduce (u ++ A ++ v) = reduce (u ++ v).
Proof.
  intros n u A v HA.
  rewrite List.app_assoc.
  rewrite <- (reduce_app_reduce_l (u ++ A) v).
  rewrite (reduce_r_zero u A HA).
  apply reduce_app_reduce_l.
Qed.

Lemma free_inv_cons : forall {n : nat} (x : Letter n) (rest : Word n),
  free_inv (x :: rest) = free_inv rest ++ [letter_inv x].
Proof.
  intros n x rest. unfold free_inv. simpl.
  rewrite List.map_app. reflexivity.
Qed.

Lemma reduce_single_cancel : forall {n : nat} (x : Letter n),
  reduce [x; letter_inv x] = [].
Proof.
  intros n x.
  unfold reduce.
  cbn [length reduce_aux].
  rewrite cancel_step_cancel by reflexivity.
  reflexivity.
Qed.

(** -- Inverse laws -- *)

Lemma free_inv_right : forall {n : nat} (w : Word n),
  free_mul w (free_inv w) = [].
Proof.
  intros n w. unfold free_mul.
  induction w as [| x rest IH].
  - reflexivity.
  - rewrite free_inv_cons.
    change ((x :: rest) ++ (free_inv rest ++ [letter_inv x]))
      with ([x] ++ rest ++ free_inv rest ++ [letter_inv x]).
    rewrite (List.app_assoc rest (free_inv rest) [letter_inv x]).
    rewrite (reduce_mid_zero [x] (rest ++ free_inv rest) [letter_inv x] IH).
    apply reduce_single_cancel.
Qed.

Lemma free_inv_left : forall {n : nat} (w : Word n),
  free_mul (free_inv w) w = [].
Proof.
  intros n w.
  rewrite <- (free_inv_involutive w) at 2.
  apply free_inv_right.
Qed.

(** -- Associativity -- *)

Lemma free_assoc : forall {n : nat} (u v w : Word n),
  free_mul u (free_mul v w) = free_mul (free_mul u v) w.
Proof.
  intros n u v w. unfold free_mul.
  (* LHS: reduce (u ++ reduce (v ++ w))
     RHS: reduce (reduce (u ++ v) ++ w) *)
  rewrite reduce_app_reduce_r.  (* LHS → reduce (u ++ (v ++ w)) *)
  rewrite reduce_app_reduce_l.  (* RHS → reduce ((u ++ v) ++ w) *)
  rewrite List.app_assoc.
  reflexivity.
Qed.

(** The StrictGroup instance.

    We use [reduce w] as the "canonical" element for each word, so
    [se = []] and the [sid_right]/[sid_left] goals become
    [free_mul w [] = w] and [free_mul [] w = w] — true only when [w]
    is already reduced.  To avoid this subtlety cleanly we note that
    all five axioms hold up to [reduce]: we state the group on the
    nose and admit the two identity axioms pending a proof that
    [reduce] is a retraction. *)

(** ** Sigma-type carrier: [{w : Word n | reduced w}]

    The correct carrier for the free group is the type of already-reduced
    words.  The identity [se = ([], nil_reduced)] and operations are defined
    so that the product of two reduced words is [reduce (u ++ v)], which is
    always reduced by [reduce_is_reduced].

    The identity axioms are now proved (using [reduce_self]).
    The inverse and associativity axioms are still admitted pending
    the Church–Rosser / confluence proof for the reduction system. *)

Definition RWord (n : nat) : Type := { w : Word n | reduced w }.

(** Equality of RWord elements: equal first components suffice. *)
Lemma rword_eq : forall {n} (a b : Word n) (Ha : reduced a) (Hb : reduced b),
  a = b -> exist _ a Ha = exist _ b Hb.
Proof.
  intros n a b Ha Hb ->. f_equal. apply proof_irrelevance.
Qed.

(** Multiplication: concatenate and reduce. *)
Definition rword_mul {n} (u v : RWord n) : RWord n :=
  exist _ (reduce (proj1_sig u ++ proj1_sig v)) (reduce_is_reduced _).

(** Identity: the empty word. *)
Definition rword_e {n} : RWord n :=
  exist _ [] nil_reduced.

(** Inverse: reverse and flip, which preserves reducedness. *)
Definition rword_inv {n} (w : RWord n) : RWord n :=
  exist _ (free_inv (proj1_sig w)) (free_inv_reduced _ (proj2_sig w)).

(** sid_right: [u * e = u] *)
Lemma rword_id_right : forall {n} (w : RWord n),
  rword_mul w rword_e = w.
Proof.
  intros n [w Hw]. apply rword_eq. simpl.
  rewrite List.app_nil_r. apply reduce_self. exact Hw.
Qed.

(** sid_left: [e * u = u] *)
Lemma rword_id_left : forall {n} (w : RWord n),
  rword_mul rword_e w = w.
Proof.
  intros n [w Hw]. apply rword_eq. simpl.
  apply reduce_self. exact Hw.
Qed.

(** Associativity: pending [reduce_app_reduce_r] (Church–Rosser). *)
Lemma rword_assoc : forall {n} (u v w : RWord n),
  rword_mul u (rword_mul v w) = rword_mul (rword_mul u v) w.
Proof.
  intros n [u Hu] [v Hv] [w Hw]. apply rword_eq. simpl.
  rewrite reduce_app_reduce_r. rewrite reduce_app_reduce_l.
  rewrite List.app_assoc. reflexivity.
Qed.

(** Inverse laws: pending confluence + free group cancellation. *)
Lemma rword_inv_right : forall {n} (w : RWord n),
  rword_mul w (rword_inv w) = rword_e.
Proof.
  intros n [w Hw]. apply rword_eq. simpl.
  apply free_inv_right.
Qed.

Lemma rword_inv_left : forall {n} (w : RWord n),
  rword_mul (rword_inv w) w = rword_e.
Proof.
  intros n [w Hw]. apply rword_eq. simpl.
  apply free_inv_left.
Qed.

(** The free group on n generators as a StrictGroup on reduced words. *)
Definition FreeGroup (n : nat) : StrictGroup (RWord n) :=
  mkSG (RWord n)
    (@rword_mul n)
    (@rword_e n)
    (@rword_inv n)
    (fun u v w => rword_assoc u v w)
    (fun w => rword_id_right w)
    (fun w => rword_id_left w)
    (fun w => rword_inv_right w)
    (fun w => rword_inv_left w).

(* ------------------------------------------------------------------ *)
(** * 6. Word problem decision procedure                                *)
(* ------------------------------------------------------------------ *)

(** Compare two words by comparing their normal forms. *)
Definition word_eq {n : nat} (u v : Word n) : bool :=
  match List.list_eq_dec (@letter_eq_dec n) (reduce u) (reduce v) with
  | left  _ => true
  | right _ => false
  end.

(** Correctness: [word_eq u v = true] iff [u] and [v] represent
    the same element of [FreeGroup n], i.e. [reduce u = reduce v]. *)
Lemma word_eq_correct : forall {n : nat} (u v : Word n),
  word_eq u v = true <-> reduce u = reduce v.
Proof.
  intros n u v. unfold word_eq.
  destruct (List.list_eq_dec (@letter_eq_dec n) (reduce u) (reduce v)) as [Heq | Hne].
  - split; [intros _; exact Heq | intros _; reflexivity].
  - split; [discriminate | intro H; contradiction].
Qed.

Lemma word_eq_refl : forall {n : nat} (w : Word n),
  word_eq w w = true.
Proof.
  intros n w. apply word_eq_correct. reflexivity.
Qed.

Lemma word_eq_sym : forall {n : nat} (u v : Word n),
  word_eq u v = true -> word_eq v u = true.
Proof.
  intros n u v H.
  apply word_eq_correct. symmetry. apply word_eq_correct. exact H.
Qed.

Lemma word_eq_trans : forall {n : nat} (u v w : Word n),
  word_eq u v = true -> word_eq v w = true -> word_eq u w = true.
Proof.
  intros n u v w Huv Hvw.
  apply word_eq_correct.
  rewrite (proj1 (word_eq_correct u v) Huv).
  apply word_eq_correct. exact Hvw.
Qed.

(* ------------------------------------------------------------------ *)
(** * 7. Extraction                                                     *)
(* ------------------------------------------------------------------ *)

(** Add to Extract.v (or a dedicated FreeExtract.v):

      From CAG Require Import FreeGroup.
      Extraction "lib/free_group.ml" reduce word_eq free_mul free_inv FreeGroup.

    The OCaml driver (bin/word_problem.ml) can then call:
      - [reduce] to normalize
      - [word_eq] to test equality
    on words over {a, b, A, B} (= F_2 with n = 2).

    Example encoding for F_2 (n = 2):
      a  = (Fin.F1,          true)
      b  = (Fin.FS Fin.F1,   true)
      A  = (Fin.F1,          false)   (* a^-1 *)
      B  = (Fin.FS Fin.F1,   false)   (* b^-1 *)

    Queries:
      word_eq [a;b;A;B] []      (* commutator ≠ e  → false *)
      word_eq [a;b;A]   [b]     (* aba^-1 = b?     → false in F_2 *)
      word_eq [a;A;b;B;a;A;b;B] []  (* reduces to []  → true *)
*)
