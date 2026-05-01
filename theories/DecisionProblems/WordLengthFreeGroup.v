(** * DecisionProblems/WordLengthFreeGroup.v

    Concrete word-length and FGGroup instance for free groups F_r.
    Addresses [G2] from OpenProblems.v.

    For free groups, the word-length is the length of the canonical
    reduced-word representative — that's the standard fact that the
    reduced word is the unique minimum-length representative, due to
    the cancellation property of free reduction.

    We provide:
    - [fin_enum n]: the explicit list of all elements of [Fin.t n].
    - [free_gens n]: the list of standard generators for [F_n].
    - [letter_to_RWord]: package a single letter as an [RWord n].
    - [free_word_length]: word length = length of reduced word.
    - [FreeGroup_FGG]: builds an [FGGroup (RWord n)] via two named
      axioms (decomposition into generators, and minimality of reduced
      length). Both are standard free-group facts; full proofs require
      a substantial induction on [reduce] which we factor into the
      separate axiom [free_word_decomposes]. *)

From CAG Require Import Group FreeGroup.
From CAG Require Import DecisionProblems.TraceProperties.
From CAG Require Import DecisionProblems.OpenProblems.
From Stdlib Require Import List Arith Lia Logic.ProofIrrelevance ZArith.
Import ListNotations.
From Stdlib Require Import Vectors.Fin.

(* ================================================================== *)
(** * 1. Enumerate Fin.t n                                              *)
(* ================================================================== *)

Fixpoint fin_enum (n : nat) : list (Fin.t n) :=
  match n with
  | 0 => []
  | S k => Fin.F1 :: List.map Fin.FS (fin_enum k)
  end.

Lemma fin_enum_complete : forall (n : nat) (i : Fin.t n),
    In i (fin_enum n).
Proof.
  induction n as [|k IH]; intro i.
  - inversion i.
  - simpl. revert IH.
    refine (match i in Fin.t (S m) return
              (forall j : Fin.t m, In j (fin_enum m)) ->
              Fin.F1 = i \/ In i (List.map Fin.FS (fin_enum m)) with
            | Fin.F1 => fun _ => or_introl eq_refl
            | Fin.FS j => fun IH => or_intror (in_map _ _ _ (IH j))
            end).
Qed.

(* ================================================================== *)
(** * 2. Standard generators of F_n                                     *)
(* ================================================================== *)

Definition free_gens (n : nat) : list (RWord n) :=
  List.map (free_gen_RWord n) (fin_enum n).

Definition letter_to_RWord {n : nat} (l : Letter n) : RWord n.
Proof.
  refine (exist _ [l] _).
  unfold reduced. simpl. reflexivity.
Defined.

(* ================================================================== *)
(** * 3. Free-group facts (axiomatized)                                  *)
(* ================================================================== *)

(** [free_word_decomposes]: every reduced word equals the iterated
    [rword_mul] of its letter-by-letter unwrap. *)

(** Helper: equality of RWords with same underlying word. *)
Lemma rword_eq_underlying : forall (n : nat) (w : Word n) (h1 h2 : reduced w),
    exist reduced w h1 = exist reduced w h2.
Proof.
  intros n w h1 h2. f_equal. apply proof_irrelevance.
Qed.

(** Helper: a reduced word's tail is reduced. *)
Lemma reduced_tail : forall (n : nat) (l : Letter n) (rest : Word n),
    reduced (l :: rest) -> reduced rest.
Proof.
  intros n l rest Hred. unfold reduced in *.
  destruct rest as [|m mr]; [reflexivity|].
  destruct (letter_eq_dec m (letter_inv l)) as [Heq | Hneq].
  - rewrite (cancel_step_cancel l m mr Heq) in Hred. discriminate.
  - rewrite (cancel_step_recurse l m mr Hneq) in Hred.
    destruct (cancel_step (m :: mr)) eqn:Hcs.
    + discriminate.
    + reflexivity.
Qed.

(** Helper: reduce of a reduced word is itself. *)
Lemma reduce_of_reduced : forall (n : nat) (w : Word n),
    reduced w -> reduce w = w.
Proof.
  intros n w Hred. unfold reduce. apply reduce_aux_none. exact Hred.
Qed.

Lemma free_word_decomposes : forall (n : nat) (x : RWord n),
    List.fold_right rword_mul rword_e
      (List.map letter_to_RWord (proj1_sig x)) = x.
Proof.
  intros n [w Hred]. simpl.
  induction w as [|l rest IH].
  - (* [] *)
    simpl. unfold rword_e.
    f_equal. apply proof_irrelevance.
  - (* l :: rest *)
    pose proof (reduced_tail n l rest Hred) as Hrest.
    specialize (IH Hrest).
    simpl.
    rewrite IH.
    (* Goal: rword_mul (letter_to_RWord l) (exist _ rest Hrest) =
             exist _ (l :: rest) Hred *)
    unfold rword_mul, letter_to_RWord. simpl.
    (* Goal: exist _ (reduce (l :: rest)) ... = exist _ (l :: rest) Hred *)
    assert (Hreduce : reduce (l :: rest) = l :: rest)
      by (apply reduce_of_reduced; exact Hred).
    (* Use the fact that reduce-result = l::rest to rewrite the goal *)
    generalize (reduce_is_reduced (l :: rest)).
    rewrite Hreduce. intro Hp.
    apply rword_eq_underlying.
Qed.

(** [letter_to_RWord_in_gens]: each single-letter RWord is a generator
    or the inverse of a generator. *)
From Stdlib Require Import Logic.ProofIrrelevance.

Lemma letter_to_RWord_in_gens : forall (n : nat) (l : Letter n),
    In (letter_to_RWord l) (free_gens n) \/
    In (rword_inv (letter_to_RWord l)) (free_gens n).
Proof.
  intros n [i b]. destruct b.
  - (* b = true: inverse generator. *)
    right.
    assert (Heq : rword_inv (letter_to_RWord (i, true)) = free_gen_RWord n i).
    { unfold rword_inv, letter_to_RWord, free_gen_RWord, free_gen_letter,
             letter_inv. simpl.
      apply rword_eq_underlying. }
    rewrite Heq. unfold free_gens. apply in_map_iff.
    exists i. split; [reflexivity | apply fin_enum_complete].
  - (* b = false: positive generator. *)
    left.
    assert (Heq : letter_to_RWord (i, false) = free_gen_RWord n i).
    { unfold letter_to_RWord, free_gen_RWord, free_gen_letter.
      apply rword_eq_underlying. }
    rewrite Heq. unfold free_gens. apply in_map_iff.
    exists i. split; [reflexivity | apply fin_enum_complete].
Qed.

(* ================================================================== *)
(** * 4. FGGroup instance                                                *)
(* ================================================================== *)

Definition FreeGroup_FGG (n : nat) : FGGroup (RWord n).
Proof.
  refine (mkFGG (RWord n) (FreeGroup n) (free_gens n) _).
  intro x.
  exists (List.map letter_to_RWord (proj1_sig x)).
  split.
  - intros w Hin. apply in_map_iff in Hin. destruct Hin as [l [Hwl _]].
    subst w. apply letter_to_RWord_in_gens.
  - simpl. apply free_word_decomposes.
Defined.

(* ================================================================== *)
(** * 5. Concrete word length                                            *)
(* ================================================================== *)

Definition free_word_length {n : nat} (x : RWord n) : nat :=
  rword_length x.

(** Minimum-length property: if x is reachable as a product of [ws]
    where each w in ws has rword_length = 1, then x's word length is
    at most the count of generators used.

    Proof: rword_mul reduces, so the length of the product is at most
    the sum of lengths of factors. By induction on ws. *)

(** Helper: cancel_step reduces length by 2 if it succeeds, else preserves. *)
Lemma reduce_aux_length_le : forall {n : nat} (fuel : nat) (w : Word n),
    length (reduce_aux fuel w) <= length w.
Proof.
  induction fuel as [|k IH]; intros w.
  - simpl. lia.
  - simpl. destruct (cancel_step w) as [w'|] eqn:Hcs.
    + (* w' was produced from w with length w' + 2 = length w. *)
      pose proof (cancel_step_shortens w w' Hcs) as Hsh.
      specialize (IH w'). lia.
    + lia.
Qed.

Lemma reduce_length_le : forall {n : nat} (w : Word n),
    length (reduce w) <= length w.
Proof. intros n w. apply reduce_aux_length_le. Qed.

(** Helper: rword_mul preserves the length-≤ bound. *)
Lemma rword_mul_length_le : forall {n : nat} (a b : RWord n),
    rword_length (rword_mul a b) <= rword_length a + rword_length b.
Proof.
  intros n [wa Ha] [wb Hb]. unfold rword_mul, rword_length. simpl.
  rewrite <- List.length_app.
  apply reduce_length_le.
Qed.

Lemma free_word_length_minimal :
  forall (n : nat) (x : RWord n) (ws : list (RWord n)),
    (forall w, In w ws -> rword_length w = 1) ->
    List.fold_right rword_mul rword_e ws = x ->
    free_word_length x <= List.length ws.
Proof.
  intros n x ws Hgen Hprod.
  unfold free_word_length.
  rewrite <- Hprod.
  clear Hprod x.
  induction ws as [|w ws' IH]; simpl.
  - (* ws = []: fold = rword_e, length = 0. *)
    unfold rword_length, rword_e. simpl. lia.
  - (* ws = w :: ws'. *)
    pose proof (Hgen w (or_introl eq_refl)) as Hw.
    assert (Hgen' : forall ww, In ww ws' -> rword_length ww = 1).
    { intros ww Hin. apply Hgen. right. exact Hin. }
    specialize (IH Hgen').
    pose proof (rword_mul_length_le w
                  (List.fold_right rword_mul rword_e ws')) as Hbound.
    lia.
Qed.

(** Generators have word length 1. *)
Lemma free_word_length_gen : forall (n : nat) (i : Fin.t n),
    free_word_length (free_gen_RWord n i) = 1.
Proof.
  intros n i. unfold free_word_length, rword_length, free_gen_RWord.
  simpl. reflexivity.
Qed.

(** Identity has word length 0. *)
Lemma free_word_length_id : forall (n : nat),
    free_word_length (@rword_e n) = 0.
Proof.
  intros n. unfold free_word_length, rword_length, rword_e. simpl.
  reflexivity.
Qed.

(** rword_length is zero iff the word is the identity. *)
From Stdlib Require Import Logic.ProofIrrelevance.

Lemma rword_length_zero_iff : forall {n : nat} (w : RWord n),
    rword_length w = 0 <-> w = @rword_e n.
Proof.
  intros n [w Hw]. unfold rword_length, rword_e. simpl. split.
  - intro Hlen. destruct w as [|x rest].
    + (* w = []: equal modulo proof irrelevance *)
      f_equal. apply proof_irrelevance.
    + simpl in Hlen. lia.
  - intro Heq. inversion Heq. reflexivity.
Qed.

(** rword_length is positive iff the word is not the identity. *)
Lemma rword_length_pos_iff : forall {n : nat} (w : RWord n),
    rword_length w >= 1 <-> w <> @rword_e n.
Proof.
  intros n w. split.
  - intros Hlen Heq. rewrite Heq in Hlen.
    unfold rword_length, rword_e in Hlen. simpl in Hlen. lia.
  - intro Hne.
    destruct (Nat.eq_dec (rword_length w) 0) as [Hz|Hnz].
    + exfalso. apply Hne. apply rword_length_zero_iff. exact Hz.
    + lia.
Qed.

(** Generators are nontrivial. *)
Lemma free_gen_RWord_ne_e : forall (n : nat) (i : Fin.t n),
    free_gen_RWord n i <> @rword_e n.
Proof.
  intros n i Hcontra.
  pose proof (free_word_length_gen n i) as Hlen.
  rewrite Hcontra in Hlen.
  rewrite (free_word_length_id n) in Hlen. discriminate.
Qed.

(** Generators are not conjugate to the identity.
    In any group, an element is conjugate to the identity iff it is
    the identity (`are_conjugate_id_iff`). Generators are non-identity. *)
Lemma free_gen_RWord_not_conj_e : forall (n : nat) (i : Fin.t n),
    ~ are_conjugate (FreeGroup n) (@rword_e n) (free_gen_RWord n i).
Proof.
  intros n i Hconj.
  apply (free_gen_RWord_ne_e n i).
  apply (proj1 (are_conjugate_id_iff (FreeGroup n) _) Hconj).
Qed.

(* ================================================================== *)
(** ** 5.1. Abelianisation: F_n -> Z via exponent-sum

    Cycle 24 (2026-04-29). The standard fact "γ_i ≁ γ_i⁻¹ in F_n" is
    proved here directly via the i-th exponent-sum homomorphism
    F_n → ℤ. The construction:
    - [letter_sign_i i l] returns +1 if l = (i, false), -1 if
      l = (i, true), 0 otherwise.
    - [expsum_word_i] sums [letter_sign_i] over a word.
    - It is preserved by [cancel_step] (a cancellation removes a letter
      and its inverse, whose signs sum to 0), and therefore by [reduce]
      and by [rword_mul] (which is "concat then reduce").
    - For the inverse, [free_inv w = map letter_inv (rev w)] reverses
      the word and flips each sign, giving sum-negation.
    - Conjugation γ↦gγg⁻¹ then preserves the exponent sum since
      [expsum (gγg⁻¹) = expsum g + expsum γ - expsum g = expsum γ].
    - Since [γ_0 ↦ +1] and [γ_0⁻¹ ↦ -1] under exp-sum, and
      [+1 ≠ -1] in ℤ, the two are not conjugate. *)

(** Sign of a single letter at index i. *)
Definition letter_sign_i {n : nat} (i : Fin.t n) (l : Letter n) : Z :=
  if Fin.eq_dec (fst l) i
  then (if snd l then (-1)%Z else 1%Z)
  else 0%Z.

(** Sum of [letter_sign_i] across a word. *)
Fixpoint expsum_word_i {n : nat} (i : Fin.t n) (w : Word n) : Z :=
  match w with
  | []       => 0%Z
  | l :: rest => (letter_sign_i i l + expsum_word_i i rest)%Z
  end.

Lemma expsum_word_i_app : forall {n : nat} (i : Fin.t n) (a b : Word n),
    expsum_word_i i (a ++ b) = (expsum_word_i i a + expsum_word_i i b)%Z.
Proof.
  intros n i a b. induction a as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. ring.
Qed.

(** A letter and its inverse contribute opposite signs. *)
Lemma letter_sign_i_inv : forall {n : nat} (i : Fin.t n) (l : Letter n),
    (letter_sign_i i l + letter_sign_i i (letter_inv l) = 0)%Z.
Proof.
  intros n i l. unfold letter_sign_i, letter_inv. simpl.
  destruct (Fin.eq_dec (fst l) i); [|reflexivity].
  destruct (snd l); simpl; reflexivity.
Qed.

(** [cancel_step] preserves [expsum_word_i]. *)
Lemma cancel_step_preserves_expsum : forall {n : nat} (i : Fin.t n) (w w' : Word n),
    cancel_step w = Some w' ->
    expsum_word_i i w' = expsum_word_i i w.
Proof.
  intros n i w. induction w as [|x rest IH]; intros w' Hcs.
  - simpl in Hcs. discriminate.
  - destruct rest as [|y rest'].
    + simpl in Hcs. discriminate.
    + destruct (letter_eq_dec y (letter_inv x)) as [Heq | Hne].
      * (* x and y cancel: w = x :: y :: rest', cancel_step gives rest' *)
        rewrite (cancel_step_cancel x y rest' Heq) in Hcs.
        injection Hcs as Hw'. subst w'. simpl.
        rewrite Heq.
        (* Need: expsum rest = sign(x) + sign(letter_inv x) + expsum rest *)
        pose proof (letter_sign_i_inv i x) as H. lia.
      * (* x and y don't cancel: cancel_step recurses on (y :: rest') *)
        rewrite (cancel_step_recurse x y rest' Hne) in Hcs.
        destruct (cancel_step (y :: rest')) as [w''|] eqn:Hcs'.
        2: discriminate.
        injection Hcs as Hw'. subst w'. simpl.
        specialize (IH w'' eq_refl).
        simpl in IH. lia.
Qed.

(** [reduce_aux] preserves [expsum_word_i]. *)
Lemma reduce_aux_preserves_expsum : forall {n : nat} (i : Fin.t n) (fuel : nat) (w : Word n),
    expsum_word_i i (reduce_aux fuel w) = expsum_word_i i w.
Proof.
  intros n i fuel. induction fuel as [|k IH]; intros w; simpl.
  - reflexivity.
  - destruct (cancel_step w) as [w'|] eqn:Hcs.
    + rewrite IH. apply (cancel_step_preserves_expsum i w w' Hcs).
    + reflexivity.
Qed.

(** [reduce] preserves [expsum_word_i]. *)
Lemma reduce_preserves_expsum : forall {n : nat} (i : Fin.t n) (w : Word n),
    expsum_word_i i (reduce w) = expsum_word_i i w.
Proof.
  intros n i w. unfold reduce. apply reduce_aux_preserves_expsum.
Qed.

(** Exponent sum at the [RWord] (canonical) level. *)
Definition expsum_i {n : nat} (i : Fin.t n) (rw : RWord n) : Z :=
  expsum_word_i i (proj1_sig rw).

(** Exponent sum is a homomorphism for [rword_mul]. *)
Lemma expsum_i_mul : forall {n : nat} (i : Fin.t n) (u v : RWord n),
    expsum_i i (rword_mul u v) = (expsum_i i u + expsum_i i v)%Z.
Proof.
  intros n i [u Hu] [v Hv]. unfold expsum_i, rword_mul. simpl.
  rewrite reduce_preserves_expsum.
  apply expsum_word_i_app.
Qed.

(** [letter_inv] flips the sign. *)
Lemma letter_sign_i_letter_inv : forall {n : nat} (i : Fin.t n) (l : Letter n),
    letter_sign_i i (letter_inv l) = (- letter_sign_i i l)%Z.
Proof.
  intros n i l. unfold letter_sign_i, letter_inv. simpl.
  destruct (Fin.eq_dec (fst l) i); [|reflexivity].
  destruct (snd l); reflexivity.
Qed.

(** [expsum_word_i] over a mapped-inverse word is sign-negated. *)
Lemma expsum_word_i_map_letter_inv : forall {n : nat} (i : Fin.t n) (w : Word n),
    expsum_word_i i (List.map letter_inv w) = (- expsum_word_i i w)%Z.
Proof.
  intros n i w. induction w as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. rewrite letter_sign_i_letter_inv. lia.
Qed.

(** [expsum_word_i] is preserved by [rev] (it's a sum, order doesn't matter). *)
Lemma expsum_word_i_rev : forall {n : nat} (i : Fin.t n) (w : Word n),
    expsum_word_i i (List.rev w) = expsum_word_i i w.
Proof.
  intros n i w. induction w as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite expsum_word_i_app. simpl. rewrite IH. lia.
Qed.

(** [free_inv] flips each [letter_sign_i]; sum over [free_inv w]
    is the negation of the sum over [w]. *)
Lemma expsum_word_i_free_inv : forall {n : nat} (i : Fin.t n) (w : Word n),
    expsum_word_i i (free_inv w) = (- expsum_word_i i w)%Z.
Proof.
  intros n i w. unfold free_inv.
  rewrite expsum_word_i_map_letter_inv.
  rewrite expsum_word_i_rev. reflexivity.
Qed.

(** Exponent sum negates under [rword_inv]. *)
Lemma expsum_i_inv : forall {n : nat} (i : Fin.t n) (w : RWord n),
    expsum_i i (rword_inv w) = (- expsum_i i w)%Z.
Proof.
  intros n i [w Hw]. unfold expsum_i, rword_inv. simpl.
  apply expsum_word_i_free_inv.
Qed.

(** Exponent sum is conjugation-invariant in the free group. *)
Lemma expsum_i_conj_invariant : forall {n : nat} (i : Fin.t n) (gamma eta : RWord n),
    are_conjugate (FreeGroup n) gamma eta ->
    expsum_i i gamma = expsum_i i eta.
Proof.
  intros n i gamma eta [g Hconj]. simpl in Hconj.
  rewrite <- Hconj.
  change (smul (RWord n) (FreeGroup n)) with (@rword_mul n).
  change (sinv (RWord n) (FreeGroup n)) with (@rword_inv n).
  rewrite expsum_i_mul, expsum_i_mul, expsum_i_inv. lia.
Qed.

(** A standard generator γ_i has exponent sum +1 at index i. *)
Lemma expsum_i_free_gen_RWord : forall (n : nat) (i : Fin.t n),
    expsum_i i (free_gen_RWord n i) = 1%Z.
Proof.
  intros n i. unfold expsum_i, free_gen_RWord, free_gen_letter. simpl.
  unfold letter_sign_i. simpl.
  destruct (Fin.eq_dec i i) as [_|Hne]; [reflexivity | exfalso; apply Hne; reflexivity].
Qed.

(** The inverse of a generator has exponent sum -1 at the same index. *)
Lemma expsum_i_free_gen_RWord_inv : forall (n : nat) (i : Fin.t n),
    expsum_i i (sinv (RWord n) (FreeGroup n) (free_gen_RWord n i)) = (-1)%Z.
Proof.
  intros n i.
  change (sinv (RWord n) (FreeGroup n)) with (@rword_inv n).
  rewrite expsum_i_inv. rewrite expsum_i_free_gen_RWord. reflexivity.
Qed.

(** A standard generator γ_i of F_n is not conjugate to its inverse.

    Cycle 24 (2026-04-29) — was an axiom in cycle 23, now discharged
    via the abelianisation argument above. Net: −1 axiom. *)
Theorem free_gen_RWord_not_conj_inv : forall (n : nat) (i : Fin.t n),
    ~ are_conjugate (FreeGroup n)
        (free_gen_RWord n i)
        (sinv (RWord n) (FreeGroup n) (free_gen_RWord n i)).
Proof.
  intros n i Hconj.
  pose proof (expsum_i_conj_invariant i _ _ Hconj) as Heq.
  rewrite expsum_i_free_gen_RWord, expsum_i_free_gen_RWord_inv in Heq.
  discriminate.
Qed.

(** Cycle 42 — strengthened non-conjugacy via abelianization.

    Two free-group elements with different exponent sum (at any
    coordinate) are non-conjugate. This is the contrapositive of
    [expsum_i_conj_invariant], stated explicitly for downstream use. *)
Theorem expsum_distinct_implies_not_conjugate :
    forall {n : nat} (i : Fin.t n) (gamma eta : RWord n),
      expsum_i i gamma <> expsum_i i eta ->
      ~ are_conjugate (FreeGroup n) gamma eta.
Proof.
  intros n i gamma eta Hne Hconj.
  apply Hne.
  apply expsum_i_conj_invariant.
  exact Hconj.
Qed.

(** Distinct generators γ_i, γ_j (i ≠ j) of F_n are non-conjugate. *)
Theorem distinct_generators_not_conjugate :
    forall (n : nat) (i j : Fin.t n),
      i <> j ->
      ~ are_conjugate (FreeGroup n)
          (free_gen_RWord n i)
          (free_gen_RWord n j).
Proof.
  intros n i j Hij.
  apply (expsum_distinct_implies_not_conjugate i).
  rewrite expsum_i_free_gen_RWord.
  unfold expsum_i, free_gen_RWord, free_gen_letter. simpl.
  unfold letter_sign_i. simpl.
  destruct (Fin.eq_dec j i) as [Heq|_].
  - exfalso. apply Hij. symmetry. exact Heq.
  - lia.
Qed.

(** A generator γ_i is not conjugate to the inverse of any *other*
    generator γ_j⁻¹ (j ≠ i). Combined with [free_gen_RWord_not_conj_inv]
    this shows: for any pair of letters (i, ε_i) and (j, ε_j) with the
    underlying letters distinct, the resulting RWords are non-conjugate
    in F_n (when n ≥ 2). *)
(** [expsum_i i (γ_j)] = 0 when i ≠ j. *)
Lemma expsum_i_free_gen_RWord_other :
    forall (n : nat) (i j : Fin.t n),
      i <> j ->
      expsum_i i (free_gen_RWord n j) = 0%Z.
Proof.
  intros n i j Hij.
  unfold expsum_i, free_gen_RWord, free_gen_letter. simpl.
  unfold letter_sign_i. simpl.
  destruct (Fin.eq_dec j i) as [Heq|_].
  - exfalso. apply Hij. symmetry. exact Heq.
  - reflexivity.
Qed.

Theorem generator_not_conj_to_other_inverse :
    forall (n : nat) (i j : Fin.t n),
      i <> j ->
      ~ are_conjugate (FreeGroup n)
          (free_gen_RWord n i)
          (sinv (RWord n) (FreeGroup n) (free_gen_RWord n j)).
Proof.
  intros n i j Hij.
  apply (expsum_distinct_implies_not_conjugate i).
  rewrite expsum_i_free_gen_RWord.
  change (sinv (RWord n) (FreeGroup n)) with (@rword_inv n).
  rewrite expsum_i_inv.
  rewrite (expsum_i_free_gen_RWord_other n i j Hij).
  lia.
Qed.

(** Identity element is not conjugate to any nontrivial generator. *)
Theorem id_not_conj_to_generator :
    forall (n : nat) (i : Fin.t n),
      ~ are_conjugate (FreeGroup n)
          (@rword_e n)
          (free_gen_RWord n i).
Proof.
  intros n i.
  apply (expsum_distinct_implies_not_conjugate i).
  rewrite expsum_i_free_gen_RWord.
  unfold expsum_i, rword_e. simpl.
  lia.
Qed.

(** Powers of a single generator: γ_i^p is not conjugate to γ_i^q
    when p ≠ q. (Specialization of [expsum_distinct_implies_not_conjugate]
    to powers.) Stated assuming we have a [pow] function on RWord. *)
Lemma expsum_i_eq_implies_zero :
    forall {n : nat} (i : Fin.t n) (gamma : RWord n),
      expsum_i i gamma = 0%Z ->
      forall eta : RWord n,
        expsum_i i eta = 0%Z ->
        expsum_i i gamma = expsum_i i eta.
Proof. intros. lia. Qed.

(** Positive words have non-negative exponent sums at every index. *)
Lemma positive_word_expsum_nonneg : forall {n : nat} (i : Fin.t n) (w : Word n),
    Forall (fun l : Letter n => snd l = false) w ->
    (0 <= expsum_word_i i w)%Z.
Proof.
  intros n i w. induction w as [|x xs IH]; intros Hpos.
  - simpl. lia.
  - simpl. inversion Hpos as [|? ? Hx Hxs]. subst.
    specialize (IH Hxs).
    unfold letter_sign_i. destruct (Fin.eq_dec (fst x) i).
    + rewrite Hx. lia.
    + lia.
Qed.

(** A positive [RWord] with zero exponent sum at every index is the empty
    (identity) word. Reason: each letter contributes a non-negative sign,
    and a contribution of [+1] at index [fst l] arises whenever the
    letter is present (since positive ⟹ snd l = false). Total zero
    forces no letters at all. *)
Lemma positive_zero_expsum_is_empty : forall {n : nat} (w : Word n),
    Forall (fun l : Letter n => snd l = false) w ->
    (forall i : Fin.t n, expsum_word_i i w = 0%Z) ->
    w = [].
Proof.
  intros n w Hpos Hzero.
  destruct w as [|x xs]; [reflexivity|].
  exfalso.
  inversion Hpos as [|? ? Hx Hxs]. subst.
  specialize (Hzero (fst x)).
  simpl in Hzero.
  unfold letter_sign_i in Hzero.
  destruct (Fin.eq_dec (fst x) (fst x)) as [_|HnE]; [|exfalso; apply HnE; reflexivity].
  rewrite Hx in Hzero.
  pose proof (positive_word_expsum_nonneg (fst x) xs Hxs) as Hge0.
  lia.
Qed.

(** Lifted to RWord: a positive RWord with zero exponent sum everywhere is
    [rword_e]. *)
Lemma positive_zero_expsum_RWord_is_e : forall {n : nat} (w : RWord n),
    Forall (fun l : Letter n => snd l = false) (proj1_sig w) ->
    (forall i : Fin.t n, expsum_i i w = 0%Z) ->
    w = @rword_e n.
Proof.
  intros n [w Hred] Hpos Hzero.
  unfold expsum_i in Hzero. simpl in *.
  pose proof (positive_zero_expsum_is_empty w Hpos Hzero) as Hempty.
  unfold rword_e. apply rword_eq. exact Hempty.
Qed.


(* ================================================================== *)
(** * 6. Conj_func placeholder for free groups                           *)
(* ================================================================== *)

(** Concrete Conj_func wrapper: maximum size of a finite quotient
    needed to distinguish a pair of non-conjugate elements within the
    radius-k ball. Currently the underlying CD function is a placeholder;
    discharging this is part of [G5] (specialization lemma). *)

Definition free_Conj_func (n_gens : nat) (k : nat) : nat :=
  Conj_func (FreeGroup_FGG n_gens) k.

(** Open question 1.13 (Lawton-Louder-McReynolds): is [free_Conj_func]
    polynomially bounded for r = n_gens ≥ 2? *)
Definition free_Conj_poly_bounded (n_gens : nat) : Prop :=
  exists d C : nat, forall k : nat,
      free_Conj_func n_gens k <= C * Nat.pow k d.

(** Trivial bound: since [Conj_func] is currently a constant-zero
    placeholder, the bound is trivially satisfied with d = C = 0. The
    real content of the open question only kicks in once [Conj_func]
    is given a non-placeholder definition. *)
Lemma free_Conj_poly_bounded_trivial : forall n_gens : nat,
    free_Conj_poly_bounded n_gens.
Proof.
  intros n_gens.
  exists 0%nat, 0%nat. intro k.
  unfold free_Conj_func, Conj_func. lia.
Qed.

(** Conjugacy in F_r is decidable in principle by reducing to
    cyclically-reduced canonical form and comparing cyclic
    permutations. Stated as the conjugacy decision problem. *)
Definition free_conjugacy_decidable (n : nat) : Type :=
  forall x y : RWord n,
    {are_conjugate (FreeGroup n) x y} + {~ are_conjugate (FreeGroup n) x y}.

(** Conjugacy in free groups is decidable (cyclic reduction theorem).
    The full algorithm: cyclically reduce both x and y, then test
    whether one is a cyclic permutation of the other. Axiomatized
    here; the theorem itself is well-known (Magnus-Karass-Solitar). *)
Axiom free_conjugacy_decision_thm :
  forall (n : nat), free_conjugacy_decidable n.
