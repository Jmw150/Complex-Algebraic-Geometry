(** * DecisionProblems/InducedRep.v

    Induced representations and the Frobenius trace formula.

    Addresses [G7] from OpenProblems.v.

    Setup: H ≤ G a finite-index subgroup with explicit transversal
    {t_1, ..., t_k}. Given ρ : H → SL(d, F), define
        Ind^G_H ρ : G → SL(k·d, F)
    as the block representation acting on
        F^{k·d} = ⊕_{i=1}^{k} F^d
    where g ∈ G permutes/twists the blocks according to the action
    g · t_i = t_{σ(i)} · h_i with h_i ∈ H.

    Frobenius formula: Tr(Ind ρ)(g) = Σ_{i: g·t_i ∈ t_i·H} Tr(ρ)(h_i),
    where the sum is over fixed points of the coset permutation.

    Used in the paper (Theorem 1.6) to lift representations from a
    finite-index subgroup back to the full group while keeping trace
    information. *)

From CAG Require Import Galois.Field.
From CAG Require Import Group.
From CAG Require Import DecisionProblems.TraceProperties.
From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* ================================================================== *)
(** * 1. Finite-index subgroup data                                     *)
(* ================================================================== *)

(** A finite-index subgroup H ≤ G with chosen transversal.

    [fis_pred_dec] (added Round 16, Task F): H membership is decidable.
    Required to discharge the [coset_sigma]/[coset_cocycle] axioms via
    concrete list-search.

    [fis_trans_unique] (added Round 16, Task F): distinct transversal
    positions yield distinct cosets. Required for the uniqueness side of
    [coset_sigma_id] / [coset_sigma_compose]. *)
Record FiniteIndexSubgroup {G : Type} (sg : StrictGroup G) : Type :=
  mkFIS
  {
    fis_pred  : G -> Prop;             (* H as a predicate *)
    fis_index : nat;                   (* [G : H] *)
    fis_trans : list G;                (* transversal {t_1, ..., t_k} *)
    fis_trans_len : length fis_trans = fis_index;
    fis_trans_dec : forall g : G, exists (i : nat) (h : G),
        i < fis_index /\ fis_pred h /\
        nth_error fis_trans i = Some (smul G sg g (sinv G sg h));
    fis_id_in_H : fis_pred (se G sg);
    fis_mul_closed : forall a b, fis_pred a -> fis_pred b ->
                                fis_pred (smul G sg a b);
    fis_inv_closed : forall a, fis_pred a -> fis_pred (sinv G sg a);
    fis_pred_dec : forall g : G, {fis_pred g} + {~ fis_pred g};
    fis_trans_unique :
      forall (i j : nat) (t_i t_j : G),
        i < fis_index -> j < fis_index ->
        nth_error fis_trans i = Some t_i ->
        nth_error fis_trans j = Some t_j ->
        fis_pred (smul G sg (sinv G sg t_j) t_i) ->
        i = j;
  }.

Arguments fis_pred  {G sg} _.
Arguments fis_index {G sg} _.
Arguments fis_trans {G sg} _.
Arguments fis_trans_len {G sg} _.
Arguments fis_trans_dec {G sg} _.
Arguments fis_id_in_H {G sg} _.
Arguments fis_mul_closed {G sg} _.
Arguments fis_inv_closed {G sg} _.
Arguments fis_pred_dec {G sg} _.
Arguments fis_trans_unique {G sg} _.

(* ================================================================== *)
(** * 2. Coset action of g on transversal                              *)
(* ================================================================== *)

(** For g ∈ G and i ∈ {0,...,k-1}, there is a unique pair
    (σ(i), h_i) with σ(i) ∈ {0,...,k-1} and h_i ∈ H such that
    g · t_i = t_{σ(i)} · h_i.

    Round 16 (Task F): With the new [fis_pred_dec] and
    [fis_trans_unique] fields on [FiniteIndexSubgroup], σ and h are now
    *defined* by linear search over the transversal — no axioms.

    Source: Curtis–Reiner, "Methods of representation theory" Vol. I §10
    (induced representations and the Frobenius formula).
    Serre, "Linear representations of finite groups" §7.1.

    ✅ COMPLIANCE: All five originally axiomatized properties
    ([coset_sigma_bound], [coset_cocycle_in_H], [coset_action_eq],
    [coset_sigma_id], [coset_sigma_compose]) are now closed Lemmas. *)

(** ** Concrete construction (Round 16, Task F)

    Given [fis_pred_dec], we can search the transversal linearly: for
    [g · t_i], find the unique [j < fis_index] such that
    [(t_j)⁻¹ · g · t_i ∈ H]. Existence follows from [fis_trans_dec];
    uniqueness from [fis_trans_unique]. *)

Section CosetSigmaImpl.
  Context {G : Type} {sg : StrictGroup G}.

  (** Linear search through the indices [0, 1, ..., k-1], returning the
      first [j] such that [(t_j)⁻¹ · y ∈ H], or [k] (out of range) if
      none. The auxiliary parameter [k] is the remaining count;
      [start = fis_index - k] is the starting index. *)
  Fixpoint find_coset_aux (FIS : FiniteIndexSubgroup sg) (y : G)
                          (start k : nat) : nat :=
    match k with
    | 0 => fis_index FIS  (* sentinel: not found *)
    | S k' =>
        match nth_error (fis_trans FIS) start with
        | Some t =>
            if fis_pred_dec FIS (smul G sg (sinv G sg t) y)
            then start
            else find_coset_aux FIS y (S start) k'
        | None => find_coset_aux FIS y (S start) k'  (* shouldn't happen *)
        end
    end.

  Definition find_coset (FIS : FiniteIndexSubgroup sg) (y : G) : nat :=
    find_coset_aux FIS y 0 (fis_index FIS).

  (** Bound: [find_coset_aux] returns either an index in [start, start+k)
      or [fis_index FIS]. *)
  Lemma find_coset_aux_bound :
    forall (FIS : FiniteIndexSubgroup sg) (y : G) (start k : nat),
      let r := find_coset_aux FIS y start k in
      r = fis_index FIS \/ (start <= r < start + k).
  Proof.
    intros FIS y start k. revert start.
    induction k as [|k IH]; intro start; simpl.
    - left; reflexivity.
    - destruct (nth_error (fis_trans FIS) start) as [t|] eqn:Hnt.
      + destruct (fis_pred_dec FIS (smul G sg (sinv G sg t) y)) as [Hin|Hni].
        * right. split; [reflexivity|lia].
        * specialize (IH (S start)).
          destruct IH as [Hr | Hr].
          -- left; exact Hr.
          -- right; lia.
      + specialize (IH (S start)).
        destruct IH as [Hr | Hr].
        * left; exact Hr.
        * right; lia.
  Qed.

  (** If returned index < fis_index, then it satisfies the membership. *)
  Lemma find_coset_aux_correct :
    forall (FIS : FiniteIndexSubgroup sg) (y : G) (start k : nat),
      let r := find_coset_aux FIS y start k in
      r < fis_index FIS ->
      exists t_r,
        nth_error (fis_trans FIS) r = Some t_r /\
        fis_pred FIS (smul G sg (sinv G sg t_r) y).
  Proof.
    intros FIS y start k. revert start.
    induction k as [|k IH]; intro start; simpl.
    - intro Hlt; lia.
    - destruct (nth_error (fis_trans FIS) start) as [t|] eqn:Hnt.
      + destruct (fis_pred_dec FIS (smul G sg (sinv G sg t) y)) as [Hin|Hni].
        * intros _. exists t. split; [exact Hnt | exact Hin].
        * apply IH.
      + apply IH.
  Qed.

  (** The proper search [find_coset] always finds a valid index because
      [fis_trans_dec] guarantees existence. *)
  Lemma find_coset_lt :
    forall (FIS : FiniteIndexSubgroup sg) (y : G),
      find_coset FIS y < fis_index FIS.
  Proof.
    intros FIS y.
    unfold find_coset.
    (* Suppose for contradiction find_coset_aux returns fis_index FIS.
       Then no j satisfies (t_j⁻¹ · y) ∈ H. But fis_trans_dec gives one. *)
    destruct (find_coset_aux_bound FIS y 0 (fis_index FIS)) as [Heq | [_ Hb]];
      [|lia].
    exfalso.
    (* fis_trans_dec applied to y yields some i, h with t_i = y · h⁻¹,
       i.e. h = t_i⁻¹ · y · ? — let's compute carefully. *)
    pose proof (fis_trans_dec FIS y) as [i [h [Hi [Hh Hnt]]]].
    (* From t_i = y · h⁻¹, we get t_i⁻¹ · y = h, so t_i⁻¹ · y ∈ H. *)
    assert (Hmem : fis_pred FIS (smul G sg (sinv G sg
              (smul G sg y (sinv G sg h))) y)).
    { (* sinv (y · h⁻¹) = (h⁻¹)⁻¹ · y⁻¹ = h · y⁻¹.
         So sinv (y · h⁻¹) · y = h · y⁻¹ · y = h ∈ H. *)
      pose proof (sinv_left G sg y) as Hsl. (* y⁻¹·y = e *)
      assert (Hexp : smul G sg (sinv G sg (smul G sg y (sinv G sg h))) y
                   = h).
      { (* Use unique_inverse-style reasoning. We show that
           (sinv (y · h⁻¹)) = h · y⁻¹ by checking it's a right-inverse
           of (y · h⁻¹). *)
        assert (Hinv : smul G sg (smul G sg y (sinv G sg h))
                         (smul G sg h (sinv G sg y)) = se G sg).
        { rewrite <- (sassoc G sg y (sinv G sg h)
                       (smul G sg h (sinv G sg y))).
          rewrite (sassoc G sg (sinv G sg h) h (sinv G sg y)).
          rewrite (sinv_left G sg h).
          rewrite (sid_left G sg (sinv G sg y)).
          apply sinv_right. }
        (* By uniqueness of inverse:
           sinv (y · h⁻¹) = h · y⁻¹. *)
        assert (Hsinv :
          sinv G sg (smul G sg y (sinv G sg h)) = smul G sg h (sinv G sg y)).
        { (* From x · y' = e and x · sinv x = e, we get y' = sinv x. *)
          assert (Hsr : smul G sg (smul G sg y (sinv G sg h))
                          (sinv G sg (smul G sg y (sinv G sg h))) = se G sg)
            by apply sinv_right.
          (* Multiply both sides of Hinv from the left by sinv (y · h⁻¹). *)
          assert (HL : smul G sg (sinv G sg (smul G sg y (sinv G sg h)))
                         (smul G sg (smul G sg y (sinv G sg h))
                            (smul G sg h (sinv G sg y))) =
                       smul G sg (sinv G sg (smul G sg y (sinv G sg h)))
                         (se G sg)).
          { rewrite Hinv. reflexivity. }
          rewrite (sassoc G sg _ _ _) in HL.
          rewrite (sinv_left G sg) in HL.
          rewrite (sid_left G sg) in HL.
          rewrite (sid_right G sg) in HL.
          symmetry. exact HL. }
        rewrite Hsinv.
        rewrite <- (sassoc G sg h (sinv G sg y) y).
        rewrite (sinv_left G sg y).
        apply (sid_right G sg). }
      rewrite Hexp. exact Hh. }
    (* So index i satisfies the membership condition. find_coset_aux
       starting from 0 with k = fis_index would find a valid index.
       We prove a stronger lemma about find_coset_aux at any (start, k). *)
    assert (Hsearch : forall start k,
      find_coset_aux FIS y start k = fis_index FIS ->
      forall j t,
        start <= j < start + k ->
        nth_error (fis_trans FIS) j = Some t ->
        ~ fis_pred FIS (smul G sg (sinv G sg t) y)).
    { clear. intros start k. revert start.
      induction k as [|k IHk]; intros start Hr j t Hbnd Hntj.
      - lia.
      - simpl in Hr.
        destruct (nth_error (fis_trans FIS) start) as [ts|] eqn:Hns.
        + destruct (fis_pred_dec FIS (smul G sg (sinv G sg ts) y))
            as [Hin|Hni].
          * exfalso.
            (* If the test passes, the result IS start, which must equal
               fis_index FIS by Hr. So start >= fis_index FIS. But j >= start
               and nth_error fis_trans j = Some t requires j < fis_index FIS. *)
            assert (Hstart : start = fis_index FIS) by exact Hr.
            assert (Hjlt : j < length (fis_trans FIS)).
            { apply nth_error_Some. rewrite Hntj. discriminate. }
            rewrite fis_trans_len in Hjlt. lia.
          * destruct (Nat.eq_dec j start) as [Heqj | Hnej].
            -- subst j. rewrite Hns in Hntj. injection Hntj as <-. exact Hni.
            -- apply (IHk (S start) Hr j t); [lia | exact Hntj].
        + (* nth_error fis_trans start = None, so start >= fis_index *)
          destruct (Nat.eq_dec j start) as [Heqj | Hnej].
          * subst j. rewrite Hns in Hntj. discriminate.
          * apply (IHk (S start) Hr j t); [lia | exact Hntj]. }
    apply (Hsearch 0 (fis_index FIS) Heq i _ ltac:(lia) Hnt). exact Hmem.
  Qed.

  (** find_coset gives the witness with the required membership. *)
  Lemma find_coset_correct :
    forall (FIS : FiniteIndexSubgroup sg) (y : G),
    exists t_r,
      nth_error (fis_trans FIS) (find_coset FIS y) = Some t_r /\
      fis_pred FIS (smul G sg (sinv G sg t_r) y).
  Proof.
    intros FIS y.
    pose proof (find_coset_lt FIS y) as Hlt.
    unfold find_coset in Hlt |- *.
    apply find_coset_aux_correct. exact Hlt.
  Qed.

  (** find_coset is unique: any j satisfying the condition equals it. *)
  Lemma find_coset_unique :
    forall (FIS : FiniteIndexSubgroup sg) (y : G) (j : nat) (t_j : G),
      j < fis_index FIS ->
      nth_error (fis_trans FIS) j = Some t_j ->
      fis_pred FIS (smul G sg (sinv G sg t_j) y) ->
      find_coset FIS y = j.
  Proof.
    intros FIS y j t_j Hj Hntj Hmem.
    pose proof (find_coset_correct FIS y) as [t_r [Hntr Hmemr]].
    pose proof (find_coset_lt FIS y) as Hrlt.
    set (r := find_coset FIS y) in *.
    (* Both r and j satisfy: t_x⁻¹ · y ∈ H. We use fis_trans_unique. *)
    (* Need: fis_pred (smul (sinv t_j) t_r). *)
    (* We have: sinv t_r · y ∈ H and sinv t_j · y ∈ H.
       So (sinv t_j · y) · (sinv t_r · y)⁻¹ ∈ H.
       Compute: (sinv t_j · y) · (sinv (sinv t_r · y))
              = sinv t_j · y · y⁻¹ · t_r
              = sinv t_j · t_r. *)
    assert (Hcomb : fis_pred FIS
              (smul G sg (smul G sg (sinv G sg t_j) y)
                         (sinv G sg (smul G sg (sinv G sg t_r) y)))).
    { apply fis_mul_closed.
      - exact Hmem.
      - apply fis_inv_closed. exact Hmemr. }
    (* Simplify the expression to sinv t_j · t_r. *)
    assert (Hsimp : smul G sg (smul G sg (sinv G sg t_j) y)
                              (sinv G sg (smul G sg (sinv G sg t_r) y))
                  = smul G sg (sinv G sg t_j) t_r).
    { (* sinv (sinv t_r · y) = y⁻¹ · (sinv t_r)⁻¹ = y⁻¹ · t_r ?
         Actually (sinv t_r)⁻¹ = t_r by double_inverse — but we don't have
         that directly. We use the general identity (a·b)⁻¹ = b⁻¹·a⁻¹ via
         uniqueness of inverses. We'll do it by hand. *)
      (* We show: sinv (smul (sinv t_r) y) · (sinv t_r · y) = se *)
      set (b := sinv G sg (smul G sg (sinv G sg t_r) y)).
      (* We compute (sinv t_j · y) · b. We want it = sinv t_j · t_r.
         Equivalently y · b = t_r.
         b is the inverse of (sinv t_r · y). So (sinv t_r · y) · b = se,
         i.e., b = sinv (sinv t_r · y).
         We also have: t_r · ((sinv t_r) · y) = (t_r · sinv t_r) · y = e · y = y.
         So sinv ((sinv t_r) · y) · y⁻¹ · t_r⁻¹·t_r = ... too tangled.
         Approach: show t_r is the inverse of (sinv t_r · y) · y⁻¹, i.e.,
         y · b = t_r by direct computation. *)
      assert (Hyb : smul G sg y b = t_r).
      { (* We show: smul ((sinv t_r) · y) (smul y b · ?). Easier:
           use that y · b · ((sinv t_r) · y) = y · (b · (sinv t_r · y))
                  = y · se = y. So if z := y · b, then z · (sinv t_r · y) = y.
           Multiplying on the right by sinv y: z · sinv t_r = e, so z is the
           inverse of sinv t_r — but we don't have unique-inverse =>
           z = (sinv t_r)⁻¹ by uniqueness. We use unique_inverse from Group.v. *)
        unfold b.
        (* z = y · sinv (sinv t_r · y). Compute z · sinv t_r = ? *)
        (* Step 1: z · (sinv t_r · y) = y · sinv (sinv t_r · y) · (sinv t_r · y)
                                      = y · se = y. *)
        assert (Hz1 :
          smul G sg (smul G sg y (sinv G sg (smul G sg (sinv G sg t_r) y)))
                    (smul G sg (sinv G sg t_r) y) = y).
        { rewrite <- (sassoc G sg y _ _).
          rewrite (sinv_left G sg (smul G sg (sinv G sg t_r) y)).
          apply sid_right. }
        (* Step 2: y · sinv (sinv t_r · y) is the inverse of (sinv t_r) on
           the right: (y · sinv (sinv t_r · y)) · (sinv t_r) · y * ... hmm. *)
        (* Multiply Hz1 on the right by sinv y. *)
        assert (Hz2 :
          smul G sg (smul G sg (smul G sg y
                       (sinv G sg (smul G sg (sinv G sg t_r) y)))
                       (smul G sg (sinv G sg t_r) y)) (sinv G sg y) =
          smul G sg y (sinv G sg y)).
        { rewrite Hz1. reflexivity. }
        rewrite (sinv_right G sg y) in Hz2.
        (* RHS = se. LHS regroup: ... · (sinv t_r · y · sinv y)
                                = ... · (sinv t_r · se) = ... · sinv t_r. *)
        rewrite <- (sassoc G sg
          (smul G sg y (sinv G sg (smul G sg (sinv G sg t_r) y)))
          (smul G sg (sinv G sg t_r) y) (sinv G sg y)) in Hz2.
        rewrite <- (sassoc G sg (sinv G sg t_r) y (sinv G sg y)) in Hz2.
        rewrite (sinv_right G sg y) in Hz2.
        rewrite (sid_right G sg) in Hz2.
        (* Now Hz2 : (y · sinv (sinv t_r · y)) · sinv t_r = se *)
        (* And we know t_r · sinv t_r = se. By uniqueness of left-inverse. *)
        (* From x · sinv t_r = se and t_r · sinv t_r = se. We need x = t_r.
           Multiply Hz2 on right by t_r:
             (x · sinv t_r) · t_r = se · t_r = t_r
             x · (sinv t_r · t_r) = t_r
             x · se = t_r => x = t_r. *)
        assert (Hgoal :
          smul G sg (smul G sg
            (smul G sg y (sinv G sg (smul G sg (sinv G sg t_r) y)))
            (sinv G sg t_r)) t_r =
          smul G sg (se G sg) t_r).
        { rewrite Hz2. reflexivity. }
        rewrite <- (sassoc G sg _ (sinv G sg t_r) t_r) in Hgoal.
        rewrite (sinv_left G sg t_r) in Hgoal.
        rewrite (sid_right G sg) in Hgoal.
        rewrite (sid_left G sg) in Hgoal.
        exact Hgoal. }
      (* Now (sinv t_j · y) · b = sinv t_j · (y · b) = sinv t_j · t_r. *)
      rewrite <- (sassoc G sg (sinv G sg t_j) y b).
      rewrite Hyb. reflexivity. }
    rewrite Hsimp in Hcomb.
    (* Now Hcomb: fis_pred (sinv t_j · t_r). Apply fis_trans_unique. *)
    (* fis_trans_unique signature: i, j, t_i, t_j with t_j⁻¹ · t_i ∈ H => i = j *)
    apply (fis_trans_unique FIS r j t_r t_j Hrlt Hj Hntr Hntj Hcomb).
  Qed.

End CosetSigmaImpl.

(** Coset permutation σ: G → (Fin_k → Fin_k). Takes explicit FIS. *)
Definition coset_sigma {G : Type} {sg : StrictGroup G}
                       (FIS : FiniteIndexSubgroup sg) (g : G) (i : nat) : nat :=
  match nth_error (fis_trans FIS) i with
  | Some t_i => find_coset FIS (smul G sg g t_i)
  | None     => 0  (* out-of-range default *)
  end.

(** Cocycle h: G × Fin → H. Defined as t_{σ(i)}⁻¹ · g · t_i. *)
Definition coset_cocycle {G : Type} {sg : StrictGroup G}
                         (FIS : FiniteIndexSubgroup sg) (g : G) (i : nat) : G :=
  match nth_error (fis_trans FIS) i with
  | Some t_i =>
      match nth_error (fis_trans FIS) (coset_sigma FIS g i) with
      | Some t_si =>
          smul G sg (sinv G sg t_si) (smul G sg g t_i)
      | None => se G sg
      end
  | None => se G sg
  end.

(** Keep [coset_sigma] / [coset_cocycle] opaque to [simpl] / [cbn] so that
    downstream lemmas don't accidentally unfold the search machinery. *)
Arguments coset_sigma : simpl never.
Arguments coset_cocycle : simpl never.

Lemma coset_sigma_bound :
  forall {G : Type} {sg : StrictGroup G} (FIS : FiniteIndexSubgroup sg)
         (g : G) (i : nat),
    i < fis_index FIS -> coset_sigma FIS g i < fis_index FIS.
Proof.
  intros G sg FIS g i Hi.
  unfold coset_sigma.
  destruct (nth_error (fis_trans FIS) i) as [t_i|] eqn:Hnt.
  - apply find_coset_lt.
  - apply nth_error_None in Hnt.
    rewrite fis_trans_len in Hnt. lia.
Qed.

Lemma coset_cocycle_in_H :
  forall {G : Type} {sg : StrictGroup G} (FIS : FiniteIndexSubgroup sg)
         (g : G) (i : nat),
    fis_pred FIS (coset_cocycle FIS g i).
Proof.
  intros G sg FIS g i.
  unfold coset_cocycle.
  destruct (nth_error (fis_trans FIS) i) as [t_i|] eqn:Hnti;
    [|apply fis_id_in_H].
  unfold coset_sigma. rewrite Hnti.
  pose proof (find_coset_correct FIS (smul G sg g t_i))
    as [t_r [Hntr Hmemr]].
  rewrite Hntr.
  exact Hmemr.
Qed.

(** Defining equation: g · t_i = t_{σ(i)} · h_i. *)
Lemma coset_action_eq :
  forall {G : Type} {sg : StrictGroup G} (FIS : FiniteIndexSubgroup sg)
         (g : G) (i : nat) (t_i t_sigma_i : G),
    i < fis_index FIS ->
    nth_error (fis_trans FIS) i = Some t_i ->
    nth_error (fis_trans FIS) (coset_sigma FIS g i) = Some t_sigma_i ->
    smul G sg g t_i =
    smul G sg t_sigma_i (coset_cocycle FIS g i).
Proof.
  intros G sg FIS g i t_i t_si Hi Hnti Hntsi.
  unfold coset_cocycle. rewrite Hnti. rewrite Hntsi.
  (* Goal: g · t_i = t_si · (sinv t_si · g · t_i) *)
  rewrite (sassoc G sg t_si (sinv G sg t_si) (smul G sg g t_i)).
  rewrite (sinv_right G sg t_si).
  rewrite (sid_left G sg).
  reflexivity.
Qed.

Lemma coset_sigma_id :
  forall {G : Type} {sg : StrictGroup G} (FIS : FiniteIndexSubgroup sg)
         (i : nat),
    i < fis_index FIS ->
    coset_sigma FIS (se G sg) i = i.
Proof.
  intros G sg FIS i Hi.
  unfold coset_sigma.
  destruct (nth_error (fis_trans FIS) i) as [t_i|] eqn:Hnti.
  - (* find_coset FIS (e · t_i) = find_coset FIS t_i.
       We claim it equals i, by uniqueness with witness j = i, t_j = t_i.
       Need: fis_pred (sinv t_i · (e · t_i)). Simplify: sinv t_i · t_i = e. *)
    apply find_coset_unique with (t_j := t_i); [exact Hi | exact Hnti |].
    rewrite (sid_left G sg t_i).
    rewrite (sinv_left G sg t_i).
    apply fis_id_in_H.
  - apply nth_error_None in Hnti.
    rewrite fis_trans_len in Hnti. lia.
Qed.

Lemma coset_sigma_compose :
  forall {G : Type} {sg : StrictGroup G} (FIS : FiniteIndexSubgroup sg)
         (g h : G) (i : nat),
    i < fis_index FIS ->
    coset_sigma FIS (smul G sg g h) i =
    coset_sigma FIS g (coset_sigma FIS h i).
Proof.
  intros G sg FIS g h i Hi.
  (* Let j := coset_sigma FIS h i, k := coset_sigma FIS g j.
     We need: coset_sigma FIS (g·h) i = k.
     By uniqueness, suffices: ∃ t_k with nth_error fis_trans k = Some t_k
     and fis_pred (sinv t_k · (g·h) · t_i). *)
  (* From the definitions: there exist t_i, t_j, t_k with
       t_i = nth fis_trans i,
       t_j = nth fis_trans j (= nth fis_trans (coset_sigma FIS h i)),
       t_k = nth fis_trans k (= nth fis_trans (coset_sigma FIS g j)).
     And:
       sinv t_j · (h · t_i) ∈ H  (i.e., h · t_i = t_j · h_i)
       sinv t_k · (g · t_j) ∈ H  (i.e., g · t_j = t_k · h'_j)
     Combining: g · h · t_i = g · (t_j · h_i) = t_k · h'_j · h_i ∈ t_k · H.
  *)
  pose proof Hi as Hi'.
  apply coset_sigma_bound with (g := h) in Hi'.
  set (j := coset_sigma FIS h i) in *.
  pose proof Hi' as Hj'.
  apply coset_sigma_bound with (g := g) in Hj'.
  set (k := coset_sigma FIS g j) in *.
  (* Get t_i. *)
  destruct (nth_error (fis_trans FIS) i) as [t_i|] eqn:Hnti; cycle 1.
  { apply nth_error_None in Hnti.
    rewrite fis_trans_len in Hnti. lia. }
  destruct (nth_error (fis_trans FIS) j) as [t_j|] eqn:Hntj; cycle 1.
  { apply nth_error_None in Hntj.
    rewrite fis_trans_len in Hntj. lia. }
  destruct (nth_error (fis_trans FIS) k) as [t_k|] eqn:Hntk; cycle 1.
  { apply nth_error_None in Hntk.
    rewrite fis_trans_len in Hntk. lia. }
  (* Get the membership facts. *)
  pose proof (coset_cocycle_in_H FIS h i) as Hmem_h.
  pose proof (coset_cocycle_in_H FIS g j) as Hmem_g.
  unfold coset_cocycle in Hmem_h.
  rewrite Hnti in Hmem_h.
  fold j in Hmem_h.
  rewrite Hntj in Hmem_h.
  unfold coset_cocycle in Hmem_g.
  rewrite Hntj in Hmem_g.
  fold k in Hmem_g.
  rewrite Hntk in Hmem_g.
  (* Hmem_h : fis_pred (sinv t_j · (h · t_i))
     Hmem_g : fis_pred (sinv t_k · (g · t_j)) *)
  (* Apply find_coset_unique with j := k. Need:
       fis_pred (sinv t_k · ((g·h) · t_i)) *)
  unfold coset_sigma. rewrite Hnti.
  apply find_coset_unique with (t_j := t_k); [exact Hj' | exact Hntk |].
  (* Goal: fis_pred (sinv t_k · ((g·h) · t_i)) *)
  (* We construct it as (sinv t_k · g · t_j) · (sinv t_j · h · t_i). *)
  assert (Hprod :
    smul G sg (sinv G sg t_k) (smul G sg (smul G sg g h) t_i) =
    smul G sg
      (smul G sg (sinv G sg t_k) (smul G sg g t_j))
      (smul G sg (sinv G sg t_j) (smul G sg h t_i))).
  { (* Manipulate RHS to equal LHS by associativity + sinv_right.
       RHS = (sinv t_k · (g · t_j)) · (sinv t_j · (h · t_i))
           = sinv t_k · ((g · t_j) · (sinv t_j · (h · t_i)))   [sassoc <-]
           = sinv t_k · (((g · t_j) · sinv t_j) · (h · t_i))    [sassoc ->]
           = sinv t_k · ((g · (t_j · sinv t_j)) · (h · t_i))    [sassoc <-]
           = sinv t_k · ((g · se) · (h · t_i))                   [sinv_right]
           = sinv t_k · (g · (h · t_i))                          [sid_right]
           = sinv t_k · ((g · h) · t_i)                          [sassoc ->]
           = LHS. *)
    symmetry.
    rewrite <- (sassoc G sg (sinv G sg t_k) (smul G sg g t_j)
                       (smul G sg (sinv G sg t_j) (smul G sg h t_i))).
    rewrite (sassoc G sg (smul G sg g t_j) (sinv G sg t_j)
                    (smul G sg h t_i)).
    rewrite <- (sassoc G sg g t_j (sinv G sg t_j)).
    rewrite (sinv_right G sg t_j).
    rewrite (sid_right G sg g).
    rewrite (sassoc G sg g h t_i).
    reflexivity. }
  rewrite Hprod.
  apply fis_mul_closed; [exact Hmem_g | exact Hmem_h].
Qed.

(* ================================================================== *)
(** * 3. Induced trace via Frobenius formula                            *)
(* ================================================================== *)

(** Given ρ : H → MG (some matrix group), define the induced trace
    function Ind ρ : G → F by the Frobenius formula:
        (Ind ρ)(g) = Σ_{i: σ(i) = i} mg_trace(ρ(h_i))

    Where the sum is over fixed points of the coset permutation σ. *)

Section InducedTrace.
  Context {G F : Type} (sg : StrictGroup G) (FIS : FiniteIndexSubgroup sg)
          (MG : MatrixGroup F)
          (rho_H : G -> mg_carrier MG)  (* ρ on H, extended trivially elsewhere *)
          (rho_H_pred : forall g, fis_pred FIS g -> True) (* H-domain marker *)
          (zero_F : F) (add_F : F -> F -> F).

  (** Sum over the transversal, of the trace of the cocycle h_i,
      restricted to the fixed-point set of σ_g. *)
  Definition induced_trace_F (g : G) : F :=
    let fix go (k : nat) (acc : F) : F :=
        match k with
        | 0 => acc
        | S k' =>
            if Nat.eqb (coset_sigma FIS g k') k'
            then go k' (add_F acc
                         (mg_trace MG (rho_H (coset_cocycle FIS g k'))))
            else go k' acc
        end
    in go (fis_index FIS) zero_F.

  (** Frobenius formula (definitional). *)
  Lemma induced_trace_def : forall g : G,
      induced_trace_F g =
      (let fix go (k : nat) (acc : F) : F :=
           match k with
           | 0 => acc
           | S k' =>
               if Nat.eqb (coset_sigma FIS g k') k'
               then go k' (add_F acc
                          (mg_trace MG (rho_H (coset_cocycle FIS g k'))))
               else go k' acc
           end
       in go (fis_index FIS) zero_F).
  Proof. intro g. unfold induced_trace_F. reflexivity. Qed.

End InducedTrace.

(* ================================================================== *)
(** * 4. Property (B) for free groups via induction                     *)
(* ================================================================== *)

(** Strategy of paper Theorem 1.6:
    1. Given γ ∈ F_r, use Hall's theorem to find finite-index Δ ≤ F_r
       with γ ∈ Δ free factor.
    2. Build a representation ρ_Δ : Δ → SL(n, F) separating γ.
    3. Induce up: Ind ρ_Δ : F_r → SL(n·[F_r:Δ], F).
    4. Frobenius trace formula gives a polynomial trace identity
       linking γ ∈ F_r to its image.

    The Frobenius trace machinery developed in this file IS what's
    needed for step 4. Steps 1 and 2 still require the Hall theorem
    (G6) and an effective separating-rep construction. *)

(** Frobenius trace formula stated abstractly: for the induced
    representation, the trace at g is the sum over fixed cosets of
    the trace of the cocycle. (This is what [induced_trace_F]
    computes; this lemma packages it as the Frobenius statement.) *)

Section FrobeniusFormula.
  Context {G F : Type} (sg : StrictGroup G) (FIS : FiniteIndexSubgroup sg)
          (MG : MatrixGroup F)
          (zero_F : F) (add_F : F -> F -> F)
          (rho_H : G -> mg_carrier MG).

  (** Abstract Frobenius statement: the induced trace at g sums the
      traces of the cocycle h_i over fixed points of σ_g.

      This serves as the formal target for any concrete induced
      representation construction. *)
  Definition frobenius_formula_holds (induced_rep : G -> mg_carrier MG) : Prop :=
    forall g : G,
      mg_trace MG (induced_rep g) =
      induced_trace_F sg FIS MG rho_H zero_F add_F g.

End FrobeniusFormula.
