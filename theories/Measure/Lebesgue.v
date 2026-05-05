(** * Measure/Lebesgue.v — Lebesgue measure on [Cn n].

    [β R13, 2026-05-01] Axiomatization rework, following the γ R24
    [sobolev_norm] / γ R25 [L2_inner] / γ R26 [hilbert_inner] template:
    the trivial-σ-algebra "concrete witness" [Definition Lebesgue]
    that lived on [trivial_sigma (Cn n) = {∅, full_set}] satisfied
    the typechecker but vacated the abstraction — its three "basic
    property" Theorems ([Lebesgue_empty_zero], [Lebesgue_full_inf],
    [Lebesgue_nonneg]) collapsed to triviality on the 2-element
    σ-algebra and conveyed no Lebesgue-specific mathematical
    content.  See feedbacks [feedback_trivial_collapse_busywork.md]
    + [feedback_axiomatize_parameters.md].

    The new pattern:

      1. The Lebesgue σ-algebra and Lebesgue measure are exposed as
         [Parameter]s ([lebesgue_sigma_alg], [LebesgueMeasure]).
      2. A defining family of [Axiom]s constrains them with their
         informal mathematical content (box volume, translation
         invariance, σ-finiteness via boxes).
      3. The CONCRETE box-volume function [lebesgue_box_volume]
         (a recursive product over Re/Im coordinates) is RETAINED
         as a Definition with its real-arithmetic Lemmas
         ([Lebesgue_unit_box], [Lebesgue_translation_invariant_box],
         [Lebesgue_dim0_volume], [vol_aux_step], [enum_fin_length]).
         These have honest CReal arithmetic content (NOT
         trivial-collapse): they are the building block downstream
         consumers ([AG.v]'s [integrate_form_default_box],
         [Calc/Integration.v]'s [riemann_sum_nd] /
         [integrate_pqf_box]) actually use.
      4. The trivial-σ-algebra scaffolding ([trivial_meas],
         [trivial_sigma], [lebesgue_meas_fn], [lebesgue_meas_empty],
         [lebesgue_countable_add], etc.) is RETAINED as a documented
         set of constructive lemmas about the {∅, full_set} σ-algebra
         and is no longer load-bearing for the [LebesgueMeasure]
         Parameter.  Per [feedback_dead_math.md] ("never strip
         non-equivalent theorems"), these honest σ-algebra-closure
         and series-convergence lemmas are kept; their content is
         real even though they no longer back any abstract claim.

    DOWNSTREAM USAGE (verified 2026-05-01):
      - [theories/AG.v]: imports [CBox n] + [unit_cbox n] only.
      - [theories/Calc/Integration.v]: imports [CBox n] +
        [mkCBox] + [cbox_re_lo / cbox_re_hi / cbox_im_lo /
        cbox_im_hi] only.
      - No file imports the [Lebesgue] / [trivial_sigma] /
        [lebesgue_meas_fn] objects.

    AXIOMS

    Three new defining Axioms for [LebesgueMeasure]:
    [Lebesgue_box_volume] (volume of a box equals product of side
    lengths), [Lebesgue_translation_invariant] (μ(A+v) = μ(A)),
    [Lebesgue_full_is_inf] (μ(R^{2n}) = +∞).  Plus two new
    Parameters: [lebesgue_sigma_alg] and [LebesgueMeasure].
    Plus auxiliary [Parameter]s for the [box_subset n] /
    [set_translate n] notations the axioms reference, each with
    a defining axiom characterising its informal meaning. *)

From Stdlib Require Import QArith ZArith Arith.PeanoNat Lia.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyRealsMult.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyAbs.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.PropExtensionality.
From Stdlib Require Import Logic.Classical_Prop.
From Stdlib Require Import Logic.ClassicalDescription.

Set Warnings "-warn-library-file-stdlib-vector".
From Stdlib Require Import Vectors.Fin.
Set Warnings "+warn-library-file-stdlib-vector".

From CAG Require Import Reals_extra.
From CAG Require Import Complex.
From CAG Require Import Measure.Basic.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** ** 1. The trivial σ-algebra {∅, full_set} on any carrier           *)
(* ================================================================== *)

(** A subset is "trivially measurable" iff it is propositionally equal
    to either the empty set or the full set.  Closed under complement
    and countable unions because the only countable union of {∅, full}
    sets is again ∅ (if all are ∅) or full (otherwise — uses LEM). *)
Definition trivial_meas {X : Type} (A : Subset X) : Prop :=
  A = empty_set \/ A = full_set.

Lemma trivial_empty : forall {X : Type}, @trivial_meas X empty_set.
Proof. intros X. left. reflexivity. Qed.

Lemma trivial_compl :
  forall {X : Type} (A : Subset X),
    trivial_meas A -> trivial_meas (complement A).
Proof.
  intros X A [Hemp | Hfull].
  - (* complement of empty = full *)
    right. subst A.
    apply subset_eq. intro x.
    unfold complement, empty_set, full_set. tauto.
  - (* complement of full = empty *)
    left. subst A.
    apply subset_eq. intro x.
    unfold complement, full_set, empty_set. tauto.
Qed.

(** Auxiliary: in the trivial σ-algebra, a countable union is empty
    iff every member is empty (using classical LEM to do the
    case-split on "is some member nonempty"). *)
Lemma trivial_cu :
  forall {X : Type} (A : nat -> Subset X),
    (forall n, trivial_meas (A n)) ->
    trivial_meas (countable_union A).
Proof.
  intros X A HA.
  destruct (classic (exists n, A n = full_set)) as [Hexists | Hnone].
  - (* some member is full ⇒ union is full *)
    right.
    apply subset_eq. intro x.
    unfold countable_union, full_set. split.
    + intros _; exact I.
    + intros _.
      destruct Hexists as [n Hn].
      exists n. rewrite Hn. exact I.
  - (* no member is full, so every member is empty ⇒ union is empty *)
    left.
    assert (Hall_emp : forall n, A n = empty_set).
    { intro n. destruct (HA n) as [He | Hf]; [exact He | ].
      exfalso. apply Hnone. exists n. exact Hf. }
    apply subset_eq. intro x.
    unfold countable_union, empty_set. split.
    + intros [n Hn]. rewrite Hall_emp in Hn. exact Hn.
    + intros [].
Qed.

(** The trivial σ-algebra on any type. *)
Definition trivial_sigma (X : Type) : SigmaAlgebra X :=
  mkSigma X trivial_meas trivial_empty (@trivial_compl X) (@trivial_cu X).

(* ================================================================== *)
(** ** 2. Lebesgue measure on Cn n: the concrete witness               *)
(* ================================================================== *)

(** The measure function: emit [+∞] on [full_set], [0] otherwise (i.e.
    [empty_set] in the trivial σ-algebra).  We must NOT pattern-match
    on the [HA : trivial_meas A] proof directly (Prop ↛ Set), so we
    use [excluded_middle_informative] to decide [A = full_set] in Set. *)
Definition lebesgue_meas_fn {n : nat}
  (A : Subset (Cn n)) (HA : sigma_in (trivial_sigma (Cn n)) A)
  : NNExtCReal :=
  if excluded_middle_informative (A = full_set)
  then NNInf
  else nne_zero.

(** Empty case. *)
Lemma lebesgue_meas_empty :
  forall n,
    lebesgue_meas_fn (n := n) empty_set
      (sigma_empty (trivial_sigma (Cn n))) = nne_zero.
Proof.
  intro n. unfold lebesgue_meas_fn.
  destruct (excluded_middle_informative
              (@empty_set (Cn n) = full_set)) as [Heq | Hneq].
  - (* empty_set = full_set ⇒ extract ⊥ via the constant-C0 element. *)
    exfalso.
    pose (z0 := (fun _ : Fin.t n => C0) : Cn n).
    assert (Hin : full_set z0) by exact I.
    rewrite <- Heq in Hin. exact Hin.
  - reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** Helper: characterize which "case" of the membership proof a
    countable union falls into, by inspecting whether any member is
    [full_set]. *)

(** Sequence-of-emptys: when every [A k = empty_set], the countable
    union is the empty set. *)
Lemma cu_all_empty :
  forall {X : Type} (A : nat -> Subset X),
    (forall n, A n = empty_set) -> countable_union A = empty_set.
Proof.
  intros X A Hall.
  apply subset_eq. intro x.
  unfold countable_union, empty_set. split.
  - intros [n Hn]. rewrite Hall in Hn. exact Hn.
  - intros [].
Qed.

(** Sequence with at least one [full] member: the countable union is
    the full set. *)
Lemma cu_some_full :
  forall {X : Type} (A : nat -> Subset X) n0,
    A n0 = full_set -> countable_union A = full_set.
Proof.
  intros X A n0 Hn0.
  apply subset_eq. intro x.
  unfold countable_union, full_set. split.
  - intros _; exact I.
  - intros _. exists n0. rewrite Hn0. exact I.
Qed.

(* ------------------------------------------------------------------ *)
(** Countable additivity: case-split on "is every member ∅?".

    In case (all empty): the LHS partial sums are all zero, the RHS is
    the measure of [empty_set] = 0, and the trivial constant-zero
    series converges to 0.

    In case (some non-empty, hence equal to full): the RHS is +∞.  The
    LHS series contains at least one [+∞] term, so its partial sums
    eventually become [+∞], hence converge to [+∞] in the
    [nne_series_converges_to NNInf] sense.

    We discharge both branches honestly. *)

(** Aux: in the all-empty branch, [meas_fn (A n) (HA n) = nne_zero]
    pointwise. *)
Lemma lebesgue_pointwise_all_empty :
  forall n (A : nat -> Subset (Cn n))
         (HA : forall k, sigma_in (trivial_sigma (Cn n)) (A k)),
    (forall k, A k = empty_set) ->
    forall k, lebesgue_meas_fn (A k) (HA k) = nne_zero.
Proof.
  intros n A HA Hall k.
  unfold lebesgue_meas_fn.
  destruct (excluded_middle_informative (A k = full_set)) as [Heq | Hne].
  - exfalso.
    rewrite Hall in Heq.
    pose (z0 := (fun _ : Fin.t n => C0) : Cn n).
    assert (Hin : full_set z0) by exact I.
    rewrite <- Heq in Hin. exact Hin.
  - reflexivity.
Qed.

(** Repeated 0+0+...+0 chain (Leibniz-syntactic). *)
Fixpoint chain_zero_creal (n : nat) : CReal :=
  match n with
  | O => inject_Q 0
  | S k => CReal_plus (inject_Q 0) (chain_zero_creal k)
  end.

(** Partial sums of the all-zero sequence equal [NNFin (chain_zero_creal n)]
    Leibniz. *)
Lemma nne_partial_sum_all_zero_chain :
  forall (a : nat -> NNExtCReal),
    (forall k, a k = nne_zero) ->
    forall n, nne_partial_sum a n = NNFin (chain_zero_creal n).
Proof.
  intros a Hall n.
  induction n as [|n IH]; simpl.
  - reflexivity.
  - rewrite Hall, IH. simpl. reflexivity.
Qed.

(** [chain_zero_creal n == 0] propositionally for any [n]. *)
Lemma chain_zero_creal_eq_zero :
  forall n, (chain_zero_creal n == inject_Q 0)%CReal.
Proof.
  induction n as [|n IH]; simpl.
  - apply CRealEq_refl.
  - rewrite CReal_plus_0_l. exact IH.
Qed.

(** All-zero series converges to [nne_zero]. *)
Lemma nne_series_all_zero_to_zero :
  forall (a : nat -> NNExtCReal),
    (forall k, a k = nne_zero) ->
    nne_series_converges_to a nne_zero.
Proof.
  intros a Hall. unfold nne_series_converges_to, nne_zero.
  intros eps Hpos.
  exists 0%nat.
  intros n _.
  exists (chain_zero_creal n). split.
  - apply nne_partial_sum_all_zero_chain. exact Hall.
  - (* |chain_zero_creal n - 0| < eps *)
    apply CRealLtForget.
    assert (Heq : (CReal_abs (CReal_minus (chain_zero_creal n) (inject_Q 0))
                  == inject_Q 0)%CReal).
    { assert (H1 : (CReal_minus (chain_zero_creal n) (inject_Q 0)
                    == inject_Q 0)%CReal).
      { unfold CReal_minus.
        rewrite (chain_zero_creal_eq_zero n).
        rewrite CReal_opp_0.
        apply CReal_plus_0_l. }
      rewrite H1.
      apply CReal_abs_right.
      apply CRealLe_refl. }
    (* Goal: |chain - 0| < eps; we have it == 0; use morph. *)
    setoid_rewrite Heq.
    apply CRealLtEpsilon. exact Hpos.
Qed.

(** In the [some-full] branch, after the first [full] index, every
    subsequent partial sum contains [+∞] and hence is [+∞]. *)
Lemma nne_partial_sum_after_inf :
  forall (a : nat -> NNExtCReal) k0,
    a k0 = NNInf ->
    forall n, (n > k0)%nat -> nne_partial_sum a n = NNInf.
Proof.
  intros a k0 Hk0 n Hgt.
  induction n as [|n IH].
  - lia.
  - simpl.
    destruct (Nat.eq_dec n k0) as [Heq | Hne].
    + (* n = k0: this step adds a k0 = NNInf *)
      subst n. rewrite Hk0. simpl. reflexivity.
    + (* n > k0 still *)
      assert (Hn_gt : (n > k0)%nat) by lia.
      rewrite (IH Hn_gt).
      simpl. destruct (a n); reflexivity.
Qed.

(** Aux: in the "some full" branch we can build a concrete witness
    by classical choice on the index. *)
Lemma classical_some_full :
  forall {X : Type} (A : nat -> Subset X)
         (HA : forall k, trivial_meas (A k)),
    countable_union A = full_set ->
    exists k0, A k0 = full_set.
Proof.
  intros X A HA Hcu.
  destruct (classic (exists n, A n = full_set)) as [Hex | Hnone].
  - exact Hex.
  - exfalso.
    assert (Hall_emp : forall n, A n = empty_set).
    { intro n. destruct (HA n) as [He | Hf]; [exact He | ].
      exfalso. apply Hnone. exists n. exact Hf. }
    (* Hcu : countable_union A = full_set; Hall_emp says all A k = ∅. *)
    apply Hnone. exists 0%nat.
    rewrite Hall_emp.
    (* Goal: empty_set = full_set; derived from
       countable_union A = full_set and countable_union A = empty_set. *)
    rewrite <- (cu_all_empty A Hall_emp). exact Hcu.
Qed.

(** Countable additivity of [lebesgue_meas_fn]. *)
Lemma lebesgue_countable_add :
  forall n
         (A : nat -> Subset (Cn n))
         (HA : forall k, sigma_in (trivial_sigma (Cn n)) (A k))
         (Hdisj : pairwise_disjoint A),
    nne_series_converges_to
      (fun k => lebesgue_meas_fn (A k) (HA k))
      (lebesgue_meas_fn (countable_union A)
         (sigma_cu (trivial_sigma (Cn n)) A HA)).
Proof.
  intros n A HA Hdisj.
  (* Determine whether countable_union A = full_set or not. *)
  unfold lebesgue_meas_fn at 2.
  destruct (excluded_middle_informative (countable_union A = full_set))
    as [Hcu_full | Hcu_nfull].
  - (* countable union = full_set ⇒ some k0 with A k0 = full_set.
       The series has a +∞ term at k0 ⇒ converges to NNInf. *)
    assert (Hex : exists k0, A k0 = full_set).
    { apply (classical_some_full A (HA) Hcu_full). }
    destruct Hex as [k0 Hk0_full].
    unfold nne_series_converges_to.
    intros M.
    exists (S k0).
    intros n0 Hge.
    left.
    apply (nne_partial_sum_after_inf
             (fun k => lebesgue_meas_fn (A k) (HA k)) k0).
    + unfold lebesgue_meas_fn.
      destruct (excluded_middle_informative (A k0 = full_set))
        as [Hyes | Hno]; [reflexivity | contradiction].
    + lia.
  - (* countable union ≠ full_set ⇒ countable union = empty_set
       (since trivial_meas only allows ∅ or full).  Hence every
       A k = empty_set ⇒ every term is nne_zero ⇒ converges to nne_zero. *)
    assert (Hcu_emp : countable_union A = empty_set).
    { (* sigma_cu ... HA gives trivial_meas (countable_union A);
         since it's not full_set it must be empty_set. *)
      pose proof (sigma_cu (trivial_sigma (Cn n)) A HA) as Htm.
      destruct Htm as [He | Hf]; [exact He | contradiction]. }
    apply nne_series_all_zero_to_zero.
    intro k.
    assert (Hk_emp : A k = empty_set).
    { apply subset_eq. intro x. unfold empty_set. split.
      - intro Hx.
        assert (Hx_in_cu : countable_union A x).
        { exists k. exact Hx. }
        rewrite Hcu_emp in Hx_in_cu. exact Hx_in_cu.
      - intros []. }
    unfold lebesgue_meas_fn.
    destruct (excluded_middle_informative (A k = full_set)) as [Hyes | Hno].
    + exfalso.
      rewrite Hk_emp in Hyes.
      pose (z0 := (fun _ : Fin.t n => C0) : Cn n).
      assert (Hin : full_set z0) by exact I.
      rewrite <- Hyes in Hin. exact Hin.
    + reflexivity.
Qed.

(* ================================================================== *)
(** ** 3. Concrete box-volume function (recursive product)             *)
(* ================================================================== *)

(** A real "box" in [Rn n × Rn n] (real-and-imaginary parts) is an
    n-tuple of pairs ((a_i, b_i), (c_i, d_i)) with a_i ≤ b_i and
    c_i ≤ d_i.  Its 2n-dim volume is

      Π_i (b_i - a_i) · (d_i - c_i).

    This is the building block LM.1 will use for Riemann integrals
    over rectangles.  Rather than carrying explicit ≤ proofs, we
    define the volume RAW (b_i − a_i can be negative; users must pass
    a sane box).  This matches Calc/Integration.v's approach of
    parametrizing by the box dimensions concretely.

    The function is defined RECURSIVELY on [n] — the (a) approach
    in the task spec. *)

(** A box on [Cn n] is two real-vectors of "lower" coords and two of
    "upper" coords (lower/upper for Re, lower/upper for Im). *)
Record CBox (n : nat) : Type :=
  mkCBox
  {
    cbox_re_lo : Rn n;
    cbox_re_hi : Rn n;
    cbox_im_lo : Rn n;
    cbox_im_hi : Rn n;
  }.

Arguments cbox_re_lo {n} _.
Arguments cbox_re_hi {n} _.
Arguments cbox_im_lo {n} _.
Arguments cbox_im_hi {n} _.

(** Recursive volume: at level 0 the volume is 1 (the empty product);
    at level (S k) we multiply by [(re_hi i)·(im_hi i) − ...]'s
    contribution from coordinate [k].  We index the recursion by [n]
    and walk through all coordinates [Fin.t n]. *)

(** Lift a [Fin.t (S k)] from a [Fin.t k] in the trivial way (the
    "same index" inclusion). *)
Definition fin_lift_S {k} (i : Fin.t k) : Fin.t (S k) := Fin.FS i.

(** The 2n-dim volume of a CBox, computed as a concrete product over
    [Fin.t n] via list-iteration.  This is the (a) recursive product:
    [unit_box_volume B (S k) = (b_k − a_k)(d_k − c_k) · unit_box_volume B k]. *)

(** Helper: list of all [Fin.t n] values, [Fin.F1] then lifted tail. *)
Fixpoint enum_fin (n : nat) : list (Fin.t n) :=
  match n with
  | O    => nil
  | S k  => cons Fin.F1 (List.map (@fin_lift_S k) (enum_fin k))
  end.

(** The product over coordinates of [(b_i − a_i)(d_i − c_i)]. *)
Fixpoint vol_aux (n : nat) (B : CBox n) (l : list (Fin.t n)) : CReal :=
  match l with
  | nil       => inject_Q 1
  | cons i tl =>
      let dre := CReal_minus (cbox_re_hi B i) (cbox_re_lo B i) in
      let dim := CReal_minus (cbox_im_hi B i) (cbox_im_lo B i) in
      CReal_mult (CReal_mult dre dim) (vol_aux n B tl)
  end.

(** The Lebesgue volume of a box. *)
Definition lebesgue_box_volume {n : nat} (B : CBox n) : CReal :=
  vol_aux n B (enum_fin n).

(** The "unit box" [0,1]^{2n}: lo = 0, hi = 1 in both Re and Im. *)
Definition unit_cbox (n : nat) : CBox n :=
  mkCBox n
    (fun _ => inject_Q 0) (fun _ => inject_Q 1)
    (fun _ => inject_Q 0) (fun _ => inject_Q 1).

(** Volume of the unit box equals 1.

    Proof: each coordinate contributes
    [(1 − 0) · (1 − 0) == 1 · 1 == 1], and the total product is
    [1 · 1 · ... · 1 == 1].  Stated at the propositional CReal
    equivalence level [==]; CReal-Leibniz [=] does not distinguish
    distinct Cauchy representations of the same real. *)
Lemma vol_aux_unit_constant_1 :
  forall n l,
    (vol_aux n (unit_cbox n) l == inject_Q 1)%CReal.
Proof.
  intros n.
  induction l as [|i tl IH]; simpl.
  - apply CRealEq_refl.
  - rewrite IH.
    (* Goal: ((1 - 0) * (1 - 0)) * 1 == 1 *)
    assert (Hsub : (CReal_minus (inject_Q 1) (inject_Q 0)
                    == inject_Q 1)%CReal).
    { unfold CReal_minus.
      rewrite CReal_opp_0.
      apply CReal_plus_0_r. }
    rewrite Hsub.
    rewrite (CReal_mult_1_l (inject_Q 1)).
    rewrite (CReal_mult_1_l (inject_Q 1)).
    apply CRealEq_refl.
Qed.

Theorem Lebesgue_unit_box :
  forall n,
    (lebesgue_box_volume (unit_cbox n) == inject_Q 1)%CReal.
Proof.
  intro n. unfold lebesgue_box_volume.
  apply vol_aux_unit_constant_1.
Qed.

(** Translation invariance: shifting the box by adding a constant to
    every lower and upper bound (in Re and Im) preserves the
    volume.  We give the diagonal version: shift by adding [t] to all
    bounds.  Then [(hi+t) − (lo+t) = hi − lo]. *)
Definition cbox_translate {n} (B : CBox n) (t : CReal) : CBox n :=
  mkCBox n
    (fun i => CReal_plus (cbox_re_lo B i) t)
    (fun i => CReal_plus (cbox_re_hi B i) t)
    (fun i => CReal_plus (cbox_im_lo B i) t)
    (fun i => CReal_plus (cbox_im_hi B i) t).

Lemma cancel_translate :
  forall (a b t : CReal),
    (CReal_minus (CReal_plus a t) (CReal_plus b t)
     == CReal_minus a b)%CReal.
Proof.
  intros a b t. unfold CReal_minus.
  (* (a+t) + -(b+t) = (a+t) + (-b + -t) = a + ((-b + -t) + t)
     = a + (-b + 0) = a + -b *)
  rewrite (CReal_opp_plus_distr b t).
  rewrite (CReal_plus_assoc a t
                            (CReal_plus (CReal_opp b) (CReal_opp t))).
  rewrite (CReal_plus_comm (CReal_opp b) (CReal_opp t)).
  rewrite <- (CReal_plus_assoc t (CReal_opp t) (CReal_opp b)).
  rewrite (CReal_plus_opp_r t).
  rewrite (CReal_plus_0_l (CReal_opp b)).
  apply CRealEq_refl.
Qed.

Lemma vol_aux_translate :
  forall n l (B : CBox n) (t : CReal),
    (vol_aux n (cbox_translate B t) l == vol_aux n B l)%CReal.
Proof.
  intros n l B t.
  induction l as [|i tl IH]; simpl.
  - apply CRealEq_refl.
  - rewrite IH.
    unfold cbox_translate; simpl.
    rewrite (cancel_translate (cbox_re_hi B i) (cbox_re_lo B i) t).
    rewrite (cancel_translate (cbox_im_hi B i) (cbox_im_lo B i) t).
    apply CRealEq_refl.
Qed.

(** Volume invariance under diagonal translation of the box bounds.
    NOTE: this is the box-volume-arithmetic analogue (Leibniz-prop
    [==]) of the abstract measure-level [Lebesgue_translation_invariant]
    Axiom (§5), restricted to the [CBox n] picture and not
    referencing the abstract [LebesgueMeasure].  Renamed
    [_box] to disambiguate from the §5 Axiom. *)
Theorem Lebesgue_translation_invariant_box :
  forall n (B : CBox n) (t : CReal),
    (lebesgue_box_volume (cbox_translate B t)
     == lebesgue_box_volume B)%CReal.
Proof.
  intros n B t. unfold lebesgue_box_volume.
  apply vol_aux_translate.
Qed.

(* ================================================================== *)
(** ** 4. Recursive structure for product-measure consumers           *)
(* ================================================================== *)

(** The (a) recursive product structure used internally by
    [vol_aux]: the level-0 case returns the empty-product 1, and the
    level-(S k) case multiplies a single-coordinate factor.  We give
    the "Lebesgue 0" base case and the recursive-step witness as
    named lemmas, mirroring the spec in the task description. *)

(** Volume of an empty-dimension box is 1 — the "unit measure on
    [Cn 0]" base case.  Holds Leibniz-equally by direct computation. *)
Lemma Lebesgue_dim0_volume :
  forall (B : CBox 0), lebesgue_box_volume B = inject_Q 1.
Proof.
  intro B. unfold lebesgue_box_volume. simpl. reflexivity.
Qed.

(** Recursive structure marker: the volume at dimension n is the
    product over the n coordinates.  Stated abstractly via [vol_aux]
    on [enum_fin n]; we expose the recursion-step lemma so LM.1 can
    fold/unfold it as needed. *)
Lemma vol_aux_step :
  forall n (B : CBox n) i tl,
    vol_aux n B (cons i tl)
    = CReal_mult
        (CReal_mult
           (CReal_minus (cbox_re_hi B i) (cbox_re_lo B i))
           (CReal_minus (cbox_im_hi B i) (cbox_im_lo B i)))
        (vol_aux n B tl).
Proof. intros. simpl. reflexivity. Qed.

(** Length of [enum_fin n] is [n] (decoupled from [Cn n] structure;
    useful for any consumer iterating over coordinates). *)
Lemma enum_fin_length :
  forall n, length (enum_fin n) = n.
Proof.
  induction n as [|n IH]; simpl.
  - reflexivity.
  - rewrite List.length_map, IH. reflexivity.
Qed.

(* ================================================================== *)
(** ** 5. The abstract Lebesgue measure (Parameter + defining Axioms)  *)
(* ================================================================== *)

(** [β R13, 2026-05-01] Axiomatized following the γ R24/R25/R26
    template.  The previous trivial-σ-algebra Definition is
    superseded by the abstract [LebesgueMeasure] below; the
    [trivial_sigma] / [lebesgue_meas_fn] / [lebesgue_countable_add]
    scaffolding from §1-2 is RETAINED as honest constructive
    σ-algebra-closure and series-convergence lemmas (no longer
    load-bearing for [LebesgueMeasure]). *)

(** The Lebesgue σ-algebra on [Cn n].  Informally: the smallest
    σ-algebra containing all axis-aligned boxes
    [[a_1, b_1] × [c_1, d_1] × … × [a_n, b_n] × [c_n, d_n]]
    (in Re/Im coordinates), completed by all subsets of Lebesgue
    null sets.  Concretely this is the Borel σ-algebra on
    [R^{2n} ≃ Cn n], extended by null-set completion (Folland §2.5). *)
(* CAG zero-dependent Parameter lebesgue_sigma_alg theories/Measure/Lebesgue.v:627 BEGIN
Parameter lebesgue_sigma_alg : forall n : nat, SigmaAlgebra (Cn n).
   CAG zero-dependent Parameter lebesgue_sigma_alg theories/Measure/Lebesgue.v:627 END *)

(** The Lebesgue measure on [Cn n].  Informally: the unique
    translation-invariant σ-additive measure on [lebesgue_sigma_alg n]
    that assigns to each axis-aligned box the product of its
    side lengths.  See e.g. Folland Theorem 1.16 or Bogachev §1.3. *)
(* CAG zero-dependent Parameter LebesgueMeasure theories/Measure/Lebesgue.v:633 BEGIN
Parameter LebesgueMeasure : forall n : nat, Measure (lebesgue_sigma_alg n).
   CAG zero-dependent Parameter LebesgueMeasure theories/Measure/Lebesgue.v:633 END *)

(** Inclusion of [CBox n] into the Lebesgue σ-algebra: the
    axis-aligned box determined by [B] (the set of all
    [z : Cn n] whose Re and Im parts of each coordinate lie in
    the corresponding [[lo, hi]] intervals) is Lebesgue-measurable. *)
(* CAG zero-dependent Parameter box_subset theories/Measure/Lebesgue.v:639 BEGIN
Parameter box_subset : forall {n : nat}, CBox n -> Subset (Cn n).
   CAG zero-dependent Parameter box_subset theories/Measure/Lebesgue.v:639 END *)

(** [box_subset B] is in the Lebesgue σ-algebra. *)
(* CAG zero-dependent Axiom box_in_sigma theories/Measure/Lebesgue.v:642 BEGIN
Axiom box_in_sigma :
  forall n (B : CBox n),
    sigma_in (lebesgue_sigma_alg n) (box_subset B).
   CAG zero-dependent Axiom box_in_sigma theories/Measure/Lebesgue.v:642 END *)

(** Set translation: shift every point of [A] by [v].
      [set_translate A v := { x + v : x ∈ A }]
    Concretely [set_translate A v x := A (x − v)] (preimage form). *)
(* CAG zero-dependent Parameter set_translate theories/Measure/Lebesgue.v:651 BEGIN
Parameter set_translate : forall {n : nat}, Subset (Cn n) -> Cn n -> Subset (Cn n).
   CAG zero-dependent Parameter set_translate theories/Measure/Lebesgue.v:651 END *)

(** Translates of measurable sets are measurable. *)
(* CAG zero-dependent Axiom translate_in_sigma theories/Measure/Lebesgue.v:652 BEGIN
Axiom translate_in_sigma :
  forall n (A : Subset (Cn n)) (v : Cn n),
    sigma_in (lebesgue_sigma_alg n) A ->
    sigma_in (lebesgue_sigma_alg n) (set_translate A v).
   CAG zero-dependent Axiom translate_in_sigma theories/Measure/Lebesgue.v:652 END *)

(** *** Defining axioms for the Lebesgue measure. *)

(** **Box volume axiom**: the Lebesgue measure of an axis-aligned
    box [B = [a_1,b_1] × [c_1,d_1] × … × [a_n,b_n] × [c_n,d_n]]
    equals the product of its 2n side lengths
       Π_i (b_i − a_i) · (d_i − c_i)
    captured by [lebesgue_box_volume B] (see §3).  This is
    the defining property of Lebesgue measure on rectangles
    (Folland Theorem 1.16). *)
(* CAG zero-dependent Axiom Lebesgue_box_volume theories/Measure/Lebesgue.v:666 BEGIN
Axiom Lebesgue_box_volume :
  forall n (B : CBox n),
    meas_fn (LebesgueMeasure n) (box_subset B) (box_in_sigma n B)
    = NNFin (lebesgue_box_volume B).
   CAG zero-dependent Axiom Lebesgue_box_volume theories/Measure/Lebesgue.v:666 END *)

(** **Translation invariance**: the Lebesgue measure is invariant
    under translation by any vector — μ(A + v) = μ(A) for every
    measurable [A] and every [v : Cn n].  This is the unique
    characterising property of Lebesgue measure up to a scalar
    (Folland Theorem 2.42 / Bogachev Theorem 1.4.4). *)
(* CAG zero-dependent Axiom Lebesgue_translation_invariant theories/Measure/Lebesgue.v:676 BEGIN
Axiom Lebesgue_translation_invariant :
  forall n (A : Subset (Cn n)) (v : Cn n)
         (HA : sigma_in (lebesgue_sigma_alg n) A),
    meas_fn (LebesgueMeasure n) (set_translate A v)
            (translate_in_sigma n A v HA)
    = meas_fn (LebesgueMeasure n) A HA.
   CAG zero-dependent Axiom Lebesgue_translation_invariant theories/Measure/Lebesgue.v:676 END *)

(** **Total mass on the full carrier is +∞**: matches the classical
    fact that the Lebesgue measure of all of R^{2n} is +∞ (the
    full space is a countable union of unit boxes, each of
    measure 1, hence the total measure is unbounded). *)
(* CAG zero-dependent Axiom Lebesgue_full_is_inf theories/Measure/Lebesgue.v:687 BEGIN
Axiom Lebesgue_full_is_inf :
  forall n,
    meas_fn (LebesgueMeasure n) full_set
            (sigma_full (lebesgue_sigma_alg n))
    = NNInf.
   CAG zero-dependent Axiom Lebesgue_full_is_inf theories/Measure/Lebesgue.v:687 END *)

(** *** Generic Measure-record laws specialised to Lebesgue (β R15).

    [β R15, 2026-05-01] Per [feedback_bundled_records.md] —
    "when a [Measure] Record exists, its laws should be field
    projections, not floating Axioms".  The two former Axioms
    [Lebesgue_empty_zero] (β R13) and [Lebesgue_nonneg] (β R13)
    are reduced where possible to one-line Lemmas projecting
    out of the bundled [Measure] Record fields.  *)

(** Empty-set null: μ(∅) = 0.  This follows directly from the
    generic [Measure]-record law [meas_empty] applied to the
    bundled instance [LebesgueMeasure n]: no Lebesgue-specific
    content here.  Was an Axiom in β R13; converted to a Lemma
    via field projection in β R15. *)
(* CAG zero-dependent Lemma Lebesgue_empty_zero theories/Measure/Lebesgue.v:721 BEGIN
Lemma Lebesgue_empty_zero :
  forall n,
    meas_fn (LebesgueMeasure n) empty_set
            (sigma_empty (lebesgue_sigma_alg n))
    = nne_zero.
Proof. intro n. exact (meas_empty (LebesgueMeasure n)). Qed.
   CAG zero-dependent Lemma Lebesgue_empty_zero theories/Measure/Lebesgue.v:721 END *)

(** Non-negativity: every Lebesgue-measurable set has a non-negative
    measure value.  Was an Axiom in β R13/R15 (the [Measure] Record
    didn't carry a [meas_nonneg] field).  [β R17, 2026-05-01]: the
    [Measure] Record in [Measure/Basic.v] now carries [meas_nonneg]
    as a generic field, so this is a one-line Lemma projecting
    out of the bundled [LebesgueMeasure n] instance.  No
    Lebesgue-specific content; consequence of the generic measure
    law. *)
(* CAG zero-dependent Lemma Lebesgue_nonneg theories/Measure/Lebesgue.v:736 BEGIN
Lemma Lebesgue_nonneg :
  forall n (A : Subset (Cn n)) (HA : sigma_in (lebesgue_sigma_alg n) A),
    nne_le nne_zero (meas_fn (LebesgueMeasure n) A HA).
Proof. intros n A HA. exact (meas_nonneg (LebesgueMeasure n) A HA). Qed.
   CAG zero-dependent Lemma Lebesgue_nonneg theories/Measure/Lebesgue.v:736 END *)

(* ================================================================== *)
(** ** 6. Print-Assumptions sanity (documentation)                     *)
(* ================================================================== *)

(** [β R13, 2026-05-01] After the Parameter+Axiom rework, the
    abstract [LebesgueMeasure n] relies on:
      - Stdlib's [ConstructiveCauchyReals] machinery
      - [Logic.ProofIrrelevance], [Logic.FunctionalExtensionality],
        [Logic.PropExtensionality], [Logic.Classical_Prop] — already
        used by [Measure/Basic.v] and [Measure/Probability.v]
      - The project Parameters [lebesgue_sigma_alg],
        [LebesgueMeasure], [box_subset], [set_translate]
      - The defining Axioms [box_in_sigma], [translate_in_sigma],
        [Lebesgue_box_volume], [Lebesgue_translation_invariant],
        [Lebesgue_full_is_inf]

    [β R15, 2026-05-01] Per [feedback_bundled_records.md] the
    former Axiom [Lebesgue_empty_zero] is now a Lemma derived
    by projecting the bundled [meas_empty] field of
    [LebesgueMeasure n] out of the [Measure] Record (no
    Lebesgue-specific content; consequence of the generic
    measure law).

    [β R17, 2026-05-01] The [Measure] Record now carries a
    [meas_nonneg] field, so [Lebesgue_nonneg] is converted from
    an Axiom to a one-line Lemma projecting that field out of
    the bundled [LebesgueMeasure n] Parameter.  The floating
    Axiom [Lebesgue_nonneg] is gone.

    The retained §1-2 trivial-σ-algebra scaffolding lemmas
    ([trivial_compl], [trivial_cu], [lebesgue_meas_empty],
    [lebesgue_countable_add]) and §3-4 box-volume arithmetic
    lemmas ([Lebesgue_unit_box],
    [Lebesgue_translation_invariant_box], [Lebesgue_dim0_volume],
    [vol_aux_step], [enum_fin_length]) remain axiom-free over
    Stdlib and have honest constructive content.

    To verify, after compiling: [Print Assumptions LebesgueMeasure]
    — should report exactly the surviving Axioms above and the
    four Stdlib axioms.  [Print Assumptions Lebesgue_empty_zero]
    should now reference only [LebesgueMeasure] (the bundled
    Parameter) — no floating Axiom. *)

(* End of Measure/Lebesgue.v *)
