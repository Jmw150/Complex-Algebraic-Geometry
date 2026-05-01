(** * Measure/Basic.v — Constructive measure theory foundations.

    Built on the constructive Cauchy reals [CReal] from Stdlib via the
    project's [Reals_extra] layer.

    This file lays out σ-algebras, measures, and measurable functions
    in a constructive style. Where classical measure theory uses
    extended reals [0, +∞], we use [CReal] augmented with an explicit
    "infinity tag" — a sum type [NonNegExtCReal := CReal_NonNeg + Infinity].

    Convention: subsets of a carrier [X] are predicates [X -> Prop].
    Sequences of subsets are functions [nat -> X -> Prop].

    Date: 2026-04-28 (run-5 pivot).
    Sources: Folland, "Real Analysis: Modern Techniques"; Bishop &
    Bridges, "Constructive Analysis" (for the constructive style);
    Coquand & Spitters, "Integrals and valuations" (for the
    constructive measure-theoretic frame). *)

From Stdlib Require Import QArith ZArith.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyRealsMult.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyAbs.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.PropExtensionality.
From Stdlib Require Import Logic.Classical_Prop.
From CAG Require Import Reals_extra.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** ** 1. Subsets and operations                                       *)
(* ================================================================== *)

Definition Subset (X : Type) : Type := X -> Prop.

Definition empty_set {X : Type} : Subset X := fun _ => False.
Definition full_set {X : Type} : Subset X := fun _ => True.

Definition union {X : Type} (A B : Subset X) : Subset X :=
  fun x => A x \/ B x.

Definition intersection {X : Type} (A B : Subset X) : Subset X :=
  fun x => A x /\ B x.

Definition complement {X : Type} (A : Subset X) : Subset X :=
  fun x => ~ A x.

Definition difference {X : Type} (A B : Subset X) : Subset X :=
  fun x => A x /\ ~ B x.

Definition subset_of {X : Type} (A B : Subset X) : Prop :=
  forall x, A x -> B x.

Definition disjoint {X : Type} (A B : Subset X) : Prop :=
  forall x, ~ (A x /\ B x).

(** Countable union: union of a sequence of subsets. *)
Definition countable_union {X : Type} (A : nat -> Subset X) : Subset X :=
  fun x => exists n, A n x.

(** Countable intersection. *)
Definition countable_intersection {X : Type} (A : nat -> Subset X) : Subset X :=
  fun x => forall n, A n x.

(** Pairwise disjoint sequence. *)
Definition pairwise_disjoint {X : Type} (A : nat -> Subset X) : Prop :=
  forall i j, i <> j -> disjoint (A i) (A j).

(* ================================================================== *)
(** ** 2. σ-algebras                                                   *)
(* ================================================================== *)

(** A σ-algebra on [X] is a collection of subsets (encoded as a
    predicate on [Subset X]) that contains the empty set, is closed
    under complement, and is closed under countable union. *)
Record SigmaAlgebra (X : Type) : Type :=
  mkSigma
  {
    sigma_in       : Subset X -> Prop;
    sigma_empty    : sigma_in empty_set;
    sigma_compl    : forall A, sigma_in A -> sigma_in (complement A);
    sigma_cu       : forall A : nat -> Subset X,
                     (forall n, sigma_in (A n)) ->
                     sigma_in (countable_union A);
  }.

Arguments sigma_in {X} _ _.
Arguments sigma_empty {X} _.
Arguments sigma_compl {X} _ _ _.
Arguments sigma_cu {X} _ _ _.

(** σ-algebra also contains the full set: complement of the empty set. *)
Lemma sigma_full : forall {X : Type} (S : SigmaAlgebra X),
    sigma_in S full_set.
Proof.
  intros X S.
  pose proof (sigma_compl S empty_set (sigma_empty S)) as Hcomp.
  unfold complement, empty_set, full_set in *.
  assert (Heq : (fun x : X => ~ False) = (fun _ : X => True)).
  { apply functional_extensionality. intro x.
    apply propositional_extensionality. tauto. }
  rewrite <- Heq. exact Hcomp.
Qed.

(** Helper: subset extensionality for predicates. *)
Lemma subset_eq : forall {X : Type} (A B : Subset X),
    (forall x, A x <-> B x) -> A = B.
Proof.
  intros X A B Hiff.
  apply functional_extensionality. intro x.
  apply propositional_extensionality. apply Hiff.
Qed.

(** Closure under finite (binary) union via the constant-after-1 sequence. *)
Lemma sigma_union :
  forall {X : Type} (S : SigmaAlgebra X) (A B : Subset X),
    sigma_in S A -> sigma_in S B -> sigma_in S (union A B).
Proof.
  intros X S A B HA HB.
  set (seq := fun n : nat => match n with O => A | _ => B end).
  assert (Hseq : forall n, sigma_in S (seq n)).
  { intros [|n]; simpl; assumption. }
  pose proof (sigma_cu S seq Hseq) as Hcu.
  assert (Heq : countable_union seq = union A B).
  { apply subset_eq. intro x. unfold countable_union, union. split.
    - intros [n Hn]. destruct n as [|n]; simpl in Hn; tauto.
    - intros [Ha | Hb].
      + exists 0%nat. simpl. exact Ha.
      + exists 1%nat. simpl. exact Hb. }
  rewrite Heq in Hcu. exact Hcu.
Qed.

(** Closure under binary intersection via union + complement (de Morgan).
    Uses LEM via [Classical_Prop.classic] for the ¬¬A → A step. *)
Lemma sigma_intersection :
  forall {X : Type} (S : SigmaAlgebra X) (A B : Subset X),
    sigma_in S A -> sigma_in S B -> sigma_in S (intersection A B).
Proof.
  intros X S A B HA HB.
  pose proof (sigma_compl S A HA) as HcA.
  pose proof (sigma_compl S B HB) as HcB.
  pose proof (sigma_union S _ _ HcA HcB) as Hu.
  pose proof (sigma_compl S _ Hu) as Hcc.
  assert (Heq : complement (union (complement A) (complement B)) =
                intersection A B).
  { apply subset_eq. intro x.
    unfold complement, union, intersection. split.
    - intro Hnn. split.
      + destruct (classic (A x)) as [Ha | Hna]; [exact Ha|].
        exfalso. apply Hnn. left. exact Hna.
      + destruct (classic (B x)) as [Hb | Hnb]; [exact Hb|].
        exfalso. apply Hnn. right. exact Hnb.
    - intros [Ha Hb] [HnA | HnB]; [apply HnA; exact Ha | apply HnB; exact Hb].
  }
  rewrite Heq in Hcc. exact Hcc.
Qed.

(** Closure under countable intersection via De Morgan. *)
Lemma sigma_ci :
  forall {X : Type} (S : SigmaAlgebra X) (A : nat -> Subset X),
    (forall n, sigma_in S (A n)) -> sigma_in S (countable_intersection A).
Proof.
  intros X S A HA.
  set (Ac := fun n => complement (A n)).
  assert (HAc : forall n, sigma_in S (Ac n)).
  { intro n. apply sigma_compl. apply HA. }
  pose proof (sigma_cu S Ac HAc) as Hcu.
  pose proof (sigma_compl S _ Hcu) as Hcc.
  assert (Heq : complement (countable_union Ac) = countable_intersection A).
  { apply subset_eq. intro x.
    unfold complement, countable_union, countable_intersection, Ac.
    split.
    - intros Hne n.
      destruct (classic (A n x)) as [Ha | Hna]; [exact Ha|].
      exfalso. apply Hne. exists n. exact Hna.
    - intros Hall [n Hn]. apply Hn. apply Hall. }
  rewrite Heq in Hcc. exact Hcc.
Qed.

(* ================================================================== *)
(** ** 3. Non-negative extended reals and measures                     *)
(* ================================================================== *)

(** A non-negative CReal: a CReal together with a (Prop-level)
    proof that it is ≥ 0. We avoid sigma type to keep equality simple
    and use proof_irrelevance for normalization. *)
Definition NonNeg : CReal -> Prop :=
  fun x => CRealLtProp (CReal_minus x x) (CReal_plus x (inject_Q 1)) /\
           ~ CRealLtProp x (inject_Q 0).

(** Extended non-negative reals: either a non-negative CReal value, or
    +∞. Using a tagged sum keeps the construction concrete. *)
Inductive NNExtCReal : Type :=
| NNFin (x : CReal) : NNExtCReal
| NNInf : NNExtCReal.

(** Addition on extended non-negative reals. *)
Definition nne_add (a b : NNExtCReal) : NNExtCReal :=
  match a, b with
  | NNInf, _ => NNInf
  | _, NNInf => NNInf
  | NNFin x, NNFin y => NNFin (CReal_plus x y)
  end.

Definition nne_zero : NNExtCReal := NNFin (inject_Q 0).
Definition nne_inf  : NNExtCReal := NNInf.

(** Order: a ≤ b on extended non-neg reals. *)
Definition nne_le (a b : NNExtCReal) : Prop :=
  match a, b with
  | _, NNInf => True
  | NNInf, NNFin _ => False
  | NNFin x, NNFin y => ~ CRealLtProp y x
  end.

(** Partial sums of an extended-real-valued sequence. *)
Fixpoint nne_partial_sum (a : nat -> NNExtCReal) (n : nat) : NNExtCReal :=
  match n with
  | O => nne_zero
  | Datatypes.S k => nne_add (a k) (nne_partial_sum a k)
  end.

(** Convergence of partial sums to a limit (for finite limits).
    For sums that diverge to +∞, the limit is NNInf (definition below). *)
Definition nne_series_converges_to (a : nat -> NNExtCReal) (L : NNExtCReal) : Prop :=
  match L with
  | NNFin Lr =>
      forall eps : CReal, CRpositive eps ->
        exists N : nat,
          forall n : nat, (n >= N)%nat ->
            (* partial sum is finite and within eps of Lr *)
            exists Sr, nne_partial_sum a n = NNFin Sr /\
                       CRealLtProp (CReal_abs (CReal_minus Sr Lr)) eps
  | NNInf =>
      (* sum is unbounded: for every M : CReal, eventually partial sum ≥ M *)
      forall M : CReal,
        exists N : nat,
          forall n : nat, (n >= N)%nat ->
            (nne_partial_sum a n = NNInf \/
             exists Sr, nne_partial_sum a n = NNFin Sr /\
                        ~ CRealLtProp Sr M)
  end.

(* ================================================================== *)
(** ** 4. Measures                                                      *)
(* ================================================================== *)

(** A measure on a σ-algebra is an extended-non-negative-valued function
    that vanishes on the empty set and is countably additive on
    pairwise-disjoint measurable sequences. *)
Record Measure {X : Type} (S : SigmaAlgebra X) : Type :=
  mkMeasure
  {
    meas_fn       : forall A : Subset X, sigma_in S A -> NNExtCReal;
    meas_empty    : meas_fn empty_set (sigma_empty S) = nne_zero;
    meas_countable_add :
      forall (A : nat -> Subset X)
             (HA : forall n, sigma_in S (A n))
             (Hdisj : pairwise_disjoint A),
        nne_series_converges_to
          (fun n => meas_fn (A n) (HA n))
          (meas_fn (countable_union A) (sigma_cu S A HA));
    (** [β R17, 2026-05-01] Non-negativity: μ(A) ≥ 0 for every measurable [A].
        The codomain [NNExtCReal] is a syntactic envelope (its [NNFin]
        constructor admits any [CReal], including negative values), so the
        non-negativity constraint must be made explicit at the Record level.
        Closes the gap noted in β R15 / [Lebesgue_nonneg]. *)
    meas_nonneg :
      forall (A : Subset X) (HA : sigma_in S A),
        nne_le nne_zero (meas_fn A HA);
  }.

Arguments meas_fn {X S} _ _ _.
Arguments meas_empty {X S} _.
Arguments meas_countable_add {X S} _ _ _ _.
Arguments meas_nonneg {X S} _ _ _.

(* ================================================================== *)
(** ** 5. Measurable functions                                          *)
(* ================================================================== *)

(** A function f : X → CReal is measurable wrt σ-algebra [S] on X if
    every preimage of an open ray (a, +∞) is in S. (Other open-ray
    formulations are equivalent classically.) *)
Definition is_measurable_fn {X : Type} (S : SigmaAlgebra X)
  (f : X -> CReal) : Prop :=
  forall a : CReal,
    sigma_in S (fun x => CRealLtProp a (f x)).

(** Constant functions are measurable. *)
Lemma const_measurable : forall {X : Type} (S : SigmaAlgebra X) (c : CReal),
    is_measurable_fn S (fun _ => c).
Proof.
  intros X S c a.
  destruct (classic (CRealLtProp a c)) as [Hlt | Hnlt].
  - (* {x : a < c} = full set *)
    assert (Heq : (fun _ : X => CRealLtProp a c) = full_set).
    { apply subset_eq. intro x. unfold full_set. tauto. }
    rewrite Heq. apply sigma_full.
  - (* {x : a < c} = empty set *)
    assert (Heq : (fun _ : X => CRealLtProp a c) = empty_set).
    { apply subset_eq. intro x. unfold empty_set. split.
      - intro H. apply Hnlt. exact H.
      - intro H; exfalso; exact H. }
    rewrite Heq. apply sigma_empty.
Qed.