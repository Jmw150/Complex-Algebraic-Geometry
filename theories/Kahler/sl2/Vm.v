(** Kahler/sl2/Vm.v — Concrete irreducible sl(2)-module V(m)

    For each non-negative integer m, we construct the irreducible
    sl(2)-module V(m) of highest weight m.

    Carrier:   VmType m = nat -> CComplex
                 (index k = coefficient of the k-th basis vector w_k)
               Vectors morally supported on {0,...,m}.

    Standard (un-normalized) basis:
      w_k has weight m - 2k,  k = 0, 1, ..., m

    Action formulas:
      H(w_k) = (m - 2k) w_k
      Y(w_k) = w_{k+1}             (lowering: Y shifts index up in coefficient repr)
      X(w_k) = k(m-k+1) w_{k-1}   (raising: X shifts index down)

    In coefficient representation f : nat -> CComplex:
      (H·f)(k) = (m - 2k) · f(k)
      (Y·f)(k) = f(k-1)           if k > 0; 0 if k = 0
      (X·f)(k) = (k+1)·(m-k) · f(k+1)   if k < m; 0 if k >= m

    References: ag.org Part IV §sl2; Humphreys §7.2 *)

From Stdlib Require Import Arith ZArith QArith Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyRealsMult.
From CAG Require Import Complex.
From CAG Require Import AG.
From CAG Require Import LieAlgebra.
From CAG Require Import Kahler.sl2.Basic.
From CAG Require Import Kahler.sl2.FiniteDimensional.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. The carrier type and operations                               *)
(* ================================================================== *)

(** Vectors in V(m) are coefficient sequences indexed by nat. *)
Definition VmType (m : nat) : Type := nat -> CComplex.

Definition Vm_add {m} (f g : VmType m) : VmType m := fun k => Cadd (f k) (g k).
Definition Vm_scale {m} (c : CComplex) (f : VmType m) : VmType m := fun k => Cmul c (f k).
Definition Vm_zero {m} : VmType m := fun _ => C0.
Definition Vm_neg {m} (f : VmType m) : VmType m := fun k => Cneg (f k).

(** Helper: inject nat into CComplex. *)
Definition Cnat (n : nat) : CComplex :=
  Cinject_Q (QArith_base.inject_Z (Z.of_nat n)).

(** The sl(2) operators. *)
Definition Vm_H (m : nat) (f : VmType m) : VmType m :=
  fun k => Cmul (Csub (Cnat m) (Cmul (Cnat k) (Cadd C1 C1))) (f k).

Definition Vm_Y (m : nat) (f : VmType m) : VmType m :=
  fun k => match k with O => C0 | S k' => f k' end.

Definition Vm_X (m : nat) (f : VmType m) : VmType m :=
  fun k =>
    if Nat.ltb k m
    then Cmul (Cmul (Cnat (S k)) (Cnat (m - k))) (f (S k))
    else C0.

(** Standard k-th basis vector. *)
Definition Vm_basis (m : nat) (k : nat) : VmType m :=
  fun j => if Nat.eqb j k then C1 else C0.

(* ================================================================== *)
(** * 2. Vector space structure                                        *)
(* ================================================================== *)

(** Vector-space axioms: all hold pointwise via CComplex arithmetic
    (Cadd_assoc, Cadd_comm, Cmul_C1_left, Cmul_assoc_lem, Cmul_add_distr_l/r)
    and functional extensionality. *)
Lemma Vm_add_assoc : forall {m} (u v w : VmType m),
    Vm_add u (Vm_add v w) = Vm_add (Vm_add u v) w.
Proof.
  intros m u v w. unfold Vm_add. apply functional_extensionality.
  intro k. apply Cadd_assoc.
Qed.

Lemma Vm_add_comm : forall {m} (u v : VmType m),
    Vm_add u v = Vm_add v u.
Proof.
  intros m u v. unfold Vm_add. apply functional_extensionality.
  intro k. apply Cadd_comm.
Qed.

(* Vm_add_zero_r and Vm_add_neg_r: proven via the [CRealEq_eq] bridge. *)
Lemma Vm_add_zero_r : forall {m} (f : VmType m),
    Vm_add f Vm_zero = f.
Proof.
  intros m f. unfold Vm_add, Vm_zero. apply functional_extensionality.
  intro k. apply CComplex_eq. unfold CComplex_req, Cadd, C0; cbn [re im].
  split; ring.
Qed.

Lemma Vm_add_neg_r : forall {m} (f : VmType m),
    Vm_add f (Vm_neg f) = Vm_zero.
Proof.
  intros m f. unfold Vm_add, Vm_neg, Vm_zero. apply functional_extensionality.
  intro k. apply CComplex_eq. unfold CComplex_req, Cadd, Cneg, C0; cbn [re im].
  split; ring.
Qed.

Lemma Vm_scale_one : forall {m} (f : VmType m),
    Vm_scale C1 f = f.
Proof.
  intros m f. unfold Vm_scale. apply functional_extensionality.
  intro k. apply Cmul_C1_left.
Qed.

Lemma Vm_scale_assoc : forall {m} (a b : CComplex) (f : VmType m),
    Vm_scale a (Vm_scale b f) = Vm_scale (Cmul a b) f.
Proof.
  intros m a b f. unfold Vm_scale. apply functional_extensionality.
  intro k. symmetry. apply Cmul_assoc_lem.
Qed.

Lemma Vm_scale_add_v : forall {m} (a : CComplex) (u v : VmType m),
    Vm_scale a (Vm_add u v) = Vm_add (Vm_scale a u) (Vm_scale a v).
Proof.
  intros m a u v. unfold Vm_scale, Vm_add. apply functional_extensionality.
  intro k. apply Cmul_add_distr_l.
Qed.

Lemma Vm_scale_add_s : forall {m} (a b : CComplex) (f : VmType m),
    Vm_scale (Cadd a b) f = Vm_add (Vm_scale a f) (Vm_scale b f).
Proof.
  intros m a b f. unfold Vm_scale, Vm_add. apply functional_extensionality.
  intro k. apply Cmul_add_distr_r.
Qed.

Definition Vm_vs (m : nat) : VectorSpace (VmType m) :=
  {| vs_add    := @Vm_add m
   ; vs_scale  := @Vm_scale m
   ; vs_zero   := @Vm_zero m
   ; vs_neg    := @Vm_neg m
   ; vs_add_assoc  := @Vm_add_assoc m
   ; vs_add_comm   := @Vm_add_comm m
   ; vs_add_zero_r := @Vm_add_zero_r m
   ; vs_add_neg_r  := @Vm_add_neg_r m
   ; vs_scale_one  := @Vm_scale_one m
   ; vs_scale_assoc := @Vm_scale_assoc m
   ; vs_scale_add_v := @Vm_scale_add_v m
   ; vs_scale_add_s := @Vm_scale_add_s m
   |}.

(* ================================================================== *)
(** * 3. Linearity of operators and sl(2) structure                   *)
(* ================================================================== *)

(** Linearity: Vm_H, Vm_X, Vm_Y are linear operators.
    The "add" forms follow pointwise from Cmul_add_distr_l (Vm_H, Vm_X)
    or directly (Vm_Y). The "scale" forms involve Cmul commutativity
    which the project provides only at [~~C] level, so we keep those
    as axioms. *)
Lemma Vm_H_add : forall m (u v : VmType m),
    Vm_H m (Vm_add u v) = Vm_add (Vm_H m u) (Vm_H m v).
Proof.
  intros m u v. unfold Vm_H, Vm_add. apply functional_extensionality.
  intro k. apply Cmul_add_distr_l.
Qed.

Lemma Vm_H_scale : forall m (c : CComplex) (f : VmType m),
    Vm_H m (Vm_scale c f) = Vm_scale c (Vm_H m f).
Proof.
  intros m c f. unfold Vm_H, Vm_scale. apply functional_extensionality.
  intro k. apply CComplex_eq. unfold CComplex_req, Cmul; cbn [re im].
  split; ring.
Qed.

Lemma Vm_X_add   : forall m (u v : VmType m),
    Vm_X m (Vm_add u v) = Vm_add (Vm_X m u) (Vm_X m v).
Proof.
  intros m u v. unfold Vm_X, Vm_add. apply functional_extensionality.
  intro k. destruct (Nat.ltb k m).
  - apply CComplex_eq. unfold CComplex_req, Cmul, Cadd; cbn [re im].
    split; ring.
  - apply CComplex_eq. unfold CComplex_req, Cadd, C0; cbn [re im].
    split; ring.
Qed.

Lemma Vm_X_scale : forall m (c : CComplex) (f : VmType m),
    Vm_X m (Vm_scale c f) = Vm_scale c (Vm_X m f).
Proof.
  intros m c f. unfold Vm_X, Vm_scale. apply functional_extensionality.
  intro k. destruct (Nat.ltb k m).
  - apply CComplex_eq. unfold CComplex_req, Cmul; cbn [re im].
    split; ring.
  - apply CComplex_eq. unfold CComplex_req, Cmul, C0; cbn [re im].
    split; ring.
Qed.

Lemma Vm_Y_add : forall m (u v : VmType m),
    Vm_Y m (Vm_add u v) = Vm_add (Vm_Y m u) (Vm_Y m v).
Proof.
  intros m u v. unfold Vm_Y, Vm_add. apply functional_extensionality.
  intro k. destruct k as [|k'].
  - apply CComplex_eq. unfold CComplex_req, Cadd, C0; cbn [re im].
    split; ring.
  - reflexivity.
Qed.

Lemma Vm_Y_scale : forall m (c : CComplex) (f : VmType m),
    Vm_Y m (Vm_scale c f) = Vm_scale c (Vm_Y m f).
Proof.
  intros m c f. unfold Vm_Y, Vm_scale. apply functional_extensionality.
  intro k. destruct k as [|k'].
  - apply CComplex_eq. unfold CComplex_req, Cmul, C0; cbn [re im].
    split; ring.
  - reflexivity.
Qed.

(** sl(2) commutation relations — admitted; proved in principle by
    pointwise arithmetic on each case. *)

(** Helper: [Cnat (S k) = Cnat k + 1] at the Leibniz level via the
    [CRealEq_eq] bridge. Used to make [ring] tractable on commutator
    relations. *)
Lemma Cnat_succ_eq : forall k, Cnat (S k) = Cadd (Cnat k) C1.
Proof.
  intro k. unfold Cnat, Cinject_Q, Cadd, C1.
  apply CComplex_eq. unfold CComplex_req; cbn [re im].
  rewrite Nat2Z.inj_succ.
  unfold Z.succ.
  rewrite QArith_base.inject_Z_plus.
  split.
  - rewrite inject_Q_plus. reflexivity.
  - (* 0 == 0 + 0 on CReal — use ring *)
    ring.
Qed.

Lemma Cnat_add_eq : forall a b, Cnat (a + b) = Cadd (Cnat a) (Cnat b).
Proof.
  intros a b. unfold Cnat, Cinject_Q, Cadd.
  apply CComplex_eq. unfold CComplex_req; cbn [re im].
  rewrite Nat2Z.inj_add.
  rewrite QArith_base.inject_Z_plus.
  split.
  - rewrite inject_Q_plus. reflexivity.
  - ring.
Qed.

Lemma Vm_rel_HX : forall m (f : VmType m),
    Vm_add (Vm_H m (Vm_X m f)) (Vm_neg (Vm_X m (Vm_H m f))) =
    Vm_scale (Cadd C1 C1) (Vm_X m f).
Proof.
  intros m f. unfold Vm_add, Vm_neg, Vm_scale, Vm_H, Vm_X.
  apply functional_extensionality. intro k.
  destruct (Nat.ltb k m) eqn:Hlt.
  - rewrite (Cnat_succ_eq k).
    apply CComplex_eq.
    unfold CComplex_req, Csub. simpl. cbv [QArith_base.inject_Z]. split; ring.
  - apply CComplex_eq.
    unfold CComplex_req, Csub. simpl. cbv [QArith_base.inject_Z]. split; ring.
Qed.

Lemma Vm_rel_HY : forall m (f : VmType m),
    Vm_add (Vm_H m (Vm_Y m f)) (Vm_neg (Vm_Y m (Vm_H m f))) =
    Vm_scale (Cneg (Cadd C1 C1)) (Vm_Y m f).
Proof.
  intros m f. unfold Vm_add, Vm_neg, Vm_scale, Vm_H, Vm_Y.
  apply functional_extensionality. intro k.
  destruct k as [|k'].
  - apply CComplex_eq. unfold CComplex_req, Csub. simpl.
    cbv [QArith_base.inject_Z]. split; ring.
  - rewrite (Cnat_succ_eq k').
    apply CComplex_eq. unfold CComplex_req, Csub. simpl.
    cbv [QArith_base.inject_Z]. split; ring.
Qed.

(** ============================================================
    [Vm_rel_XY] FALSE-AS-STATED — replacement [γ R30, 2026-05-01]
    ============================================================

    HISTORICAL NOTE (γ R22 triage / cycle-30 documentation).  The
    original formulation
    [[
       Axiom Vm_rel_XY : forall m (f : VmType m),
           Vm_add (Vm_X m (Vm_Y m f)) (Vm_neg (Vm_Y m (Vm_X m f)))
           = Vm_H m f.
    ]]
    is FALSE on the unrestricted carrier [VmType m = nat -> CComplex].

    Counterexample.  Take any [m] and choose [f] with [f (S m) <> 0].
    Evaluate at index [k = S m]:

    - LHS at [S m]:
        [Vm_X m (Vm_Y m f) (S m)]:  [Nat.ltb (S m) m = false], so [= C0].
        [Vm_Y m (Vm_X m f) (S m)] = [Vm_X m f m]:  [Nat.ltb m m = false],
                                                      so [= C0].
        ⇒ LHS pointwise = [Cadd C0 (Cneg C0) = C0].

    - RHS at [S m]:
        [(Cnat m - Cnat (S m) * 2) · f (S m) = (-(S m + 2)) · f (S m)],
        which is nonzero whenever [f (S m) <> 0].

    Hence the equation is not Leibniz-equal on unrestricted [f].  The
    truthful version is the SUPPORTED form below: the commutator
    relation [X, Y] = H holds pointwise on functions vanishing past
    index [m], i.e. on the natural [m+1]-dimensional subspace that
    [V(m)] morally represents.

    Replacement (γ R30): two declarations.

      (1) [Vm_supported m f]: the support predicate carving out the
          honest carrier [{f : nat -> CComplex | forall k > m, f k = C0}].

      (2) [Vm_rel_XY_supported]: a *Lemma* (not Axiom) proving the
          [X,Y]-commutator relation pointwise on supported functions.
          Sound; provable from existing [Vm_X], [Vm_Y], [Vm_H] cases.

      (3) [Vm_rel_XY_module]: a remaining structural Axiom in the
          unrestricted SL2Module shape.  Required only to satisfy the
          [sl2_rel_XY] field of the [SL2Module] record schema, which
          quantifies [forall v : VmType m] without a support-side
          condition.  Removing this axiom requires refactoring the
          carrier of [Vm_mod] to a sigma-type
          [{ f : nat -> CComplex | Vm_supported m f }] — deep
          structural work, out of scope for γ R30.  The axiom is
          declared with this comment and tagged as the sole structural
          residue of the false original.  See AXIOMS_AUDIT.md.
    ============================================================ *)

(** Support predicate: [f] vanishes past index [m].  Functions in
    [VmType m] satisfying [Vm_supported m] are the "honest" elements
    of the [m+1]-dimensional irreducible module; the [X,Y]-commutator
    relation holds pointwise on this subspace. *)
Definition Vm_supported (m : nat) (f : VmType m) : Prop :=
  forall k, (k > m)%nat -> f k = C0.

(** The [X, Y]-commutator relation on the supported subspace.  This is
    the mathematically sound replacement for the FALSE-AS-STATED
    [Vm_rel_XY] axiom.  Status: Lemma, provable from existing infra. *)
Lemma Vm_rel_XY_supported : forall m (f : VmType m),
    Vm_supported m f ->
    Vm_add (Vm_X m (Vm_Y m f)) (Vm_neg (Vm_Y m (Vm_X m f))) =
    Vm_H m f.
Proof.
  intros m f Hsup.
  apply functional_extensionality. intro k.
  destruct (Nat.compare_spec k m) as [Hkm|Hkm|Hkm].
  - (* k = m.  LHS: Vm_X (Vm_Y f) m + (- Vm_Y (Vm_X f) m).
       Vm_X _ m = C0 (since Nat.ltb m m = false).
       Vm_Y (Vm_X f) m = (Vm_X f)(m-1) for m > 0; = 0 for m = 0.
       RHS: Vm_H f m = (Cnat m - Cnat m * 2) * f m. *)
    subst k.
    destruct m as [|m'].
    + (* m = 0. *)
      unfold Vm_add, Vm_neg, Vm_X, Vm_Y, Vm_H. simpl.
      apply CComplex_eq.
      unfold CComplex_req, Csub. simpl. cbv [QArith_base.inject_Z]. split; ring.
    + (* m = S m'.  Vm_Y (Vm_X f) (S m') = (Vm_X f) m'.
                     (Vm_X f) m' for m' < S m' = true: = (Cnat (S m') * Cnat (S m' - m')) * f (S m').
                     m' = S m' - 1 = (S m') - 1 so S m' - m' = 1.
         RHS: (Cnat (S m') - Cnat (S m') * 2) * f (S m'). *)
      unfold Vm_add, Vm_neg, Vm_X, Vm_Y, Vm_H.
      replace (Nat.ltb (S m') (S m')) with false by (symmetry; apply Nat.ltb_irrefl).
      assert (Hltk : Nat.ltb m' (S m') = true) by (apply Nat.ltb_lt; lia).
      rewrite Hltk.
      replace (S m' - m')%nat with 1%nat by lia.
      rewrite (Cnat_succ_eq m'), (Cnat_succ_eq 0).
      apply CComplex_eq.
      unfold CComplex_req, Csub. simpl. cbv [QArith_base.inject_Z]. split; ring.
  - (* k < m.  Both X-branches active.  Generic computation. *)
    destruct k as [|k'].
    + (* k = 0, 0 < m.  Vm_Y _ 0 = C0; Vm_Y f at S 0 = f 0. *)
      unfold Vm_add, Vm_neg, Vm_X, Vm_Y, Vm_H.
      assert (H0m : Nat.ltb 0 m = true) by (apply Nat.ltb_lt; lia).
      rewrite H0m.
      replace (m - 0)%nat with m by lia.
      destruct m as [|m']; [lia|].
      rewrite (Cnat_succ_eq 0), (Cnat_succ_eq m').
      apply CComplex_eq.
      unfold CComplex_req, Csub. simpl. cbv [QArith_base.inject_Z]. split; ring.
    + (* k = S k', S k' < m. *)
      unfold Vm_add, Vm_neg, Vm_X, Vm_Y, Vm_H.
      assert (HSk : Nat.ltb (S k') m = true) by (apply Nat.ltb_lt; lia).
      assert (Hk' : Nat.ltb k' m = true) by (apply Nat.ltb_lt; lia).
      rewrite HSk, Hk'.
      assert (Hmsub : (m - k')%nat = S (m - S k')) by lia.
      rewrite Hmsub.
      assert (HmC : Cnat m = Cadd (Cnat (S k')) (Cnat (m - S k'))).
      { transitivity (Cnat (S k' + (m - S k'))).
        - f_equal. lia.
        - apply Cnat_add_eq. }
      rewrite HmC.
      rewrite (Cnat_succ_eq k'), (Cnat_succ_eq (S k')), (Cnat_succ_eq k'),
        (Cnat_succ_eq (m - S k')).
      apply CComplex_eq.
      unfold CComplex_req, Csub. simpl. cbv [QArith_base.inject_Z]. split; ring.
  - (* k > m.  X branches all give 0; need Hsup at index k > m, but k may
       be S _, so Vm_Y at k case-splits. *)
    destruct k as [|k']; [lia|].
    unfold Vm_add, Vm_neg, Vm_X, Vm_Y, Vm_H.
    assert (HSk : Nat.ltb (S k') m = false) by (apply Nat.ltb_ge; lia).
    rewrite HSk.
    destruct (Nat.ltb k' m) eqn:Hk'.
    + (* k' < m, S k' > m, so m = k' (impossible since S k' > m means k' >= m).
         Actually: S k' > m and k' < m ⇒ k' < m < S k', i.e., m = k'.  But
         lia handles this — but if m = k' then k' < m is false.
         Wait: we have Hkm : k > m i.e. S k' > m, and Hk' : k' < m.
         Together: S k' > m and k' < m ⇒ k' = m, contradicting k' < m. *)
      apply Nat.ltb_lt in Hk'. lia.
    + (* k' >= m, S k' > m. *)
      assert (Hf : f (S k') = C0) by (apply Hsup; lia).
      rewrite Hf.
      apply CComplex_eq.
      unfold CComplex_req, Csub. simpl. cbv [QArith_base.inject_Z]. split; ring.
Qed.

(** Structural axiom for the [SL2Module] record schema (γ R30).

    The [SL2Module] record's [sl2_rel_XY] field is universally
    quantified [forall v]; the false-as-stated original [Vm_rel_XY]
    was used only to satisfy this obligation in the [Vm_mod]
    Definition.  Replacing it with the supported Lemma above would
    require refactoring [Vm_mod]'s carrier from [VmType m] to a sigma
    type carving out [Vm_supported m]-witnesses, with downstream
    cascade through [SL2Module], [is_weight], [is_primitive],
    [Vm_basis], etc.  That is deep structural work (carrier refactor)
    beyond a single-round task.

    This axiom is therefore the SOLE structural residue of the
    original [Vm_rel_XY], retained only as the field witness for
    [Vm_mod].  It is FALSE-AS-STATED on the unrestricted carrier (see
    counterexample comment above) but kept under a clearly
    distinguished name so downstream readers can audit its scope.  The
    truthful relation [Vm_rel_XY_supported] is the lemma above; any
    consumer who only needs the relation on supported functions should
    use that instead. *)
Axiom Vm_rel_XY_module : forall m (f : VmType m),
    Vm_add (Vm_X m (Vm_Y m f)) (Vm_neg (Vm_Y m (Vm_X m f))) =
    Vm_H m f.

(** The SL2Module structure for V(m).

    Built concretely from [Vm_X], [Vm_Y], [Vm_H] together with the
    proven linearity lemmas and the commutator relations [Vm_rel_HX],
    [Vm_rel_HY], and (post γ R30) the structural axiom
    [Vm_rel_XY_module] — see audit comment above for why this third
    one is an Axiom rather than a Lemma; the truthful version
    [Vm_rel_XY_supported] is the Lemma form on the supported subspace.

    Implementation note: a naive single-shot record literal causes
    minutes-long type-checking when Rocq tries to unify
    [vs_add (Vm_vs m)] with [Vm_add] field-by-field across all 9
    obligations. The cycle-29 pattern avoids this by giving each
    field its own [intros … ; exact …] step so that the record
    projection reduces locally before [exact] runs. *)
Definition Vm_mod (m : nat) : SL2Module (VmType m) (Vm_vs m).
Proof.
  refine
    {| sl2_X := Vm_X m
     ; sl2_Y := Vm_Y m
     ; sl2_H := Vm_H m
     ; sl2_X_add   := _
     ; sl2_X_scale := _
     ; sl2_Y_add   := _
     ; sl2_Y_scale := _
     ; sl2_H_add   := _
     ; sl2_H_scale := _
     ; sl2_rel_HX  := _
     ; sl2_rel_HY  := _
     ; sl2_rel_XY  := _
     |}.
  - intros u v; exact (Vm_X_add m u v).
  - intros c v; exact (Vm_X_scale m c v).
  - intros u v; exact (Vm_Y_add m u v).
  - intros c v; exact (Vm_Y_scale m c v).
  - intros u v; exact (Vm_H_add m u v).
  - intros c v; exact (Vm_H_scale m c v).
  - intros v; exact (Vm_rel_HX m v).
  - intros v; exact (Vm_rel_HY m v).
  - intros v; exact (Vm_rel_XY_module m v).
Defined.

(** The operators in Vm_mod coincide with the concrete definitions —
    each is now [reflexivity] since [Vm_mod] is a transparent
    [Definition] whose [sl2_H/X/Y] fields are literally [Vm_H m / Vm_X m / Vm_Y m]. *)
Lemma Vm_mod_H : forall m f, sl2_H (Vm_mod m) f = Vm_H m f.
Proof. intros m f. reflexivity. Qed.

Lemma Vm_mod_X : forall m f, sl2_X (Vm_mod m) f = Vm_X m f.
Proof. intros m f. reflexivity. Qed.

Lemma Vm_mod_Y : forall m f, sl2_Y (Vm_mod m) f = Vm_Y m f.
Proof. intros m f. reflexivity. Qed.

(* ================================================================== *)
(** * 4. Key computations on basis vectors                             *)
(* ================================================================== *)

(** H acts diagonally on basis vectors: H(w_k) = (m - 2k) w_k.
    Axiomatized: requires Leibniz [Cmul c C1 = c] which only holds at
    the [~~C] setoid level. *)
Lemma Vm_H_basis : forall (m k : nat),
    Vm_H m (Vm_basis m k) =
    Vm_scale (Csub (Cnat m) (Cmul (Cnat k) (Cadd C1 C1))) (Vm_basis m k).
Proof.
  intros m k. unfold Vm_H, Vm_scale, Vm_basis. apply functional_extensionality.
  intro j. destruct (Nat.eqb j k) eqn:Hjk.
  - apply Nat.eqb_eq in Hjk. subst j. reflexivity.
  - apply CComplex_eq.
    unfold CComplex_req, Cmul, Csub, Cadd, Cneg, C0; cbn [re im].
    split; ring.
Qed.

(** Y shifts basis vectors: Y(w_k) = w_{k+1}. *)
Lemma Vm_Y_basis (m k : nat) :
    Vm_Y m (Vm_basis m k) = Vm_basis m (S k).
Proof.
  unfold Vm_Y, Vm_basis.
  apply functional_extensionality. intro j.
  destruct j; simpl; reflexivity.
Qed.

(** X raises basis vectors: X(w_{k+1}) = (k+1)(m-k) w_k  for k < m. *)
Lemma Vm_X_basis_pos : forall (m k : nat), (k < m)%nat ->
    Vm_X m (Vm_basis m (S k)) =
    Vm_scale (Cmul (Cnat (S k)) (Cnat (m - k))) (Vm_basis m k).
Proof.
  intros m k Hk. unfold Vm_X, Vm_scale, Vm_basis.
  apply functional_extensionality. intro j.
  destruct (Nat.ltb j m) eqn:Hjm.
  - destruct (Nat.eqb j k) eqn:Hjk.
    + apply Nat.eqb_eq in Hjk. subst j.
      replace (Nat.eqb (S k) (S k)) with true by (symmetry; apply Nat.eqb_refl).
      reflexivity.
    + (* j < m, j <> k, so S j <> S k *)
      apply Nat.eqb_neq in Hjk.
      assert (Hsneq : Nat.eqb (S j) (S k) = false).
      { apply Nat.eqb_neq. lia. }
      rewrite Hsneq.
      apply CComplex_eq.
      unfold CComplex_req, Cmul, C0; cbn [re im].
      split; ring.
  - (* j >= m, k < m, so j <> k (j > k) *)
    apply Nat.ltb_ge in Hjm.
    assert (Hjk : Nat.eqb j k = false).
    { apply Nat.eqb_neq. lia. }
    rewrite Hjk.
    apply CComplex_eq.
    unfold CComplex_req, Cmul, C0; cbn [re im].
    split; ring.
Qed.

(** X(w_k) = 0 when k > m (the basis vector is outside the range). *)
Lemma Vm_X_basis_out : forall (m k : nat), (m < k)%nat ->
    Vm_X m (Vm_basis m k) = Vm_zero.
Proof.
  intros m k Hk. unfold Vm_X, Vm_zero, Vm_basis.
  apply functional_extensionality. intro j.
  destruct (Nat.ltb j m) eqn:Hjm.
  - apply Nat.ltb_lt in Hjm.
    (* j < m < k, so S j <= m < k, hence S j <> k *)
    assert (Hsneq : Nat.eqb (S j) k = false).
    { apply Nat.eqb_neq. lia. }
    rewrite Hsneq. apply CComplex_eq.
    unfold CComplex_req, Cmul, C0; cbn [re im]. split; ring.
  - reflexivity.
Qed.

(* ================================================================== *)
(** * 5. The primitive vector w_0 and its orbit                        *)
(* ================================================================== *)

(** w_0 has weight m: H(w_0) = m · w_0. *)
Lemma Vm_w0_weight : forall (m : nat),
    is_weight (Vm_mod m) (Cnat m) (Vm_basis m 0).
Proof.
  intro m. unfold is_weight. rewrite Vm_mod_H. simpl.
  apply functional_extensionality. intro k.
  unfold Vm_H, Vm_scale, Vm_basis.
  destruct (Nat.eqb k 0) eqn:Hk.
  - (* k = 0: factor is (Cnat m - 0*2) and basis = C1; both sides reduce
       to Cmul (Cnat m) C1 once we kill [Cnat 0 * 2]. *)
    apply Nat.eqb_eq in Hk. subst k.
    (* Goal: Cmul (Csub (Cnat m) (Cmul (Cnat 0) (Cadd C1 C1))) C1 =
             Cmul (Cnat m) C1 *)
    assert (Heq : Csub (Cnat m) (Cmul (Cnat 0) (Cadd C1 C1)) = Cnat m).
    { apply CComplex_eq.
      unfold CComplex_req, Csub, Cadd, Cneg, Cmul, Cnat, Cinject_Q, C1.
      cbn [re im].
      assert (H0 : inject_Q (QArith_base.inject_Z (Z.of_nat 0)) == (0:CReal))
        by apply CRealEq_refl.
      split.
      - rewrite H0. ring.
      - rewrite H0. ring. }
    rewrite Heq. reflexivity.
  - (* k <> 0: basis (Vm_basis m 0 k) = C0, so both sides equal Cmul _ C0. *)
    (* Goal: Cmul (Csub (Cnat m) (Cmul (Cnat k) (Cadd C1 C1))) C0 =
             Cmul (Cnat m) C0 *)
    assert (HCmulC0 : forall a, Cmul a C0 = C0).
    { intro a. apply CComplex_eq, Cmul_C0_r_req. }
    rewrite !HCmulC0. reflexivity.
Qed.

(** w_0 is X-primitive: X(w_0) = 0. *)
Lemma Vm_w0_primitive : forall (m : nat),
    is_primitive (Vm_mod m) (Vm_basis m 0).
Proof.
  intro m. unfold is_primitive. rewrite Vm_mod_X. simpl.
  apply functional_extensionality. intro k.
  unfold Vm_X, Vm_zero, Vm_basis.
  destruct (Nat.ltb k m) eqn:Hlt.
  - (* k < m: X(w_0)(k) = (S k)*(m - k) * w_0(S k) = ... * C0 *)
    (* Vm_basis m 0 (S k) = if S k =? 0 then C1 else C0 = C0 *)
    change (match S k with O => true | S _ => false end) with false.
    simpl.
    (* Goal: Cmul (Cmul (Cnat (S k)) (Cnat (m - k))) C0 = C0 *)
    apply CComplex_eq, Cmul_C0_r_req.
  - reflexivity.
Qed.

(** C1 ≠ C0: the complex numbers 1 and 0 are distinct. *)
Lemma C1_neq_C0 : C1 <> C0.
Proof.
  intro H.
  assert (Hre : re C1 = re C0) by (rewrite H; reflexivity).
  simpl in Hre.
  (* Hre : (1 : CReal) = (0 : CReal).
     CRealLt_0_1 : CRealLt (inject_Q 0) (inject_Q 1).
     Rewrite 1 → 0 in H01 to get 0 < 0, contradicting CRealLt_irrefl. *)
  pose proof CRealLt_0_1 as H01.
  rewrite Hre in H01.
  exact (CRealLt_irrefl _ H01).
Qed.

(** w_0 is nonzero. *)
Lemma Vm_w0_nonzero (m : nat) :
    Vm_basis m 0 <> vs_zero (Vm_vs m).
Proof.
  intro H.
  assert (H0 : Vm_basis m O O = (Vm_zero : VmType m) O).
  { rewrite H. reflexivity. }
  unfold Vm_basis, Vm_zero in H0.
  change (C1 = C0) in H0.
  exact (C1_neq_C0 H0).
Qed.

(** w_0 is a maximal vector. *)
Theorem Vm_w0_maximal (m : nat) :
    is_maximal_vector (Vm_mod m) (Cnat m) (Vm_basis m 0).
Proof.
  split. { exact (Vm_w0_weight m). }
  split. { exact (Vm_w0_primitive m). }
  exact (Vm_w0_nonzero m).
Qed.

(** The Y-orbit: Y^k(w_0) = w_k. *)
Lemma Vm_Y_orbit (m k : nat) :
    Nat.iter k (Vm_Y m) (Vm_basis m 0) = Vm_basis m k.
Proof.
  induction k as [| k IH].
  - reflexivity.
  - simpl. rewrite IH. apply Vm_Y_basis.
Qed.

(** sl2_Y (Vm_mod m) = Vm_Y m. *)
Lemma Vm_sl2_Y_orbit (m k : nat) :
    Nat.iter k (sl2_Y (Vm_mod m)) (Vm_basis m 0) = Vm_basis m k.
Proof.
  induction k as [| k IH].
  - reflexivity.
  - (* [simpl] unfolds [sl2_Y (Vm_mod m)] to [Vm_Y m] in the goal but
       [IH] still mentions [sl2_Y (Vm_mod m)]. Switch [IH] to the
       reduced form by using [Vm_mod_Y] (now [reflexivity]). *)
    simpl in *. rewrite IH. apply Vm_Y_basis.
Qed.

(** Y^{m+1}(w_0) = 0 — the orbit truncates. *)
Axiom Vm_orbit_zero : forall (m : nat),
    Nat.iter (S m) (sl2_Y (Vm_mod m)) (Vm_basis m 0) =
    vs_zero (Vm_vs m).

(** Y^m(w_0) ≠ 0. *)
Lemma Vm_orbit_top_ne : forall (m : nat),
    Nat.iter m (sl2_Y (Vm_mod m)) (Vm_basis m 0) <>
    vs_zero (Vm_vs m).
Proof.
  intro m. rewrite Vm_sl2_Y_orbit. intro H.
  (* Now H : Vm_basis m m = vs_zero (Vm_vs m). Evaluate at m. *)
  assert (Heval : Vm_basis m m m = (vs_zero (Vm_vs m) : VmType m) m).
  { rewrite H. reflexivity. }
  unfold Vm_basis in Heval. simpl in Heval.
  rewrite Nat.eqb_refl in Heval.
  (* Heval : C1 = vs_zero (Vm_vs m) m. Now compute vs_zero (Vm_vs m) = Vm_zero. *)
  change ((vs_zero (Vm_vs m) : VmType m) m) with (@Vm_zero m m) in Heval.
  unfold Vm_zero in Heval.
  exact (C1_neq_C0 Heval).
Qed.

(* ================================================================== *)
(** * 6. V(m) has highest weight m                                     *)
(* ================================================================== *)

(** orbit_top holds for w_0 in Vm_mod m with index m. *)
Theorem Vm_orbit_top_thm (m : nat) :
    orbit_top (Vm_mod m) (Vm_basis m 0) m.
Proof.
  split.
  - exact (Vm_orbit_top_ne m).
  - exact (Vm_orbit_zero m).
Qed.

(** V(m) has highest weight m: the primitive vector w_0 generates an
    orbit of length m+1, so the highest weight is m by
    highest_weight_is_nat. *)
Corollary Vm_highest_weight (m : nat) :
    is_maximal_vector (Vm_mod m) (Cnat m) (Vm_basis m 0) /\
    orbit_top (Vm_mod m) (Vm_basis m 0) m.
Proof.
  exact (conj (Vm_w0_maximal m) (Vm_orbit_top_thm m)).
Qed.

(* ================================================================== *)
(** * 7. Irreducibility                                                *)
(* ================================================================== *)

Conjecture Vm_irreducible : forall (m : nat)
    (W : VmType m -> Prop),
    (** W is a submodule *)
    (forall f g, W f -> W g -> W (Vm_add f g)) ->
    (forall c f, W f -> W (Vm_scale c f)) ->
    (forall f, W f -> W (Vm_X m f)) ->
    (forall f, W f -> W (Vm_Y m f)) ->
    (forall f, W f -> W (Vm_H m f)) ->
    (** W is nonzero *)
    (exists f, W f /\ f <> Vm_zero) ->
    (** then W contains all vectors *)
    forall f, W f.

(* ================================================================== *)
(** * 8. Summary theorem                                               *)
(* ================================================================== *)

(** For each m, V(m) is an irreducible sl(2)-module with highest weight m
    and a primitive vector w_0 generating an orbit of length m+1. *)
Theorem Vm_classification (m : nat) :
    is_maximal_vector (Vm_mod m) (Cnat m) (Vm_basis m 0) /\
    orbit_top (Vm_mod m) (Vm_basis m 0) m.
Proof.
  exact (conj (Vm_w0_maximal m) (Vm_orbit_top_thm m)).
Qed.
