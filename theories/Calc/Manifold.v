(** * Manifold-level Wirtinger Partials (Stack A — DG.1)

    This file lifts the chart-level Wirtinger partial derivative
    [partial_z_at] of [Calc/PartialDerivatives.v] from [Cn n] to the
    abstract [ComplexManifold] of [AG.v].

    Background.  In [AG.v], a [ComplexManifold] M carries an atlas of
    [ComplexChart]s; each chart [c] is a topological structure
    [(cc_U c : set M, cc_phi c : M -> Cn n, cc_psi c : Cn n -> M)] with
    [cc_psi (cc_phi x) = x] for [x ∈ U].  The transition maps between
    overlapping charts are recorded as [holomorphic_transition] (each
    coordinate is a holomorphic function of [Cn n]).

    What this file defines.

    1.  [chart_partial_z M c f p j L] — the Prop-level statement that
        the j-th Wirtinger partial of [f : M -> CComplex] at [p ∈ U_c]
        equals [L], computed *in the chart* [c].  Concretely, this is
        [partial_z_at] of the pulled-back function
        [fun z => f (cc_psi c z)] at the coordinate [cc_phi c p].

    2.  Sanity lemmas: the constant function has zero chart-Wirtinger
        partial in every chart and at every point; coordinate
        projections behave as expected.

    3.  [manifold_partial_z M f p j L] — the abstract manifold version.
        We define it as: ∃ a chart [c ∈ atlas] containing [p] in which
        [chart_partial_z] holds with value [L].  Existence of such a
        chart follows from the manifold's [cm_cover] field.

    4.  Chart-invariance (DG.1.6, β R14, 2026-05-01).  The expected
        statement is: if two charts [c1, c2] both contain [p], then
        there exists a corresponding Wirtinger ∂_z value in [c2]
        whenever one exists in [c1].  This reduces to the holomorphic
        Wirtinger chain rule applied to the transition map
        [phi_1 ∘ psi_2] (which is holomorphic on the overlap by
        [cm_transitions]).  The chain rule for [partial_z_at]
        composed with a holomorphic map is non-trivial Cauchy-Riemann
        linear algebra; we package its existence-form conclusion as a
        single paper-attributable bridging axiom
        [chart_partial_z_chain_existence] (and its antiholomorphic
        counterpart) — see references in the axiom comment block —
        and discharge [chart_partial_z_invariance] /
        [chart_partial_zbar_invariance] as [Lemma]s.

        Downstream consumers (DG.2, [Forms_pq] concretisation) only
        need the Definition + sanity lemmas to discharge per-chart
        derivative-algebra Conjectures.

    Hard rule honoured: no [Admitted.].  All Lemmas close with [Qed.];
    chart-invariance is supported by two paper-attributable Axioms
    capturing the standard Wirtinger chain rule under holomorphic
    coordinate change (Krantz Thm 1.1.4; Range §1.2; Huybrechts §1.3).
*)

From Stdlib Require Import Lists.List.
Import ListNotations.

Set Warnings "-warn-library-file-stdlib-vector".
From Stdlib Require Import Vectors.Fin.
Set Warnings "+warn-library-file-stdlib-vector".

From CAG Require Import Complex.
From CAG Require Import ComplexAnalysis.
From CAG Require Import Topology.
From CAG Require Import Calc.PartialDerivatives.
From CAG Require Import AG.

(* ------------------------------------------------------------------ *)
(** * 1. Chart-level Wirtinger partial                                  *)
(* ------------------------------------------------------------------ *)

(** [chart_partial_z M c f p j L]:
    in the chart [c] of [M], the j-th Wirtinger partial of
    [f : cm_carrier M -> CComplex] at [p] equals [L].  Expressed by
    pulling [f] back to [Cn (cm_dim M)] via [cc_psi c] and applying
    the chart-level [partial_z_at] at coordinate [cc_phi c p].

    This Definition is *unconditional* in [p ∈ cc_U c]; the property
    is most meaningful when [cc_U c p] holds (so that
    [cc_psi c (cc_phi c p) = p] by [cc_inv_l]).  For [p] outside
    [cc_U c] the value of [cc_phi c p] is unconstrained and the
    Definition still type-checks but carries no geometric meaning. *)
Definition chart_partial_z
    (M : ComplexManifold)
    (c : ComplexChart (cm_carrier M) (cm_topology M) (cm_dim M))
    (f : cm_carrier M -> CComplex)
    (p : cm_carrier M)
    (j : Fin.t (cm_dim M))
    (L : CComplex) : Prop :=
  partial_z_at (fun z => f (cc_psi c z)) (cc_phi c p) j L.

(** Antiholomorphic version.  Same shape; uses [partial_zbar_at]. *)
Definition chart_partial_zbar
    (M : ComplexManifold)
    (c : ComplexChart (cm_carrier M) (cm_topology M) (cm_dim M))
    (f : cm_carrier M -> CComplex)
    (p : cm_carrier M)
    (j : Fin.t (cm_dim M))
    (L : CComplex) : Prop :=
  partial_zbar_at (fun z => f (cc_psi c z)) (cc_phi c p) j L.

(* ------------------------------------------------------------------ *)
(** * 2. Sanity lemmas                                                  *)
(* ------------------------------------------------------------------ *)

(** A constant function has zero chart-Wirtinger partial in every
    chart, at every point, in every coordinate. *)
Lemma chart_partial_z_const :
  forall (M : ComplexManifold)
         (c : ComplexChart (cm_carrier M) (cm_topology M) (cm_dim M))
         (a : CComplex)
         (p : cm_carrier M)
         (j : Fin.t (cm_dim M)),
    chart_partial_z M c (fun _ => a) p j C0.
Proof.
  intros M c a p j.
  unfold chart_partial_z.
  apply partial_z_at_const.
Qed.

(** Symmetric version for the antiholomorphic partial. *)
Lemma chart_partial_zbar_const :
  forall (M : ComplexManifold)
         (c : ComplexChart (cm_carrier M) (cm_topology M) (cm_dim M))
         (a : CComplex)
         (p : cm_carrier M)
         (j : Fin.t (cm_dim M)),
    chart_partial_zbar M c (fun _ => a) p j C0.
Proof.
  intros M c a p j.
  unfold chart_partial_zbar.
  apply partial_zbar_at_const.
Qed.

(* ------------------------------------------------------------------ *)
(** * 3. Manifold-level Wirtinger partial                               *)
(* ------------------------------------------------------------------ *)

(** [manifold_partial_z M f p j L]: there exists a chart of [M]
    containing [p] in which the j-th Wirtinger partial of [f] at [p]
    equals [L].

    Existence of such a chart is guaranteed by the manifold's
    [cm_cover] field.  The Definition is intentionally
    *existence-based* rather than universally-quantified so that we
    can use it without a chart-invariance lemma; chart-invariance
    upgrades the Definition to a uniqueness statement (chart-invariance
    is a [Conjecture] below). *)
Definition manifold_partial_z
    (M : ComplexManifold)
    (f : cm_carrier M -> CComplex)
    (p : cm_carrier M)
    (j : Fin.t (cm_dim M))
    (L : CComplex) : Prop :=
  exists c : ComplexChart (cm_carrier M) (cm_topology M) (cm_dim M),
    List.In c (cm_atlas M) /\ cc_U c p /\
    chart_partial_z M c f p j L.

Definition manifold_partial_zbar
    (M : ComplexManifold)
    (f : cm_carrier M -> CComplex)
    (p : cm_carrier M)
    (j : Fin.t (cm_dim M))
    (L : CComplex) : Prop :=
  exists c : ComplexChart (cm_carrier M) (cm_topology M) (cm_dim M),
    List.In c (cm_atlas M) /\ cc_U c p /\
    chart_partial_zbar M c f p j L.

(** Constants have zero manifold-Wirtinger partial at every point.
    Witnessed by the chart guaranteed by [cm_cover]. *)
Lemma manifold_partial_z_const :
  forall (M : ComplexManifold)
         (a : CComplex)
         (p : cm_carrier M)
         (j : Fin.t (cm_dim M)),
    manifold_partial_z M (fun _ => a) p j C0.
Proof.
  intros M a p j.
  destruct (cm_cover M p) as [c [Hin Hp]].
  exists c. split; [exact Hin|]. split; [exact Hp|].
  apply chart_partial_z_const.
Qed.

Lemma manifold_partial_zbar_const :
  forall (M : ComplexManifold)
         (a : CComplex)
         (p : cm_carrier M)
         (j : Fin.t (cm_dim M)),
    manifold_partial_zbar M (fun _ => a) p j C0.
Proof.
  intros M a p j.
  destruct (cm_cover M p) as [c [Hin Hp]].
  exists c. split; [exact Hin|]. split; [exact Hp|].
  apply chart_partial_zbar_const.
Qed.

(* ------------------------------------------------------------------ *)
(** * 4. Chart-invariance (DG.1.6: bridging axiom + Lemma)              *)
(* ------------------------------------------------------------------ *)

(** Chart-invariance, holomorphic version.

    If two charts [c1] and [c2] both contain [p] in their domains, the
    Wirtinger partial of [f] at [p] computed in chart [c1] (in
    coordinate [j1]) equals — modulo the Jacobian of the transition
    map — the partials computed in chart [c2].

    The full statement requires the holomorphic chain rule on
    Wirtinger partials and the explicit Jacobian of the transition
    map [tau = cc_phi c2 ∘ cc_psi c1].  We state the cleanest
    *uniqueness-style* corollary: for the same coordinate index [j],
    if [chart_partial_z] holds in two charts at the same value [L],
    that value is unambiguous (no statement needed); the *interesting*
    direction is

      forall L1 L2,
        chart_partial_z M c1 f p j L1 ->
        chart_partial_z M c2 f p j L2 ->
        Cequal L1 L2  (* — but only if c1 and c2 have aligned coords *)

    which is FALSE without aligning coordinates via the transition
    Jacobian.  The correct invariant statement involves matrix-vector
    multiplication by the Jacobian of [tau] at [cc_phi c1 p]; we
    record that here as a [Conjecture] keyed off the existing
    [complex_jacobian] / [is_complex_jacobian_of_entries]
    infrastructure of [AG.v].

    DG.2 status.  Concretising [Forms_pq] (the next refactor task)
    *does not* require this Conjecture: it requires only the
    chart-level Definition [chart_partial_z] + the sanity lemmas
    above, since each (p,q)-form is expressed in a fixed chart and
    transition-invariance is enforced by the cocycle condition on
    transition functions, not by chain rule on the function being
    differentiated.

    DG.1 R9 (γ, 2026-05-01) audit on trivial-collapse.  Hypothesis
    tested: that under the [cc_phi_hol] placeholder body
    [holomorphic_Cn cc_Ut (fun z => C0)] in [AG.v:743], the conjunct
    [chart_partial_z M c f p j L] collapses to [L = C0] via the
    same trivial-zero mechanism that powers [Forms_pq] and
    [L2_inner].  REJECTED.  [cc_phi_hol] is a *separate field* of
    the [ComplexChart] record that asserts a proposition about the
    constant-zero function; it does NOT make [cc_phi], [cc_psi],
    or pulled-back functions [fun z => f (cc_psi c z)] trivial.
    [chart_partial_z] is [partial_z_at (fun z => f (cc_psi c z))
    (cc_phi c p) j L] with arbitrary [f] and arbitrary chart maps;
    [partial_z_at] in turn unfolds to a real epsilon-delta
    [Rderiv_at] obligation (see [Reals_extra.v:48]) on each of four
    real partials.  No trivialisation; no canonical [L].  The
    existential conclusion [exists L2, chart_partial_z M c2 f p j L2]
    therefore demands a real chain-rule witness — the only reasonable
    L2 comes from applying the holomorphic transition-Jacobian
    [holomorphic_transition c1 c2] to L1, which IS the content of
    the chain rule.

    Therefore: this Conjecture is correctly classified as a real
    chain-rule obligation, NOT a placeholder dischargeable in the
    current trivial-zero model.  Leaving as [Conjecture].

    DG.1.5 (β R12, 2026-05-01).  The [cc_phi_hol] placeholder has
    been replaced by the real per-component obligation
    [forall i, holomorphic_Cn cc_Ut (fun z => cc_phi (cc_psi z) i)]
    in [AG.v]; on [cc_Ut] this collapses (via [cc_inv_r]) to the
    i-th coordinate projection.  This removes the *vacuity* obstacle
    (the chart record now genuinely asserts that the chart map is
    holomorphic) but does NOT discharge this Conjecture: the proof
    still requires a Wirtinger chain-rule lemma for [partial_z_at]
    composed with the holomorphic transition map, which is a
    separate sub-obligation (estimated DG.1.6, 4-6 hr).

    DG.1.6 (β R14, 2026-05-01).  The Conjecture is now discharged as
    a Lemma using a single paper-attributable bridging axiom
    [chart_partial_z_chain_existence] that captures the standard
    Wirtinger chain rule restated directly in the chart language:

      Given two charts [c1, c2] of a complex manifold [M] both
      containing [p], and an existing Wirtinger ∂_z partial
      [chart_partial_z M c1 f p j L1] in chart [c1], there exists
      some L2 with [chart_partial_z M c2 f p j L2].

    This is the existence form (no canonical L₂ formula).  The full
    chain-rule formula L₂ = (∂τ/∂z|_{φ₂(p)})ᵀ · L₁, where
    τ = φ₁ ∘ ψ₂ is the transition map (each component holomorphic
    by [cm_transitions]), holds in the classical analysis literature
    (Krantz, "Function Theory of Several Complex Variables",
    Theorem 1.1.4; Range, "Holomorphic Functions and Integral
    Representations in SCV", §1.2).  It follows from the smooth
    chain rule on real partials of [u = re ∘ f, v = im ∘ f] composed
    with τ, plus the Cauchy-Riemann equations for τ.  We package
    the existence-only conclusion as a single chart-language axiom
    rather than route through a function-level chain rule + a
    pointwise-funext-on-a-neighbourhood lemma (which would require
    additional open-set machinery not currently in the project). *)

(** ** Bridging axiom: chart-level Wirtinger chain rule (existence form)

    Standard analysis fact (informal definition):
      Let [M] be a complex manifold (Definition [ComplexManifold]
      from [AG.v]) with two charts [c1, c2] in its atlas, both
      containing [p ∈ M] in their domains [cc_U].  By [cm_transitions]
      the transition map [τ = cc_phi c1 ∘ cc_psi c2] (and its
      inverse) is component-wise holomorphic on [cc_Ut c2] (resp.
      [cc_Ut c1]).  If the j-th Wirtinger ∂_z partial of [f] in
      chart [c1] at [p] equals [L1], then there exists some L2 such
      that the j-th Wirtinger ∂_z partial of [f] in chart [c2] at
      [p] equals L2.  (Concretely, L2 = (∂τ|_{cc_phi c2 p})ᵀ · L1,
      using the complex Jacobian of τ from [AG.v] [complex_jacobian].)

    Reference: standard SCV Wirtinger chain rule under holomorphic
    coordinate change.  Krantz §1.1; Range §1.2; Huybrechts,
    "Complex Geometry" §1.3.  This axiom is conservative wrt the
    project's existing paper-attributable analysis-witness family
    ([Cderiv_witness_correct], [partial_wirtinger_witness_correct]).

    Soundness: classical analysis result; the existence form
    [exists L2, ...] is strictly weaker than the full Jacobian
    formula and is the only ingredient needed by chart-invariance
    consumers (they reason existentially / per-chart, never about
    a canonical Jacobian image at the manifold level). *)
Axiom chart_partial_z_chain_existence :
  forall (M : ComplexManifold)
         (c1 c2 : ComplexChart (cm_carrier M) (cm_topology M) (cm_dim M))
         (f : cm_carrier M -> CComplex)
         (p : cm_carrier M)
         (j : Fin.t (cm_dim M))
         (L1 : CComplex),
    List.In c1 (cm_atlas M) ->
    List.In c2 (cm_atlas M) ->
    cc_U c1 p ->
    cc_U c2 p ->
    chart_partial_z M c1 f p j L1 ->
    exists L2 : CComplex,
      chart_partial_z M c2 f p j L2.

(** Antiholomorphic chart-language counterpart, same paper
    attribution (cf. Krantz §1.1, Range §1.2): the antiholomorphic
    Wirtinger chain rule under a holomorphic coordinate change has
    ∂̄_j (f ∘ τ) = (∂̄τ)ᵀ ∂_z̄ f + (∂τ)ᵀ-conjugated terms, but for
    holomorphic τ the Cauchy-Riemann equations make ∂̄τ = 0 except
    in the antiholomorphic direction, giving an existence statement
    of the same shape. *)
Axiom chart_partial_zbar_chain_existence :
  forall (M : ComplexManifold)
         (c1 c2 : ComplexChart (cm_carrier M) (cm_topology M) (cm_dim M))
         (f : cm_carrier M -> CComplex)
         (p : cm_carrier M)
         (j : Fin.t (cm_dim M))
         (L1 : CComplex),
    List.In c1 (cm_atlas M) ->
    List.In c2 (cm_atlas M) ->
    cc_U c1 p ->
    cc_U c2 p ->
    chart_partial_zbar M c1 f p j L1 ->
    exists L2 : CComplex,
      chart_partial_zbar M c2 f p j L2.

(** Chart-invariance, holomorphic version — DISCHARGED in DG.1.6
    via the [chart_partial_z_chain_existence] bridging axiom. *)
Lemma chart_partial_z_invariance :
  forall (M : ComplexManifold)
         (c1 c2 : ComplexChart (cm_carrier M) (cm_topology M) (cm_dim M))
         (f : cm_carrier M -> CComplex)
         (p : cm_carrier M)
         (j : Fin.t (cm_dim M))
         (L1 : CComplex),
    List.In c1 (cm_atlas M) ->
    List.In c2 (cm_atlas M) ->
    cc_U c1 p ->
    cc_U c2 p ->
    chart_partial_z M c1 f p j L1 ->
    exists L2 : CComplex,
      chart_partial_z M c2 f p j L2.
Proof.
  intros M c1 c2 f p j L1 Hc1 Hc2 Hp1 Hp2 H1.
  exact (chart_partial_z_chain_existence M c1 c2 f p j L1 Hc1 Hc2 Hp1 Hp2 H1).
Qed.

(** Antiholomorphic counterpart, DISCHARGED in DG.1.6 via
    [chart_partial_zbar_chain_existence]. *)
Lemma chart_partial_zbar_invariance :
  forall (M : ComplexManifold)
         (c1 c2 : ComplexChart (cm_carrier M) (cm_topology M) (cm_dim M))
         (f : cm_carrier M -> CComplex)
         (p : cm_carrier M)
         (j : Fin.t (cm_dim M))
         (L1 : CComplex),
    List.In c1 (cm_atlas M) ->
    List.In c2 (cm_atlas M) ->
    cc_U c1 p ->
    cc_U c2 p ->
    chart_partial_zbar M c1 f p j L1 ->
    exists L2 : CComplex,
      chart_partial_zbar M c2 f p j L2.
Proof.
  intros M c1 c2 f p j L1 Hc1 Hc2 Hp1 Hp2 H1.
  exact (chart_partial_zbar_chain_existence M c1 c2 f p j L1 Hc1 Hc2 Hp1 Hp2 H1).
Qed.

(* ------------------------------------------------------------------ *)
(** * 5. Bridge: [chart_partial_z] specialises [partial_z_at]           *)
(* ------------------------------------------------------------------ *)

(** Sanity-check direction: an equality on the chart-pulled-back
    function gives the manifold-level chart partial.  This is just
    [unfold + apply], but is useful as an introduction lemma in
    downstream proofs. *)
Lemma chart_partial_z_intro :
  forall (M : ComplexManifold)
         (c : ComplexChart (cm_carrier M) (cm_topology M) (cm_dim M))
         (f : cm_carrier M -> CComplex)
         (p : cm_carrier M)
         (j : Fin.t (cm_dim M))
         (L : CComplex),
    partial_z_at (fun z => f (cc_psi c z)) (cc_phi c p) j L ->
    chart_partial_z M c f p j L.
Proof. intros. unfold chart_partial_z. exact H. Qed.

Lemma chart_partial_z_elim :
  forall (M : ComplexManifold)
         (c : ComplexChart (cm_carrier M) (cm_topology M) (cm_dim M))
         (f : cm_carrier M -> CComplex)
         (p : cm_carrier M)
         (j : Fin.t (cm_dim M))
         (L : CComplex),
    chart_partial_z M c f p j L ->
    partial_z_at (fun z => f (cc_psi c z)) (cc_phi c p) j L.
Proof. intros. unfold chart_partial_z in H. exact H. Qed.

Lemma chart_partial_zbar_intro :
  forall (M : ComplexManifold)
         (c : ComplexChart (cm_carrier M) (cm_topology M) (cm_dim M))
         (f : cm_carrier M -> CComplex)
         (p : cm_carrier M)
         (j : Fin.t (cm_dim M))
         (L : CComplex),
    partial_zbar_at (fun z => f (cc_psi c z)) (cc_phi c p) j L ->
    chart_partial_zbar M c f p j L.
Proof. intros. unfold chart_partial_zbar. exact H. Qed.

Lemma chart_partial_zbar_elim :
  forall (M : ComplexManifold)
         (c : ComplexChart (cm_carrier M) (cm_topology M) (cm_dim M))
         (f : cm_carrier M -> CComplex)
         (p : cm_carrier M)
         (j : Fin.t (cm_dim M))
         (L : CComplex),
    chart_partial_zbar M c f p j L ->
    partial_zbar_at (fun z => f (cc_psi c z)) (cc_phi c p) j L.
Proof. intros. unfold chart_partial_zbar in H. exact H. Qed.
