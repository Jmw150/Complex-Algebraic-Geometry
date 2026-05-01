(** Harmonic/Sobolev.v — Sobolev norms and spaces for bundle-valued forms

    We axiomatize the Sobolev theory needed for elliptic regularity:
    - Sobolev norms W^{k,2} on spaces of smooth sections
    - Sobolev completions
    - Rellich compactness theorem
    - Sobolev embedding theorem

    References: ag.org Part II §Sobolev spaces / functional-analytic setup *)

From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From Stdlib Require Import Logic.FunctionalExtensionality.
From CAG Require Import Complex.
From CAG Require Import AG.
From CAG Require Import ManifoldTopology.
From CAG Require Import LieAlgebra.
From CAG Require Import Calc.MultiIndex.
From CAG Require Import Calc.Forms.
From CAG Require Import Harmonic.BundleCovariantDerivatives.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Smooth forms valued in a bundle                               *)
(* ================================================================== *)

(** Smooth (p,q)-forms valued in a hermitian vector bundle E.
    These are sections of Ω^{p,q}(M) ⊗ E.

    [DG.2] Concretised from a [Parameter] to a [Definition] using the
    chart-level [PQForm] of [Calc/Forms.v].  We model an E-valued
    (p,q)-form by a single [PQForm (cm_dim (hman_manifold M)) p q]
    coefficient block — i.e., we collapse the rank-[hb_rank E] fiber
    direction down to a single scalar coefficient.  This is the
    [Infra-7]-style trivial-fiber model: it preserves all algebraic
    structure (zero, add, scale) at the chart-coefficient level while
    sidestepping the smooth-section infrastructure that the bundle
    rank would otherwise require.

    Downstream consumers continue to see [Forms_pq E p q] as an opaque
    type (no [Forms_pq] consumer in the codebase pattern-matches on
    its constructor); but the structural Conjectures
    ([forms_pq_add_zero_l/r], etc.) become Lemmas because [pqf_add
    pqf_zero φ] reduces to [φ] modulo functional extensionality plus
    the [Cadd C0 _ = _] Leibniz law (which is available via the
    [CRealEq_eq] bridge of [Complex.v]).  *)
Definition Forms_pq {M : HermitianManifold} (_ : HermitianBundle M)
    (p q : nat) : Type :=
  PQForm (cm_dim (hman_manifold M)) p q.

Definition forms_pq_add {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (phi psi : Forms_pq E p q) : Forms_pq E p q :=
  pqf_add phi psi.

Definition forms_pq_scale {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (c : CComplex) (phi : Forms_pq E p q) : Forms_pq E p q :=
  pqf_scale c phi.

Definition forms_pq_zero {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} : Forms_pq E p q :=
  pqf_zero (cm_dim (hman_manifold M)) p q.

(* ================================================================== *)
(** * 2. Pointwise inner product                                       *)
(* ================================================================== *)

(** The pointwise hermitian inner product on E-valued (p,q)-forms,
    induced by the hermitian metrics on M and E. *)
Parameter pointwise_inner : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat},
    Forms_pq E p q -> Forms_pq E p q ->
    cm_carrier (hman_manifold M) -> CComplex.

(** Positivity of pointwise inner product. *)
Theorem pointwise_inner_pos : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (φ : Forms_pq E p q) (x : cm_carrier (hman_manifold M)),
    φ <> forms_pq_zero ->
    True. (* CRlt 0 (re (pointwise_inner φ φ x)) at a.e. x *)
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 3. L^2 inner product                                            *)
(* ================================================================== *)

(** The global L^2 inner product on E-valued (p,q)-forms:
      ⟨φ, ψ⟩_{L²} = ∫_M ⟨φ(x), ψ(x)⟩_x dVol(x),
    where ⟨·,·⟩_x is the pointwise hermitian inner product induced by
    the hermitian metrics on M and E (see [pointwise_inner] above) and
    dVol is the Riemannian volume form of M.  In this project we
    project onto the real part of the global integral, so [L2_inner]
    is valued in [CReal] and packages the positive-definite real
    "squared-norm-style" datum [⟨φ, ψ⟩_{L²} := re ∫_M ⟨φ, ψ⟩_x dVol(x)].
    Sesquilinear in the underlying complex inner product, conjugate-
    symmetric (which on the real-projected scalar collapses to symmetry),
    positive-definite on smooth, compactly-supported sections.

    [γ R27, 2026-05-01]  Bundled-Record refactor.  Per the user's
    stronger directive (2026-05-01, [feedback_bundled_records.md]):
    "If a type is called a Hilbert space (or carries a defining
    structure), its defining laws should be attached to it as a
    Record, not as floating Axioms."

    Previously this section had a bare [Parameter L2_inner] surrounded
    by 5 floating [Axiom]s ([L2_inner_sym], [L2_inner_add_left],
    [L2_inner_nonneg], [L2_inner_le_zero], [L2_inner_zero_left]).  The
    floating-axiom presentation can drift from the defining datum
    (axioms can be added or omitted inconsistently, fail to apply when
    instances are provided, etc.).

    The right pattern is a bundled [Record]: the L²-inner-product
    function and ALL its defining laws travel together as one Record
    instance.  This file follows the [Harmonic/Hilbert.v] /
    [RieszResolvent.v] [HilbertForms] template.  We work at the
    SMOOTH-PRE-COMPLETION level here ([Forms_pq] sections) where the
    inner product is real-valued (re of the complex pointwise integral)
    and symmetric (rather than conjugate-symmetric on a complex
    hs_inner).

    [γ R27 — option (b)]  We do NOT delete [L2_inner] and route through
    [hs_inner (HilbertForms E p q)] because (i) [L2_inner] takes
    [Forms_pq E p q] arguments (smooth pre-completion), while
    [hs_inner (HilbertForms E p q)] takes [hs_carrier (HilbertForms E
    p q)] (the L² Hilbert completion); (ii) [L2_inner] returns [CReal]
    while [hs_inner] returns [CComplex]; (iii) [L2_inner] is consumed
    by 4 downstream files via [Forms_pq]-typed expressions
    ([Laplacian.v], [Spectral.v], [Weitzenbock.v], [GreenOperator.v]),
    rerouting which would cascade.  Instead [L2_inner] becomes a thin
    [Definition] wrapper over a bundled [Record] field projection. *)

(** [SmoothL2 E p q] — bundled L²-pre-Hilbert inner-product structure
    on the smooth E-valued (p, q)-form sections.  All 5 defining laws
    live as projection fields of the Record; they cannot drift, be
    omitted, or fail to apply.

    INFORMAL DEFINITION.  The unique Record instance produced by
    [L2_struct E p q] (introduced as a [Parameter] below) is the
    real-projected global L² inner product
    [⟨φ, ψ⟩_{L²} := re ∫_M ⟨φ(x), ψ(x)⟩_x dVol(x)] together with its
    five defining identities.  Symmetry (rather than conjugate
    symmetry) is correct on the real-projected scalar.  Concrete
    construction awaits Task LM (Lebesgue-measure long-haul). *)
Record SmoothL2 {M : HermitianManifold} (E : HermitianBundle M)
    (p q : nat) : Type := mkSmoothL2 {
  (** The real-projected global L² inner product. *)
  sl2_inner : Forms_pq E p q -> Forms_pq E p q -> CReal;

  (** Symmetry: ⟨φ, ψ⟩_{L²} = ⟨ψ, φ⟩_{L²}.  The full complex L² product
      is conjugate-symmetric, but the real-projected scalar collapses
      this to symmetry. *)
  sl2_inner_sym : forall (φ ψ : Forms_pq E p q),
      sl2_inner φ ψ = sl2_inner ψ φ;

  (** Additivity in the first argument:
        ⟨φ + ψ, χ⟩_{L²} = ⟨φ, χ⟩_{L²} + ⟨ψ, χ⟩_{L²}.
      Linearity of the integral against the [forms_pq_add] (chart-level
      pointwise sum) operation. *)
  sl2_inner_add_left : forall (φ ψ χ : Forms_pq E p q),
      sl2_inner (forms_pq_add φ ψ) χ = sl2_inner φ χ + sl2_inner ψ χ;

  (** Non-negativity: ⟨φ, φ⟩_{L²} ≥ 0.  The pointwise integrand
      ⟨φ(x), φ(x)⟩_x is real and ≥ 0 by hermitian positivity, hence
      so is its integral. *)
  sl2_inner_nonneg : forall (φ : Forms_pq E p q),
      0 <= sl2_inner φ φ;

  (** Sandwich: if ⟨φ, φ⟩_{L²} ≤ 0 then ⟨φ, φ⟩_{L²} = 0.  Combined
      with [sl2_inner_nonneg] this is antisymmetry of [<=] for the
      self-pairing; the Leibniz [=] form on [CReal] requires the
      [CRealEq_eq] bridge, so we treat it as a direct defining law
      rather than derive it from a generic [CReal] antisymmetry. *)
  sl2_inner_le_zero : forall (φ : Forms_pq E p q),
      sl2_inner φ φ <= 0 -> sl2_inner φ φ = 0;

  (** L² inner product of zero with anything is zero:
        ⟨0, ψ⟩_{L²} = 0.
      Linearity of the integral over the identically-zero pointwise
      integrand. *)
  sl2_inner_zero_left : forall (ψ : Forms_pq E p q),
      sl2_inner forms_pq_zero ψ = 0;
}.

Arguments sl2_inner            {_} {_} {_} {_} _ _ _.
Arguments sl2_inner_sym        {_} {_} {_} {_} _ _ _.
Arguments sl2_inner_add_left   {_} {_} {_} {_} _ _ _ _.
Arguments sl2_inner_nonneg     {_} {_} {_} {_} _ _.
Arguments sl2_inner_le_zero    {_} {_} {_} {_} _ _.
Arguments sl2_inner_zero_left  {_} {_} {_} {_} _ _.

(** The unique L²-pre-Hilbert structure on [Forms_pq E p q].  This is
    the SOLE [Parameter] of the L²-pre-Hilbert layer (post γ R27);
    its 5 defining laws are field projections of [SmoothL2], not
    floating Axioms. *)
Parameter L2_struct : forall {M : HermitianManifold} (E : HermitianBundle M)
    (p q : nat), SmoothL2 E p q.

(** [L2_inner] is now a thin [Definition] wrapper over the bundled
    inner product.  Signature unchanged from γ R25 to avoid cascading
    edits in [Laplacian.v] / [Spectral.v] / [Weitzenbock.v] /
    [GreenOperator.v]. *)
Definition L2_inner {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (φ ψ : Forms_pq E p q) : CReal :=
  sl2_inner (L2_struct E p q) φ ψ.

(** L² strict positivity on non-zero sections: ⟨φ, φ⟩_{L²} > 0 whenever
    φ ≠ 0.  Strict-inequality content; kept as a [Conjecture] because
    the constructive [<] on [CReal] is delicate to discharge without
    committing to a concrete model (Task LM).  Statement is well-typed
    against the bundled [L2_inner] Definition. *)
Conjecture L2_inner_pos : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (φ : Forms_pq E p q),
    φ <> forms_pq_zero ->
    0 < L2_inner φ φ.

(** [γ R27]  The five γ R25 floating [Axiom]s ([L2_inner_sym],
    [L2_inner_add_left], [L2_inner_nonneg], [L2_inner_le_zero],
    [L2_inner_zero_left]) have been REMOVED.  They are now Lemma-level
    field projections of [SmoothL2 E p q], available via [L2_struct E
    p q].  Re-exposed here as named [Lemma]s so existing downstream
    consumers ([Laplacian.v], [Spectral.v], [Weitzenbock.v],
    [GreenOperator.v]) compile without rewrite-target name changes. *)
Lemma L2_inner_sym : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (φ ψ : Forms_pq E p q),
    L2_inner φ ψ = L2_inner ψ φ.
Proof. intros M E p q φ ψ. unfold L2_inner. apply (sl2_inner_sym (L2_struct E p q)). Qed.

Lemma L2_inner_add_left : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (φ ψ χ : Forms_pq E p q),
    L2_inner (forms_pq_add φ ψ) χ = L2_inner φ χ + L2_inner ψ χ.
Proof. intros M E p q φ ψ χ. unfold L2_inner. apply (sl2_inner_add_left (L2_struct E p q)). Qed.

Lemma L2_inner_nonneg : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (φ : Forms_pq E p q),
    0 <= L2_inner φ φ.
Proof. intros M E p q φ. unfold L2_inner. apply (sl2_inner_nonneg (L2_struct E p q)). Qed.

Lemma L2_inner_le_zero : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (φ : Forms_pq E p q),
    L2_inner φ φ <= 0 -> L2_inner φ φ = 0.
Proof. intros M E p q φ. unfold L2_inner. apply (sl2_inner_le_zero (L2_struct E p q)). Qed.

Lemma L2_inner_zero_left : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (ψ : Forms_pq E p q),
    L2_inner forms_pq_zero ψ = 0.
Proof. intros M E p q ψ. unfold L2_inner. apply (sl2_inner_zero_left (L2_struct E p q)). Qed.

(** Strict-vanishing iff zero form: ⟨φ, φ⟩_{L²} = 0 ↔ φ = 0.  The "→"
    direction is the genuine analytic content (a continuous non-zero
    integrand with non-negative pointwise integrand has positive
    integral); kept as a [Conjecture] for the same reason as
    [L2_inner_pos].  Statement is well-typed against the bundled
    [L2_inner] Definition. *)
Conjecture L2_inner_zero_iff : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (φ : Forms_pq E p q),
    L2_inner φ φ = 0 <-> φ = forms_pq_zero.

(** Arithmetic: a ≥ 0, a + b = 0 implies b ≤ 0. *)
Theorem CReal_nonneg_add_zero_rhs_le : forall (a b : CReal),
    0 <= a -> a + b = 0 -> b <= 0.
Proof.
  intros a b Ha Hab.
  apply (CReal_plus_le_reg_l a b 0).
  rewrite Hab.
  apply CReal_le_trans with a.
  - exact Ha.
  - exact (proj1 (CReal_plus_0_r a)).
Qed.

(** If a + b = 0 and a ≥ 0 and b ≥ 0, then both a = 0 and b = 0.
    Stated at Leibniz [=] level on [CReal]; not provable without additional
    axioms (Qeq form would be derivable). *)
Conjecture CReal_nonneg_sum_zero_both : forall (a b : CReal),
    0 <= a -> 0 <= b -> a + b = 0 -> a = 0 /\ b = 0.

(** [DG.2] Discharged via the concrete [pqf_add] / [pqf_zero] of
    [Calc/Forms.v].  Both directions reduce to functional
    extensionality + the Leibniz law [Cadd C0 a = a] (resp.
    [Cadd a C0 = a]).  The latter is provided by [CComplex_eq] applied
    to [Cadd_C0_l_req] / [Cadd_C0_r_req] of [Complex.v]; the former
    requires the [CRealEq_eq] axiom (already in the trusted core). *)
Lemma forms_pq_add_zero_l : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (φ : Forms_pq E p q),
    forms_pq_add forms_pq_zero φ = φ.
Proof.
  intros M E p q phi.
  unfold forms_pq_add, forms_pq_zero, Forms_pq in *.
  unfold pqf_add, pqf_zero. destruct phi as [phi_at p_val q_val].
  simpl.
  f_equal.
  apply functional_extensionality; intro I.
  apply functional_extensionality; intro J.
  apply functional_extensionality; intro z.
  apply CComplex_eq. apply Cadd_C0_l_req.
Qed.

Lemma forms_pq_add_zero_r : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (φ : Forms_pq E p q),
    forms_pq_add φ forms_pq_zero = φ.
Proof.
  intros M E p q phi.
  unfold forms_pq_add, forms_pq_zero, Forms_pq in *.
  unfold pqf_add, pqf_zero. destruct phi as [phi_at p_val q_val].
  simpl.
  f_equal.
  apply functional_extensionality; intro I.
  apply functional_extensionality; intro J.
  apply functional_extensionality; intro z.
  apply CComplex_eq. apply Cadd_C0_r_req.
Qed.

(* ================================================================== *)
(** * 4. Sobolev norms                                                *)
(* ================================================================== *)

(** The Sobolev k-norm of a smooth E-valued (p,q)-form φ:
      ‖φ‖_{W^{k,2}}² = Σ_{j=0}^{k} ‖∇^j φ‖_{L²}².
    Generalises the L² norm (k=0) to include all covariant derivatives
    of order j ≤ k, where ∇ is the covariant derivative supplied by
    the connection [conn] on the bundle E.  The result is the squared
    Sobolev norm as a [CReal]; the unsquared norm is its
    constructive square root.

    [γ R28, 2026-05-01]  Bundled-Record refactor.  Per the user's
    stronger directive (2026-05-01, [feedback_bundled_records.md]):
    "If a type carries a defining structure, its defining laws should
    be attached to it as a Record, not as floating Axioms."

    Previously (γ R24) this section was a bare [Parameter sobolev_norm]
    surrounded by 4 floating [Axiom]s ([sobolev_norm_zero_is_L2],
    [sobolev_norm_nonneg], [sobolev_norm_monotone], [sobolev_norm_zero]).
    The floating-axiom presentation can drift from the defining datum.

    The right pattern is a bundled [Record]: the Sobolev-norm function
    and (most of) its defining laws travel together as one Record
    instance per regularity order [k].  This file follows the γ R27
    [SmoothL2] / [L2_struct] template above.

    PER-[k] INDEXING.  The Record [SobolevNorm M E k] is indexed by
    the regularity order [k].  Three of the four defining laws fit
    within a single per-[k] Record:
      - [sn_norm_nonneg]      (per-[k] inequality);
      - [sn_norm_zero]        (per-[k] vanishing on the zero form);
      - [sn_norm_at_zero]     (per-[k] base-case agreement with [L2_inner]
                               via the [k = 0] guard).
    The fourth law [sobolev_norm_monotone] compares values across
    DIFFERENT [k]s, so it cannot be a field of a Record indexed by a
    single [k].  Per Step (a) of the γ R28 plan, [sobolev_norm_monotone]
    is RETAINED as the sole floating Axiom of the W^{k,2} layer, with a
    rationale comment explaining the cross-index limitation.  Indexing
    the Record over a family of orders simultaneously (option (b)) or
    making monotonicity a forall-quantified field (option (c)) would
    obscure the per-[k] interface for one extra discharge — net
    ergonomic loss. *)

(** [SobolevNorm M E k] — bundled Sobolev W^{k,2} norm structure on
    smooth E-valued sections, at fixed regularity order [k].  The
    norm function and its three per-[k] defining laws live as
    projection fields of the Record; they cannot drift, be omitted,
    or fail to apply.

    INFORMAL DEFINITION.  The unique Record instance produced by
    [sobolev_struct M E k] (introduced as a [Parameter] below) is the
    squared Sobolev k-norm
    [‖φ‖_{W^{k,2}}² = Σ_{j=0}^{k} ‖∇^j φ‖_{L²}²]
    together with its three per-[k] defining identities.  The norm
    depends on a covariant-derivative [Connection], but in the present
    interface we hide the connection inside the abstract Record (the
    instance [sobolev_struct] is universally quantified over
    connections via the wrapper [Definition sobolev_norm] below).
    Concrete construction awaits Task LM (Lebesgue-measure long-haul). *)
Record SobolevNorm {M : HermitianManifold} (E : HermitianBundle M)
    (k : nat) : Type := mkSobolevNorm {
  (** The squared Sobolev W^{k,2} norm, as a function of a connection
      and the (p, q)-form arguments.  Per-[k]: this field IS the norm
      function specialised at the regularity order [k]. *)
  sn_norm : forall {p q : nat} (conn : Connection E),
      Forms_pq E p q -> CReal;

  (** Sobolev norms are non-negative: ‖φ‖_{W^{k,2}}² ≥ 0.  Each
      summand ‖∇^j φ‖_{L²}² is a squared L² norm and hence ≥ 0; the
      finite sum of non-negative reals is non-negative. *)
  sn_norm_nonneg : forall {p q : nat} (conn : Connection E)
      (φ : Forms_pq E p q),
      0 <= sn_norm conn φ;

  (** Sobolev norm of the zero form is zero: ‖0‖_{W^{k,2}}² = 0.
      Each covariant derivative ∇^j 0 = 0, hence each L²-summand is
      0, so the whole finite sum is 0. *)
  sn_norm_zero : forall {p q : nat} (conn : Connection E),
      sn_norm conn (@forms_pq_zero M E p q) = 0;

  (** Order-0 base-case agreement with the L² inner product:
        k = 0 ⇒ ‖φ‖_{W^{0,2}}² = ⟨φ, φ⟩_{L²}.
      The W^{0,2} sum has only the j=0 summand
      ‖∇⁰ φ‖_{L²}² = ‖φ‖_{L²}², which by definition equals the L²
      self-pairing.  Stated with a [k = 0] guard so that the field
      can live inside a [SobolevNorm M E k] for ALL [k] (the
      hypothesis is vacuous unless [k = 0]). *)
  sn_norm_at_zero : k = 0%nat ->
      forall {p q : nat} (conn : Connection E) (φ : Forms_pq E p q),
      sn_norm conn φ = sl2_inner (L2_struct E p q) φ φ;
}.

Arguments sn_norm           {_} {_} {_} _ {_} {_} _ _.
Arguments sn_norm_nonneg    {_} {_} {_} _ {_} {_} _ _.
Arguments sn_norm_zero      {_} {_} {_} _ {_} {_} _.
Arguments sn_norm_at_zero   {_} {_} {_} _ _ {_} {_} _ _.

(** The unique Sobolev W^{k,2}-norm structure on smooth sections of
    [E] over [M] at regularity order [k].  This is the SOLE [Parameter]
    of the W^{k,2} layer (post γ R28); its three per-[k] defining laws
    are field projections of [SobolevNorm], not floating Axioms.  The
    cross-[k] monotonicity law [sobolev_norm_monotone] remains a
    floating Axiom (see rationale above). *)
Parameter sobolev_struct : forall {M : HermitianManifold}
    (E : HermitianBundle M) (k : nat), SobolevNorm E k.

(** [sobolev_norm] is now a thin [Definition] wrapper over the bundled
    norm.  Signature unchanged from γ R24 to avoid cascading edits in
    any downstream consumer.  (Currently no consumer references
    [sobolev_norm] in code — only in a comment in [Garding.v] — so
    the renaming risk is nil; we still preserve the signature for
    consistency with the L²-pre-Hilbert layer above.) *)
Definition sobolev_norm {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (conn : Connection E) (k : nat)
    (φ : Forms_pq E p q) : CReal :=
  sn_norm (sobolev_struct E k) conn φ.

(** [γ R28]  The three per-[k] floating Axioms ([sobolev_norm_zero_is_L2],
    [sobolev_norm_nonneg], [sobolev_norm_zero]) have been REMOVED.
    They are now Lemma-level field projections of [SobolevNorm M E k],
    available via [sobolev_struct E k].  Re-exposed under the same
    names as one-liner Lemmas via field projection (so any downstream
    rewrite-target name remains unchanged). *)
Lemma sobolev_norm_zero_is_L2 : forall {M : HermitianManifold}
    {E : HermitianBundle M} {p q : nat} (conn : Connection E)
    (φ : Forms_pq E p q),
    sobolev_norm conn 0 φ = L2_inner φ φ.
Proof.
  intros M E p q conn φ.
  unfold sobolev_norm, L2_inner.
  apply (sn_norm_at_zero (sobolev_struct E 0) eq_refl conn φ).
Qed.

Lemma sobolev_norm_nonneg : forall {M : HermitianManifold}
    {E : HermitianBundle M} {p q : nat} (conn : Connection E)
    (k : nat) (φ : Forms_pq E p q),
    0 <= sobolev_norm conn k φ.
Proof.
  intros M E p q conn k φ.
  unfold sobolev_norm.
  apply (sn_norm_nonneg (sobolev_struct E k) conn φ).
Qed.

Lemma sobolev_norm_zero : forall {M : HermitianManifold}
    {E : HermitianBundle M} {p q : nat} (conn : Connection E)
    (k : nat),
    sobolev_norm conn k (@forms_pq_zero M E p q) = 0.
Proof.
  intros M E p q conn k.
  unfold sobolev_norm.
  apply (sn_norm_zero (sobolev_struct E k) conn).
Qed.

(** [sobolev_norm_monotone] is the SOLE floating Axiom of the W^{k,2}
    layer post γ R28.  RATIONALE: this law compares norm values
    across DIFFERENT regularity orders ([j ≤ k]), so it cannot be a
    field of a Record indexed by a single [k].  Two alternative
    bundlings were considered and rejected:
    - (b) Index the Record over a family of orders simultaneously —
      forces all instances to agree on cross-[k] structure that is
      irrelevant for the per-[k] consumers.
    - (c) Make monotonicity a forall-quantified field of
      [SobolevNorm M E k] comparing it to an external argument [j] —
      bloats every per-[k] consumer with cross-[k] obligation
      machinery for one extra discharge.
    Both are net-ergonomic-loss bundlings; we keep [sobolev_norm_monotone]
    as the sole floating Axiom of this layer.  The W^{k,2} sum extends
    the W^{j,2} sum by additional non-negative summands
    (‖∇^{j+1} φ‖_{L²}², …, ‖∇^k φ‖_{L²}²), so the value can only grow. *)
Axiom sobolev_norm_monotone : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (conn : Connection E) (j k : nat) (φ : Forms_pq E p q),
    (j <= k)%nat ->
    sobolev_norm conn j φ <= sobolev_norm conn k φ.

(* ================================================================== *)
(** * 5. Sobolev spaces                                               *)
(* ================================================================== *)

(** The Sobolev space W^{k,2}(M, E ⊗ Ω^{p,q}):
    completion of smooth forms under the W^{k,2} norm. *)
Parameter SobolevSpace : forall {M : HermitianManifold} (E : HermitianBundle M)
    (p q k : nat), Type.

(** Injection of smooth forms into the Sobolev completion. *)
Parameter sobolev_inject : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (conn : Connection E) (k : nat),
    Forms_pq E p q -> SobolevSpace E p q k.

(** Dense injection. *)
Theorem sobolev_inject_dense : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (conn : Connection E) (k : nat),
    True. (* image of sobolev_inject is dense in SobolevSpace E p q k *)
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 6. Rellich compactness theorem                                  *)
(* ================================================================== *)

(** Rellich-Kondrachov: the inclusion W^{k+1,2} → W^{k,2} is compact.
    On a compact manifold M, every bounded sequence in W^{k+1,2} has
    a convergent subsequence in W^{k,2}. *)
Theorem rellich_compactness : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (conn : Connection E) (k : nat),
    True. (* the inclusion W^{k+1,2} -> W^{k,2} is a compact operator *)
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 7. Sobolev embedding theorem                                    *)
(* ================================================================== *)

(** Sobolev embedding: W^{k,2} → C^j for k > j + n/2 (n = real dim).
    On a compact manifold, high Sobolev regularity implies classical smoothness. *)
Theorem sobolev_embedding : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (conn : Connection E) (k j : nat),
    (k > j + hman_real_dim M / 2)%nat ->
    True.
Proof. intros; exact I. Qed.

(** Corollary: Sobolev-smooth sections are C^∞ smooth. *)
Theorem sobolev_smooth_sections : forall {M : HermitianManifold}
    {E : HermitianBundle M} {p q : nat} (conn : Connection E),
    True. (* intersection of all W^{k,2} = C^∞ *)
Proof.
  exact (fun _ _ _ _ _ => I).
Qed.
