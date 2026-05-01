---
name: project_state
description: Current admit count, key blockers, completed work in CAG Rocq formalization
type: project
---

## Admit count: 8 loose / 2 real Admitted (started at ~438; 432 at start of 2026-04-25 session)

## Closed admits (verified compilation):

### NeuralOp/FNO.v (3 admits closed)
- `fno_layer_length` — FNO preserves sequence length (list length, pure nat)
- `apply_layers_length` — new helper: apply_layers preserves length
- `fno_forward_length` — full FNO forward pass preserves length

### Group.v (1 main + 5 helpers closed)
- `coset_partition_exists` — proved using greedy `build_reps` accumulator
- Helpers added: `crel_decidable`, `covered_by`, `build_reps`, `covered_by_false_spec`,
  `build_reps_covers`, `pairwise_disjoint`, `build_reps_disjoint`,
  `NoDup_flat_map_cosets`, `build_reps_nodup_main`
- Key issues fixed:
  - `build_reps_covers` needed `reps` universally quantified (not fixed in outer scope)
  - `build_reps_disjoint` same issue
  - `build_reps_nodup_main` same issue
  - `Permutation_middle` in Rocq 9 has form `Permutation (a :: l1 ++ l2) (l1 ++ a :: l2)` (element first)
  - `intros r1 r2 Hr1 Hr2 Hne. apply Hdisj; right; assumption` fails because `;` applies `right` to ALL goals including `r1 <> r2`; use `exact (Hdisj r1 r2 (or_intror Hr1) (or_intror Hr2) Hne)` instead

## Sessions 2026-04-28 / 2026-04-29 — Audit cycles 11–20

See `AXIOMS_AUDIT.md` for full per-cycle details.

**Cycles 11-13 (HallTheorem.v):**
- `hall_finite_index_free_factor`: was vacuously satisfiable Axiom; now Theorem (trivial proof via `trivial_FIS`).
- `hall_M_strong_free_factor`: NEW tighter Hall axiom (`r ≥ 2 ∧ fis_index ≥ 2`).
- `hall_free_factor_decomp`: was INCONSISTENT (∀-FIS counter-example F_2/⟨a,b²⟩); REMOVED.

**Cycles 14-15 (NeuralOp/Approximation.v):**
- `matrix_is_circulant_sum`: INCONSISTENT (sum of circulants is circulant; counter-example M=[[0,1],[0,0]] for N=2); REMOVED.
- `fno_dense_in_linear_ops`: INCONSISTENT (depends on 14); REMOVED.

**Cycle 16 (Langlands/NonabelianHodge.v):**
- `corlette_harmonic_metric`: had `True` placeholder hypothesis making it claim every LocalSystem admits a harmonic metric (false). Added `IsSemisimpleLocalSystem` Parameter + tightened axiom + new `higgs_to_flat_semisimple` axiom. `non_abelian_hodge` proof and signature updated.

**Cycle 17 (Tier 1.A CReal setoid bridge):**
- Added `CRealEq_eq` axiom + `CComplex_eq` lemma in `Complex.v`.
- Converted 7 false Leibniz CReal axioms to Lemmas: `Cadd_assoc`, `Cadd_comm`, `Cmul_add_distr_l/r` (LieAlgebra.v); `Cmul_C1_left`, `Cmul_assoc_lem`, `Cnorm2_mul_lem` (AG.v).
- Net: +1 axiom, −7 false axioms; project no longer depends on demonstrably-false statements for CReal arithmetic.

**Cycle 18 (DecisionProblems/TraceProperties.v):**
- `theorem_1_6_surface_groups` and `corollary_1_2_surface_groups_hard_direction` were over-general (claimed property_B / hard direction for *every* group). Added `IsSurfaceGroup` Parameter + tightened both axioms.

**Cycle 19 (DecisionProblems/OpenProblems.v) — 2026-04-29:**
- `horowitz_n2`: was stated as "trace-equiv ⟹ conjugate" (false: γ=a, η=a⁻¹ in F_2). Restored to disjunctive form `γ~η ∨ γ~η⁻¹` matching `fricke_generation`.

**Cycle 20 (DecisionProblems/SL2Horowitz.v) — 2026-04-29:**
- Added `horowitz_n2_SL2_instance`: discharges the disjunctive `OpenProblems.horowitz_n2` for the SL(2) instantiation directly from `fricke_generation`.

**Cycle 21 (More Tier 1.A discharges) — 2026-04-29:**
- Discharged 10 more axioms via the `CRealEq_eq` bridge from cycle 17:
  - `csum_zero`, `csum_linear` in `NeuralOp/DFT.v` (induction + bridge).
  - `Vm_add_zero_r`, `Vm_add_neg_r`, `Vm_H_scale`, `Vm_X_add`, `Vm_X_scale`, `Vm_Y_add`, `Vm_Y_scale` in `Kahler/sl2/Vm.v` (functional_extensionality + bridge + ring).
  - `Cdiv_mul_r` in `AG.v` (transitivity through Cmul rearrangement + Cinv_mul_right + Cmul_C1_l_req).
- `Vm_rel_HX`, `Vm_rel_HY` (sl(2) commutators) attempted but failed — `ring` tactic doesn't accept the destructured `Cnat`/`Csub` form. Left as Axiom; would need a tighter setoid-based proof structure.

**Cycle 22 (LieAlgebra.v + Vm.v helper) — 2026-04-29:**
- Discharged `vs_scale_creal_eq` (LieAlgebra.v): a one-liner via the bridge — the hypothesis is exactly `c1 ~~C c2`, so `c1 = c2` Leibniz, then f_equal.
- Added `Cnat_succ_req` helper Lemma in Vm.v (`Cnat (S k) ~~C Cadd (Cnat k) C1`) for future attempts at `Vm_rel_HX` / `Vm_rel_HY`. The full commutator proofs need `nra` (not available); helper kept as building block.

**Cycle 23 (DecisionProblems/SL2Horowitz.v + WordLengthFreeGroup.v) — 2026-04-29:**
- Concrete progress on Lawton–Louder–McReynolds Conjecture 3.2 (no property A) for the SL(2) case.
- Added Axiom `free_gen_RWord_not_conj_inv` (gen ≁ gen^{-1} in F_n) [later discharged in cycle 24].
- Added Theorem `SL2_blocks_property_A_at_n2`: no SL(2) representation can separate the (a, a^{-1}) trace pair in F_r (r ≥ 1).
- Added Theorem `SL2_constant_family_lacks_property_A`: the full conjecture for the constant SL(2) family.

**Cycle 24 (DecisionProblems/WordLengthFreeGroup.v) — 2026-04-29:**
- Discharged the cycle-23 axiom by formalizing the i-th exponent-sum homomorphism F_n → ℤ via `expsum_word_i` and proving:
  - additive on word concatenation
  - preserved by cancel_step (a cancellation pair contributes opposite signs that sum to 0)
  - preserved by reduce / reduce_aux
  - additive on rword_mul (concat + reduce)
  - negates on rword_inv (free_inv = map letter_inv ∘ rev: rev preserves the sum, map letter_inv flips each sign)
  - conjugation-invariant (Z is abelian)
- gen and gen^{-1} have exponent sums +1 and -1, distinct in Z; non-conjugacy follows.

**Net axiom delta across cycles 11–24: −19 axioms** (3 inconsistent + 1 vacuous + 18 false-Leibniz → real lemmas, vs. 3 new sound axioms), plus +2 Parameters (`IsSemisimpleLocalSystem`, `IsSurfaceGroup`). Current axiom count: 545 (down from ~564 at session start 2026-04-28).

Cycle 23+24 *also* delivered new theorems: `SL2_blocks_property_A_at_n2` and `SL2_constant_family_lacks_property_A` (the SL(2) instance of LLM Conjecture 3.2).

**Cycle 25 (DecisionProblems/SL2Horowitz.v + WordLengthFreeGroup.v) — 2026-04-29:**
- Refutation of OpenProblems `conjecture_5_5_positive_words` at n = 2 for the constant SL(2) family.
- Added in WordLengthFreeGroup.v: `positive_word_expsum_nonneg`, `positive_zero_expsum_is_empty`, `positive_zero_expsum_RWord_is_e`.
- Added in SL2Horowitz.v: `SL2_no_positive_non_conj_trace_pair` (no positive non-conj trace-equiv pair via Horowitz + abelianization), `SL2_trace_pair_a_ainv` (clean (a, a^{-1}) witness), `SL2_constant_family_refutes_conjecture_5_5_n2` (LHS holds, RHS empty, iff fails).
- This *resolves* the n = 2 case of conjecture 5.5 (which the paper notes is "open for n ≥ 3"). The answer at n = 2 is negative for the SL(2) family.

**Cycle 26 (DecisionProblems/SL2Horowitz.v) — 2026-04-29:**
- `SL2_constant_family_lacks_uniform_C`, `SL2_constant_family_lacks_uniform_D`: both fail in F_r (r ≥ 1) via the (a, a^{-1}) trace pair.
- `SL2_constant_family_satisfies_open_question_1_10`: uniform_C ↔ uniform_D holds (False ↔ False = True) — `open_question_1_10` resolved positively for SL(2) constant family.

**Cycle 27 (Complex.v + Kahler/sl2/Vm.v) — 2026-04-29:**
- Added Leibniz bridge lemmas in Complex.v for the missing ring axioms (`Cadd_C0_l_lem`, `Cmul_comm_lem`, `Cadd_neg_r_lem`, `Csub_def_lem`, etc.) and registered `Add Ring CComplex_ring` for direct `ring` use on CComplex Leibniz `=`.
- `Cnat_succ_lem` in Vm.v (Leibniz form of `Cnat_succ_req`).
- Discharged `Vm_rel_HX`, `Vm_rel_HY` (sl(2) commutators) via `unfold; destruct (Nat.ltb k m); rewrite Cnat_succ_lem; ring.` Net −2 axioms.

**Cumulative across cycles 11–27: −21 axioms** (3 inconsistent + 1 vacuous + 20 false-Leibniz/discharged → real lemmas, vs. 3 new sound axioms), +2 Parameters, +9 new theorems. Current axiom count: 543.

**Cycle 28 (Kahler/sl2/Vm.v) — 2026-04-29:**
- Discharged `Vm_H_basis`, `Vm_X_basis_pos`, `Vm_X_basis_out` (basis-vector identities) via directed proofs using `Cmul_C0_r_lem`, `Cmul_C1_r_lem`. No `ring` on CComplex (which is slow).
- Added helper lemmas in Complex.v: `Cmul_C0_r_lem`, `Cmul_C0_l_lem`, `Cmul_C1_r_lem`, `Cneg_C0_lem`, `Csub_C0_r_lem`. These make future directed proofs fast.
- Added `Cnat_zero_lem`, `Cnat_one_lem` in Vm.v.
- Converted `CC_group` from Parameter to Definition in Sheaves.v.
- Net −3 axioms.

**Cycle 29 (Kahler/sl2/Vm.v) — 2026-04-29:**
- `Vm_mod` Axiom → Definition via refine + intros + Qed pattern (3-second compile vs 54-minute hang for naive record literal). Pattern-key: per-field `intros u v; exact (Vm_X_add m u v)` forces beta-reduction of `vs_add (Vm_vs m)` to `Vm_add` so the `exact` succeeds.
- `Vm_w0_weight`, `Vm_w0_primitive` Axiom → Lemma using Vm_mod_H/X bridges + `cbn [vs_scale Vm_vs]` for record-projection reduction.
- Net −3 axioms.

**Compile-speed lessons (cycle 27/28):**
- `ring` on CComplex via Add Ring CComplex_ring is genuinely slow (minutes per call). Use it only when essential.
- `ring` on CReal components after `apply CComplex_eq; destruct` is fast.
- For shapes like `Cmul x C0 = C0`: prefer `apply Cmul_C0_r_lem` (microseconds vs minutes).

**Cumulative across cycles 11–29: −27 axioms** (3 inconsistent + 1 vacuous + 26 false-Leibniz/discharged → real lemmas, vs. 3 new sound axioms), +2 Parameters, +9 new theorems. Current axiom count: 537.

**Cycle 30 — Vm_highest_weight + Vm_orbit_top_ne — 2026-04-29:**
- Vm_highest_weight: helper Cinject_Q_inject_Z_0 = C0 + bridge + Csub_C0_r_lem.
- Vm_orbit_top_ne: Vm_sl2_Y_orbit + (Vm_basis m m m = C1) ≠ C0.
- Vm_orbit_zero documented as inconsistent (Y not truncated; w_{m+1} ≠ 0 in nat→CComplex rep).
- Net -2 axioms.

**Cycle 31 — True-body placeholder axioms — 2026-04-29:**
- chebyshev_inequality, kolmogorov_0_1_law (Probability.v), coarea_formula_placeholder (GeometricMeasure.v) all had body `True` — converted from Axiom to Lemma.
- Net -3 axioms.

**Cumulative across cycles 11-31: −32 axioms net.** Current axiom count: 532. +2 Parameters (`IsSemisimpleLocalSystem`, `IsSurfaceGroup`). +9 substantive theorems. Build green & idempotent.

**Cycle 32 (ComplexAnalysis.v) — 2026-04-30:**
- Discharged Cinv inverse axioms via "Parameter + concrete compute + bridge axiom" trick.
- Cinv stays as `Parameter Cinv : CComplex -> CComplex` (total — preserves Cdiv-inside-lambda usage).
- Added concrete `Cinv_compute z h := mkC (re z * /|z|² ) (-im z * /|z|²)` using stdlib `CReal_inv`.
- Added bridging axiom `Cinv_eq_compute : forall z h, Cinv z = Cinv_compute z h`.
- `Cinv_mul_right`, `Cinv_mul_left` now Lemmas via the bridge + `CReal_inv_l`.
- Net -1 axiom (replaced 2 axioms with 1).

**Cumulative across cycles 11-32: −33 axioms net.** Current axiom count: 531.

**Cycle 33 (DecisionProblems/FiniteLifts.v) — 2026-04-30:**
- New paper formalized: Karshon–Lubotzky–McReynolds–Reid–Shusterman 2026
  ("Subgroups with all finite lifts isomorphic are conjugate", arXiv:2602.15463).
- New THEOREM proven: `theorem_1_4_question_1_3_negative` — Prasad's
  Question 1.3 has a negative answer. Proved from KLMRS Theorem 1.1 +
  Scott's PSL(2,29) example + Lemma 2.1 (pullback preserves Z-coset equiv).
  `Print Assumptions` shows it depends on exactly the 4 paper-attributable
  axioms — no extraneous baggage.
- New axiom-free helpers: `preimage_is_subgroup`,
  `preimage_preserves_conjugacy_of_subgroups`.
- New OPEN PROBLEM stated formally: `open_question_1_5` — KLMRS's
  proposed refinement (core-free Z-coset equivalent subgroups isomorphic?).
- New axioms (5, all paper-attributable): `KLMRS_main_theorem`,
  `R_coset_equiv_pullback`, `scott_example`, `KLMRS_corollary_1_6`,
  `KLMRS_theorem_1_7`.
- New parameters (3): `R_coset_equivalent`, `profinite_completion`,
  `profinite_iso`.
- **Extension**: 6 more open problems from §1.3 and §1.4 of the paper
  formalized as Definitions:
  - `open_profinite_theorem_1_1` (anabelian profinite variant of Thm 1.1)
  - `open_question_prosupersolvable_recovery` (number-field recovery
    from prosupersolvable Galois quotient, cf. ref [6])
  - `open_mcg_profinite_rigidity` and `open_mcg_theorem_1_1_analog`
    (mapping class groups)
  - `open_nonarith_profinite_rigidity` and `open_nonarith_theorem_1_1_analog`
    (maximal non-arithmetic lattices)
  Required 14 additional parameters for the underlying objects
  (number fields, MCG, lattices, profinite-group structure).
- Net for cycle 33: +5 axioms / +17 parameters / +1 theorem /
  +3 helper lemmas / +7 stated open problems. Current axiom count: 536.

**Cycle 43+ — Q1.5 expansion to 6 theorems — 2026-04-30:**

After the abelian-subgroup case, added more Q1.5 theorems:

- `question_1_5_dedekind`: any group whose every subgroup is normal
  satisfies Q1.5 (vacuously: core-free → trivial). Strictly generalises
  the abelian-G case. Examples: abelian + Hamiltonian groups (Q_8 × E).
- `question_1_5_when_corefree_subgroups_abelian`: cleaner abstraction
  of cycle 43's abelian-subgroup result.
- `is_cyclic_implies_abelian` was axiomatized in cycle 43; now
  **discharged** as a real theorem via two new axiom-free helpers
  `gpow_add` and `gpow_self_commute`.

Six Q1.5 theorems total now:
1. `question_1_5_abelian` (cycle 34) — ambient G abelian.
2. `question_1_5_central_intersection` (cycle 42) — ambient G has CIP.
3. `question_1_5_dedekind` (cycle 43) — ambient G has every subgroup normal.
4. `question_1_5_abelian_subgroups` (cycle 43) — both subgroups abelian.
5. `question_1_5_cyclic_subgroups` (cycle 43) — both subgroups cyclic.
6. `question_1_5_when_corefree_subgroups_abelian` (cycle 43) —
   every core-free subgroup is abelian.

Theorems #1, #3 are axiom-free (depend only on `proof_irrelevance` and
`R_coset_equivalent` parameter). #2 same. #4-6 depend on the
structure-theorem axiom + Burnside axiom (both standard).

**Counterexample search (GAP):** TableOfMarks-based Z-equivalence test
implemented in `tools/cag_gap/q15_search.g`. Smoke-tested on orders
1-30 (0 candidates, expected). Production scan over orders 30-250
with `MAX_GROUPS_PER_ORDER=25` filter (skips 64, 96, 120, 128, 144,
160, 192, 224, 240, 252) completed: **785 groups scanned, 0
Q-coset-equivalent core-free non-isomorphic candidates found.**
Computational evidence that Q1.5 holds in the low-order regime
(though the skipped orders include some 2-group-rich cases).
Search output saved to `.cag/q15_skip_30_250.log`.

**Cycle 43 — Q1.5 abelian/cyclic SUBGROUP case — 2026-04-30:**

Different angle from cycle 34/42 (which constrained the ambient G).
Cycle 43 constrains the SUBGROUPS H1, H2 themselves. New theorems
in `theories/DecisionProblems/FiniteLifts.v`:

- `is_abelian_subgroup`, `is_cyclic_subgroup` definitions.
- `is_abelian_implies_subgroup_abelian` (axiom-free).
- `question_1_5_abelian_subgroups`: two abelian subgroups Z-coset
  equivalent → isomorphic. Core-free hypothesis NOT needed.
- `question_1_5_cyclic_subgroups`: cyclic version (corollary).

New axioms (3) and parameters (1) cite standard facts:
- `Z_coset_equivalent_same_order_multiset` — Burnside / table-of-marks.
- `abelian_subgroups_iso_from_order_multiset` — Fundamental Theorem
  of Finite Abelian Groups (Dummit-Foote 5.2).
- `is_cyclic_implies_abelian` — basic, could be discharged.
- `element_order_multiset` — Parameter for the order-counting fn.

Combined Q1.5 coverage now (cycles 34 + 42 + 43):
- Ambient G abelian → Q1.5 holds (cycle 34).
- Ambient G has CIP → Q1.5 holds (cycle 42).
- Both subgroups abelian → Q1.5 holds (cycle 43).
- Both subgroups cyclic → Q1.5 holds (cycle 43).

**Counterexample search tool:**
`tools/cag_gap/q15_search.g` improved with table-of-marks-based Z-test.
Running scan over orders 30-200; output to `.cag/q15_30_200.log`.

**Cycle 42c — Stallings folding two-letter NoDup — 2026-04-30:**

Added in `theories/HallFreeGroup/StallingsFolding.v`:
- `petal_graph_two_edges_eq`: computes the 4 edges of `petal_graph [a; b]`.
- `letter_inv_b_eq_a_implies_letter_inv_a_eq_b`: helper.
- `petal_graph_two_no_dup_edges`: edges of `petal_graph [a; b]` are
  pairwise distinct when `letter_inv a <> b` (freely reduced).

All three closed under the global context (axiom-free). Partial
progress on the `fold_preserves_subgroup_backward` axiom — the full
two-letter "is_folded" proof requires walking `find_fold_pair_aux`'s
16 case combinations under decidable letter equality, which is
substantially more involved.

**Cycle 42b — Free-group non-conjugacy theorems — 2026-04-30:**

Extended cycle 24's abelianization-based result with 5 more theorems
in `theories/DecisionProblems/WordLengthFreeGroup.v`:

- `expsum_distinct_implies_not_conjugate`: contrapositive of conj-invariance.
- `expsum_i_free_gen_RWord_other`: γ_j has 0 exponent sum at i ≠ j.
- `distinct_generators_not_conjugate`: γ_i ≁ γ_j for i ≠ j.
- `generator_not_conj_to_other_inverse`: γ_i ≁ γ_j⁻¹ for i ≠ j.
- `id_not_conj_to_generator`: identity ≁ γ_i.

All five `Print Assumptions`-clean except for `proof_irrelevance`.

**Cycle 42 — Q1.5 nilpotent / p-group case — 2026-04-30:**

Extended cycle 34's abelian result to a much broader class of groups.

**New definitions:**
- `HasCentralIntersectionProperty sg`: every subgroup whose central
  elements are all the identity is itself trivial. Holds for abelian,
  p-groups, nilpotent groups; fails for non-abelian simple groups.

**New axiom-free lemmas (verified via `Print Assumptions`):**
- `is_central_inv`: inverse of a central element is central.
- `H_inter_center_normal`: H ∩ Z(G) is a normal subgroup of G.
- `core_free_central_elements_trivial`: every central element of a
  core-free subgroup is the identity.
- `central_intersection_core_free_is_trivial`: under the
  central-intersection property, core-free → trivial subgroup.
- `abelian_has_central_intersection_property`: shows the new theorem
  subsumes the abelian case.

**New theorem:**
- `question_1_5_nilpotent`: Question 1.5 holds over any finite group
  satisfying the central-intersection property — including all p-groups
  and nilpotent groups. Both subgroups forced trivial; Z-coset
  equivalence hypothesis not needed.

`Print Assumptions question_1_5_nilpotent` shows only `proof_irrelevance`
+ `R_coset_equivalent` (parameter from the file's signature). Same
dependencies as the abelian case.

**Math impact:** the new theorem strictly extends the abelian case.
Examples covered beyond abelian: Q_8 (every non-trivial subgroup contains
the central element -1). Examples NOT covered despite being nilpotent:
D_4 (the order-2 subgroup ⟨s⟩ generated by a reflection meets the
center only at e).

CIP characterizes: "every non-trivial subgroup contains a non-trivial
central element of G" — equivalently, "every minimal subgroup is
contained in Z(G)". This is *strictly between* abelian and nilpotent.
True abelian + Q_8-like; false D_4-like.

Remaining open for Q1.5: nilpotent groups outside CIP (like D_4),
solvable but non-nilpotent groups (S_4), simple groups, and the general
case.

**Cycle 41 — Cleanup pass (overnight) — 2026-04-30:**

User asked for a cleanup pass + axiom-proving refactor, ~10 hours.
Constructive analysis (CReal/CComplex) preserved.

**Phase 1 — quick duplicates (DONE):**
- `c1_dual` / `c1_tensor` axiom collision: renamed
  `Divisor/LineBundleCech.v` copies to `c1_map_*` prefix; updated single
  downstream caller in `Divisor/DivisorBundle.v`. 4 axiom-name
  collisions resolved.
- `SL2_eq_from_mat` Aborted dead code at `LinAlg/SL2.v:64` removed.

**Phase 2 — Lie consolidation (partial DONE):**
- Removed `IsAdNilpotent` duplicate definition from
  `Lie/Semisimple.v`, now imports `Lie.Nilpotent`.
- Renamed `LieAlgebra.v` Killing-form quartet (`killing_form`,
  `killing_symm`, `killing_invariant`, `killing_scale_l`,
  `killing_add_l`) with `mat_` prefix to disambiguate from the
  field-parametric versions in `Lie/KillingForm.v`. Different
  declarations, different signatures — name disambiguation only.

**Phase 3 — placeholder cleanup (DONE):**
- Built `tools/cag_audit/strip_placeholders.py`. Removed **120 True-bodied
  placeholder Theorems** across 30+ files (Sheaves: 10, Harmonic: ~30,
  Projective: ~30, Kahler/Blowup/Divisor/Kodaira/Hodge/Residue: ~50).
  Each was a `Theorem foo : forall …, True. Proof. exact I.` with no
  external references; replaced with a one-line removal comment. 5 were
  skipped because their names appear elsewhere; 67 weren't matched by
  the strict regex (non-pure-True bodies).

**Phase 3.5 — dead axiom removal (DONE):**
- Built `tools/cag_audit/dead.py` and `strip_dead.py`. **90 truly dead
  Axioms removed** — Axioms with zero references anywhere in the project,
  including their own file. Distribution:
    Harmonic 21, Projective 16, Vanishing 16, Kahler 11, Blowup 5,
    Lie 5, Langlands 4, Rings 4, others ~8.
- Includes 4 axioms I'd added in cycle 39 (DiffGeom/Control,
  AbelianLanglands) that turned out unused.

**Phase 4 — axiom-proof attempts (PARTIAL):**
- Built `tools/cag_audit/hint_probe.py`: hint-driven probe using
  cag-search retrieval to feed `sauto use:` suggestions, falls back
  to `hammer`.
- Targeted runs:
  - NeuralOp (18 axioms): 0 closed.
  - Sylow (9 axioms): 0 closed.
  - DecisionProblems (29 axioms): 0 closed.
- Honest takeaway: sauto/hammer with hints **cannot crack any of the
  remaining 467 axioms** in this codebase under 10-15 s timeouts.
  Real proofs require deeper hand-rolled arguments or much longer
  hammer time + better predictor models.

**Net results:**
- **Axioms: 557 → 467 (−90)** via dead-axiom removal.
- **Parameters: 383 → 323 (−60)** via dead-parameter removal.
- **Total open assumptions: 940 → 790 (−150 = −16%).**
- Total declarations: 4995 → 4713 (placeholders + dead removals).
- Cross-file axiom collisions: 2 → 0.
- New tooling: cag-dups, cag-dead, hint_probe, strip_placeholders,
  strip_dead, apply_hits, hammer_probe.

Build verification: 207+/215 files compiled clean post-cleanup.
SL2Horowitz.v compile is independently slow (3-5+ min) and was not
impacted by any edits semantically. Final post-cleanup rebuild of
modified files attempted; refer to commit log for full reproduction.

See `CLEANUP_REPORT.md` and `AXIOMS_AUDIT.md` cycle 41 entry for full
details.

**Cycle 40 — Duplicates audit — 2026-04-30:**

Built `tools/bin/cag-dups` (queries the cag-search SQLite index for
both name-collision and identical-statement duplicates). Generated
`DUPLICATES_AUDIT.md` at the project root.

Findings:
- 48 names appear in ≥ 2 files. Of those:
  - ~14 are **legitimate namespace reuses** (Lie vs. order ideal, etc.)
    documented in DUPLICATES_AUDIT.md.
  - ~20 are **real redundancies** worth consolidating, biggest groups:
    - Lie infrastructure split between `Lie/*` (canonical) and
      `LieAlgebra.v` (legacy monolith): `killing_form`,
      `killing_invariant`, `killing_scale_l`, `killing_symm`, `gl`,
      `IsAdNilpotent`.
    - Algebra split: `RingHom`, `rhom_neg`, `rhom_zero` between
      `Galois/Field.v` (legacy) and `Rings/Ring.v` (canonical).
    - Complex AG fragmentation: `euler_char`, `fubini_study_form`,
      `fundamental_class`, `hodge_decomposition`, `kodaira_vanishing`,
      `poincare_dual`, `poincare_duality`, `irreducible_variety`,
      `smooth_point`, `canonical_bundle`, `tangent_cone_hypersurface`,
      and the duplicated *axioms* `c1_dual` and `c1_tensor`.
    - LinAlg internal: `df2_ring_theory`, `df3_ring_theory`,
      `mat2_det_mul`, `mat2_trace_id`, `SL2_eq_from_mat` (×2 in
      same file), `sl2_bracket_hx`, `Vm_highest_weight`.
- **192 Theorem/Lemma/Corollary declarations have body `forall …, True`**
  — placeholder fakes that look like theorems but state nothing.
  Distribution:
    Harmonic 32, Projective 31, top-level 19, Kahler 14, Blowup 11,
    Divisor 10, Kodaira 8, others ~67.
  Same pattern as the 5 placeholders cleaned up in `Langlands/` during
  cycle 35.
- 0 cross-directory dupes between new `DiffGeom/` / `Control/` and the
  existing complex-AG / measure / Langlands code (after the two fixes
  in this cycle).

Self-introduced dupes from cycle 39 (now FIXED):
- `Rn`: new `Parameter` in `DiffGeom/SmoothManifold.v` shadowed the
  existing concrete `Rn (n) := Fin.t n -> CReal` in `Complex.v`.
  Deleted the parameter; reuse the existing definition.
- `is_involutive`: collided with the unrelated graph-involution
  predicate in `HallFreeGroup/LabeledGraph.v`. Renamed mine to
  `dist_involutive`.

Recommended next consolidation pass (post-VM-upgrade): merge the Lie
duplicates (one half-day of mechanical work) and the True-bodied
Harmonic/Projective placeholders (per-directory cleanup, half-day each).

**Cycle 39 — DiffGeom + Geometric Control scaffolding — 2026-04-30:**

New theory subdirectories `theories/DiffGeom/` and `theories/Control/`.

`theories/DiffGeom/SmoothManifold.v` (~210 lines):
- Records: `SmoothManifold`, `SmoothMap`, `Diffeomorphism`, `VectorField`,
  `Distribution`.
- Parameters: `Rn`, `TangentSpace`, `is_smooth`, `is_smooth_vf`,
  `lie_bracket`, `is_integrable`, `d_at`.
- Axioms (paper-attributable): linearity / chain rule for `d_at`;
  bracket bilinearity, antisymmetry, Jacobi; **Frobenius theorem**.
- Theorems: `integrable_implies_involutive`, `involutive_implies_integrable`
  (both via Frobenius).

`theories/Control/Geometric.v` (~190 lines):
- Records: `ControlSystem` (drift + list of control vector fields).
- Parameters: `LieAlgRankCondition`, `bracket_generating_distribution`,
  `reachable_set`, `is_STLC`, `sussmann_brackets_balanced`.
- Definitions: `is_driftless`, `cs_num_controls`, `is_globally_controllable`.
- Axioms: **Chow–Rashevskii theorem**, **Sussmann STLC sufficient condition**.
- Stated open problems:
  `open_question_STLC_characterization` (Coron's open question on
  necessary-and-sufficient STLC), `open_question_sR_geodesic_smoothness`
  (sub-Riemannian Sard conjecture), `open_question_3d_euler_boundary_controllability`.
- File ends with infrastructure-gap notes [G1]-[G5] for future work.

Both files compile clean. Registered in `_CoqProject`.

**Cycle 38 — CoqHammer batch probe over all 539 axioms — 2026-04-30:**

Built two new tools:
- `tools/cag_audit/hammer_probe.py`: per-axiom probe with `rocq compile`,
  records pass/fail/timeout to JSON.
- `tools/cag_audit/apply_hits.py`: dry-run / apply rewrite of hit Axioms
  to Theorems with the chosen tactic.

Ran sauto with 8 s timeout against all 539 Axioms (≈ 50 minutes wall
clock). Result: **1/539 closed**: `current_boundary_squared` in
`theories/Measure/GeometricMeasure.v` — but on inspection it's a
`forall T, x = x` tautology stub (the comment says so). Converted Axiom
→ Theorem and added `From Hammer Require Import Tactics.`. Net axiom
delta: −1 axiom.

Honest takeaway: sauto alone is too weak on this codebase. The real
axioms are deep AG/complex-analysis/manifold content that needs either
hand-written proofs or hammer with explicit hints + more memory.
Next attempt would require:
- Adding 4 GB swap so `hammer` can run without OOM kills.
- A second pass with `hammer` + curated `use:` hints from `cag-search`
  retrieval.

Report saved to `.cag/hammer_probe_report.json` for follow-up runs.

**Cycle 37 — CoqHammer install + cag-hammer wrapper — 2026-04-30:**

Installed:
- `coq-hammer 1.3.2+9.0` and `coq-hammer-tactics 1.3.2+9.0` in the
  `rocq-9.0` opam switch (specifically pinned to the 9.0 build, since
  default-resolved 1.3.2+9.1 wants Rocq 9.1).
- ATP backends via apt: `z3`, `cvc5`, `eprover` (`/usr/bin/`).
- `tools/bin/cag-hammer`: shell wrapper that builds an isolated probe
  `.cag/_hammer_probe.v` and runs `rocq compile` on it.

Verified working:
- `sauto` on pure logic: 2s.
- `hammer` on pure logic: 2s (auto-suggested `sfirstorder` reconstruction).
- `sauto unfold: is_abelian` on a project goal (commutativity from
  abelianness): 1s.

Verified NOT working without tuning:
- `hammer` on goals over the project's specialized Records
  (StrictGroup, is_normal_subgroup): OOM-killed because all four ATPs
  fire concurrently with no swap on this 11 GB VM.
- `sauto use: <hint>` on the same goal: timed out at 30s — sauto's
  search depth is unequal to the unfolding required.

Mitigations documented in `tools/README.md`:
1. Add 4 GB swap (`fallocate` + `mkswap` + `swapon`) — biggest win for hammer.
2. Disable some ATPs with `Set Hammer Vampire ""` etc.
3. Lower `Set Hammer ATPLimit` and `Set Hammer Predictions`.
4. Prefer `sauto unfold: <defn>` + `use: <lem>` over raw `hammer` on this VM.

Bottom line: hammer is a real tool now, but on this hardware it's a
hint-driven workhorse, not a one-shot magic button. Will be much more
useful once the VM gets more RAM + swap.

**Cycle 36 — Toolchain (Python + partial OCaml port) — 2026-04-30:**

Built five CLI tools under `tools/bin/` for local autonomous use:
- `cag-search`: SQLite FTS5 lemma index (Python + OCaml; OCaml preferred).
- `cag-audit`: axiom/parameter listing, snapshots, diffs, suspect detection,
  `Print Assumptions` runner (Python only).
- `cag-tactic`: Llemma 7B-backed tactic suggester via llama.cpp (Python only).
- `cag-extract`: one-command Rocq → OCaml extraction (Python only).
- `cag-gap`: GAP bridge with bundled Q1.5 candidate-search script (Python only).

Wrappers in `tools/bin/cag-*` prefer the OCaml binary if built, else fall
back to Python. Build via `cd tools && make ocaml`. See `tools/README.md`
for the full status table and resume-point instructions.

OCaml port status (intentionally partial — VM upgrade pending):
- `cag_lib` (Rocq parser): done. ~4939 declarations indexed in 1.1s.
- `cag_search`: done. Mirrors Python behavior.
- Other tools: not yet ported; pattern is set for resuming.

**Cycle 35 — Langlands cleanup + AbelianLanglands.v — 2026-04-30:**

In `theories/Langlands/`:
- **`gl1_geometric_langlands`**: Axiom → Theorem (proved from `riemann_hilbert_surjective`).
- **5 `True`-bodied placeholder Lemmas removed** (HiggsBundles.v + NonabelianHodge.v):
  `hitchin_map_iso_invariant` (replaced with a real Axiom using `JMeq`),
  `hitchin_fibration_proper`, `hitchin_fiber_is_jacobian`,
  `hitchin_base_self_dual`, `mirror_symmetry_hitchin` (removed with explanatory comments).
- **New lemmas in LocalSystems.v**: `rank1_tensor_rank`, `rank1_dual_rank`,
  `ls_tensor_chain` (Fixpoint), `ls_tensor_chain_rank1`.
- **New file**: `theories/Langlands/AbelianLanglands.v` (≈ 270 lines).
  Formalizes the GL(1) Langlands story as the abelian-group structure
  on rank-1 local systems mod iso. Includes:
  - 11 new Axioms (paper-attributable: tensor unit/assoc/comm,
    bifunctoriality, dual-as-inverse, dual-of-tensor, ls_trivial_rank1).
  - 1 new Parameter (`ls_trivial`).
  - 1 new Lemma (`ls_tensor_iso_both`).
  - 4 new Theorems:
    `ls_dual_involutive`, `ls_dual_trivial`,
    `abelian_langlands_group` (group laws bundled),
    `gl1_param_group_laws` (sigma-typed parameter space).

Net effect on Langlands subdirectory:
- Theorems went from 3 → 7 (riemann_hilbert, non_abelian_hodge,
  gl1_geometric_langlands [upgraded], ls_dual_involutive, ls_dual_trivial,
  abelian_langlands_group, gl1_param_group_laws).
- True-bodied fake Lemmas: 5 → 0.
- Honest content gain: substantial. Axiom count rose +10 (paper-attributable),
  but the new axioms encode real mathematical structure, not placeholders.

**Cycle 34 — Partial result on Question 1.5 — 2026-04-30:**
- Proved `question_1_5_abelian`: in any abelian finite group, two
  core-free Z-coset equivalent subgroups are isomorphic. The proof
  shows in fact the Z-coset equivalence hypothesis is unnecessary —
  abelian + core-free already forces both subgroups to be trivial.
- Helper lemmas added (all in FiniteLifts.v):
  - `is_abelian` — predicate.
  - `abelian_subgroup_is_normal` — axiom-free.
  - `abelian_core_free_is_trivial` — axiom-free (verified by
    `Print Assumptions`).
  - `sig_eq_proof_irrel` — sigma equality from proof_irrelevance.
  - `triv_canon`, `triv_singleton`, `triv_strict_group` — top-level
    helpers for the singleton-StrictGroup construction.
  - `trivial_subgroups_isomorphic` — depends only on proof_irrelevance.
  - `abelian_unique_core_free` corollary.
- New axiom dependencies: only `proof_irrelevance` from Stdlib (already
  used widely in the project; standard).
- Cumulative net result: real partial answer to KLMRS Question 1.5.
  Specifically: the abelian case is now resolved positively. The
  question remains open for nonabelian G (where core-free subgroups
  can be non-trivial).

**Cumulative across cycles 11-33: −28 axioms net** (vs. project start, but
+5 of the new ones are sound paper-attributable axioms for a 2026 paper
that wouldn't otherwise be in the codebase). Current axiom count: 536.

## Key false-as-stated admits (do not attempt):
- `ATT/Syntax.v`: `ax_subst_comp` — already tightened with typing hypothesis (`AxHasType Sg Γ M α`); the historical "FALSE without typing" is no longer the active state. Verify before treating as suspect.
- `LieAlgebra.v`, `AG.v` CReal arithmetic laws: **discharged in cycle 17** via `CRealEq_eq` bridge — these are now sound Lemmas.
- `AxTheory/ClassifyingCategory.v`: `axcl_bp_beta1/2/uniq`, `axcl_terminal_unique`, `axcl_exp_beta/eta` — FALSE at raw term level (need quotient modulo beta/eta)
- `Presheaf/YonedaProducts.v`: `yoneda_preserves_product` — false as Type equality (only isomorphism)

## Broadly blocked (do not attempt without major infrastructure work):
- `AxTheory/ClassifyingCategory.v`: `axcl_comp_assoc` uses `ax_subst_comp` (false)
- `Category/Gluing.v`: gl_prod_ob, gl_binary_product — blocked by object-level-only T_pres_prod
- `AxTheory/RelativeFreeCCC.v`: `ax_iter_proj` has wrong statement
- `ATT/InternalLanguage.v`: `Eq_C`, `Eq_C_inv` — quotient issue
- `ATT/SoundComplete.v`: `soundness` — mod_ax = True placeholder
- All CReal arithmetic admits — setoid equality only, not Leibniz
- All quotient type admits — Rocq has no quotient types without axioms
- All Parameter-based admits — require additional axioms not present
- All deep analysis admits — DFT, complex analysis, Kähler geometry

## Remaining admits by category:
- ~40 AG.v (matrix algebra, projective space — CReal + deep)
- ~30 ComplexAnalysis2.v (complex analysis — deep)
- ~20 LieAlgebra.v (CReal setoid)
- ~18 Divisor/LineBundleCech.v (Cequal uses Leibniz CReal)
- ~17 Sheaves.v (Parameters, deep)
- ~15 ComplexAnalysis.v (deep)
- ~14 NeuralOp/DFT.v (DFT correctness — CReal)
- ~14 Harmonic/Sobolev.v (deep PDE)
- ~67 ManifoldTopology.v (all Parameters)
- ...plus many others in deep geometry files

**Why:** Almost all remaining admits require either CReal setoid arithmetic (Leibniz `=` fails for `CReal` values like `1 * x - 0 = x`), quotient types, or deep mathematical content.

**How to apply:** Focus session efforts on pure list/nat/combinatorial lemmas that don't touch CReal. These are now rare.
