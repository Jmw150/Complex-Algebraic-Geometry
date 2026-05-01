# Q1.5 Formalization Progress

**Paper:** Karshon–Lubotzky–McReynolds–Reid–Shusterman (KLMRS),
"Subgroups with all finite lifts isomorphic are conjugate",
arXiv:2602.15463v1 (February 2026).

**File:** `theories/DecisionProblems/FiniteLifts.v`

**Last updated:** 2026-04-30 (cycles 33, 34, 42, 42b, 42c, 43, 43+)

---

## 1. Statement of Question 1.5

**Paper formulation (§1, p. 2).**
Let G be a finite group and let G₁, G₂ ≤ G be subgroups that satisfy:

1. G₁ and G₂ are **Z-coset equivalent**: the permutation representations
   G ↷ G/G₁ and G ↷ G/G₂ are isomorphic as Z[G]-modules
   (equivalently, G/G₁ and G/G₂ are isomorphic as G-sets over Z — this is
   the classical Gassmann–Sunada equivalence).
2. Both G₁ and G₂ are **core-free**: neither subgroup contains any
   non-trivial normal subgroup of G.

**Question:** Under these two conditions, must G₁ and G₂ be isomorphic as
abstract groups?

**Context.** Prasad's earlier Question 1.3 asked whether Z-coset equivalence
alone forces isomorphism. Theorem 1.4 of the paper (proved from KLMRS
Theorem 1.1 + Scott's 1993 PSL(2,29) example) says **no**: there exist
finite groups with non-isomorphic Z-coset equivalent subgroups. The core-free
condition is the refinement KLMRS propose to rescue the question.

**Formal definition in Rocq** (`FiniteLifts.v:308`):

```rocq
Definition open_question_1_5 : Prop :=
  forall (G : Type) (sg : StrictGroup G) (G_list : list G),
    IsFiniteEnum sg G_list ->
    forall G1 G2 : G -> Prop,
      is_subgroup (StrictGroup_to_Group sg) G1 ->
      is_subgroup (StrictGroup_to_Group sg) G2 ->
      is_core_free sg G1 ->
      is_core_free sg G2 ->
      Z_coset_equivalent sg G1 G2 ->
      subgroups_isomorphic sg sg G1 G2.
```

---

## 2. Inventory of Q1.5 Theorems Formally Proved

Six special-case theorems have been proved. All live in
`theories/DecisionProblems/FiniteLifts.v`.

| # | Theorem name | Hypothesis on G or subgroups | Z-coset hyp used? | Axiom-cleanliness | Line |
|---|---|---|---|---|---|
| 1 | `question_1_5_abelian` | Ambient G is abelian (`is_abelian sg`) | No (Z-coset hyp is discarded) | Only `proof_irrelevance` + `R_coset_equivalent` parameter | 709 |
| 2 | `question_1_5_central_intersection` | G has the Central-Intersection Property (`HasCentralIntersectionProperty`) | No | Same as #1 | 892 |
| 3 | `question_1_5_dedekind` | Every subgroup of G is normal (Dedekind group) | No | Only `proof_irrelevance` + `R_coset_equivalent` | 1065 |
| 4 | `question_1_5_abelian_subgroups` | G₁ and G₂ are abelian as subgroups | Yes | `proof_irrelevance` + `R_coset_equivalent` + `Z_coset_equivalent_same_order_multiset` + `abelian_subgroups_iso_from_order_multiset` | 976 |
| 5 | `question_1_5_cyclic_subgroups` | G₁ and G₂ are cyclic | Yes (inherited from #4) | Same as #4 | 1118 |
| 6 | `question_1_5_when_corefree_subgroups_abelian` | Every core-free subgroup of G is abelian | Yes (delegates to #4) | Same as #4 | 1097 |

**Proof strategy summary:**

- **Theorems 1–3** proceed by forcing G₁ = G₂ = {e}: core-freeness + the
  ambient-group hypothesis forces every core-free subgroup to be trivial;
  two trivial subgroups are isomorphic by `trivial_subgroups_isomorphic`.
- **Theorems 4–6** proceed via the structure theorem: Z-coset equivalence
  implies equal element-order multisets (Burnside); for abelian groups,
  equal multisets imply isomorphism (Fundamental Theorem of Finite Abelian
  Groups). Cyclic implies abelian (discharged as a real theorem via
  `gpow_self_commute`).
- **Theorem 3 subsumes Theorem 1** (abelian → every subgroup normal →
  Dedekind). Shown by `abelian_has_central_intersection_property`.
- **Theorem 6 subsumes Theorem 4** (if every core-free sub is abelian, both
  G₁, G₂ are abelian, so #4 applies directly).

---

## 3. Supporting Axioms

### Paper-attributable axioms (cited to KLMRS 2026 or Scott 1993)

| Axiom name | Source | Line | Purpose |
|---|---|---|---|
| `KLMRS_main_theorem` | KLMRS Theorem 1.1 | 202 | Existence of finite lift separating non-conjugate subgroups |
| `R_coset_equiv_pullback` | KLMRS Lemma 2.1 | 150 | Pullback preserves R-coset equivalence under surjective hom |
| `scott_example` | Scott 1993, PSL(2,29) | 245 | Non-conjugate Z-coset equivalent subgroups of PSL(2,29) |
| `KLMRS_corollary_1_6` | KLMRS Corollary 1.6 | 335 | Profinite finite-quotient factoring result |
| `KLMRS_theorem_1_7` | KLMRS Theorem 1.7 | 369 | Tetrahedral quotient of Γ separates the Scott pair |

### Standard-mathematics axioms (basic group theory / algebra)

| Axiom name | Content | Status | Line |
|---|---|---|---|
| `Z_coset_equivalent_same_order_multiset` | Z-coset equivalence implies equal element-order multisets (Burnside / table-of-marks) | Sound, standard | 950 |
| `abelian_subgroups_iso_from_order_multiset` | Finite abelian groups with equal order multisets are isomorphic (Dummit–Foote Theorem 5.2) | Sound, standard | 963 |

### Stdlib axiom used

| Axiom | Source | Role |
|---|---|---|
| `proof_irrelevance` | Rocq Stdlib | Needed for the `triv_strict_group` sigma-type construction; already project-wide |

### Parameters (abstractions, not asserting content)

| Parameter | Purpose | Line |
|---|---|---|
| `R_coset_equivalent` | Abstract R[G]-module isomorphism predicate | 129 |
| `element_order_multiset` | Order-counting function on subgroups | 944 |
| `profinite_completion`, `profinite_iso` | Infrastructure for Corollary 1.6 | 331–333 |

---

## 4. GAP Counterexample Searches

The GAP script `tools/cag_gap/q15_search.g` implements a table-of-marks-based
Z-equivalence test and enumerates group pairs within order bounds.

| Search ID | Log file | Orders scanned | Group-count filter | Groups scanned | Groups skipped | Candidates found | Notes |
|---|---|---|---|---|---|---|---|
| Smoke test (orders 1–30) | (in-memory) | 1–30 | ≤25 per order | ~50 | 0 | 0 | Baseline verification |
| Production scan A | `.cag/q15_skip_30_250.log` | 30–250 | ≤25 per order | 785 | orders 32,48,64,72,80,96,108,112,120,128,144,160,162,168,176,180,192,200,208,216,224,240,243 (p-group-rich) | 0 Z-equivalent non-iso candidates | |
| Production scan B | `.cag/q15_fast.log` | 16–350 | ≤30 per order | 1217 | 1195 filtered by proven-theorem tests | 0 candidates | More aggressive proven-case filtering |
| Filtered scan | `.cag/q15_filtered_16_300.log` | 16–300 | ≤50 per order | (partial) | orders 32,48,64,72,80,96,108,112,120,128... | 0 | |

**Summary:** Across all scans, **0 counterexample candidates** were found.
The scanned range (orders 16–350, thin coverage) provides computational
evidence that Q1.5 holds in the low-order regime. The skipped orders are
precisely the 2-power orders where most small groups live (orders 32, 64,
128, 192, 256, 320), plus other high-multiplicity orders. These remain
unverified computationally.

---

## 5. Group Classes Covered

| Class | Definition | Covered by theorem | Mechanism |
|---|---|---|---|
| **Abelian groups** | All elements commute | `question_1_5_abelian` (Thm 1) | Core-free → trivial (every sub is normal) |
| **Dedekind groups** | Every subgroup is normal (abelian ∪ Hamiltonian) | `question_1_5_dedekind` (Thm 3) | Same: core-free = normal → trivial |
| **Hamiltonian groups** | Non-abelian Dedekind: Q₈ × A × ℤ₂ᵏ | `question_1_5_dedekind` (Thm 3) | Dedekind case |
| **CIP groups** (Central-Intersection Property) | Every non-trivial subgroup meets Z(G) non-trivially | `question_1_5_central_intersection` (Thm 2) | Core-free → central elements trivial → H trivial |
| **Groups where every core-free sub is abelian** | e.g. S₃ (core-free subs are order-1 or order-2 cyclic) | `question_1_5_when_corefree_subgroups_abelian` (Thm 6) | Delegates to structure theorem |
| **Ambient G arbitrary, G₁ G₂ abelian** | No constraint on G | `question_1_5_abelian_subgroups` (Thm 4) | Z-coset → same order multiset → FTFAG |
| **Ambient G arbitrary, G₁ G₂ cyclic** | No constraint on G | `question_1_5_cyclic_subgroups` (Thm 5) | Cyclic → abelian → Thm 4 |

### Still open (not yet covered)

| Class | Why open | Smallest example |
|---|---|---|
| General nilpotent groups (outside CIP) | CIP fails when a non-central element of prime order exists; trivial-subgroup argument breaks | D₄ (dihedral of order 8) |
| Solvable non-nilpotent groups | No forcing mechanism yet for core-free → trivial or abelian | A₄ (order 12), S₄ (order 24) |
| Non-solvable groups | No structural forcing; counterexamples might exist | PSL(2,5) ≅ A₅ (order 60) |
| The full question | No unconditional proof | — |

---

## 6. Specific Examples of Groups That ARE Covered

| Group | Order | Covered by | Justification |
|---|---|---|---|
| Any Z/nZ, Z/pZ, Z/2Z | n | `question_1_5_abelian` | Abelian; core-free sub must be trivial |
| ℤ₂ × ℤ₂ (Klein four-group) | 4 | `question_1_5_abelian` | Abelian |
| Z/pZ × Z/qZ (p ≠ q primes) | pq | `question_1_5_abelian` | Abelian |
| Any finite abelian group | — | `question_1_5_abelian` | Abelian by definition |
| **Q₈** (quaternion group) | 8 | `question_1_5_dedekind` | Hamiltonian (Dedekind non-abelian): every subgroup is normal; core-free → trivial |
| Q₈ × ℤ₂ × ℤ₂ | 32 | `question_1_5_dedekind` | Hamiltonian product (Dedekind) |
| **S₃** (symmetric group) | 6 | `question_1_5_when_corefree_subgroups_abelian` | Non-abelian, but every core-free subgroup of S₃ is cyclic (order 1 or 2), hence abelian |
| **A₄** (alternating group) | 12 | `question_1_5_abelian_subgroups` (conditional) | Core-free subgroups of A₄ that arise in Z-coset equivalent pairs are cyclic groups of order 2 or 3; covered if the pair is abelian/cyclic. **Not** covered by the ambient-group theorems (A₄ is not Dedekind, not CIP). |
| Groups with cyclic core-free subpairs | — | `question_1_5_cyclic_subgroups` | Any G whose Z-coset equivalent core-free pair (G₁,G₂) happen to both be cyclic |

---

## 7. Specific Examples of Groups NOT Covered

| Group | Order | Why not covered |
|---|---|---|
| **D₄** (dihedral of order 8) | 8 | Nilpotent but outside CIP: the subgroup ⟨s⟩ (a reflection) has order 2 and is not central; CIP fails. Core-free subgroups of D₄ can be non-trivial cyclic subgroups. Theorems 1–3 do not apply. (Theorem 4 would apply if both core-free subgroups are abelian, but D₄ is not classified by ambient-group conditions.) |
| **S₄** | 24 | Solvable but not nilpotent. Has core-free non-abelian subgroups: S₃ embeds as the stabilizer of a point, and the S₃-copy is core-free and non-abelian. No current theorem covers non-abelian core-free subgroups. |
| **PSL(2,5) ≅ A₅** | 60 | Simple non-abelian; all proper subgroups are core-free (since the group is simple). Has many non-abelian subgroups (D₅, A₄, S₃ copies). No current theorem applies. |
| **PSL(2,7)** | 168 | Simple; similar to A₅. Core-free subgroups include S₄ and others. |
| **PSL(2,29)** | 12180 | The paper's motivating example (Scott's pair lives here). Has non-conjugate Z-coset-equivalent A₅-subgroups; Q1.5 asks whether these must be isomorphic. They happen to both be isomorphic to A₅ in Scott's example, but the question is whether this is forced. |
| **General finite group** | — | The full question remains open. |

---

## 8. Open Extensions Worth Pursuing

The following extensions would meaningfully advance the formalization of Q1.5.

### 8.1 Nilpotent case outside CIP

**Goal:** Prove Q1.5 for nilpotent groups G that do not satisfy CIP (e.g., D₄).

**Obstacle:** The CIP argument forces core-free → trivial via central elements.
For D₄, a reflection subgroup ⟨s⟩ has no non-trivial central elements yet
is non-trivial. A different forcing mechanism is needed — likely using the
structure of Sylow p-subgroups together with the Z-coset equivalence
hypothesis (rather than discarding it as theorems 1–3 do).

**Suggested approach:** Axiomatize "in a nilpotent group, Z-coset equivalent
subgroups have the same order" (which follows from the p-subgroup structure),
then use Sylow theory already in the project.

### 8.2 Solvable case (A₄, S₄, dihedral groups in general)

**Goal:** Prove Q1.5 for solvable groups.

**Key fact needed:** In a solvable group, a core-free subgroup is a Hall
π-subgroup for some set of primes π (Schur–Zassenhaus). Two Z-coset
equivalent Hall subgroups are conjugate (Hall's theorem), hence isomorphic.

**Infrastructure gap:** The project's Hall theory (`HallTheorem.v`) has the
main theorem axiomatized; a proof of Q1.5 for solvable groups would reduce
to those axioms and would be a genuine new result.

### 8.3 Subgroup-structure theorem for non-abelian pairs

**Goal:** Extend `question_1_5_abelian_subgroups` to pairs where G₁, G₂ are
non-abelian but isomorphic type can be determined from Z-coset invariants.

**Key fact needed:** A general structure theorem beyond FTFAG — for instance,
showing that Z-coset equivalent subgroups have the same composition factors
(Jordan–Hölder), which would force isomorphism for groups with unique
decompositions.

### 8.4 GAP search over skipped orders

The production scan skips all orders with > 25–30 isomorphism classes
(including 32, 48, 64, 96, 128, 192, 256). These 2-power orders are the
most interesting from the perspective of Q1.5 (many non-abelian p-groups,
some with interesting core-free subgroup structure). A targeted scan over
selected 2-groups (D₄, Q₁₆, the 14 groups of order 16, etc.) would fill
the most important gap.

### 8.5 PSL(2,p) family

**Goal:** Verify Q1.5 computationally or theoretically for PSL(2,p) (the
motivating family, containing Scott's example).

**Approach:** GAP search restricted to PSL(2,p) for small primes p ≤ 100,
or a theoretical argument using the known subgroup structure of PSL(2,p)
(Dickson's theorem: maximal subgroups are dihedral, A₄/S₄/A₅, or Borel).

### 8.6 Discharge the standard-math axioms

`Z_coset_equivalent_same_order_multiset` and
`abelian_subgroups_iso_from_order_multiset` are both sound but axiomatized
because the project lacks a concrete `element_order_multiset` implementation
and FTFAG in Rocq. The first could be discharged by building a concrete
table-of-marks computation; the second requires formalizing FTFAG (a
substantial but self-contained project using the existing Sylow infrastructure).

### 8.7 Profinite variant (Corollary 1.6)

`KLMRS_corollary_1_6` is axiomatized. A partial discharge would require
adding profinite completions to the project (abstract enough to get started:
a `Parameter profinite_of : StrictGroup G -> ...` plus the key universal
property). This would connect Q1.5 to the profinite open problems already
stated in §§11–13 of `FiniteLifts.v`.

---

## Appendix: File Structure and Proof Dependencies

### Section map of `FiniteLifts.v`

| Section | Lines | Content |
|---|---|---|
| §1 | 33–65 | Finite group basics: `IsFiniteEnum`, `conjugate_subgroups`, `preimage_subset`, `is_surjective_hom` |
| §2 | 66–116 | `preimage_is_subgroup`, `preimage_preserves_conjugacy_of_subgroups` (both axiom-free) |
| §3 | 117–173 | R-coset equivalence: `R_coset_equivalent` (Parameter), `Z_coset_equivalent`, `R_coset_equiv_pullback` (Axiom), `Z_coset_equiv_pullback` |
| §4–5 | 174–216 | `subgroups_isomorphic`, `KLMRS_main_theorem` (Axiom) |
| §6–7 | 217–253 | `prasad_question_1_3`, `scott_example` (Axiom) |
| §8 | 254–283 | `theorem_1_4_question_1_3_negative` — **proved theorem** |
| §9–10 | 284–354 | `is_core_free`, `open_question_1_5` (Definition = open problem) |
| §11–13 | 355–580 | Corollaries 1.6, 1.7 and §1.3–1.4 open problems (6 Definitions) |
| §14 | 581–743 | Abelian case: infrastructure lemmas + `question_1_5_abelian` (Thm) |
| §15 | 744–923 | CIP case: `HasCentralIntersectionProperty`, 5 helper lemmas, `question_1_5_central_intersection` (Thm) |
| §16 | 924–1133 | Abelian/cyclic subgroup cases: `question_1_5_abelian_subgroups`, `question_1_5_cyclic_subgroups`, `question_1_5_dedekind`, `question_1_5_when_corefree_subgroups_abelian` |

### Dependency graph (axiom level)

```
question_1_5_abelian
  └── proof_irrelevance (Stdlib)
  └── R_coset_equivalent (Parameter — no content asserted)

question_1_5_central_intersection
  └── same as above

question_1_5_dedekind
  └── same as above

question_1_5_abelian_subgroups
  └── Z_coset_equivalent_same_order_multiset (Axiom — Burnside)
  └── abelian_subgroups_iso_from_order_multiset (Axiom — FTFAG)
  └── proof_irrelevance

question_1_5_cyclic_subgroups
  └── is_cyclic_implies_abelian (Theorem — axiom-free)
  └── question_1_5_abelian_subgroups (above)

question_1_5_when_corefree_subgroups_abelian
  └── question_1_5_abelian_subgroups (above)

theorem_1_4_question_1_3_negative
  └── KLMRS_main_theorem (Axiom — KLMRS 2026, Theorem 1.1)
  └── R_coset_equiv_pullback (Axiom — KLMRS 2026, Lemma 2.1)
  └── scott_example (Axiom — Scott 1993)
  └── proof_irrelevance
```
