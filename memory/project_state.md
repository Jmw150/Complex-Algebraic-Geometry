---
name: project_state
description: Current admit count, key blockers, completed work in CAG Rocq formalization
type: project
---

## Admit count: 435 (started at ~438)

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

## Key false-as-stated admits (do not attempt):
- `ATT/Syntax.v`: `ax_subst_comp` — FALSE without typing hypothesis
- `LieAlgebra.v`, `AG.v`: CReal arithmetic laws — FALSE with Leibniz `=`, need setoid `~~C`
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
