# Corpus Analysis

This report summarizes the tactic-script corpus extracted from Rocq/Coq source files. The extraction is syntactic: it records proof-script steps, normalizes recognizable tactic names, and preserves raw first tokens for diagnosis. It does not yet include live proof-state terms, hypotheses, or kernel-level ASTs.

## Executive Summary

The corpus contains **6966 extracted tactic steps** across **982 proofs with extracted steps**, **112 files**, and **19 top-level modules**. The average extracted proof length is **7.09 steps**, while the median is **1 step**, which means the proof-length distribution is strongly skewed toward short proofs with a smaller number of long scripts. The source scan found **1164 proof-ending commands**. The longest extracted proof has **139 steps**.

SSReflect-style compact `by` steps account for **0 steps**, or **0.00%** of the extracted tactic steps. One-step proofs account for **498 proofs** (**50.71%** of proofs), while proofs with at least 10 extracted steps account for **188 proofs** (**19.14%**) and proofs with at least 25 extracted steps account for **61 proofs** (**6.21%**).

## Headline Counts

| Statistic | Value |
| --- | ---: |
| Total extracted tactic steps | 6966 |
| Proofs with extracted steps | 982 |
| `Proof` starts in source | 1180 |
| Proof-ending commands in source | 1164 |
| Files with extracted steps | 112 |
| Top-level modules | 19 |
| SSReflect `by` steps | 0 |
| SSReflect `by` share | 0.00% |

## Proof Endings

This section counts source-level proof terminators such as `Qed` and `Defined`. It is the best count of how many proofs the source files contain, including proofs that produced no extracted tactic steps. The scan found **1180 `Proof` starts** and **1164 proof-ending commands**. The start/end difference is **16**; a nonzero difference can come from unusual proof syntax, parsing limitations, or commands outside the simple `Proof ... Qed` shape.

| Ending command | Count | Share of endings |
| --- | ---: | ---: |
| `Qed` | 645 | 55.41% |
| `Admitted` | 428 | 36.77% |
| `Defined` | 91 | 7.82% |
| `Abort` | 0 | 0.00% |
| `Save` | 0 | 0.00% |

## Proof Lengths

| Measure | Steps |
| --- | ---: |
| Mean | 7.09 |
| Median | 1 |
| P75 | 6 |
| P90 | 18 |
| P95 | 28 |
| P99 | 77 |
| Max | 139 |

Interpretation: the gap between the median and the high percentiles is a quick measure of proof-script concentration. A low median with a high maximum usually means many proof obligations are discharged quickly, while a small set of files contains the hard engineering work.

## Tactic Action Distribution

The top 10 normalized actions cover **6800 steps** (**97.62%** of the corpus). This concentration matters for tactic prediction because a small action vocabulary can already explain a large share of proof-script behavior.

| Rank | Action | Count | Share |
| ---: | --- | ---: | ---: |
| 1 | `other` | 3217 | 46.18% |
| 2 | `apply` | 944 | 13.55% |
| 3 | `intro` | 820 | 11.77% |
| 4 | `rewrite` | 679 | 9.75% |
| 5 | `exact` | 566 | 8.13% |
| 6 | `reflexivity` | 226 | 3.24% |
| 7 | `split` | 169 | 2.43% |
| 8 | `elim` | 83 | 1.19% |
| 9 | `constructor` | 48 | 0.69% |
| 10 | `set` | 48 | 0.69% |
| 11 | `lia` | 41 | 0.59% |
| 12 | `pose` | 40 | 0.57% |
| 13 | `exact_I` | 29 | 0.42% |
| 14 | `right` | 21 | 0.30% |
| 15 | `left` | 19 | 0.27% |
| 16 | `ring` | 9 | 0.13% |
| 17 | `done` | 4 | 0.06% |
| 18 | `assumption` | 1 | 0.01% |
| 19 | `auto` | 1 | 0.01% |
| 20 | `clear` | 1 | 0.01% |

## Raw First Tokens

Raw first-token counts are included to diagnose normalization gaps. If `other` is large in the action distribution, this table shows which raw tactics should be added to the normalizer next.

| Rank | First token | Count | Share |
| ---: | --- | ---: | ---: |
| 1 | `unknown` | 1081 | 15.52% |
| 2 | `apply` | 920 | 13.21% |
| 3 | `intros` | 705 | 10.12% |
| 4 | `rewrite` | 679 | 9.75% |
| 5 | `exact` | 595 | 8.54% |
| 6 | `admit` | 260 | 3.73% |
| 7 | `unfold` | 236 | 3.39% |
| 8 | `destruct` | 228 | 3.27% |
| 9 | `reflexivity` | 226 | 3.24% |
| 10 | `simpl` | 222 | 3.19% |
| 11 | `assert` | 188 | 2.70% |
| 12 | `split` | 169 | 2.43% |
| 13 | `cbn` | 163 | 2.34% |
| 14 | `exists` | 145 | 2.08% |
| 15 | `intro` | 115 | 1.65% |
| 16 | `induction` | 83 | 1.19% |
| 17 | `symmetry` | 59 | 0.85% |
| 18 | `f_equal` | 57 | 0.82% |
| 19 | `refine` | 51 | 0.73% |
| 20 | `constructor` | 48 | 0.69% |
| 21 | `set` | 48 | 0.69% |
| 22 | `lia` | 41 | 0.59% |
| 23 | `pose` | 40 | 0.57% |
| 24 | `subst` | 36 | 0.52% |
| 25 | `discriminate` | 29 | 0.42% |
| 26 | `change` | 24 | 0.34% |
| 27 | `eapply` | 24 | 0.34% |
| 28 | `inject_Z` | 24 | 0.34% |
| 29 | `of_nat` | 24 | 0.34% |
| 30 | `transitivity` | 23 | 0.33% |
| 31 | `right` | 21 | 0.30% |
| 32 | `inversion` | 20 | 0.29% |
| 33 | `left` | 19 | 0.27% |
| 34 | `nth_error_map` | 17 | 0.24% |
| 35 | `injection` | 16 | 0.23% |
| 36 | `length_map` | 16 | 0.23% |
| 37 | `map` | 15 | 0.22% |
| 38 | `replace` | 15 | 0.22% |
| 39 | `Lemma` | 13 | 0.19% |
| 40 | `nth_error` | 11 | 0.16% |

## Declaration Kinds

| Declaration kind | Steps | Share |
| --- | ---: | ---: |
| `Lemma` | 4884 | 70.11% |
| `Theorem` | 2054 | 29.49% |
| `Corollary` | 28 | 0.40% |

## File Concentration

The top 10 files contain **3376 extracted steps** (**48.46%** of the corpus). These files are useful places to inspect when looking for hard proof patterns, missing tactics, or overrepresented training examples.

| Rank | File | Steps | Share |
| ---: | --- | ---: | ---: |
| 1 | `Group.v` | 576 | 8.27% |
| 2 | `FreeGroup.v` | 479 | 6.88% |
| 3 | `Order/IdealLifting.v` | 399 | 5.73% |
| 4 | `Galois/Field.v` | 393 | 5.64% |
| 5 | `Order/Ideal.v` | 390 | 5.60% |
| 6 | `Order/Adjunction.v` | 266 | 3.82% |
| 7 | `Category/FunctorCategoryLimits.v` | 235 | 3.37% |
| 8 | `ATT/Syntax.v` | 229 | 3.29% |
| 9 | `ATT/ClassifyingCategory.v` | 208 | 2.99% |
| 10 | `AG.v` | 201 | 2.89% |
| 11 | `Kahler/sl2/Basic.v` | 199 | 2.86% |
| 12 | `Category/Products.v` | 196 | 2.81% |
| 13 | `Category/UnderLimits.v` | 194 | 2.78% |
| 14 | `AxTheory/Syntax.v` | 192 | 2.76% |
| 15 | `Category/AdjunctionLimits.v` | 187 | 2.68% |
| 16 | `Character.v` | 175 | 2.51% |
| 17 | `Galois/Correspondence.v` | 153 | 2.20% |
| 18 | `Order/Lattice.v` | 125 | 1.79% |
| 19 | `Order/DCPO.v` | 112 | 1.61% |
| 20 | `AxTheory/ClassifyingCategory.v` | 96 | 1.38% |
| 21 | `ATT/Model.v` | 92 | 1.32% |
| 22 | `Category/Coproducts.v` | 80 | 1.15% |
| 23 | `ManifoldTopology.v` | 79 | 1.13% |
| 24 | `Category/Comma.v` | 77 | 1.11% |
| 25 | `Representation.v` | 72 | 1.03% |

## Module Concentration

The top 10 modules contain **6728 extracted steps** (**96.58%** of the corpus). A highly concentrated module distribution can make random train/test splits look better than cross-module generalization would be.

| Rank | Module | Steps | Share |
| ---: | --- | ---: | ---: |
| 1 | `.` | 1796 | 25.78% |
| 2 | `Order` | 1411 | 20.26% |
| 3 | `Category` | 1328 | 19.06% |
| 4 | `ATT` | 603 | 8.66% |
| 5 | `Galois` | 603 | 8.66% |
| 6 | `AxTheory` | 379 | 5.44% |
| 7 | `Kahler` | 265 | 3.80% |
| 8 | `Harmonic` | 167 | 2.40% |
| 9 | `NeuralOp` | 99 | 1.42% |
| 10 | `Projective` | 77 | 1.11% |
| 11 | `Kodaira` | 68 | 0.98% |
| 12 | `Divisor` | 57 | 0.82% |
| 13 | `Vanishing` | 33 | 0.47% |
| 14 | `Blowup` | 19 | 0.27% |
| 15 | `Hypersurface` | 19 | 0.27% |
| 16 | `CanonicalBundle` | 16 | 0.23% |
| 17 | `Residue` | 12 | 0.17% |
| 18 | `Hodge` | 11 | 0.16% |
| 19 | `Presheaf` | 3 | 0.04% |

## Longest Extracted Proofs

The longest proofs are especially useful for qualitative analysis because they often expose missing automation, repeated proof idioms, or places where tactic prediction needs richer proof-state features.

| Rank | Steps | Declaration | File |
| ---: | ---: | --- | --- |
| 1 | 139 | `functor_category_limits` | `Category/FunctorCategoryLimits.v` |
| 2 | 132 | `under_forget_preserves_limits` | `Category/UnderLimits.v` |
| 3 | 124 | `image_K_is_subfield` | `Galois/Field.v` |
| 4 | 108 | `XY_primitive_identity` | `Kahler/sl2/Basic.v` |
| 5 | 105 | `field_hom_injective` | `Galois/Field.v` |
| 6 | 96 | `eval_preserves_limits` | `Category/FunctorCategoryLimits.v` |
| 7 | 90 | `fixed_pred_is_subfield` | `Galois/Correspondence.v` |
| 8 | 88 | `left_adjoint_preserves_colimits` | `Category/AdjunctionLimits.v` |
| 9 | 83 | `prod_assoc` | `Category/Products.v` |
| 10 | 77 | `right_adjoint_preserves_limits` | `Category/AdjunctionLimits.v` |
| 11 | 72 | `ideal_lift_universal` | `Order/IdealLifting.v` |
| 12 | 70 | `ideal_lift_jsl_all_joins` | `Order/IdealLifting.v` |
| 13 | 67 | `compact_ideal_is_principal` | `Order/Ideal.v` |
| 14 | 65 | `theta_iso` | `Order/IdealLifting.v` |
| 15 | 64 | `ideal_generated_is_ideal` | `Order/Ideal.v` |
| 16 | 63 | `ideal_completion_algebraic` | `Order/Ideal.v` |
| 17 | 61 | `cl_bp_uniq` | `ATT/ClassifyingCategory.v` |
| 18 | 60 | `under_category_limits` | `Category/UnderLimits.v` |
| 19 | 57 | `rhom_neg` | `Galois/Field.v` |
| 20 | 56 | `ideal_lift_cont` | `Order/IdealLifting.v` |
| 21 | 54 | `finite_and_directed_to_all_joins` | `Order/Adjunction.v` |
| 22 | 54 | `jsl_to_ideal_preserves_join` | `Order/Ideal.v` |
| 23 | 53 | `fno_layer_length` | `NeuralOp/FNO.v` |
| 24 | 49 | `finite_sups_directed` | `Order/Adjunction.v` |
| 25 | 47 | `ax_lift_preserves_type_gen` | `AxTheory/Syntax.v` |

## Notes For Model Training

For neural tactic prediction, the action distribution gives the first label vocabulary. The raw-token table tells us which labels are being hidden inside `other`. The proof length and file/module concentration sections warn about possible dataset leakage: a model can learn project-local style if train and holdout examples are split randomly across the same files. A stronger evaluation should eventually include file-level or module-level holdout splits.

The current extractor is good enough for baseline tactic-label experiments and corpus statistics. The next major improvement is semantic extraction of live goals, hypotheses, conclusion heads, and Rocq term structure so that the token, tree/graph, transformer, and ranker models can learn from proof states rather than proof-script metadata alone.
