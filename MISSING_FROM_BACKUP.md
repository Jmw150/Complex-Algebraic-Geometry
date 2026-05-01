# Proofs in ~/cag (backup) missing from ~/Complex-Algebraic-Geometry

Generated 2026-04-30. Compares top-level proof declarations (Theorem / Lemma /
Corollary / Proposition / Fact / Remark / Example / Property / Instance, plus
Program-prefixed variants) by name.

- backup `~/cag`: 2479 proofs across 2465 unique names
- current `~/Complex-Algebraic-Geometry`: 2288 proofs across 2213 unique names
- **609 names exist in cag but not in current**, spread over 84 files
- 0 .v files exist only in backup (every backup file has a current counterpart)
- 4 .v files exist only in current: `theories/Control/Geometric.v`,
  `theories/DecisionProblems/FiniteLifts.v`, `theories/DiffGeom/SmoothManifold.v`,
  `theories/Langlands/AbelianLanglands.v` (plus 3 stray `.cag/*.v` scratch files)

Spot-checked 10 names by full-tree grep — all 10 are genuinely absent from
current, not renamed. The diff is a real deletion, not a refactor.

## Top files by missing-proof count

| count | file |
|------:|------|
| 156 | theories/DecisionProblems/HallTheorem.v |
| 114 | theories/LinAlg/SL2Fricke.v |
|  94 | theories/Rings/Polynomial.v |
|  31 | theories/Lie/Linear.v |
|  23 | theories/Groups/DirectProduct.v |
|  10 | theories/Sheaves.v |
|   7 | theories/Kahler/sl2/Vm.v |
|   7 | theories/Residue/PoincareResidue.v |
|   6 | theories/Harmonic/RieszResolvent.v |
|   6 | theories/Langlands/HiggsBundles.v |
|   6 | theories/LinAlg/Concrete.v |
|   6 | theories/LinAlg/KillingLa3.v |
|   6 | theories/LinAlg/SL2.v |
|   6 | theories/Projective/FunctionFields.v |
|   5 | theories/Harmonic/Spectral.v |
|   5 | theories/Langlands/BeilinsonBernstein.v |
|   5 | theories/ManifoldTopology.v |

(See `/tmp/proof_diff.json` for the full machine-readable list with line numbers.)

## Notable individually-named missing theorems

These are big-name results whose absence is most likely to matter:

- `wirtinger_formula`, `d_eq_del_plus_dbar`, `jacobian_det_identity` (AG.v)
- `dolbeault_isomorphism`, `hodge_symmetry` (Vanishing/KodairaVanishing.v)
- `serre_duality_Pn`, `serre_duality_vb` (CanonicalBundle/, Vanishing/)
- `borel_weil`, `borel_weil_bott`, `harish_chandra_isomorphism` (Langlands/)
- `kahler_identity_1`, `kahler_identity_2`, `kahler_laplacians_equal`,
  `dbar_d_lemma` (Harmonic/KahlerCurvature.v)
- `elliptic_regularity` (Harmonic/Laplacian.v)
- `riesz_representation`, `rellich_compactness` (Harmonic/)
- `spectral_decomposition`, `harmonic_finite_dim` (Harmonic/Spectral.v)
- `hard_lefschetz`-adjacent: `HdR_finite_dim`, `Lambda_op_adjoint`,
  `primitive_hodge_decomposition` (Kahler/Lefschetz/)
- `canonical_bundle_plane_curve`, `conormal_exact_sequence` (CanonicalBundle/)
- `degree_equals_curvature_integral` (Divisor/RiemannSurfaceDegree.v)
- `meromorphic_is_rational`, `meromorphic_is_rational_Pn`,
  `holomorphic_maps_are_algebraic` (Projective/FunctionFields.v)
- `long_exact_residue_sequence`, `poincare_residue_well_defined`,
  `residue_surjective_surface_P3` (Residue/PoincareResidue.v)
- `deRham_theorem`, `dolbeault_comparison`, `mittag_leffler_obstruction`,
  `cech_simplicial_comparison`, `long_exact_sequence` (Sheaves.v)
- `transversality_exists`, `product_poincare_dual`, `pullback_poincare_dual`
  (ManifoldTopology.v)
- `simple_order_60_is_A5` (Sylow/Applications.v)
- `A5_simple_via_conjugacy_classes` (Conjugacy/ClassEquation.v)
- `char_orthogonality_first` (Character.v)
- `galois_unit` (Galois/Correspondence.v)
- `recognition_theorem` (Groups/SemidirectProduct.v)
- `quotient_direct_product_iso_product_quotients`, `sylow_in_product`,
  `center_direct_product` (Groups/DirectProduct.v)
- Hall-theorem entire infrastructure (156 lemmas/theorems in
  DecisionProblems/HallTheorem.v including `F_n_infinite`, `F_n_non_abelian`,
  `F_1_classification`, `hall_construction_separates_r0`, etc.)
- SL2/Fricke/trace combinatorics (114 in LinAlg/SL2Fricke.v including
  `sl2_3gen_param_A/B/C`, `sl2_lie_group_commutator_identity`, the whole
  `gamma_pow_*` family)
- Polynomial algebra core (94 in Rings/Polynomial.v including `peval_pmul_comm`,
  `peval_pmul_assoc`, `D_pcomp_pequiv`, `peval_pcomp`, `peval_pcomp_assoc`)

Per the 2026-04-30 dead-math incident note: do **not** mass-delete unused
theorems. These should be restored unless the user explicitly intends to drop
them.
