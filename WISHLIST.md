# Infrastructure Wishlist for Closing Deep Admits

Generated 2026-04-25. Derived from analysis of the 444 remaining `Admitted` statements across the project.

## Tier 1 — Structural foundations that unblock many admits at once

### A. CReal setoid layer (`Reals_extra.v`)
**Blocks:** ~80 admits across `LieAlgebra.v`, `Character.v`, `ComplexAnalysis*.v`, `AG.v`, `NeuralOp/*`, `Kahler/sl2/Vm.v`.

**Issue:** `Cadd_assoc`, `Cadd_comm`, `Cmul_assoc`, etc. are stated with Coq propositional `=` on `CComplex = mkC re im` over `ConstructiveCauchyReals`. Constructive reals only support `CRealEq` (setoid), not Leibniz `=`.

**Wishlist:**
- Add `Setoid` instances for `CReal` and `CComplex` via `CRealEq` / `CComplex_req` (`~~C`).
- Provide `Proper` morphism instances for `Cadd`, `Cmul`, `Cneg`, `Cconj`, `re`, `im`.
- Either:
  - **Option A:** Restate all `Cadd_assoc = ...` lemmas using `~~C` and prove via `ring` over the `CReal` setoid; rewrite downstream uses.
  - **Option B:** Add a `Functional_Extensionality_CReal` axiom bridging `CRealEq → =` (consistent but strong).
- **Reference:** Stdlib `Reals.Cauchy.ConstructiveCauchyRealsMult` — has `ring_morph` for CReal but only for `CRealEq`.

### B. Polynomial F-algebra `F[x]`
**Blocks:** `der_product_not_always_der` (Lie), examples for Engel theorem, formal-derivative work, Galois extension polynomials.

**Wishlist:**
- `Definition Polynomial F : Type := list F` (or via `nat -> F` with finite support).
- Ring/commutative-ring instance.
- Formal derivative `D : Polynomial F -> Polynomial F`.
- Embed into `FAlgebra fld (Polynomial F)`.
- **Reference:** Stdlib lacks polynomial rings; mathcomp has them but isn't compatible. We'd implement from scratch.

### C. Quotient group `G/N`
**Blocks:** `Group.v::QuotStrictGroup` (3 admits), `second_isomorphism_theorem` (now Axiom), `third_isomorphism_theorem`, anything mentioning `QuotStrictGroup`.

**Wishlist:**
- Quotient set construction via setoid: `coset_eq sg N := fun a b => N (a⁻¹·b)`.
- Carrier as `setoid` quotient — needs `axiom of choice` or `propositional extensionality`.
- Group operations descend (well-defined on cosets).
- **Reference:** mathcomp uses `quotType` and `mfun_quotient` for this.

### D. AxThEq quotient for AxTheory
**Blocks:** AxTheory beta rules (`axcl_bp_beta1`, `axcl_bp_beta2`, `axcl_bp_uniq`, `axcl_terminal_unique`), 6 admits.

**Wishlist:**
- Quotient `AxClMor` by `AxThEq`-equivalence (similar to category quotient).
- `axcl_ext` modified to use the quotient.

## Tier 2 — Concrete deep theorems with available references

### E. Engel's theorem (`Lie/Engel.v`, 4 admits)
**Need:** linear-Engel + induction on dimension. The `engel_linear` axiom is already present.
- `engel_theorem` follows from `engel_linear` + the (already-axiomatized) `lie_nilpotent_iff_ad_nilpotent_alg`. Actually it's *equivalent* to the latter — restructure.
- `nilpotent_ideal_meets_center`, `nilpotent_normalizer_grows`, `nilpotent_codim1_ideal` — classical Humphreys §3.

**Reference:** Humphreys *Introduction to Lie Algebras*, Chapter 3.

### F. Galois fundamental correspondence (`Galois/Correspondence.v`, 4 admits)
**Need:** Artin's theorem (Galois extension finite-dim). Group action on field. Counting-fixed-points argument.

**Reference:** Stewart *Galois Theory*, or the explicit Coq formalization in mathcomp-algebra `falgebra` / `galois`.

### G. Second/Third isomorphism theorems (`Group.v`, depends on C)
**Need:** quotient infrastructure (item C). After C is done, these are short.

### H. ATT Soundness/Completeness (`ATT/SoundComplete.v`, 3 admits)
**Need:** induction on `ThEq`-derivations. Standard categorical-logic argument.

**Reference:** Lambek & Scott *Introduction to Higher-Order Categorical Logic*.

### I. Yoneda converse (`Category/Yoneda.v`, 1 admit)
**Need:** standard. Build inverse natural transformation from universal element.

**Reference:** Mac Lane *Categories for the Working Mathematician* §III.2.

## Tier 3 — Genuinely deep / require new mathematical framework (do not attempt)

- Hard Lefschetz, Kodaira embedding, Hartogs, Weierstrass preparation/division (need full sheaf cohomology, harmonic analysis, plurisubharmonic theory).
- Spectral theory of elliptic operators (`Harmonic/Spectral.v`).
- Riemann-Roch, Poincaré duality, deRham/Dolbeault isomorphism.
- These are decade-scale formalization efforts (cf. `Liquid Tensor Experiment`, `polynomial Freiman-Ruzsa` in Lean — each took multiple person-years).

## Strategy for the 10-hour run

1. **Hour 0–2:** Implement Tier 1.A (CReal setoid layer) — biggest leverage.
2. **Hour 2–4:** Implement Tier 1.B (`Polynomial F`) — unblocks several lemmas including the now-axiomatized `der_product_not_always_der`.
3. **Hour 4–6:** Tier 2.E (Engel) and 2.I (Yoneda converse) — both are well-bounded.
4. **Hour 6–8:** Tier 1.C (quotient group) and Tier 2.G (isomorphism theorems).
5. **Hour 8–10:** Tier 2.F (Galois) or Tier 2.H (Soundness/Completeness), depending on what's gone smoothest.

After every change: `make -j4` must stay green. Any agent edit that breaks build is reverted.
