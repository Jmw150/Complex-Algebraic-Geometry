# Remaining Theorem Bottlenecks: 2026-04-20

This note records what appears to be blocking the last large batch of unresolved
theorems in `CAG`, especially the final few hundred admitted statements.

The short version is:

- many of the remaining theorems are not merely "hard proofs";
- they depend on missing definitions, quotient constructions, analytic
  infrastructure, or setoid/equality bridges;
- several top-level files are intentionally interface-first and currently use
  axiomatized placeholders rather than executable or proof-friendly structures.

## Snapshot

Quick grep inventory at the time of writing:

- `.v` files under `theories/`: `121`
- admitted-style matches under `theories/`: `442`

Largest admit clusters:

- [theories/ManifoldTopology.v](../theories/ManifoldTopology.v): `67`
- [theories/AG.v](../theories/AG.v): `42`
- [theories/ComplexAnalysis2.v](../theories/ComplexAnalysis2.v): `31`
- [theories/LieAlgebra.v](../theories/LieAlgebra.v): `21`
- [theories/Sheaves.v](../theories/Sheaves.v): `18`
- [theories/Divisor/LineBundleCech.v](../theories/Divisor/LineBundleCech.v): `18`
- [theories/ComplexAnalysis.v](../theories/ComplexAnalysis.v): `15`
- [theories/NeuralOp/DFT.v](../theories/NeuralOp/DFT.v): `14`
- [theories/Harmonic/Sobolev.v](../theories/Harmonic/Sobolev.v): `14`

These counts strongly suggest the project is currently bottlenecked by a handful
of foundational layers rather than by isolated difficult lemmas.

## What Seems Missing

### 1. A bridge from constructive-real equivalence to usable proof equality

This shows up repeatedly around `CComplex`, matrix algebra, and algebraic
geometry.

Relevant places:

- [theories/Complex.v](../theories/Complex.v:102)
- [theories/AG.v](../theories/AG.v:930)
- [theories/LieAlgebra.v](../theories/LieAlgebra.v:57)

Symptoms:

- arithmetic naturally proves `CRealEq` facts, not strict Coq `=`;
- many algebraic statements over `CComplex` would be easier if the library had a
  systematic setoid story;
- proofs become fragile because every rewrite must manually navigate between
  definitional equality, `CRealEq`, and componentwise complex equality.

What is missing:

- a consistent setoid interface for `CComplex`;
- `Proper` instances for key operations like `Cadd`, `Cmul`, matrix operations,
  traces, polynomials, and norms;
- a documented policy for when statements should use `=` and when they should
  use `~~C`.

Why this matters:

- many “simple algebra” theorems are artificially hard until rewriting under the
  intended equality notion becomes routine.

### 2. A more robust linear algebra and matrix library

The project has enough matrix definitions to state many results, but not yet
enough proved infrastructure to make higher theorems cheap.

Relevant places:

- [theories/AG.v](../theories/AG.v:200)
- [theories/Character.v](../theories/Character.v:37)
- [theories/LieAlgebra.v](../theories/LieAlgebra.v:264)

Symptoms:

- matrix operations are defined on lists with truncating behavior;
- dimension correctness is carried by side conditions such as `Mat_wf`;
- foundational facts like associativity, cyclic trace, additive inverses,
  compatibility with well-formedness, and distributivity are still missing or
  only partially proved.

What is missing:

- a dimension-safe matrix representation, or at least a disciplined wrapper
  around the current list-based one;
- a proved basis of matrix algebra lemmas;
- better lemmas connecting `Mat_wf` to row/column operations automatically.

Why this matters:

- a lot of representation theory, Lie algebra, and character theory sits on top
  of these facts.

### 3. Concrete quotient and subtype infrastructure

Some group-theoretic developments are blocked because the code can state
quotients but not construct them comfortably.

Relevant places:

- [theories/Group.v](../theories/Group.v:529)
- [theories/Group.v](../theories/Group.v:532)
- [theories/Group.v](../theories/Group.v:1222)

Symptoms:

- quotient carrier and quotient group operations are admitted;
- subgroup-restricted structures are awkward to express;
- standard algebraic constructions become “one theorem away” from requiring a
  whole quotient framework.

What is missing:

- a reusable quotient/setoid construction strategy;
- support for subgroup-induced `StrictGroup` structures and related transport;
- better infrastructure for finite group quotients and normal subgroup
  arguments.

Why this matters:

- this blocks deeper group theory and anything that wants clean isomorphism or
  quotient-based arguments.

### 4. A real analytic library, not just interfaces

Several analysis-heavy files are explicitly written as theorem interfaces with
admitted analytic content.

Relevant places:

- [theories/ComplexAnalysis.v](../theories/ComplexAnalysis.v:17)
- [theories/ComplexAnalysis2.v](../theories/ComplexAnalysis2.v:35)
- [theories/NeuralOp/DFT.v](../theories/NeuralOp/DFT.v:27)
- [theories/NeuralOp/FNO.v](../theories/NeuralOp/FNO.v:54)

Symptoms:

- `sin`, `cos`, `exp(iθ)`, `π`, cutoff functions, partitions of unity, and
  smoothness facts are axiomatized or left abstract;
- Hartogs/Weierstrass/localization results are stated with placeholders;
- even basic neural-operator theorems depend on complex exponential and Fourier
  facts that have not been fully developed internally.

What is missing:

- a constructive complex-analysis toolkit with proved exponential/trigonometric
  identities;
- smooth partition-of-unity infrastructure;
- more genuine definitions and fewer placeholder `True`-style assumptions in
  SCV files.

Why this matters:

- many “advanced” theorems are currently blocked by missing first-order
  analytic primitives.

### 5. Concrete homology, cohomology, and integration models

Some of the heaviest topology and geometry files are interface layers, not full
formalizations yet.

Relevant places:

- [theories/ManifoldTopology.v](../theories/ManifoldTopology.v:68)
- [theories/ManifoldTopology.v](../theories/ManifoldTopology.v:115)
- [theories/Divisor/RiemannSurfaceDegree.v](../theories/Divisor/RiemannSurfaceDegree.v:118)
- [theories/Hodge/AnalyticClasses.v](../theories/Hodge/AnalyticClasses.v:59)

Symptoms:

- chain complexes, homology groups, intersection pairings, Poincare duality,
  Kunneth, and related maps are largely axiomatized;
- integrals and comparison maps are often placeholders;
- many later statements depend on these as if they were fully formalized.

What is missing:

- a chosen concrete model of chains/cochains/homology/cohomology;
- proved functoriality, exactness, pairing, and integration interfaces;
- compatibility lemmas between topological, Dolbeault, and de Rham viewpoints.

Why this matters:

- much of the algebraic geometry tower depends on this layer, so unresolved
  admits accumulate downstream.

### 6. Bundle, sheaf, and Čech infrastructure

There is a strong amount of geometry in the project, but several glueing and
cohomological mechanisms are still admitted at the interface level.

Relevant places:

- [theories/Sheaves.v](../theories/Sheaves.v)
- [theories/Divisor/LineBundleCech.v](../theories/Divisor/LineBundleCech.v:121)
- [theories/Divisor/DivisorBundle.v](../theories/Divisor/DivisorBundle.v:141)

Symptoms:

- line bundle classification, Čech cocycle equivalence, divisor-to-bundle
  correspondence, and curvature/cohomology links are often axiomatized;
- later vanishing and projective geometry results rely on these interfaces.

What is missing:

- better developed sheaf operations and Čech cohomology machinery;
- line-bundle pullback/restriction/tensor infrastructure;
- explicit comparison lemmas between divisors, bundles, and cohomology classes.

Why this matters:

- this is a core dependency for divisors, Chern classes, Kodaira-style theorems,
  and projective geometry.

### 7. Functional analysis and spectral theory infrastructure

The harmonic/Kähler side of the project depends on Sobolev and elliptic theory
that is mostly declared but not internally built.

Relevant places:

- [theories/Harmonic/Sobolev.v](../theories/Harmonic/Sobolev.v:3)
- [theories/Harmonic/Laplacian.v](../theories/Harmonic/Laplacian.v:159)
- [theories/Harmonic/Spectral.v](../theories/Harmonic/Spectral.v:52)
- [theories/Kahler/Signature.v](../theories/Kahler/Signature.v:48)

Symptoms:

- Sobolev spaces, compactness, embedding, spectral decompositions, and
  eigenvalue-based arguments are axiomatized;
- signature, positivity, and Hodge-theoretic results depend on these spaces as
  if the functional analysis were already available.

What is missing:

- an actual Hilbert-space style interface over constructive reals;
- compact/self-adjoint operator theory;
- eigenvalue counting and nondegeneracy infrastructure;
- a disciplined separation between axiomatized analysis and proved algebraic
  consequences.

Why this matters:

- many Kähler and vanishing results are currently blocked not by one proof, but
  by an entire undeveloped analysis layer.

### 8. Better finite-dimensional algebra infrastructure

The Lie algebra and representation layers still need some standard linear
algebra and module reasoning.

Relevant places:

- [theories/LieAlgebra.v](../theories/LieAlgebra.v:108)
- [theories/Kahler/Lefschetz/Primitive.v](../theories/Kahler/Lefschetz/Primitive.v:82)
- [theories/Kahler/Lefschetz/HardLefschetz.v](../theories/Kahler/Lefschetz/HardLefschetz.v:51)

Symptoms:

- direct sums, spans, dimensions, eigenspace decompositions, and nondegeneracy
  arguments are repeatedly deferred;
- many standard finite-dimensional arguments have no reusable library to call.

What is missing:

- a small but solid finite-dimensional vector space library;
- basis/span/direct-sum/isomorphism lemmas;
- matrix/Lie algebra compatibility results that avoid reproving routine facts.

Why this matters:

- otherwise every major theorem in representation theory or Hodge theory turns
  into a bespoke infrastructure project.

### 9. Fewer placeholders of the form `True`

Some files keep interfaces readable by inserting placeholders. That helps with
structure, but it also means many later theorems are not yet genuinely tied to
formal content.

Examples:

- [theories/ComplexAnalysis2.v](../theories/ComplexAnalysis2.v:97)
- [theories/Harmonic/BundleCovariantDerivatives.v](../theories/Harmonic/BundleCovariantDerivatives.v:30)
- [theories/Kahler/Lefschetz/Operators.v](../theories/Kahler/Lefschetz/Operators.v:29)
- [theories/Vanishing/TheoremB.v](../theories/Vanishing/TheoremB.v:76)

Why this matters:

- these placeholders keep files compilable, but they also prevent later proofs
  from being meaningful reductions to earlier established mathematics.

## Interpretation

The remaining admits are hard for three different reasons:

1. Some are ordinary missing lemmas.
   Example: matrix-additivity or row-length bookkeeping.

2. Some require medium-size library growth.
   Example: quotient groups, matrix setoid rewriting, finite-dimensional linear
   algebra.

3. Some require choosing and formalizing an entire semantic layer.
   Example: Sobolev spaces, homology/cohomology, integration, partitions of
   unity, spectral theory.

The current project contains many theorems in categories (2) and (3), so the
raw admit count overstates how many are “just waiting for clever proofs.”

## Most Valuable Missing Infrastructure

If the goal is to reduce the last ~400 theorems efficiently, the highest-leverage
additions look like this:

1. A `CComplex` setoid and rewrite-friendly algebra layer.
2. A proved core matrix library with dimension discipline.
3. Quotient/subtype infrastructure for algebraic constructions.
4. A small finite-dimensional linear algebra library.
5. A genuine interface for homology/cohomology and integration.
6. A clearer boundary between axiomatized analysis and proved consequences.

## Practical Next Steps

The most realistic path is probably:

1. Strengthen the algebra core.
   Finish `CComplex` equality infrastructure and matrix lemmas.

2. Reduce placeholder debt in one vertical slice.
   For example, fully support character/Lie/matrix results before trying to
   solve more Kähler or vanishing theorems.

3. Pick one semantic foundation to make concrete.
   Either:
   - homology/cohomology and integration, or
   - Sobolev/Hilbert/spectral infrastructure.

4. Avoid spreading new admits across additional top-level theories until one of
   those foundations is materially completed.

## Bottom Line

What is missing is not mainly “hard tactic work.” The project is missing several
foundational layers that higher theorems are currently pretending already
exist:

- equality/setoid infrastructure for constructive complex numbers,
- dependable matrix and linear algebra foundations,
- quotients and transports,
- concrete topology/cohomology/integration semantics,
- and real analytic / functional analytic machinery.

Until those layers are improved, many of the last 400 theorems will remain hard
for structural reasons rather than because the individual arguments are obscure.
