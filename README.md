# Complex Algebraic Geometry

This project is a Rocq/Coq formalization effort built around a constructive foundation for complex algebraic geometry following "Principles of Algebraic Geometry" by Griffiths and Harris, "Introduction to Lie Algebras and Representation Theory" by Humphreys, and "Categories for Types" by Crole, and some constructive analysis.

## What Is Here

The main development lives in [`theories/`](cag/theories).
At the moment the project contains about 120 theory files spanning several
mathematical layers.

## Through-Line

The intended mathematical story is:

1. constructive Cauchy reals
2. constructive complex numbers
3. complex analysis and complex manifolds
4. line bundles, divisors, projective geometry, and algebraic geometry
5. harmonic and Kähler methods
6. representation theory as a tool for Lefschetz and Hodge-type arguments

That is why the repository contains both foundational files like
[`Complex.v`](cag/theories/Complex.v:1)
and higher-level targets such as Kodaira-style, Lefschetz-style, vanishing, and
adjunction-type developments.

## Named Theorem Targets

One of the interesting things about this repository is how many well-known
theorem targets it reaches toward. The codebase contains developments and named
statements related to:

- the Yoneda lemma
- the fundamental theorem of Galois theory
- Hard Lefschetz
- Hodge-Riemann bilinear relations
- Kodaira embedding / algebraicity criteria
- Kodaira vanishing
- Lefschetz hyperplane statements
- Theorem B
- Poincaré residue and adjunction-type formulas
- Bézout-type intersection statements

So this is not a repository of isolated exercises. It is clearly aiming at
standard landmark mathematics.

## Current Status

This project should be read as an active formalization project, not as a
finished uniform library.

In practice that means:

- the infrastructure and bridge lemmas are often the most convincing completed
  parts
- many of the famous high-level algebraic-geometry and Hodge-theory theorem
  names are present, but some of those files are still scaffolded
- the mathematical ambition is already visible even where the final theorem
  proofs are not yet fully closed

This is especially true in the harmonic, vanishing, and top-level Kähler
directories, where the project is clearly building toward major results but is
not yet uniformly finished.

## Why The Project Is Interesting

The interesting part is not only the list of theorem names. It is the
combination of:

- constructive Cauchy-real foundations
- a push toward complex and algebraic geometry
- interaction with category theory and internal language
- representation-theoretic support for Lefschetz/Hodge arguments

That combination is unusual. Even where a theorem is standard mathematics, the
route taken by the project is distinctive.

## Reading Suggestions

If you want a quick sense of the project, a good reading path is:

1. [theories/Complex.v](cag/theories/Complex.v:1)
2. [theories/ComplexAnalysis.v](cag/theories/ComplexAnalysis.v:1)
3. [theories/Category/Yoneda.v](cag/theories/Category/Yoneda.v:1)
4. [theories/Order/Ideal.v](cag/theories/Order/Ideal.v:1)
5. [theories/Galois/Field.v](cag/theories/Galois/Field.v:1)
6. [theories/Kahler/sl2/Basic.v](cag/theories/Kahler/sl2/Basic.v:1)

If you want examples of presentation-friendly proof candidates, see:

- [docs/presentation-proof-candidates.md](cag/docs/presentation-proof-candidates.md:1)

## Building

The project includes generated Rocq/Coq makefiles at the repository root.

Typical commands are:

```bash
cd theories
make
```

or, if you want the numerical tools.

```bash
dune build
cd theories
make
```

