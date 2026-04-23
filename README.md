# Complex Algebraic Geometry

This project is a Rocq/Coq formalization effort built around a constructive foundation for complex algebraic geometry following "Principles of Algebraic Geometry" by Griffiths and Harris, "Introduction to Lie Algebras and Representation Theory" by Humphreys, and "Categories for Types" by Crole, and some constructive analysis.

The project starts from constructive Cauchy reals, builds complex numbers on
top of them, and then uses that base to develop a broad library touching:

- complex analysis
- complex manifolds
- category theory and internal language machinery
- divisors, line bundles, and canonical bundles
- projective and algebraic geometry
- harmonic, Kähler, and Hodge-theoretic structures
- `sl2` representation theory in support of Lefschetz-style arguments

This repository is not just “complex numbers in Coq.” It is an attempt to build
a substantial geometric library on a constructive analytic foundation.

## What Is Here

The main development lives in [`theories/`](/home/jmw150/backup/code/projects/cag/theories).
At the moment the project contains about 120 theory files spanning several
mathematical layers.

Some good entry points are:

- [theories/Complex.v](/home/jmw150/backup/code/projects/cag/theories/Complex.v:1)
  for the constructive complex-number layer
- [theories/ComplexAnalysis.v](/home/jmw150/backup/code/projects/cag/theories/ComplexAnalysis.v:1)
  and [theories/ComplexAnalysis2.v](/home/jmw150/backup/code/projects/cag/theories/ComplexAnalysis2.v:1)
  for analytic structure
- [theories/Category](/home/jmw150/backup/code/projects/cag/theories/Category)
  for categorical infrastructure
- [theories/Galois](/home/jmw150/backup/code/projects/cag/theories/Galois)
  for field extensions and Galois correspondence
- [theories/Divisor](/home/jmw150/backup/code/projects/cag/theories/Divisor),
  [theories/Projective](/home/jmw150/backup/code/projects/cag/theories/Projective),
  and [theories/CanonicalBundle](/home/jmw150/backup/code/projects/cag/theories/CanonicalBundle)
  for algebraic-geometric constructions
- [theories/Harmonic](/home/jmw150/backup/code/projects/cag/theories/Harmonic)
  and [theories/Kahler](/home/jmw150/backup/code/projects/cag/theories/Kahler)
  for Hodge/Kähler/Lefschetz material
- [theories/ATT](/home/jmw150/backup/code/projects/cag/theories/ATT)
  and [theories/AxTheory](/home/jmw150/backup/code/projects/cag/theories/AxTheory)
  for internal-language and classifying-category developments

## Through-Line

The intended mathematical story is:

1. constructive Cauchy reals
2. constructive complex numbers
3. complex analysis and complex manifolds
4. line bundles, divisors, projective geometry, and algebraic geometry
5. harmonic and Kähler methods
6. representation theory as a tool for Lefschetz and Hodge-type arguments

That is why the repository contains both foundational files like
[`Complex.v`](/home/jmw150/backup/code/projects/cag/theories/Complex.v:1)
and higher-level targets such as Kodaira-style, Lefschetz-style, vanishing, and
adjunction-type developments.

## Stronger Completed Pieces

The project is broad and uneven, but several parts already look like genuine
formal mathematics rather than just scaffolding.

Some especially strong areas are:

- [theories/Category/Yoneda.v](/home/jmw150/backup/code/projects/cag/theories/Category/Yoneda.v:1)
  for a polished Yoneda lemma / Yoneda embedding development
- [theories/Order/Ideal.v](/home/jmw150/backup/code/projects/cag/theories/Order/Ideal.v:1)
  for ideal completion and algebraic complete lattice structure
- [theories/Galois/Field.v](/home/jmw150/backup/code/projects/cag/theories/Galois/Field.v:1)
  for nontrivial field-homomorphism infrastructure
- [theories/Kahler/sl2/Basic.v](/home/jmw150/backup/code/projects/cag/theories/Kahler/sl2/Basic.v:1)
  for `sl2` weight-shift lemmas and primitive-orbit calculations used in the
  Hard Lefschetz story
- [theories/Harmonic/Spectral.v](/home/jmw150/backup/code/projects/cag/theories/Harmonic/Spectral.v:112)
  for some readable harmonic-analysis style arguments such as
  `harmonic_implies_dbar_zero`

These files are good places to look if you want proofs that are more than
boilerplate and that can be compared fruitfully with textbook arguments.

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

There is a mix of:

- concrete definitions and infrastructure
- fully proved lemmas and theorems
- long formal proofs in support libraries
- higher-level theorem statements with partially axiomatized background
- some files with substantial use of `Admitted`

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

1. [theories/Complex.v](/home/jmw150/backup/code/projects/cag/theories/Complex.v:1)
2. [theories/ComplexAnalysis.v](/home/jmw150/backup/code/projects/cag/theories/ComplexAnalysis.v:1)
3. [theories/Category/Yoneda.v](/home/jmw150/backup/code/projects/cag/theories/Category/Yoneda.v:1)
4. [theories/Order/Ideal.v](/home/jmw150/backup/code/projects/cag/theories/Order/Ideal.v:1)
5. [theories/Galois/Field.v](/home/jmw150/backup/code/projects/cag/theories/Galois/Field.v:1)
6. [theories/Kahler/sl2/Basic.v](/home/jmw150/backup/code/projects/cag/theories/Kahler/sl2/Basic.v:1)

If you want examples of presentation-friendly proof candidates, see:

- [docs/presentation-proof-candidates.md](/home/jmw150/backup/code/projects/cag/docs/presentation-proof-candidates.md:1)

## Building

The project includes generated Rocq/Coq makefiles at the repository root.

Typical commands are:

```bash
make
```

or, if you want to focus on theories:

```bash
make -C theories
```

The logical namespace is declared in [`_CoqProject`](/home/jmw150/backup/code/projects/cag/_CoqProject:1).

## Summary

The best short description of this repository is:

Constructive complex geometry in Rocq, growing from Cauchy reals into category
theory, Galois theory, projective geometry, harmonic/Kähler methods, and
representation theory, with an eye toward Griffiths-Harris-style mathematics.
