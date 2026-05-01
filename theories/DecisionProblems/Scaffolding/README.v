(** * DecisionProblems/Scaffolding/README.v

    Index of scaffolding files for the deep classical theorems needed
    to attack the McReynolds open problems.

    Each scaffolding file:
    1. States the relevant theorem(s) as named [Axiom]s with full
       hypotheses.
    2. Decomposes the proof into intermediate lemmas (also axiomatized).
    3. Gives a detailed proof sketch in comments.
    4. Lists the additional infrastructure needed to discharge each
       intermediate axiom.

    These are NOT proofs — they're roadmaps. The intent is that future
    work can pick up any one of these scaffolds, develop the
    infrastructure, and discharge the axioms one by one.

    ## Files

    - [Procesi.v]: Procesi's invariant-theory theorem on n×n matrices.
      Needed for: open_SLn_trace_pair n=3+, GIT-orbit ⟹ conjugacy.

    - [HallFreeGroup.v]: Hall's theorems on subgroups of free groups
      (proper finitely-generated case, free factor decomposition).
      Needed for: theorem_1_6_free_groups (property B for F_r).

    - [BassLubotzky.v]: specialization theorem for f.g. integral
      domains (mapping nonzero elements to nonzero in some finite
      field).
      Needed for: proposition_1_3 (property D ⟹ conjugacy separable).

    - [BaireRepVarieties.v]: Baire-category argument in algebraic /
      analytic representation varieties.
      Needed for: open_question_1_10 (uniform C ⟺ uniform D).

    - [GaloisFundamental.v]: fundamental theorem of Galois theory
      (annotation of the existing axiomatization in
      Galois/Correspondence.v).
      Needed for: Galois symmetrization in the
      Specialization → Frobenius chain.

    ## Status

    All five scaffolds: AXIOMATIZED with proof sketches. None of the
    underlying classical results have been formalized in Coq for this
    project; each represents 100s-1000s of pages of mathematical theory
    plus the corresponding Coq library development.

    The scaffolds make explicit the "modular" structure of the open
    problem attack: each open problem reduces to one or two of the
    scaffolded theorems plus the structural/reduction lemmas already
    proven in [DecisionProblems/OpenProblems.v] and
    [DecisionProblems/TraceProperties.v]. *)

From CAG Require Import DecisionProblems.Scaffolding.Procesi.
From CAG Require Import DecisionProblems.Scaffolding.HallFreeGroup.
From CAG Require Import DecisionProblems.Scaffolding.BassLubotzky.
From CAG Require Import DecisionProblems.Scaffolding.BaireRepVarieties.
From CAG Require Import DecisionProblems.Scaffolding.GaloisFundamental.
