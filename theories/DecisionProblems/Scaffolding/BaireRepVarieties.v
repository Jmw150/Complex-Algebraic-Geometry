(** * DecisionProblems/Scaffolding/BaireRepVarieties.v

    SCAFFOLDING for the Baire-category argument needed in the McReynolds
    uniform (C) ⟹ uniform (D) implication, i.e., open question 1.10.

    Setup: the representation variety Hom(F_r, SL(n, ℂ)) is an algebraic
    variety (more precisely, an algebraic scheme). The IRREDUCIBLE
    representations form an open subvariety. For a Baire-category
    argument, we work with the analytic (Hausdorff) topology where
    Hom(F_r, SL(n, ℂ)) is a complex manifold of dimension n²·r. *)

From CAG Require Import Galois.Field.
From CAG Require Import Group FreeGroup.
From CAG Require Import LinAlg.Matrix2 LinAlg.SL2.
From CAG Require Import DecisionProblems.TraceProperties.
From Stdlib Require Import List Arith.
Import ListNotations.

(* ================================================================== *)
(** * 1. The representation variety as a topological space             *)
(* ================================================================== *)

(** Hom(F_r, SL(n, F)) ≃ SL(n, F)^r as a set (assigning each
    generator to a matrix). Topologically, it's the product of r
    copies of SL(n, F).

    For F = ℂ, SL(n, ℂ) is a (n²-1)-dimensional complex Lie group,
    so Hom(F_r, SL(n, ℂ)) ≃ SL(n, ℂ)^r is a (r·(n²-1))-dim variety. *)

Section RepVariety.
  Context {F : Type} (fld : Field F).

  (** Representation variety as a tuple of generators. *)
  Definition rep_variety (r n : nat) : Type :=
    list (mg_carrier (SL2_as_MG fld)).
    (* For SL(2). For full SL(n) we'd need a generic n-matrix type. *)

  (** A representation in the variety is a list of length r. *)
  Definition is_rep_in_variety (r : nat) (rho_data : rep_variety r 2) : Prop :=
    List.length rho_data = r.

End RepVariety.

(* ================================================================== *)
(** * 2. Irreducible representations                                   *)
(* ================================================================== *)

(** A representation ρ : F_r → SL(n, ℂ) is IRREDUCIBLE if there's no
    nontrivial proper subspace V ⊊ ℂ^n preserved by every ρ(g).

    For F_r → SL(2, ℂ): ρ is irreducible iff ρ(F_r) doesn't fix any
    1-dimensional subspace iff there's no common eigenvector.

    Equivalently for F_2 = ⟨a, b⟩ → SL(2, ℂ) with A = ρ(a), B = ρ(b):
    ρ is REDUCIBLE iff A and B share an eigenvector, iff
    tr([A, B]_group) = 2 (cf. our Markov surface). *)

Definition is_reducible_2gen
    {F : Type} (fld : Field F)
    (A B : Mat2 F) : Prop :=
  (* A and B share an eigenvector v ∈ F^2. *)
  exists v : F * F,
    v <> (cr_zero fld, cr_zero fld) /\
    (* v is eigenvector for A *) True /\
    (* v is eigenvector for B *) True.

(** **CONNECTION TO MARKOV:** for SL(2,ℂ) and r=2, ρ is reducible iff
    tr(ρ([a,b]_group)) = 2. By our FMK identity:
      tr(A·B·adj(A)·adj(B)) = m(tr A, tr B, tr(A·B)) - 2.
    So reducible iff m(x, y, z) - 2 = 2 iff m(x, y, z) = 4. *)

(* ================================================================== *)
(** * 3. Baire category in algebraic varieties                         *)
(* ================================================================== *)

(** A topological space X has the BAIRE PROPERTY if a countable union
    of closed nowhere-dense subsets has empty interior, equivalently a
    countable intersection of open dense subsets is dense.

    Standard fact: any LOCALLY COMPACT HAUSDORFF space has the Baire
    property. SL(n, ℂ) is locally compact, hence Hom(F_r, SL(n, ℂ))
    has the Baire property.

    Standard fact: any COMPLETE METRIC SPACE has the Baire property.
    SL(n, ℂ) embeds in M_n(ℂ) ≃ ℂ^{n²}, which is a complete metric
    space; SL(n, ℂ) is closed in this embedding (cut out by det = 1)
    so is itself complete. *)

(** rep_variety_baire: the representation variety Hom(F_r, SL(n, C)) has
    the Baire property in its analytic topology.
    Informal: SL(n, C) embeds as a closed subset of M_n(C) = C^{n^2},
    a complete metric space; closed subspaces of complete metric spaces
    are themselves complete; hence SL(n, C) (and the r-fold product
    Hom(F_r, SL(n, C)) of it) is a complete metric space and so is Baire
    by Baire category theorem.  Pending the [BaireSpace] predicate;
    encoded as signature-bearing reflexive on (r, n).
    Ref: Baire, "Sur les fonctions de variables réelles" (1899);
    Royden "Real Analysis" §7.4 [Baire's theorem]; Munkres "Topology"
    §48; Rotman "Theory of Groups" §1 [SL(n,C) topology]. *)
(* CAG zero-dependent Conjecture rep_variety_baire theories/DecisionProblems/Scaffolding/BaireRepVarieties.v:100 BEGIN
Conjecture rep_variety_baire :
  forall (r n : nat),
    (r + n)%nat = (r + n)%nat.
   CAG zero-dependent Conjecture rep_variety_baire theories/DecisionProblems/Scaffolding/BaireRepVarieties.v:100 END *)

(* ================================================================== *)
(** * 4. The uniform (D) ⟹ uniform (C) attack                          *)
(* ================================================================== *)

(** **OPEN QUESTION 1.10 (one direction):** uniform (D) ⟹ uniform (C).

    uniform (D): there's n_0 such that for any non-conjugate γ, η, some
    ρ in dim n_0 separates them.
    uniform (C): there's n_0 such that for any FINITE list of words,
    some single ρ in dim n_0 separates all non-conjugate pairs in it.

    BAIRE-CATEGORY ARGUMENT:
    1. For each non-conjugate pair (γ, η), the set
         B(γ,η) := {ρ ∈ Hom(F_r, SL(n_0)) : tr(ρ(γ)) = tr(ρ(η))}
       is a closed algebraic subset of the rep variety (it's the
       vanishing locus of a polynomial).
    2. By uniform (D), for each (γ, η) the set B(γ,η) is a PROPER
       subset of Hom(F_r, SL(n_0)) (since SOME ρ separates them, the
       complement is nonempty).
    3. A proper closed subset of an irreducible variety has empty
       interior in the analytic topology.
    4. By Baire category, the countable union ⋃_{(γ,η)} B(γ,η) over
       non-conjugate pairs has empty interior.
    5. So there's an open dense set of ρ that separate ALL such pairs.
    6. Pick any such ρ → witnesses uniform (C). *)

(** Each step requires substantial infrastructure:
    - Step 1: trace difference is a polynomial; vanishing locus is
      algebraic ⟹ closed in analytic topology.
    - Step 2: uniform (D) gives existential, complementing gives the
      "some ρ doesn't satisfy B(γ,η)".
    - Step 3: irreducibility of Hom(F_r, SL(n)) — proven for n=2 by
      Goldman; general n by general representation variety theory.
    - Step 4: Baire applied to F_r-conjugacy classes (countably many).
    - Steps 5-6: select an actual representative. *)

(* CAG zero-dependent Conjecture uniform_D_implies_uniform_C_via_Baire theories/DecisionProblems/Scaffolding/BaireRepVarieties.v:140 BEGIN
Conjecture uniform_D_implies_uniform_C_via_Baire :
  forall {G F : Type} (sg : StrictGroup G) (MG_family : nat -> MatrixGroup F),
    (* Under suitable conditions on G (e.g., G = F_r) and the family
       MG_family (e.g., SL(n, ℂ) for n ≥ 2): *)
    uniform_D sg MG_family ->
    uniform_C sg MG_family.
   CAG zero-dependent Conjecture uniform_D_implies_uniform_C_via_Baire theories/DecisionProblems/Scaffolding/BaireRepVarieties.v:140 END *)

(* ================================================================== *)
(** * 5. What's still open                                              *)
(* ================================================================== *)

(** To formalize the Baire-category argument:
    1. Build a topology on representation varieties (analytic / Hausdorff).
    2. Prove SL(n, ℂ) is locally compact / a complete metric space.
    3. Prove the Baire property for the variety.
    4. Prove that trace-difference vanishing loci are closed.
    5. Prove that the rep variety is irreducible (so a proper closed
       subset has empty interior).

    Each of these is its own substantial topic. The full uniform (D)
    ⟹ uniform (C) implication is OPEN even informally — Baire-category
    suggests the right direction but the irreducibility gap (step 3)
    isn't trivially established. *)
