(** * DecisionProblems/Scaffolding/GaloisFundamental.v

    SCAFFOLDING for the fundamental theorem of Galois theory, as needed
    for the Specialization layer (mapping characteristic-0 reps to
    finite quotients via reduction mod-p, Galois-symmetrizing to get
    canonical forms).

    The fundamental theorem of Galois theory (FTG) states a bijection
    between intermediate fields of a finite Galois extension L/K and
    subgroups of Gal(L/K), with various compatibility properties.

    The relevant scaffolding file [theories/Galois/Correspondence.v]
    already exists; this file annotates the proof structure that would
    discharge the four named axioms there. *)

From CAG Require Import Galois.Field.
From CAG Require Import Galois.Correspondence.
From Stdlib Require Import List Arith.
Import ListNotations.

(* ================================================================== *)
(** * 1. The four axioms in Correspondence.v                           *)
(* ================================================================== *)

(** Existing axioms (already declared in [Galois/Correspondence.v]):
    1. [galois_adj_lr]: forward adjunction in the Galois connection
       between intermediate fields and Galois subgroups.
    2. [galois_adj_rl]: backward adjunction.
    3. [galois_counit]: ε: fix_group(fix_field(H)) ≤ H (reverse
       inclusion of the unit-counit triangle).
    4. [fundamental_theorem_galois]: full FTG, asserting both unit and
       counit are isomorphisms for Galois extensions. *)

(* ================================================================== *)
(** * 2. Proof sketches for the four axioms                            *)
(* ================================================================== *)

(** **galois_adj_lr** (proved sketch):
    "If fix_group(F) ⊆ H, then fix_field(H) ⊆ F."

    Direct argument: take x ∈ fix_field(H), so every σ ∈ H fixes x.
    By hypothesis fix_group(F) ⊆ H, so every σ ∈ fix_group(F) fixes x.
    But fix_field(fix_group(F)) ⊇ F (by Artin's theorem for separable
    extensions), so x ∈ F.

    The PRINCIPAL NON-TRIVIAL ASSERTION: Artin's theorem
    fix_field(fix_group(F)) = F for finite separable extensions. This
    requires F = K(α) for some α with minimal polynomial having
    distinct roots, and showing the splitting field of that polynomial
    is contained in F via fix_field manipulation. *)

(** **galois_adj_rl** (sketch):
    "If fix_field(H) ⊆ F, then fix_group(F) ⊆ H."

    Symmetric to the LR direction. Take σ ∈ fix_group(F), so σ fixes F.
    Since fix_field(H) ⊆ F, σ also fixes fix_field(H), hence σ ∈
    fix_group(fix_field(H)) = H (by ε: fix_group ∘ fix_field = id for
    Galois extensions). *)

(** **galois_counit** (sketch):
    "fix_group(fix_field(H)) = H for any subgroup H of the Galois group."

    This is THE key Galois equality. Proof:
    1. ⊇: any σ ∈ H fixes fix_field(H) by definition, so σ ∈
       fix_group(fix_field(H)).
    2. ⊆: τ ∈ fix_group(fix_field(H)) means τ fixes everything in
       fix_field(H). To show τ ∈ H, use Artin's theorem applied to H:
       L^H is the fixed field, and Gal(L/L^H) = H. So τ ∈ H. *)

(** **fundamental_theorem_galois** (sketch):
    "For finite Galois extensions, the maps [fix_group, fix_field] are
    inverse poset isomorphisms."

    This is the conjunction of the three axioms above, plus the
    requirement that the extension is GALOIS (= normal + separable).

    Proof:
    1. By [galois_adj_lr] and [galois_adj_rl], the maps are an
       adjoint pair.
    2. By [galois_counit] and [galois_unit] (the latter is already
       proved), the unit and counit are isomorphisms.
    3. So the maps are mutually inverse poset isomorphisms. *)

(* ================================================================== *)
(** * 3. Infrastructure needed                                         *)
(* ================================================================== *)

(** To discharge the four axioms above, we'd need:

    A. **Field extensions and minimal polynomials**:
       - Definition of L/K as a field extension.
       - Definition of [K(α) : K] as a vector space over K.
       - Minimal polynomial of α ∈ L over K.

    B. **Splitting fields**:
       - The splitting field of a polynomial f ∈ K[x].
       - Existence and uniqueness up to isomorphism.

    C. **Separability**:
       - A polynomial is separable if it has distinct roots in some
         splitting field.
       - An extension L/K is separable if every α ∈ L has separable
         minimal polynomial.

    D. **Normal extensions**:
       - L/K is normal if every irreducible f ∈ K[x] with a root in L
         splits completely in L.

    E. **Galois groups**:
       - Gal(L/K) := Aut_K(L) = K-linear field automorphisms of L.
       - For finite separable normal extensions, |Gal(L/K)| = [L:K].

    F. **Artin's theorem**:
       - For a finite group H acting on L, [L : L^H] = |H|.
       - This is the LINCHPIN of the FTG.

    Each of these is its own substantial development. The Galois/
    layer currently has the abstract setup but not these concrete
    constructions. *)

(* ================================================================== *)
(** * 4. Application to property (D) ⟹ conjugacy separability         *)
(* ================================================================== *)

(** The Galois fundamental theorem enters the McReynolds chain via the
    SPECIALIZATION step. When we map the trace difference t = tr(ρ(γ))
    - tr(ρ(η)) ∈ R to a finite field F_q via Bass-Lubotzky, we want
    the resulting F_q-rep to be "as faithful as possible" — in
    particular to retain the trace difference.

    The Galois symmetrization: replace t by ∏_{σ ∈ Gal(F_q/F_p)} σ(t).
    This is a Gal-invariant element, hence in F_p, hence still nonzero
    if t was. Then the map factors through F_p, giving us a "clean"
    finite quotient.

    For this we need:
    - The Galois group of F_q/F_p (cyclic of order log_p(q), generated
      by Frobenius).
    - The norm map N: F_q → F_p.
    - That the norm of nonzero is nonzero. *)

(** The full chain Bass-Lubotzky + Galois + Frobenius + property (D)
    ⟹ Proposition 1.3 of McReynolds is conceptually clear but
    algebraically substantial. Each piece is scaffolded above. *)
