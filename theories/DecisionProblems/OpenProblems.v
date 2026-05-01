(** * DecisionProblems/OpenProblems.v

    Open problems and conjectures from
    Lawton–Louder–McReynolds (arXiv:1312.1261v3),
    "Decision problems, complexity, traces, and representations".

    This file SCAFFOLDS the open questions from the paper for free
    groups F_r and their representations into SL(n, F). It does not
    prove them — these are research-level open problems. The goal here
    is to (1) state each conjecture as a formal Coq Definition that the
    project can later refer to, (2) tie each statement to a specific
    theorem/conjecture number in the paper, and (3) record the
    infrastructure gaps that block any attempt at proof.

    See the bottom of the file for the [INFRASTRUCTURE GAPS] roadmap. *)

From CAG Require Import Group.
From CAG Require Import FreeGroup.
From CAG Require Import DecisionProblems.TraceProperties.
From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* ================================================================== *)
(** * 1. Concrete free group as an FGGroup                             *)
(* ================================================================== *)

(** The standard generators of [FreeGroup n] as letters with no
    inversion bit set. Word length on [RWord n] is the length of the
    underlying reduced word. *)

Definition free_gen_letter (n : nat) (i : Fin.t n) : Letter n := (i, false).

Definition free_gen_RWord (n : nat) (i : Fin.t n) : RWord n.
Proof.
  refine (exist _ [free_gen_letter n i] _).
  unfold reduced. simpl. reflexivity.
Defined.

(** Length of the underlying reduced word (the canonical free-group
    word length). *)
Definition rword_length {n : nat} (w : RWord n) : nat :=
  length (proj1_sig w).

(** A [RWord n] is a positive word iff every letter has [false]
    inversion bit. *)
Definition is_positive_RWord {n : nat} (w : RWord n) : Prop :=
  Forall (fun l : Letter n => snd l = false) (proj1_sig w).

(** Cyclically reduced: first and last letters are not inverses of each
    other. *)
Definition is_cyclically_reduced {n : nat} (w : RWord n) : Prop :=
  match proj1_sig w with
  | [] => True
  | a :: rest =>
      match List.last rest a with
      | b => letter_inv a <> b \/ rest = []
      end
  end.

(* ================================================================== *)
(** * 2. Concrete SL_n family placeholder                              *)
(* ================================================================== *)

(** The paper studies representations into SL(n, F) for F an
    algebraically closed field (mostly C). The project currently
    axiomatizes such families as [nat -> MatrixGroup F]. A concrete
    SL(n, F) construction would require a full development of
    invertible matrices with determinant 1; this is one of the major
    infrastructure gaps listed at the bottom of the file.

    For now we use the axiomatized [MatrixGroup F] families from
    [TraceProperties] and parametrize the open problems by them. *)

Section OpenProblemsForFreeGroup.

  Variable n_gens : nat.
  Variable F : Type.
  Variable MG_family_SLn : nat -> MatrixGroup F.

  (** The free group on [n_gens] generators as a StrictGroup. *)
  Let FG : StrictGroup (RWord n_gens) := FreeGroup n_gens.

(* ================================================================== *)
(** * 3. The open problems / conjectures                                *)
(* ================================================================== *)

(** ** 3.1 — Conjecture (paper Question 1.7)

    [F_r] has property (A) for some n ∈ ℕ. Equivalently: there exists
    a single representation ρ : F_r → SL(n, ℂ) whose trace separates
    all non-conjugate elements simultaneously.

    Status: OPEN for r ≥ 2. The case r = 1 is trivial. The case r ≥ 2
    is widely conjectured to be FALSE (see [conjecture_3_2_no_A]
    below). *)
  Definition open_question_1_7 : Prop :=
    property_A FG MG_family_SLn.

(** ** 3.2 — Conjecture (negation): F_r lacks property (A) for r ≥ 2.

    The paper (and folklore) suggests that no single bounded-dimension
    representation can separate all conjugacy classes by trace. A
    diagonalization-style argument is expected; no proof is known. *)
  Definition conjecture_3_2_no_A : Prop :=
    2 <= n_gens -> ~ property_A FG MG_family_SLn.

(** ** 3.3 — Theorem 1.6 (proved in paper, not yet here).

    Free groups have property (B): for each γ ∈ F_r, there exists a
    representation ρ_γ : F_r → SL(n_γ, ℂ) such that γ is trace-
    separated from every non-conjugate η.

    Proof in paper: Hall's theorem (free groups are subgroup
    separable) + induced representation + Frobenius trace formula.

    Status here: AXIOMATIZED via [theorem_1_6_free_groups] in
    [TraceProperties]. *)
  Definition theorem_1_6_statement : Prop :=
    property_B FG MG_family_SLn.

(** ** 3.4 — Open Question (paper Question 1.10): Is uniform (C)
    equivalent to uniform (D)?

    The paper proves uniform (C) ⇒ (A) under irreducibility hypotheses
    on [Hom(F_r, SL(n, ℂ))]. Whether uniform (C) and uniform (D) are
    actually distinct is open.

    Even WHETHER F_r has uniform (D) is open. *)
  Definition open_question_1_10 : Prop :=
    uniform_C FG MG_family_SLn <-> uniform_D FG MG_family_SLn.

(** ** 3.5 — Open Question: SL_n-trace equivalence in F_r for n ≥ 3.

    Two non-conjugate elements γ, η ∈ F_r are SL_n-trace equivalent if
    Tr(ρ(γ)) = Tr(ρ(η)) for EVERY ρ : F_r → SL(n, ℂ).

    For n = 2 NO such pair exists (Horowitz / Procesi: trace functions
    generate the coordinate ring of the SL_2 character variety, and
    distinct conjugacy classes give distinct points).

    For n ≥ 3 the existence of such a pair is OPEN. *)
  Definition open_SLn_trace_pair (n : nat) : Prop :=
    2 <= n ->
    exists gamma eta : RWord n_gens,
      ~ are_conjugate FG gamma eta /\
      SLn_trace_equivalent FG MG_family_SLn n gamma eta.

(** ** 3.6 — Conjecture 5.5 (positive-word reduction).

    SL_n-trace-equivalent non-conjugate pairs exist in F_r if and only
    if such a pair can be found among positive words. Both halves are
    open for n ≥ 3. *)
  Definition conjecture_5_5_positive_words (n : nat) : Prop :=
    (exists gamma eta : RWord n_gens,
        ~ are_conjugate FG gamma eta /\
        SLn_trace_equivalent FG MG_family_SLn n gamma eta)
    <->
    (exists gamma eta : RWord n_gens,
        is_positive_RWord gamma /\ is_positive_RWord eta /\
        ~ are_conjugate FG gamma eta /\
        SLn_trace_equivalent FG MG_family_SLn n gamma eta).

  (** *** Trivial direction of Conjecture 5.5: positive ⟹ general.
      The hard direction (general ⟹ positive) requires a "negative-letter
      elimination" reduction and remains OPEN for n ≥ 3. *)

  Lemma conjecture_5_5_positive_to_general : forall n : nat,
      (exists gamma eta : RWord n_gens,
          is_positive_RWord gamma /\ is_positive_RWord eta /\
          ~ are_conjugate FG gamma eta /\
          SLn_trace_equivalent FG MG_family_SLn n gamma eta) ->
      (exists gamma eta : RWord n_gens,
          ~ are_conjugate FG gamma eta /\
          SLn_trace_equivalent FG MG_family_SLn n gamma eta).
  Proof.
    intros n [gamma [eta [_ [_ [Hnc Hte]]]]].
    exists gamma, eta. split; assumption.
  Qed.

  (** *** Sufficient condition for failure of property (A).

      Property (A) says: there exists a single rep ρ : F_r → SL(n, ℂ)
      separating ALL conjugacy classes by trace. If we can exhibit a
      non-conjugate pair γ, η with EQUAL traces under EVERY rep at some
      fixed n, then in particular no single ρ at that n can separate
      them — but that's a different statement than property (A) failing
      at all n.

      However, if we have such a pair at n_0 AND we have such a pair at
      every n, then property (A) fails. The KEY OBSERVATION: at n=2,
      our parametric trace identities (sl2_swap_bk_bl_general, etc.)
      give such pairs for every SL(2) rep. So at n=2, property (A)
      fails (modulo F_2 non-conjugacy of, e.g., bbabaa/babbaa).

      To get property (A) failing at every n, we'd need similar pairs
      at SL(n) for n ≥ 3 — the OPEN open_SLn_trace_pair question. *)

  Lemma trace_pair_at_n_blocks_property_A_at_n :
    forall (n : nat),
      (exists gamma eta : RWord n_gens,
          ~ are_conjugate FG gamma eta /\
          @trace_equiv_in_MG (RWord n_gens) F FG (MG_family_SLn n) gamma eta) ->
      ~ (exists rho : Representation FG (MG_family_SLn n),
            forall gamma' eta' : RWord n_gens,
              ~ are_conjugate FG gamma' eta' ->
              trace_at rho gamma' <> trace_at rho eta').
  Proof.
    intros n [gamma [eta [Hnc Hte]]] [rho Hsep].
    apply (Hsep gamma eta Hnc).
    apply Hte.
  Qed.

  (** Property (A) fails iff there's NO single rep separating all
      conjugacy classes. The above gives one half of "fails": if a
      trace-pair exists at the dimension for which (A) was claimed,
      that specific dimension can't witness (A). But (A) lets us pick
      ANY dimension, so this only blocks the witness at THAT n. *)

  Lemma trace_pair_every_n_implies_no_property_A :
    (forall n : nat, exists gamma eta : RWord n_gens,
        ~ are_conjugate FG gamma eta /\
        @trace_equiv_in_MG (RWord n_gens) F FG (MG_family_SLn n) gamma eta) ->
    ~ property_A FG MG_family_SLn.
  Proof.
    intros Hpair [n [rho Hsep]].
    destruct (Hpair n) as [gamma [eta [Hnc Hte]]].
    apply (Hsep gamma eta Hnc).
    apply Hte.
  Qed.

(** ** 3.7 — Open quantitative question (paper Question 1.13).

    Is the conjugacy distinguishing function Conj_{F_r}(n) polynomially
    bounded?

    The paper proves polynomial upper bounds CONDITIONAL on properties
    (A) or (B); but unconditionally the bound is open (and would
    follow from Conjecture 1.7 + effective version of theorem 1.4). *)
  Definition open_question_1_13 (fgg : FGGroup (RWord n_gens)) : Prop :=
    exists d C : nat, forall k : nat, Conj_func fgg k <= C * Nat.pow k d.

End OpenProblemsForFreeGroup.

(* ================================================================== *)
(** * 4. The Magnus / Horowitz boundary                                  *)
(* ================================================================== *)

(** Horowitz's theorem (n = 2, character variety reasoning):
    On F_r, two non-conjugate elements always have a representation
    ρ : F_r → SL(2, ℂ) that trace-separates them.

    This is the [n = 2] case of property (B); it is THEOREM 1.6
    restricted to n = 2. The general statement is axiomatized in
    [TraceProperties] as [theorem_1_6_free_groups]. The paper points
    out that the n = 2 case admits a much more elementary proof using
    Fricke characters. *)

(** ** 4.1 — Horowitz boundary (formal stub).

    Tr(ρ(γ)) = Tr(ρ(η)) for ALL ρ : F_r → SL(2, ℂ) iff γ ~ η.

    This is the n = 2 case of [open_SLn_trace_pair] — it has a
    POSITIVE answer (no such non-conjugate pair exists). *)
Section HorowitzBoundary.
  Variable n_gens : nat.
  Variable F : Type.
  Variable MG_family_SLn : nat -> MatrixGroup F.

  Definition horowitz_n2 : Prop :=
    forall gamma eta : RWord n_gens,
      (forall rho : Representation (FreeGroup n_gens) (MG_family_SLn 2),
          trace_at rho gamma = trace_at rho eta) ->
      are_conjugate (FreeGroup n_gens) gamma eta \/
      are_conjugate (FreeGroup n_gens) gamma
                    (sinv (RWord n_gens) (FreeGroup n_gens) eta).

End HorowitzBoundary.

(* ================================================================== *)
(** * 5. INFRASTRUCTURE GAPS                                             *)
(* ================================================================== *)

(** The open problems above are stated formally, but ATTEMPTING any of
    them in Coq requires substantial new infrastructure that the
    project currently lacks. Below is an itemized roadmap of what
    would have to be built.

    [G1] CONCRETE SL(n, F).
        We have a [MatrixGroup F] record (axiomatized: carrier +
        StrictGroup + trace + dim). To attempt the open problems
        meaningfully we need:
        - A type [SquareMat F n] of n × n matrices over a ring/field F
          with concrete entries; matrix multiplication; identity.
        - A determinant [det : SquareMat F n -> F] with the standard
          Leibniz formula and properties [det(AB) = det(A) det(B)],
          [det(I) = 1].
        - A subset/subtype [SL n F := { M | det M = 1 }] with
          inherited group structure.
        - Trace [trace : SquareMat F n -> F] = sum of diagonal entries
          (we have this for n = 2, 3 already in [LinAlg/Trace.v]).
        - A [MatrixGroup] instance built FROM [SL n F].
        Difficulty: LARGE. The current [LinAlg/Concrete.v] only has
        bases for [F^1], [F^2], [F^3]. We would need general n × n
        matrices.

    [G2] WORD LENGTH AND BALL FOR FREE GROUPS.
        [TraceProperties.word_length] is currently a placeholder that
        always returns 0. For free groups the right definition is
        [rword_length] (defined above in this file): length of the
        unique reduced representative.
        - Need: [word_length_RWord_correct] establishing that
          [word_length] equals the minimum word length.
        - Need: [Conj_func] computed concretely for [F_r] (currently
          returns 0).
        Difficulty: MODERATE. Once minimum-length is set up using
        Nat.find or strong induction, free-group case is mechanical.

    [G3] CHARACTER VARIETY OF F_r.
        Hom(F_r, SL(n, F)) has the structure of an algebraic variety,
        and the GIT quotient by conjugation is the character variety.
        The paper uses irreducibility of Hom(F_r, SL(n, ℂ)).
        - Need: AlgebraicVariety, irreducible, dim, codim.
        - Need: Fricke characters (n = 2): functions tr_w : F_r → ℂ.
        - Need: Procesi's theorem (n ≥ 3): trace-relations generate
          the coordinate ring of SL_n character variety.
        Difficulty: VERY LARGE. This is research algebra-geometry.

    [G4] BAIRE / COUNTABILITY ON VARIETIES.
        Theorem 1.1 (uniform (C) ⇒ (A)) needs that an irreducible
        variety is not a countable union of proper closed subvarieties.
        - Need: Baire category in the Zariski topology, or the
          equivalent fact about irreducible varieties over uncountable
          fields.
        Difficulty: LARGE. Depends on [G3].

    [G5] SPECIALIZATION LEMMA (Bass / Lubotzky).
        For Proposition 1.3 ((D) ⇒ conjugacy separable):
        - Need: a finitely generated integral domain has a residue
          field that is a finite field, with non-trivial elements
          surviving.
        - Need: ring of integers of a number field, mod-p reductions.
        Difficulty: MODERATE-LARGE. We have [Rings/Ring.v] and
        [Domains/UFD.v] but no number-theoretic ring infrastructure.

    [G6] HALL'S THEOREM FOR FREE GROUPS.
        For Theorem 1.6: every γ ∈ F_r lies in a finitely generated
        free factor with explicit complement.
        - Need: subgroup separability of free groups.
        - Need: Schreier transversal / Stallings folding.
        Difficulty: LARGE. We have [FreeGroup.v] but no Stallings
        machinery.

    [G7] INDUCED REPRESENTATIONS / FROBENIUS TRACE.
        For Theorem 1.6 again: given ρ : H → SL(n, F) and H ≤ G of
        finite index, build Ind^G_H(ρ) : G → SL([G:H]·n, F) with the
        Frobenius trace formula.
        - Need: tensor products of representations.
        - Need: cosets enumerated and finite.
        Difficulty: MODERATE.

    [G8] FULLY RESIDUALLY FREE.
        For Theorem 1.8: the class of fully residually free groups,
        and a workable definition that supports the inductive proof.
        Difficulty: LARGE.

    Summary of dependency graph:
        [G1] is foundational. Everything else relies on it.
        [G2], [G5], [G6], [G7] are independent of each other.
        [G3] depends on [G1].
        [G4] depends on [G3].
        [G8] depends on [G6].

    Suggested first attack:
        - Build [G1] (concrete SL(n, F)). This unlocks all the rest.
        - Specialize the [F_r → SL(2, F)] case and try [horowitz_n2]
          as the first concrete open-problem-adjacent target — it's
          known true and provable by Fricke / character variety
          arguments, but for n = 2 it's the most tractable. *)
