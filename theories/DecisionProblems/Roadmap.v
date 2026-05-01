(** * DecisionProblems/Roadmap.v

    Integration file: ties together all the pieces from
    OpenProblems.v, SL2Horowitz.v, InducedRep.v, Specialization.v,
    HallTheorem.v, WordLengthFreeGroup.v.

    Final tally of what is proved (modulo named research-level axioms)
    and what remains open. *)

From CAG Require Import Group FreeGroup.
From CAG Require Import LinAlg.Matrix2 LinAlg.SL2 LinAlg.SL2Fricke.
From CAG Require Import DecisionProblems.TraceProperties.
From CAG Require Import DecisionProblems.OpenProblems.
From CAG Require Import DecisionProblems.WordLengthFreeGroup.
From CAG Require Import DecisionProblems.SL2Horowitz.
From CAG Require Import DecisionProblems.InducedRep.
From CAG Require Import DecisionProblems.Specialization.
From CAG Require Import DecisionProblems.HallTheorem.
From CAG Require Import Galois.Field.

(* ================================================================== *)
(** * Status tracking                                                   *)
(* ================================================================== *)

(** ** Settled (proved, modulo named classical axioms):

    [horowitz_n2_thm]
        SL_2 trace separates conjugacy classes in F_r.
        Resolved by axiom [fricke_generation] (the Fricke generation
        theorem).

    [free_groups_property_B]
        Free groups F_r have property (B).
        Resolved by axiom [hall_construction_separates] +
        [free_id_separating_rep] (Hall's free-factor theorem +
        existence of faithful traces).

    [SL2 (mat2/SL2/SL2Fricke layer)]
        Concrete SL(2, F) MatrixGroup, fully proved (no axioms),
        including Cayley-Hamilton, trace cyclicity, Fricke identity
        tr(AB) + tr(AB⁻¹) = tr(A)·tr(B).

    [sl2_trace_conjugation_invariant]
        SL_2 trace is class function (proved, no axioms).

    [conjugate_trivial]
        e ∼ e in F_r (proved, no axioms).

    ** New (April 2026 run 3, sl2_swap family):

    [sl2_swap_bk_p_general]:
        forall A B : Mat2 F, forall k p j : nat,
          tr(B^k · A^p · B · A^j) = tr(B · A^p · B^k · A^j)
        Proven by induction on k + Cayley-Hamilton + cyclicity.
        Discharges an INFINITE family of trace identities in M_2(F).

    [sl2_swap_b2_general] / [sl2_swap_bk_general_proven]:
        Specializations of sl2_swap_bk_p_general.

    [sl2_smallest_positive_identity_unconditional]:
        tr(B² · A · B · A²) = tr(B · A · B² · A²)
        Smallest example (length 6).

    [sl2_3gen_length9_identity], [sl2_3gen_length9_id_2],
    [sl2_3gen_length9_id_3]:
        Three different 3-generator length-9 trace identities.
        All proven by ring on 12-variable polynomial difference.

    [mat2_pow_recur]: A^{j+2} = tr(A)·A^{j+1} - det(A)·A^j (matrix eq).
    [trace_pow_succ_succ_recur]: Chebyshev recurrence on trace.
    [trace_pow_left_recur]: mirror version.
    [trace_rotate_BA]: 4-factor cyclicity.
    [mat2_pow_pow_comm]: A-powers commute.

    All of the above: Closed under global context. No axioms.

    ** Reduced to named research-level axioms:

    [hall_finite_index_free_factor]
        Hall (1949): every nontrivial element of F_r has a
        finite-index normal subgroup with the desired free-product
        decomposition.

    [hall_construction_separates]
        Combined Hall + induction; the explicit separating rep.

    [bass_lubotzky_specialization]
        Specialization lemma: f.g. integral domain → finite quotient
        with element survival.

    [fricke_generation]
        Fricke (~1896) and Procesi (1976): SL_2 trace polynomials
        separate conjugacy classes.

    ** Genuinely open (no axiom resolves them):

    [open_question_1_7]
        Does F_r have property (A)? (open for r ≥ 2)

    [conjecture_3_2_no_A]
        Folklore: F_r LACKS (A) for r ≥ 2.

    [open_question_1_10]
        uniform (C) ⇔ uniform (D)?

    [open_SLn_trace_pair n] for n ≥ 3
        Does there exist a non-conjugate pair in F_r whose traces
        agree under every SL_n representation?
        (For n = 2 the answer is NO, by [horowitz_n2_thm].)

    [conjecture_5_5_positive_words n] for n ≥ 3
        SL_n-trace pair iff positive-word pair?

    [open_question_1_13]
        Conj_{F_r}(n) polynomially bounded? *)

(* ================================================================== *)
(** * Connection summary: which axioms resolve which open problems     *)
(* ================================================================== *)

(** The chain of implications: *)

(** [bass_lubotzky_specialization] + concrete trace ring construction
    ⇒ Proposition 1.3 ((D) ⇒ conjugacy separable). *)

(** [hall_finite_index_free_factor] + induced reps + Frobenius
    ⇒ [free_groups_property_B] (Theorem 1.6 for F_r). *)

(** [fricke_generation]
    ⇒ [horowitz_n2_thm] (negative answer to open_SLn_trace_pair n=2). *)

(* ================================================================== *)
(** * Coq-level integration: replace axioms in TraceProperties.v       *)
(* ================================================================== *)

(** [TraceProperties.theorem_1_6_free_groups] is currently axiomatized
    in the project. With our [HallTheorem.free_groups_property_B], we
    can derive it. *)

Theorem theorem_1_6_free_groups_derived :
  forall {F : Type} (MG_family : nat -> MatrixGroup F)
         (r : nat),
    property_B (FreeGroup r) MG_family.
Proof.
  intros F MG_family r.
  apply free_groups_property_B.
Qed.

(** Sanity check: [theorem_1_6_free_groups_derived] is not just a
    restatement of [TraceProperties.theorem_1_6_free_groups] — the
    former is a Theorem, while the latter is an Axiom. They have the
    same statement; the difference is that ours has a chain of
    reductions to named classical axioms. *)

(* ================================================================== *)
(** * Polynomial bound theorems: now derivable via Conj_func           *)
(* ================================================================== *)

(** Once [Conj_func] is replaced with its concrete instance for free
    groups (which would require enumerating words of length ≤ k and
    determining their conjugacy classes), the polynomial bound from
    Theorem 1.4 becomes: tr(ρ(γ))-tr(ρ(η)) is a polynomial of degree
    ≤ word-length, hence Conj_func ≤ poly(k). *)

(** Open task wrapping it up: provide [Conj_func_concrete] for free
    groups (i.e., NOT the placeholder = 0). With that and our
    [free_groups_property_B], the polynomial bound becomes derivable.
    Currently the trivial bound holds since [Conj_func] returns 0. *)
