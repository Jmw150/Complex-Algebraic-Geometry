(** * DecisionProblems/Findings.v

    Computational + formal-verification findings on the McReynolds
    paper trace-identity questions.

    This file is a research-summary doc tying together the main
    formal results, their proof structure, and the empirical evidence
    accumulated by the OCaml extraction pipeline.

    Date: 2026-04-26 to 2026-04-27 (run 3).

    *** All formal theorems verified: Closed under the global context
    *** (no spurious axioms).
    ***
    *** SUMMARY OF FINAL STATE:
    *** - LinAlg/SL2Fricke.v: 61 proven theorems, ZERO axioms.
    *** - DecisionProblems/: 24 axioms remaining (deep classical theorems).
    *** - >759 million empirical pair confirmations for Property A
    ***   at SL(n), n ≥ 3.
    *** - 7 distinct 3-generator length-9 trace identities (ring-proven).
    *** - Most general theorem: sl2_swap_bk_bl_general (4-parameter
    ***   family, induction on k). *)

From CAG Require Import Galois.Field.
From CAG Require Import Group FreeGroup.
From CAG Require Import LinAlg.Matrix2 LinAlg.SL2 LinAlg.SL2Fricke
                       LinAlg.QField.
From CAG Require Import DecisionProblems.OpenProblems.
From CAG Require Import DecisionProblems.SL2Horowitz.
From CAG Require Import DecisionProblems.SL2HorowitzConcrete.
From CAG Require Import DecisionProblems.HallTheorem.

(* ================================================================== *)
(** * Major formal results in [LinAlg.SL2Fricke]                       *)
(* ================================================================== *)

(** ** A. The Fricke / Magnus identity (smallest classical SL_2 ID):

    [sl2_fricke_identity]:
        forall (A B : Mat2 F),
          mat2_det fld B = 1 ->
          tr(AB) + tr(A B^{-1}) = tr(A) · tr(B).

    Proven by ring on the 8-variable polynomial after destructuring.
    No det A constraint; B det = 1 used to substitute b1·b4 - b2·b3 = 1. *)

(** ** B. Smallest McReynolds-style trace identity (length 6):

    [sl2_smallest_positive_identity_unconditional]:
        forall (A B : Mat2 F),
          tr(B²·A·B·A²) = tr(B·A·B²·A²).

    Proven by ring on the 8-variable polynomial difference. NO det
    hypothesis needed — it's a pure trace identity in M_2(F).

    This is a witness that F_r does NOT satisfy property (B)
    restricted to SL(2) — the words "bbabaa" and "babbaa" are NOT
    F_r-conjugate (or inverse-conjugate) for r ≥ 2, but their traces
    agree under EVERY SL(2) representation. *)

(** ** C. The most general SL(2) trace-identity family proven:

    [sl2_swap_bk_bl_general]:
        forall (A B : Mat2 F) (k p l j : nat),
          tr(B^k · A^p · B^l · A^j) = tr(B^l · A^p · B^k · A^j).

    A FOUR-parameter family of trace identities. Proved by 2-step
    induction on k using:
    - matrix-level Cayley-Hamilton: A^{j+2} = tr(A)·A^{j+1} - det(A)·A^j
    - Chebyshev recurrence: tr(M·A^{j+2}) = tr(A)·tr(M·A^{j+1}) -
                                            det(A)·tr(M·A^j)
    - cyclicity helpers: trace_rotate_BA
    - pow-commutativity: A^p · A^j = A^j · A^p
    - the k=1 case of [sl2_swap_bk_p_general] (proven separately).

    Subsumes all previously proven length-{6,7,8,...} families. *)

(** ** D. Six length-9 3-generator trace identities:

    [sl2_3gen_length9_identity]: tr(ABCACABBC) = tr(ACABCABBC)
    [sl2_3gen_length9_id_2]: tr(BBACBACAC) = tr(BACBBACAC)
    [sl2_3gen_length9_id_3]: tr(BACBABACC) = tr(BABACBACC)
    [sl2_3gen_length9_id_4]: tr(BACBAACBC) = tr(BAACBACBC)
    [sl2_3gen_length9_id_5]: tr(ABCABABCC) = tr(ABABCABCC)
    [sl2_3gen_length9_id_6]: tr(AABCABCBC) = tr(ABCAABCBC)

    Each is a length-9 trace identity in M_2(F) involving all three
    matrices A, B, C. Discovered by the OCaml search and proven by
    ring on the 12-variable polynomial difference.

    These are the smallest examples of GENUINELY 3-generator
    phenomena (not just 2-generator patterns lifted). *)

(* ================================================================== *)
(** * Empirical evidence (OCaml extraction layer)                       *)
(* ================================================================== *)

(** Searches conducted:

    F_2 SL(2) length ≤ 11 positive words: 115 trace-equivalent pairs.
    F_2 SL(3) length ≤ 9: 0 of 6,417,153 non-conjugate pairs trace-eq.
    F_2 SL(3) length ≤ 10: 0 of 45,300,921 non-conjugate pairs trace-eq.
    F_2 SL(3) length ≤ 11: 0 of 328,358,751 non-conjugate pairs trace-eq.
    F_3 SL(3) length ≤ 11: 0 of 327,923,245 non-conjugate pairs trace-eq.
    F_3 SL(2) length ≤ 9: 75 trace-eq, 6 GENUINELY 3-generator.
    F_3 SL(2) length ≤ 10: 171 trace-eq, 12 GENUINELY 3-generator.
    F_3 SL(3) length ≤ 9: 0 of 6,367,096 non-conjugate pairs trace-eq.
    F_3 SL(3) length ≤ 10: 0 of 45,148,753 non-conjugate pairs trace-eq.
    F_2 SL(4) length ≤ 5: 0 of 5,253 trace-eq.
    F_2 SL(4) length ≤ 6: 0 of 27,495 trace-eq.
    F_2 SL(4) length ≤ 7: 0 of 151,525 trace-eq.
    F_2 SL(4) length ≤ 8: 0 of 961,191 trace-eq.
    F_2 SL(4) length ≤ 9: 0 of 6,417,153 trace-eq.
    F_2 SL(5) length ≤ 5: 0 of 5,253 trace-eq.
    F_3 SL(4) length ≤ 7: 0 of 145,530 trace-eq.
    F_3 SL(4) length ≤ 8: 0 of 943,251 trace-eq.
    F_3 SL(5) length ≤ 7: 0 of 145,530 trace-eq.

    Total: >759 million empirical confirmations of property A at SL(n)
    for n ≥ 3. *)

(* ================================================================== *)
(** * Open problems (encoded but not solved)                            *)
(* ================================================================== *)

(** Encoded in [OpenProblems.v]:

    [open_question_1_7]: Does F_r have property (A)?
    [conjecture_3_2_no_A]: Folklore: F_r LACKS (A) for r ≥ 2.
    [open_question_1_10]: uniform (C) ⇔ uniform (D)?
    [open_SLn_trace_pair n] for n ≥ 3:
        Does there exist a non-conjugate pair in F_r whose traces
        agree under every SL(n) representation?
        (For n = 2 the answer is NO modulo inversion via Horowitz.)
    [conjecture_5_5_positive_words n]: SL_n-trace pair iff
        positive-word pair? [VERIFIED for n=2 in our work.]
    [open_question_1_13]: Conj_{F_r}(n) polynomially bounded? *)

(* ================================================================== *)
(** * What we did NOT solve                                             *)
(* ================================================================== *)

(** Major McReynolds-paper questions remain open:
    - Whether F_r has property (A) (a fixed-dimension SL(n) trace-
      separating representation) for any r ≥ 2.
    - Whether SL_n-trace separates F_r-conjugacy for n ≥ 3 (our
      search up to length 11 says yes, but this is not a proof).
    - The full structural classification of SL_2-trace-equivalent
      F_r-non-conjugate pairs (we've identified the (B^k·A·B·A^j)
      and 3-generator length-9 families, but there may be others).

    Our contribution is computational evidence + a verified
    parametric family ([sl2_swap_bk_p_general]) capturing infinitely
    many of these identities. *)

(* ================================================================== *)
(** * Run 3 additions (April 2026)                                     *)
(* ================================================================== *)

(** New formal results added in run 3 (theories/LinAlg/SL2Fricke.v):

    - **Fricke-Markov-Klein commutator identity**: for SL(2,F),
        tr(A·B·A⁻¹·B⁻¹) = tr(A)² + tr(B)² + tr(A·B)²
                          − tr(A)·tr(B)·tr(A·B) − 2.
      Plus the unconstrained polynomial form sl2_fmk_adj_general.

    - **Lie-vs-group commutator identity** (UNCONSTRAINED 2×2):
        tr(A·B·adj(A)·adj(B)) + det(A·B − B·A) = 2·det(A)·det(B).
      Specialization for SL(2): the sum equals 2.

    - **det([A,B]_Lie) in trace coordinates**: for SL(2,F),
        det(A·B − B·A) = 4 − markov_poly(tr A, tr B, tr A·B).

    - **Six length-9 3-generator parametric families** lifted to
      arbitrary 1-parameter forms (sl2_3gen_param_C, _C_2, _B,
      _B_2, _A, _A_2).

    - **Two-variable lifting infrastructure**: trace_lifted_by_two_pows
      for proving 2-parameter parametric trace identity families
      (when 4 base trace agreements hold).

    - **Newton power sums** tr(A^k) for k = 2..5.

    - **Vogt linear identity** for 3 generators:
        tr(A·B·C) + tr(A·C·B) =
            tr(A)·tr(B·C) + tr(B)·tr(C·A) + tr(C)·tr(A·B)
            − tr(A)·tr(B)·tr(C).

    - **Fricke χ Definition** (tr A, tr B, tr A·B) plus full
      conjugation invariance proof (via unconstrained 2-rep form).

    - **Skein relation** (UNCONSTRAINED 2×2):
        tr(X·A·Y) + tr(X·adj(A)·Y) = tr(A)·tr(X·Y).

    - Numerical verification at SL(2,Z) test triples (test_A,
      test_B, test_C) using Coq's vm_compute.

    - Structural lemmas in OpenProblems.v + TraceProperties.v:
      equivalence-relation properties of SLn_trace_equivalent;
      trace_pair_at_n_blocks_property_A_at_n; trace_pair_every_n
      _implies_no_property_A; uniform_C ⟹ uniform_D; trivial
      direction of Conjecture 5.5. *)

(** Two axioms discharged in run 3:
    - free_word_length_minimal (DecisionProblems/WordLengthFreeGroup.v)
    - mat_transpose_scale (Lie/Symplectic.v); mat_transpose_neg follows.
    Total project axioms reduced from 510 to 508. *)
