(** * LinAlg/SL2Fricke.v
    Fricke trace identities for SL(2, F).

    These are the fundamental polynomial identities relating traces of
    products of SL(2, F) matrices. They are the foundation of the SL_2
    character variety theory (Fricke, Vogt, Magnus).

    Core identities:
    - Cayley-Hamilton for SL(2,F): A² = tr(A)·A - I.
    - Trace duality: tr(A) = tr(A⁻¹) for A ∈ SL(2, F).
    - Magnus identity: tr(AB) + tr(AB⁻¹) = tr(A)·tr(B).
    - Trace cyclicity: tr(AB) = tr(BA).

    These identities completely determine the SL_2 trace function on
    free groups via "Fricke characters": every word trace tr(ρ(w)) is
    a polynomial in the basic traces tr(ρ(g_i)), tr(ρ(g_i g_j)),
    tr(ρ(g_i g_j g_k)).

    Addresses [G3] from DecisionProblems/OpenProblems.v. *)

Require Import CAG.Galois.Field.
Require Import CAG.LinAlg.Matrix2.
Require Import CAG.LinAlg.SL2.
From Stdlib Require Import Ring Setoid Lia.
From Stdlib Require Import Logic.ProofIrrelevance.

Section SL2Fricke.
  Context {F : Type} (fld : Field F).

  Local Lemma fricke_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring fricke_ring : fricke_ring_theory.

  (* ============================================================ *)
  (** ** 1. Cayley-Hamilton for SL(2,F)                            *)
  (* ============================================================ *)

  (** For A ∈ SL(2, F), A² = tr(A)·A - I.

      Proof: A² - tr(A)·A + det(A)·I = 0 (Cayley-Hamilton);
      det(A) = 1 in SL(2). *)

  Lemma sl2_cayley_hamilton :
      forall (A : Mat2 F),
        mat2_det fld A = cr_one fld ->
        mat2_mul fld A A =
        mat2_add fld
          (mat2_scale fld (mat2_trace fld A) A)
          (mat2_neg fld (mat2_id fld)).
  Proof.
    intros [[[a b] c] d] HA.
    unfold mat2_det, mat2_mk in HA.
    (* HA: a*d - b*c = 1, so b*c = a*d - 1 *)
    assert (Hbc_eq : cr_mul fld b c = cr_sub fld (cr_mul fld a d) (cr_one fld))
      by (unfold cr_sub in *; rewrite <- HA; ring).
    unfold mat2_mul, mat2_trace, mat2_scale, mat2_add, mat2_neg,
           mat2_id, mat2_mk.
    (* Goal is (M_aa, M_ab, M_ac, M_ad) = (R_aa, R_ab, R_ac, R_ad) *)
    f_equal; [f_equal; [f_equal|]|]; unfold cr_sub.
    - (* a*a + b*c = (a+d)*a + -1 *)
      rewrite Hbc_eq. unfold cr_sub. ring.
    - (* a*b + b*d = (a+d)*b + 0 *)
      ring.
    - (* c*a + d*c = (a+d)*c + 0 *)
      ring.
    - (* c*b + d*d = (a+d)*d + -1 *)
      assert (Hbc' : cr_mul fld c b =
                    cr_sub fld (cr_mul fld a d) (cr_one fld)).
      { rewrite <- Hbc_eq. ring. }
      rewrite Hbc'. unfold cr_sub. ring.
  Qed.

  (* ============================================================ *)
  (** ** 2. Trace duality                                          *)
  (* ============================================================ *)

  (** For A ∈ SL(2, F), tr(A⁻¹) = tr(A). *)

  Lemma sl2_trace_inv_eq_trace :
      forall A : Mat2 F,
        mat2_det fld A = cr_one fld ->
        mat2_trace fld (mat2_adj fld A) = mat2_trace fld A.
  Proof.
    intros [[[a b] c] d] _.
    unfold mat2_trace, mat2_adj, mat2_mk. ring.
  Qed.

  (* ============================================================ *)
  (** ** 3. Fricke / Magnus identity                                *)
  (* ============================================================ *)

  (** The fundamental Fricke identity:
      tr(AB) + tr(AB⁻¹) = tr(A) · tr(B), for A, B ∈ SL(2, F).

      Equivalently: tr(AB⁻¹) = tr(A)·tr(B) - tr(AB).

      Proof: using B + B⁻¹ = tr(B)·I (Cayley-Hamilton), so
      A·(B + B⁻¹) = tr(B)·A, hence tr(AB) + tr(AB⁻¹) = tr(B)·tr(A). *)

  Lemma sl2_fricke_identity :
      forall A B : Mat2 F,
        mat2_det fld B = cr_one fld ->
        cr_add fld
          (mat2_trace fld (mat2_mul fld A B))
          (mat2_trace fld (mat2_mul fld A (mat2_adj fld B))) =
        cr_mul fld (mat2_trace fld A) (mat2_trace fld B).
  Proof.
    intros [[[a1 b1] c1] d1] [[[a2 b2] c2] d2] HB.
    unfold mat2_trace, mat2_mul, mat2_adj, mat2_mk in *.
    unfold mat2_det, mat2_mk in HB.
    (* tr(AB) = a1*a2 + b1*c2 + c1*b2 + d1*d2... wait, no:
       tr is sum of (1,1) and (2,2), so
       tr(AB) = a1*a2 + b1*c2 + c1*b2 + d1*d2.
       tr(A·adj(B)) where adj(B) = [d2, -b2; -c2, a2]
       = a1*d2 + b1*(-c2) + c1*(-b2) + d1*a2.
       Sum = a1*a2 + a1*d2 + d1*a2 + d1*d2 = (a1+d1)*(a2+d2). *)
    ring.
  Qed.

  (** Equivalent form: tr(AB⁻¹) = tr(A)·tr(B) - tr(AB). *)
  Lemma sl2_fricke_inv_form :
      forall A B : Mat2 F,
        mat2_det fld B = cr_one fld ->
        mat2_trace fld (mat2_mul fld A (mat2_adj fld B)) =
        cr_sub fld
          (cr_mul fld (mat2_trace fld A) (mat2_trace fld B))
          (mat2_trace fld (mat2_mul fld A B)).
  Proof.
    intros A B HB.
    pose proof (sl2_fricke_identity A B HB) as HF.
    unfold cr_sub. rewrite <- HF. ring.
  Qed.

  (** *** Fricke-Markov-Klein adjugate identity (unconstrained polynomial form).

      For ANY 2×2 matrices A, B (no determinant constraint):
        tr(A·B·adj(A)·adj(B)) =
          det(A)·tr(B)² + det(B)·tr(A)² + tr(A·B)²
          − tr(A)·tr(B)·tr(A·B) − 2·det(A)·det(B)

      This is the generalized Fricke-Markov-Klein identity expressing
      the trace of the "commutator-like" word A·B·adj(A)·adj(B) purely
      in terms of the elementary symmetric functions of A, B, A·B and
      their determinants. Pure polynomial identity, provable by ring. *)

  Lemma sl2_fmk_adj_general :
      forall A B : Mat2 F,
        mat2_trace fld
          (mat2_mul fld A
             (mat2_mul fld B
                (mat2_mul fld (mat2_adj fld A) (mat2_adj fld B)))) =
        cr_sub fld
          (cr_add fld
             (cr_add fld
                (cr_mul fld (mat2_det fld A)
                            (cr_mul fld (mat2_trace fld B) (mat2_trace fld B)))
                (cr_mul fld (mat2_det fld B)
                            (cr_mul fld (mat2_trace fld A) (mat2_trace fld A))))
             (cr_sub fld
                (cr_mul fld (mat2_trace fld (mat2_mul fld A B))
                            (mat2_trace fld (mat2_mul fld A B)))
                (cr_mul fld
                   (cr_mul fld (mat2_trace fld A) (mat2_trace fld B))
                   (mat2_trace fld (mat2_mul fld A B)))))
          (cr_add fld
             (cr_mul fld (mat2_det fld A) (mat2_det fld B))
             (cr_mul fld (mat2_det fld A) (mat2_det fld B))).
  Proof.
    intros [[[a1 b1] c1] d1] [[[a2 b2] c2] d2].
    unfold mat2_trace, mat2_mul, mat2_adj, mat2_det, mat2_mk, cr_sub.
    ring.
  Qed.

  (** *** Fricke-Markov-Klein commutator identity for SL(2).

      For A, B in SL(2, F) (i.e., det(A) = det(B) = 1):
        tr([A,B]) = tr(A)² + tr(B)² + tr(A·B)² − tr(A)·tr(B)·tr(A·B) − 2

      where [A,B] = A·B·A⁻¹·B⁻¹ and A⁻¹ = adj(A) when det(A) = 1.

      This is the classical generating identity for the Fricke–Klein
      character variety of SL(2,C). Derived as a corollary of the
      unconstrained polynomial form sl2_fmk_adj_general. *)

  Lemma sl2_fmk_commutator :
      forall A B : Mat2 F,
        mat2_det fld A = cr_one fld ->
        mat2_det fld B = cr_one fld ->
        mat2_trace fld
          (mat2_mul fld A
             (mat2_mul fld B
                (mat2_mul fld (mat2_adj fld A) (mat2_adj fld B)))) =
        cr_sub fld
          (cr_add fld
             (cr_add fld
                (cr_mul fld (mat2_trace fld A) (mat2_trace fld A))
                (cr_mul fld (mat2_trace fld B) (mat2_trace fld B)))
             (cr_sub fld
                (cr_mul fld (mat2_trace fld (mat2_mul fld A B))
                            (mat2_trace fld (mat2_mul fld A B)))
                (cr_mul fld
                   (cr_mul fld (mat2_trace fld A) (mat2_trace fld B))
                   (mat2_trace fld (mat2_mul fld A B)))))
          (cr_add fld (cr_one fld) (cr_one fld)).
  Proof.
    intros A B HA HB.
    rewrite (sl2_fmk_adj_general A B).
    rewrite HA, HB.
    unfold cr_sub. ring.
  Qed.

  (** *** Trace of [A²·B] in SL(2)-form.

      For any 2×2 matrices A, B,
        tr(A²·B) = tr(A)·tr(A·B) − det(A)·tr(B).

      In SL(2) (det A = 1) this becomes
        tr(A²·B) = tr(A)·tr(A·B) − tr(B). *)

  Lemma sl2_trace_a2b :
      forall (A B : Mat2 F),
        mat2_trace fld (mat2_mul fld (mat2_mul fld A A) B) =
        cr_sub fld
          (cr_mul fld (mat2_trace fld A)
                      (mat2_trace fld (mat2_mul fld A B)))
          (cr_mul fld (mat2_det fld A) (mat2_trace fld B)).
  Proof.
    intros A B.
    destruct A as [[[a1 a2] a3] a4].
    destruct B as [[[b1 b2] b3] b4].
    unfold mat2_mul, mat2_trace, mat2_det, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** *** Trace of [A·B²], analog by symmetry. *)

  Lemma sl2_trace_ab2 :
      forall (A B : Mat2 F),
        mat2_trace fld (mat2_mul fld A (mat2_mul fld B B)) =
        cr_sub fld
          (cr_mul fld (mat2_trace fld B)
                      (mat2_trace fld (mat2_mul fld A B)))
          (cr_mul fld (mat2_det fld B) (mat2_trace fld A)).
  Proof.
    intros A B.
    destruct A as [[[a1 a2] a3] a4].
    destruct B as [[[b1 b2] b3] b4].
    unfold mat2_mul, mat2_trace, mat2_det, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** *** Trace of [A·B·A] (= tr(A²·B) by cyclicity). *)

  Lemma sl2_trace_aba :
      forall (A B : Mat2 F),
        mat2_trace fld (mat2_mul fld A (mat2_mul fld B A)) =
        cr_sub fld
          (cr_mul fld (mat2_trace fld A)
                      (mat2_trace fld (mat2_mul fld A B)))
          (cr_mul fld (mat2_det fld A) (mat2_trace fld B)).
  Proof.
    intros A B.
    destruct A as [[[a1 a2] a3] a4].
    destruct B as [[[b1 b2] b3] b4].
    unfold mat2_mul, mat2_trace, mat2_det, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** *** Trace of [A·B·A·B] = tr((A·B)²).

      Length-4 trace polynomial: tr(A·B·A·B) = tr(A·B)² − 2·det(A·B).
      In SL(2), tr(A·B·A·B) = tr(A·B)² − 2. *)

  Lemma sl2_trace_abab :
      forall (A B : Mat2 F),
        mat2_trace fld (mat2_mul fld A (mat2_mul fld B (mat2_mul fld A B))) =
        cr_sub fld
          (cr_mul fld (mat2_trace fld (mat2_mul fld A B))
                      (mat2_trace fld (mat2_mul fld A B)))
          (cr_add fld
             (cr_mul fld (mat2_det fld A) (mat2_det fld B))
             (cr_mul fld (mat2_det fld A) (mat2_det fld B))).
  Proof.
    intros A B.
    destruct A as [[[a1 a2] a3] a4].
    destruct B as [[[b1 b2] b3] b4].
    unfold mat2_mul, mat2_trace, mat2_det, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** *** Trace of [A³·B].

      For any 2×2 matrices A, B,
        tr(A³·B) = (tr(A)² − det(A))·tr(A·B) − det(A)·tr(A)·tr(B).

      In SL(2) (det A = 1):
        tr(A³·B) = (tr(A)² − 1)·tr(A·B) − tr(A)·tr(B). *)

  Lemma sl2_trace_a3b :
      forall (A B : Mat2 F),
        mat2_trace fld
          (mat2_mul fld (mat2_mul fld A (mat2_mul fld A A)) B) =
        cr_sub fld
          (cr_mul fld
             (cr_sub fld
                (cr_mul fld (mat2_trace fld A) (mat2_trace fld A))
                (mat2_det fld A))
             (mat2_trace fld (mat2_mul fld A B)))
          (cr_mul fld (mat2_det fld A)
                      (cr_mul fld (mat2_trace fld A) (mat2_trace fld B))).
  Proof.
    intros A B.
    destruct A as [[[a1 a2] a3] a4].
    destruct B as [[[b1 b2] b3] b4].
    unfold mat2_mul, mat2_trace, mat2_det, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** *** Trace of [A²·B·C].

      For any 2×2 matrices A, B, C:
        tr(A²·B·C) = tr(A)·tr(A·B·C) − det(A)·tr(B·C).

      In SL(2): tr(A²·B·C) = tr(A)·tr(A·B·C) − tr(B·C).
      Proof: Cayley-Hamilton on A reduces A²·B·C to a linear combination
      of A·B·C and B·C, and trace is linear. *)

  Lemma sl2_trace_a2bc :
      forall (A B C : Mat2 F),
        mat2_trace fld
          (mat2_mul fld (mat2_mul fld A A) (mat2_mul fld B C)) =
        cr_sub fld
          (cr_mul fld (mat2_trace fld A)
             (mat2_trace fld (mat2_mul fld A (mat2_mul fld B C))))
          (cr_mul fld (mat2_det fld A)
             (mat2_trace fld (mat2_mul fld B C))).
  Proof.
    intros A B C.
    destruct A as [[[a1 a2] a3] a4].
    destruct B as [[[b1 b2] b3] b4].
    destruct C as [[[c1 c2] c3] c4].
    unfold mat2_mul, mat2_trace, mat2_det, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** *** Trace of [A·B²·C], symmetric to sl2_trace_a2bc.

      For any 2×2 matrices A, B, C:
        tr(A·B²·C) = tr(B)·tr(A·B·C) − det(B)·tr(A·C). *)

  Lemma sl2_trace_ab2c :
      forall (A B C : Mat2 F),
        mat2_trace fld
          (mat2_mul fld A
             (mat2_mul fld (mat2_mul fld B B) C)) =
        cr_sub fld
          (cr_mul fld (mat2_trace fld B)
             (mat2_trace fld (mat2_mul fld A (mat2_mul fld B C))))
          (cr_mul fld (mat2_det fld B)
             (mat2_trace fld (mat2_mul fld A C))).
  Proof.
    intros A B C.
    destruct A as [[[a1 a2] a3] a4].
    destruct B as [[[b1 b2] b3] b4].
    destruct C as [[[c1 c2] c3] c4].
    unfold mat2_mul, mat2_trace, mat2_det, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** *** Trace of [A·B·C²], symmetric to sl2_trace_a2bc.

      For any 2×2 matrices A, B, C:
        tr(A·B·C²) = tr(C)·tr(A·B·C) − det(C)·tr(A·B). *)

  Lemma sl2_trace_abc2 :
      forall (A B C : Mat2 F),
        mat2_trace fld
          (mat2_mul fld A
             (mat2_mul fld B (mat2_mul fld C C))) =
        cr_sub fld
          (cr_mul fld (mat2_trace fld C)
             (mat2_trace fld (mat2_mul fld A (mat2_mul fld B C))))
          (cr_mul fld (mat2_det fld C)
             (mat2_trace fld (mat2_mul fld A B))).
  Proof.
    intros A B C.
    destruct A as [[[a1 a2] a3] a4].
    destruct B as [[[b1 b2] b3] b4].
    destruct C as [[[c1 c2] c3] c4].
    unfold mat2_mul, mat2_trace, mat2_det, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** *** Trace difference [A,B] · C identity.

      For any 2×2 matrices A, B, C:
        tr(A·B·C) − tr(A·C·B) = tr((A·B − B·A)·C)
                              = tr(A·B·C) − tr(B·A·C)
                              = tr(A·B·C) − tr(A·C·B)  (by cyclicity of tr(BAC) = tr(ACB))

      So in fact tr(ABC) − tr(ACB) is a trivial restatement of trace
      cyclicity tr(BAC) = tr(ACB). The interesting content is that
      this difference equals tr([A,B]·C) where [A,B] = AB − BA is the
      MATRIX (Lie) commutator, NOT the group commutator. *)

  Lemma sl2_trace_abc_minus_acb :
      forall (A B C : Mat2 F),
        cr_sub fld
          (mat2_trace fld (mat2_mul fld A (mat2_mul fld B C)))
          (mat2_trace fld (mat2_mul fld A (mat2_mul fld C B))) =
        cr_sub fld
          (mat2_trace fld (mat2_mul fld (mat2_mul fld A B) C))
          (mat2_trace fld (mat2_mul fld (mat2_mul fld B A) C)).
  Proof.
    intros A B C.
    destruct A as [[[a1 a2] a3] a4].
    destruct B as [[[b1 b2] b3] b4].
    destruct C as [[[c1 c2] c3] c4].
    unfold mat2_mul, mat2_trace, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** *** Vogt's 3-generator linear trace identity.

      For ANY 2×2 matrices A, B, C (no det constraint):
        tr(A·B·C) + tr(A·C·B) =
          tr(A)·tr(B·C) + tr(B)·tr(C·A) + tr(C)·tr(A·B)
          − tr(A)·tr(B)·tr(C).

      This is the LINEAR coordinate of the SL(2)-character variety of
      F_3. It expresses tr(ABC) + tr(ACB) symmetrically in the seven
      classical Fricke coordinates {tr(A), tr(B), tr(C), tr(AB), tr(BC),
      tr(CA)}. Combined with the Vogt-Fricke quadratic relation, this
      determines tr(ABC) and tr(ACB) up to the standard ambiguity. *)

  Lemma sl2_vogt_linear :
      forall (A B C : Mat2 F),
        cr_add fld
          (mat2_trace fld (mat2_mul fld A (mat2_mul fld B C)))
          (mat2_trace fld (mat2_mul fld A (mat2_mul fld C B))) =
        cr_sub fld
          (cr_add fld
             (cr_add fld
                (cr_mul fld (mat2_trace fld A)
                            (mat2_trace fld (mat2_mul fld B C)))
                (cr_mul fld (mat2_trace fld B)
                            (mat2_trace fld (mat2_mul fld C A))))
             (cr_mul fld (mat2_trace fld C)
                         (mat2_trace fld (mat2_mul fld A B))))
          (cr_mul fld (mat2_trace fld A)
                      (cr_mul fld (mat2_trace fld B) (mat2_trace fld C))).
  Proof.
    intros A B C.
    destruct A as [[[a1 a2] a3] a4].
    destruct B as [[[b1 b2] b3] b4].
    destruct C as [[[c1 c2] c3] c4].
    unfold mat2_mul, mat2_trace, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** *** Skein relation (generalized Fricke).

      For ANY 2×2 matrices X, A, Y (no determinant constraint):
        tr(X·A·Y) + tr(X·adj(A)·Y) = tr(A)·tr(X·Y).

      Proof: A + adj(A) = tr(A)·I (a 2×2 algebraic identity), so
      X·(A + adj(A))·Y = tr(A)·X·Y and trace gives the result. This
      generalizes [sl2_fricke_identity] (which is the X = I case). *)

  Lemma sl2_skein_general :
      forall (X A Y : Mat2 F),
        cr_add fld
          (mat2_trace fld (mat2_mul fld X (mat2_mul fld A Y)))
          (mat2_trace fld (mat2_mul fld X (mat2_mul fld (mat2_adj fld A) Y))) =
        cr_mul fld (mat2_trace fld A) (mat2_trace fld (mat2_mul fld X Y)).
  Proof.
    intros [[[x1 x2] x3] x4] [[[a1 a2] a3] a4] [[[y1 y2] y3] y4].
    unfold mat2_mul, mat2_trace, mat2_adj, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** *** Sum identity: tr(A²·B²) + tr(A·B·adj(A)·adj(B)) = tr(A·B)².

      Surprising 2×2 polynomial identity: the sum of two length-4 trace
      expressions reduces to the SQUARE of the length-2 trace tr(A·B).
      Proof: ring on the 8-variable polynomial difference. *)

  Lemma sl2_trace_sum_identity :
      forall (A B : Mat2 F),
        cr_add fld
          (mat2_trace fld
             (mat2_mul fld (mat2_mul fld A A) (mat2_mul fld B B)))
          (mat2_trace fld
             (mat2_mul fld A
                (mat2_mul fld B
                   (mat2_mul fld (mat2_adj fld A) (mat2_adj fld B))))) =
        cr_mul fld
          (mat2_trace fld (mat2_mul fld A B))
          (mat2_trace fld (mat2_mul fld A B)).
  Proof.
    intros A B.
    destruct A as [[[a1 a2] a3] a4].
    destruct B as [[[b1 b2] b3] b4].
    unfold mat2_mul, mat2_trace, mat2_adj, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** *** Trace of [A·B³], analog of sl2_trace_a3b. *)

  Lemma sl2_trace_ab3 :
      forall (A B : Mat2 F),
        mat2_trace fld
          (mat2_mul fld A (mat2_mul fld B (mat2_mul fld B B))) =
        cr_sub fld
          (cr_mul fld
             (cr_sub fld
                (cr_mul fld (mat2_trace fld B) (mat2_trace fld B))
                (mat2_det fld B))
             (mat2_trace fld (mat2_mul fld A B)))
          (cr_mul fld (mat2_det fld B)
                      (cr_mul fld (mat2_trace fld B) (mat2_trace fld A))).
  Proof.
    intros A B.
    destruct A as [[[a1 a2] a3] a4].
    destruct B as [[[b1 b2] b3] b4].
    unfold mat2_mul, mat2_trace, mat2_det, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** *** Trace of [A²·B²].

      tr(A²·B²) = tr(A)·tr(B)·tr(A·B) − det(B)·tr(A)² − det(A)·tr(B)²
                  + 2·det(A)·det(B).

      In SL(2): tr(A²·B²) = tr(A)·tr(B)·tr(A·B) − tr(A)² − tr(B)² + 2. *)

  Lemma sl2_trace_a2b2 :
      forall (A B : Mat2 F),
        mat2_trace fld
          (mat2_mul fld (mat2_mul fld A A) (mat2_mul fld B B)) =
        cr_add fld
          (cr_sub fld
             (cr_sub fld
                (cr_mul fld
                   (cr_mul fld (mat2_trace fld A) (mat2_trace fld B))
                   (mat2_trace fld (mat2_mul fld A B)))
                (cr_mul fld (mat2_det fld B)
                            (cr_mul fld (mat2_trace fld A)
                                        (mat2_trace fld A))))
             (cr_mul fld (mat2_det fld A)
                         (cr_mul fld (mat2_trace fld B)
                                     (mat2_trace fld B))))
          (cr_add fld
             (cr_mul fld (mat2_det fld A) (mat2_det fld B))
             (cr_mul fld (mat2_det fld A) (mat2_det fld B))).
  Proof.
    intros A B.
    destruct A as [[[a1 a2] a3] a4].
    destruct B as [[[b1 b2] b3] b4].
    unfold mat2_mul, mat2_trace, mat2_det, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** *** Length-5 trace identity: tr(A·B²·A·B).

      For any 2×2 matrices A, B,
        tr(A·B²·A·B) = tr(B)·tr(A·B)² − det(A)·det(B)·tr(B)
                       − det(B)·tr(A)·tr(A·B).

      In SL(2): tr(A·B²·A·B) = tr(B)·tr(A·B)² − tr(B) − tr(A)·tr(A·B). *)

  Lemma sl2_trace_ab2ab :
      forall (A B : Mat2 F),
        mat2_trace fld
          (mat2_mul fld A
             (mat2_mul fld B (mat2_mul fld B (mat2_mul fld A B)))) =
        cr_sub fld
          (cr_sub fld
             (cr_mul fld (mat2_trace fld B)
                         (cr_mul fld (mat2_trace fld (mat2_mul fld A B))
                                     (mat2_trace fld (mat2_mul fld A B))))
             (cr_mul fld
                (cr_mul fld (mat2_det fld A) (mat2_det fld B))
                (mat2_trace fld B)))
          (cr_mul fld (mat2_det fld B)
             (cr_mul fld (mat2_trace fld A)
                         (mat2_trace fld (mat2_mul fld A B)))).
  Proof.
    intros A B.
    destruct A as [[[a1 a2] a3] a4].
    destruct B as [[[b1 b2] b3] b4].
    unfold mat2_mul, mat2_trace, mat2_det, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** *** Markov surface equation (rearranged FMK).

      For A, B in SL(2, F), set
          x = tr(A),  y = tr(B),  z = tr(A·B).
      Then
          x² + y² + z² − x·y·z = 2 + tr([A,B]).

      The "Markov surface" {(x,y,z) : x² + y² + z² = xyz} is the locus
      of pairs (A,B) where the commutator [A,B] is parabolic of trace 2
      (the unipotent class). For trace [A,B] = -2 we recover the
      Markov-Fricke "Cayley cubic" {x² + y² + z² + xyz = 4}.

      This is just sl2_fmk_commutator with the −2 moved to the LHS. *)

  Lemma sl2_markov_surface :
      forall A B : Mat2 F,
        mat2_det fld A = cr_one fld ->
        mat2_det fld B = cr_one fld ->
        cr_sub fld
          (cr_add fld
             (cr_add fld
                (cr_mul fld (mat2_trace fld A) (mat2_trace fld A))
                (cr_mul fld (mat2_trace fld B) (mat2_trace fld B)))
             (cr_mul fld (mat2_trace fld (mat2_mul fld A B))
                         (mat2_trace fld (mat2_mul fld A B))))
          (cr_mul fld
             (cr_mul fld (mat2_trace fld A) (mat2_trace fld B))
             (mat2_trace fld (mat2_mul fld A B))) =
        cr_add fld
          (cr_add fld (cr_one fld) (cr_one fld))
          (mat2_trace fld
             (mat2_mul fld A
                (mat2_mul fld B
                   (mat2_mul fld (mat2_adj fld A) (mat2_adj fld B))))).
  Proof.
    intros A B HA HB.
    rewrite (sl2_fmk_commutator A B HA HB).
    unfold cr_sub. ring.
  Qed.

  (** *** Markov polynomial.

      Define M(x, y, z) = x² + y² + z² − x·y·z. Then for A, B in SL(2,F):
        tr([A, B]) = M(tr A, tr B, tr A·B) − 2.
      The Markov surface M = 0 is the locus of pairs with parabolic
      commutator (tr = -2 ↔ M = 0); the Cayley cubic M = 4 is the
      identity-commutator locus. *)

  Definition markov_poly (x y z : F) : F :=
    cr_sub fld
      (cr_add fld
         (cr_add fld (cr_mul fld x x) (cr_mul fld y y))
         (cr_mul fld z z))
      (cr_mul fld x (cr_mul fld y z)).

  Lemma sl2_markov_poly_eq_commutator_plus_2 :
      forall A B : Mat2 F,
        mat2_det fld A = cr_one fld ->
        mat2_det fld B = cr_one fld ->
        markov_poly (mat2_trace fld A) (mat2_trace fld B)
                    (mat2_trace fld (mat2_mul fld A B)) =
        cr_add fld
          (cr_add fld (cr_one fld) (cr_one fld))
          (mat2_trace fld
             (mat2_mul fld A
                (mat2_mul fld B
                   (mat2_mul fld (mat2_adj fld A) (mat2_adj fld B))))).
  Proof.
    intros A B HA HB.
    pose proof (sl2_markov_surface A B HA HB) as Hms.
    unfold markov_poly. unfold cr_sub in *. rewrite <- Hms. ring.
  Qed.

  (* ============================================================ *)
  (** ** 4. Trace cyclicity                                          *)
  (* ============================================================ *)

  (** tr(AB) = tr(BA), independently of det. *)
  Lemma sl2_trace_cyclic_full : forall A B : Mat2 F,
      mat2_trace fld (mat2_mul fld A B) =
      mat2_trace fld (mat2_mul fld B A).
  Proof. intros A B. apply mat2_trace_cyclic. Qed.

  (* ============================================================ *)
  (** ** 5. Trace of a power                                         *)
  (* ============================================================ *)

  (** Iterated multiplication. *)
  Fixpoint mat2_pow (A : Mat2 F) (n : nat) : Mat2 F :=
    match n with
    | 0 => mat2_id fld
    | S k => mat2_mul fld A (mat2_pow A k)
    end.

  Lemma mat2_pow_0 : forall A : Mat2 F,
      mat2_pow A 0 = mat2_id fld.
  Proof. reflexivity. Qed.

  Lemma mat2_pow_1 : forall A : Mat2 F,
      mat2_pow A 1 = A.
  Proof.
    intro A. simpl. apply mat2_mul_id_r.
  Qed.

  (** Trace of A² for any A: tr(A²) = tr(A)² - 2·det(A).
      For A ∈ SL(2): tr(A²) = tr(A)² - 2. *)
  Lemma sl2_trace_squared_general :
      forall A : Mat2 F,
        mat2_trace fld (mat2_mul fld A A) =
        cr_sub fld
          (cr_mul fld (mat2_trace fld A) (mat2_trace fld A))
          (cr_add fld (mat2_det fld A) (mat2_det fld A)).
  Proof.
    intros [[[a b] c] d].
    unfold mat2_trace, mat2_mul, mat2_det, mat2_mk. ring.
  Qed.

  Lemma sl2_trace_squared :
      forall A : Mat2 F,
        mat2_det fld A = cr_one fld ->
        mat2_trace fld (mat2_mul fld A A) =
        cr_sub fld
          (cr_mul fld (mat2_trace fld A) (mat2_trace fld A))
          (cr_add fld (cr_one fld) (cr_one fld)).
  Proof.
    intros A HA. rewrite sl2_trace_squared_general, HA. reflexivity.
  Qed.

  (** *** Trace of A^3.

      For any 2×2 matrix A:
        tr(A³) = tr(A)³ − 3·det(A)·tr(A).

      In SL(2): tr(A³) = tr(A)³ − 3·tr(A). *)

  Lemma sl2_trace_cubed_general :
      forall A : Mat2 F,
        mat2_trace fld (mat2_mul fld A (mat2_mul fld A A)) =
        cr_sub fld
          (cr_mul fld (mat2_trace fld A)
             (cr_mul fld (mat2_trace fld A) (mat2_trace fld A)))
          (cr_mul fld
             (cr_add fld (cr_add fld (mat2_det fld A) (mat2_det fld A))
                          (mat2_det fld A))
             (mat2_trace fld A)).
  Proof.
    intros [[[a b] c] d].
    unfold mat2_trace, mat2_mul, mat2_det, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** *** Trace of A^5.

      For any 2×2 matrix A:
        tr(A⁵) = tr(A)⁵ − 5·det(A)·tr(A)³ + 5·det(A)²·tr(A).

      In SL(2): tr(A⁵) = tr(A)⁵ − 5·tr(A)³ + 5·tr(A). *)

  Lemma sl2_trace_fifth_general :
      forall A : Mat2 F,
        mat2_trace fld
          (mat2_mul fld A
             (mat2_mul fld A
                (mat2_mul fld A (mat2_mul fld A A)))) =
        cr_add fld
          (cr_sub fld
             (cr_mul fld
                (cr_mul fld (mat2_trace fld A) (mat2_trace fld A))
                (cr_mul fld (mat2_trace fld A)
                   (cr_mul fld (mat2_trace fld A) (mat2_trace fld A))))
             (cr_mul fld
                (cr_add fld (cr_add fld (cr_add fld (cr_add fld
                   (mat2_det fld A) (mat2_det fld A))
                   (mat2_det fld A)) (mat2_det fld A)) (mat2_det fld A))
                (cr_mul fld (mat2_trace fld A)
                   (cr_mul fld (mat2_trace fld A) (mat2_trace fld A)))))
          (cr_mul fld
             (cr_add fld (cr_add fld (cr_add fld (cr_add fld
                (cr_mul fld (mat2_det fld A) (mat2_det fld A))
                (cr_mul fld (mat2_det fld A) (mat2_det fld A)))
                (cr_mul fld (mat2_det fld A) (mat2_det fld A)))
                (cr_mul fld (mat2_det fld A) (mat2_det fld A)))
                (cr_mul fld (mat2_det fld A) (mat2_det fld A)))
             (mat2_trace fld A)).
  Proof.
    intros [[[a b] c] d].
    unfold mat2_trace, mat2_mul, mat2_det, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** *** Trace of A^4.

      For any 2×2 matrix A:
        tr(A^4) = tr(A)^4 − 4·det(A)·tr(A)² + 2·det(A)².

      In SL(2): tr(A^4) = tr(A)^4 − 4·tr(A)² + 2. *)

  Lemma sl2_trace_fourth_general :
      forall A : Mat2 F,
        mat2_trace fld (mat2_mul fld A (mat2_mul fld A (mat2_mul fld A A))) =
        cr_add fld
          (cr_sub fld
             (cr_mul fld (cr_mul fld (mat2_trace fld A) (mat2_trace fld A))
                         (cr_mul fld (mat2_trace fld A) (mat2_trace fld A)))
             (cr_mul fld
                (cr_add fld
                   (cr_add fld
                      (cr_add fld (mat2_det fld A) (mat2_det fld A))
                      (mat2_det fld A))
                   (mat2_det fld A))
                (cr_mul fld (mat2_trace fld A) (mat2_trace fld A))))
          (cr_add fld (cr_mul fld (mat2_det fld A) (mat2_det fld A))
                       (cr_mul fld (mat2_det fld A) (mat2_det fld A))).
  Proof.
    intros [[[a b] c] d].
    unfold mat2_trace, mat2_mul, mat2_det, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (* ============================================================ *)
  (** ** 6. Chebyshev recursion for trace of a power                *)
  (* ============================================================ *)

  (** For A ∈ SL(2): tr(A^{n+2}) = tr(A)·tr(A^{n+1}) - tr(A^n).

      This is the Chebyshev recursion: tr(A^n) = U_{n-1}(tr(A)/2)
      (rescaled). Standard fact, follows from Cayley-Hamilton.

      Stated as the recursive identity that drives the polynomial
      structure. *)
  Lemma sl2_trace_pow_chebyshev :
      forall (A : Mat2 F) (n : nat),
        mat2_det fld A = cr_one fld ->
        mat2_trace fld (mat2_pow A (S (S n))) =
        cr_sub fld
          (cr_mul fld
             (mat2_trace fld A)
             (mat2_trace fld (mat2_pow A (S n))))
          (mat2_trace fld (mat2_pow A n)).
  Proof.
    intros A n HA.
    (* mat2_pow A (S (S n)) = A * (A * mat2_pow A n)
       = (A * A) * mat2_pow A n  (by associativity)
       = (tr(A)*A - I) * mat2_pow A n  (by Cayley-Hamilton)
       = tr(A) * (A * mat2_pow A n) - mat2_pow A n
       = tr(A) * mat2_pow A (S n) - mat2_pow A n.
       Take trace. *)
    simpl mat2_pow.
    rewrite mat2_mul_assoc.
    rewrite (sl2_cayley_hamilton A HA).
    (* Now: tr( (tr(A)·A + (-I)) * (mat2_pow A n) ) =
       tr(A)·tr(A · mat2_pow A n) - tr(mat2_pow A n).
       Use linearity of trace via destructuring. *)
    destruct A as [[[a b] c] d].
    destruct (mat2_pow (a, b, c, d) n) as [[[p1 p2] p3] p4] eqn:Epn.
    unfold mat2_mul, mat2_add, mat2_scale, mat2_neg, mat2_id,
           mat2_trace, mat2_mk. cbn. ring.
  Qed.

  (** SL2_pow agrees with mat2_pow on the underlying matrix. *)
  Lemma SL2_mat_pow : forall (g : SL2_carrier fld) (k : nat),
      SL2_mat fld (SL2_pow fld g k) = mat2_pow (SL2_mat fld g) k.
  Proof.
    intros g k. induction k as [|k IH].
    - reflexivity.
    - simpl. unfold SL2_mul. simpl. rewrite IH. reflexivity.
  Qed.

  (** Chebyshev recursion for SL2_pow trace:
      tr(g^{n+2}) = tr(g) · tr(g^{n+1}) - tr(g^n). *)
  Lemma SL2_trace_pow_chebyshev :
      forall (g : SL2_carrier fld) (n : nat),
        SL2_trace fld (SL2_pow fld g (S (S n))) =
        cr_sub fld
          (cr_mul fld
             (SL2_trace fld g)
             (SL2_trace fld (SL2_pow fld g (S n))))
          (SL2_trace fld (SL2_pow fld g n)).
  Proof.
    intros g n. unfold SL2_trace.
    rewrite !SL2_mat_pow.
    apply sl2_trace_pow_chebyshev.
    apply (SL2_det fld).
  Qed.

  (** SL2_pow at 1 equals the element. *)
  Lemma SL2_pow_one : forall g : SL2_carrier fld,
      SL2_pow fld g 1 = g.
  Proof.
    intros g. simpl. apply SL2_id_right.
  Qed.

  (** Trace of SL2_pow at 1 equals the trace. *)
  Lemma SL2_trace_pow_one : forall g : SL2_carrier fld,
      SL2_trace fld (SL2_pow fld g 1) = SL2_trace fld g.
  Proof.
    intros g. rewrite SL2_pow_one. reflexivity.
  Qed.

  (** Trace of SL2_pow at 0 is 2 (= 1 + 1). *)
  Lemma SL2_trace_pow_zero : forall g : SL2_carrier fld,
      SL2_trace fld (SL2_pow fld g 0) =
      cr_add fld (cr_one fld) (cr_one fld).
  Proof.
    intros g. simpl. apply SL2_trace_id.
  Qed.

  (** Trace of any power of SL2_id is 2. *)
  Lemma SL2_trace_pow_id : forall (k : nat),
      SL2_trace fld (SL2_pow fld (SL2_id fld) k) =
      cr_add fld (cr_one fld) (cr_one fld).
  Proof.
    intros k. rewrite SL2_pow_id. apply SL2_trace_id.
  Qed.

  (** If two SL2 elements have equal trace, their powers do too.
      Proof: 2-step strong induction using Chebyshev recursion. *)
  Lemma SL2_trace_pow_determined_by_trace :
    forall (a b : SL2_carrier fld),
      SL2_trace fld a = SL2_trace fld b ->
      forall k, SL2_trace fld (SL2_pow fld a k) =
                SL2_trace fld (SL2_pow fld b k).
  Proof.
    intros a b Htr k.
    (* Two-step strong induction: prove P(k) and P(k+1) together. *)
    assert (H : forall j, SL2_trace fld (SL2_pow fld a j) =
                          SL2_trace fld (SL2_pow fld b j) /\
                          SL2_trace fld (SL2_pow fld a (S j)) =
                          SL2_trace fld (SL2_pow fld b (S j))).
    { intros j. induction j as [|j IH].
      - split.
        + change (SL2_pow fld a 0) with (SL2_id fld).
          change (SL2_pow fld b 0) with (SL2_id fld).
          reflexivity.
        + rewrite (SL2_pow_one a). rewrite (SL2_pow_one b). exact Htr.
      - destruct IH as [IH1 IH2]. split.
        + exact IH2.
        + rewrite (SL2_trace_pow_chebyshev a j).
          rewrite (SL2_trace_pow_chebyshev b j).
          f_equal.
          * f_equal.
            -- exact Htr.
            -- exact IH2.
          * exact IH1. }
    apply (proj1 (H k)).
  Qed.

  (** Trace of a power of inverse equals trace of the power.
      Direct corollary: SL2_trace_inv + SL2_trace_pow_determined_by_trace. *)
  Lemma SL2_trace_pow_inv :
    forall (g : SL2_carrier fld) (k : nat),
      SL2_trace fld (SL2_pow fld (SL2_inv fld g) k) =
      SL2_trace fld (SL2_pow fld g k).
  Proof.
    intros g k.
    apply SL2_trace_pow_determined_by_trace.
    apply SL2_trace_inv.
  Qed.

  (** Iff form: equal traces iff all powers have equal traces. *)
  Lemma SL2_trace_pow_iff :
    forall (a b : SL2_carrier fld),
      SL2_trace fld a = SL2_trace fld b <->
      forall k, SL2_trace fld (SL2_pow fld a k) =
                SL2_trace fld (SL2_pow fld b k).
  Proof.
    intros a b. split.
    - apply SL2_trace_pow_determined_by_trace.
    - intro Hpow. specialize (Hpow 1).
      rewrite !SL2_trace_pow_one in Hpow. exact Hpow.
  Qed.

  (** tr(g^2) = tr(g)^2 - 2.
      Direct application of Chebyshev with n = 0. *)
  Lemma SL2_trace_pow_two :
    forall (g : SL2_carrier fld),
      SL2_trace fld (SL2_pow fld g 2) =
      cr_sub fld (cr_mul fld (SL2_trace fld g) (SL2_trace fld g))
                  (cr_add fld (cr_one fld) (cr_one fld)).
  Proof.
    intros g. rewrite (SL2_trace_pow_chebyshev g 0).
    rewrite SL2_trace_pow_zero.
    rewrite SL2_trace_pow_one. reflexivity.
  Qed.

  (** tr(g^3) = tr(g)^3 - 3·tr(g).
      Application of Chebyshev with n = 1, expanded via SL2_trace_pow_two. *)
  Lemma SL2_trace_pow_three :
    forall (g : SL2_carrier fld),
      SL2_trace fld (SL2_pow fld g 3) =
      cr_sub fld
        (cr_mul fld (cr_mul fld (SL2_trace fld g) (SL2_trace fld g))
                    (SL2_trace fld g))
        (cr_mul fld (cr_add fld (cr_one fld)
                              (cr_add fld (cr_one fld) (cr_one fld)))
                    (SL2_trace fld g)).
  Proof.
    intros g. rewrite (SL2_trace_pow_chebyshev g 1).
    rewrite SL2_trace_pow_two.
    rewrite SL2_trace_pow_one. ring.
  Qed.

  (** tr(g^4) = tr(g)^4 - 4·tr(g)^2 + 2.
      Chebyshev with n = 2. *)
  Lemma SL2_trace_pow_four :
    forall (g : SL2_carrier fld),
      SL2_trace fld (SL2_pow fld g 4) =
      cr_add fld
        (cr_sub fld
          (cr_mul fld (cr_mul fld (SL2_trace fld g) (SL2_trace fld g))
                      (cr_mul fld (SL2_trace fld g) (SL2_trace fld g)))
          (cr_mul fld
            (cr_add fld (cr_add fld (cr_one fld) (cr_one fld))
                        (cr_add fld (cr_one fld) (cr_one fld)))
            (cr_mul fld (SL2_trace fld g) (SL2_trace fld g))))
        (cr_add fld (cr_one fld) (cr_one fld)).
  Proof.
    intros g.
    rewrite (SL2_trace_pow_chebyshev g 2).
    rewrite SL2_trace_pow_three.
    rewrite SL2_trace_pow_two.
    ring.
  Qed.

  (** tr(g^5) computed via Chebyshev (using tr^3 and tr^4 rewrites). *)
  Lemma SL2_trace_pow_five :
    forall (g : SL2_carrier fld),
      SL2_trace fld (SL2_pow fld g 5) =
      cr_sub fld
        (cr_mul fld (SL2_trace fld g)
                    (SL2_trace fld (SL2_pow fld g 4)))
        (SL2_trace fld (SL2_pow fld g 3)).
  Proof.
    intros g. apply (SL2_trace_pow_chebyshev g 3).
  Qed.


  (** Parabolic case: if tr(g) = 2 then tr(g^k) = 2 for all k. *)
  Lemma SL2_trace_pow_parabolic :
    forall (g : SL2_carrier fld),
      SL2_trace fld g = cr_add fld (cr_one fld) (cr_one fld) ->
      forall k, SL2_trace fld (SL2_pow fld g k) =
                cr_add fld (cr_one fld) (cr_one fld).
  Proof.
    intros g Hg k.
    (* Two-step strong induction: prove P(k) and P(k+1) together. *)
    assert (H : forall j, SL2_trace fld (SL2_pow fld g j) =
                          cr_add fld (cr_one fld) (cr_one fld) /\
                          SL2_trace fld (SL2_pow fld g (S j)) =
                          cr_add fld (cr_one fld) (cr_one fld)).
    { intros j. induction j as [|j IH].
      - split.
        + apply SL2_trace_pow_zero.
        + rewrite SL2_trace_pow_one. exact Hg.
      - destruct IH as [IH1 IH2]. split.
        + exact IH2.
        + rewrite (SL2_trace_pow_chebyshev g j).
          rewrite Hg, IH1, IH2. ring. }
    apply (proj1 (H k)).
  Qed.

  (* ============================================================ *)
  (** ** 7. Trace polynomial for words: notion                      *)
  (* ============================================================ *)

  (** The Fricke / Magnus theorem (SL_2): for any word w in r
      generators g_1, ..., g_r, the trace tr(ρ(w)) (under any
      representation ρ : F_r → SL(2, F)) is a polynomial in the
      basic traces:
        tr(ρ(g_i)) for 1 ≤ i ≤ r,
        tr(ρ(g_i g_j)) for 1 ≤ i < j ≤ r,
        tr(ρ(g_i g_j g_k)) for 1 ≤ i < j < k ≤ r.

      This follows by induction on word length using Fricke's
      identity sl2_fricke_inv_form to reduce tr of any product to
      the basic generators.

      We don't formalize the polynomial structure here (that is
      [G3'] in the roadmap); we record the key reduction step. *)

  (** Trace reduction step: tr(A · g · B · g⁻¹) reduces to a
      polynomial in trace of subwords. (Stated as a placeholder
      structural lemma.) *)
  (** A "sandwich" form of the Fricke identity, via cyclicity:
      tr(A·g·B) + tr(A·adj(g)·B) = tr(g) · tr(A·B).

      This is a direct corollary of [sl2_fricke_identity] +
      [mat2_trace_cyclic], but the rewrite chain on nested
      multiplications is fragile to argument order. We axiomatize for
      now; ungating this is mechanical given access to the right
      setoid_rewrite + cyclicity normalization. *)
  Theorem sl2_trace_reduction_step :
      forall A B g : Mat2 F,
        mat2_det fld g = cr_one fld ->
        cr_add fld
          (mat2_trace fld (mat2_mul fld (mat2_mul fld A g) B))
          (mat2_trace fld
             (mat2_mul fld (mat2_mul fld A (mat2_adj fld g)) B)) =
        cr_mul fld
          (mat2_trace fld g)
          (mat2_trace fld (mat2_mul fld A B)).
  Proof.
    intros A B g Hg.
    (* tr(AgB) = tr(BAg) by cyclicity. *)
    rewrite (mat2_trace_cyclic _ (mat2_mul fld A g) B).
    rewrite (mat2_mul_assoc fld B A g).
    rewrite (mat2_trace_cyclic _ (mat2_mul fld A (mat2_adj fld g)) B).
    rewrite (mat2_mul_assoc fld B A (mat2_adj fld g)).
    rewrite (sl2_fricke_identity (mat2_mul fld B A) g Hg).
    rewrite (mat2_trace_cyclic _ B A).
    apply (cr_mul_comm fld).
  Qed.

  (* ============================================================ *)
  (** ** 8. Smallest positive-word trace identity in F_2            *)
  (* ============================================================ *)

  (** Computational discovery (length 6): for A, B ∈ SL(2, F),
      tr(B²ABA²) = tr(BAB²A²).

      Both sides represent positive F_2 words [bbabaa] and [babbaa]
      that are non-conjugate in F_2 yet trace-equivalent under all
      SL(2) representations.

      Proof: by Cayley-Hamilton (B² = tr(B)·B - I) plus trace cyclicity.

      tr(B²ABA²) = tr((tr(B)B - I)·ABA²)
                 = tr(B)·tr(B·ABA²) - tr(ABA²)
                 = tr(B)·tr(BABA²) - tr(ABA²)

      tr(BAB²A²) = tr(BA·(tr(B)B - I)·A²)
                 = tr(B)·tr(BABA²) - tr(BA·A²)
                 = tr(B)·tr(BABA²) - tr(BA³)

      Since tr(ABA²) = tr(BA²·A) = tr(BA³) by cyclicity, equal.

      This is the smallest example of the McReynolds property-(B)-fails-
      for-SL_2 phenomenon for F_2: a length-6 positive-word pair that
      cannot be separated by any SL(2) representation. *)

  (** A polynomial-level lemma: for any 2×2 matrices A, B (any det),
      writing tr(γ) - tr(η) directly as a polynomial in entries shows
      the difference equals (det B - 1) · P + (det A - 1) · Q for some
      polynomials P, Q. Hence equal when det A = det B = 1.

      Rather than proving via Cayley-Hamilton lifting (which would need
      add-distributivity of mat2_mul that we haven't proven), we
      compute the polynomial difference as a linear combination of
      (det B - 1) and use that. *)
  Lemma sl2_smallest_positive_identity_diff_general :
      forall a1 a2 a3 a4 b1 b2 b3 b4 : F,
        let A := mat2_mk a1 a2 a3 a4 in
        let B := mat2_mk b1 b2 b3 b4 in
        cr_sub fld
          (mat2_trace fld (mat2_mul fld (mat2_mul fld B B)
                          (mat2_mul fld A (mat2_mul fld B
                            (mat2_mul fld A A)))))
          (mat2_trace fld (mat2_mul fld B
                          (mat2_mul fld A (mat2_mul fld B
                            (mat2_mul fld B (mat2_mul fld A A)))))) =
        cr_zero fld.
  Proof.
    intros a1 a2 a3 a4 b1 b2 b3 b4 A B. subst A B.
    unfold mat2_mul, mat2_trace, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** The smallest positive-word trace identity in F_2 (length 6).
      Even more striking: no det = 1 hypothesis is needed!

      tr(B²ABA²) = tr(BAB²A²) for ANY 2×2 matrices A, B.

      This means the identity is a TRACE IDENTITY in M_2(F), not just
      in SL_2(F). It's a consequence of trace cyclicity alone:
      tr(B²ABA²) = tr(BABA²B) = ...= tr(BAB²A²)? Let's see if it
      reduces to a cyclic permutation.

      Actually we already showed:
      tr(B²ABA²) - tr(BAB²A²) = (substituting cancellations) ... = 0.

      The proof works without the det=1 hypothesis because the
      polynomial difference identically vanishes — it's a pure trace
      identity coming from cyclicity reordering. *)
  Theorem sl2_smallest_positive_identity_unconditional :
      forall A B : Mat2 F,
        mat2_trace fld (mat2_mul fld (mat2_mul fld B B)
                        (mat2_mul fld A (mat2_mul fld B
                          (mat2_mul fld A A)))) =
        mat2_trace fld (mat2_mul fld B
                        (mat2_mul fld A (mat2_mul fld B
                          (mat2_mul fld B (mat2_mul fld A A))))).
  Proof.
    intros [[[a1 a2] a3] a4] [[[b1 b2] b3] b4].
    pose proof (sl2_smallest_positive_identity_diff_general
                  a1 a2 a3 a4 b1 b2 b3 b4) as Hd.
    unfold cr_sub in Hd.
    apply (f_equal (fun x => cr_add fld x (mat2_trace fld
            (mat2_mul fld (mat2_mk b1 b2 b3 b4) (mat2_mul fld
              (mat2_mk a1 a2 a3 a4) (mat2_mul fld (mat2_mk b1 b2 b3 b4)
                (mat2_mul fld (mat2_mk b1 b2 b3 b4) (mat2_mul fld
                  (mat2_mk a1 a2 a3 a4) (mat2_mk a1 a2 a3 a4))))))))) in Hd.
    rewrite <- (cr_add_assoc fld) in Hd.
    rewrite (cr_add_comm fld _ (mat2_trace fld _)) in Hd.
    rewrite (cr_add_neg fld) in Hd.
    rewrite (cr_add_zero fld) in Hd.
    rewrite (cr_add_comm fld) in Hd.
    rewrite (cr_add_zero fld) in Hd.
    exact Hd.
  Qed.

  (** For SL(2): same thing, det=1 hypothesis present but unused. *)
  Corollary sl2_smallest_positive_identity :
      forall A B : Mat2 F,
        mat2_det fld A = cr_one fld ->
        mat2_det fld B = cr_one fld ->
        mat2_trace fld (mat2_mul fld (mat2_mul fld B B)
                        (mat2_mul fld A (mat2_mul fld B
                          (mat2_mul fld A A)))) =
        mat2_trace fld (mat2_mul fld B
                        (mat2_mul fld A (mat2_mul fld B
                          (mat2_mul fld B (mat2_mul fld A A))))).
  Proof.
    intros A B _ _. apply sl2_smallest_positive_identity_unconditional.
  Qed.

  (** Helper: x - y = 0 implies x = y (in any commutative ring). *)
  Lemma cr_sub_eq_zero_implies_eq : forall x y : F,
      cr_sub fld x y = cr_zero fld -> x = y.
  Proof.
    intros x y H. unfold cr_sub in H.
    apply (f_equal (fun z => cr_add fld z y)) in H.
    rewrite (cr_add_comm fld (cr_zero fld) y) in H.
    rewrite (cr_add_zero fld) in H.
    rewrite <- (cr_add_assoc fld) in H.
    rewrite (cr_add_comm fld (cr_neg fld y) y) in H.
    rewrite (cr_add_neg fld) in H.
    rewrite (cr_add_zero fld) in H.
    exact H.
  Qed.

  (** Length 7 case: tr(B²ABA³) = tr(BAB²A³). *)
  Theorem sl2_length7_identity :
      forall A B : Mat2 F,
        mat2_trace fld (mat2_mul fld (mat2_mul fld B B)
                       (mat2_mul fld A (mat2_mul fld B
                         (mat2_mul fld A (mat2_mul fld A A))))) =
        mat2_trace fld (mat2_mul fld B
                       (mat2_mul fld A (mat2_mul fld B
                         (mat2_mul fld B (mat2_mul fld A
                           (mat2_mul fld A A)))))).
  Proof.
    intros [[[a1 a2] a3] a4] [[[b1 b2] b3] b4].
    apply cr_sub_eq_zero_implies_eq.
    unfold mat2_mul, mat2_trace, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** Length 8 case: tr(B²ABA⁴) = tr(BAB²A⁴). *)
  Theorem sl2_length8_identity :
      forall A B : Mat2 F,
        mat2_trace fld (mat2_mul fld (mat2_mul fld B B)
                       (mat2_mul fld A (mat2_mul fld B
                         (mat2_mul fld A (mat2_mul fld A
                           (mat2_mul fld A A)))))) =
        mat2_trace fld (mat2_mul fld B
                       (mat2_mul fld A (mat2_mul fld B
                         (mat2_mul fld B (mat2_mul fld A
                           (mat2_mul fld A (mat2_mul fld A A))))))).
  Proof.
    intros [[[a1 a2] a3] a4] [[[b1 b2] b3] b4].
    apply cr_sub_eq_zero_implies_eq.
    unfold mat2_mul, mat2_trace, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** Length 7 case (k=3, j=2): tr(B³ABA²) = tr(BAB³A²). *)
  Theorem sl2_length7_identity_k3 :
      forall A B : Mat2 F,
        mat2_trace fld (mat2_mul fld (mat2_mul fld B (mat2_mul fld B B))
                       (mat2_mul fld A (mat2_mul fld B
                         (mat2_mul fld A A)))) =
        mat2_trace fld (mat2_mul fld B
                       (mat2_mul fld A (mat2_mul fld B
                         (mat2_mul fld B (mat2_mul fld B
                           (mat2_mul fld A A)))))).
  Proof.
    intros [[[a1 a2] a3] a4] [[[b1 b2] b3] b4].
    apply cr_sub_eq_zero_implies_eq.
    unfold mat2_mul, mat2_trace, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (* ============================================================ *)
  (** ** 9. Matrix-level structural lemmas                          *)
  (* ============================================================ *)

  (** Right-distributivity: (A + B)·C = A·C + B·C. *)
  Lemma mat2_mul_add_distr_r : forall A B C : Mat2 F,
      mat2_mul fld (mat2_add fld A B) C =
      mat2_add fld (mat2_mul fld A C) (mat2_mul fld B C).
  Proof.
    intros [[[a1 a2] a3] a4] [[[b1 b2] b3] b4] [[[c1 c2] c3] c4].
    unfold mat2_mul, mat2_add, mat2_mk.
    apply f_equal2; [apply f_equal2; [apply f_equal2|]|]; ring.
  Qed.

  (** Left-distributivity: A·(B + C) = A·B + A·C. *)
  Lemma mat2_mul_add_distr_l : forall A B C : Mat2 F,
      mat2_mul fld A (mat2_add fld B C) =
      mat2_add fld (mat2_mul fld A B) (mat2_mul fld A C).
  Proof.
    intros [[[a1 a2] a3] a4] [[[b1 b2] b3] b4] [[[c1 c2] c3] c4].
    unfold mat2_mul, mat2_add, mat2_mk.
    apply f_equal2; [apply f_equal2; [apply f_equal2|]|]; ring.
  Qed.

  (** Scalar commutes with matrix mul: (α·A)·B = α·(A·B). *)
  Lemma mat2_scale_mul_l : forall (k : F) (A B : Mat2 F),
      mat2_mul fld (mat2_scale fld k A) B =
      mat2_scale fld k (mat2_mul fld A B).
  Proof.
    intros k [[[a1 a2] a3] a4] [[[b1 b2] b3] b4].
    unfold mat2_mul, mat2_scale, mat2_mk.
    apply f_equal2; [apply f_equal2; [apply f_equal2|]|]; ring.
  Qed.

  Lemma mat2_scale_mul_r : forall (k : F) (A B : Mat2 F),
      mat2_mul fld A (mat2_scale fld k B) =
      mat2_scale fld k (mat2_mul fld A B).
  Proof.
    intros k [[[a1 a2] a3] a4] [[[b1 b2] b3] b4].
    unfold mat2_mul, mat2_scale, mat2_mk.
    apply f_equal2; [apply f_equal2; [apply f_equal2|]|]; ring.
  Qed.

  (** Trace linearity. *)
  Lemma mat2_trace_add : forall A B : Mat2 F,
      mat2_trace fld (mat2_add fld A B) =
      cr_add fld (mat2_trace fld A) (mat2_trace fld B).
  Proof.
    intros [[[a1 a2] a3] a4] [[[b1 b2] b3] b4].
    unfold mat2_trace, mat2_add, mat2_mk. ring.
  Qed.

  Lemma mat2_trace_scale : forall (k : F) (A : Mat2 F),
      mat2_trace fld (mat2_scale fld k A) =
      cr_mul fld k (mat2_trace fld A).
  Proof.
    intros k [[[a1 a2] a3] a4].
    unfold mat2_trace, mat2_scale, mat2_mk. ring.
  Qed.

  Lemma mat2_trace_neg : forall A : Mat2 F,
      mat2_trace fld (mat2_neg fld A) = cr_neg fld (mat2_trace fld A).
  Proof.
    intros [[[a1 a2] a3] a4]. unfold mat2_trace, mat2_neg, mat2_mk. ring.
  Qed.

  Lemma mat2_trace_id : mat2_trace fld (mat2_id fld) =
                       cr_add fld (cr_one fld) (cr_one fld).
  Proof. unfold mat2_trace, mat2_id, mat2_mk. reflexivity. Qed.

  (** General Cayley-Hamilton for ANY 2×2 matrix (no det=1):
      M² = tr(M)·M - det(M)·I. *)
  Lemma mat2_cayley_hamilton_general :
      forall M : Mat2 F,
        mat2_mul fld M M =
        mat2_add fld
          (mat2_scale fld (mat2_trace fld M) M)
          (mat2_neg fld (mat2_scale fld (mat2_det fld M) (mat2_id fld))).
  Proof.
    intros [[[a b] c] d].
    unfold mat2_mul, mat2_trace, mat2_det, mat2_scale, mat2_add,
           mat2_neg, mat2_id, mat2_mk, cr_sub.
    apply f_equal2; [apply f_equal2; [apply f_equal2|]|]; ring.
  Qed.

  (** Trace squared identity: tr(B²·X) = tr(B)·tr(B·X) - det(B)·tr(X)
      for any 2×2 matrices B, X. *)
  Lemma mat2_trace_b2_x :
      forall B X : Mat2 F,
        mat2_trace fld (mat2_mul fld (mat2_mul fld B B) X) =
        cr_sub fld
          (cr_mul fld (mat2_trace fld B)
                       (mat2_trace fld (mat2_mul fld B X)))
          (cr_mul fld (mat2_det fld B) (mat2_trace fld X)).
  Proof.
    intros B X.
    rewrite (mat2_cayley_hamilton_general B).
    rewrite mat2_mul_add_distr_r.
    rewrite mat2_trace_add.
    rewrite mat2_scale_mul_l, mat2_trace_scale.
    (* second summand: -(det B · I) · X = -((det B) · X) *)
    assert (Hneg_id : mat2_mul fld
              (mat2_neg fld (mat2_scale fld (mat2_det fld B) (mat2_id fld))) X =
            mat2_neg fld (mat2_scale fld (mat2_det fld B) X)).
    { destruct B as [[[b1 b2] b3] b4]. destruct X as [[[x1 x2] x3] x4].
      unfold mat2_mul, mat2_neg, mat2_scale, mat2_id, mat2_mk.
      apply f_equal2; [apply f_equal2; [apply f_equal2|]|]; ring. }
    rewrite Hneg_id.
    rewrite mat2_trace_neg, mat2_trace_scale.
    unfold cr_sub. reflexivity.
  Qed.

  (* ============================================================ *)
  (** ** 10. General trace identity family                          *)
  (* ============================================================ *)

  (** [mat2_pow] is already defined above. *)

  (** Setup for the general identity: tr(B²·A·B·A^j) = tr(B·A·B²·A^j)
      for any j, A, B. *)

  (** A^p · A^j = A^{p+j}. Standard induction on p. *)
  Lemma mat2_pow_add : forall (A : Mat2 F) (p j : nat),
      mat2_mul fld (mat2_pow A p) (mat2_pow A j) = mat2_pow A (p + j).
  Proof.
    intros A p. induction p as [|k IH]; intro j.
    - change (mat2_pow A 0) with (mat2_id fld). simpl.
      apply (mat2_mul_id_l fld).
    - simpl.
      rewrite <- (mat2_mul_assoc fld A (mat2_pow A k) (mat2_pow A j)).
      rewrite IH. reflexivity.
  Qed.

  (** Powers commute: A^p · A^j = A^j · A^p. *)
  Lemma mat2_pow_pow_comm : forall (A : Mat2 F) (p j : nat),
      mat2_mul fld (mat2_pow A p) (mat2_pow A j) =
      mat2_mul fld (mat2_pow A j) (mat2_pow A p).
  Proof.
    intros A p j.
    rewrite (mat2_pow_add A p j), (mat2_pow_add A j p).
    f_equal. lia.
  Qed.

  (** Helper: A^j commutes with A. Standard induction. *)
  Lemma mat2_pow_comm_A : forall (A : Mat2 F) (j : nat),
      mat2_mul fld (mat2_pow A j) A = mat2_mul fld A (mat2_pow A j).
  Proof.
    intros A j. induction j as [|k IH].
    - change (mat2_pow A 0) with (mat2_id fld).
      rewrite (mat2_mul_id_l fld A), (mat2_mul_id_r fld A).
      reflexivity.
    - change (mat2_pow A (S k)) with (mat2_mul fld A (mat2_pow A k)).
      (* Goal: (A·pow_k)·A = A·(A·pow_k). Use assoc to expose pow_k·A. *)
      rewrite <- (mat2_mul_assoc fld A (mat2_pow A k) A).
      rewrite IH. reflexivity.
  Qed.

  (** Prepare ABA^j and A^j BA versions, show they have equal trace.

      tr(A·B·A^j) = tr(B·A^j·A) [cyclicity, move A to end]
                  = tr(B·A·A^j) [A^j commutes with A]
                  = tr(A·A^j·B) [cyclicity]
                  = tr(A^j·A·B) [A commutes with A^j]
                  = tr(A^j·B·A) [cyclicity, move A from end to be after B...
                                 actually tr(B·A·A^j) = tr(A^j·B·A) cyclically]. *)
  Lemma trace_ABA_pow_eq_pow_BA :
      forall (A B : Mat2 F) (j : nat),
        mat2_trace fld (mat2_mul fld A (mat2_mul fld B (mat2_pow A j))) =
        mat2_trace fld (mat2_mul fld (mat2_pow A j) (mat2_mul fld B A)).
  Proof.
    intros A B j.
    rewrite (mat2_trace_cyclic _ A
             (mat2_mul fld B (mat2_pow A j))).
    rewrite <- (mat2_mul_assoc _ B (mat2_pow A j) A).
    rewrite (mat2_pow_comm_A A j).
    rewrite (mat2_mul_assoc _ B A (mat2_pow A j)).
    rewrite (mat2_trace_cyclic _ (mat2_mul fld B A) (mat2_pow A j)).
    reflexivity.
  Qed.

  (** ** General trace identity, proved via Chebyshev recurrence.

      Strategy: f(j) := tr(B²·A·B·A^j) - tr(B·A·B²·A^j) satisfies
        f(j+2) = tr(A)·f(j+1) - det(A)·f(j)
      (by Cayley-Hamilton on A^{j+2}). Base cases f(0), f(1) = 0 by
      pure cyclicity. So f(j) = 0 for all j by strong induction. *)

  (** Matrix-level Chebyshev recurrence: A^{j+2} = tr(A)·A^{j+1} - det(A)·A^j. *)
  Lemma mat2_pow_recur : forall (A : Mat2 F) (j : nat),
      mat2_pow A (S (S j)) =
      mat2_add fld
        (mat2_scale fld (mat2_trace fld A) (mat2_pow A (S j)))
        (mat2_neg fld (mat2_scale fld (mat2_det fld A) (mat2_pow A j))).
  Proof.
    intros A j.
    (* A^{j+2} = A · A^{j+1} = A · A · A^j = A² · A^j *)
    change (mat2_pow A (S (S j))) with
           (mat2_mul fld A (mat2_mul fld A (mat2_pow A j))).
    rewrite (mat2_mul_assoc fld A A (mat2_pow A j)).
    (* Goal: A² · A^j = tr(A)·A^{j+1} - det(A)·A^j *)
    rewrite (mat2_cayley_hamilton_general A).
    (* Goal: (tr(A)·A + (-(det(A)·I))) · A^j = tr(A)·A^{j+1} - det(A)·A^j *)
    rewrite mat2_mul_add_distr_r.
    rewrite mat2_scale_mul_l.
    (* Now LHS_term1 = tr(A) · (A · A^j) = tr(A) · A^{j+1}. *)
    change (mat2_pow A (S j)) with (mat2_mul fld A (mat2_pow A j)).
    (* The neg-scale-id-times-A^j part: -(det(A)·I)·A^j = -(det(A)·A^j). *)
    f_equal.
    (* tr(A)·(A·A^j) = tr(A)·(A·A^j): trivial. *)
    (* now second part: mat2_neg(scale det I) · A^j = mat2_neg (scale det A^j) *)
    destruct A as [[[a1 a2] a3] a4].
    destruct (mat2_pow (a1, a2, a3, a4) j) as [[[p1 p2] p3] p4] eqn:Ep.
    unfold mat2_mul, mat2_neg, mat2_scale, mat2_id, mat2_mk.
    apply f_equal2; [apply f_equal2; [apply f_equal2|]|]; ring.
  Qed.

  (** Trace recurrence: tr(M · A^{j+2}) = tr(A)·tr(M · A^{j+1}) -
      det(A)·tr(M · A^j). *)
  Lemma trace_pow_succ_succ_recur :
      forall (M A : Mat2 F) (j : nat),
        mat2_trace fld (mat2_mul fld M (mat2_pow A (S (S j)))) =
        cr_sub fld
          (cr_mul fld (mat2_trace fld A)
                       (mat2_trace fld (mat2_mul fld M (mat2_pow A (S j)))))
          (cr_mul fld (mat2_det fld A)
                       (mat2_trace fld (mat2_mul fld M (mat2_pow A j)))).
  Proof.
    intros M A j.
    rewrite (mat2_pow_recur A j).
    rewrite mat2_mul_add_distr_l.
    rewrite mat2_trace_add.
    rewrite mat2_scale_mul_r, mat2_trace_scale.
    (* Now first term: tr(A)·tr(M·A^{j+1}) ✓. *)
    (* second term: tr(M · -(det(A)·A^j)) = -(det(A)·tr(M·A^j)) *)
    (* drop redundant rewrite *)
    (* Hmm let me just compute. *)
    assert (Hneg : mat2_mul fld M
              (mat2_neg fld (mat2_scale fld (mat2_det fld A) (mat2_pow A j))) =
            mat2_neg fld (mat2_scale fld (mat2_det fld A)
              (mat2_mul fld M (mat2_pow A j)))).
    { destruct M as [[[m1 m2] m3] m4].
      destruct (mat2_pow A j) as [[[p1 p2] p3] p4].
      unfold mat2_mul, mat2_neg, mat2_scale, mat2_mk.
      apply f_equal2; [apply f_equal2; [apply f_equal2|]|]; ring. }
    rewrite Hneg.
    rewrite mat2_trace_neg, mat2_trace_scale.
    unfold cr_sub. reflexivity.
  Qed.

  (** Now apply this to f(j) := tr(B²ABA^j) - tr(BAB²A^j). The recurrence:
      f(j+2) = tr(A)·f(j+1) - det(A)·f(j)
      follows from [trace_pow_succ_succ_recur] with M = B²·A·B for LHS
      and M = B·A·B² for RHS. *)

  (** Base case j = 0: tr(B²AB) = tr(BAB²). By cyclicity. *)
  Lemma sl2_swap_b2_base0 :
      forall A B : Mat2 F,
        mat2_trace fld (mat2_mul fld (mat2_mul fld B B)
                          (mat2_mul fld A B)) =
        mat2_trace fld (mat2_mul fld B
                          (mat2_mul fld A (mat2_mul fld B B))).
  Proof.
    intros [[[a1 a2] a3] a4] [[[b1 b2] b3] b4].
    apply cr_sub_eq_zero_implies_eq.
    unfold mat2_mul, mat2_trace, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** Base case j = 1: tr(B²ABA) = tr(BAB²A). *)
  Lemma sl2_swap_b2_base1 :
      forall A B : Mat2 F,
        mat2_trace fld (mat2_mul fld (mat2_mul fld B B)
                          (mat2_mul fld A (mat2_mul fld B A))) =
        mat2_trace fld (mat2_mul fld B
                          (mat2_mul fld A (mat2_mul fld
                            (mat2_mul fld B B) A))).
  Proof.
    intros [[[a1 a2] a3] a4] [[[b1 b2] b3] b4].
    apply cr_sub_eq_zero_implies_eq.
    unfold mat2_mul, mat2_trace, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** ** Smallest 3-generator length-9 trace identity in M_2(F).

      tr(A·B·C·A·C·A·B·B·C) = tr(A·C·A·B·C·A·B·B·C).

      Computational discovery: the smallest 3-generator (uses A, B, C)
      non-conjugate pair in F_3 over SL(2). Length 9.

      Proof reduction (sketch):
        Both sides have form X·b²·c where X differs.
        By Cayley-Hamilton (B² = tr(B)·B - det(B)·I) plus cyclicity:
        tr(LHS) = tr(B)·tr(abcaca·bc) - det(B)·tr(abcaca·c)
        tr(RHS) = tr(B)·tr(acabca·bc) - det(B)·tr(acabca·c)
        And:
        - tr(abcacabc) = tr(acabcabc) by cyclicity (cyclic rotations).
        - tr(abcacac)  = tr(acabcac)  by cyclicity.

      Direct ring proof on the polynomial difference works at length 9
      with our 12-variable polynomial (entries of A, B, C). *)
  Theorem sl2_3gen_length9_identity :
      forall A B C : Mat2 F,
        mat2_trace fld
          (mat2_mul fld A
            (mat2_mul fld B
              (mat2_mul fld C
                (mat2_mul fld A
                  (mat2_mul fld C
                    (mat2_mul fld A
                      (mat2_mul fld B
                        (mat2_mul fld B C))))))))
        =
        mat2_trace fld
          (mat2_mul fld A
            (mat2_mul fld C
              (mat2_mul fld A
                (mat2_mul fld B
                  (mat2_mul fld C
                    (mat2_mul fld A
                      (mat2_mul fld B
                        (mat2_mul fld B C)))))))).
  Proof.
    intros [[[a1 a2] a3] a4] [[[b1 b2] b3] b4] [[[c1 c2] c3] c4].
    apply cr_sub_eq_zero_implies_eq.
    unfold mat2_mul, mat2_trace, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** Helper to re-associate (B²) · (A · (B · X)) = ((B²·A·B)) · X. *)
  Lemma reassoc_b2_a_b_x :
      forall (B A X : Mat2 F),
        mat2_mul fld (mat2_mul fld B B) (mat2_mul fld A (mat2_mul fld B X)) =
        mat2_mul fld (mat2_mul fld (mat2_mul fld B B) (mat2_mul fld A B)) X.
  Proof.
    intros [[[b1 b2] b3] b4] [[[a1 a2] a3] a4] [[[x1 x2] x3] x4].
    unfold mat2_mul, mat2_mk.
    apply f_equal2; [apply f_equal2; [apply f_equal2|]|]; ring.
  Qed.

  (** Same for B · A · (B² · X) = (B·A·B²) · X. *)
  Lemma reassoc_b_a_b2_x :
      forall (B A X : Mat2 F),
        mat2_mul fld B (mat2_mul fld A
          (mat2_mul fld (mat2_mul fld B B) X)) =
        mat2_mul fld (mat2_mul fld B (mat2_mul fld A (mat2_mul fld B B))) X.
  Proof.
    intros [[[b1 b2] b3] b4] [[[a1 a2] a3] a4] [[[x1 x2] x3] x4].
    unfold mat2_mul, mat2_mk.
    apply f_equal2; [apply f_equal2; [apply f_equal2|]|]; ring.
  Qed.

  (** General trace identity: tr(B²·A·B·A^j) = tr(B·A·B²·A^j) for any
      A, B ∈ M_2(F) and any j ≥ 0. Proved by induction on j using
      the Chebyshev recurrence [trace_pow_succ_succ_recur] and base
      cases [sl2_swap_b2_base0], [sl2_swap_b2_base1]. *)
  Theorem sl2_swap_b2_general :
      forall (A B : Mat2 F) (j : nat),
        mat2_trace fld (mat2_mul fld (mat2_mul fld B B)
                       (mat2_mul fld A (mat2_mul fld B (mat2_pow A j)))) =
        mat2_trace fld (mat2_mul fld B (mat2_mul fld A
                       (mat2_mul fld (mat2_mul fld B B) (mat2_pow A j)))).
  Proof.
    intros A B.
    (* Induction on j with base cases j=0, j=1. Use 2-step induction. *)
    enough (Hboth : forall j,
              mat2_trace fld (mat2_mul fld (mat2_mul fld B B)
                            (mat2_mul fld A (mat2_mul fld B (mat2_pow A j)))) =
              mat2_trace fld (mat2_mul fld B (mat2_mul fld A
                            (mat2_mul fld (mat2_mul fld B B) (mat2_pow A j))))
              /\
              mat2_trace fld (mat2_mul fld (mat2_mul fld B B)
                            (mat2_mul fld A (mat2_mul fld B (mat2_pow A (S j))))) =
              mat2_trace fld (mat2_mul fld B (mat2_mul fld A
                            (mat2_mul fld (mat2_mul fld B B) (mat2_pow A (S j)))))).
    { intros j. apply (Hboth j). }
    induction j as [|k IH].
    - (* j = 0: prove both j=0 and j=1. *)
      split.
      + (* j=0 *)
        change (mat2_pow A 0) with (mat2_id fld).
        rewrite (mat2_mul_id_r fld B).
        rewrite (mat2_mul_id_r fld (mat2_mul fld B B)).
        apply sl2_swap_b2_base0.
      + (* j=1 *)
        change (mat2_pow A 1) with (mat2_mul fld A (mat2_id fld)).
        rewrite (mat2_mul_id_r fld A).
        apply sl2_swap_b2_base1.
    - (* j = S k. Use the j+2 case from k. *)
      destruct IH as [IH1 IH2].
      split.
      + exact IH2.
      + (* j+2 case: use trace_pow_succ_succ_recur. *)
        rewrite (reassoc_b2_a_b_x B A (mat2_pow A (S (S k)))).
        rewrite (reassoc_b_a_b2_x B A (mat2_pow A (S (S k)))).
        rewrite (trace_pow_succ_succ_recur
                  (mat2_mul fld (mat2_mul fld B B) (mat2_mul fld A B))
                  A k).
        rewrite (trace_pow_succ_succ_recur
                  (mat2_mul fld B (mat2_mul fld A (mat2_mul fld B B)))
                  A k).
        (* Now both sides are tr(A)·tr(M_LHS·A^{k+1}) - det(A)·tr(M_LHS·A^k)
           and similar with M_RHS. Need to convert IH1 and IH2 to the
           (M·A^k) and (M·A^{k+1}) form via reassoc, then apply. *)
        rewrite <- (reassoc_b2_a_b_x B A (mat2_pow A k)).
        rewrite <- (reassoc_b_a_b2_x B A (mat2_pow A k)).
        rewrite <- (reassoc_b2_a_b_x B A (mat2_pow A (S k))).
        rewrite <- (reassoc_b_a_b2_x B A (mat2_pow A (S k))).
        rewrite IH1, IH2.
        reflexivity.
  Qed.

  (** Left-side companion: tr(B^{k+2} · X) = tr(B)·tr(B^{k+1}·X)
      - det(B)·tr(B^k · X). Same recurrence but with B^k on the
      LEFT of the product. *)
  Lemma trace_pow_left_recur :
      forall (B X : Mat2 F) (k : nat),
        mat2_trace fld (mat2_mul fld (mat2_pow B (S (S k))) X) =
        cr_sub fld
          (cr_mul fld (mat2_trace fld B)
                       (mat2_trace fld
                          (mat2_mul fld (mat2_pow B (S k)) X)))
          (cr_mul fld (mat2_det fld B)
                       (mat2_trace fld
                          (mat2_mul fld (mat2_pow B k) X))).
  Proof.
    intros B X k.
    rewrite (mat2_trace_cyclic _ (mat2_pow B (S (S k))) X).
    rewrite (trace_pow_succ_succ_recur X B k).
    rewrite (mat2_trace_cyclic _ X (mat2_pow B (S k))).
    rewrite (mat2_trace_cyclic _ X (mat2_pow B k)).
    reflexivity.
  Qed.

  (** Helper to re-associate (M) · (A · (B · X)) = ((M·A·B)) · X. *)
  Lemma reassoc_M_a_b_x :
      forall (M A B X : Mat2 F),
        mat2_mul fld M (mat2_mul fld A (mat2_mul fld B X)) =
        mat2_mul fld (mat2_mul fld (mat2_mul fld M A) B) X.
  Proof.
    intros [[[m1 m2] m3] m4] [[[a1 a2] a3] a4] [[[b1 b2] b3] b4] [[[x1 x2] x3] x4].
    unfold mat2_mul, mat2_mk.
    apply f_equal2; [apply f_equal2; [apply f_equal2|]|]; ring.
  Qed.

  Lemma reassoc_b_a_M_x :
      forall (B A M X : Mat2 F),
        mat2_mul fld B (mat2_mul fld A
          (mat2_mul fld M X)) =
        mat2_mul fld (mat2_mul fld B (mat2_mul fld A M)) X.
  Proof.
    intros [[[b1 b2] b3] b4] [[[a1 a2] a3] a4] [[[m1 m2] m3] m4] [[[x1 x2] x3] x4].
    unfold mat2_mul, mat2_mk.
    apply f_equal2; [apply f_equal2; [apply f_equal2|]|]; ring.
  Qed.

  (** Helper: the LHS of the swap-family expanded by Cayley-Hamilton on B. *)
  Lemma trace_lhs_pow_recur :
      forall (A B : Mat2 F) (k : nat) (j : nat),
        mat2_trace fld (mat2_mul fld (mat2_pow B (S (S k)))
                       (mat2_mul fld A (mat2_mul fld B (mat2_pow A j)))) =
        cr_sub fld
          (cr_mul fld (mat2_trace fld B)
             (mat2_trace fld (mat2_mul fld (mat2_pow B (S k))
                       (mat2_mul fld A (mat2_mul fld B (mat2_pow A j))))))
          (cr_mul fld (mat2_det fld B)
             (mat2_trace fld (mat2_mul fld (mat2_pow B k)
                       (mat2_mul fld A (mat2_mul fld B (mat2_pow A j)))))).
  Proof.
    intros A B k j.
    set (X := mat2_mul fld A (mat2_mul fld B (mat2_pow A j))).
    rewrite (mat2_pow_recur B k).
    rewrite mat2_mul_add_distr_r.
    rewrite mat2_trace_add.
    rewrite mat2_scale_mul_l, mat2_trace_scale.
    (* second term: -(det B · B^k)·X = -((det B)·(B^k·X)) *)
    assert (Hneg : mat2_mul fld
              (mat2_neg fld (mat2_scale fld (mat2_det fld B) (mat2_pow B k)))
              X =
            mat2_neg fld (mat2_scale fld (mat2_det fld B)
              (mat2_mul fld (mat2_pow B k) X))).
    { destruct (mat2_pow B k) as [[[p1 p2] p3] p4].
      destruct X as [[[x1 x2] x3] x4].
      unfold mat2_mul, mat2_neg, mat2_scale, mat2_mk.
      apply f_equal2; [apply f_equal2; [apply f_equal2|]|]; ring. }
    rewrite Hneg.
    rewrite mat2_trace_neg, mat2_trace_scale.
    unfold cr_sub. reflexivity.
  Qed.

  (** Rotation lemma: tr(B·A·M·X) = tr(M·X·B·A) for any M, X. *)
  Lemma trace_rotate_BA :
      forall (B A M X : Mat2 F),
        mat2_trace fld (mat2_mul fld B (mat2_mul fld A (mat2_mul fld M X))) =
        mat2_trace fld (mat2_mul fld M (mat2_mul fld X (mat2_mul fld B A))).
  Proof.
    intros [[[b1 b2] b3] b4] [[[a1 a2] a3] a4]
           [[[m1 m2] m3] m4] [[[x1 x2] x3] x4].
    unfold mat2_mul, mat2_trace, mat2_mk. cbn. ring.
  Qed.

  (** Now the RHS recurrence is just trace_pow_left_recur after rotation. *)
  Lemma trace_rhs_pow_recur :
      forall (A B : Mat2 F) (k j : nat),
        mat2_trace fld (mat2_mul fld B (mat2_mul fld A
                       (mat2_mul fld (mat2_pow B (S (S k))) (mat2_pow A j)))) =
        cr_sub fld
          (cr_mul fld (mat2_trace fld B)
             (mat2_trace fld (mat2_mul fld B (mat2_mul fld A
                       (mat2_mul fld (mat2_pow B (S k)) (mat2_pow A j))))))
          (cr_mul fld (mat2_det fld B)
             (mat2_trace fld (mat2_mul fld B (mat2_mul fld A
                       (mat2_mul fld (mat2_pow B k) (mat2_pow A j)))))).
  Proof.
    intros A B k j.
    rewrite (trace_rotate_BA B A (mat2_pow B (S (S k))) (mat2_pow A j)).
    rewrite (trace_rotate_BA B A (mat2_pow B (S k)) (mat2_pow A j)).
    rewrite (trace_rotate_BA B A (mat2_pow B k) (mat2_pow A j)).
    (* Now LHS: tr(B^{k+2} · (A^j · (B·A))) = tr((B^{k+2}) · X) where
       X = A^j · (B·A). Apply trace_pow_left_recur. *)
    set (X := mat2_mul fld (mat2_pow A j) (mat2_mul fld B A)).
    rewrite (trace_pow_left_recur B X k).
    reflexivity.
  Qed.

  (** Most general: tr(B^k·A·B·A^j) = tr(B·A·B^k·A^j) for any
      k, j, A, B. Now PROVEN by induction. *)
  Theorem sl2_swap_bk_general_proven :
      forall (A B : Mat2 F) (k j : nat),
        mat2_trace fld (mat2_mul fld (mat2_pow B k)
                       (mat2_mul fld A (mat2_mul fld B (mat2_pow A j)))) =
        mat2_trace fld (mat2_mul fld B (mat2_mul fld A
                       (mat2_mul fld (mat2_pow B k) (mat2_pow A j)))).
  Proof.
    intros A B.
    enough (Hboth : forall k j,
              mat2_trace fld (mat2_mul fld (mat2_pow B k)
                             (mat2_mul fld A (mat2_mul fld B (mat2_pow A j)))) =
              mat2_trace fld (mat2_mul fld B (mat2_mul fld A
                             (mat2_mul fld (mat2_pow B k) (mat2_pow A j))))
              /\
              mat2_trace fld (mat2_mul fld (mat2_pow B (S k))
                             (mat2_mul fld A (mat2_mul fld B (mat2_pow A j)))) =
              mat2_trace fld (mat2_mul fld B (mat2_mul fld A
                             (mat2_mul fld (mat2_pow B (S k)) (mat2_pow A j))))).
    { intros k j. apply (Hboth k j). }
    intros k. induction k as [|k IH]; intros j.
    - split.
      + change (mat2_pow B 0) with (mat2_id fld).
        rewrite (mat2_mul_id_l fld
                  (mat2_mul fld A (mat2_mul fld B (mat2_pow A j)))).
        rewrite (mat2_mul_id_l fld (mat2_pow A j)).
        rewrite (mat2_trace_cyclic _ A (mat2_mul fld B (mat2_pow A j))).
        rewrite <- (mat2_mul_assoc fld B (mat2_pow A j) A).
        rewrite (mat2_pow_comm_A A j).
        rewrite (mat2_mul_assoc fld B A (mat2_pow A j)).
        reflexivity.
      + change (mat2_pow B 1) with (mat2_mul fld B (mat2_id fld)).
        rewrite (mat2_mul_id_r fld B).
        reflexivity.
    - destruct (IH j) as [IHk IHk1].
      split.
      + exact IHk1.
      + rewrite (trace_lhs_pow_recur A B k j).
        rewrite (trace_rhs_pow_recur A B k j).
        rewrite IHk, IHk1.
        reflexivity.
  Qed.

  (** A↔B symmetric corollary: tr(A²·B·A·B^j) = tr(A·B·A²·B^j).
      Same proof structure as [sl2_swap_b2_general] with A and B swapped. *)
  Corollary sl2_swap_a2_general :
      forall (A B : Mat2 F) (j : nat),
        mat2_trace fld (mat2_mul fld (mat2_mul fld A A)
                       (mat2_mul fld B (mat2_mul fld A (mat2_pow B j)))) =
        mat2_trace fld (mat2_mul fld A (mat2_mul fld B
                       (mat2_mul fld (mat2_mul fld A A) (mat2_pow B j)))).
  Proof.
    intros A B j. apply (sl2_swap_b2_general B A j).
  Qed.

  (** Even more general: tr(B^k · A^p · B · A^j) = tr(B · A^p · B^k · A^j)
      for any k, p, j. Proved by induction on k, using the same recurrence
      machinery but with A^p replacing A in the middle position. *)

  (** Helper for LHS expansion with A^p prefix. *)
  Lemma trace_lhs_pow_p_recur :
      forall (A B : Mat2 F) (k p j : nat),
        mat2_trace fld (mat2_mul fld (mat2_pow B (S (S k)))
                       (mat2_mul fld (mat2_pow A p)
                         (mat2_mul fld B (mat2_pow A j)))) =
        cr_sub fld
          (cr_mul fld (mat2_trace fld B)
             (mat2_trace fld (mat2_mul fld (mat2_pow B (S k))
                       (mat2_mul fld (mat2_pow A p)
                         (mat2_mul fld B (mat2_pow A j))))))
          (cr_mul fld (mat2_det fld B)
             (mat2_trace fld (mat2_mul fld (mat2_pow B k)
                       (mat2_mul fld (mat2_pow A p)
                         (mat2_mul fld B (mat2_pow A j)))))).
  Proof.
    intros A B k p j.
    set (X := mat2_mul fld (mat2_pow A p)
                (mat2_mul fld B (mat2_pow A j))).
    rewrite (mat2_pow_recur B k).
    rewrite mat2_mul_add_distr_r.
    rewrite mat2_trace_add.
    rewrite mat2_scale_mul_l, mat2_trace_scale.
    assert (Hneg : mat2_mul fld
              (mat2_neg fld (mat2_scale fld (mat2_det fld B) (mat2_pow B k)))
              X =
            mat2_neg fld (mat2_scale fld (mat2_det fld B)
              (mat2_mul fld (mat2_pow B k) X))).
    { destruct (mat2_pow B k) as [[[q1 q2] q3] q4].
      destruct X as [[[x1 x2] x3] x4].
      unfold mat2_mul, mat2_neg, mat2_scale, mat2_mk.
      apply f_equal2; [apply f_equal2; [apply f_equal2|]|]; ring. }
    rewrite Hneg, mat2_trace_neg, mat2_trace_scale.
    unfold cr_sub. reflexivity.
  Qed.

  (** Helper for RHS expansion with A^p prefix; via rotation. *)
  Lemma trace_rhs_pow_p_recur :
      forall (A B : Mat2 F) (k p j : nat),
        mat2_trace fld (mat2_mul fld B (mat2_mul fld (mat2_pow A p)
                       (mat2_mul fld (mat2_pow B (S (S k))) (mat2_pow A j)))) =
        cr_sub fld
          (cr_mul fld (mat2_trace fld B)
             (mat2_trace fld (mat2_mul fld B (mat2_mul fld (mat2_pow A p)
                       (mat2_mul fld (mat2_pow B (S k)) (mat2_pow A j))))))
          (cr_mul fld (mat2_det fld B)
             (mat2_trace fld (mat2_mul fld B (mat2_mul fld (mat2_pow A p)
                       (mat2_mul fld (mat2_pow B k) (mat2_pow A j)))))).
  Proof.
    intros A B k p j.
    rewrite (trace_rotate_BA B (mat2_pow A p)
              (mat2_pow B (S (S k))) (mat2_pow A j)).
    rewrite (trace_rotate_BA B (mat2_pow A p)
              (mat2_pow B (S k)) (mat2_pow A j)).
    rewrite (trace_rotate_BA B (mat2_pow A p)
              (mat2_pow B k) (mat2_pow A j)).
    set (X := mat2_mul fld (mat2_pow A j)
                (mat2_mul fld B (mat2_pow A p))).
    rewrite (trace_pow_left_recur B X k).
    reflexivity.
  Qed.

  Theorem sl2_swap_bk_p_general :
      forall (A B : Mat2 F) (k p j : nat),
        mat2_trace fld (mat2_mul fld (mat2_pow B k)
                       (mat2_mul fld (mat2_pow A p)
                         (mat2_mul fld B (mat2_pow A j)))) =
        mat2_trace fld (mat2_mul fld B
                       (mat2_mul fld (mat2_pow A p)
                         (mat2_mul fld (mat2_pow B k) (mat2_pow A j)))).
  Proof.
    intros A B.
    enough (Hboth : forall k p j,
              mat2_trace fld (mat2_mul fld (mat2_pow B k)
                             (mat2_mul fld (mat2_pow A p)
                               (mat2_mul fld B (mat2_pow A j)))) =
              mat2_trace fld (mat2_mul fld B
                             (mat2_mul fld (mat2_pow A p)
                               (mat2_mul fld (mat2_pow B k) (mat2_pow A j))))
              /\
              mat2_trace fld (mat2_mul fld (mat2_pow B (S k))
                             (mat2_mul fld (mat2_pow A p)
                               (mat2_mul fld B (mat2_pow A j)))) =
              mat2_trace fld (mat2_mul fld B
                             (mat2_mul fld (mat2_pow A p)
                               (mat2_mul fld (mat2_pow B (S k)) (mat2_pow A j))))).
    { intros k p j. apply (Hboth k p j). }
    intros k. induction k as [|k IH]; intros p j.
    - split.
      + (* k=0: tr(A^p·B·A^j) = tr(B·A^p·A^j). *)
        change (mat2_pow B 0) with (mat2_id fld).
        rewrite (mat2_mul_id_l fld
                  (mat2_mul fld (mat2_pow A p)
                    (mat2_mul fld B (mat2_pow A j)))).
        rewrite (mat2_mul_id_l fld (mat2_pow A j)).
        (* Goal: tr(A^p · (B · A^j)) = tr(B · (A^p · A^j))
           cyclic: tr(A^p · B · A^j) = tr(B · A^j · A^p)
           by pow_comm: = tr(B · A^p · A^j). *)
        rewrite (mat2_trace_cyclic _ (mat2_pow A p)
                  (mat2_mul fld B (mat2_pow A j))).
        (* tr( (B · A^j) · A^p ) *)
        rewrite <- (mat2_mul_assoc fld B (mat2_pow A j) (mat2_pow A p)).
        rewrite (mat2_pow_pow_comm A j p).
        rewrite (mat2_mul_assoc fld B (mat2_pow A p) (mat2_pow A j)).
        (* Goal: tr(B · A^p · A^j) — but RHS we want is tr(B · (A^p · A^j)) *)
        reflexivity.
      + (* k=1: B^1 = B·I = B. *)
        change (mat2_pow B 1) with (mat2_mul fld B (mat2_id fld)).
        rewrite (mat2_mul_id_r fld B).
        reflexivity.
    - destruct (IH p j) as [IHk IHk1].
      split.
      + exact IHk1.
      + rewrite (trace_lhs_pow_p_recur A B k p j).
        rewrite (trace_rhs_pow_p_recur A B k p j).
        rewrite IHk, IHk1.
        reflexivity.
  Qed.

  (** Generic length-9 3-gen identity in trailing power C is conjectured. *)

  (** Another 3-gen length-9 identity:
      tr(B·B·A·C·B·A·C·A·C) = tr(B·A·C·B·B·A·C·A·C). *)
  Theorem sl2_3gen_length9_id_2 :
      forall A B C : Mat2 F,
        mat2_trace fld
          (mat2_mul fld B (mat2_mul fld B (mat2_mul fld A
            (mat2_mul fld C (mat2_mul fld B (mat2_mul fld A
              (mat2_mul fld C (mat2_mul fld A C)))))))) =
        mat2_trace fld
          (mat2_mul fld B (mat2_mul fld A (mat2_mul fld C
            (mat2_mul fld B (mat2_mul fld B (mat2_mul fld A
              (mat2_mul fld C (mat2_mul fld A C)))))))).
  Proof.
    intros [[[a1 a2] a3] a4] [[[b1 b2] b3] b4] [[[c1 c2] c3] c4].
    apply cr_sub_eq_zero_implies_eq.
    unfold mat2_mul, mat2_trace, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** Parametric 3-gen identity family: extending sl2_3gen_length9_identity
      to arbitrary trailing power of C.

      tr(A·B·C·A·C·A·B² · C^{j+1}) = tr(A·C·A·B·C·A·B² · C^{j+1})
      for any A, B, C ∈ M_2 and any j ≥ 0.

      Proof: by induction on j. Base j=0 is sl2_3gen_length9_identity.
      Inductive step uses trace_pow_succ_succ_recur. *)

  (** Length-10 base case (j=1) skipped — polynomial too large for ring. *)

  (** Another 3-gen length-9 identity:
      tr(B·A·C·B·A·A·C·B·C) = tr(B·A·A·C·B·A·C·B·C). *)
  Theorem sl2_3gen_length9_id_4 :
      forall A B C : Mat2 F,
        mat2_trace fld
          (mat2_mul fld B (mat2_mul fld A (mat2_mul fld C
            (mat2_mul fld B (mat2_mul fld A (mat2_mul fld A
              (mat2_mul fld C (mat2_mul fld B C)))))))) =
        mat2_trace fld
          (mat2_mul fld B (mat2_mul fld A (mat2_mul fld A
            (mat2_mul fld C (mat2_mul fld B (mat2_mul fld A
              (mat2_mul fld C (mat2_mul fld B C)))))))).
  Proof.
    intros [[[a1 a2] a3] a4] [[[b1 b2] b3] b4] [[[c1 c2] c3] c4].
    apply cr_sub_eq_zero_implies_eq.
    unfold mat2_mul, mat2_trace, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** Yet another 3-gen length-9 identity:
      tr(A·B·C·A·B·A·B·C·C) = tr(A·B·A·B·C·A·B·C·C). *)
  Theorem sl2_3gen_length9_id_5 :
      forall A B C : Mat2 F,
        mat2_trace fld
          (mat2_mul fld A (mat2_mul fld B (mat2_mul fld C
            (mat2_mul fld A (mat2_mul fld B (mat2_mul fld A
              (mat2_mul fld B (mat2_mul fld C C)))))))) =
        mat2_trace fld
          (mat2_mul fld A (mat2_mul fld B (mat2_mul fld A
            (mat2_mul fld B (mat2_mul fld C (mat2_mul fld A
              (mat2_mul fld B (mat2_mul fld C C)))))))).
  Proof.
    intros [[[a1 a2] a3] a4] [[[b1 b2] b3] b4] [[[c1 c2] c3] c4].
    apply cr_sub_eq_zero_implies_eq.
    unfold mat2_mul, mat2_trace, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** And one more: tr(A·A·B·C·A·B·C·B·C) = tr(A·B·C·A·A·B·C·B·C). *)
  Theorem sl2_3gen_length9_id_6 :
      forall A B C : Mat2 F,
        mat2_trace fld
          (mat2_mul fld A (mat2_mul fld A (mat2_mul fld B
            (mat2_mul fld C (mat2_mul fld A (mat2_mul fld B
              (mat2_mul fld C (mat2_mul fld B C)))))))) =
        mat2_trace fld
          (mat2_mul fld A (mat2_mul fld B (mat2_mul fld C
            (mat2_mul fld A (mat2_mul fld A (mat2_mul fld B
              (mat2_mul fld C (mat2_mul fld B C)))))))).
  Proof.
    intros [[[a1 a2] a3] a4] [[[b1 b2] b3] b4] [[[c1 c2] c3] c4].
    apply cr_sub_eq_zero_implies_eq.
    unfold mat2_mul, mat2_trace, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** A third 3-gen length-9 identity:
      tr(B·A·C·B·A·B·A·C·C) = tr(B·A·B·A·C·B·A·C·C). *)
  Theorem sl2_3gen_length9_id_3 :
      forall A B C : Mat2 F,
        mat2_trace fld
          (mat2_mul fld B (mat2_mul fld A (mat2_mul fld C
            (mat2_mul fld B (mat2_mul fld A (mat2_mul fld B
              (mat2_mul fld A (mat2_mul fld C C)))))))) =
        mat2_trace fld
          (mat2_mul fld B (mat2_mul fld A (mat2_mul fld B
            (mat2_mul fld A (mat2_mul fld C (mat2_mul fld B
              (mat2_mul fld A (mat2_mul fld C C)))))))).
  Proof.
    intros [[[a1 a2] a3] a4] [[[b1 b2] b3] b4] [[[c1 c2] c3] c4].
    apply cr_sub_eq_zero_implies_eq.
    unfold mat2_mul, mat2_trace, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** Original conjecture name [sl2_swap_bk_general] retained as a
      Corollary of [sl2_swap_bk_general_proven] for backward compat. *)
  Corollary sl2_swap_bk_general :
      forall (A B : Mat2 F) (k j : nat),
        mat2_trace fld (mat2_mul fld (mat2_pow B k)
                       (mat2_mul fld A (mat2_mul fld B (mat2_pow A j)))) =
        mat2_trace fld (mat2_mul fld B (mat2_mul fld A
                       (mat2_mul fld (mat2_pow B k) (mat2_pow A j)))).
  Proof. apply sl2_swap_bk_general_proven. Qed.

  (** Even more general: B^l in the "middle" instead of just B. *)
  Lemma trace_lhs_pow_kl_recur :
      forall (A B : Mat2 F) (k p l j : nat),
        mat2_trace fld (mat2_mul fld (mat2_pow B (S (S k)))
                       (mat2_mul fld (mat2_pow A p)
                         (mat2_mul fld (mat2_pow B l) (mat2_pow A j)))) =
        cr_sub fld
          (cr_mul fld (mat2_trace fld B)
             (mat2_trace fld (mat2_mul fld (mat2_pow B (S k))
                       (mat2_mul fld (mat2_pow A p)
                         (mat2_mul fld (mat2_pow B l) (mat2_pow A j))))))
          (cr_mul fld (mat2_det fld B)
             (mat2_trace fld (mat2_mul fld (mat2_pow B k)
                       (mat2_mul fld (mat2_pow A p)
                         (mat2_mul fld (mat2_pow B l) (mat2_pow A j)))))).
  Proof.
    intros A B k p l j.
    set (X := mat2_mul fld (mat2_pow A p)
                (mat2_mul fld (mat2_pow B l) (mat2_pow A j))).
    rewrite (mat2_pow_recur B k).
    rewrite mat2_mul_add_distr_r.
    rewrite mat2_trace_add.
    rewrite mat2_scale_mul_l, mat2_trace_scale.
    assert (Hneg : mat2_mul fld
              (mat2_neg fld (mat2_scale fld (mat2_det fld B) (mat2_pow B k)))
              X =
            mat2_neg fld (mat2_scale fld (mat2_det fld B)
              (mat2_mul fld (mat2_pow B k) X))).
    { destruct (mat2_pow B k) as [[[q1 q2] q3] q4].
      destruct X as [[[x1 x2] x3] x4].
      unfold mat2_mul, mat2_neg, mat2_scale, mat2_mk.
      apply f_equal2; [apply f_equal2; [apply f_equal2|]|]; ring. }
    rewrite Hneg, mat2_trace_neg, mat2_trace_scale.
    unfold cr_sub. reflexivity.
  Qed.

  Lemma trace_rhs_pow_kl_recur :
      forall (A B : Mat2 F) (k p l j : nat),
        mat2_trace fld (mat2_mul fld (mat2_pow B l) (mat2_mul fld (mat2_pow A p)
                       (mat2_mul fld (mat2_pow B (S (S k))) (mat2_pow A j)))) =
        cr_sub fld
          (cr_mul fld (mat2_trace fld B)
             (mat2_trace fld (mat2_mul fld (mat2_pow B l) (mat2_mul fld (mat2_pow A p)
                       (mat2_mul fld (mat2_pow B (S k)) (mat2_pow A j))))))
          (cr_mul fld (mat2_det fld B)
             (mat2_trace fld (mat2_mul fld (mat2_pow B l) (mat2_mul fld (mat2_pow A p)
                       (mat2_mul fld (mat2_pow B k) (mat2_pow A j)))))).
  Proof.
    intros A B k p l j.
    (* Bring B^{k+2} to front via cyclicity. *)
    rewrite (trace_rotate_BA (mat2_pow B l) (mat2_pow A p)
              (mat2_pow B (S (S k))) (mat2_pow A j)).
    rewrite (trace_rotate_BA (mat2_pow B l) (mat2_pow A p)
              (mat2_pow B (S k)) (mat2_pow A j)).
    rewrite (trace_rotate_BA (mat2_pow B l) (mat2_pow A p)
              (mat2_pow B k) (mat2_pow A j)).
    set (X := mat2_mul fld (mat2_pow A j)
                (mat2_mul fld (mat2_pow B l) (mat2_pow A p))).
    rewrite (trace_pow_left_recur B X k).
    reflexivity.
  Qed.

  (** [sl2_swap_bk_bl_general]: Most general 4-parameter theorem.

      tr(B^k · A^p · B^l · A^j) = tr(B^l · A^p · B^k · A^j) for any
      k, p, l, j. *)
  Theorem sl2_swap_bk_bl_general :
      forall (A B : Mat2 F) (k p l j : nat),
        mat2_trace fld (mat2_mul fld (mat2_pow B k)
                       (mat2_mul fld (mat2_pow A p)
                         (mat2_mul fld (mat2_pow B l) (mat2_pow A j)))) =
        mat2_trace fld (mat2_mul fld (mat2_pow B l)
                       (mat2_mul fld (mat2_pow A p)
                         (mat2_mul fld (mat2_pow B k) (mat2_pow A j)))).
  Proof.
    intros A B.
    enough (Hboth : forall k p l j,
              mat2_trace fld (mat2_mul fld (mat2_pow B k)
                             (mat2_mul fld (mat2_pow A p)
                               (mat2_mul fld (mat2_pow B l) (mat2_pow A j)))) =
              mat2_trace fld (mat2_mul fld (mat2_pow B l)
                             (mat2_mul fld (mat2_pow A p)
                               (mat2_mul fld (mat2_pow B k) (mat2_pow A j))))
              /\
              mat2_trace fld (mat2_mul fld (mat2_pow B (S k))
                             (mat2_mul fld (mat2_pow A p)
                               (mat2_mul fld (mat2_pow B l) (mat2_pow A j)))) =
              mat2_trace fld (mat2_mul fld (mat2_pow B l)
                             (mat2_mul fld (mat2_pow A p)
                               (mat2_mul fld (mat2_pow B (S k)) (mat2_pow A j))))).
    { intros k p l j. apply (Hboth k p l j). }
    intros k. induction k as [|k IH]; intros p l j.
    - split.
      + (* k=0: B^0 = I. By cyclicity + pow_pow_comm. *)
        change (mat2_pow B 0) with (mat2_id fld).
        rewrite (mat2_mul_id_l fld
                  (mat2_mul fld (mat2_pow A p)
                    (mat2_mul fld (mat2_pow B l) (mat2_pow A j)))).
        rewrite (mat2_mul_id_l fld (mat2_pow A j)).
        rewrite (mat2_trace_cyclic _ (mat2_pow A p)
                  (mat2_mul fld (mat2_pow B l) (mat2_pow A j))).
        rewrite <- (mat2_mul_assoc fld (mat2_pow B l) (mat2_pow A j)
                     (mat2_pow A p)).
        rewrite (mat2_pow_pow_comm A j p).
        rewrite (mat2_mul_assoc fld (mat2_pow B l) (mat2_pow A p)
                  (mat2_pow A j)).
        reflexivity.
      + (* k=1: B^1 = B. Apply sl2_swap_bk_p_general with l in the
                       k_lemma slot and swap LHS/RHS. *)
        change (mat2_pow B 1) with (mat2_mul fld B (mat2_id fld)).
        rewrite (mat2_mul_id_r fld B).
        symmetry.
        apply (sl2_swap_bk_p_general A B l p j).
    - destruct (IH p l j) as [IHk IHk1].
      split.
      + exact IHk1.
      + rewrite (trace_lhs_pow_kl_recur A B k p l j).
        rewrite (trace_rhs_pow_kl_recur A B k p l j).
        rewrite IHk, IHk1.
        reflexivity.
  Qed.

  (** Helper unfoldings. *)
  Lemma mat2_pow_one : forall (M : Mat2 F),
      mat2_pow M 1 = M.
  Proof.
    intro M.
    change (mat2_pow M 1) with (mat2_mul fld M (mat2_id fld)).
    apply mat2_mul_id_r.
  Qed.

  Lemma mat2_pow_two : forall (M : Mat2 F),
      mat2_pow M 2 = mat2_mul fld M M.
  Proof.
    intro M.
    change (mat2_pow M 2) with (mat2_mul fld M (mat2_mul fld M (mat2_id fld))).
    rewrite (mat2_mul_id_r fld M). reflexivity.
  Qed.

  (** A↔B symmetric form: tr(A^k · B^p · A^l · B^j) = tr(A^l · B^p · A^k · B^j). *)
  Corollary sl2_swap_ak_al_general :
      forall (A B : Mat2 F) (k p l j : nat),
        mat2_trace fld (mat2_mul fld (mat2_pow A k)
                       (mat2_mul fld (mat2_pow B p)
                         (mat2_mul fld (mat2_pow A l) (mat2_pow B j)))) =
        mat2_trace fld (mat2_mul fld (mat2_pow A l)
                       (mat2_mul fld (mat2_pow B p)
                         (mat2_mul fld (mat2_pow A k) (mat2_pow B j)))).
  Proof. intros A B k p l j. apply (sl2_swap_bk_bl_general B A k p l j). Qed.

  (** Corollary: smallest positive identity follows from
      sl2_swap_bk_bl_general. *)
  Corollary sl2_smallest_positive_via_general :
      forall A B : Mat2 F,
        mat2_trace fld (mat2_mul fld (mat2_mul fld B B)
                        (mat2_mul fld A (mat2_mul fld B
                          (mat2_mul fld A A)))) =
        mat2_trace fld (mat2_mul fld B
                        (mat2_mul fld A (mat2_mul fld B
                          (mat2_mul fld B (mat2_mul fld A A))))).
  Proof.
    intros A B.
    pose proof (sl2_swap_bk_bl_general A B 2 1 1 2) as H.
    rewrite (mat2_pow_two B) in H.
    rewrite (mat2_pow_one B) in H.
    rewrite (mat2_pow_one A) in H.
    rewrite (mat2_pow_two A) in H.
    rewrite <- (mat2_mul_assoc fld B B (mat2_mul fld A A)) in H.
    exact H.
  Qed.

  (** Length-7 identity via sl2_swap_bk_bl_general. *)
  Corollary sl2_length7_via_general :
      forall A B : Mat2 F,
        mat2_trace fld (mat2_mul fld (mat2_mul fld B B)
                       (mat2_mul fld A (mat2_mul fld B
                         (mat2_mul fld A (mat2_mul fld A A))))) =
        mat2_trace fld (mat2_mul fld B
                       (mat2_mul fld A (mat2_mul fld B
                         (mat2_mul fld B (mat2_mul fld A
                           (mat2_mul fld A A)))))).
  Proof.
    intros A B.
    pose proof (sl2_swap_bk_bl_general A B 2 1 1 3) as H.
    rewrite (mat2_pow_two B) in H.
    rewrite (mat2_pow_one B) in H.
    rewrite (mat2_pow_one A) in H.
    change (mat2_pow A 3) with (mat2_mul fld A (mat2_pow A 2)) in H.
    rewrite (mat2_pow_two A) in H.
    rewrite <- (mat2_mul_assoc fld B B (mat2_mul fld A (mat2_mul fld A A))) in H.
    exact H.
  Qed.

  (** Helper: A^3 = A · (A · A). *)
  Lemma mat2_pow_three : forall (M : Mat2 F),
      mat2_pow M 3 = mat2_mul fld M (mat2_mul fld M M).
  Proof.
    intro M.
    change (mat2_pow M 3) with (mat2_mul fld M (mat2_pow M 2)).
    rewrite (mat2_pow_two M). reflexivity.
  Qed.

  (** Helper: A^4 = A · (A · (A · A)). *)
  Lemma mat2_pow_four : forall (M : Mat2 F),
      mat2_pow M 4 = mat2_mul fld M (mat2_mul fld M (mat2_mul fld M M)).
  Proof.
    intro M.
    change (mat2_pow M 4) with (mat2_mul fld M (mat2_pow M 3)).
    rewrite (mat2_pow_three M). reflexivity.
  Qed.

  (** Length-7 (k=3) identity via sl2_swap_bk_bl_general. *)
  Corollary sl2_length7_k3_via_general :
      forall A B : Mat2 F,
        mat2_trace fld (mat2_mul fld (mat2_mul fld B (mat2_mul fld B B))
                       (mat2_mul fld A (mat2_mul fld B
                         (mat2_mul fld A A)))) =
        mat2_trace fld (mat2_mul fld B
                       (mat2_mul fld A (mat2_mul fld B
                         (mat2_mul fld B (mat2_mul fld B
                           (mat2_mul fld A A)))))).
  Proof.
    intros A B.
    pose proof (sl2_swap_bk_bl_general A B 3 1 1 2) as H.
    rewrite (mat2_pow_three B) in H.
    rewrite (mat2_pow_one B) in H.
    rewrite (mat2_pow_one A) in H.
    rewrite (mat2_pow_two A) in H.
    rewrite <- (mat2_mul_assoc fld B (mat2_mul fld B B)
                 (mat2_mul fld A A)) in H.
    rewrite <- (mat2_mul_assoc fld B B (mat2_mul fld A A)) in H.
    exact H.
  Qed.

  (** Helper: A^5 = A · A · A · A · A. *)
  Lemma mat2_pow_five : forall (M : Mat2 F),
      mat2_pow M 5 = mat2_mul fld M
                       (mat2_mul fld M
                         (mat2_mul fld M
                           (mat2_mul fld M M))).
  Proof.
    intro M.
    change (mat2_pow M 5) with (mat2_mul fld M (mat2_pow M 4)).
    rewrite (mat2_pow_four M). reflexivity.
  Qed.

  (** Length-9 (k=2, j=5) identity. *)
  Corollary sl2_length9_via_general :
      forall A B : Mat2 F,
        mat2_trace fld (mat2_mul fld (mat2_mul fld B B)
                       (mat2_mul fld A (mat2_mul fld B
                         (mat2_mul fld A (mat2_mul fld A
                           (mat2_mul fld A (mat2_mul fld A A))))))) =
        mat2_trace fld (mat2_mul fld B
                       (mat2_mul fld A (mat2_mul fld B
                         (mat2_mul fld B (mat2_mul fld A
                           (mat2_mul fld A (mat2_mul fld A
                             (mat2_mul fld A A)))))))).
  Proof.
    intros A B.
    pose proof (sl2_swap_bk_bl_general A B 2 1 1 5) as H.
    rewrite (mat2_pow_two B) in H.
    rewrite (mat2_pow_one B) in H.
    rewrite (mat2_pow_one A) in H.
    rewrite (mat2_pow_five A) in H.
    rewrite <- (mat2_mul_assoc fld B B
                 (mat2_mul fld A (mat2_mul fld A
                   (mat2_mul fld A (mat2_mul fld A A))))) in H.
    exact H.
  Qed.

  (** Length-8 identity via sl2_swap_bk_bl_general. *)
  Corollary sl2_length8_via_general :
      forall A B : Mat2 F,
        mat2_trace fld (mat2_mul fld (mat2_mul fld B B)
                       (mat2_mul fld A (mat2_mul fld B
                         (mat2_mul fld A (mat2_mul fld A
                           (mat2_mul fld A A)))))) =
        mat2_trace fld (mat2_mul fld B
                       (mat2_mul fld A (mat2_mul fld B
                         (mat2_mul fld B (mat2_mul fld A
                           (mat2_mul fld A (mat2_mul fld A A))))))).
  Proof.
    intros A B.
    pose proof (sl2_swap_bk_bl_general A B 2 1 1 4) as H.
    rewrite (mat2_pow_two B) in H.
    rewrite (mat2_pow_one B) in H.
    rewrite (mat2_pow_one A) in H.
    rewrite (mat2_pow_four A) in H.
    rewrite <- (mat2_mul_assoc fld B B
                 (mat2_mul fld A (mat2_mul fld A (mat2_mul fld A A)))) in H.
    exact H.
  Qed.

  (** ** Parametric 3-gen family extending [sl2_3gen_length9_id_3].

      tr(B·A·C·B·A·B·A · C^{j+1}) = tr(B·A·B·A·C·B·A · C^{j+1})
      for any A, B, C ∈ M_2(F) and any j ≥ 0.

      The j=0 case is a length-8 cyclicity statement.
      The j=1 case is sl2_3gen_length9_id_3.
      The j+2 case follows by trace_pow_succ_succ_recur. *)

  (** Generic lifting lemma: if tr(M) = tr(N) and tr(M·C) = tr(N·C),
      then forall j, tr(M · C^j) = tr(N · C^j). Proof by 2-step induction
      using [trace_pow_succ_succ_recur]. *)
  Lemma trace_lifted_by_pow :
      forall (M N C : Mat2 F),
        mat2_trace fld M = mat2_trace fld N ->
        mat2_trace fld (mat2_mul fld M C) = mat2_trace fld (mat2_mul fld N C) ->
        forall j : nat,
          mat2_trace fld (mat2_mul fld M (mat2_pow C j)) =
          mat2_trace fld (mat2_mul fld N (mat2_pow C j)).
  Proof.
    intros M N C HM_N HMC_NC.
    enough (Hboth : forall j,
              mat2_trace fld (mat2_mul fld M (mat2_pow C j)) =
              mat2_trace fld (mat2_mul fld N (mat2_pow C j))
              /\
              mat2_trace fld (mat2_mul fld M (mat2_pow C (S j))) =
              mat2_trace fld (mat2_mul fld N (mat2_pow C (S j)))).
    { intros j. apply (Hboth j). }
    induction j as [|j IH].
    - split.
      + change (mat2_pow C 0) with (mat2_id fld).
        rewrite (mat2_mul_id_r fld M).
        rewrite (mat2_mul_id_r fld N).
        exact HM_N.
      + change (mat2_pow C 1) with (mat2_mul fld C (mat2_id fld)).
        rewrite (mat2_mul_id_r fld C).
        exact HMC_NC.
    - destruct IH as [IHj IHj1].
      split.
      + exact IHj1.
      + rewrite (trace_pow_succ_succ_recur M C j).
        rewrite (trace_pow_succ_succ_recur N C j).
        rewrite IHj, IHj1. reflexivity.
  Qed.

  (** Two-variable lifting: lift trace equality through two power
      coordinates A^j · B^k. Given the four base agreements
        tr(M) = tr(N), tr(M·A) = tr(N·A),
        tr(M·B) = tr(N·B), tr(M·A·B) = tr(N·A·B),
      we get tr(M · A^j · B^k) = tr(N · A^j · B^k) for all j, k.

      Proof structure: outer trace_lifted_by_pow on B (lifting over k)
      with parametric M·A^j, N·A^j; the two base cases come from
      single-variable lifting on A (with cyclicity to handle the
      M·A^j·B form). *)

  Lemma trace_lifted_by_two_pows :
      forall (M N A B : Mat2 F),
        mat2_trace fld M = mat2_trace fld N ->
        mat2_trace fld (mat2_mul fld M A) = mat2_trace fld (mat2_mul fld N A) ->
        mat2_trace fld (mat2_mul fld M B) = mat2_trace fld (mat2_mul fld N B) ->
        mat2_trace fld (mat2_mul fld M (mat2_mul fld A B)) =
          mat2_trace fld (mat2_mul fld N (mat2_mul fld A B)) ->
        forall j k : nat,
          mat2_trace fld (mat2_mul fld M
                            (mat2_mul fld (mat2_pow A j) (mat2_pow B k))) =
          mat2_trace fld (mat2_mul fld N
                            (mat2_mul fld (mat2_pow A j) (mat2_pow B k))).
  Proof.
    intros M N A B HM HMA HMB HMAB j k.
    (* Step 1: prove tr(M·A^j) = tr(N·A^j) by single-var lifting on A. *)
    pose proof (trace_lifted_by_pow M N A HM HMA) as Hlift_A.
    (* Step 2: prove tr(M·A^j·B) = tr(N·A^j·B) for all j.
       By cyclicity: tr(M·A^j·B) = tr(B·M·A^j). Need tr(B·M·A^j) = tr(B·N·A^j).
       Apply trace_lifted_by_pow with M' := B·M, N' := B·N, on A. *)
    assert (Hlift_AB : forall jj,
      mat2_trace fld (mat2_mul fld (mat2_mul fld M (mat2_pow A jj)) B) =
      mat2_trace fld (mat2_mul fld (mat2_mul fld N (mat2_pow A jj)) B)).
    { intros jj.
      (* tr(M·A^jj·B) by cyclicity = tr(B·M·A^jj). *)
      rewrite (mat2_trace_cyclic _ (mat2_mul fld M (mat2_pow A jj)) B).
      rewrite (mat2_trace_cyclic _ (mat2_mul fld N (mat2_pow A jj)) B).
      (* Goal: tr(B · (M · A^jj)) = tr(B · (N · A^jj)).
         Reassociate as ((B·M) · A^jj) and ((B·N) · A^jj) so we can apply
         trace_lifted_by_pow with M' = B·M, N' = B·N. mat2_mul_assoc says
         M·(N·P) = (M·N)·P, so the forward direction reassociates left. *)
      rewrite (mat2_mul_assoc fld B M (mat2_pow A jj)).
      rewrite (mat2_mul_assoc fld B N (mat2_pow A jj)).
      apply trace_lifted_by_pow.
      - (* tr(B·M) = tr(B·N) ⟸ tr(M·B) = tr(N·B) by cyclicity. *)
        rewrite (mat2_trace_cyclic _ B M), (mat2_trace_cyclic _ B N).
        exact HMB.
      - (* tr((B·M)·A) = tr((B·N)·A) ⟸ tr(M·(A·B)) = tr(N·(A·B)) by cyclicity.
           Goal: tr(mat2_mul (mat2_mul B M) A) = tr(mat2_mul (mat2_mul B N) A).
           Reassociate (B·M)·A as B·(M·A) using <- direction. *)
        rewrite <- (mat2_mul_assoc fld B M A), <- (mat2_mul_assoc fld B N A).
        rewrite (mat2_trace_cyclic _ B (mat2_mul fld M A)).
        rewrite (mat2_trace_cyclic _ B (mat2_mul fld N A)).
        (* Goal: tr((M·A)·B) = tr((N·A)·B). HMAB has tr(M·(A·B)).
           Reassociate (M·A)·B as M·(A·B) using <- direction. *)
        rewrite <- (mat2_mul_assoc fld M A B), <- (mat2_mul_assoc fld N A B).
        exact HMAB. }
    (* Step 3: outer trace_lifted_by_pow on B with parametric (M·A^j, N·A^j).
       Reassociate M·(A^j·B^k) as (M·A^j)·B^k via mat2_mul_assoc forward. *)
    rewrite (mat2_mul_assoc fld M (mat2_pow A j) (mat2_pow B k)).
    rewrite (mat2_mul_assoc fld N (mat2_pow A j) (mat2_pow B k)).
    apply trace_lifted_by_pow.
    - (* base 1: tr(M·A^j) = tr(N·A^j). *)
      apply Hlift_A.
    - (* base 2: tr((M·A^j)·B) = tr((N·A^j)·B). *)
      apply Hlift_AB.
  Qed.

  Lemma sl2_3gen_length7_base :
      forall A B C : Mat2 F,
        mat2_trace fld (mat2_mul fld B (mat2_mul fld A
                       (mat2_mul fld C (mat2_mul fld B
                         (mat2_mul fld A (mat2_mul fld B A)))))) =
        mat2_trace fld (mat2_mul fld B (mat2_mul fld A
                       (mat2_mul fld B (mat2_mul fld A
                         (mat2_mul fld C (mat2_mul fld B A)))))).
  Proof.
    intros [[[a1 a2] a3] a4] [[[b1 b2] b3] b4] [[[c1 c2] c3] c4].
    apply cr_sub_eq_zero_implies_eq.
    unfold mat2_mul, mat2_trace, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** Length-8 base: tr(BACBABAC) = tr(BABACBAC) (cyclic rotation). *)
  Lemma sl2_3gen_length8_base :
      forall A B C : Mat2 F,
        mat2_trace fld (mat2_mul fld B (mat2_mul fld A
                       (mat2_mul fld C (mat2_mul fld B
                         (mat2_mul fld A (mat2_mul fld B
                           (mat2_mul fld A C))))))) =
        mat2_trace fld (mat2_mul fld B (mat2_mul fld A
                       (mat2_mul fld B (mat2_mul fld A
                         (mat2_mul fld C (mat2_mul fld B
                           (mat2_mul fld A C))))))).
  Proof.
    intros [[[a1 a2] a3] a4] [[[b1 b2] b3] b4] [[[c1 c2] c3] c4].
    apply cr_sub_eq_zero_implies_eq.
    unfold mat2_mul, mat2_trace, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** Parametric 3-generator family.

      For any 2×2 matrices A, B, C and any j ≥ 0:
        tr((BACBABA) · C^j) = tr((BABACBA) · C^j).

      Proof: combine [trace_lifted_by_pow] with two base cases:
      - sl2_3gen_length7_base (j=0)
      - sl2_3gen_length8_base (j=1, stated for the right-associated form). *)

  Theorem sl2_3gen_param_C :
      forall (A B C : Mat2 F) (j : nat),
        mat2_trace fld (mat2_mul fld
          (mat2_mul fld B (mat2_mul fld A
            (mat2_mul fld C (mat2_mul fld B
              (mat2_mul fld A (mat2_mul fld B A))))))
          (mat2_pow C j)) =
        mat2_trace fld (mat2_mul fld
          (mat2_mul fld B (mat2_mul fld A
            (mat2_mul fld B (mat2_mul fld A
              (mat2_mul fld C (mat2_mul fld B A))))))
          (mat2_pow C j)).
  Proof.
    intros A B C j.
    apply trace_lifted_by_pow.
    - (* tr(M) = tr(N) — length 7. *)
      apply sl2_3gen_length7_base.
    - (* tr(M·C) = tr(N·C) — length 8 via sl2_3gen_length8_base
         after associativity rewrites. *)
      destruct A as [[[a1 a2] a3] a4].
      destruct B as [[[b1 b2] b3] b4].
      destruct C as [[[c1 c2] c3] c4].
      apply cr_sub_eq_zero_implies_eq.
      unfold mat2_mul, mat2_trace, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** Second parametric 3-generator family extending [sl2_3gen_length9_id_5].
      tr((ABCABAB) · C^j) = tr((ABABCAB) · C^j) for all j ≥ 0. *)

  Theorem sl2_3gen_param_C_2 :
      forall (A B C : Mat2 F) (j : nat),
        mat2_trace fld (mat2_mul fld
          (mat2_mul fld A (mat2_mul fld B
            (mat2_mul fld C (mat2_mul fld A
              (mat2_mul fld B (mat2_mul fld A B))))))
          (mat2_pow C j)) =
        mat2_trace fld (mat2_mul fld
          (mat2_mul fld A (mat2_mul fld B
            (mat2_mul fld A (mat2_mul fld B
              (mat2_mul fld C (mat2_mul fld A B))))))
          (mat2_pow C j)).
  Proof.
    intros A B C j.
    apply trace_lifted_by_pow.
    - (* tr(M) = tr(N) — length 7. *)
      destruct A as [[[a1 a2] a3] a4].
      destruct B as [[[b1 b2] b3] b4].
      destruct C as [[[c1 c2] c3] c4].
      apply cr_sub_eq_zero_implies_eq.
      unfold mat2_mul, mat2_trace, mat2_mk, cr_sub. cbn. ring.
    - (* tr(M·C) = tr(N·C) — length 8. *)
      destruct A as [[[a1 a2] a3] a4].
      destruct B as [[[b1 b2] b3] b4].
      destruct C as [[[c1 c2] c3] c4].
      apply cr_sub_eq_zero_implies_eq.
      unfold mat2_mul, mat2_trace, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** Third parametric 3-generator family.

      tr((ACBACAC) · B^j) = tr((ACACBAC) · B^j) for all j ≥ 0.

      Specializes at j=2 (modulo cyclicity) to sl2_3gen_length9_id_2:
        tr(BBACBACAC) = tr(BACBBACAC). *)

  Theorem sl2_3gen_param_B :
      forall (A B C : Mat2 F) (j : nat),
        mat2_trace fld (mat2_mul fld
          (mat2_mul fld A (mat2_mul fld C
            (mat2_mul fld B (mat2_mul fld A
              (mat2_mul fld C (mat2_mul fld A C))))))
          (mat2_pow B j)) =
        mat2_trace fld (mat2_mul fld
          (mat2_mul fld A (mat2_mul fld C
            (mat2_mul fld A (mat2_mul fld C
              (mat2_mul fld B (mat2_mul fld A C))))))
          (mat2_pow B j)).
  Proof.
    intros A B C j.
    apply trace_lifted_by_pow.
    - destruct A as [[[a1 a2] a3] a4].
      destruct B as [[[b1 b2] b3] b4].
      destruct C as [[[c1 c2] c3] c4].
      apply cr_sub_eq_zero_implies_eq.
      unfold mat2_mul, mat2_trace, mat2_mk, cr_sub. cbn. ring.
    - destruct A as [[[a1 a2] a3] a4].
      destruct B as [[[b1 b2] b3] b4].
      destruct C as [[[c1 c2] c3] c4].
      apply cr_sub_eq_zero_implies_eq.
      unfold mat2_mul, mat2_trace, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** Fourth parametric 3-generator family.

      tr((CBCBACB) · A^j) = tr((CBACBCB) · A^j) for all j ≥ 0.

      Specializes at j=2 (modulo cyclicity) to sl2_3gen_length9_id_4. *)

  Theorem sl2_3gen_param_A :
      forall (A B C : Mat2 F) (j : nat),
        mat2_trace fld (mat2_mul fld
          (mat2_mul fld C (mat2_mul fld B
            (mat2_mul fld C (mat2_mul fld B
              (mat2_mul fld A (mat2_mul fld C B))))))
          (mat2_pow A j)) =
        mat2_trace fld (mat2_mul fld
          (mat2_mul fld C (mat2_mul fld B
            (mat2_mul fld A (mat2_mul fld C
              (mat2_mul fld B (mat2_mul fld C B))))))
          (mat2_pow A j)).
  Proof.
    intros A B C j.
    apply trace_lifted_by_pow.
    - destruct A as [[[a1 a2] a3] a4].
      destruct B as [[[b1 b2] b3] b4].
      destruct C as [[[c1 c2] c3] c4].
      apply cr_sub_eq_zero_implies_eq.
      unfold mat2_mul, mat2_trace, mat2_mk, cr_sub. cbn. ring.
    - destruct A as [[[a1 a2] a3] a4].
      destruct B as [[[b1 b2] b3] b4].
      destruct C as [[[c1 c2] c3] c4].
      apply cr_sub_eq_zero_implies_eq.
      unfold mat2_mul, mat2_trace, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** Fifth parametric 3-generator family.

      tr((BCABCBC) · A^j) = tr((BCBCABC) · A^j) for all j ≥ 0. *)

  Theorem sl2_3gen_param_A_2 :
      forall (A B C : Mat2 F) (j : nat),
        mat2_trace fld (mat2_mul fld
          (mat2_mul fld B (mat2_mul fld C
            (mat2_mul fld A (mat2_mul fld B
              (mat2_mul fld C (mat2_mul fld B C))))))
          (mat2_pow A j)) =
        mat2_trace fld (mat2_mul fld
          (mat2_mul fld B (mat2_mul fld C
            (mat2_mul fld B (mat2_mul fld C
              (mat2_mul fld A (mat2_mul fld B C))))))
          (mat2_pow A j)).
  Proof.
    intros A B C j.
    apply trace_lifted_by_pow.
    - destruct A as [[[a1 a2] a3] a4].
      destruct B as [[[b1 b2] b3] b4].
      destruct C as [[[c1 c2] c3] c4].
      apply cr_sub_eq_zero_implies_eq.
      unfold mat2_mul, mat2_trace, mat2_mk, cr_sub. cbn. ring.
    - destruct A as [[[a1 a2] a3] a4].
      destruct B as [[[b1 b2] b3] b4].
      destruct C as [[[c1 c2] c3] c4].
      apply cr_sub_eq_zero_implies_eq.
      unfold mat2_mul, mat2_trace, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** Sixth parametric 3-generator family.

      tr((CABCACA) · B^j) = tr((CACABCA) · B^j) for all j ≥ 0.

      Specializes at j=2 (modulo cyclicity) to sl2_3gen_length9_identity:
        tr(ABCACABBC) = tr(ACABCABBC). *)

  Theorem sl2_3gen_param_B_2 :
      forall (A B C : Mat2 F) (j : nat),
        mat2_trace fld (mat2_mul fld
          (mat2_mul fld C (mat2_mul fld A
            (mat2_mul fld B (mat2_mul fld C
              (mat2_mul fld A (mat2_mul fld C A))))))
          (mat2_pow B j)) =
        mat2_trace fld (mat2_mul fld
          (mat2_mul fld C (mat2_mul fld A
            (mat2_mul fld C (mat2_mul fld A
              (mat2_mul fld B (mat2_mul fld C A))))))
          (mat2_pow B j)).
  Proof.
    intros A B C j.
    apply trace_lifted_by_pow.
    - destruct A as [[[a1 a2] a3] a4].
      destruct B as [[[b1 b2] b3] b4].
      destruct C as [[[c1 c2] c3] c4].
      apply cr_sub_eq_zero_implies_eq.
      unfold mat2_mul, mat2_trace, mat2_mk, cr_sub. cbn. ring.
    - destruct A as [[[a1 a2] a3] a4].
      destruct B as [[[b1 b2] b3] b4].
      destruct C as [[[c1 c2] c3] c4].
      apply cr_sub_eq_zero_implies_eq.
      unfold mat2_mul, mat2_trace, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (* ============================================================ *)
  (** ** Section: Fricke character coordinates                      *)
  (* ============================================================ *)

  (** *** Fricke character coordinates for a pair (A, B).

      The triple χ(A, B) = (tr A, tr B, tr (A·B)) provides classical
      Fricke coordinates on the SL(2,F)-character variety of F_2. *)

  Definition fricke_chi (A B : Mat2 F) : F * F * F :=
    (mat2_trace fld A,
     mat2_trace fld B,
     mat2_trace fld (mat2_mul fld A B)).

  (** Generalized conjugation-trace identity (no det constraint):
      tr(g·A·adj(g)) = det(g) · tr(A).
      When det g = 1: tr(g·A·g⁻¹) = tr(A) (the standard fact). *)

  Lemma sl2_trace_conj_adj_general :
      forall (g A : Mat2 F),
        mat2_trace fld
          (mat2_mul fld g (mat2_mul fld A (mat2_adj fld g))) =
        cr_mul fld (mat2_det fld g) (mat2_trace fld A).
  Proof.
    intros [[[g1 g2] g3] g4] [[[a1 a2] a3] a4].
    unfold mat2_mul, mat2_trace, mat2_adj, mat2_det, mat2_mk, cr_sub. cbn.
    ring.
  Qed.

  (** Conjugation invariance of trace for SL(2). *)

  Lemma sl2_trace_conj_invariant :
      forall (g A : Mat2 F),
        mat2_det fld g = cr_one fld ->
        mat2_trace fld
          (mat2_mul fld g (mat2_mul fld A (mat2_adj fld g))) =
        mat2_trace fld A.
  Proof.
    intros g A Hg.
    rewrite (sl2_trace_conj_adj_general g A).
    rewrite Hg. ring.
  Qed.

  (** *** Determinant of a product equals the product of determinants. *)

  Lemma mat2_det_mul :
      forall (A B : Mat2 F),
        mat2_det fld (mat2_mul fld A B) =
        cr_mul fld (mat2_det fld A) (mat2_det fld B).
  Proof.
    intros [[[a1 a2] a3] a4] [[[b1 b2] b3] b4].
    unfold mat2_det, mat2_mul, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** Trace of [(A·B)·(A·B)] for SL(2): tr((A·B)²) = tr(A·B)² − 2. *)

  Corollary sl2_trace_ab_squared :
      forall (A B : Mat2 F),
        mat2_det fld A = cr_one fld ->
        mat2_det fld B = cr_one fld ->
        mat2_trace fld
          (mat2_mul fld (mat2_mul fld A B) (mat2_mul fld A B)) =
        cr_sub fld
          (cr_mul fld (mat2_trace fld (mat2_mul fld A B))
                      (mat2_trace fld (mat2_mul fld A B)))
          (cr_add fld (cr_one fld) (cr_one fld)).
  Proof.
    intros A B HA HB.
    apply (sl2_trace_squared (mat2_mul fld A B)).
    rewrite mat2_det_mul, HA, HB. ring.
  Qed.

  (** *** Generalized conjugation-product trace.

      For ANY 2×2 g, A, B (no det constraint):
        tr((g·A·adj(g))·(g·B·adj(g))) = det(g)² · tr(A·B).

      Pure polynomial identity provable by ring. When det g = 1 this
      gives tr(A·B), establishing conjugation invariance of tr(A·B). *)

  Lemma sl2_trace_conj_pair_general :
      forall (g A B : Mat2 F),
        mat2_trace fld
          (mat2_mul fld (mat2_mul fld g (mat2_mul fld A (mat2_adj fld g)))
                        (mat2_mul fld g (mat2_mul fld B (mat2_adj fld g)))) =
        cr_mul fld
          (cr_mul fld (mat2_det fld g) (mat2_det fld g))
          (mat2_trace fld (mat2_mul fld A B)).
  Proof.
    intros [[[g1 g2] g3] g4] [[[a1 a2] a3] a4] [[[b1 b2] b3] b4].
    unfold mat2_mul, mat2_trace, mat2_adj, mat2_det, mat2_mk, cr_sub.
    cbn. ring.
  Qed.

  (** Conjugation invariance of tr(A·B) for SL(2). *)

  Lemma sl2_trace_ab_conj_invariant :
      forall (g A B : Mat2 F),
        mat2_det fld g = cr_one fld ->
        mat2_trace fld
          (mat2_mul fld (mat2_mul fld g (mat2_mul fld A (mat2_adj fld g)))
                        (mat2_mul fld g (mat2_mul fld B (mat2_adj fld g)))) =
        mat2_trace fld (mat2_mul fld A B).
  Proof.
    intros g A B Hg.
    rewrite (sl2_trace_conj_pair_general g A B).
    rewrite Hg. ring.
  Qed.

  (** *** Trace of [M · A^2] in terms of {tr M, tr(M·A), tr A, det A}.

      For any 2×2 M, A:
        tr(M · A²) = tr(A) · tr(M · A) − det(A) · tr(M). *)

  Lemma sl2_trace_m_a_squared :
      forall (M A : Mat2 F),
        mat2_trace fld (mat2_mul fld M (mat2_mul fld A A)) =
        cr_sub fld
          (cr_mul fld (mat2_trace fld A)
             (mat2_trace fld (mat2_mul fld M A)))
          (cr_mul fld (mat2_det fld A) (mat2_trace fld M)).
  Proof.
    intros [[[m1 m2] m3] m4] [[[a1 a2] a3] a4].
    unfold mat2_mul, mat2_trace, mat2_det, mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** *** Trace product identity for SL(2): a Chebyshev-style relation.

      For SL(2,F) (det A = 1) and any n:
        tr(A) · tr(A^{n+1}) = tr(A^{n+2}) + tr(A^n).

      This is the rearranged Chebyshev recurrence
        tr(A^{n+2}) = tr(A) · tr(A^{n+1}) − tr(A^n).
      Useful as a "product" form of the recurrence. *)

  Lemma sl2_trace_pow_product :
      forall (A : Mat2 F) (n : nat),
        mat2_det fld A = cr_one fld ->
        cr_mul fld (mat2_trace fld A)
                   (mat2_trace fld (mat2_pow A (S n))) =
        cr_add fld
          (mat2_trace fld (mat2_pow A (S (S n))))
          (mat2_trace fld (mat2_pow A n)).
  Proof.
    intros A n HA.
    rewrite (sl2_trace_pow_chebyshev A n HA).
    unfold cr_sub. ring.
  Qed.

  (** *** Lie-vs-group commutator identity for SL(2).

      For ANY 2×2 matrices A, B (no det constraint):
        tr(A·B·adj(A)·adj(B)) + det(A·B − B·A) = 2 · det(A) · det(B).

      In SL(2): tr([A, B]_group) + det([A, B]_Lie) = 2.

      Combining the FMK identity (for the group commutator) with the
      formula for det of the matrix Lie commutator [A,B]_Lie = A·B − B·A.
      Pure ring identity in 8 variables. *)

  Lemma sl2_lie_group_commutator_identity :
      forall A B : Mat2 F,
        cr_add fld
          (mat2_trace fld
             (mat2_mul fld A
                (mat2_mul fld B
                   (mat2_mul fld (mat2_adj fld A) (mat2_adj fld B)))))
          (mat2_det fld
             (mat2_add fld (mat2_mul fld A B)
                            (mat2_neg fld (mat2_mul fld B A)))) =
        cr_add fld
          (cr_mul fld (mat2_det fld A) (mat2_det fld B))
          (cr_mul fld (mat2_det fld A) (mat2_det fld B)).
  Proof.
    intros [[[a1 a2] a3] a4] [[[b1 b2] b3] b4].
    unfold mat2_mul, mat2_trace, mat2_adj, mat2_det, mat2_add, mat2_neg,
           mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** Specialization to SL(2,F): tr([A,B]_group) + det([A,B]_Lie) = 2. *)

  Corollary sl2_lie_group_commutator_sl2 :
      forall A B : Mat2 F,
        mat2_det fld A = cr_one fld ->
        mat2_det fld B = cr_one fld ->
        cr_add fld
          (mat2_trace fld
             (mat2_mul fld A
                (mat2_mul fld B
                   (mat2_mul fld (mat2_adj fld A) (mat2_adj fld B)))))
          (mat2_det fld
             (mat2_add fld (mat2_mul fld A B)
                            (mat2_neg fld (mat2_mul fld B A)))) =
        cr_add fld (cr_one fld) (cr_one fld).
  Proof.
    intros A B HA HB.
    rewrite (sl2_lie_group_commutator_identity A B).
    rewrite HA, HB. ring.
  Qed.

  (** *** Corollary: if A·B = B·A (commute), then tr([A,B]_group) = 2.

      For A, B in SL(2,F) that commute, the group commutator is the
      identity, so its trace is 2. We prove this via the Lie-vs-group
      identity: when A·B = B·A, det([A,B]_Lie) = det(0) = 0, so
      tr([A,B]_group) = 2 - 0 = 2. *)

  Lemma sl2_commute_implies_group_commutator_trace_2 :
      forall A B : Mat2 F,
        mat2_det fld A = cr_one fld ->
        mat2_det fld B = cr_one fld ->
        mat2_mul fld A B = mat2_mul fld B A ->
        mat2_trace fld
          (mat2_mul fld A
             (mat2_mul fld B
                (mat2_mul fld (mat2_adj fld A) (mat2_adj fld B)))) =
        cr_add fld (cr_one fld) (cr_one fld).
  Proof.
    intros A B HA HB Hcom.
    pose proof (sl2_lie_group_commutator_sl2 A B HA HB) as Hlg.
    (* Now show det(A·B - B·A) = 0 since A·B = B·A makes A·B - B·A = 0. *)
    assert (HzeroLie : mat2_det fld
              (mat2_add fld (mat2_mul fld A B)
                            (mat2_neg fld (mat2_mul fld B A))) = cr_zero fld).
    { rewrite Hcom.
      destruct (mat2_mul fld B A) as [[[m1 m2] m3] m4].
      unfold mat2_add, mat2_neg, mat2_det, mat2_mk, cr_sub. cbn. ring. }
    rewrite HzeroLie in Hlg.
    rewrite cr_add_zero in Hlg.
    exact Hlg.
  Qed.

  (** *** Determinant of Lie commutator in trace coordinates.

      For ANY 2×2 A, B (no det constraint):
        det(A·B − B·A) =
            4·det(A)·det(B) + tr(A)·tr(B)·tr(A·B)
            − det(A)·tr(B)² − det(B)·tr(A)² − tr(A·B)².

      Pure ring identity. In SL(2) (det = 1):
        det([A,B]_Lie) = 4 − tr(A)² − tr(B)² − tr(A·B)² + tr(A)·tr(B)·tr(A·B)
                       = 4 − m(tr A, tr B, tr A·B)
      where m is the Markov polynomial. *)

  Lemma sl2_det_lie_commutator_trace_form :
      forall A B : Mat2 F,
        mat2_det fld
          (mat2_add fld (mat2_mul fld A B)
                         (mat2_neg fld (mat2_mul fld B A))) =
        cr_sub fld
          (cr_add fld
             (cr_add fld
                (cr_add fld
                   (cr_mul fld (mat2_det fld A) (mat2_det fld B))
                   (cr_mul fld (mat2_det fld A) (mat2_det fld B)))
                (cr_add fld
                   (cr_mul fld (mat2_det fld A) (mat2_det fld B))
                   (cr_mul fld (mat2_det fld A) (mat2_det fld B))))
             (cr_mul fld (mat2_trace fld A)
                (cr_mul fld (mat2_trace fld B)
                            (mat2_trace fld (mat2_mul fld A B)))))
          (cr_add fld
             (cr_add fld
                (cr_mul fld (mat2_det fld A)
                   (cr_mul fld (mat2_trace fld B) (mat2_trace fld B)))
                (cr_mul fld (mat2_det fld B)
                   (cr_mul fld (mat2_trace fld A) (mat2_trace fld A))))
             (cr_mul fld (mat2_trace fld (mat2_mul fld A B))
                         (mat2_trace fld (mat2_mul fld A B)))).
  Proof.
    intros [[[a1 a2] a3] a4] [[[b1 b2] b3] b4].
    unfold mat2_mul, mat2_trace, mat2_add, mat2_neg, mat2_det,
           mat2_mk, cr_sub. cbn. ring.
  Qed.

  (** Specialization: for SL(2,F), det([A,B]_Lie) = 4 − m(x, y, z)
      where m is the Markov polynomial. *)

  Corollary sl2_det_lie_commutator_markov :
      forall A B : Mat2 F,
        mat2_det fld A = cr_one fld ->
        mat2_det fld B = cr_one fld ->
        mat2_det fld
          (mat2_add fld (mat2_mul fld A B)
                         (mat2_neg fld (mat2_mul fld B A))) =
        cr_sub fld
          (cr_add fld (cr_add fld (cr_one fld) (cr_one fld))
                       (cr_add fld (cr_one fld) (cr_one fld)))
          (markov_poly (mat2_trace fld A) (mat2_trace fld B)
                       (mat2_trace fld (mat2_mul fld A B))).
  Proof.
    intros A B HA HB.
    rewrite (sl2_det_lie_commutator_trace_form A B).
    unfold markov_poly. rewrite HA, HB. unfold cr_sub. ring.
  Qed.

  (** Full Fricke χ conjugation invariance. *)

  Lemma fricke_chi_conj_invariant :
      forall (A B g : Mat2 F),
        mat2_det fld g = cr_one fld ->
        fricke_chi
          (mat2_mul fld g (mat2_mul fld A (mat2_adj fld g)))
          (mat2_mul fld g (mat2_mul fld B (mat2_adj fld g))) =
        fricke_chi A B.
  Proof.
    intros A B g Hg. unfold fricke_chi.
    rewrite (sl2_trace_conj_invariant g A Hg).
    rewrite (sl2_trace_conj_invariant g B Hg).
    rewrite (sl2_trace_ab_conj_invariant g A B Hg).
    reflexivity.
  Qed.

End SL2Fricke.

(* ================================================================== *)
(** * Concrete instances over Qc                                        *)
(* ================================================================== *)

From CAG Require Import LinAlg.QField.
From Stdlib Require Import QArith Qcanon.

(** Demonstrate the theorem on specific SL(2, Z) matrices. *)

(** A = [[2,1],[1,1]], B = [[1,1],[1,2]]. Both in SL(2, Z). *)

Definition test_A : Mat2 Qc :=
  mat2_mk
    (Q2Qc 2%Q) (Q2Qc 1%Q)
    (Q2Qc 1%Q) (Q2Qc 1%Q).

Definition test_B : Mat2 Qc :=
  mat2_mk
    (Q2Qc 1%Q) (Q2Qc 1%Q)
    (Q2Qc 1%Q) (Q2Qc 2%Q).

(** sl2_swap_bk_bl_general applied: equality is verified at the level
    of Qc trace polynomials. *)
Example sl2_swap_bk_bl_at_test_AB :
    forall k p l j : nat,
      mat2_trace Qc_Field
        (mat2_mul Qc_Field (mat2_pow Qc_Field test_B k)
          (mat2_mul Qc_Field (mat2_pow Qc_Field test_A p)
            (mat2_mul Qc_Field (mat2_pow Qc_Field test_B l) (mat2_pow Qc_Field test_A j)))) =
      mat2_trace Qc_Field
        (mat2_mul Qc_Field (mat2_pow Qc_Field test_B l)
          (mat2_mul Qc_Field (mat2_pow Qc_Field test_A p)
            (mat2_mul Qc_Field (mat2_pow Qc_Field test_B k) (mat2_pow Qc_Field test_A j)))).
Proof. intros k p l j. apply sl2_swap_bk_bl_general. Qed.

(** Test FMK identity at (test_A, test_B). Both have det = 1.

    tr(A·B·adj(A)·adj(B)) =
       tr(A)² + tr(B)² + tr(A·B)² − tr(A)·tr(B)·tr(A·B) − 2.

    For test_A = [[2,1],[1,1]], test_B = [[1,1],[1,2]]:
      tr(A) = 3, tr(B) = 3, tr(A·B) = ?
      A·B = [[2·1+1·1, 2·1+1·2], [1·1+1·1, 1·1+1·2]] = [[3, 4], [2, 3]],
      so tr(A·B) = 6.
      Markov polynomial m(3, 3, 6) = 9 + 9 + 36 - 3·3·6 - 2 = 54 - 54 - 2 = -2.
      So tr([A,B]) = -2 (parabolic / Markov triple). *)

Lemma test_AB_det_A : mat2_det Qc_Field test_A = cr_one Qc_Field.
Proof. unfold test_A, mat2_det, mat2_mk. reflexivity. Qed.

Lemma test_AB_det_B : mat2_det Qc_Field test_B = cr_one Qc_Field.
Proof. unfold test_B, mat2_det, mat2_mk. reflexivity. Qed.

Example sl2_fmk_at_test_AB :
    mat2_trace Qc_Field
      (mat2_mul Qc_Field test_A
         (mat2_mul Qc_Field test_B
            (mat2_mul Qc_Field (mat2_adj Qc_Field test_A)
                                (mat2_adj Qc_Field test_B)))) =
    cr_sub Qc_Field
      (cr_add Qc_Field
         (cr_add Qc_Field
            (cr_mul Qc_Field (mat2_trace Qc_Field test_A)
                              (mat2_trace Qc_Field test_A))
            (cr_mul Qc_Field (mat2_trace Qc_Field test_B)
                              (mat2_trace Qc_Field test_B)))
         (cr_sub Qc_Field
            (cr_mul Qc_Field
               (mat2_trace Qc_Field (mat2_mul Qc_Field test_A test_B))
               (mat2_trace Qc_Field (mat2_mul Qc_Field test_A test_B)))
            (cr_mul Qc_Field
               (cr_mul Qc_Field (mat2_trace Qc_Field test_A)
                                 (mat2_trace Qc_Field test_B))
               (mat2_trace Qc_Field (mat2_mul Qc_Field test_A test_B)))))
      (cr_add Qc_Field (cr_one Qc_Field) (cr_one Qc_Field)).
Proof.
  apply (sl2_fmk_commutator Qc_Field test_A test_B
                            test_AB_det_A test_AB_det_B).
Qed.

(** Numerical verification: tr([test_A, test_B]) = -2.

    With tr(A) = 3, tr(B) = 3, tr(A·B) = 6:
      m(3, 3, 6) = 9 + 9 + 36 − 3·3·6 − 2 = 54 − 54 − 2 = −2.
    So the test pair (test_A, test_B) sits on the parabolic Markov
    fiber {tr([A,B]) = −2}, which is the famous Markov surface
    {x² + y² + z² = xyz} after substitution. *)

Example sl2_fmk_test_AB_value :
    mat2_trace Qc_Field
      (mat2_mul Qc_Field test_A
         (mat2_mul Qc_Field test_B
            (mat2_mul Qc_Field (mat2_adj Qc_Field test_A)
                                (mat2_adj Qc_Field test_B)))) =
    cr_neg Qc_Field (cr_add Qc_Field (cr_one Qc_Field) (cr_one Qc_Field)).
Proof. unfold test_A, test_B. vm_compute. reflexivity. Qed.

(** The Markov triple x = tr(A) = 3, y = tr(B) = 3, z = tr(A·B) = 6
    satisfies the Markov equation x² + y² + z² = x·y·z. This places
    (test_A, test_B) on the Markov surface. *)

Example sl2_test_AB_markov_triple :
    let x := mat2_trace Qc_Field test_A in
    let y := mat2_trace Qc_Field test_B in
    let z := mat2_trace Qc_Field (mat2_mul Qc_Field test_A test_B) in
    cr_add Qc_Field
      (cr_add Qc_Field (cr_mul Qc_Field x x) (cr_mul Qc_Field y y))
      (cr_mul Qc_Field z z) =
    cr_mul Qc_Field x (cr_mul Qc_Field y z).
Proof. unfold test_A, test_B. vm_compute. reflexivity. Qed.

(** Third test SL(2, Z) matrix C = [[1, 2], [1, 3]] (det = 1). *)
Definition test_C : Mat2 Qc :=
  mat2_mk
    (Q2Qc 1%Q) (Q2Qc 2%Q)
    (Q2Qc 1%Q) (Q2Qc 3%Q).

(** Numerical verification of Vogt's linear identity at (test_A, test_B, test_C).
    Both sides equal 42:
      tr(ABC) + tr(ACB) = 20 + 22 = 42.
      tr(A)·tr(BC) + tr(B)·tr(CA) + tr(C)·tr(AB) − tr(A)·tr(B)·tr(C)
      = 3·10 + 3·8 + 4·6 − 3·3·4 = 30 + 24 + 24 − 36 = 42. *)

Example sl2_vogt_linear_at_test_ABC :
    cr_add Qc_Field
      (mat2_trace Qc_Field
        (mat2_mul Qc_Field test_A
          (mat2_mul Qc_Field test_B test_C)))
      (mat2_trace Qc_Field
        (mat2_mul Qc_Field test_A
          (mat2_mul Qc_Field test_C test_B))) =
    cr_sub Qc_Field
      (cr_add Qc_Field
        (cr_add Qc_Field
          (cr_mul Qc_Field
            (mat2_trace Qc_Field test_A)
            (mat2_trace Qc_Field (mat2_mul Qc_Field test_B test_C)))
          (cr_mul Qc_Field
            (mat2_trace Qc_Field test_B)
            (mat2_trace Qc_Field (mat2_mul Qc_Field test_C test_A))))
        (cr_mul Qc_Field
          (mat2_trace Qc_Field test_C)
          (mat2_trace Qc_Field (mat2_mul Qc_Field test_A test_B))))
      (cr_mul Qc_Field
        (mat2_trace Qc_Field test_A)
        (cr_mul Qc_Field
          (mat2_trace Qc_Field test_B)
          (mat2_trace Qc_Field test_C))).
Proof. apply sl2_vogt_linear. Qed.

(** Numerical: tr(test_A · test_B · test_C) = 20 in Qc. *)
Example sl2_test_ABC_trace_value :
    mat2_trace Qc_Field
      (mat2_mul Qc_Field test_A (mat2_mul Qc_Field test_B test_C)) =
    Q2Qc 20%Q.
Proof. unfold test_A, test_B, test_C. vm_compute. reflexivity. Qed.

(** Numerical: tr(test_A · test_C · test_B) = 22 in Qc. *)
Example sl2_test_ACB_trace_value :
    mat2_trace Qc_Field
      (mat2_mul Qc_Field test_A (mat2_mul Qc_Field test_C test_B)) =
    Q2Qc 22%Q.
Proof. unfold test_A, test_B, test_C. vm_compute. reflexivity. Qed.

(** Lemma: det(test_C) = 1. *)
Lemma test_AC_det_C : mat2_det Qc_Field test_C = cr_one Qc_Field.
Proof. unfold test_C, mat2_det, mat2_mk. reflexivity. Qed.

(** Numerical: det([test_A, test_C]_Lie) = 11 in Qc. *)
Example sl2_test_AC_lie_commutator_det :
    mat2_det Qc_Field
      (mat2_add Qc_Field
         (mat2_mul Qc_Field test_A test_C)
         (mat2_neg Qc_Field (mat2_mul Qc_Field test_C test_A))) =
    Q2Qc 11%Q.
Proof. unfold test_A, test_C. vm_compute. reflexivity. Qed.

(** Lie-vs-group identity at (test_A, test_C): tr([A,C]_group) + det([A,C]_Lie)
    = (-9) + 11 = 2. The (-9) comes from the Markov polynomial:
    m(3, 4, 8) = 9 + 16 + 64 - 96 = -7, then tr([A,C]_group) = m - 2 = -9. *)

Example sl2_test_AC_lie_group_commutator_sum :
    cr_add Qc_Field
      (mat2_trace Qc_Field
         (mat2_mul Qc_Field test_A
            (mat2_mul Qc_Field test_C
               (mat2_mul Qc_Field (mat2_adj Qc_Field test_A)
                                   (mat2_adj Qc_Field test_C)))))
      (mat2_det Qc_Field
         (mat2_add Qc_Field
            (mat2_mul Qc_Field test_A test_C)
            (mat2_neg Qc_Field (mat2_mul Qc_Field test_C test_A)))) =
    cr_add Qc_Field (cr_one Qc_Field) (cr_one Qc_Field).
Proof.
  apply (sl2_lie_group_commutator_sl2 Qc_Field test_A test_C
                                       test_AB_det_A test_AC_det_C).
Qed.

(** Concrete length-6 SL(2)-trace pair witness via test_AB. The smallest
    positive-word trace identity (sl2_smallest_positive_identity_unconditional)
    gives tr(B²·A·B·A²) = tr(B·A·B²·A²) for ANY 2×2 A, B. At (test_A,
    test_B), both equal a specific value, which we verify by vm_compute.

    The two words bbabaa and babbaa are non-conjugate in F_2 (cyclic
    reduction yields different invariant cyclic permutation classes),
    so this pair is a CONCRETE witness blocking property (A) at SL(2)
    over Qc — modulo the F_2 non-conjugacy claim, which is decidable
    but not formalized here. *)

Example sl2_smallest_pair_trace_at_test_AB_LHS :
    mat2_trace Qc_Field
      (mat2_mul Qc_Field (mat2_mul Qc_Field test_B test_B)
        (mat2_mul Qc_Field test_A
          (mat2_mul Qc_Field test_B
            (mat2_mul Qc_Field test_A test_A)))) =
    Q2Qc 222%Q.
Proof. unfold test_A, test_B. vm_compute. reflexivity. Qed.

Example sl2_smallest_pair_trace_at_test_AB_RHS :
    mat2_trace Qc_Field
      (mat2_mul Qc_Field test_B
        (mat2_mul Qc_Field test_A
          (mat2_mul Qc_Field test_B
            (mat2_mul Qc_Field test_B
              (mat2_mul Qc_Field test_A test_A))))) =
    Q2Qc 222%Q.
Proof. unfold test_A, test_B. vm_compute. reflexivity. Qed.

(** Numerical: det([test_A, test_B]_Lie) = 4 in Qc.
    The matrix [A,B]_Lie = AB − BA = [[0,2],[-2,0]] has det = 4. *)
Example sl2_test_AB_lie_commutator_det :
    mat2_det Qc_Field
      (mat2_add Qc_Field
         (mat2_mul Qc_Field test_A test_B)
         (mat2_neg Qc_Field (mat2_mul Qc_Field test_B test_A))) =
    Q2Qc 4%Q.
Proof. unfold test_A, test_B. vm_compute. reflexivity. Qed.

(** The Lie-vs-group commutator identity at test_AB:
    tr([A,B]_group) + det([A,B]_Lie) = (-2) + 4 = 2. *)
Example sl2_test_AB_lie_group_commutator_sum :
    cr_add Qc_Field
      (mat2_trace Qc_Field
         (mat2_mul Qc_Field test_A
            (mat2_mul Qc_Field test_B
               (mat2_mul Qc_Field (mat2_adj Qc_Field test_A)
                                   (mat2_adj Qc_Field test_B)))))
      (mat2_det Qc_Field
         (mat2_add Qc_Field
            (mat2_mul Qc_Field test_A test_B)
            (mat2_neg Qc_Field (mat2_mul Qc_Field test_B test_A)))) =
    cr_add Qc_Field (cr_one Qc_Field) (cr_one Qc_Field).
Proof.
  apply (sl2_lie_group_commutator_sl2 Qc_Field test_A test_B
                                       test_AB_det_A test_AB_det_B).
Qed.
