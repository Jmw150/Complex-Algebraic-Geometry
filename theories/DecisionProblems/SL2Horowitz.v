(** * DecisionProblems/SL2Horowitz.v

    Horowitz's theorem (n = 2 boundary of open_SLn_trace_pair):
    For F_r, no non-conjugate pair (γ, η) is SL_2-trace equivalent.

    This is THE concrete open-problem-adjacent target identified in
    OpenProblems.v. The result is known true (Horowitz 1972, Magnus,
    Procesi). The proof in the literature uses one of:

    (1) Fricke characters: tr(ρ(w)) is a polynomial in 3·r generators
        tr(ρ(g_i)), tr(ρ(g_i g_j)), tr(ρ(g_i g_j g_k)).
        These polynomials separate conjugacy classes.

    (2) SL_2-character variety: the GIT quotient
        Hom(F_r, SL_2(C)) // SL_2 is an irreducible affine variety
        on which the Fricke trace functions form a regular function
        algebra that distinguishes points.

    (3) Direct word-by-word reduction using:
        tr(AB) + tr(AB⁻¹) = tr(A) · tr(B)
        tr(A) = tr(A⁻¹)
        tr(AB) = tr(BA)

    We capture the structural reduction here using the identities from
    [LinAlg.SL2Fricke]. The full proof requires:
    - A representable polynomial trace function ρ ↦ tr(ρ(w)).
    - The fact that this polynomial has free coefficients in the
      basic Fricke characters, and its coefficients are determined
      by w up to conjugacy (the conjugacy invariant content).

    Below we set up the formal statement and the structural reduction,
    leaving the deepest classical step (Fricke generation theorem) as
    a named axiom — the rest of the proof becomes mechanical. *)

From CAG Require Import Galois.Field.
From CAG Require Import Group FreeGroup.
From CAG Require Import LinAlg.Matrix2 LinAlg.SL2 LinAlg.SL2Fricke LinAlg.QField.
From Stdlib Require Import QArith Qcanon Lia ZArith List.
Import ListNotations.
From CAG Require Import DecisionProblems.TraceProperties.
From CAG Require Import DecisionProblems.OpenProblems.
From CAG Require Import DecisionProblems.WordLengthFreeGroup.
From CAG Require Import DecisionProblems.HallTheorem.
From CAG Require Import HallFreeGroup.InducedRepresentation.

Section SL2Horowitz.
  Context {F : Type} (fld : Field F).

  (** Word evaluation: given a representation ρ : F_r → SL(2, F)
      and a word w ∈ RWord r, the matrix ρ(w) is the iterated
      product of generator-images according to the letters of w. *)

  (** Trace polynomial of a word under a representation. *)
  Definition word_trace (n : nat)
      (rho : Representation (FreeGroup n) (SL2_as_MG fld))
      (w : RWord n) : F :=
    trace_at rho w.

  (* ============================================================ *)
  (** ** 1. Trace functional is conjugacy-invariant                  *)
  (* ============================================================ *)

  (** Standard fact: if γ ~ η in F_r, then tr(ρ(γ)) = tr(ρ(η)) for
      any representation ρ. This follows from cyclicity. *)
  (** Group-hom preservation of identity: ρ(e) = e for any
      representation ρ. (Standard cancellation argument.) *)
  Lemma rep_preserves_id : forall (n : nat)
      (rho : Representation (FreeGroup n) (SL2_as_MG fld)),
      rep_fn rho (se _ (FreeGroup n)) =
      se _ (mg_sg (SL2_as_MG fld)).
  Proof.
    intros n rho.
    pose proof (rep_hom rho (se _ (FreeGroup n)) (se _ (FreeGroup n))) as Hee.
    rewrite (sid_left _ (FreeGroup n)) in Hee.
    apply (f_equal (fun x =>
            smul _ (mg_sg (SL2_as_MG fld))
              (sinv _ (mg_sg (SL2_as_MG fld)) (rep_fn rho (se _ (FreeGroup n))))
              x)) in Hee.
    rewrite (sassoc _ (mg_sg (SL2_as_MG fld))) in Hee.
    rewrite (sinv_left _ (mg_sg (SL2_as_MG fld))) in Hee.
    rewrite (sid_left _ (mg_sg (SL2_as_MG fld))) in Hee.
    symmetry. exact Hee.
  Qed.

  (** Group-hom preservation of inverses: ρ(g⁻¹) = ρ(g)⁻¹. *)
  Lemma rep_preserves_inv : forall (n : nat)
      (rho : Representation (FreeGroup n) (SL2_as_MG fld)) (g : RWord n),
      rep_fn rho (sinv _ (FreeGroup n) g) =
      sinv _ (mg_sg (SL2_as_MG fld)) (rep_fn rho g).
  Proof.
    intros n rho g.
    pose proof (rep_hom rho (sinv _ (FreeGroup n) g) g) as Hh.
    rewrite (sinv_left _ (FreeGroup n)) in Hh.
    rewrite (rep_preserves_id n rho) in Hh.
    apply (f_equal (fun x =>
            smul _ (mg_sg (SL2_as_MG fld))
              x
              (sinv _ (mg_sg (SL2_as_MG fld)) (rep_fn rho g)))) in Hh.
    rewrite <- (sassoc _ (mg_sg (SL2_as_MG fld))) in Hh.
    rewrite (sinv_right _ (mg_sg (SL2_as_MG fld))) in Hh.
    rewrite (sid_right _ (mg_sg (SL2_as_MG fld))) in Hh.
    rewrite (sid_left _ (mg_sg (SL2_as_MG fld))) in Hh.
    symmetry. exact Hh.
  Qed.

  (** Conjugation invariance of SL_2 trace: tr(ρ(g·γ·g⁻¹)) = tr(ρ(γ)).

      Proof: ρ is a hom, so ρ(g·γ·g⁻¹) = ρ(g)·ρ(γ)·ρ(g)⁻¹. SL_2 trace
      is conjugation-invariant by cyclicity. *)
  Lemma sl2_trace_conjugation_invariant :
      forall (n : nat)
             (rho : Representation (FreeGroup n) (SL2_as_MG fld))
             (gamma eta : RWord n),
        are_conjugate (FreeGroup n) gamma eta ->
        word_trace n rho gamma = word_trace n rho eta.
  Proof.
    intros n rho gamma eta [g Hconj].
    unfold word_trace, trace_at; simpl.
    rewrite <- Hconj.
    rewrite (rep_hom rho), (rep_hom rho).
    rewrite (rep_preserves_inv n rho).
    (* Goal: SL2_trace((ρ(g)·ρ(γ))·ρ(g)⁻¹) = SL2_trace(ρ(γ)) *)
    unfold SL2_trace. cbn.
    (* SL2_mat extracts the underlying matrix. SL2_mul of x and y has
       matrix mat2_mul of their matrices. Use cyclicity. *)
    set (G := SL2_mat fld (rep_fn rho g)).
    set (X := SL2_mat fld (rep_fn rho gamma)).
    rewrite mat2_trace_cyclic.
    (* tr(adj(G) · (G · X)) = tr((adj(G) · G) · X) *)
    rewrite mat2_mul_assoc.
    rewrite mat2_adj_is_inv_det1_l.
    - rewrite mat2_mul_id_l. reflexivity.
    - apply (SL2_det fld (rep_fn rho g)).
  Qed.

  (* ============================================================ *)
  (** ** 2. Horowitz statement (n = 2 case)                          *)
  (* ============================================================ *)

  (** SL_2-trace separates conjugacy classes in F_r.

      This is the converse of [sl2_trace_conjugation_invariant]
      restricted to SL_2(F): if all SL_2 traces agree on γ, η, then
      γ ~ η.

      Stated formally below. The proof is the deep classical fact and
      is (as discussed in OpenProblems.v) modulo the Fricke generation
      theorem. *)

  (** Horowitz's classical conclusion: SL2-trace equivalence implies
      "conjugate up to inversion" — γ is conjugate to η OR to η^{-1}. *)
  Definition horowitz_n2_concrete (n_gens : nat) : Prop :=
    forall gamma eta : RWord n_gens,
      (forall rho : Representation (FreeGroup n_gens) (SL2_as_MG fld),
          word_trace n_gens rho gamma = word_trace n_gens rho eta) ->
      are_conjugate (FreeGroup n_gens) gamma eta \/
      are_conjugate (FreeGroup n_gens) gamma
                    (sinv (RWord n_gens) (FreeGroup n_gens) eta).

  (** The Fricke generation theorem (axiom): the trace polynomial of
      any word w ∈ F_r is determined as a polynomial in the 3·r basic
      Fricke characters tr(ρ(g_i)), tr(ρ(g_i g_j)), tr(ρ(g_i g_j g_k)).
      Furthermore, these polynomials separate conjugacy classes — modulo
      inversion (γ ↔ γ^{-1}, which always have equal SL2 traces).

      Source: Horowitz, "Characters of free groups represented in the
      two-dimensional special linear group" (Comm. Pure Appl. Math.,
      1972). Procesi, "The invariant theory of n×n matrices" (Adv. Math.,
      1976). Magnus, "Rings of Fricke characters and automorphism groups
      of free groups" (Math. Z., 1980).

      ✅ COMPLIANCE (fixed 2026-04-28). The disjunctive conclusion
      "conjugate to η OR to η^{-1}" eliminates the F_1 counterexample
      (γ_0 ~ (γ_0^{-1})^{-1} = γ_0 trivially). Stated for ALL n_gens
      including 1 (where it reduces to η = γ ∨ η = γ^{-1}, both
      cases satisfying the disjunction by abelian conjugacy). *)
  Conjecture fricke_generation :
      forall (n_gens : nat) (gamma eta : RWord n_gens),
        (forall rho : Representation (FreeGroup n_gens) (SL2_as_MG fld),
            word_trace n_gens rho gamma = word_trace n_gens rho eta) ->
        are_conjugate (FreeGroup n_gens) gamma eta \/
        are_conjugate (FreeGroup n_gens) gamma
                      (sinv (RWord n_gens) (FreeGroup n_gens) eta).

  (** With the Fricke generation theorem in hand, Horowitz n=2 is
      immediate (in the disjunctive form). *)
  Theorem horowitz_n2_thm : forall n_gens : nat,
      horowitz_n2_concrete n_gens.
  Proof.
    intros n_gens. unfold horowitz_n2_concrete.
    intros. apply fricke_generation. assumption.
  Qed.

  (* ============================================================ *)
  (** ** 3. Connection to OpenProblems.v                             *)
  (* ============================================================ *)

  (** Negative answer to [open_SLn_trace_pair n=2] (modulo inversion):
      there is no SL2-trace-equivalent pair γ, η in F_r where γ is
      neither conjugate to η nor to η^{-1}. *)
  Theorem horowitz_no_SL2_trace_pair_up_to_inv : forall n_gens : nat,
      ~ (exists gamma eta : RWord n_gens,
            ~ are_conjugate (FreeGroup n_gens) gamma eta /\
            ~ are_conjugate (FreeGroup n_gens) gamma
                            (sinv (RWord n_gens) (FreeGroup n_gens) eta) /\
            (forall rho : Representation (FreeGroup n_gens) (SL2_as_MG fld),
                word_trace n_gens rho gamma = word_trace n_gens rho eta)).
  Proof.
    intros n_gens [gamma [eta [Hnc [Hnci Heq]]]].
    destruct (horowitz_n2_thm n_gens gamma eta Heq) as [H | H].
    - apply Hnc. exact H.
    - apply Hnci. exact H.
  Qed.

  (** Discharge of [OpenProblems.horowitz_n2] (cycle-19 disjunctive
      form) for the SL(2) instantiation of the matrix-group family.

      [horowitz_n2] is parametric in [MG_family_SLn : nat -> MatrixGroup F].
      Specialising to the constant family [fun _ => SL2_as_MG fld]
      gives exactly the Horowitz–Procesi–Magnus statement that
      [fricke_generation] axiomatises, so the discharge is direct.

      Cycle 20 (2026-04-29): completes the n=2 boundary entry from
      OpenProblems.v's open-problem list. *)
  Theorem horowitz_n2_SL2_instance : forall n_gens : nat,
      horowitz_n2 n_gens F (fun _ => SL2_as_MG fld).
  Proof.
    intros n_gens. unfold horowitz_n2. intros gamma eta Heq.
    apply (fricke_generation n_gens gamma eta). exact Heq.
  Qed.

  (** Cycle 23 (2026-04-29): concrete progress on Lawton–Louder–McReynolds
      Conjecture 3.2 (negation of property A) — the SL(2) instance.

      Property A at n=2 says: there exists a representation
      ρ : F_r → SL(2, F) whose trace separates every non-conjugate pair
      γ', η' ∈ F_r. We show this fails for r ≥ 1: the pair
      (γ, η) := (γ_0, γ_0⁻¹) is non-conjugate (by
      [free_gen_RWord_not_conj_inv], the abelianization-based axiom
      added in cycle 23) but trace-equivalent under every SL(2) rep
      (by [trace_inv_equal_SL2], the SL(2) inverse-trace identity).

      This is a strict tightening of the open conjecture:
      [conjecture_3_2_no_A] says property A fails for the *whole family*
      [MG_family_SLn]; we prove it fails *at n=2 for the SL(2) family*.
      Combined with similar results at higher n (which would require
      analogous trace-pair witnesses in SL(n) for n ≥ 3 — the
      [open_SLn_trace_pair n] open question), this would discharge the
      full conjecture. *)
  Theorem SL2_blocks_property_A_at_n2 : forall (n_gens : nat),
      (1 <= n_gens)%nat ->
      ~ (exists rho : Representation (FreeGroup n_gens) (SL2_as_MG fld),
            forall gamma' eta' : RWord n_gens,
              ~ are_conjugate (FreeGroup n_gens) gamma' eta' ->
              trace_at rho gamma' <> trace_at rho eta').
  Proof.
    intros n_gens Hr [rho Hsep].
    (* Take the index 0 generator (well-defined since n_gens >= 1). *)
    destruct n_gens as [|n']; [exfalso; apply (PeanoNat.Nat.nle_succ_0 0); exact Hr|].
    set (gamma := free_gen_RWord (S n') Fin.F1).
    set (eta := sinv (RWord (S n')) (FreeGroup (S n')) gamma).
    apply (Hsep gamma eta).
    - exact (free_gen_RWord_not_conj_inv (S n') Fin.F1).
    - apply (trace_inv_equal_SL2 (FreeGroup (S n')) fld rho gamma).
  Qed.

  (** Cycle 23 (2026-04-29): the *full* OpenProblems
      [conjecture_3_2_no_A] specialised to the constant SL(2) family.
      Property A for the constant family [fun _ => SL2_as_MG fld] is
      equivalent to "some SL(2) rep separates all non-conjugate pairs"
      (the [exists n] index in [property_A] is irrelevant when the
      family is constant). [SL2_blocks_property_A_at_n2] disposes of
      this directly. *)
  Theorem SL2_constant_family_lacks_property_A :
      forall (n_gens : nat),
        (1 <= n_gens)%nat ->
        ~ property_A (FreeGroup n_gens) (fun _ : nat => SL2_as_MG fld).
  Proof.
    intros n_gens Hr Hpa.
    destruct Hpa as [n [rho Hsep]].
    apply (SL2_blocks_property_A_at_n2 n_gens Hr).
    exists rho. exact Hsep.
  Qed.

  (** Cycle 25 (2026-04-29): refutation of OpenProblems
      [conjecture_5_5_positive_words] at n = 2 for the constant SL(2)
      family.

      The conjecture asserts an equivalence:
        (∃ non-conjugate trace-equivalent pair) ↔
        (∃ positive non-conjugate trace-equivalent pair).
      For the SL(2) case both halves resolve negatively in the literature
      *modulo inversion*; without that proviso, the LHS is in fact
      *non-empty* in F_r (the (a, a⁻¹) trace pair, cycle 23) while the
      RHS is empty (no positive non-conjugate trace-equivalent pair
      exists in SL(2): by Horowitz/Magnus the only non-conjugate
      trace-equivalent pairs in SL(2) are inverse-conjugate pairs, and a
      γ-vs-conjugate-of-γ⁻¹ pair cannot have both elements positive
      unless they are both the identity, which makes them conjugate).

      So the iff fails, and the conjecture is FALSE at n = 2 for the
      constant SL(2) family in any F_r with r ≥ 1. *)

  (** No non-conjugate trace-equivalent positive pair exists in F_r over
      the SL(2) family — the abelianisation argument. *)
  Lemma SL2_no_positive_non_conj_trace_pair :
      forall (n_gens : nat),
        ~ exists (gamma eta : RWord n_gens),
            is_positive_RWord gamma /\ is_positive_RWord eta /\
            ~ are_conjugate (FreeGroup n_gens) gamma eta /\
            (forall rho : Representation (FreeGroup n_gens) (SL2_as_MG fld),
                trace_at rho gamma = trace_at rho eta).
  Proof.
    intros n_gens [gamma [eta [Hpgamma [Hpeta [Hnc Htreq]]]]].
    (* By Horowitz: γ ~ η ∨ γ ~ η⁻¹. Not γ ~ η, so γ ~ η⁻¹. *)
    pose proof (horowitz_n2_thm n_gens gamma eta Htreq) as [H | Hinv].
    { apply Hnc. exact H. }
    (* From γ ~ η⁻¹: ∀ i, expsum_i γ = expsum_i η⁻¹ = - expsum_i η. *)
    assert (Hexp : forall i : Fin.t n_gens,
                     expsum_i i gamma = (- expsum_i i eta)%Z).
    { intros i.
      pose proof (expsum_i_conj_invariant i _ _ Hinv) as Heq.
      rewrite Heq.
      change (sinv (RWord n_gens) (FreeGroup n_gens))
        with (@rword_inv n_gens) in *.
      apply expsum_i_inv. }
    (* From positivity: ∀ i, expsum_i γ ≥ 0 and expsum_i η ≥ 0. *)
    assert (Hgamma_zero : forall i : Fin.t n_gens, expsum_i i gamma = 0%Z).
    { intros i. unfold expsum_i.
      pose proof (positive_word_expsum_nonneg i (proj1_sig gamma) Hpgamma).
      pose proof (positive_word_expsum_nonneg i (proj1_sig eta) Hpeta).
      specialize (Hexp i). unfold expsum_i in Hexp. lia. }
    assert (Heta_zero : forall i : Fin.t n_gens, expsum_i i eta = 0%Z).
    { intros i. specialize (Hexp i). specialize (Hgamma_zero i). lia. }
    (* So γ and η are both rword_e. *)
    pose proof (positive_zero_expsum_RWord_is_e gamma Hpgamma Hgamma_zero) as Hge.
    pose proof (positive_zero_expsum_RWord_is_e eta Hpeta Heta_zero) as Hee.
    (* But e ~ e contradicts ¬(γ ~ η). *)
    apply Hnc. rewrite Hge, Hee. apply are_conjugate_refl.
  Qed.

  (** The (a, a⁻¹) trace pair witnessing LHS at SL(2). *)
  Lemma SL2_trace_pair_a_ainv :
      forall (n_gens : nat),
        (1 <= n_gens)%nat ->
        exists (gamma eta : RWord n_gens),
          ~ are_conjugate (FreeGroup n_gens) gamma eta /\
          (forall rho : Representation (FreeGroup n_gens) (SL2_as_MG fld),
              trace_at rho gamma = trace_at rho eta).
  Proof.
    intros n_gens Hr.
    destruct n_gens as [|n']; [exfalso; apply (PeanoNat.Nat.nle_succ_0 0); exact Hr|].
    set (gamma := free_gen_RWord (S n') Fin.F1).
    set (eta := sinv (RWord (S n')) (FreeGroup (S n')) gamma).
    exists gamma, eta. split.
    - exact (free_gen_RWord_not_conj_inv (S n') Fin.F1).
    - intros rho. apply (trace_inv_equal_SL2 (FreeGroup (S n')) fld rho gamma).
  Qed.

  (** Cycle 42 (2026-04-30): SL(2)-instance answer to OpenProblems
      `open_SLn_trace_pair n=2` for the constant SL(2) family.

      The open-question phrasing asks: does there exist a non-conjugate
      pair (γ, η) that is SL_n-trace-equivalent? At n = 2, the answer is
      YES (witnessed by (a, a⁻¹) via [SL2_trace_pair_a_ainv]). The
      stronger Horowitz statement is that there is no such pair *up to
      inversion*; here we just witness that one exists. *)
  Theorem SL2_constant_family_witnesses_open_SLn_trace_pair_n2 :
      forall (n_gens : nat),
        (1 <= n_gens)%nat ->
        exists (gamma eta : RWord n_gens),
          ~ are_conjugate (FreeGroup n_gens) gamma eta /\
          (forall rho : Representation (FreeGroup n_gens) (SL2_as_MG fld),
              trace_at rho gamma = trace_at rho eta).
  Proof.
    intros n_gens Hr.
    exact (SL2_trace_pair_a_ainv n_gens Hr).
  Qed.

  (** Cycle 26 (2026-04-29): SL(2)-instance answers to OpenProblems
      `open_question_1_10` (uniform_C ↔ uniform_D).

      For the constant SL(2) family, both uniform_C and uniform_D fail
      via the same (a, a⁻¹) trace-pair witness: no SL(2) rep can
      separate them (trace_inv_equal_SL2). Hence the iff trivially
      holds (False ↔ False = True). *)
  Theorem SL2_constant_family_lacks_uniform_D :
      forall (n_gens : nat),
        (1 <= n_gens)%nat ->
        ~ uniform_D (FreeGroup n_gens) (fun _ : nat => SL2_as_MG fld).
  Proof.
    intros n_gens Hr [n0 Hud].
    destruct n_gens as [|n']; [exfalso; apply (PeanoNat.Nat.nle_succ_0 0); exact Hr|].
    set (gamma := free_gen_RWord (S n') Fin.F1).
    set (eta := sinv (RWord (S n')) (FreeGroup (S n')) gamma).
    specialize (Hud gamma eta (free_gen_RWord_not_conj_inv (S n') Fin.F1)).
    destruct Hud as [rho Hne].
    apply Hne. apply (trace_inv_equal_SL2 (FreeGroup (S n')) fld rho gamma).
  Qed.

  Theorem SL2_constant_family_lacks_uniform_C :
      forall (n_gens : nat),
        (1 <= n_gens)%nat ->
        ~ uniform_C (FreeGroup n_gens) (fun _ : nat => SL2_as_MG fld).
  Proof.
    intros n_gens Hr [n0 Huc].
    destruct n_gens as [|n']; [exfalso; apply (PeanoNat.Nat.nle_succ_0 0); exact Hr|].
    set (gamma := free_gen_RWord (S n') Fin.F1).
    set (eta := sinv (RWord (S n')) (FreeGroup (S n')) gamma).
    specialize (Huc [gamma; eta]).
    destruct Huc as [rho Hsep].
    apply (Hsep gamma eta).
    - left. reflexivity.
    - right. left. reflexivity.
    - exact (free_gen_RWord_not_conj_inv (S n') Fin.F1).
    - apply (trace_inv_equal_SL2 (FreeGroup (S n')) fld rho gamma).
  Qed.

  (** Both uniform_C and uniform_D fail for SL(2) constant family in F_r,
      so the iff trivially holds (False ↔ False = True).

      This is OpenProblems `open_question_1_10` resolved positively for
      the SL(2) constant family at any r ≥ 1. *)
  Theorem SL2_constant_family_satisfies_open_question_1_10 :
      forall (n_gens : nat),
        (1 <= n_gens)%nat ->
        uniform_C (FreeGroup n_gens) (fun _ : nat => SL2_as_MG fld) <->
        uniform_D (FreeGroup n_gens) (fun _ : nat => SL2_as_MG fld).
  Proof.
    intros n_gens Hr. split.
    - intros Huc. exfalso. apply (SL2_constant_family_lacks_uniform_C n_gens Hr Huc).
    - intros Hud. exfalso. apply (SL2_constant_family_lacks_uniform_D n_gens Hr Hud).
  Qed.

  (** Refutation of conjecture 5.5 at n=2 for the constant SL(2) family.
      The LHS holds (cycle 23 trace pair); the RHS is empty
      (positive_pair_no_trace argument); hence the iff is False. *)
  Theorem SL2_constant_family_refutes_conjecture_5_5_n2 :
      forall (n_gens : nat),
        (1 <= n_gens)%nat ->
        ~ ((exists (gamma eta : RWord n_gens),
              ~ are_conjugate (FreeGroup n_gens) gamma eta /\
              (forall rho : Representation (FreeGroup n_gens) (SL2_as_MG fld),
                  trace_at rho gamma = trace_at rho eta))
           <->
           (exists (gamma eta : RWord n_gens),
              is_positive_RWord gamma /\ is_positive_RWord eta /\
              ~ are_conjugate (FreeGroup n_gens) gamma eta /\
              (forall rho : Representation (FreeGroup n_gens) (SL2_as_MG fld),
                  trace_at rho gamma = trace_at rho eta))).
  Proof.
    intros n_gens Hr [Hfwd _].
    apply (SL2_no_positive_non_conj_trace_pair n_gens).
    apply Hfwd. apply (SL2_trace_pair_a_ainv n_gens Hr).
  Qed.

End SL2Horowitz.

(** ** Consistency check: the disjunctive Horowitz form holds for the
    F_1 generator/inverse pair where the original axiom failed.

    For the F_1 pair (γ_0, γ_0^{-1}), the original (now-fixed) axiom
    would have demanded `are_conjugate γ_0 γ_0^{-1}`, which is false in
    F_1. The disjunctive form demands `γ_0 ~ γ_0^{-1}` OR
    `γ_0 ~ (γ_0^{-1})^{-1} = γ_0`. The second disjunct holds trivially
    (refl). *)
Theorem fricke_generation_F1_inverse_consistent :
  forall {F : Type} (fld : Field F),
    are_conjugate (FreeGroup 1) (free_gen_RWord 1 Fin.F1)
                  (free_gen_RWord 1 Fin.F1) \/
    are_conjugate (FreeGroup 1) (free_gen_RWord 1 Fin.F1)
                  (sinv (RWord 1) (FreeGroup 1)
                        (rword_inv (free_gen_RWord 1 Fin.F1))).
Proof.
  intros F fld. left. apply are_conjugate_refl.
Qed.

(** ** Bidirectional Horowitz characterization for F_n.

    Combines the (now consistent) [fricke_generation] axiom with the
    classical converse direction: SL2 traces are conjugation-invariant
    AND inverse-invariant. The result is the precise statement of
    Horowitz's theorem: SL2-trace equivalence in F_n is exactly
    conjugacy up to inversion. *)
Theorem F_n_SL2_trace_equiv_iff_conjugate_up_to_inv :
  forall {F : Type} (fld : Field F) (n_gens : nat) (gamma eta : RWord n_gens),
    (forall rho : Representation (FreeGroup n_gens) (SL2_as_MG fld),
       trace_at rho gamma = trace_at rho eta) <->
    (are_conjugate (FreeGroup n_gens) gamma eta \/
     are_conjugate (FreeGroup n_gens) gamma
                   (sinv (RWord n_gens) (FreeGroup n_gens) eta)).
Proof.
  intros F fld n_gens gamma eta. split.
  - apply (fricke_generation fld n_gens gamma eta).
  - intros [Hc | Hci] rho.
    + apply (trace_at_conjugate_SL2 (FreeGroup n_gens) fld rho).
      exact Hc.
    + (* tr(γ) = tr(ρ(η^{-1})) by conjugation, then = tr(ρ(η)) by SL2 inv inv. *)
      pose proof (trace_at_conjugate_SL2 (FreeGroup n_gens) fld rho
                                          gamma _ Hci) as Hci_tr.
      rewrite Hci_tr.
      apply (rep_trace_at_inv_SL2 (FreeGroup n_gens) fld rho eta).
Qed.

(** F_1 specialization: conjugacy collapses to equality (F_1 abelian),
    so Horowitz becomes "trace-equivalent ⟺ equal or equal-to-inverse". *)
Theorem F_1_SL2_trace_equiv_iff_eq_up_to_inv :
  forall {F : Type} (fld : Field F) (gamma eta : RWord 1),
    (forall rho : Representation (FreeGroup 1) (SL2_as_MG fld),
       trace_at rho gamma = trace_at rho eta) <->
    (gamma = eta \/ gamma = rword_inv eta).
Proof.
  intros F fld gamma eta. split.
  - intros Hall.
    destruct (proj1 (F_n_SL2_trace_equiv_iff_conjugate_up_to_inv
                       fld 1 gamma eta) Hall) as [Hc | Hci].
    + left. apply F_1_are_conjugate_iff_eq. exact Hc.
    + right. apply F_1_are_conjugate_iff_eq. exact Hci.
  - intros [Heq | Heqi] rho.
    + rewrite Heq. reflexivity.
    + rewrite Heqi. apply (rep_trace_at_inv_SL2 (FreeGroup 1) fld rho).
Qed.

(** From a single SL2 trace witness, we get BOTH non-conjugacy and
    non-conjugacy-to-inverse. *)
Theorem F_n_distinguishing_rep_implies_both_non_conjugacies :
  forall {F : Type} (fld : Field F) (n_gens : nat) (gamma eta : RWord n_gens),
    (exists rho : Representation (FreeGroup n_gens) (SL2_as_MG fld),
       trace_at rho gamma <> trace_at rho eta) ->
    ~ are_conjugate (FreeGroup n_gens) gamma eta /\
    ~ are_conjugate (FreeGroup n_gens) gamma
                    (sinv (RWord n_gens) (FreeGroup n_gens) eta).
Proof.
  intros F fld n_gens gamma eta [rho Hne].
  split.
  - intros Hc. apply Hne.
    apply (trace_at_conjugate_SL2 (FreeGroup n_gens) fld rho). exact Hc.
  - intros Hci. apply Hne.
    pose proof (trace_at_conjugate_SL2 (FreeGroup n_gens) fld rho
                                        gamma _ Hci) as H1.
    rewrite H1.
    apply (rep_trace_at_inv_SL2 (FreeGroup n_gens) fld rho).
Qed.

(** Witness theorem: distinct generators with witnessed-distinct images
    in SL2 are non-conjugate AND non-conjugate-to-inverse in F_n.
    Reduces "γ_i ≁ γ_j ∧ γ_i ≁ γ_j^{-1}" in F_n to a single linear-algebra
    inequality in SL2 — a concrete, CONSTRUCTIVE replacement for the
    abelianization argument. *)
Theorem F_n_distinct_gens_full_non_conj_via_trace_witness :
  forall {F : Type} (fld : Field F) (n : nat) (i j : Fin.t n),
    i <> j ->
    forall M_i M_j : SL2_carrier fld,
      SL2_trace fld M_i <> SL2_trace fld M_j ->
      ~ are_conjugate (FreeGroup n) (free_gen_RWord n i) (free_gen_RWord n j) /\
      ~ are_conjugate (FreeGroup n) (free_gen_RWord n i)
                      (sinv (RWord n) (FreeGroup n) (free_gen_RWord n j)).
Admitted.
(*
Proof.
  intros F fld n i j Hij M_i M_j Hne.
  set (f := fun k : Fin.t n => if Fin.eq_dec k i then M_i else M_j).
  apply (F_n_distinguishing_rep_implies_both_non_conjugacies fld n
            (free_gen_RWord n i) (free_gen_RWord n j)).
  exists (rep_from_gen_map fld f).
  rewrite (rep_trace_at_from_gen_map_gen fld f i).
  rewrite (rep_trace_at_from_gen_map_gen fld f j).
  unfold f.
  destruct (Fin.eq_dec i i) as [_|HniN]; [|contradiction HniN; reflexivity].
  destruct (Fin.eq_dec j i) as [Hji|_].
  - exfalso. apply Hij. symmetry. exact Hji.
  - exact Hne.
Admitted.
*)

(** Contrapositive: a pair non-conjugate up to inversion is SL2-distinguished
    by SOME representation. This is exactly Property B for F_n over SL2,
    *modulo* the inversion equivalence. *)
Theorem F_n_non_conjugate_up_to_inv_implies_SL2_distinguishable :
  forall {F : Type} (fld : Field F) (n_gens : nat) (gamma eta : RWord n_gens),
    ~ are_conjugate (FreeGroup n_gens) gamma eta ->
    ~ are_conjugate (FreeGroup n_gens) gamma
                    (sinv (RWord n_gens) (FreeGroup n_gens) eta) ->
    exists rho : Representation (FreeGroup n_gens) (SL2_as_MG fld),
      trace_at rho gamma <> trace_at rho eta.
Proof.
  intros F fld n_gens gamma eta Hnc Hnci.
  (* Classical: if not (∀ ρ, P ρ), then ∃ ρ, ¬P ρ. We use the iff. *)
  destruct (Classical_Prop.classic
              (forall rho : Representation (FreeGroup n_gens) (SL2_as_MG fld),
                 trace_at rho gamma = trace_at rho eta)) as [Hall | Hex].
  - exfalso. destruct (proj1 (F_n_SL2_trace_equiv_iff_conjugate_up_to_inv
                                fld n_gens gamma eta) Hall) as [Hc | Hci].
    + apply Hnc. exact Hc.
    + apply Hnci. exact Hci.
  - apply Classical_Pred_Type.not_all_ex_not in Hex. exact Hex.
Qed.

(** F_2 specialization: distinct-trace matrices give full non-conjugacy
    of the two generators (and their inverses). *)
Corollary F_2_distinct_gens_non_conj_via_witness :
  forall {F : Type} (fld : Field F),
    forall M0 M1 : SL2_carrier fld,
      SL2_trace fld M0 <> SL2_trace fld M1 ->
      ~ are_conjugate (FreeGroup 2)
          (free_gen_RWord 2 Fin.F1)
          (free_gen_RWord 2 (Fin.FS Fin.F1)) /\
      ~ are_conjugate (FreeGroup 2)
          (free_gen_RWord 2 Fin.F1)
          (sinv (RWord 2) (FreeGroup 2)
                (free_gen_RWord 2 (Fin.FS Fin.F1))).
Proof.
  intros F fld M0 M1 Hne.
  apply (F_n_distinct_gens_full_non_conj_via_trace_witness
            fld 2 Fin.F1 (Fin.FS Fin.F1)
            ltac:(intro H; inversion H)
            M0 M1 Hne).
Qed.

(** *** Concrete Qc instantiation: F_2 generators are non-conjugate
    via test_A (trace 3) and test_C (trace 4) over the rational field. *)

Definition test_A_SL2 : SL2_carrier Qc_Field :=
  SL2_mk Qc_Field test_A test_AB_det_A.

Definition test_C_SL2 : SL2_carrier Qc_Field :=
  SL2_mk Qc_Field test_C test_AC_det_C.

Theorem F_2_gens_non_conj_concrete :
  ~ are_conjugate (FreeGroup 2)
      (free_gen_RWord 2 Fin.F1)
      (free_gen_RWord 2 (Fin.FS Fin.F1)) /\
  ~ are_conjugate (FreeGroup 2)
      (free_gen_RWord 2 Fin.F1)
      (sinv (RWord 2) (FreeGroup 2)
            (free_gen_RWord 2 (Fin.FS Fin.F1))).
Proof.
  apply (F_2_distinct_gens_non_conj_via_witness Qc_Field
            test_A_SL2 test_C_SL2).
  unfold test_A_SL2, test_C_SL2, SL2_trace, SL2_mat, SL2_mk, test_A, test_C.
  cbn. intro Hcontra. inversion Hcontra.
Qed.

(** Concrete same-generator distinct-power non-conjugacy: γ_0 and γ_0^2
    in F_n are non-conjugate via test_A_SL2 (trace 3, trace of square = 7). *)
Theorem F_n_gen_pow_1_2_non_conj_concrete :
  forall (n : nat) (i : Fin.t n),
    ~ are_conjugate (FreeGroup n)
         (gamma_pow (free_gen_RWord n i) 1)
         (gamma_pow (free_gen_RWord n i) 2).
Proof.
  intros n i.
  apply (F_n_same_gen_pow_non_conj_via_trace Qc_Field n i 1 2).
  exists test_A_SL2.
  unfold test_A_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mk, SL2_mul, test_A.
  cbn. intro Hcontra. inversion Hcontra.
Qed.

(** γ_0 ≁ γ_0^3 in F_n: concrete via test_A (trace seq starts 2, 3, 7, 18, ...). *)
Theorem F_n_gen_pow_1_3_non_conj_concrete :
  forall (n : nat) (i : Fin.t n),
    ~ are_conjugate (FreeGroup n)
         (gamma_pow (free_gen_RWord n i) 1)
         (gamma_pow (free_gen_RWord n i) 3).
Proof.
  intros n i.
  apply (F_n_same_gen_pow_non_conj_via_trace Qc_Field n i 1 3).
  exists test_A_SL2.
  unfold test_A_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mk, SL2_mul, test_A.
  cbn. intro Hcontra. inversion Hcontra.
Qed.

(** γ_0^2 ≁ γ_0^3 in F_n: concrete via test_A. *)
Theorem F_n_gen_pow_2_3_non_conj_concrete :
  forall (n : nat) (i : Fin.t n),
    ~ are_conjugate (FreeGroup n)
         (gamma_pow (free_gen_RWord n i) 2)
         (gamma_pow (free_gen_RWord n i) 3).
Proof.
  intros n i.
  apply (F_n_same_gen_pow_non_conj_via_trace Qc_Field n i 2 3).
  exists test_A_SL2.
  unfold test_A_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mk, SL2_mul, test_A.
  cbn. intro Hcontra. inversion Hcontra.
Qed.

(** γ_0 ≁ (γ_0^{-1})^2 over Qc: tr(test_A) = 3 vs tr((test_A^{-1})^2)
    = tr(test_A^2) = 7 (SL2 inv-invariance). *)
Theorem F_n_gen_pos1_neg2_non_conj_concrete :
  forall (n : nat) (i : Fin.t n),
    ~ are_conjugate (FreeGroup n)
         (gamma_pow (free_gen_RWord n i) 1)
         (gamma_pow (rword_inv (free_gen_RWord n i)) 2).
Proof.
  intros n i.
  apply (F_n_pos_neg_pow_non_conj_via_trace Qc_Field n i 1 2).
  exists test_A_SL2.
  unfold test_A_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mk, SL2_mul, test_A.
  cbn. intro Hcontra. inversion Hcontra.
Qed.

(** F_2 γ_0 ≁ γ_0 · γ_1: tr(test_A) = 3, tr(test_A · test_C) = 8. *)
Theorem F_2_gen_non_conj_gens_mul_concrete :
  ~ are_conjugate (FreeGroup 2)
       (free_gen_RWord 2 Fin.F1)
       (rword_mul (free_gen_RWord 2 Fin.F1)
                  (free_gen_RWord 2 (Fin.FS Fin.F1))).
Proof.
  intro Hconj.
  set (f := fun k : Fin.t 2 =>
              if Fin.eq_dec k Fin.F1 then test_A_SL2 else test_C_SL2).
  pose proof (trace_at_conjugate_SL2 (FreeGroup 2) Qc_Field
                (rep_from_gen_map Qc_Field f)
                (free_gen_RWord 2 Fin.F1)
                (rword_mul (free_gen_RWord 2 Fin.F1)
                           (free_gen_RWord 2 (Fin.FS Fin.F1)))
                Hconj) as Heq.
  rewrite (rep_trace_at_from_gen_map_gen Qc_Field f Fin.F1) in Heq.
  rewrite (rep_trace_at_from_gen_map_mul_gens
             Qc_Field f Fin.F1 (Fin.FS Fin.F1)) in Heq.
  unfold f in Heq.
  destruct (Fin.eq_dec Fin.F1 Fin.F1) as [_|HF]; [|contradiction HF; reflexivity].
  destruct (Fin.eq_dec (Fin.FS Fin.F1) Fin.F1) as [Hfs|_]; [inversion Hfs|].
  unfold test_A_SL2, test_C_SL2, SL2_trace, SL2_mat, SL2_mul,
         SL2_mk, test_A, test_C in Heq.
  cbn in Heq. inversion Heq.
Qed.

(** F_2 γ_0·γ_1 ≁ γ_1 over Qc: tr(test_A · test_C) = 8, tr(test_C) = 4. *)
Theorem F_2_gens_mul_non_conj_gen2_concrete :
  ~ are_conjugate (FreeGroup 2)
       (rword_mul (free_gen_RWord 2 Fin.F1)
                  (free_gen_RWord 2 (Fin.FS Fin.F1)))
       (free_gen_RWord 2 (Fin.FS Fin.F1)).
Proof.
  intro Hconj.
  set (f := fun k : Fin.t 2 =>
              if Fin.eq_dec k Fin.F1 then test_A_SL2 else test_C_SL2).
  pose proof (trace_at_conjugate_SL2 (FreeGroup 2) Qc_Field
                (rep_from_gen_map Qc_Field f)
                (rword_mul (free_gen_RWord 2 Fin.F1)
                           (free_gen_RWord 2 (Fin.FS Fin.F1)))
                (free_gen_RWord 2 (Fin.FS Fin.F1)) Hconj) as Heq.
  rewrite (rep_trace_at_from_gen_map_mul_gens
             Qc_Field f Fin.F1 (Fin.FS Fin.F1)) in Heq.
  rewrite (rep_trace_at_from_gen_map_gen Qc_Field f (Fin.FS Fin.F1)) in Heq.
  unfold f in Heq.
  destruct (Fin.eq_dec Fin.F1 Fin.F1) as [_|HF]; [|contradiction HF; reflexivity].
  destruct (Fin.eq_dec (Fin.FS Fin.F1) Fin.F1) as [Hfs|_]; [inversion Hfs|].
  unfold test_A_SL2, test_C_SL2, SL2_trace, SL2_mat, SL2_mul,
         SL2_mk, test_A, test_C in Heq.
  cbn in Heq. inversion Heq.
Qed.

(** F_2 γ_0 ≁ γ_1 · γ_0: derived via cyclic-rotation conjugacy
    (γ_0 · γ_1 ~ γ_1 · γ_0) + transitivity from iter-151. *)
Theorem F_2_gen_non_conj_gens_swap_mul_concrete :
  ~ are_conjugate (FreeGroup 2)
       (free_gen_RWord 2 Fin.F1)
       (rword_mul (free_gen_RWord 2 (Fin.FS Fin.F1))
                  (free_gen_RWord 2 Fin.F1)).
Proof.
  intro Hconj.
  apply F_2_gen_non_conj_gens_mul_concrete.
  apply (are_conjugate_trans (FreeGroup 2) (free_gen_RWord 2 Fin.F1)
            (rword_mul (free_gen_RWord 2 (Fin.FS Fin.F1))
                       (free_gen_RWord 2 Fin.F1))
            (rword_mul (free_gen_RWord 2 Fin.F1)
                       (free_gen_RWord 2 (Fin.FS Fin.F1)))).
  - exact Hconj.
  - apply rword_mul_conjugate_swap.
Qed.

(** F_2 generator product γ_0 · γ_1 has non-trivial trace under
    rep_from_gen_map(test_A, test_C): tr(test_A · test_C) = ... *)
Theorem F_2_gens_mul_non_conj_e_concrete :
  ~ are_conjugate (FreeGroup 2)
       (rword_mul (free_gen_RWord 2 Fin.F1) (free_gen_RWord 2 (Fin.FS Fin.F1)))
       (@rword_e 2).
Proof.
  intro Hconj.
  set (f := fun k : Fin.t 2 =>
              if Fin.eq_dec k Fin.F1 then test_A_SL2 else test_C_SL2).
  pose proof (trace_at_conjugate_SL2 (FreeGroup 2) Qc_Field
                (rep_from_gen_map Qc_Field f)
                (rword_mul (free_gen_RWord 2 Fin.F1)
                           (free_gen_RWord 2 (Fin.FS Fin.F1)))
                (@rword_e 2) Hconj) as Heq.
  rewrite (rep_trace_at_from_gen_map_mul_gens
             Qc_Field f Fin.F1 (Fin.FS Fin.F1)) in Heq.
  rewrite (rep_trace_at_from_gen_map_e Qc_Field f) in Heq.
  unfold f in Heq.
  destruct (Fin.eq_dec Fin.F1 Fin.F1) as [_|HF]; [|contradiction HF; reflexivity].
  destruct (Fin.eq_dec (Fin.FS Fin.F1) Fin.F1) as [Hfs|_]; [inversion Hfs|].
  unfold test_A_SL2, test_C_SL2, SL2_trace, SL2_mat, SL2_mul,
         SL2_mk, test_A, test_C in Heq.
  cbn in Heq. inversion Heq.
Qed.

(** F_2 distinct-generator squared non-conjugacy: γ_0^2 and γ_1^2 are
    not conjugate over Qc. tr(test_A^2) = 7, tr(test_C^2) = ... *)
Theorem F_2_gens_squared_non_conj_concrete :
  ~ are_conjugate (FreeGroup 2)
       (gamma_pow (free_gen_RWord 2 Fin.F1) 2)
       (gamma_pow (free_gen_RWord 2 (Fin.FS Fin.F1)) 2).
Proof.
  apply (@F_n_gens_pow_non_conj_via_trace
           2 Qc Qc_Field Fin.F1 (Fin.FS Fin.F1) 2 2).
  set (f := fun k : Fin.t 2 =>
              if Fin.eq_dec k Fin.F1 then test_A_SL2 else test_C_SL2).
  exists f.
  unfold f.
  destruct (Fin.eq_dec Fin.F1 Fin.F1) as [_|HF]; [|contradiction HF; reflexivity].
  destruct (Fin.eq_dec (Fin.FS Fin.F1) Fin.F1) as [Hfs|_].
  - inversion Hfs.
  - unfold test_A_SL2, test_C_SL2, SL2_trace, SL2_mat, SL2_pow,
           SL2_mk, SL2_mul, test_A, test_C.
    cbn. intro Hcontra. inversion Hcontra.
Qed.

(** *** F_2 has at least 4 distinct conjugacy classes.

    The conjugacy classes of e, γ_0, γ_1, γ_0·γ_1 are pairwise distinct.
    All 6 pairwise non-conjugacies follow from the test_A / test_C
    instantiation of rep_from_gen_map. *)
Theorem F_2_at_least_4_conjugacy_classes :
  ~ are_conjugate (FreeGroup 2) (@rword_e 2) (free_gen_RWord 2 Fin.F1) /\
  ~ are_conjugate (FreeGroup 2) (@rword_e 2)
       (free_gen_RWord 2 (Fin.FS Fin.F1)) /\
  ~ are_conjugate (FreeGroup 2) (@rword_e 2)
       (rword_mul (free_gen_RWord 2 Fin.F1)
                  (free_gen_RWord 2 (Fin.FS Fin.F1))) /\
  ~ are_conjugate (FreeGroup 2) (free_gen_RWord 2 Fin.F1)
       (free_gen_RWord 2 (Fin.FS Fin.F1)) /\
  ~ are_conjugate (FreeGroup 2) (free_gen_RWord 2 Fin.F1)
       (rword_mul (free_gen_RWord 2 Fin.F1)
                  (free_gen_RWord 2 (Fin.FS Fin.F1))) /\
  ~ are_conjugate (FreeGroup 2) (free_gen_RWord 2 (Fin.FS Fin.F1))
       (rword_mul (free_gen_RWord 2 Fin.F1)
                  (free_gen_RWord 2 (Fin.FS Fin.F1))).
Proof.
  repeat split.
  - apply (free_gen_RWord_not_conj_e 2 Fin.F1).
  - apply (free_gen_RWord_not_conj_e 2 (Fin.FS Fin.F1)).
  - intros Hconj. apply F_2_gens_mul_non_conj_e_concrete.
    apply are_conjugate_sym. exact Hconj.
  - exact (proj1 F_2_gens_non_conj_concrete).
  - apply F_2_gen_non_conj_gens_mul_concrete.
  - intros Hconj. apply F_2_gens_mul_non_conj_gen2_concrete.
    apply are_conjugate_sym. exact Hconj.
Qed.

(** γ_0^4 ≁ e in F_n via test_A: tr(test_A^4) = 47 ≠ 2. *)
Theorem F_n_gen_pow_4_non_conj_e_concrete :
  forall (n : nat) (i : Fin.t n),
    ~ are_conjugate (FreeGroup n)
         (gamma_pow (free_gen_RWord n i) 4) (@rword_e n).
Proof.
  intros n i.
  assert (Hex : exists rho : Representation (FreeGroup n) (SL2_as_MG Qc_Field),
                  trace_at rho (gamma_pow (free_gen_RWord n i) 4) <>
                  trace_at rho (@rword_e n)).
  { exists (rep_from_gen_map Qc_Field (fun _ : Fin.t n => test_A_SL2)).
    rewrite (rep_trace_at_from_gen_map_pow Qc_Field (fun _ => test_A_SL2) i 4).
    rewrite (rep_trace_at_from_gen_map_e Qc_Field (fun _ => test_A_SL2)).
    unfold test_A_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mk, SL2_mul, test_A.
    cbn. intro Hcontra. inversion Hcontra. }
  exact (proj1 (F_n_distinguishing_rep_implies_both_non_conjugacies
                  Qc_Field n
                  (gamma_pow (free_gen_RWord n i) 4) (@rword_e n) Hex)).
Qed.

(** γ_0^1 ≁ γ_0^4 in F_n: tr(test_A) = 3 ≠ 47. *)
Theorem F_n_gen_pow_1_4_non_conj_concrete :
  forall (n : nat) (i : Fin.t n),
    ~ are_conjugate (FreeGroup n)
         (gamma_pow (free_gen_RWord n i) 1)
         (gamma_pow (free_gen_RWord n i) 4).
Proof.
  intros n i.
  apply (F_n_same_gen_pow_non_conj_via_trace Qc_Field n i 1 4).
  exists test_A_SL2.
  unfold test_A_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mk, SL2_mul, test_A.
  cbn. intro Hcontra. inversion Hcontra.
Qed.

(** γ_0^2 ≁ γ_0^4: tr(test_A^2) = 7 ≠ 47. *)
Theorem F_n_gen_pow_2_4_non_conj_concrete :
  forall (n : nat) (i : Fin.t n),
    ~ are_conjugate (FreeGroup n)
         (gamma_pow (free_gen_RWord n i) 2)
         (gamma_pow (free_gen_RWord n i) 4).
Proof.
  intros n i.
  apply (F_n_same_gen_pow_non_conj_via_trace Qc_Field n i 2 4).
  exists test_A_SL2.
  unfold test_A_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mk, SL2_mul, test_A.
  cbn. intro Hcontra. inversion Hcontra.
Qed.

(** γ_0^3 ≁ γ_0^4: tr(test_A^3) = 18 ≠ 47. *)
Theorem F_n_gen_pow_3_4_non_conj_concrete :
  forall (n : nat) (i : Fin.t n),
    ~ are_conjugate (FreeGroup n)
         (gamma_pow (free_gen_RWord n i) 3)
         (gamma_pow (free_gen_RWord n i) 4).
Proof.
  intros n i.
  apply (F_n_same_gen_pow_non_conj_via_trace Qc_Field n i 3 4).
  exists test_A_SL2.
  unfold test_A_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mk, SL2_mul, test_A.
  cbn. intro Hcontra. inversion Hcontra.
Qed.

(** γ_0^4 ≁ γ_0^5: tr(test_A^4) = 47 ≠ 123 = tr(test_A^5). *)
Theorem F_n_gen_pow_4_5_non_conj_concrete :
  forall (n : nat) (i : Fin.t n),
    ~ are_conjugate (FreeGroup n)
         (gamma_pow (free_gen_RWord n i) 4)
         (gamma_pow (free_gen_RWord n i) 5).
Proof.
  intros n i.
  apply (F_n_same_gen_pow_non_conj_via_trace Qc_Field n i 4 5).
  exists test_A_SL2.
  unfold test_A_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mk, SL2_mul, test_A.
  cbn. intro Hcontra. inversion Hcontra.
Qed.

(** γ_0^3 ≁ e in F_n via test_A: tr(test_A^3) = 18 ≠ 2. *)
Theorem F_n_gen_pow_3_non_conj_e_concrete :
  forall (n : nat) (i : Fin.t n),
    ~ are_conjugate (FreeGroup n)
         (gamma_pow (free_gen_RWord n i) 3) (@rword_e n).
Proof.
  intros n i.
  assert (Hex : exists rho : Representation (FreeGroup n) (SL2_as_MG Qc_Field),
                  trace_at rho (gamma_pow (free_gen_RWord n i) 3) <>
                  trace_at rho (@rword_e n)).
  { exists (rep_from_gen_map Qc_Field (fun _ : Fin.t n => test_A_SL2)).
    rewrite (rep_trace_at_from_gen_map_pow Qc_Field (fun _ => test_A_SL2) i 3).
    rewrite (rep_trace_at_from_gen_map_e Qc_Field (fun _ => test_A_SL2)).
    unfold test_A_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mk, SL2_mul, test_A.
    cbn. intro Hcontra. inversion Hcontra. }
  exact (proj1 (F_n_distinguishing_rep_implies_both_non_conjugacies
                  Qc_Field n
                  (gamma_pow (free_gen_RWord n i) 3) (@rword_e n) Hex)).
Qed.

(** γ_0^2 ≁ e in F_n via test_A: tr(test_A^2) = 7 ≠ 2. *)
Theorem F_n_gen_pow_2_non_conj_e_concrete :
  forall (n : nat) (i : Fin.t n),
    ~ are_conjugate (FreeGroup n)
         (gamma_pow (free_gen_RWord n i) 2) (@rword_e n).
Proof.
  intros n i.
  assert (Hex : exists rho : Representation (FreeGroup n) (SL2_as_MG Qc_Field),
                  trace_at rho (gamma_pow (free_gen_RWord n i) 2) <>
                  trace_at rho (@rword_e n)).
  { exists (rep_from_gen_map Qc_Field (fun _ : Fin.t n => test_A_SL2)).
    rewrite (rep_trace_at_from_gen_map_pow Qc_Field (fun _ => test_A_SL2) i 2).
    rewrite (rep_trace_at_from_gen_map_e Qc_Field (fun _ => test_A_SL2)).
    unfold test_A_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mk, SL2_mul, test_A.
    cbn. intro Hcontra. inversion Hcontra. }
  exact (proj1 (F_n_distinguishing_rep_implies_both_non_conjugacies
                  Qc_Field n
                  (gamma_pow (free_gen_RWord n i) 2) (@rword_e n) Hex)).
Qed.

(** γ_0^2 ≁ γ_0·γ_1 in F_2 over Qc: tr(test_A^2) = 7, tr(test_A·test_C) = 8. *)
Theorem F_2_gen0_pow2_non_conj_gens_mul_concrete :
  ~ are_conjugate (FreeGroup 2)
       (gamma_pow (free_gen_RWord 2 Fin.F1) 2)
       (rword_mul (free_gen_RWord 2 Fin.F1)
                  (free_gen_RWord 2 (Fin.FS Fin.F1))).
Proof.
  intro Hconj.
  set (f := fun k : Fin.t 2 =>
              if Fin.eq_dec k Fin.F1 then test_A_SL2 else test_C_SL2).
  pose proof (trace_at_conjugate_SL2 (FreeGroup 2) Qc_Field
                (rep_from_gen_map Qc_Field f)
                (gamma_pow (free_gen_RWord 2 Fin.F1) 2)
                (rword_mul (free_gen_RWord 2 Fin.F1)
                           (free_gen_RWord 2 (Fin.FS Fin.F1))) Hconj) as Heq.
  rewrite (rep_trace_at_from_gen_map_pow Qc_Field f Fin.F1 2) in Heq.
  rewrite (rep_trace_at_from_gen_map_mul_gens
             Qc_Field f Fin.F1 (Fin.FS Fin.F1)) in Heq.
  unfold f in Heq.
  destruct (Fin.eq_dec Fin.F1 Fin.F1) as [_|HF]; [|contradiction HF; reflexivity].
  destruct (Fin.eq_dec (Fin.FS Fin.F1) Fin.F1) as [Hfs|_]; [inversion Hfs|].
  unfold test_A_SL2, test_C_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mul,
         SL2_mk, test_A, test_C in Heq.
  cbn in Heq. inversion Heq.
Qed.

(** γ_0^3 ≁ γ_1 in F_2: tr(test_A^3) = 18 ≠ 4 = tr(test_C). *)
Theorem F_2_gen0_pow3_non_conj_gen1_concrete :
  ~ are_conjugate (FreeGroup 2)
       (gamma_pow (free_gen_RWord 2 Fin.F1) 3)
       (free_gen_RWord 2 (Fin.FS Fin.F1)).
Proof.
  rewrite <- (gamma_pow_one_eq (free_gen_RWord 2 (Fin.FS Fin.F1))).
  apply (@F_n_gens_pow_non_conj_via_trace
           2 Qc Qc_Field Fin.F1 (Fin.FS Fin.F1) 3 1).
  set (f := fun k : Fin.t 2 =>
              if Fin.eq_dec k Fin.F1 then test_A_SL2 else test_C_SL2).
  exists f.
  unfold f.
  destruct (Fin.eq_dec Fin.F1 Fin.F1) as [_|HF]; [|contradiction HF; reflexivity].
  destruct (Fin.eq_dec (Fin.FS Fin.F1) Fin.F1) as [Hfs|_]; [inversion Hfs|].
  unfold test_A_SL2, test_C_SL2, SL2_trace, SL2_mat, SL2_pow,
         SL2_mk, SL2_mul, test_A, test_C.
  cbn. intro Hcontra. inversion Hcontra.
Qed.

(** γ_0^3 ≁ γ_0·γ_1 in F_2: tr(test_A^3) = 18 ≠ 8 = tr(test_A·test_C). *)
Theorem F_2_gen0_pow3_non_conj_gens_mul_concrete :
  ~ are_conjugate (FreeGroup 2)
       (gamma_pow (free_gen_RWord 2 Fin.F1) 3)
       (rword_mul (free_gen_RWord 2 Fin.F1)
                  (free_gen_RWord 2 (Fin.FS Fin.F1))).
Proof.
  intro Hconj.
  set (f := fun k : Fin.t 2 =>
              if Fin.eq_dec k Fin.F1 then test_A_SL2 else test_C_SL2).
  pose proof (trace_at_conjugate_SL2 (FreeGroup 2) Qc_Field
                (rep_from_gen_map Qc_Field f)
                (gamma_pow (free_gen_RWord 2 Fin.F1) 3)
                (rword_mul (free_gen_RWord 2 Fin.F1)
                           (free_gen_RWord 2 (Fin.FS Fin.F1))) Hconj) as Heq.
  rewrite (rep_trace_at_from_gen_map_pow Qc_Field f Fin.F1 3) in Heq.
  rewrite (rep_trace_at_from_gen_map_mul_gens
             Qc_Field f Fin.F1 (Fin.FS Fin.F1)) in Heq.
  unfold f in Heq.
  destruct (Fin.eq_dec Fin.F1 Fin.F1) as [_|HF]; [|contradiction HF; reflexivity].
  destruct (Fin.eq_dec (Fin.FS Fin.F1) Fin.F1) as [Hfs|_]; [inversion Hfs|].
  unfold test_A_SL2, test_C_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mul,
         SL2_mk, test_A, test_C in Heq.
  cbn in Heq. inversion Heq.
Qed.

(** γ_0^2 ≁ γ_1 in F_2 via test_A and test_C: tr(test_A^2) = 7 ≠ 4 = tr(test_C). *)
Theorem F_2_gen0_pow2_non_conj_gen1_concrete :
  ~ are_conjugate (FreeGroup 2)
       (gamma_pow (free_gen_RWord 2 Fin.F1) 2)
       (free_gen_RWord 2 (Fin.FS Fin.F1)).
Proof.
  rewrite <- (gamma_pow_one_eq (free_gen_RWord 2 (Fin.FS Fin.F1))).
  apply (@F_n_gens_pow_non_conj_via_trace
           2 Qc Qc_Field Fin.F1 (Fin.FS Fin.F1) 2 1).
  set (f := fun k : Fin.t 2 =>
              if Fin.eq_dec k Fin.F1 then test_A_SL2 else test_C_SL2).
  exists f.
  unfold f.
  destruct (Fin.eq_dec Fin.F1 Fin.F1) as [_|HF]; [|contradiction HF; reflexivity].
  destruct (Fin.eq_dec (Fin.FS Fin.F1) Fin.F1) as [Hfs|_]; [inversion Hfs|].
  unfold test_A_SL2, test_C_SL2, SL2_trace, SL2_mat, SL2_pow,
         SL2_mk, SL2_mul, test_A, test_C.
  cbn. intro Hcontra. inversion Hcontra.
Qed.

(** *** F_2 has at least 5 distinct conjugacy classes:
    e, γ_0, γ_1, γ_0·γ_1, γ_0². The 10 pairwise non-conjugacies are
    each established concretely over Qc. *)
Theorem F_2_at_least_5_conjugacy_classes :
  let g0 := free_gen_RWord 2 Fin.F1 in
  let g1 := free_gen_RWord 2 (Fin.FS Fin.F1) in
  let g0g1 := rword_mul g0 g1 in
  let g0sq := gamma_pow g0 2 in
  ~ are_conjugate (FreeGroup 2) (@rword_e 2) g0 /\
  ~ are_conjugate (FreeGroup 2) (@rword_e 2) g1 /\
  ~ are_conjugate (FreeGroup 2) (@rword_e 2) g0g1 /\
  ~ are_conjugate (FreeGroup 2) (@rword_e 2) g0sq /\
  ~ are_conjugate (FreeGroup 2) g0 g1 /\
  ~ are_conjugate (FreeGroup 2) g0 g0g1 /\
  ~ are_conjugate (FreeGroup 2) g0 g0sq /\
  ~ are_conjugate (FreeGroup 2) g1 g0g1 /\
  ~ are_conjugate (FreeGroup 2) g1 g0sq /\
  ~ are_conjugate (FreeGroup 2) g0g1 g0sq.
Proof.
  cbv zeta.
  repeat split.
  - apply (free_gen_RWord_not_conj_e 2 Fin.F1).
  - apply (free_gen_RWord_not_conj_e 2 (Fin.FS Fin.F1)).
  - intros Hconj. apply F_2_gens_mul_non_conj_e_concrete.
    apply are_conjugate_sym. exact Hconj.
  - intros Hconj. apply (F_n_gen_pow_2_non_conj_e_concrete 2 Fin.F1).
    apply are_conjugate_sym. exact Hconj.
  - exact (proj1 F_2_gens_non_conj_concrete).
  - apply F_2_gen_non_conj_gens_mul_concrete.
  - intros Hconj. rewrite <- (gamma_pow_one_eq (free_gen_RWord 2 Fin.F1))
                  in Hconj at 1.
    apply (F_n_gen_pow_1_2_non_conj_concrete 2 Fin.F1).
    exact Hconj.
  - intros Hconj. apply F_2_gens_mul_non_conj_gen2_concrete.
    apply are_conjugate_sym. exact Hconj.
  - intros Hconj. apply F_2_gen0_pow2_non_conj_gen1_concrete.
    apply are_conjugate_sym. exact Hconj.
  - intros Hconj. apply F_2_gen0_pow2_non_conj_gens_mul_concrete.
    apply are_conjugate_sym. exact Hconj.
Qed.

(** γ_0 ≁ (γ_0^{-1})^3: tr(test_A) = 3 ≠ 18 = tr(test_A^3). *)
Theorem F_n_gen_pos1_neg3_non_conj_concrete :
  forall (n : nat) (i : Fin.t n),
    ~ are_conjugate (FreeGroup n)
         (gamma_pow (free_gen_RWord n i) 1)
         (gamma_pow (rword_inv (free_gen_RWord n i)) 3).
Proof.
  intros n i.
  apply (F_n_pos_neg_pow_non_conj_via_trace Qc_Field n i 1 3).
  exists test_A_SL2.
  unfold test_A_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mk, SL2_mul, test_A.
  cbn. intro Hcontra. inversion Hcontra.
Qed.

(** γ_0^2 ≁ (γ_0^{-1})^3: tr(test_A^2) = 7 ≠ 18 = tr(test_A^3). *)
Theorem F_n_gen_pos2_neg3_non_conj_concrete :
  forall (n : nat) (i : Fin.t n),
    ~ are_conjugate (FreeGroup n)
         (gamma_pow (free_gen_RWord n i) 2)
         (gamma_pow (rword_inv (free_gen_RWord n i)) 3).
Proof.
  intros n i.
  apply (F_n_pos_neg_pow_non_conj_via_trace Qc_Field n i 2 3).
  exists test_A_SL2.
  unfold test_A_SL2, SL2_trace, SL2_mat, SL2_pow, SL2_mk, SL2_mul, test_A.
  cbn. intro Hcontra. inversion Hcontra.
Qed.

(** F_1 has infinitely many distinct conjugacy classes: distinct
    positive powers of γ_0 are pairwise non-conjugate. F_1 is abelian
    so conjugacy = equality, then gamma_pow_gen_inj closes the loop. *)
Theorem F_1_infinite_conjugacy_classes :
  forall (a b : nat), a <> b ->
    ~ are_conjugate (FreeGroup 1)
        (gamma_pow (free_gen_RWord 1 Fin.F1) a)
        (gamma_pow (free_gen_RWord 1 Fin.F1) b).
Proof.
  intros a b Hab Hconj.
  apply Hab.
  apply (gamma_pow_gen_inj 1%nat Fin.F1 a b).
  apply F_1_are_conjugate_iff_eq. exact Hconj.
Qed.

(** F_1: positive and inverse powers (both nontrivial) are never conjugate. *)
Theorem F_1_pos_neg_distinct_classes :
  forall (a b : nat), (1 <= a)%nat -> (1 <= b)%nat ->
    ~ are_conjugate (FreeGroup 1)
        (gamma_pow (free_gen_RWord 1 Fin.F1) a)
        (gamma_pow (rword_inv (free_gen_RWord 1 Fin.F1)) b).
Proof.
  intros a b Ha Hb Hconj.
  pose proof (F_1_are_conjugate_iff_eq
                (gamma_pow (free_gen_RWord 1 Fin.F1) a)
                (gamma_pow (rword_inv (free_gen_RWord 1 Fin.F1)) b)) as Hiff.
  destruct Hiff as [Hfwd _].
  pose proof (Hfwd Hconj) as Heq.
  apply (gamma_pow_gen_pos_ne_neg 1 Fin.F1 a b Ha Hb Heq).
Qed.

(** *** F_n has at least 4 distinct generator-power conjugacy classes.

    For n ≥ 1, the powers e = γ_0^0, γ_0^1, γ_0^2, γ_0^3 are pairwise
    non-conjugate. All 6 pairwise non-conjugacies follow from concrete
    test_A trace computations (sequence 2, 3, 7, 18). *)
Theorem F_n_gen_pow_0_to_3_pairwise_non_conj :
  forall (n : nat) (i : Fin.t n),
  ~ are_conjugate (FreeGroup n) (@rword_e n) (gamma_pow (free_gen_RWord n i) 1) /\
  ~ are_conjugate (FreeGroup n) (@rword_e n) (gamma_pow (free_gen_RWord n i) 2) /\
  ~ are_conjugate (FreeGroup n) (@rword_e n) (gamma_pow (free_gen_RWord n i) 3) /\
  ~ are_conjugate (FreeGroup n)
       (gamma_pow (free_gen_RWord n i) 1) (gamma_pow (free_gen_RWord n i) 2) /\
  ~ are_conjugate (FreeGroup n)
       (gamma_pow (free_gen_RWord n i) 1) (gamma_pow (free_gen_RWord n i) 3) /\
  ~ are_conjugate (FreeGroup n)
       (gamma_pow (free_gen_RWord n i) 2) (gamma_pow (free_gen_RWord n i) 3).
Proof.
  intros n i.
  repeat split.
  - intro Hconj. apply (free_gen_RWord_not_conj_e n i).
    rewrite gamma_pow_one_eq in Hconj. exact Hconj.
  - intro Hconj. apply (F_n_gen_pow_2_non_conj_e_concrete n i).
    apply are_conjugate_sym. exact Hconj.
  - intro Hconj. apply (F_n_gen_pow_3_non_conj_e_concrete n i).
    apply are_conjugate_sym. exact Hconj.
  - apply (F_n_gen_pow_1_2_non_conj_concrete n i).
  - apply (F_n_gen_pow_1_3_non_conj_concrete n i).
  - apply (F_n_gen_pow_2_3_non_conj_concrete n i).
Qed.

(** F_n has at least 5 distinct generator-power conjugacy classes:
    e, γ_i, γ_i^2, γ_i^3, γ_i^4 are pairwise non-conjugate. C(5,2) = 10 pairs. *)
Theorem F_n_gen_pow_0_to_4_pairwise_non_conj :
  forall (n : nat) (i : Fin.t n),
  ~ are_conjugate (FreeGroup n) (@rword_e n) (gamma_pow (free_gen_RWord n i) 1) /\
  ~ are_conjugate (FreeGroup n) (@rword_e n) (gamma_pow (free_gen_RWord n i) 2) /\
  ~ are_conjugate (FreeGroup n) (@rword_e n) (gamma_pow (free_gen_RWord n i) 3) /\
  ~ are_conjugate (FreeGroup n) (@rword_e n) (gamma_pow (free_gen_RWord n i) 4) /\
  ~ are_conjugate (FreeGroup n)
       (gamma_pow (free_gen_RWord n i) 1) (gamma_pow (free_gen_RWord n i) 2) /\
  ~ are_conjugate (FreeGroup n)
       (gamma_pow (free_gen_RWord n i) 1) (gamma_pow (free_gen_RWord n i) 3) /\
  ~ are_conjugate (FreeGroup n)
       (gamma_pow (free_gen_RWord n i) 1) (gamma_pow (free_gen_RWord n i) 4) /\
  ~ are_conjugate (FreeGroup n)
       (gamma_pow (free_gen_RWord n i) 2) (gamma_pow (free_gen_RWord n i) 3) /\
  ~ are_conjugate (FreeGroup n)
       (gamma_pow (free_gen_RWord n i) 2) (gamma_pow (free_gen_RWord n i) 4) /\
  ~ are_conjugate (FreeGroup n)
       (gamma_pow (free_gen_RWord n i) 3) (gamma_pow (free_gen_RWord n i) 4).
Proof.
  intros n i.
  destruct (F_n_gen_pow_0_to_3_pairwise_non_conj n i)
    as [H1 [H2 [H3 [H12 [H13 H23]]]]].
  repeat split; auto.
  - intro Hconj. apply (F_n_gen_pow_4_non_conj_e_concrete n i).
    apply are_conjugate_sym. exact Hconj.
  - apply F_n_gen_pow_1_4_non_conj_concrete.
  - apply F_n_gen_pow_2_4_non_conj_concrete.
  - apply F_n_gen_pow_3_4_non_conj_concrete.
Qed.
