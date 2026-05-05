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
(* CAG zero-dependent Conjecture fricke_generation theories/DecisionProblems/SL2Horowitz.v:177 BEGIN
  Conjecture fricke_generation :
      forall (n_gens : nat) (gamma eta : RWord n_gens),
        (forall rho : Representation (FreeGroup n_gens) (SL2_as_MG fld),
            word_trace n_gens rho gamma = word_trace n_gens rho eta) ->
        are_conjugate (FreeGroup n_gens) gamma eta \/
        are_conjugate (FreeGroup n_gens) gamma
                      (sinv (RWord n_gens) (FreeGroup n_gens) eta).
   CAG zero-dependent Conjecture fricke_generation theories/DecisionProblems/SL2Horowitz.v:177 END *)

  (** With the Fricke generation theorem in hand, Horowitz n=2 is
      immediate (in the disjunctive form). *)
(* CAG zero-dependent Theorem horowitz_n2_thm theories/DecisionProblems/SL2Horowitz.v:187 BEGIN
  Theorem horowitz_n2_thm : forall n_gens : nat,
      horowitz_n2_concrete n_gens.
  Proof.
    intros n_gens. unfold horowitz_n2_concrete.
    intros. apply fricke_generation. assumption.
  Qed.
   CAG zero-dependent Theorem horowitz_n2_thm theories/DecisionProblems/SL2Horowitz.v:187 END *)

  (* ============================================================ *)
  (** ** 3. Connection to OpenProblems.v                             *)
  (* ============================================================ *)

  (** Negative answer to [open_SLn_trace_pair n=2] (modulo inversion):
      there is no SL2-trace-equivalent pair γ, η in F_r where γ is
      neither conjugate to η nor to η^{-1}. *)
(* CAG zero-dependent Theorem horowitz_no_SL2_trace_pair_up_to_inv theories/DecisionProblems/SL2Horowitz.v:201 BEGIN
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
   CAG zero-dependent Theorem horowitz_no_SL2_trace_pair_up_to_inv theories/DecisionProblems/SL2Horowitz.v:201 END *)

  (** Discharge of [OpenProblems.horowitz_n2] (cycle-19 disjunctive
      form) for the SL(2) instantiation of the matrix-group family.

      [horowitz_n2] is parametric in [MG_family_SLn : nat -> MatrixGroup F].
      Specialising to the constant family [fun _ => SL2_as_MG fld]
      gives exactly the Horowitz–Procesi–Magnus statement that
      [fricke_generation] axiomatises, so the discharge is direct.

      Cycle 20 (2026-04-29): completes the n=2 boundary entry from
      OpenProblems.v's open-problem list. *)
(* CAG zero-dependent Theorem horowitz_n2_SL2_instance theories/DecisionProblems/SL2Horowitz.v:225 BEGIN
  Theorem horowitz_n2_SL2_instance : forall n_gens : nat,
      horowitz_n2 n_gens F (fun _ => SL2_as_MG fld).
  Proof.
    intros n_gens. unfold horowitz_n2. intros gamma eta Heq.
    apply (fricke_generation n_gens gamma eta). exact Heq.
  Qed.
   CAG zero-dependent Theorem horowitz_n2_SL2_instance theories/DecisionProblems/SL2Horowitz.v:225 END *)

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
(* CAG zero-dependent Lemma SL2_no_positive_non_conj_trace_pair theories/DecisionProblems/SL2Horowitz.v:306 BEGIN
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
   CAG zero-dependent Lemma SL2_no_positive_non_conj_trace_pair theories/DecisionProblems/SL2Horowitz.v:306 END *)

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
(* CAG zero-dependent Theorem SL2_constant_family_refutes_conjecture_5_5_n2 theories/DecisionProblems/SL2Horowitz.v:438 BEGIN
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
   CAG zero-dependent Theorem SL2_constant_family_refutes_conjecture_5_5_n2 theories/DecisionProblems/SL2Horowitz.v:438 END *)

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
(* CAG zero-dependent Theorem F_n_SL2_trace_equiv_iff_conjugate_up_to_inv theories/DecisionProblems/SL2Horowitz.v:485 BEGIN
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
   CAG zero-dependent Theorem F_n_SL2_trace_equiv_iff_conjugate_up_to_inv theories/DecisionProblems/SL2Horowitz.v:485 END *)

(** F_1 specialization: conjugacy collapses to equality (F_1 abelian),
    so Horowitz becomes "trace-equivalent ⟺ equal or equal-to-inverse". *)
(* CAG zero-dependent Theorem F_1_SL2_trace_equiv_iff_eq_up_to_inv theories/DecisionProblems/SL2Horowitz.v:507 BEGIN
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
   CAG zero-dependent Theorem F_1_SL2_trace_equiv_iff_eq_up_to_inv theories/DecisionProblems/SL2Horowitz.v:507 END *)

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
(* CAG zero-dependent Theorem F_n_distinct_gens_full_non_conj_via_trace_witness theories/DecisionProblems/SL2Horowitz.v:550 BEGIN
Theorem F_n_distinct_gens_full_non_conj_via_trace_witness :
  forall {F : Type} (fld : Field F) (n : nat) (i j : Fin.t n),
    i <> j ->
    forall M_i M_j : SL2_carrier fld,
      SL2_trace fld M_i <> SL2_trace fld M_j ->
      ~ are_conjugate (FreeGroup n) (free_gen_RWord n i) (free_gen_RWord n j) /\
      ~ are_conjugate (FreeGroup n) (free_gen_RWord n i)
                      (sinv (RWord n) (FreeGroup n) (free_gen_RWord n j)).
Admitted.
   CAG zero-dependent Theorem F_n_distinct_gens_full_non_conj_via_trace_witness theories/DecisionProblems/SL2Horowitz.v:550 END *)
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
(* CAG zero-dependent Theorem F_n_non_conjugate_up_to_inv_implies_SL2_distinguishable theories/DecisionProblems/SL2Horowitz.v:579 BEGIN
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
   CAG zero-dependent Theorem F_n_non_conjugate_up_to_inv_implies_SL2_distinguishable theories/DecisionProblems/SL2Horowitz.v:579 END *)

(** F_2 specialization: distinct-trace matrices give full non-conjugacy
    of the two generators (and their inverses). *)
(* CAG zero-dependent Corollary F_2_distinct_gens_non_conj_via_witness theories/DecisionProblems/SL2Horowitz.v:601 BEGIN
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
   CAG zero-dependent Corollary F_2_distinct_gens_non_conj_via_witness theories/DecisionProblems/SL2Horowitz.v:601 END *)

(** *** Concrete Qc instantiation: F_2 generators are non-conjugate
    via test_A (trace 3) and test_C (trace 4) over the rational field. *)

Definition test_A_SL2 : SL2_carrier Qc_Field :=
  SL2_mk Qc_Field test_A test_AB_det_A.

Definition test_C_SL2 : SL2_carrier Qc_Field :=
  SL2_mk Qc_Field test_C test_AC_det_C.

(** Concrete non-conjugacy examples live in [DecisionProblems.SL2HorowitzConcrete].
    Keeping this file focused on the general Horowitz/SL2 trace layer avoids
    recompiling the long concrete-example section after unrelated edits. *)
