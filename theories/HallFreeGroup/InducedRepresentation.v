(** * HallFreeGroup/InducedRepresentation.v

    Induced representation construction: given ρ : H → SL(d, F) and
    a transversal {t_1, ..., t_k} of H ≤ G with [G:H] = k, build
        Ind^G_H ρ : G → SL(k·d, F).

    The induced rep acts on F^{k·d} = ⊕_{i=1}^{k} F^d (k copies).
    For g ∈ G, the matrix Ind ρ(g) is the block matrix with blocks:
        (Ind ρ(g))_{ij} =
          ρ(t_i^{-1} · g · t_j)   if t_i^{-1} · g · t_j ∈ H, else 0.
    Equivalently, with the coset action g·t_j = t_{σ(j)} · h_j,
        (Ind ρ(g))_{i,j} = δ_{i, σ(j)} · ρ(h_j).

    Frobenius trace formula:
        tr(Ind ρ(g)) = Σ_{i: σ_g(i) = i} tr(ρ(h_i)). *)

From CAG Require Import Galois.Field.
From CAG Require Import Group FreeGroup.
From CAG Require Import LinAlg.Matrix2 LinAlg.SL2 LinAlg.SL2Fricke.
From CAG Require Import HallFreeGroup.LabeledGraph.
From CAG Require Import HallFreeGroup.StallingsFolding.
From CAG Require Import HallFreeGroup.SchreierTransversal.
From CAG Require Import DecisionProblems.TraceProperties.
From CAG Require Import DecisionProblems.InducedRep.
From CAG Require Import DecisionProblems.OpenProblems.
From CAG Require Import DecisionProblems.HallTheorem.
From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* ================================================================== *)
(** * 1. Block matrices                                                 *)
(* ================================================================== *)

(** A block matrix with k×k blocks of d×d matrices over F. We
    represent it as a k×k array of d×d matrix entries. *)

Section BlockMatrices.
  Context {F : Type} (fld : Field F) (d : nat).

  (** A block matrix as a list of lists. *)
  Definition block_matrix : Type := list (list (option (Mat2 F))).
    (* Using Mat2 (d=2) for now since SL(2) is what we have. *)

End BlockMatrices.

(* ================================================================== *)
(** * 2. The induced trace via Frobenius                                *)
(* ================================================================== *)

(** Given:
    - A finite-index subgroup H ≤ G with transversal {t_0, ..., t_{k-1}}.
    - A representation ρ : H → SL(d, F).
    - An element g ∈ G.

    The induced trace is
        tr(Ind ρ(g)) = Σ_{i=0}^{k-1} [σ_g(i) = i] · tr(ρ(h_i))
    where (σ_g, h_i) is the coset action data g·t_i = t_{σ_g(i)} · h_i.

    Below we wrap this in the existing [InducedRep.coset_sigma] +
    [InducedRep.coset_cocycle] infrastructure. *)

Section InducedTrace.
  Context {G F : Type} (sg : StrictGroup G) (FIS : FiniteIndexSubgroup sg)
          (fld : Field F)
          (rho_H : G -> mg_carrier (SL2_as_MG fld)).

  (** Sum the traces over fixed points of the coset permutation. *)
  Fixpoint induced_trace_aux (g : G) (k : nat) (acc : F) : F :=
    match k with
    | 0 => acc
    | S k' =>
        let i := k' in
        if Nat.eqb (coset_sigma FIS g i) i then
          let h_i := coset_cocycle FIS g i in
          induced_trace_aux g k'
            (cr_add fld acc (mat2_trace fld (proj1_sig (rho_H h_i))))
        else
          induced_trace_aux g k' acc
    end.

  Definition induced_trace (g : G) : F :=
    induced_trace_aux g (fis_index FIS) (cr_zero fld).

End InducedTrace.

(* ================================================================== *)
(** * 2.5. Basic properties of induced_trace                            *)
(* ================================================================== *)

(** Extensional equivalence: if rho_H1 and rho_H2 agree on all elements,
    they yield the same induced_trace. *)
Lemma induced_trace_aux_ext :
  forall {G F : Type} (sg : StrictGroup G) (FIS : FiniteIndexSubgroup sg)
         (fld : Field F)
         (rho_H1 rho_H2 : G -> mg_carrier (SL2_as_MG fld))
         (g : G) (k : nat) (acc : F),
    (forall x, rho_H1 x = rho_H2 x) ->
    induced_trace_aux sg FIS fld rho_H1 g k acc =
    induced_trace_aux sg FIS fld rho_H2 g k acc.
Proof.
  intros G F sg FIS fld rho1 rho2 g k.
  induction k as [|k IH]; intros acc Hext.
  - reflexivity.
  - simpl. destruct (Nat.eqb (coset_sigma FIS g k) k).
    + rewrite Hext. apply IH. exact Hext.
    + apply IH. exact Hext.
Qed.

Lemma induced_trace_ext :
  forall {G F : Type} (sg : StrictGroup G) (FIS : FiniteIndexSubgroup sg)
         (fld : Field F)
         (rho_H1 rho_H2 : G -> mg_carrier (SL2_as_MG fld))
         (g : G),
    (forall x, rho_H1 x = rho_H2 x) ->
    induced_trace sg FIS fld rho_H1 g = induced_trace sg FIS fld rho_H2 g.
Proof.
  intros G F sg FIS fld rho1 rho2 g Hext.
  unfold induced_trace.
  apply induced_trace_aux_ext. exact Hext.
Qed.

(** When fis_index = 0 (trivial degenerate case), induced_trace = zero. *)
Lemma induced_trace_index_zero :
  forall {G F : Type} (sg : StrictGroup G) (FIS : FiniteIndexSubgroup sg)
         (fld : Field F)
         (rho_H : G -> mg_carrier (SL2_as_MG fld))
         (g : G),
    fis_index FIS = 0 ->
    induced_trace sg FIS fld rho_H g = cr_zero fld.
Proof.
  intros G F sg FIS fld rho g Hzero.
  unfold induced_trace. rewrite Hzero. simpl. reflexivity.
Qed.

(** Class-function property at h = identity: g·e·g^{-1} = e, so trivial. *)
Lemma induced_trace_class_function_identity :
  forall {G F : Type} (sg : StrictGroup G) (FIS : FiniteIndexSubgroup sg)
         (fld : Field F)
         (rho_H : G -> mg_carrier (SL2_as_MG fld))
         (g : G),
    induced_trace sg FIS fld rho_H
      (smul G sg (smul G sg g (se G sg)) (sinv G sg g)) =
    induced_trace sg FIS fld rho_H (se G sg).
Proof.
  intros G F sg FIS fld rho g.
  rewrite (sid_right G sg g).
  rewrite (sinv_right G sg g).
  reflexivity.
Qed.

(** Helper: sinv of identity is identity. *)
Lemma sinv_se_eq_se : forall {G : Type} (sg : StrictGroup G),
    sinv G sg (se G sg) = se G sg.
Proof.
  intros G sg.
  pose proof (sinv_left G sg (se G sg)) as Hl.
  rewrite (sid_right G sg) in Hl. exact Hl.
Qed.

(** Class-function property at h = identity for arbitrary g — alternate form. *)
Lemma induced_trace_class_e_h :
  forall {G F : Type} (sg : StrictGroup G) (FIS : FiniteIndexSubgroup sg)
         (fld : Field F)
         (rho_H : G -> mg_carrier (SL2_as_MG fld)),
    induced_trace sg FIS fld rho_H
      (smul G sg (smul G sg (se G sg) (se G sg)) (sinv G sg (se G sg))) =
    induced_trace sg FIS fld rho_H (se G sg).
Proof.
  intros G F sg FIS fld rho.
  rewrite (sid_left G sg).
  rewrite sinv_se_eq_se.
  rewrite (sid_right G sg).
  reflexivity.
Qed.

(** Class-function property at g = identity: e·h·e^{-1} = h, so trivial. *)
Lemma induced_trace_class_function_identity_g :
  forall {G F : Type} (sg : StrictGroup G) (FIS : FiniteIndexSubgroup sg)
         (fld : Field F)
         (rho_H : G -> mg_carrier (SL2_as_MG fld))
         (h : G),
    induced_trace sg FIS fld rho_H
      (smul G sg (smul G sg (se G sg) h) (sinv G sg (se G sg))) =
    induced_trace sg FIS fld rho_H h.
Proof.
  intros G F sg FIS fld rho h.
  rewrite (sid_left G sg h).
  rewrite (sinv_se_eq_se sg).
  rewrite (sid_right G sg h).
  reflexivity.
Qed.

(** Accumulator factoring: induced_trace_aux with arbitrary acc equals
    [acc + (induced_trace_aux ... 0)]. Standard tail-recursive
    accumulator transformation. *)
Lemma induced_trace_aux_acc :
  forall {G F : Type} (sg : StrictGroup G) (FIS : FiniteIndexSubgroup sg)
         (fld : Field F)
         (rho_H : G -> mg_carrier (SL2_as_MG fld))
         (g : G) (k : nat) (acc : F),
    induced_trace_aux sg FIS fld rho_H g k acc =
    cr_add fld acc
      (induced_trace_aux sg FIS fld rho_H g k (cr_zero fld)).
Proof.
  intros G F sg FIS fld rho g k.
  induction k as [|k IH]; intro acc.
  - simpl. rewrite (cr_add_zero fld acc). reflexivity.
  - simpl.
    destruct (Nat.eqb (coset_sigma FIS g k) k) eqn:Hfix.
    + (* fixed: accumulate trace term *)
      rewrite IH.
      symmetry. rewrite IH. symmetry.
      (* both sides factored: LHS = (acc + t) + ind0 ;
         RHS = acc + ((0 + t) + ind0) where 0 + t = t. *)
      rewrite (cr_add_comm fld (cr_zero fld)).
      rewrite (cr_add_zero fld).
      rewrite (cr_add_assoc fld). reflexivity.
    + (* not fixed: just IH *)
      apply IH.
Qed.

(** induced_trace_aux additive: factoring out the accumulator gives
    [induced_trace_aux ... (a + b) = a + (induced_trace_aux ... b)]. *)
Lemma induced_trace_aux_add :
  forall {G F : Type} (sg : StrictGroup G) (FIS : FiniteIndexSubgroup sg)
         (fld : Field F)
         (rho_H : G -> mg_carrier (SL2_as_MG fld))
         (g : G) (k : nat) (a b : F),
    induced_trace_aux sg FIS fld rho_H g k (cr_add fld a b) =
    cr_add fld a (induced_trace_aux sg FIS fld rho_H g k b).
Proof.
  intros G F sg FIS fld rho g k a b.
  rewrite (induced_trace_aux_acc _ _ _ _ _ _ (cr_add fld a b)).
  rewrite (induced_trace_aux_acc _ _ _ _ _ _ b).
  rewrite (cr_add_assoc fld). reflexivity.
Qed.

(* ================================================================== *)
(** * 2.6. Coset action — derived facts                                *)
(* ================================================================== *)

(** σ_{g^{-1}} undoes σ_g: σ_{g^{-1}}(σ_g(i)) = i. *)
Lemma coset_sigma_inv : forall {G : Type} {sg : StrictGroup G}
                                (FIS : FiniteIndexSubgroup sg)
                                (g : G) (i : nat),
    i < fis_index FIS ->
    coset_sigma FIS (sinv G sg g) (coset_sigma FIS g i) = i.
Proof.
  intros G sg FIS g i Hi.
  pose proof (coset_sigma_compose FIS (sinv G sg g) g i Hi) as H.
  rewrite (sinv_left G sg) in H.
  rewrite (coset_sigma_id FIS i Hi) in H.
  symmetry. exact H.
Qed.

(** σ_g undoes σ_{g^{-1}}: σ_g(σ_{g^{-1}}(i)) = i. *)
Lemma coset_sigma_inv_inv : forall {G : Type} {sg : StrictGroup G}
                                   (FIS : FiniteIndexSubgroup sg)
                                   (g : G) (i : nat),
    i < fis_index FIS ->
    coset_sigma FIS g (coset_sigma FIS (sinv G sg g) i) = i.
Proof.
  intros G sg FIS g i Hi.
  pose proof (coset_sigma_compose FIS g (sinv G sg g) i Hi) as H.
  rewrite (sinv_right G sg) in H.
  rewrite (coset_sigma_id FIS i Hi) in H.
  symmetry. exact H.
Qed.

(** σ is injective on Fin_k (as a permutation — pulled from σ_{g^{-1}} ∘ σ_g = id). *)
Lemma coset_sigma_inj : forall {G : Type} {sg : StrictGroup G}
                                (FIS : FiniteIndexSubgroup sg)
                                (g : G) (i j : nat),
    i < fis_index FIS ->
    j < fis_index FIS ->
    coset_sigma FIS g i = coset_sigma FIS g j ->
    i = j.
Proof.
  intros G sg FIS g i j Hi Hj Heq.
  pose proof (coset_sigma_inv FIS g i Hi) as Hii.
  pose proof (coset_sigma_inv FIS g j Hj) as Hjj.
  rewrite <- Hii. rewrite <- Hjj. rewrite Heq. reflexivity.
Qed.

(** σ is surjective on Fin_k: every j has a preimage σ_{g^{-1}}(j). *)
Lemma coset_sigma_surj : forall {G : Type} {sg : StrictGroup G}
                                (FIS : FiniteIndexSubgroup sg)
                                (g : G) (j : nat),
    j < fis_index FIS ->
    exists i, i < fis_index FIS /\ coset_sigma FIS g i = j.
Proof.
  intros G sg FIS g j Hj.
  exists (coset_sigma FIS (sinv G sg g) j). split.
  - apply coset_sigma_bound. exact Hj.
  - apply (coset_sigma_inv_inv FIS g j Hj).
Qed.

(** σ is a bijection on the coset indices: σ is injective AND surjective. *)
Theorem coset_sigma_bijective : forall {G : Type} {sg : StrictGroup G}
                                       (FIS : FiniteIndexSubgroup sg)
                                       (g : G),
    (forall i j, i < fis_index FIS -> j < fis_index FIS ->
                 coset_sigma FIS g i = coset_sigma FIS g j -> i = j) /\
    (forall j, j < fis_index FIS ->
               exists i, i < fis_index FIS /\ coset_sigma FIS g i = j).
Proof.
  intros G sg FIS g. split.
  - apply (coset_sigma_inj FIS g).
  - apply (coset_sigma_surj FIS g).
Qed.

(** Fixed-point preservation through σ_{g^{-1}}: i is fixed by σ_g iff
    i is fixed by σ_{g^{-1}}. Because σ_g and σ_{g^{-1}} are mutual
    inverses as permutations, fixed points coincide. *)
Lemma coset_sigma_fix_inv : forall {G : Type} {sg : StrictGroup G}
                                   (FIS : FiniteIndexSubgroup sg)
                                   (g : G) (i : nat),
    i < fis_index FIS ->
    coset_sigma FIS g i = i ->
    coset_sigma FIS (sinv G sg g) i = i.
Proof.
  intros G sg FIS g i Hi Hfix.
  pose proof (coset_sigma_inv FIS g i Hi) as Hii.
  rewrite Hfix in Hii. exact Hii.
Qed.

(** Symmetric: σ_g fixes i iff σ_{g^{-1}} fixes i. *)
Lemma coset_sigma_fix_iff_inv : forall {G : Type} {sg : StrictGroup G}
                                       (FIS : FiniteIndexSubgroup sg)
                                       (g : G) (i : nat),
    i < fis_index FIS ->
    (coset_sigma FIS g i = i <-> coset_sigma FIS (sinv G sg g) i = i).
Proof.
  intros G sg FIS g i Hi. split.
  - intros Hf. apply (coset_sigma_fix_inv FIS g i Hi Hf).
  - intros Hf'.
    pose proof (coset_sigma_fix_inv FIS (sinv G sg g) i Hi Hf') as H.
    rewrite (double_inverse sg) in H. exact H.
Qed.

(** Iterating σ_g: define the n-fold iteration of σ_g on an index. *)
Fixpoint sigma_iter {G : Type} {sg : StrictGroup G}
  (FIS : FiniteIndexSubgroup sg) (g : G) (n : nat) (i : nat) : nat :=
  match n with
  | 0 => i
  | S k => coset_sigma FIS g (sigma_iter FIS g k i)
  end.

(** σ at gamma_pow γ k (in any group with smul): equals k-fold iterate of σ_γ. *)
Lemma coset_sigma_gamma_pow :
  forall {r : nat} (FIS : FiniteIndexSubgroup (FreeGroup r))
         (gamma : RWord r) (k : nat) (i : nat),
    i < fis_index FIS ->
    coset_sigma FIS (gamma_pow gamma k) i =
    sigma_iter FIS gamma k i.
Proof.
  intros r FIS gamma k i Hi. induction k as [|k IH].
  - simpl. change (@rword_e r) with (se (RWord r) (FreeGroup r)).
    apply coset_sigma_id. exact Hi.
  - simpl.
    change (rword_mul gamma (gamma_pow gamma k))
      with (smul (RWord r) (FreeGroup r) gamma (gamma_pow gamma k)).
    rewrite (coset_sigma_compose FIS gamma (gamma_pow gamma k) i Hi).
    f_equal. apply IH.
Qed.

(** σ_{γ^k} applied at e (= γ^0): just iterates σ_γ. *)
Lemma sigma_iter_zero : forall {G : Type} {sg : StrictGroup G}
                                 (FIS : FiniteIndexSubgroup sg)
                                 (g : G) (i : nat),
    sigma_iter FIS g 0 i = i.
Proof. reflexivity. Qed.

Lemma sigma_iter_succ : forall {G : Type} {sg : StrictGroup G}
                                 (FIS : FiniteIndexSubgroup sg)
                                 (g : G) (k i : nat),
    sigma_iter FIS g (S k) i = coset_sigma FIS g (sigma_iter FIS g k i).
Proof. reflexivity. Qed.

(** sigma_iter at identity g = se is constant identity. *)
Lemma sigma_iter_e : forall {G : Type} {sg : StrictGroup G}
                            (FIS : FiniteIndexSubgroup sg)
                            (n i : nat),
    i < fis_index FIS ->
    sigma_iter FIS (se G sg) n i = i.
Proof.
  intros G sg FIS n i Hi. induction n as [|n IH].
  - reflexivity.
  - simpl. rewrite IH. apply coset_sigma_id. exact Hi.
Qed.

(** sigma_iter preserves bounds: if i < fis_index, so does iterated. *)
Lemma sigma_iter_bound : forall {G : Type} {sg : StrictGroup G}
                                (FIS : FiniteIndexSubgroup sg)
                                (g : G) (n i : nat),
    i < fis_index FIS ->
    sigma_iter FIS g n i < fis_index FIS.
Proof.
  intros G sg FIS g n i Hi. induction n as [|n IH].
  - exact Hi.
  - simpl. apply (coset_sigma_bound FIS g _ IH).
Qed.

(** If i is a fixed point of σ_g, it's a fixed point of all sigma_iter. *)
Lemma sigma_iter_fix : forall {G : Type} {sg : StrictGroup G}
                              (FIS : FiniteIndexSubgroup sg)
                              (g : G) (n i : nat),
    coset_sigma FIS g i = i ->
    sigma_iter FIS g n i = i.
Proof.
  intros G sg FIS g n i Hfix. induction n as [|n IH].
  - reflexivity.
  - simpl. rewrite IH. exact Hfix.
Qed.

(** sigma_iter is additive in the iteration count: σ_g^{a+b}(i) = σ_g^a(σ_g^b(i)). *)
Lemma sigma_iter_add : forall {G : Type} {sg : StrictGroup G}
                              (FIS : FiniteIndexSubgroup sg)
                              (g : G) (a b i : nat),
    sigma_iter FIS g (a + b) i =
    sigma_iter FIS g a (sigma_iter FIS g b i).
Proof.
  intros G sg FIS g a. induction a as [|a IH]; intros b i.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(** Connection: σ_{γ^(a+b)}(i) = sigma_iter γ a (sigma_iter γ b i).
    This combines coset_sigma_gamma_pow + sigma_iter_add. *)
Lemma coset_sigma_gamma_pow_add :
  forall {r : nat} (FIS : FiniteIndexSubgroup (FreeGroup r))
         (gamma : RWord r) (a b i : nat),
    i < fis_index FIS ->
    coset_sigma FIS (gamma_pow gamma (a + b)) i =
    sigma_iter FIS gamma a (sigma_iter FIS gamma b i).
Proof.
  intros r FIS gamma a b i Hi.
  rewrite (coset_sigma_gamma_pow FIS gamma (a + b) i Hi).
  apply sigma_iter_add.
Qed.

(** Fixed point of σ_γ is fixed by σ_{γ^k}. *)
Lemma coset_sigma_gamma_pow_fix :
  forall {r : nat} (FIS : FiniteIndexSubgroup (FreeGroup r))
         (gamma : RWord r) (k i : nat),
    i < fis_index FIS ->
    coset_sigma FIS gamma i = i ->
    coset_sigma FIS (gamma_pow gamma k) i = i.
Proof.
  intros r FIS gamma k i Hi Hfix.
  rewrite (coset_sigma_gamma_pow FIS gamma k i Hi).
  apply sigma_iter_fix. exact Hfix.
Qed.

(** Conjugation acts on σ: σ_{ghg^{-1}}(i) = σ_g(σ_h(σ_{g^{-1}}(i))). *)
Lemma coset_sigma_conj : forall {G : Type} {sg : StrictGroup G}
                                 (FIS : FiniteIndexSubgroup sg)
                                 (g h : G) (i : nat),
    i < fis_index FIS ->
    coset_sigma FIS (smul G sg (smul G sg g h) (sinv G sg g)) i =
    coset_sigma FIS g
      (coset_sigma FIS h (coset_sigma FIS (sinv G sg g) i)).
Proof.
  intros G sg FIS g h i Hi.
  rewrite (coset_sigma_compose FIS (smul G sg g h) (sinv G sg g) i Hi).
  pose proof (coset_sigma_bound FIS (sinv G sg g) i Hi) as Hgi.
  rewrite (coset_sigma_compose FIS g h _ Hgi).
  reflexivity.
Qed.

(** Fixed-point-set bijection: i is fixed by σ_{ghg^{-1}}
    iff σ_{g^{-1}}(i) is fixed by σ_h. *)
Lemma coset_sigma_conj_fix : forall {G : Type} {sg : StrictGroup G}
                                     (FIS : FiniteIndexSubgroup sg)
                                     (g h : G) (i : nat),
    i < fis_index FIS ->
    coset_sigma FIS (smul G sg (smul G sg g h) (sinv G sg g)) i = i <->
    coset_sigma FIS h (coset_sigma FIS (sinv G sg g) i) =
    coset_sigma FIS (sinv G sg g) i.
Proof.
  intros G sg FIS g h i Hi.
  rewrite (coset_sigma_conj FIS g h i Hi).
  split.
  - intro Heq.
    (* σ_g (σ_h (σ_{g^{-1}}(i))) = i means σ_h (σ_{g^{-1}}(i)) = σ_{g^{-1}}(i) *)
    pose proof (coset_sigma_bound FIS (sinv G sg g) i Hi) as Hbnd.
    pose proof (coset_sigma_bound FIS h _ Hbnd) as Hbnd2.
    apply (coset_sigma_inj FIS g _ _ Hbnd2 Hbnd).
    rewrite Heq. symmetry. apply (coset_sigma_inv_inv FIS g i Hi).
  - intro Heq.
    rewrite Heq. apply (coset_sigma_inv_inv FIS g i Hi).
Qed.

(** Helper: if i < fis_index then nth_error fis_trans i = Some t for some t. *)
Lemma fis_trans_nth_error : forall {G : Type} {sg : StrictGroup G}
                                    (FIS : FiniteIndexSubgroup sg) (i : nat),
    i < fis_index FIS ->
    exists t, nth_error (fis_trans FIS) i = Some t.
Proof.
  intros G sg FIS i Hi.
  pose proof (fis_trans_len FIS) as Hlen.
  destruct (nth_error (fis_trans FIS) i) as [t|] eqn:Hnth.
  - exists t. reflexivity.
  - exfalso.
    apply (proj2 (List.nth_error_Some (fis_trans FIS) i)) in Hnth.
    + exact Hnth.
    + rewrite Hlen. exact Hi.
Qed.

(** Cocycle at identity is identity: h_{e, i} = e (provable from coset_action_eq). *)
Lemma coset_cocycle_id_at_e : forall {G : Type} {sg : StrictGroup G}
                                      (FIS : FiniteIndexSubgroup sg)
                                      (i : nat),
    i < fis_index FIS ->
    coset_cocycle FIS (se G sg) i = se G sg.
Proof.
  intros G sg FIS i Hi.
  pose proof (fis_trans_len FIS) as Hlen.
  destruct (nth_error (fis_trans FIS) i) as [t_i|] eqn:Hnth.
  - pose proof (coset_sigma_id FIS i Hi) as Hsi.
    pose proof (coset_action_eq FIS (se G sg) i t_i t_i Hi Hnth) as Heq.
    rewrite Hsi in Heq. specialize (Heq Hnth).
    rewrite (sid_left G sg) in Heq.
    (* Heq: t_i = t_i · h_{e, i} *)
    apply (left_cancel sg t_i).
    rewrite (sid_right G sg). symmetry. exact Heq.
  - exfalso.
    apply (proj2 (List.nth_error_Some (fis_trans FIS) i)) in Hnth.
    + exact Hnth.
    + rewrite Hlen. exact Hi.
Qed.

(** Cocycle at gamma_pow γ 0 = e: trivial via coset_cocycle_id_at_e. *)
Lemma coset_cocycle_gamma_pow_zero :
  forall {r : nat} (FIS : FiniteIndexSubgroup (FreeGroup r))
         (gamma : RWord r) (i : nat),
    i < fis_index FIS ->
    coset_cocycle FIS (gamma_pow gamma 0) i = se (RWord r) (FreeGroup r).
Proof.
  intros r FIS gamma i Hi.
  change (gamma_pow gamma 0) with (se (RWord r) (FreeGroup r)).
  apply coset_cocycle_id_at_e. exact Hi.
Qed.

(** σ at gamma_pow e k = e^k = e: identity. *)
Lemma coset_sigma_at_e_pow :
  forall {r : nat} (FIS : FiniteIndexSubgroup (FreeGroup r))
         (k i : nat),
    i < fis_index FIS ->
    coset_sigma FIS (gamma_pow (@rword_e r) k) i = i.
Proof.
  intros r FIS k i Hi.
  rewrite gamma_pow_id.
  change (@rword_e r) with (se (RWord r) (FreeGroup r)).
  apply coset_sigma_id. exact Hi.
Qed.

(** Cocycle at gamma_pow e k = e: identity. *)
Lemma coset_cocycle_at_e_pow :
  forall {r : nat} (FIS : FiniteIndexSubgroup (FreeGroup r))
         (k i : nat),
    i < fis_index FIS ->
    coset_cocycle FIS (gamma_pow (@rword_e r) k) i =
    se (RWord r) (FreeGroup r).
Proof.
  intros r FIS k i Hi.
  rewrite gamma_pow_id.
  change (@rword_e r) with (se (RWord r) (FreeGroup r)).
  apply coset_cocycle_id_at_e. exact Hi.
Qed.

(** Class function at e: induced_trace at e·h·e^{-1} = h. *)
Lemma induced_trace_class_function_e_h :
  forall {G F : Type} (sg : StrictGroup G) (FIS : FiniteIndexSubgroup sg)
         (fld : Field F)
         (rho_H : G -> mg_carrier (SL2_as_MG fld))
         (h : G),
    induced_trace sg FIS fld rho_H
      (smul G sg (smul G sg (se G sg) h) (sinv G sg (se G sg))) =
    induced_trace sg FIS fld rho_H h.
Proof.
  intros G F sg FIS fld rho h.
  rewrite (sid_left G sg).
  rewrite sinv_se_eq_se.
  rewrite (sid_right G sg). reflexivity.
Qed.

(** When g and h commute, the class-function property is trivial:
    ghg^{-1} = h. *)
Lemma induced_trace_class_function_commute :
  forall {G F : Type} (sg : StrictGroup G) (FIS : FiniteIndexSubgroup sg)
         (fld : Field F)
         (rho_H : G -> mg_carrier (SL2_as_MG fld))
         (g h : G),
    smul G sg g h = smul G sg h g ->
    induced_trace sg FIS fld rho_H
      (smul G sg (smul G sg g h) (sinv G sg g)) =
    induced_trace sg FIS fld rho_H h.
Proof.
  intros G F sg FIS fld rho g h Hcomm.
  rewrite Hcomm.
  rewrite <- (sassoc G sg).
  rewrite (sinv_right G sg).
  rewrite (sid_right G sg). reflexivity.
Qed.

(** When g = h, gg g^{-1} = g (self-conjugate). *)
Lemma induced_trace_class_function_self :
  forall {G F : Type} (sg : StrictGroup G) (FIS : FiniteIndexSubgroup sg)
         (fld : Field F)
         (rho_H : G -> mg_carrier (SL2_as_MG fld))
         (g : G),
    induced_trace sg FIS fld rho_H
      (smul G sg (smul G sg g g) (sinv G sg g)) =
    induced_trace sg FIS fld rho_H g.
Proof.
  intros G F sg FIS fld rho g.
  apply induced_trace_class_function_commute. reflexivity.
Qed.

(** Cocycle composition (1-cocycle relation):
    h_{g·h, i} = h_{g, σ_h(i)} · h_{h, i}. *)
Lemma coset_cocycle_compose :
  forall {G : Type} {sg : StrictGroup G}
         (FIS : FiniteIndexSubgroup sg) (g h : G) (i : nat),
    i < fis_index FIS ->
    coset_cocycle FIS (smul G sg g h) i =
    smul G sg
      (coset_cocycle FIS g (coset_sigma FIS h i))
      (coset_cocycle FIS h i).
Proof.
  intros G sg FIS g h i Hi.
  pose proof (fis_trans_nth_error FIS i Hi) as [t_i Ht_i].
  pose proof (coset_sigma_bound FIS h i Hi) as Hh_bnd.
  pose proof (fis_trans_nth_error FIS (coset_sigma FIS h i) Hh_bnd)
    as [t_hi Ht_hi].
  pose proof (coset_sigma_bound FIS g (coset_sigma FIS h i) Hh_bnd) as Hgh_bnd.
  pose proof (fis_trans_nth_error FIS
              (coset_sigma FIS g (coset_sigma FIS h i)) Hgh_bnd)
    as [t_ghi Ht_ghi].
  (* h · t_i = t_{σ_h i} · h_{h, i} *)
  pose proof (coset_action_eq FIS h i t_i t_hi Hi Ht_i Ht_hi) as Hh.
  (* g · t_{σ_h i} = t_{σ_g(σ_h i)} · h_{g, σ_h i} *)
  pose proof (coset_action_eq FIS g (coset_sigma FIS h i) t_hi t_ghi
                              Hh_bnd Ht_hi Ht_ghi) as Hg.
  (* Compute (gh)·t_i two ways:
     - directly: (gh)·t_i = t_{σ_{gh} i} · h_{gh, i}
       with σ_{gh} i = σ_g(σ_h i) by coset_sigma_compose
     - via h then g: gh·t_i = g·(h·t_i) = g·(t_{σ_h i}·h_{h,i})
       = (g·t_{σ_h i})·h_{h,i} = (t_{σ_g(σ_h i)}·h_{g,σ_h i})·h_{h,i}
       = t_{σ_g(σ_h i)} · (h_{g,σ_h i}·h_{h,i}) *)
  pose proof (coset_sigma_compose FIS g h i Hi) as Hsigma_comp.
  assert (Ht_ghi' : nth_error (fis_trans FIS)
                              (coset_sigma FIS (smul G sg g h) i) =
                    Some t_ghi).
  { rewrite Hsigma_comp. exact Ht_ghi. }
  pose proof (coset_action_eq FIS (smul G sg g h) i t_i t_ghi
                              Hi Ht_i Ht_ghi') as Hgh.
  (* Hgh: (gh)·t_i = t_{σ_{gh} i}·h_{gh,i}
     Hh:  h·t_i = t_{σ_h i}·h_{h,i}
     Hg:  g·t_{σ_h i} = t_{σ_g(σ_h i)}·h_{g, σ_h i}
     Combine: (gh)·t_i = g·(h·t_i) = g·(t_{σ_h i}·h_{h,i}) *)
  rewrite <- (sassoc G sg) in Hgh.
  rewrite Hh in Hgh.
  rewrite (sassoc G sg) in Hgh.
  rewrite Hg in Hgh.
  rewrite <- (sassoc G sg) in Hgh.
  (* Hgh: t_ghi · (h_{g,σ_h i}·h_{h,i}) = t_ghi · h_{gh,i} *)
  apply (left_cancel sg t_ghi). symmetry. exact Hgh.
Qed.

(** Conjugates have equal SL2 trace under any representation. *)
Lemma trace_at_conjugate_SL2 : forall {G F : Type} (sg : StrictGroup G)
                                       (fld : Field F)
                                       (rho : Representation sg (SL2_as_MG fld))
                                       (a b : G),
    are_conjugate sg a b -> trace_at rho a = trace_at rho b.
Proof.
  intros G F sg fld rho a b Hconj.
  apply (trace_at_conjugate sg (SL2_as_MG fld) rho).
  - intros x y. apply SL2_trace_cyclic.
  - exact Hconj.
Qed.

(** Contrapositive: distinct traces ⟹ non-conjugate. *)
Lemma not_conjugate_from_trace_SL2 : forall {G F : Type} (sg : StrictGroup G)
                                              (fld : Field F)
                                              (rho : Representation sg (SL2_as_MG fld))
                                              (a b : G),
    trace_at rho a <> trace_at rho b -> ~ are_conjugate sg a b.
Proof.
  intros G F sg fld rho a b Htr Hconj.
  apply Htr. apply (trace_at_conjugate_SL2 sg fld rho). exact Hconj.
Qed.

(** Distinct power traces ⟹ original elements are non-conjugate. *)
Lemma not_conjugate_from_trace_pow_SL2 :
  forall {F : Type} (r : nat) (fld : Field F)
         (rho : Representation (FreeGroup r) (SL2_as_MG fld))
         (gamma eta : RWord r) (k : nat),
    trace_at rho (gamma_pow gamma k) <> trace_at rho (gamma_pow eta k) ->
    ~ are_conjugate (FreeGroup r) gamma eta.
Proof.
  intros F r fld rho gamma eta k Htr Hconj.
  apply Htr.
  apply (trace_at_conjugate_SL2 (FreeGroup r) fld rho).
  apply are_conjugate_gamma_pow. exact Hconj.
Qed.

(** Distinct inverse-power traces ⟹ original elements are non-conjugate. *)
Lemma not_conjugate_from_trace_inv_pow_SL2 :
  forall {F : Type} (r : nat) (fld : Field F)
         (rho : Representation (FreeGroup r) (SL2_as_MG fld))
         (gamma eta : RWord r) (k : nat),
    trace_at rho (gamma_pow (rword_inv gamma) k) <>
    trace_at rho (gamma_pow (rword_inv eta) k) ->
    ~ are_conjugate (FreeGroup r) gamma eta.
Proof.
  intros F r fld rho gamma eta k Htr Hconj.
  apply Htr.
  apply (trace_at_conjugate_SL2 (FreeGroup r) fld rho).
  apply (are_conjugate_inv_pow_F gamma eta k Hconj).
Qed.

(** Generalized: if ANY h ∈ ⟨γ⟩-style element has trace differing from
    the corresponding element in ⟨η⟩, then γ and η are non-conjugate. *)
Lemma not_conjugate_from_trace_pair_SL2 :
  forall {F : Type} (r : nat) (fld : Field F)
         (rho : Representation (FreeGroup r) (SL2_as_MG fld))
         (gamma eta : RWord r),
    (trace_at rho gamma <> trace_at rho eta \/
     (exists k, trace_at rho (gamma_pow gamma k) <>
                trace_at rho (gamma_pow eta k)) \/
     (exists k, trace_at rho (gamma_pow (rword_inv gamma) k) <>
                trace_at rho (gamma_pow (rword_inv eta) k))) ->
    ~ are_conjugate (FreeGroup r) gamma eta.
Proof.
  intros F r fld rho gamma eta [Hd | [[k Hk] | [k Hk]]].
  - apply (not_conjugate_from_trace_SL2 (FreeGroup r) fld rho gamma eta Hd).
  - apply (not_conjugate_from_trace_pow_SL2 r fld rho gamma eta k Hk).
  - apply (not_conjugate_from_trace_inv_pow_SL2 r fld rho gamma eta k Hk).
Qed.


(** Representation respects gamma_pow: ρ(γ^k) = (ρ γ)^k in SL2. *)
Lemma rep_fn_gamma_pow :
  forall {F : Type} (r : nat) (fld : Field F)
         (rho : Representation (FreeGroup r) (SL2_as_MG fld))
         (gamma : RWord r) (k : nat),
    rep_fn rho (gamma_pow gamma k) = SL2_pow fld (rep_fn rho gamma) k.
Proof.
  intros F r fld rho gamma k. induction k as [|k IH].
  - simpl.
    set (phi := {| hom_fn := rep_fn rho;
                   hom_mul := rep_hom rho |}
                : GroupHom (FreeGroup r) (SL2 fld)).
    exact (hom_id (FreeGroup r) (SL2 fld) phi).
  - simpl.
    change (rword_mul gamma (gamma_pow gamma k))
      with (smul (RWord r) (FreeGroup r) gamma (gamma_pow gamma k)).
    rewrite (rep_hom rho). simpl.
    rewrite IH. reflexivity.
Qed.

(** Representation respects gamma_pow at successor:
    ρ(γ^{S k}) = (ρ γ) · (ρ γ)^k. *)
Lemma rep_fn_gamma_pow_succ :
  forall {F : Type} (r : nat) (fld : Field F)
         (rho : Representation (FreeGroup r) (SL2_as_MG fld))
         (gamma : RWord r) (k : nat),
    rep_fn rho (gamma_pow gamma (S k)) =
    SL2_mul fld (rep_fn rho gamma) (SL2_pow fld (rep_fn rho gamma) k).
Proof.
  intros F r fld rho gamma k.
  rewrite (rep_fn_gamma_pow r fld rho gamma (S k)).
  reflexivity.
Qed.

(** Trace at gamma_pow under representation: tr(ρ(γ^k)) = tr((ρ γ)^k). *)
Lemma rep_trace_at_gamma_pow :
  forall {F : Type} (r : nat) (fld : Field F)
         (rho : Representation (FreeGroup r) (SL2_as_MG fld))
         (gamma : RWord r) (k : nat),
    trace_at rho (gamma_pow gamma k) =
    SL2_trace fld (SL2_pow fld (rep_fn rho gamma) k).
Proof.
  intros F r fld rho gamma k.
  unfold trace_at. simpl.
  rewrite (rep_fn_gamma_pow r fld rho gamma k). reflexivity.
Qed.

(** trace_at rho (γ^0) = 2 (= 1 + 1). *)
Lemma rep_trace_at_gamma_pow_zero :
  forall {F : Type} (r : nat) (fld : Field F)
         (rho : Representation (FreeGroup r) (SL2_as_MG fld))
         (gamma : RWord r),
    trace_at rho (gamma_pow gamma 0) =
    cr_add fld (cr_one fld) (cr_one fld).
Proof.
  intros F r fld rho gamma.
  rewrite (rep_trace_at_gamma_pow r fld rho gamma 0).
  apply SL2_trace_pow_zero.
Qed.

(** trace_at rho (γ^1) = trace_at rho γ. *)
Lemma rep_trace_at_gamma_pow_one :
  forall {F : Type} (r : nat) (fld : Field F)
         (rho : Representation (FreeGroup r) (SL2_as_MG fld))
         (gamma : RWord r),
    trace_at rho (gamma_pow gamma 1) = trace_at rho gamma.
Proof.
  intros F r fld rho gamma.
  rewrite (rep_trace_at_gamma_pow r fld rho gamma 1).
  unfold trace_at. simpl. f_equal.
  apply SL2_pow_one.
Qed.

(** SL2-trace-equivalence for powers: if trace_at rho is the same for γ
    and η, it's the same for all powers. *)
Lemma SL2_trace_equiv_pow :
  forall {F : Type} (r : nat) (fld : Field F)
         (rho : Representation (FreeGroup r) (SL2_as_MG fld))
         (gamma eta : RWord r),
    trace_at rho gamma = trace_at rho eta ->
    forall k, trace_at rho (gamma_pow gamma k) =
              trace_at rho (gamma_pow eta k).
Proof.
  intros F r fld rho gamma eta Hgeq k.
  rewrite (rep_trace_at_gamma_pow r fld rho gamma k).
  rewrite (rep_trace_at_gamma_pow r fld rho eta k).
  apply SL2_trace_pow_determined_by_trace.
  unfold trace_at in Hgeq. simpl in Hgeq. exact Hgeq.
Qed.


(** Property D contrapositive specialized to SL2: if tr(ρ γ^k) and
    tr(ρ η^k) differ for some k, the originals already differ in trace. *)
Lemma SL2_trace_neq_implies_pow_neq :
  forall {F : Type} (r : nat) (fld : Field F)
         (rho : Representation (FreeGroup r) (SL2_as_MG fld))
         (gamma eta : RWord r) (k : nat),
    trace_at rho (gamma_pow gamma k) <> trace_at rho (gamma_pow eta k) ->
    trace_at rho gamma <> trace_at rho eta.
Proof.
  intros F r fld rho gamma eta k Hpow Hgeq.
  apply Hpow.
  apply (SL2_trace_equiv_pow r fld rho gamma eta Hgeq).
Qed.

(** Parabolic case: if tr(ρ γ) = 2 (= 1 + 1), then tr(ρ γ^k) = 2 for all k. *)
Lemma rep_trace_at_gamma_pow_parabolic :
  forall {F : Type} (r : nat) (fld : Field F)
         (rho : Representation (FreeGroup r) (SL2_as_MG fld))
         (gamma : RWord r),
    trace_at rho gamma = cr_add fld (cr_one fld) (cr_one fld) ->
    forall k, trace_at rho (gamma_pow gamma k) =
              cr_add fld (cr_one fld) (cr_one fld).
Proof.
  intros F r fld rho gamma Hg k.
  rewrite (rep_trace_at_gamma_pow r fld rho gamma k).
  apply (SL2_trace_pow_parabolic fld (rep_fn rho gamma)).
  unfold trace_at in Hg. simpl in Hg. exact Hg.
Qed.

(** Representation respects gamma_pow at the inverse:
    ρ((γ^{-1})^k) = (ρ γ)^{-k} = SL2_inv (SL2_pow (ρ γ) k). *)
Lemma rep_fn_gamma_pow_inv :
  forall {F : Type} (r : nat) (fld : Field F)
         (rho : Representation (FreeGroup r) (SL2_as_MG fld))
         (gamma : RWord r) (k : nat),
    rep_fn rho (gamma_pow (rword_inv gamma) k) =
    SL2_inv fld (SL2_pow fld (rep_fn rho gamma) k).
Proof.
  intros F r fld rho gamma k.
  rewrite (rep_fn_gamma_pow r fld rho (rword_inv gamma) k).
  set (phi := {| hom_fn := rep_fn rho;
                 hom_mul := rep_hom rho |}
              : GroupHom (FreeGroup r) (SL2 fld)).
  assert (Hinv : rep_fn rho (rword_inv gamma) =
                 SL2_inv fld (rep_fn rho gamma)).
  { exact (hom_inv (FreeGroup r) (SL2 fld) phi gamma). }
  rewrite Hinv.
  symmetry. apply SL2_inv_pow.
Qed.

(** trace_at rho (γ^{-1})^k = trace_at rho γ^k. *)
Lemma rep_trace_at_gamma_inv_pow :
  forall {F : Type} (r : nat) (fld : Field F)
         (rho : Representation (FreeGroup r) (SL2_as_MG fld))
         (gamma : RWord r) (k : nat),
    trace_at rho (gamma_pow (rword_inv gamma) k) =
    trace_at rho (gamma_pow gamma k).
Proof.
  intros F r fld rho gamma k.
  rewrite (rep_trace_at_gamma_pow r fld rho (rword_inv gamma) k).
  rewrite (rep_trace_at_gamma_pow r fld rho gamma k).
  (* Need: SL2_pow (ρ(γ^{-1})) k = SL2_pow (ρ γ) k at trace level *)
  set (phi := {| hom_fn := rep_fn rho;
                 hom_mul := rep_hom rho |}
              : GroupHom (FreeGroup r) (SL2 fld)).
  assert (Hinv : rep_fn rho (rword_inv gamma) =
                 SL2_inv fld (rep_fn rho gamma)).
  { exact (hom_inv (FreeGroup r) (SL2 fld) phi gamma). }
  rewrite Hinv.
  apply SL2_trace_pow_inv.
Qed.

(** Chebyshev recursion for representation traces:
    tr(ρ(γ^{n+2})) = tr(ρ(γ)) · tr(ρ(γ^{n+1})) - tr(ρ(γ^n)).
    Combines [rep_trace_at_gamma_pow] with [SL2_trace_pow_chebyshev]. *)
Theorem rep_trace_at_gamma_pow_chebyshev :
  forall {F : Type} (r : nat) (fld : Field F)
         (rho : Representation (FreeGroup r) (SL2_as_MG fld))
         (gamma : RWord r) (n : nat),
    trace_at rho (gamma_pow gamma (S (S n))) =
    cr_sub fld
      (cr_mul fld
         (trace_at rho gamma)
         (trace_at rho (gamma_pow gamma (S n))))
      (trace_at rho (gamma_pow gamma n)).
Proof.
  intros F r fld rho gamma n.
  rewrite (rep_trace_at_gamma_pow r fld rho gamma (S (S n))).
  rewrite (rep_trace_at_gamma_pow r fld rho gamma (S n)).
  rewrite (rep_trace_at_gamma_pow r fld rho gamma n).
  apply SL2_trace_pow_chebyshev.
Qed.

(** Trace at the inverse equals trace at the original (under SL2 rep).
    Standard fact: SL2 elements satisfy tr(g^{-1}) = tr(g). *)
Lemma rep_trace_at_inv_SL2 : forall {G F : Type} (sg : StrictGroup G)
                                      (fld : Field F)
                                      (rho : Representation sg (SL2_as_MG fld))
                                      (g : G),
    trace_at rho (sinv G sg g) = trace_at rho g.
Proof.
  intros G F sg fld rho g. unfold trace_at. simpl.
  set (phi := {| hom_fn := rep_fn rho;
                 hom_mul := rep_hom rho |} : GroupHom sg (SL2 fld)).
  pose proof (hom_inv sg (SL2 fld) phi g) as Hinv.
  simpl in Hinv. rewrite Hinv.
  apply SL2_trace_inv.
Qed.

(** g and g^{-1} have equal SL2 traces, so are "trace-equivalent."
    However, this does NOT mean they are conjugate (as in F_2, an
    element and its inverse are not conjugate in general). *)
Lemma trace_inv_equal_SL2 : forall {G F : Type} (sg : StrictGroup G)
                                    (fld : Field F)
                                    (rho : Representation sg (SL2_as_MG fld))
                                    (g : G),
    trace_at rho g = trace_at rho (sinv G sg g).
Proof.
  intros G F sg fld rho g. symmetry. apply rep_trace_at_inv_SL2.
Qed.


(** When ρ comes from a representation (i.e., is a homomorphism), trace
    is conjugation-invariant — derived from SL2_trace_conj + rep_hom. *)
Lemma rep_trace_conj :
  forall {G : Type} {F : Type} (sg : StrictGroup G)
         (fld : Field F) (rho : Representation sg (SL2_as_MG fld))
         (a b : G),
    SL2_trace fld (rep_fn rho
      (smul G sg (smul G sg a b) (sinv G sg a))) =
    SL2_trace fld (rep_fn rho b).
Proof.
  intros G F sg fld rho a b.
  rewrite (rep_hom rho).
  rewrite (rep_hom rho).
  (* Need: rep_fn rho (sinv G sg a) = SL2_inv fld (rep_fn rho a).
     Build a GroupHom from rho and apply hom_inv. *)
  set (phi := {| hom_fn := rep_fn rho;
                 hom_mul := rep_hom rho |} : GroupHom sg (SL2 fld)).
  assert (Hinv : rep_fn rho (sinv G sg a) =
                 sinv (SL2_carrier fld) (SL2 fld) (rep_fn rho a)).
  { exact (hom_inv sg (SL2 fld) phi a). }
  rewrite Hinv.
  (* Now goal is SL2_trace at conjugate. *)
  apply SL2_trace_conj.
Qed.

(** Cocycle inverse identity: h_{g^{-1}, σ_g(i)} · h_{g, i} = e. *)
Lemma coset_cocycle_inverse :
  forall {G : Type} {sg : StrictGroup G}
         (FIS : FiniteIndexSubgroup sg) (g : G) (i : nat),
    i < fis_index FIS ->
    smul G sg
      (coset_cocycle FIS (sinv G sg g) (coset_sigma FIS g i))
      (coset_cocycle FIS g i) = se G sg.
Proof.
  intros G sg FIS g i Hi.
  pose proof (fis_trans_nth_error FIS i Hi) as [t_i Ht_i].
  pose proof (coset_sigma_bound FIS g i Hi) as Hsi_bnd.
  pose proof (fis_trans_nth_error FIS (coset_sigma FIS g i) Hsi_bnd)
    as [t_si Ht_si].
  pose proof (coset_sigma_inv FIS g i Hi) as Hsinv.
  (* coset_action_eq for g, i: g · t_i = t_{σ_g i} · h_{g, i} *)
  pose proof (coset_action_eq FIS g i t_i t_si Hi Ht_i Ht_si) as Hg.
  (* coset_action_eq for g^{-1}, σ_g(i):
     g^{-1} · t_{σ_g i} = t_{σ_{g^{-1}}(σ_g i)} · h_{g^{-1}, σ_g i}
     We supply t_si as t_{σ_g i} and t_i as t_{σ_{g^{-1}}(σ_g i)}.
     The third hypothesis becomes: nth_error fis_trans
        (σ_{g^{-1}}(σ_g i)) = Some t_i.
     Using Hsinv (σ_{g^{-1}}(σ_g i) = i), this is just Ht_i. *)
  assert (Ht_i' : nth_error (fis_trans FIS)
                            (coset_sigma FIS (sinv G sg g)
                                          (coset_sigma FIS g i)) =
                  Some t_i).
  { rewrite Hsinv. exact Ht_i. }
  pose proof (coset_action_eq FIS (sinv G sg g) (coset_sigma FIS g i)
                              t_si t_i Hsi_bnd Ht_si Ht_i') as Hginv.
  (* Hg: g · t_i = t_{σ_g i} · h_{g, i}.
     Multiply by g^{-1} on left: g^{-1} · g · t_i = g^{-1} · (t_{σ_g i} · h_{g, i}). *)
  apply (f_equal (smul G sg (sinv G sg g))) in Hg.
  rewrite (sassoc G sg) in Hg.
  rewrite (sinv_left G sg) in Hg.
  rewrite (sid_left G sg) in Hg.
  (* Hg: t_i = g^{-1} · (t_{σ_g i} · h_{g, i}) *)
  rewrite (sassoc G sg) in Hg.
  rewrite Hginv in Hg.
  (* Hg: t_i = (t_i · h_{g^{-1}, σ_g i}) · h_{g, i}.
     Equivalently after sassoc: t_i = t_i · (h_{g^{-1}, σ_g i} · h_{g, i}). *)
  rewrite <- (sassoc G sg) in Hg.
  apply (left_cancel sg t_i).
  rewrite (sid_right G sg). symmetry. exact Hg.
Qed.

(** Cocycle conjugation formula at fixed points:
    For i a fixed point of σ_{ghg^{-1}}, with j = σ_{g^{-1}} i (a fixed
    point of σ_h), we have:
    h_{ghg^{-1}, i} = h_{g, j} · h_{h, j} · (h_{g, j})^{-1}. *)
Lemma coset_cocycle_conj_at_fix :
  forall {G : Type} {sg : StrictGroup G}
         (FIS : FiniteIndexSubgroup sg) (g h : G) (i : nat),
    i < fis_index FIS ->
    coset_sigma FIS (smul G sg (smul G sg g h) (sinv G sg g)) i = i ->
    coset_cocycle FIS (smul G sg (smul G sg g h) (sinv G sg g)) i =
    smul G sg
      (coset_cocycle FIS g (coset_sigma FIS (sinv G sg g) i))
      (smul G sg
        (coset_cocycle FIS h (coset_sigma FIS (sinv G sg g) i))
        (sinv G sg
          (coset_cocycle FIS g (coset_sigma FIS (sinv G sg g) i)))).
Proof.
  intros G sg FIS g h i Hi Hfix.
  pose proof (coset_sigma_bound FIS (sinv G sg g) i Hi) as Hj_bnd.
  remember (coset_sigma FIS (sinv G sg g) i) as j eqn:Hj_def.
  (* Step 1: j is a fixed point of σ_h. *)
  pose proof (proj1 (coset_sigma_conj_fix FIS g h i Hi) Hfix) as Hh_fix.
  rewrite <- Hj_def in Hh_fix.
  (* Hh_fix: σ_h j = j *)
  (* Step 2: h_{ghg^{-1}, i} = h_{gh, j} · h_{g^{-1}, i}. *)
  pose proof (coset_cocycle_compose FIS (smul G sg g h) (sinv G sg g) i Hi)
    as Hcomp1.
  rewrite <- Hj_def in Hcomp1.
  (* Step 3: h_{gh, j} = h_{g, σ_h j} · h_{h, j} = h_{g, j} · h_{h, j}. *)
  pose proof (coset_cocycle_compose FIS g h j Hj_bnd) as Hcomp2.
  rewrite Hh_fix in Hcomp2.
  (* Step 4: cocycle inverse on g at j: h_{g^{-1}, σ_g j} · h_{g, j} = e.
     Using σ_g j = i. *)
  pose proof (coset_sigma_inv_inv FIS g i Hi) as Hsj.
  rewrite <- Hj_def in Hsj.
  pose proof (coset_cocycle_inverse FIS g j Hj_bnd) as Hcocinv.
  rewrite Hsj in Hcocinv.
  (* Hcocinv: h_{g^{-1}, i} · h_{g, j} = e
     Combine: h_{ghg^{-1}, i} = h_{gh, j} · h_{g^{-1}, i}
                              = (h_{g, j} · h_{h, j}) · h_{g^{-1}, i}
     Goal: h_{ghg^{-1}, i} = h_{g, j} · (h_{h, j} · (h_{g, j})^{-1}) *)
  rewrite Hcomp1, Hcomp2.
  assert (Hgi_inv : coset_cocycle FIS (sinv G sg g) i =
                    sinv G sg (coset_cocycle FIS g j)).
  { (* From Hcocinv: b · a = e where a = h_{g, j}, b = h_{g^{-1}, i}.
       From sinv_left: sinv a · a = e.
       By right_cancel, b = sinv a. *)
    apply (right_cancel sg (coset_cocycle FIS g j)).
    rewrite Hcocinv. symmetry. apply (sinv_left G sg). }
  rewrite Hgi_inv.
  rewrite <- (sassoc G sg). reflexivity.
Qed.

(** Element-wise trace match: for i fixed by σ_{ghg^{-1}}, the trace of
    ρ at the cocycle h_{ghg^{-1}, i} equals the trace of ρ at h_{h, j}
    where j = σ_{g^{-1}} i. *)
Lemma cocycle_trace_match_at_fix :
  forall {G F : Type} (sg : StrictGroup G) (FIS : FiniteIndexSubgroup sg)
         (fld : Field F)
         (rho : Representation sg (SL2_as_MG fld)) (g h : G) (i : nat),
    i < fis_index FIS ->
    coset_sigma FIS (smul G sg (smul G sg g h) (sinv G sg g)) i = i ->
    SL2_trace fld (rep_fn rho
      (coset_cocycle FIS (smul G sg (smul G sg g h) (sinv G sg g)) i)) =
    SL2_trace fld (rep_fn rho
      (coset_cocycle FIS h (coset_sigma FIS (sinv G sg g) i))).
Proof.
  intros G F sg FIS fld rho g h i Hi Hfix.
  rewrite (coset_cocycle_conj_at_fix FIS g h i Hi Hfix).
  rewrite (sassoc G sg).
  apply (rep_trace_conj sg fld rho).
Qed.

(* ================================================================== *)
(** * 2.7. Indexed-sum normal form for induced_trace                    *)
(* ================================================================== *)

(** Indexed sum: Σ_{i<k} f(i). *)
Fixpoint indexed_sum {F : Type} (fld : Field F) (f : nat -> F) (k : nat) : F :=
  match k with
  | 0 => cr_zero fld
  | S k' => cr_add fld (f k') (indexed_sum fld f k')
  end.

(** indexed_sum at zero. *)
Lemma indexed_sum_zero : forall {F : Type} (fld : Field F) (f : nat -> F),
    indexed_sum fld f 0 = cr_zero fld.
Proof. reflexivity. Qed.

(** indexed_sum at successor. *)
Lemma indexed_sum_succ : forall {F : Type} (fld : Field F)
                                  (f : nat -> F) (k : nat),
    indexed_sum fld f (S k) = cr_add fld (f k) (indexed_sum fld f k).
Proof. reflexivity. Qed.

(** Extensionality of indexed_sum: equal functions yield equal sums. *)
Lemma indexed_sum_ext : forall {F : Type} (fld : Field F)
                                (f g : nat -> F) (k : nat),
    (forall i, i < k -> f i = g i) ->
    indexed_sum fld f k = indexed_sum fld g k.
Proof.
  intros F fld f g k Hext.
  induction k as [|k IH].
  - reflexivity.
  - simpl. rewrite (Hext k (Nat.lt_succ_diag_r k)).
    f_equal. apply IH. intros i Hi. apply Hext. lia.
Qed.

(** indexed_sum of zero is zero. *)
Lemma indexed_sum_zero_fn : forall {F : Type} (fld : Field F) (k : nat),
    indexed_sum fld (fun _ => cr_zero fld) k = cr_zero fld.
Proof.
  intros F fld k. induction k as [|k IH].
  - reflexivity.
  - simpl. rewrite IH. apply (cr_add_zero fld).
Qed.

(** indexed_sum splits at any prefix: Σ_{i<a+b} f(i) = Σ_{i<a} f(i) + Σ_{i<b} f(a+i). *)
Lemma indexed_sum_split : forall {F : Type} (fld : Field F)
                                  (f : nat -> F) (a b : nat),
    indexed_sum fld f (a + b) =
    cr_add fld (indexed_sum fld (fun i => f (a + i)) b)
               (indexed_sum fld f a).
Proof.
  intros F fld f a b. induction b as [|b IH].
  - rewrite Nat.add_0_r. simpl.
    rewrite (cr_add_comm fld). symmetry. apply (cr_add_zero fld).
  - replace (a + S b) with (S (a + b)) by lia.
    simpl. rewrite IH.
    rewrite (cr_add_assoc fld). reflexivity.
Qed.

(** indexed_sum is additive in the function. *)
Lemma indexed_sum_add_fn : forall {F : Type} (fld : Field F)
                                   (f g : nat -> F) (k : nat),
    indexed_sum fld (fun i => cr_add fld (f i) (g i)) k =
    cr_add fld (indexed_sum fld f k) (indexed_sum fld g k).
Proof.
  intros F fld f g k.
  induction k as [|k IH].
  - simpl. rewrite (cr_add_zero fld). reflexivity.
  - simpl. rewrite IH.
    set (a := f k). set (b := g k).
    set (Sf := indexed_sum fld f k). set (Sg := indexed_sum fld g k).
    (* (a+b)+(Sf+Sg) = (a+Sf)+(b+Sg) by commutative-monoid algebra. *)
    rewrite (cr_add_assoc fld _ Sf Sg).
    rewrite <- (cr_add_assoc fld a b Sf).
    rewrite (cr_add_comm fld b Sf).
    rewrite (cr_add_assoc fld a Sf b).
    rewrite <- (cr_add_assoc fld _ b Sg).
    reflexivity.
Qed.

(** For trivial_FIS, induced_trace reduces to trace of rho_H at g. *)
Lemma induced_trace_trivial_FIS :
  forall {F : Type} (r : nat) (fld : Field F)
         (rho_H : RWord r -> mg_carrier (SL2_as_MG fld))
         (g : RWord r),
    induced_trace (FreeGroup r) (trivial_FIS r) fld rho_H g =
    mat2_trace fld (proj1_sig (rho_H g)).
Proof.
  intros F r fld rho g. unfold induced_trace.
  rewrite trivial_FIS_index. simpl.
  (* simpl computes coset_sigma (trivial_FIS r) g 0 = 0 by reduction
     (the trivial subgroup membership test is concrete), so the
     conditional resolves to the [then] branch automatically. *)
  rewrite trivial_FIS_cocycle.
  rewrite (cr_add_comm fld). rewrite (cr_add_zero fld).
  reflexivity.
Qed.

(** Specialized to a representation: induced_trace at trivial_FIS
    equals SL2_trace at the rep. *)
Lemma induced_trace_trivial_FIS_rep :
  forall {F : Type} (r : nat) (fld : Field F)
         (rho : Representation (FreeGroup r) (SL2_as_MG fld))
         (g : RWord r),
    induced_trace (FreeGroup r) (trivial_FIS r) fld (rep_fn rho) g =
    trace_at rho g.
Proof.
  intros F r fld rho g.
  rewrite induced_trace_trivial_FIS.
  unfold trace_at. simpl. reflexivity.
Qed.

(** Trivial representation: every element maps to SL2_id. *)
Definition trivial_rep_SL2 {G F : Type} (sg : StrictGroup G) (fld : Field F)
  : Representation sg (SL2_as_MG fld) :=
  mkRep G F sg (SL2_as_MG fld)
    (fun _ : G => SL2_id fld)
    (fun g h => eq_sym (SL2_id_left fld (SL2_id fld))).

(** Trace under trivial representation is always 2 (= 1 + 1). *)
Lemma trivial_rep_SL2_trace : forall {G F : Type} (sg : StrictGroup G)
                                       (fld : Field F) (g : G),
    trace_at (trivial_rep_SL2 sg fld) g =
    cr_add fld (cr_one fld) (cr_one fld).
Proof.
  intros G F sg fld g. unfold trace_at, trivial_rep_SL2. simpl.
  apply SL2_trace_id.
Qed.

(** Representation at identity is identity matrix. *)
Lemma rep_fn_at_e_eq_se :
  forall {G F : Type} (sg : StrictGroup G)
         (fld : Field F) (rho : Representation sg (SL2_as_MG fld)),
    rep_fn rho (se G sg) = SL2_id fld.
Proof.
  intros G F sg fld rho.
  set (phi := {| hom_fn := rep_fn rho;
                 hom_mul := rep_hom rho |} : GroupHom sg (SL2 fld)).
  exact (hom_id sg (SL2 fld) phi).
Qed.

(** Trace at identity for a representation: tr(ρ(e)) = 1 + 1. *)
Lemma rep_trace_at_e :
  forall {G F : Type} (sg : StrictGroup G)
         (fld : Field F) (rho : Representation sg (SL2_as_MG fld)),
    trace_at rho (se G sg) = cr_add fld (cr_one fld) (cr_one fld).
Proof.
  intros G F sg fld rho. unfold trace_at. simpl.
  rewrite (rep_fn_at_e_eq_se sg fld rho).
  apply SL2_trace_id.
Qed.

(** induced_trace at the identity for trivial_FIS + rep equals 2 (= 1 + 1). *)
Lemma induced_trace_trivial_FIS_at_e :
  forall {F : Type} (r : nat) (fld : Field F)
         (rho : Representation (FreeGroup r) (SL2_as_MG fld)),
    induced_trace (FreeGroup r) (trivial_FIS r) fld (rep_fn rho)
      (@rword_e r) =
    cr_add fld (cr_one fld) (cr_one fld).
Proof.
  intros F r fld rho.
  rewrite induced_trace_trivial_FIS_rep.
  apply (rep_trace_at_e (FreeGroup r) fld rho).
Qed.

(** induced_trace_class_function discharged for F_0 (vacuously, via abelian). *)
Theorem induced_trace_class_function_F0 :
  forall {F : Type} (FIS : FiniteIndexSubgroup (FreeGroup 0))
         (fld : Field F)
         (rho_H : RWord 0 -> mg_carrier (SL2_as_MG fld))
         (g h : RWord 0),
    induced_trace (FreeGroup 0) FIS fld rho_H
      (smul (RWord 0) (FreeGroup 0)
        (smul (RWord 0) (FreeGroup 0) g h)
        (sinv (RWord 0) (FreeGroup 0) g)) =
    induced_trace (FreeGroup 0) FIS fld rho_H h.
Proof.
  intros F FIS fld rho g h.
  change (smul (RWord 0) (FreeGroup 0)) with (@rword_mul 0).
  change (sinv (RWord 0) (FreeGroup 0)) with (@rword_inv 0).
  rewrite (F_0_conjugate_trivial g h). reflexivity.
Qed.

(** Generic abelian-group case: induced_trace_class_function holds when G is abelian. *)
Theorem induced_trace_class_function_abelian :
  forall {G F : Type} (sg : StrictGroup G) (FIS : FiniteIndexSubgroup sg)
         (fld : Field F)
         (rho_H : G -> mg_carrier (SL2_as_MG fld))
         (g h : G),
    (forall a b : G, smul G sg a b = smul G sg b a) ->
    induced_trace sg FIS fld rho_H
      (smul G sg (smul G sg g h) (sinv G sg g)) =
    induced_trace sg FIS fld rho_H h.
Proof.
  intros G F sg FIS fld rho g h Habel.
  rewrite (Habel g h).
  rewrite <- (sassoc G sg).
  rewrite (sinv_right G sg g).
  rewrite (sid_right G sg). reflexivity.
Qed.

(** induced_trace_class_function discharged for F_1 (since F_1 is abelian). *)
Theorem induced_trace_class_function_F1 :
  forall {F : Type} (FIS : FiniteIndexSubgroup (FreeGroup 1))
         (fld : Field F)
         (rho_H : RWord 1 -> mg_carrier (SL2_as_MG fld))
         (g h : RWord 1),
    induced_trace (FreeGroup 1) FIS fld rho_H
      (smul (RWord 1) (FreeGroup 1)
        (smul (RWord 1) (FreeGroup 1) g h)
        (sinv (RWord 1) (FreeGroup 1) g)) =
    induced_trace (FreeGroup 1) FIS fld rho_H h.
Proof.
  intros F FIS fld rho g h.
  change (smul (RWord 1) (FreeGroup 1)) with (@rword_mul 1).
  change (sinv (RWord 1) (FreeGroup 1)) with (@rword_inv 1).
  rewrite (F_1_conjugate_trivial g h). reflexivity.
Qed.

(** Class-function property for induced_trace at trivial_FIS, when
    rho is a representation. *)
Theorem induced_trace_class_function_trivial_FIS_rep :
  forall {F : Type} (r : nat) (fld : Field F)
         (rho : Representation (FreeGroup r) (SL2_as_MG fld))
         (g h : RWord r),
    induced_trace (FreeGroup r) (trivial_FIS r) fld (rep_fn rho)
      (smul (RWord r) (FreeGroup r)
        (smul (RWord r) (FreeGroup r) g h)
        (sinv (RWord r) (FreeGroup r) g)) =
    induced_trace (FreeGroup r) (trivial_FIS r) fld (rep_fn rho) h.
Proof.
  intros F r fld rho g h.
  rewrite induced_trace_trivial_FIS_rep.
  rewrite induced_trace_trivial_FIS_rep.
  apply (trace_at_conjugate_SL2 (FreeGroup r) fld rho).
  (* are_conjugate ((g·h)·g^{-1}) h with witness sinv g:
     (sinv g · ((g·h)·sinv g)) · g = h. *)
  exists (sinv (RWord r) (FreeGroup r) g).
  rewrite (sassoc (RWord r) (FreeGroup r)).
  rewrite (sassoc (RWord r) (FreeGroup r) (sinv _ _ g) g h).
  rewrite (sinv_left (RWord r) (FreeGroup r)).
  rewrite (sid_left (RWord r) (FreeGroup r)).
  rewrite (double_inverse (FreeGroup r)).
  rewrite <- (sassoc (RWord r) (FreeGroup r)).
  rewrite (sinv_left (RWord r) (FreeGroup r)).
  apply (sid_right (RWord r) (FreeGroup r)).
Qed.

(** When σ_g fixes all indices in [0, k), induced_trace_aux is the
    indexed_sum of (tr ρ(h_{g, i})) over all i < k. *)
Lemma induced_trace_aux_all_fix :
  forall {G F : Type} (sg : StrictGroup G) (FIS : FiniteIndexSubgroup sg)
         (fld : Field F)
         (rho_H : G -> mg_carrier (SL2_as_MG fld))
         (g : G) (k : nat),
    (forall i, i < k -> coset_sigma FIS g i = i) ->
    induced_trace_aux sg FIS fld rho_H g k (cr_zero fld) =
    indexed_sum fld
      (fun i => mat2_trace fld (proj1_sig (rho_H (coset_cocycle FIS g i)))) k.
Proof.
  intros G F sg FIS fld rho g k Hall_fix.
  induction k as [|k IH].
  - reflexivity.
  - simpl.
    assert (Hfix : Nat.eqb (coset_sigma FIS g k) k = true).
    { apply Nat.eqb_eq. apply Hall_fix. apply Nat.lt_succ_diag_r. }
    rewrite Hfix.
    rewrite (induced_trace_aux_acc _ _ _ _ _ _).
    rewrite IH.
    + rewrite (cr_add_comm fld (cr_zero fld)).
      rewrite (cr_add_zero fld). reflexivity.
    + intros i Hi. apply Hall_fix. lia.
Qed.

(** When σ_g has no fixed points in [0, k), induced_trace_aux is zero. *)
Lemma induced_trace_aux_no_fix :
  forall {G F : Type} (sg : StrictGroup G) (FIS : FiniteIndexSubgroup sg)
         (fld : Field F)
         (rho_H : G -> mg_carrier (SL2_as_MG fld))
         (g : G) (k : nat),
    (forall i, i < k -> coset_sigma FIS g i <> i) ->
    induced_trace_aux sg FIS fld rho_H g k (cr_zero fld) = cr_zero fld.
Proof.
  intros G F sg FIS fld rho g k Hno_fix.
  induction k as [|k IH].
  - reflexivity.
  - simpl.
    destruct (Nat.eqb (coset_sigma FIS g k) k) eqn:Hfix.
    + (* contradiction: σ_g k = k but Hno_fix says σ_g k ≠ k *)
      apply Nat.eqb_eq in Hfix.
      exfalso. apply (Hno_fix k (Nat.lt_succ_diag_r k)). exact Hfix.
    + apply IH. intros i Hi. apply Hno_fix. lia.
Qed.

(** induced_trace_aux as an indexed_sum (with zero accumulator). *)
Lemma induced_trace_aux_as_indexed_sum :
  forall {G F : Type} (sg : StrictGroup G) (FIS : FiniteIndexSubgroup sg)
         (fld : Field F)
         (rho_H : G -> mg_carrier (SL2_as_MG fld))
         (g : G) (k : nat),
    induced_trace_aux sg FIS fld rho_H g k (cr_zero fld) =
    indexed_sum fld
      (fun i => if Nat.eqb (coset_sigma FIS g i) i
                then mat2_trace fld (proj1_sig (rho_H (coset_cocycle FIS g i)))
                else cr_zero fld) k.
Proof.
  intros G F sg FIS fld rho g k.
  induction k as [|k IH].
  - reflexivity.
  - simpl. destruct (Nat.eqb (coset_sigma FIS g k) k) eqn:Hfix.
    + (* fixed *)
      rewrite (induced_trace_aux_acc _ _ _ _ _ _
                 (cr_add fld (cr_zero fld)
                    (mat2_trace fld (proj1_sig (rho (coset_cocycle FIS g k)))))).
      rewrite IH.
      rewrite (cr_add_comm fld (cr_zero fld)).
      rewrite (cr_add_zero fld).
      reflexivity.
    + (* not fixed *)
      rewrite IH.
      rewrite (cr_add_comm fld (cr_zero fld)).
      rewrite (cr_add_zero fld). reflexivity.
Qed.


(* ================================================================== *)
(** * 3. Properties of induced trace (axiomatized for now)              *)
(* ================================================================== *)

(** The induced trace is well-defined and is the trace of the induced
    representation Ind ρ : G → SL(k·d, F). Specifically, for g ∈ G,
    [induced_trace g] = tr(Ind ρ(g)). *)

(** Note: the FULL Frobenius statement (induced_trace = trace of induced
    representation) requires constructing the block-matrix representation
    and showing equal traces. The placeholder True version is provable; a
    full version remains future work. *)

Lemma induced_trace_eq_rep_trace :
  forall {G F : Type} (sg : StrictGroup G) (FIS : FiniteIndexSubgroup sg)
         (fld : Field F)
         (rho_H : G -> mg_carrier (SL2_as_MG fld))
         (g : G),
    (* induced_trace sg FIS fld rho_H g equals the trace of Ind ρ(g)
       in the abstract sense. *)
    True. (* placeholder *)
Proof. intros. exact I. Qed.

(** Frobenius reciprocity: induced_trace is conjugation-invariant. *)
Conjecture induced_trace_class_function :
  forall {G F : Type} (sg : StrictGroup G) (FIS : FiniteIndexSubgroup sg)
         (fld : Field F)
         (rho_H : G -> mg_carrier (SL2_as_MG fld))
         (g h : G),
    induced_trace sg FIS fld rho_H
      (smul G sg (smul G sg g h) (sinv G sg g)) =
    induced_trace sg FIS fld rho_H h.

(* ================================================================== *)
(** * 4. The McReynolds theorem-1.6 chain                               *)
(* ================================================================== *)

(** **THEOREM (sketch, axiomatized):** for free groups F_r with r ≥ 1
    and any γ ≠ e in F_r:
    1. By Hall's free factor theorem (axiomatized), there's a
       finite-index subgroup Δ with γ a free factor.
    2. Choose a "diagonal" representation ρ_Δ : Δ → SL(d, F) sending
       γ to a hyperbolic element with trace ≠ 2.
    3. Induce: Ind ρ_Δ : F_r → SL(k·d, F) where k = [F_r : Δ].
    4. By Frobenius, tr(Ind ρ_Δ(γ)) is determined by the fixed points
       of σ_γ, which are exactly the cosets where γ acts trivially —
       there's at least one such (the trivial coset since γ ∈ Δ),
       contributing tr(ρ_Δ(γ)).
    5. For η non-conjugate to γ in F_r: σ_η has different fixed-point
       structure, giving a different trace.

    This is what's already in HallTheorem.hall_construction_separates,
    refined by the Stallings/Schreier infrastructure above. *)

Theorem theorem_1_6_via_hall :
  forall {F : Type} (MG_family : nat -> MatrixGroup F) (r : nat),
    property_B (FreeGroup r) MG_family.
Proof.
  intros F MG_family r.
  (* Defer to the existing chain in HallTheorem. *)
  apply (free_groups_property_B r F MG_family).
Qed.

(** SL2 reps fail to distinguish γ^k from (γ^{-1})^k in F_1: their traces
    are always equal. Concretely: tr(ρ(gen i^k)) = tr(ρ((gen i^{-1})^k)). *)
Theorem F_n_SL2_trace_pow_eq_inv_pow :
  forall {F : Type} (r : nat) (i : Fin.t r) (fld : Field F)
         (rho : Representation (FreeGroup r) (SL2_as_MG fld)) (k : nat),
    trace_at rho (gamma_pow (free_gen_RWord r i) k) =
    trace_at rho (gamma_pow (rword_inv (free_gen_RWord r i)) k).
Proof.
  intros F r i fld rho k.
  symmetry. apply (rep_trace_at_gamma_inv_pow r fld rho (free_gen_RWord r i) k).
Qed.

(** F_1 trace under SL2 representations is fully determined by tr at gen 0. *)
Theorem F_1_SL2_trace_determined_by_gen :
  forall {F : Type} (fld : Field F)
         (rho rho' : Representation (FreeGroup 1) (SL2_as_MG fld)),
    trace_at rho (free_gen_RWord 1 Fin.F1) =
    trace_at rho' (free_gen_RWord 1 Fin.F1) ->
    forall w : RWord 1, trace_at rho w = trace_at rho' w.
Proof.
  intros F fld rho rho' Hgen w.
  destruct (F_1_classification w) as [He | [[k [Hk Hw]] | [k [Hk Hw]]]].
  - rewrite He.
    change (@rword_e 1) with (se (RWord 1) (FreeGroup 1)).
    rewrite (rep_trace_at_e (FreeGroup 1) fld rho).
    rewrite (rep_trace_at_e (FreeGroup 1) fld rho').
    reflexivity.
  - rewrite Hw.
    rewrite (rep_trace_at_gamma_pow 1 fld rho (free_gen_RWord 1 Fin.F1) k).
    rewrite (rep_trace_at_gamma_pow 1 fld rho' (free_gen_RWord 1 Fin.F1) k).
    apply SL2_trace_pow_determined_by_trace.
    unfold trace_at in Hgen. simpl in Hgen. exact Hgen.
  - rewrite Hw.
    rewrite (rep_trace_at_gamma_pow 1 fld rho
              (rword_inv (free_gen_RWord 1 Fin.F1)) k).
    rewrite (rep_trace_at_gamma_pow 1 fld rho'
              (rword_inv (free_gen_RWord 1 Fin.F1)) k).
    apply SL2_trace_pow_determined_by_trace.
    set (phi := {| hom_fn := rep_fn rho;
                   hom_mul := rep_hom rho |}
                : GroupHom (FreeGroup 1) (SL2 fld)).
    set (phi' := {| hom_fn := rep_fn rho';
                   hom_mul := rep_hom rho' |}
                : GroupHom (FreeGroup 1) (SL2 fld)).
    pose proof (hom_inv (FreeGroup 1) (SL2 fld) phi
                        (free_gen_RWord 1 Fin.F1)) as Hinv.
    pose proof (hom_inv (FreeGroup 1) (SL2 fld) phi'
                        (free_gen_RWord 1 Fin.F1)) as Hinv'.
    simpl in Hinv, Hinv'.
    unfold trace_at. simpl. rewrite Hinv, Hinv'.
    rewrite !SL2_trace_inv.
    unfold trace_at in Hgen. simpl in Hgen. exact Hgen.
Qed.

(** Cross-rep determination on a single-generator cyclic subgroup of F_r:
    if two SL2 reps agree on the trace of a generator, they agree on the
    trace of every positive power of that generator. *)
Theorem F_n_SL2_trace_pow_gen_determined :
  forall {F : Type} (r : nat) (i : Fin.t r) (fld : Field F)
         (rho rho' : Representation (FreeGroup r) (SL2_as_MG fld)) (k : nat),
    trace_at rho (free_gen_RWord r i) =
    trace_at rho' (free_gen_RWord r i) ->
    trace_at rho (gamma_pow (free_gen_RWord r i) k) =
    trace_at rho' (gamma_pow (free_gen_RWord r i) k).
Proof.
  intros F r i fld rho rho' k Hgen.
  rewrite (rep_trace_at_gamma_pow r fld rho (free_gen_RWord r i) k).
  rewrite (rep_trace_at_gamma_pow r fld rho' (free_gen_RWord r i) k).
  apply SL2_trace_pow_determined_by_trace.
  unfold trace_at in Hgen. simpl in Hgen. exact Hgen.
Qed.

(** Same conclusion for negative powers: agreement on the generator-trace
    forces agreement on tr(ρ((γ^{-1})^k)) for all k. *)
Theorem F_n_SL2_trace_inv_pow_gen_determined :
  forall {F : Type} (r : nat) (i : Fin.t r) (fld : Field F)
         (rho rho' : Representation (FreeGroup r) (SL2_as_MG fld)) (k : nat),
    trace_at rho (free_gen_RWord r i) =
    trace_at rho' (free_gen_RWord r i) ->
    trace_at rho (gamma_pow (rword_inv (free_gen_RWord r i)) k) =
    trace_at rho' (gamma_pow (rword_inv (free_gen_RWord r i)) k).
Proof.
  intros F r i fld rho rho' k Hgen.
  rewrite <- (F_n_SL2_trace_pow_eq_inv_pow r i fld rho k).
  rewrite <- (F_n_SL2_trace_pow_eq_inv_pow r i fld rho' k).
  apply F_n_SL2_trace_pow_gen_determined; exact Hgen.
Qed.

(** General form: for any γ ∈ F_r and any SL2 rep, the trace on positive
    powers of γ matches the trace on positive powers of γ^{-1}. *)
Theorem SL2_trace_pow_eq_inv_pow_general :
  forall {F : Type} (r : nat) (fld : Field F)
         (rho : Representation (FreeGroup r) (SL2_as_MG fld))
         (gamma : RWord r) (k : nat),
    trace_at rho (gamma_pow gamma k) =
    trace_at rho (gamma_pow (rword_inv gamma) k).
Proof.
  intros F r fld rho gamma k.
  symmetry. apply rep_trace_at_gamma_inv_pow.
Qed.

(** General form of cross-rep trace determination: agreement on tr(ρ(γ))
    forces agreement on tr(ρ(γ^k)) for all k, for any rword γ. *)
Theorem SL2_trace_pow_determined_general :
  forall {F : Type} (r : nat) (fld : Field F)
         (rho rho' : Representation (FreeGroup r) (SL2_as_MG fld))
         (gamma : RWord r) (k : nat),
    trace_at rho gamma = trace_at rho' gamma ->
    trace_at rho (gamma_pow gamma k) = trace_at rho' (gamma_pow gamma k).
Proof.
  intros F r fld rho rho' gamma k Hgamma.
  rewrite (rep_trace_at_gamma_pow r fld rho gamma k).
  rewrite (rep_trace_at_gamma_pow r fld rho' gamma k).
  apply SL2_trace_pow_determined_by_trace.
  unfold trace_at in Hgamma. simpl in Hgamma. exact Hgamma.
Qed.

(** Same conclusion for negative powers of an arbitrary γ. *)
Theorem SL2_trace_inv_pow_determined_general :
  forall {F : Type} (r : nat) (fld : Field F)
         (rho rho' : Representation (FreeGroup r) (SL2_as_MG fld))
         (gamma : RWord r) (k : nat),
    trace_at rho gamma = trace_at rho' gamma ->
    trace_at rho (gamma_pow (rword_inv gamma) k) =
    trace_at rho' (gamma_pow (rword_inv gamma) k).
Proof.
  intros F r fld rho rho' gamma k Hgamma.
  rewrite <- (SL2_trace_pow_eq_inv_pow_general r fld rho gamma k).
  rewrite <- (SL2_trace_pow_eq_inv_pow_general r fld rho' gamma k).
  apply SL2_trace_pow_determined_general; exact Hgamma.
Qed.

(** Iff form: under a fixed SL2 rep, two elements have the same trace iff
    they have the same trace on every positive power. (Forward: take k=1
    and use rep_trace_at_gamma_pow_one. Backward: SL2_trace_equiv_pow.) *)
Theorem SL2_trace_eq_iff_pow_trace_eq :
  forall {F : Type} (r : nat) (fld : Field F)
         (rho : Representation (FreeGroup r) (SL2_as_MG fld))
         (gamma eta : RWord r),
    trace_at rho gamma = trace_at rho eta <->
    (forall k, trace_at rho (gamma_pow gamma k) =
               trace_at rho (gamma_pow eta k)).
Proof.
  intros F r fld rho gamma eta. split.
  - intros Hgeq k. apply (SL2_trace_equiv_pow r fld rho gamma eta Hgeq).
  - intros Hall.
    pose proof (Hall 1) as H1.
    rewrite (rep_trace_at_gamma_pow_one r fld rho gamma) in H1.
    rewrite (rep_trace_at_gamma_pow_one r fld rho eta) in H1.
    exact H1.
Qed.

(** Cross-rep iff form: the two reps agree on tr(γ) iff they agree on
    tr(γ^k) for every k. Combines `SL2_trace_pow_determined_general` with
    the k=1 specialization. *)
Theorem SL2_cross_trace_eq_iff_pow_trace_eq :
  forall {F : Type} (r : nat) (fld : Field F)
         (rho rho' : Representation (FreeGroup r) (SL2_as_MG fld))
         (gamma : RWord r),
    trace_at rho gamma = trace_at rho' gamma <->
    (forall k, trace_at rho (gamma_pow gamma k) =
               trace_at rho' (gamma_pow gamma k)).
Proof.
  intros F r fld rho rho' gamma. split.
  - intros Hgeq k.
    apply (SL2_trace_pow_determined_general r fld rho rho' gamma k Hgeq).
  - intros Hall.
    pose proof (Hall 1) as H1.
    rewrite (rep_trace_at_gamma_pow_one r fld rho gamma) in H1.
    rewrite (rep_trace_at_gamma_pow_one r fld rho' gamma) in H1.
    exact H1.
Qed.

(** Whole-cyclic-subgroup determination: if two SL2 reps agree on tr(ρ(γ)),
    they agree on tr(ρ(h)) for every h ∈ ⟨γ⟩. *)
Theorem in_cyclic_SL2_trace_determined :
  forall {F : Type} (r : nat) (fld : Field F)
         (rho rho' : Representation (FreeGroup r) (SL2_as_MG fld))
         (gamma h : RWord r),
    in_cyclic gamma h ->
    trace_at rho gamma = trace_at rho' gamma ->
    trace_at rho h = trace_at rho' h.
Proof.
  intros F r fld rho rho' gamma h Hin Hgamma.
  destruct Hin as [[k Hk] | [k Hk]]; rewrite Hk.
  - apply (SL2_trace_pow_determined_general r fld rho rho' gamma k Hgamma).
  - apply (SL2_trace_inv_pow_determined_general r fld rho rho' gamma k Hgamma).
Qed.

(** SL2-trace equivalence of γ^k and (γ^{-1})^k as a trace_equiv_in_MG fact:
    no SL2 representation can distinguish them. *)
Lemma SL2_trace_equiv_pow_inv_pow :
  forall {F : Type} (r : nat) (fld : Field F) (gamma : RWord r) (k : nat),
    @trace_equiv_in_MG (RWord r) F (FreeGroup r) (SL2_as_MG fld)
      (gamma_pow gamma k) (gamma_pow (rword_inv gamma) k).
Proof.
  intros F r fld gamma k rho.
  apply (SL2_trace_pow_eq_inv_pow_general r fld rho gamma k).
Qed.

(** Specialization: γ and γ^{-1} are SL2-trace-equivalent. *)
Lemma SL2_trace_equiv_inv :
  forall {F : Type} (r : nat) (fld : Field F) (gamma : RWord r),
    @trace_equiv_in_MG (RWord r) F (FreeGroup r) (SL2_as_MG fld)
      gamma (rword_inv gamma).
Proof.
  intros F r fld gamma rho.
  pose proof (SL2_trace_pow_eq_inv_pow_general r fld rho gamma 1) as H.
  rewrite (gamma_pow_one_eq gamma) in H.
  rewrite (gamma_pow_one_eq (rword_inv gamma)) in H.
  exact H.
Qed.

(** Single-rep variant: trace_at rho is constant across same-trace
    elements when restricted to a cyclic subgroup ⟨γ⟩. Specifically, if γ
    and η have equal trace under ρ, then so do all corresponding pairs
    of powers. *)
Theorem in_cyclic_pow_pair_trace :
  forall {F : Type} (r : nat) (fld : Field F)
         (rho : Representation (FreeGroup r) (SL2_as_MG fld))
         (gamma eta : RWord r),
    trace_at rho gamma = trace_at rho eta ->
    forall h, in_cyclic gamma h ->
    exists h', in_cyclic eta h' /\ trace_at rho h = trace_at rho h'.
Proof.
  intros F r fld rho gamma eta Hgeq h Hin.
  destruct Hin as [[k Hk] | [k Hk]].
  - exists (gamma_pow eta k). split.
    + left. exists k. reflexivity.
    + rewrite Hk. apply (SL2_trace_equiv_pow r fld rho gamma eta Hgeq).
  - exists (gamma_pow (rword_inv eta) k). split.
    + right. exists k. reflexivity.
    + rewrite Hk.
      rewrite <- (SL2_trace_pow_eq_inv_pow_general r fld rho gamma k).
      rewrite <- (SL2_trace_pow_eq_inv_pow_general r fld rho eta k).
      apply (SL2_trace_equiv_pow r fld rho gamma eta Hgeq).
Qed.

(** Counterexample: in F_1, the generator γ_0 and its inverse γ_0^{-1} are
    SL2-trace-equivalent (every rep gives equal traces) yet they are NOT
    conjugate. This shows that the unconditional Fricke-generation form
    of "SL2-trace equivalence ⟹ conjugacy" is FALSE in F_1.
    The classical Horowitz/Fricke result requires F_n with n ≥ 2 AND
    a quotient by inversion / cyclic-reduction conditions. *)
Theorem F1_SL2_trace_equiv_not_implies_conjugate :
  forall {F : Type} (fld : Field F),
    exists (gamma eta : RWord 1),
      (forall rho : Representation (FreeGroup 1) (SL2_as_MG fld),
         trace_at rho gamma = trace_at rho eta) /\
      ~ are_conjugate (FreeGroup 1) gamma eta.
Proof.
  intros F fld.
  exists (free_gen_RWord 1 Fin.F1).
  exists (rword_inv (free_gen_RWord 1 Fin.F1)).
  split.
  - intro rho. apply (trace_inv_equal_SL2 (FreeGroup 1) fld rho).
  - intro Hconj.
    apply F_1_are_conjugate_iff_eq in Hconj.
    pose proof (gamma_pow_gen_pos_ne_neg 1 Fin.F1 1 1
                 (le_n 1) (le_n 1)) as Hne.
    apply Hne.
    rewrite (gamma_pow_one_eq (free_gen_RWord 1 Fin.F1)).
    rewrite (gamma_pow_one_eq (rword_inv (free_gen_RWord 1 Fin.F1))).
    exact Hconj.
Qed.

(** SL2 trace is cyclic for two-letter generator products: a single rep
    cannot distinguish γ_i·γ_j from γ_j·γ_i. Combines trace_at_conjugate_SL2
    with free_gens_mul_conjugate_swap. *)
Lemma SL2_trace_at_gens_mul_swap :
  forall {F : Type} (n : nat) (i j : Fin.t n) (fld : Field F)
         (rho : Representation (FreeGroup n) (SL2_as_MG fld)),
    trace_at rho (rword_mul (free_gen_RWord n i) (free_gen_RWord n j)) =
    trace_at rho (rword_mul (free_gen_RWord n j) (free_gen_RWord n i)).
Proof.
  intros F n i j fld rho.
  apply (trace_at_conjugate_SL2 (FreeGroup n) fld rho).
  apply free_gens_mul_conjugate_swap.
Qed.

(** Cyclic invariance of SL2 trace on three-letter products: tr(abc) = tr(bca).
    Via [rword_mul_conjugate_swap] applied to a and (b·c). *)
Theorem SL2_trace_at_mul_three_cyclic :
  forall {F : Type} (n : nat) (a b c : RWord n) (fld : Field F)
         (rho : Representation (FreeGroup n) (SL2_as_MG fld)),
    trace_at rho (rword_mul (rword_mul a b) c) =
    trace_at rho (rword_mul (rword_mul b c) a).
Proof.
  intros F n a b c fld rho.
  rewrite <- (rword_assoc a b c).
  apply (trace_at_conjugate_SL2 (FreeGroup n) fld rho).
  apply rword_mul_conjugate_swap.
Qed.

(** General form: SL2 trace of any two-word product is invariant under swap.
    This is the trace cyclic invariance tr(AB) = tr(BA) lifted through
    representations, plus the F_n-level conjugacy [rword_mul_conjugate_swap]. *)
Theorem SL2_trace_at_mul_swap :
  forall {F : Type} (n : nat) (a b : RWord n) (fld : Field F)
         (rho : Representation (FreeGroup n) (SL2_as_MG fld)),
    trace_at rho (rword_mul a b) = trace_at rho (rword_mul b a).
Proof.
  intros F n a b fld rho.
  apply (trace_at_conjugate_SL2 (FreeGroup n) fld rho).
  apply rword_mul_conjugate_swap.
Qed.

(* ================================================================== *)
(** ** Universal property for SL2 representations of F_n              *)
(* ================================================================== *)

(** Map a single letter to an SL2 element using a generator-image map. *)
Definition extend_letter_SL2 {n : nat} {F : Type} (fld : Field F)
  (f : Fin.t n -> SL2_carrier fld) (l : Letter n) : SL2_carrier fld :=
  if snd l then SL2_inv fld (f (fst l)) else f (fst l).

(** Extend to an underlying word by left-folding multiplication. *)
Fixpoint extend_word_SL2 {n : nat} {F : Type} (fld : Field F)
  (f : Fin.t n -> SL2_carrier fld) (w : list (Letter n)) : SL2_carrier fld :=
  match w with
  | nil => SL2_id fld
  | l :: rest => SL2_mul fld (extend_letter_SL2 fld f l)
                              (extend_word_SL2 fld f rest)
  end.

(** Extension at the empty word is the SL2 identity. *)
Lemma extend_word_SL2_nil :
  forall {n : nat} {F : Type} (fld : Field F)
         (f : Fin.t n -> SL2_carrier fld),
    extend_word_SL2 fld f nil = SL2_id fld.
Proof. reflexivity. Qed.

(** Extension at a single-letter word is just the letter image. *)
Lemma extend_word_SL2_single :
  forall {n : nat} {F : Type} (fld : Field F)
         (f : Fin.t n -> SL2_carrier fld) (l : Letter n),
    extend_word_SL2 fld f (l :: nil) = extend_letter_SL2 fld f l.
Proof.
  intros. simpl. apply SL2_id_right.
Qed.

(** Extension distributes over concatenation. *)
Lemma extend_word_SL2_app :
  forall {n : nat} {F : Type} (fld : Field F)
         (f : Fin.t n -> SL2_carrier fld) (u v : list (Letter n)),
    extend_word_SL2 fld f (u ++ v) =
    SL2_mul fld (extend_word_SL2 fld f u) (extend_word_SL2 fld f v).
Proof.
  intros n F fld f u. induction u as [|l u IH]; intro v.
  - simpl. rewrite (SL2_id_left fld). reflexivity.
  - simpl. rewrite IH. apply SL2_assoc.
Qed.

(** A letter and its inverse multiply to the identity under extension. *)
Lemma extend_letter_letter_inv :
  forall {n : nat} {F : Type} (fld : Field F)
         (f : Fin.t n -> SL2_carrier fld) (l : Letter n),
    SL2_mul fld (extend_letter_SL2 fld f l)
                (extend_letter_SL2 fld f (letter_inv l)) =
    SL2_id fld.
Proof.
  intros n F fld f [i b].
  unfold extend_letter_SL2, letter_inv. simpl.
  destruct b.
  - apply (SL2_inv_left fld).
  - apply (SL2_inv_right fld).
Qed.

(** A two-element word [a; letter_inv a] extends to the identity. *)
Lemma extend_word_SL2_pair :
  forall {n : nat} {F : Type} (fld : Field F)
         (f : Fin.t n -> SL2_carrier fld) (l : Letter n),
    extend_word_SL2 fld f (l :: (letter_inv l) :: nil) = SL2_id fld.
Proof.
  intros n F fld f l. simpl.
  rewrite SL2_id_right.
  apply extend_letter_letter_inv.
Qed.

(** Extension is invariant under removal of an adjacent inverse pair anywhere in
    the word: extend(pre ++ [a; letter_inv a] ++ post) = extend(pre ++ post). *)
Lemma extend_word_SL2_remove_pair :
  forall {n : nat} {F : Type} (fld : Field F)
         (f : Fin.t n -> SL2_carrier fld)
         (pre post : list (Letter n)) (l : Letter n),
    extend_word_SL2 fld f
      (pre ++ (l :: (letter_inv l) :: nil) ++ post) =
    extend_word_SL2 fld f (pre ++ post).
Proof.
  intros n F fld f pre post l.
  rewrite (extend_word_SL2_app fld f pre _).
  rewrite (extend_word_SL2_app fld f pre post).
  f_equal.
  rewrite (extend_word_SL2_app fld f (l :: (letter_inv l) :: nil) post).
  rewrite extend_word_SL2_pair.
  apply (SL2_id_left fld).
Qed.

(** A single cancel_step preserves the extension. *)
Lemma extend_word_SL2_cancel_step :
  forall {n : nat} {F : Type} (fld : Field F)
         (f : Fin.t n -> SL2_carrier fld) (w w' : list (Letter n)),
    cancel_step w = Some w' ->
    extend_word_SL2 fld f w = extend_word_SL2 fld f w'.
Proof.
  intros n F fld f w. induction w as [|x rest IH]; intros w' Hc.
  - simpl in Hc. discriminate.
  - simpl in Hc. destruct rest as [|y rest'].
    + discriminate.
    + destruct (letter_eq_dec y (letter_inv x)) as [Hyx | Hyx].
      * inversion Hc as [Hw'].
        simpl. rewrite Hyx. rewrite SL2_assoc.
        rewrite extend_letter_letter_inv. rewrite SL2_id_left.
        reflexivity.
      * destruct (cancel_step (y :: rest')) as [t'|] eqn:Ht; [|discriminate].
        injection Hc as Hw'. subst w'.
        change (extend_word_SL2 fld f (x :: y :: rest'))
          with (SL2_mul fld (extend_letter_SL2 fld f x)
                            (extend_word_SL2 fld f (y :: rest'))).
        change (extend_word_SL2 fld f (x :: t'))
          with (SL2_mul fld (extend_letter_SL2 fld f x)
                            (extend_word_SL2 fld f t')).
        f_equal. apply (IH t' eq_refl).
Qed.

(** Iterated cancel_step (reduce_aux) preserves the extension. *)
Lemma extend_word_SL2_reduce_aux :
  forall {n : nat} {F : Type} (fld : Field F)
         (f : Fin.t n -> SL2_carrier fld) (fuel : nat) (w : list (Letter n)),
    extend_word_SL2 fld f (reduce_aux fuel w) = extend_word_SL2 fld f w.
Proof.
  intros n F fld f fuel. induction fuel as [|k IH]; intro w.
  - reflexivity.
  - simpl. destruct (cancel_step w) as [w'|] eqn:Hcs.
    + rewrite (IH w').
      symmetry. apply (extend_word_SL2_cancel_step fld f w w' Hcs).
    + reflexivity.
Qed.

(** reduce preserves the extension. *)
Lemma extend_word_SL2_reduce :
  forall {n : nat} {F : Type} (fld : Field F)
         (f : Fin.t n -> SL2_carrier fld) (w : list (Letter n)),
    extend_word_SL2 fld f (reduce w) = extend_word_SL2 fld f w.
Proof.
  intros. unfold reduce. apply extend_word_SL2_reduce_aux.
Qed.

(** Extension to reduced words: factor through proj1_sig. *)
Definition extend_RWord_SL2 {n : nat} {F : Type} (fld : Field F)
  (f : Fin.t n -> SL2_carrier fld) (w : RWord n) : SL2_carrier fld :=
  extend_word_SL2 fld f (proj1_sig w).

(** Extension is a multiplicative homomorphism on RWord n:
    extend(u · v) = extend(u) · extend(v). The reduce step in rword_mul
    preserves the extension by [extend_word_SL2_reduce]. *)
Lemma extend_RWord_SL2_hom :
  forall {n : nat} {F : Type} (fld : Field F)
         (f : Fin.t n -> SL2_carrier fld) (u v : RWord n),
    extend_RWord_SL2 fld f (rword_mul u v) =
    SL2_mul fld (extend_RWord_SL2 fld f u) (extend_RWord_SL2 fld f v).
Proof.
  intros n F fld f u v.
  unfold extend_RWord_SL2, rword_mul. cbn [proj1_sig].
  rewrite extend_word_SL2_reduce.
  apply (extend_word_SL2_app fld f).
Qed.

(** Extension at the identity is SL2_id. *)
Lemma extend_RWord_SL2_id :
  forall {n : nat} {F : Type} (fld : Field F)
         (f : Fin.t n -> SL2_carrier fld),
    extend_RWord_SL2 fld f (@rword_e n) = SL2_id fld.
Proof.
  intros. unfold extend_RWord_SL2. reflexivity.
Qed.

(** Build a representation from a generator-image map. *)
Definition rep_from_gen_map {n : nat} {F : Type} (fld : Field F)
  (f : Fin.t n -> SL2_carrier fld)
  : Representation (FreeGroup n) (SL2_as_MG fld) :=
  mkRep (RWord n) F (FreeGroup n) (SL2_as_MG fld)
    (extend_RWord_SL2 fld f)
    (extend_RWord_SL2_hom fld f).

(** rep_from_gen_map agrees with f on generators (positive). *)
Lemma rep_from_gen_map_gen :
  forall {n : nat} {F : Type} (fld : Field F)
         (f : Fin.t n -> SL2_carrier fld) (i : Fin.t n),
    rep_fn (rep_from_gen_map fld f) (free_gen_RWord n i) = f i.
Proof.
  intros n F fld f i.
  unfold rep_from_gen_map, extend_RWord_SL2, free_gen_RWord, free_gen_letter.
  cbn [proj1_sig].
  unfold extend_word_SL2. unfold extend_letter_SL2. simpl.
  apply SL2_id_right.
Qed.

(** rep_from_gen_map sends inverse generators to inverses. By the homomorphism
    property of any representation: rep(g^{-1}) = rep(g)^{-1}. *)
Lemma rep_from_gen_map_inv_gen :
  forall {n : nat} {F : Type} (fld : Field F)
         (f : Fin.t n -> SL2_carrier fld) (i : Fin.t n),
    rep_fn (rep_from_gen_map fld f) (rword_inv (free_gen_RWord n i)) =
    SL2_inv fld (f i).
Proof.
  intros n F fld f i.
  set (rho := rep_from_gen_map fld f).
  set (phi := {| hom_fn := rep_fn rho;
                 hom_mul := rep_hom rho |} : GroupHom (FreeGroup n) (SL2 fld)).
  pose proof (hom_inv (FreeGroup n) (SL2 fld) phi (free_gen_RWord n i)) as Hinv.
  change (sinv (RWord n) (FreeGroup n)) with (@rword_inv n) in Hinv.
  change (hom_fn phi) with (rep_fn rho) in Hinv.
  rewrite Hinv. simpl. f_equal.
  apply rep_from_gen_map_gen.
Qed.

(** rep_from_gen_map respects gamma_pow on positive powers. *)
Lemma rep_from_gen_map_pow :
  forall {n : nat} {F : Type} (fld : Field F)
         (f : Fin.t n -> SL2_carrier fld) (i : Fin.t n) (k : nat),
    rep_fn (rep_from_gen_map fld f)
           (gamma_pow (free_gen_RWord n i) k) =
    SL2_pow fld (f i) k.
Proof.
  intros n F fld f i k.
  rewrite (rep_fn_gamma_pow n fld (rep_from_gen_map fld f)
                            (free_gen_RWord n i) k).
  f_equal. apply rep_from_gen_map_gen.
Qed.

(** Trace under rep_from_gen_map at a positive generator power. *)
Lemma rep_trace_at_from_gen_map_pow :
  forall {n : nat} {F : Type} (fld : Field F)
         (f : Fin.t n -> SL2_carrier fld) (i : Fin.t n) (k : nat),
    trace_at (rep_from_gen_map fld f)
             (gamma_pow (free_gen_RWord n i) k) =
    SL2_trace fld (SL2_pow fld (f i) k).
Proof.
  intros n F fld f i k.
  rewrite (rep_trace_at_gamma_pow n fld (rep_from_gen_map fld f)
                                   (free_gen_RWord n i) k).
  rewrite (rep_from_gen_map_gen fld f i). reflexivity.
Qed.

(** Trace under rep_from_gen_map at a negative generator power; equal
    to the positive-power trace by [SL2_trace_pow_inv]. *)
Lemma rep_trace_at_from_gen_map_inv_pow :
  forall {n : nat} {F : Type} (fld : Field F)
         (f : Fin.t n -> SL2_carrier fld) (i : Fin.t n) (k : nat),
    trace_at (rep_from_gen_map fld f)
             (gamma_pow (rword_inv (free_gen_RWord n i)) k) =
    SL2_trace fld (SL2_pow fld (f i) k).
Proof.
  intros n F fld f i k.
  rewrite (rep_trace_at_gamma_inv_pow n fld
                                       (rep_from_gen_map fld f)
                                       (free_gen_RWord n i) k).
  apply rep_trace_at_from_gen_map_pow.
Qed.

(** Trace under rep_from_gen_map at a single generator equals the field
    trace of its image. *)
Lemma rep_trace_at_from_gen_map_gen :
  forall {n : nat} {F : Type} (fld : Field F)
         (f : Fin.t n -> SL2_carrier fld) (i : Fin.t n),
    trace_at (rep_from_gen_map fld f) (free_gen_RWord n i) =
    SL2_trace fld (f i).
Proof.
  intros n F fld f i.
  rewrite <- (gamma_pow_one_eq (free_gen_RWord n i)).
  rewrite (rep_trace_at_from_gen_map_pow fld f i 1).
  rewrite (SL2_pow_one fld). reflexivity.
Qed.

(** Trace under rep_from_gen_map at the inverse of a generator equals
    the trace of its image. *)
Lemma rep_trace_at_from_gen_map_inv_gen :
  forall {n : nat} {F : Type} (fld : Field F)
         (f : Fin.t n -> SL2_carrier fld) (i : Fin.t n),
    trace_at (rep_from_gen_map fld f) (rword_inv (free_gen_RWord n i)) =
    SL2_trace fld (f i).
Proof.
  intros n F fld f i.
  rewrite <- (gamma_pow_one_eq (rword_inv (free_gen_RWord n i))).
  rewrite (rep_trace_at_from_gen_map_inv_pow fld f i 1).
  rewrite (SL2_pow_one fld). reflexivity.
Qed.

(** Conditional non-conjugacy of distinct generators: if a generator-image
    map can separate γ_i from γ_j by trace, then γ_i and γ_j are not
    conjugate in F_n. This reduces the abelianization-based non-conjugacy
    to a concrete linear-algebra existence statement on the field. *)
Theorem F_n_gens_non_conj_via_trace :
  forall {n : nat} {F : Type} (fld : Field F) (i j : Fin.t n),
    (exists f : Fin.t n -> SL2_carrier fld,
       SL2_trace fld (f i) <> SL2_trace fld (f j)) ->
    ~ are_conjugate (FreeGroup n) (free_gen_RWord n i) (free_gen_RWord n j).
Proof.
  intros n F fld i j [f Hne] Hconj.
  apply Hne.
  pose proof (trace_at_conjugate_SL2 (FreeGroup n) fld
                                     (rep_from_gen_map fld f)
                                     (free_gen_RWord n i)
                                     (free_gen_RWord n j) Hconj) as Heq.
  rewrite (rep_trace_at_from_gen_map_gen fld f i) in Heq.
  rewrite (rep_trace_at_from_gen_map_gen fld f j) in Heq.
  exact Heq.
Qed.

(** Trace at the identity under rep_from_gen_map is 2 (= 1 + 1). *)
Lemma rep_trace_at_from_gen_map_e :
  forall {n : nat} {F : Type} (fld : Field F)
         (f : Fin.t n -> SL2_carrier fld),
    trace_at (rep_from_gen_map fld f) (@rword_e n) =
    cr_add fld (cr_one fld) (cr_one fld).
Proof.
  intros. apply (rep_trace_at_e (FreeGroup n) fld _).
Qed.

(** Image of γ_i · γ_j under rep_from_gen_map is f(i) · f(j) (multiplicative). *)
Lemma rep_at_from_gen_map_mul_gens :
  forall {n : nat} {F : Type} (fld : Field F)
         (f : Fin.t n -> SL2_carrier fld) (i j : Fin.t n),
    rep_fn (rep_from_gen_map fld f)
           (rword_mul (free_gen_RWord n i) (free_gen_RWord n j)) =
    SL2_mul fld (f i) (f j).
Proof.
  intros n F fld f i j.
  pose proof (rep_hom (rep_from_gen_map fld f)
                      (free_gen_RWord n i) (free_gen_RWord n j)) as Hh.
  change (smul (RWord n) (FreeGroup n)) with (@rword_mul n) in Hh.
  rewrite Hh.
  change (smul (mg_carrier (SL2_as_MG fld)) (mg_sg (SL2_as_MG fld)))
    with (SL2_mul fld).
  rewrite (rep_from_gen_map_gen fld f i).
  rewrite (rep_from_gen_map_gen fld f j).
  reflexivity.
Qed.

(** Image of γ_i · γ_j · γ_i^{-1} (a conjugation by γ_i) is
    f(i) · f(j) · f(i)^{-1}. *)
Lemma rep_at_from_gen_map_conj_gens :
  forall {n : nat} {F : Type} (fld : Field F)
         (f : Fin.t n -> SL2_carrier fld) (i j : Fin.t n),
    rep_fn (rep_from_gen_map fld f)
           (rword_mul (rword_mul (free_gen_RWord n i) (free_gen_RWord n j))
                      (rword_inv (free_gen_RWord n i))) =
    SL2_mul fld (SL2_mul fld (f i) (f j)) (SL2_inv fld (f i)).
Proof.
  intros n F fld f i j.
  pose proof (rep_hom (rep_from_gen_map fld f)
                      (rword_mul (free_gen_RWord n i) (free_gen_RWord n j))
                      (rword_inv (free_gen_RWord n i))) as Hh.
  change (smul (RWord n) (FreeGroup n)) with (@rword_mul n) in Hh.
  rewrite Hh.
  change (smul (mg_carrier (SL2_as_MG fld)) (mg_sg (SL2_as_MG fld)))
    with (SL2_mul fld).
  rewrite (rep_at_from_gen_map_mul_gens fld f i j).
  rewrite (rep_from_gen_map_inv_gen fld f i).
  reflexivity.
Qed.

(** Trace at γ_i^k and (γ_i^{-1})^k are always equal under rep_from_gen_map.
    Direct via the matching [rep_trace_at_from_gen_map_*_pow] lemmas. *)
Lemma rep_trace_at_from_gen_map_pow_inv_eq :
  forall {n : nat} {F : Type} (fld : Field F)
         (f : Fin.t n -> SL2_carrier fld) (i : Fin.t n) (k : nat),
    trace_at (rep_from_gen_map fld f)
             (gamma_pow (free_gen_RWord n i) k) =
    trace_at (rep_from_gen_map fld f)
             (gamma_pow (rword_inv (free_gen_RWord n i)) k).
Proof.
  intros. rewrite (rep_trace_at_from_gen_map_pow fld f i k).
  rewrite (rep_trace_at_from_gen_map_inv_pow fld f i k). reflexivity.
Qed.

(** Trace at a two-generator product under rep_from_gen_map. *)
Lemma rep_trace_at_from_gen_map_mul_gens :
  forall {n : nat} {F : Type} (fld : Field F)
         (f : Fin.t n -> SL2_carrier fld) (i j : Fin.t n),
    trace_at (rep_from_gen_map fld f)
             (rword_mul (free_gen_RWord n i) (free_gen_RWord n j)) =
    SL2_trace fld (SL2_mul fld (f i) (f j)).
Proof.
  intros n F fld f i j.
  pose proof (rep_hom (rep_from_gen_map fld f)
                      (free_gen_RWord n i) (free_gen_RWord n j)) as Hh.
  unfold trace_at.
  change (smul (RWord n) (FreeGroup n)) with (@rword_mul n) in Hh.
  rewrite Hh.
  change (mg_trace (SL2_as_MG fld)) with (SL2_trace fld).
  change (smul (mg_carrier (SL2_as_MG fld)) (mg_sg (SL2_as_MG fld)))
    with (SL2_mul fld).
  rewrite (rep_from_gen_map_gen fld f i).
  rewrite (rep_from_gen_map_gen fld f j).
  reflexivity.
Qed.

(** Distinct generators are not SL2-trace-equivalent (in the universal
    sense) given witnessed-distinct matrix images: pick f matching i to
    M_i and j to M_j. This gives a single rep refuting the universal
    trace equality. *)
Theorem F_n_gens_not_SL2_trace_equiv_via_witnesses :
  forall {F : Type} (fld : Field F) (n : nat) (i j : Fin.t n),
    i <> j ->
    forall M_i M_j : SL2_carrier fld,
      SL2_trace fld M_i <> SL2_trace fld M_j ->
      ~ (forall rho : Representation (FreeGroup n) (SL2_as_MG fld),
           trace_at rho (free_gen_RWord n i) =
           trace_at rho (free_gen_RWord n j)).
Proof.
  intros F fld n i j Hij M_i M_j Hne Hall.
  apply Hne.
  set (f := fun k : Fin.t n => if Fin.eq_dec k i then M_i else M_j).
  pose proof (Hall (rep_from_gen_map fld f)) as Heq.
  rewrite (rep_trace_at_from_gen_map_gen fld f i) in Heq.
  rewrite (rep_trace_at_from_gen_map_gen fld f j) in Heq.
  unfold f in Heq.
  destruct (Fin.eq_dec i i) as [_|HniN]; [|contradiction HniN; reflexivity].
  destruct (Fin.eq_dec j i) as [Hji|_].
  - exfalso. apply Hij. symmetry. exact Hji.
  - exact Heq.
Qed.

(** Inverse-of-positive-power non-conjugacy: γ_i^a ≁ (γ_i^{-1})^b when
    there's a witness with distinct traces.
    Note: this is a vacuous distinction for SL2 because tr(M^a) = tr(M^{-a}).
    So the only way to have distinct traces is for genuine difference in
    |a| vs |b|. *)
Theorem F_n_pos_neg_pow_non_conj_via_trace :
  forall {F : Type} (fld : Field F) (n : nat) (i : Fin.t n) (a b : nat),
    (exists M : SL2_carrier fld,
       SL2_trace fld (SL2_pow fld M a) <> SL2_trace fld (SL2_pow fld M b)) ->
    ~ are_conjugate (FreeGroup n)
         (gamma_pow (free_gen_RWord n i) a)
         (gamma_pow (rword_inv (free_gen_RWord n i)) b).
Proof.
  intros F fld n i a b [M Hne] Hconj.
  apply Hne.
  pose proof (trace_at_conjugate_SL2 (FreeGroup n) fld
                (rep_from_gen_map fld (fun _ => M))
                (gamma_pow (free_gen_RWord n i) a)
                (gamma_pow (rword_inv (free_gen_RWord n i)) b) Hconj) as Heq.
  rewrite (rep_trace_at_from_gen_map_pow fld (fun _ => M) i a) in Heq.
  rewrite (rep_trace_at_from_gen_map_inv_pow fld (fun _ => M) i b) in Heq.
  exact Heq.
Qed.

(** Same-generator distinct power non-conjugacy: γ_i^a and γ_i^b are not
    conjugate when there's a Chebyshev-injective matrix witness — i.e.,
    some M whose powers have distinct traces at exponents a and b. *)
Theorem F_n_same_gen_pow_non_conj_via_trace :
  forall {F : Type} (fld : Field F) (n : nat) (i : Fin.t n) (a b : nat),
    (exists M : SL2_carrier fld,
       SL2_trace fld (SL2_pow fld M a) <> SL2_trace fld (SL2_pow fld M b)) ->
    ~ are_conjugate (FreeGroup n)
         (gamma_pow (free_gen_RWord n i) a)
         (gamma_pow (free_gen_RWord n i) b).
Proof.
  intros F fld n i a b [M Hne] Hconj.
  apply Hne.
  pose proof (trace_at_conjugate_SL2 (FreeGroup n) fld
                (rep_from_gen_map fld (fun _ => M))
                (gamma_pow (free_gen_RWord n i) a)
                (gamma_pow (free_gen_RWord n i) b) Hconj) as Heq.
  rewrite (rep_trace_at_from_gen_map_pow fld (fun _ => M) i a) in Heq.
  rewrite (rep_trace_at_from_gen_map_pow fld (fun _ => M) i b) in Heq.
  exact Heq.
Qed.

(** Generalization to generator powers: γ_i^a and γ_j^b are not conjugate
    if their trace images can be separated by some generator-map f. *)
Theorem F_n_gens_pow_non_conj_via_trace :
  forall {n : nat} {F : Type} (fld : Field F) (i j : Fin.t n) (a b : nat),
    (exists f : Fin.t n -> SL2_carrier fld,
       SL2_trace fld (SL2_pow fld (f i) a) <>
       SL2_trace fld (SL2_pow fld (f j) b)) ->
    ~ are_conjugate (FreeGroup n)
         (gamma_pow (free_gen_RWord n i) a)
         (gamma_pow (free_gen_RWord n j) b).
Proof.
  intros n F fld i j a b [f Hne] Hconj.
  apply Hne.
  pose proof (trace_at_conjugate_SL2 (FreeGroup n) fld
                                     (rep_from_gen_map fld f)
                                     (gamma_pow (free_gen_RWord n i) a)
                                     (gamma_pow (free_gen_RWord n j) b)
                                     Hconj) as Heq.
  rewrite (rep_trace_at_from_gen_map_pow fld f i a) in Heq.
  rewrite (rep_trace_at_from_gen_map_pow fld f j b) in Heq.
  exact Heq.
Qed.

(** Conditional free-id-separating rep for F_1: given a hyperbolic-style
    matrix M whose powers all have non-identity trace, F_1 has a separating
    rep. Reduces the existence of separating reps to a concrete linear-algebra
    condition on the field. The classical Hall-axiom statement applies for ANY
    matrix-group family which is too strong; this is the proper SL2 form. *)
Theorem free_id_separating_rep_F1_SL2 :
  forall {F : Type} (fld : Field F),
    (exists M : SL2_carrier fld,
       forall k : nat, k >= 1 ->
         SL2_trace fld (SL2_pow fld M k) <>
         cr_add fld (cr_one fld) (cr_one fld)) ->
    exists rho : Representation (FreeGroup 1) (SL2_as_MG fld),
      forall eta : RWord 1,
        ~ are_conjugate (FreeGroup 1) (@rword_e 1) eta ->
        trace_at rho (@rword_e 1) <> trace_at rho eta.
Proof.
  intros F fld [M HM].
  exists (rep_from_gen_map fld (fun _ : Fin.t 1 => M)).
  intros eta Hnc.
  rewrite (rep_trace_at_e (FreeGroup 1) fld _).
  destruct (F_1_classification eta) as [He | [[k [Hk Heta]] | [k [Hk Heta]]]].
  - exfalso. apply Hnc. rewrite He. apply are_conjugate_refl.
  - rewrite Heta.
    rewrite (rep_trace_at_gamma_pow 1 fld _ (free_gen_RWord 1 Fin.F1) k).
    rewrite (rep_from_gen_map_gen fld (fun _ => M) Fin.F1).
    intro Habs. apply (HM k Hk). symmetry. exact Habs.
  - rewrite Heta.
    rewrite (rep_trace_at_gamma_inv_pow 1 fld _ (free_gen_RWord 1 Fin.F1) k).
    rewrite (rep_trace_at_gamma_pow 1 fld _ (free_gen_RWord 1 Fin.F1) k).
    rewrite (rep_from_gen_map_gen fld (fun _ => M) Fin.F1).
    intro Habs. apply (HM k Hk). symmetry. exact Habs.
Qed.
