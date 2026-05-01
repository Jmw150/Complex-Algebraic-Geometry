(** * LinAlg/SL2.v
    The special linear group SL(2, F) as a concrete StrictGroup,
    plus a MatrixGroup F instance built from it.

    SL(2, F) = { M ∈ Mat2 F | det M = 1 } with matrix multiplication.

    This is part of [G1] from DecisionProblems/OpenProblems.v. *)

Require Import CAG.Galois.Field.
Require Import CAG.Group.
Require Import CAG.LinAlg.Matrix2.
Require Import CAG.DecisionProblems.TraceProperties.
From Stdlib Require Import Ring Setoid Arith Lia.

Section SL2.
  Context {F : Type} (fld : Field F).

  Local Lemma sl2_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring sl2_ring : sl2_ring_theory.

  (** SL(2, F) as a sigma type. *)
  Definition SL2_carrier : Type :=
    { M : Mat2 F | mat2_det fld M = cr_one fld }.

  Definition SL2_mk (M : Mat2 F) (H : mat2_det fld M = cr_one fld) : SL2_carrier :=
    exist _ M H.

  Definition SL2_mat (g : SL2_carrier) : Mat2 F := proj1_sig g.

  Definition SL2_det (g : SL2_carrier) : mat2_det fld (SL2_mat g) = cr_one fld :=
    proj2_sig g.

  (** Identity. *)
  Definition SL2_id : SL2_carrier :=
    SL2_mk (mat2_id fld) (mat2_det_id fld).

  (** Multiplication. *)
  Definition SL2_mul (g h : SL2_carrier) : SL2_carrier.
  Proof.
    refine (SL2_mk (mat2_mul fld (SL2_mat g) (SL2_mat h)) _).
    rewrite mat2_det_mul.
    rewrite (SL2_det g), (SL2_det h). ring.
  Defined.

  (** Inverse via the adjugate (since det = 1). *)
  Definition SL2_inv (g : SL2_carrier) : SL2_carrier.
  Proof.
    refine (SL2_mk (mat2_adj fld (SL2_mat g)) _).
    apply mat2_det_adj_det1. apply (SL2_det g).
  Defined.

  (** Trace. *)
  Definition SL2_trace (g : SL2_carrier) : F := mat2_trace fld (SL2_mat g).

  (* ============================================================ *)
  (** ** Group laws                                                *)
  (* ============================================================ *)

  (** Equality of SL2 elements: equal underlying matrices suffice
      (proof irrelevance for the determinant equation). *)
  Lemma SL2_eq_from_mat : forall g h : SL2_carrier,
      SL2_mat g = SL2_mat h -> g = h.
  Proof.
    intros [Mg Hg] [Mh Hh] Heq. simpl in Heq. subst Mh.
    f_equal. apply Eqdep_dec.UIP_dec.
    (* Need decidable equality on F to discharge UIP — instead use
       proof_irrelevance from Stdlib if available, but we want to
       keep this constructive. We'll use the fact that any equality
       on F is decidable for our concrete uses; for the abstract
       case use proof_irrelevance. *)
  Abort.

End SL2.

(** Equality of SL2 elements via matrix equality requires UIP/proof
    irrelevance for the determinant proof. We use the standard
    [Logic.ProofIrrelevance] axiom (already used elsewhere in the
    project — Galois/Field.v imports it). *)
From Stdlib Require Import Logic.ProofIrrelevance.

Section SL2_Group.
  Context {F : Type} (fld : Field F).

  Local Lemma sl2g_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring sl2g_ring : sl2g_ring_theory.

  Lemma SL2_eq_from_mat : forall g h : SL2_carrier fld,
      SL2_mat fld g = SL2_mat fld h -> g = h.
  Proof.
    intros [Mg Hg] [Mh Hh] Heq. simpl in Heq. subst Mh.
    f_equal. apply proof_irrelevance.
  Qed.

  Lemma SL2_assoc : forall g h k : SL2_carrier fld,
      SL2_mul fld g (SL2_mul fld h k) =
      SL2_mul fld (SL2_mul fld g h) k.
  Proof.
    intros g h k. apply SL2_eq_from_mat. simpl.
    apply mat2_mul_assoc.
  Qed.

  Lemma SL2_id_left : forall g : SL2_carrier fld,
      SL2_mul fld (SL2_id fld) g = g.
  Proof.
    intros g. apply SL2_eq_from_mat. simpl.
    apply mat2_mul_id_l.
  Qed.

  Lemma SL2_id_right : forall g : SL2_carrier fld,
      SL2_mul fld g (SL2_id fld) = g.
  Proof.
    intros g. apply SL2_eq_from_mat. simpl.
    apply mat2_mul_id_r.
  Qed.

  Lemma SL2_inv_left : forall g : SL2_carrier fld,
      SL2_mul fld (SL2_inv fld g) g = SL2_id fld.
  Proof.
    intros g. apply SL2_eq_from_mat. simpl.
    apply mat2_adj_is_inv_det1_l. apply (SL2_det fld g).
  Qed.

  Lemma SL2_inv_right : forall g : SL2_carrier fld,
      SL2_mul fld g (SL2_inv fld g) = SL2_id fld.
  Proof.
    intros g. apply SL2_eq_from_mat. simpl.
    apply mat2_adj_is_inv_det1. apply (SL2_det fld g).
  Qed.

  (** SL(2, F) is a StrictGroup. *)
  Definition SL2 : StrictGroup (SL2_carrier fld) :=
    mkSG (SL2_carrier fld)
      (SL2_mul fld) (SL2_id fld) (SL2_inv fld)
      SL2_assoc SL2_id_right SL2_id_left
      SL2_inv_right SL2_inv_left.

  (** SL(2, F) as a MatrixGroup F. *)
  Definition SL2_as_MG : MatrixGroup F :=
    mkMG F (SL2_carrier fld) SL2 (SL2_trace fld) 2.

  (** Trace is conjugation-invariant: tr(g·h·g^{-1}) = tr(h). *)
  Lemma SL2_trace_conj : forall g h : SL2_carrier fld,
      SL2_trace fld (SL2_mul fld (SL2_mul fld g h) (SL2_inv fld g)) =
      SL2_trace fld h.
  Proof.
    intros g h. unfold SL2_trace, SL2_mul, SL2_inv. simpl.
    (* tr((M_g · M_h) · adj M_g) = tr(M_h) *)
    rewrite (mat2_trace_cyclic fld
              (mat2_mul fld (SL2_mat fld g) (SL2_mat fld h))
              (mat2_adj fld (SL2_mat fld g))).
    (* now: tr(adj M_g · (M_g · M_h)) *)
    rewrite mat2_mul_assoc.
    (* now: tr((adj M_g · M_g) · M_h) *)
    rewrite (mat2_adj_is_inv_det1_l fld (SL2_mat fld g) (SL2_det fld g)).
    rewrite mat2_mul_id_l. reflexivity.
  Qed.

  (** Trace at conjugate: tr(g · h · g^{-1}) = tr(h) (alternative form via cyclic). *)
  Lemma SL2_trace_cyclic : forall g h : SL2_carrier fld,
      SL2_trace fld (SL2_mul fld g h) = SL2_trace fld (SL2_mul fld h g).
  Proof.
    intros g h. unfold SL2_trace, SL2_mul. simpl.
    apply mat2_trace_cyclic.
  Qed.

  (** Trace of inverse equals trace: tr(g^{-1}) = tr(g) for SL2 elements. *)
  Lemma SL2_trace_inv : forall g : SL2_carrier fld,
      SL2_trace fld (SL2_inv fld g) = SL2_trace fld g.
  Proof.
    intros [[[[a b] c] d] Hg]. unfold SL2_trace, SL2_inv, SL2_mat. simpl.
    unfold mat2_trace, mat2_adj, mat2_mk. simpl. ring.
  Qed.

  (** Trace is invariant under double inversion (trivially): tr((g^{-1})^{-1}) = tr(g). *)
  Lemma SL2_trace_inv_inv : forall g : SL2_carrier fld,
      SL2_trace fld (SL2_inv fld (SL2_inv fld g)) = SL2_trace fld g.
  Proof.
    intros g. rewrite SL2_trace_inv, SL2_trace_inv. reflexivity.
  Qed.

  (** Trace identity at SL2 identity. *)
  Lemma SL2_trace_id : SL2_trace fld (SL2_id fld) =
                       cr_add fld (cr_one fld) (cr_one fld).
  Proof.
    unfold SL2_trace, SL2_id, SL2_mat. simpl.
    unfold mat2_trace, mat2_id, mat2_mk. reflexivity.
  Qed.

  (** SL2_id is its own inverse (involution). *)
  Lemma SL2_inv_id : SL2_inv fld (SL2_id fld) = SL2_id fld.
  Proof.
    apply SL2_eq_from_mat.
    unfold SL2_inv, SL2_id, SL2_mat. simpl.
    unfold mat2_adj, mat2_id, mat2_mk. simpl.
    apply f_equal2; [apply f_equal2; [apply f_equal2|]|]; ring.
  Qed.

  (** SL2 power: g · g · ... · g (k times). *)
  Fixpoint SL2_pow (g : SL2_carrier fld) (k : nat) : SL2_carrier fld :=
    match k with
    | 0 => SL2_id fld
    | S k' => SL2_mul fld g (SL2_pow g k')
    end.

  Lemma SL2_pow_zero : forall g, SL2_pow g 0 = SL2_id fld.
  Proof. reflexivity. Qed.

  Lemma SL2_pow_succ : forall g k,
      SL2_pow g (S k) = SL2_mul fld g (SL2_pow g k).
  Proof. reflexivity. Qed.

  (** SL2_pow at 2 is multiplication. *)
  Lemma SL2_pow_two_eq : forall g : SL2_carrier fld,
      SL2_pow g 2 = SL2_mul fld g g.
  Proof.
    intros g. simpl. rewrite SL2_id_right. reflexivity.
  Qed.

  (** SL2_pow on identity: SL2_id^k = SL2_id. *)
  Lemma SL2_pow_id : forall k, SL2_pow (SL2_id fld) k = SL2_id fld.
  Proof.
    intros k. induction k as [|k IH].
    - reflexivity.
    - simpl. rewrite IH. apply SL2_id_left.
  Qed.

  (** SL2_pow is additive in the exponent: g^(a+b) = g^a · g^b. *)
  Lemma SL2_pow_add : forall (g : SL2_carrier fld) (a b : nat),
      SL2_pow g (a + b) = SL2_mul fld (SL2_pow g a) (SL2_pow g b).
  Proof.
    intros g a b. induction a as [|a IH].
    - simpl. symmetry. apply SL2_id_left.
    - simpl. rewrite IH. apply SL2_assoc.
  Qed.

  (** SL2_pow multiplicativity: g^(a*b) = (g^b)^a. *)
  Lemma SL2_pow_mul : forall (g : SL2_carrier fld) (a b : nat),
      SL2_pow g (a * b) = SL2_pow (SL2_pow g b) a.
  Proof.
    intros g a b. induction a as [|a IH].
    - reflexivity.
    - simpl. rewrite SL2_pow_add. rewrite IH. reflexivity.
  Qed.

  (** g and g^k commute. *)
  Lemma SL2_pow_commute : forall (g : SL2_carrier fld) (k : nat),
      SL2_mul fld g (SL2_pow g k) = SL2_mul fld (SL2_pow g k) g.
  Proof.
    intros g k. induction k as [|k IH].
    - simpl. rewrite SL2_id_right, SL2_id_left. reflexivity.
    - simpl.
      (* Goal: g · (g · g^k) = (g · g^k) · g *)
      pose proof IH as IH'.
      rewrite IH at 1.
      (* Now: g · (g^k · g) = (g · g^k) · g. *)
      apply SL2_assoc.
  Qed.

  (** SL2_pow is multiplicative: g^a · g^b = g^(a+b). Symmetric of SL2_pow_add. *)
  Lemma SL2_pow_mul_pow : forall (g : SL2_carrier fld) (a b : nat),
      SL2_mul fld (SL2_pow g a) (SL2_pow g b) = SL2_pow g (a + b).
  Proof.
    intros g a b. symmetry. apply SL2_pow_add.
  Qed.

  (** Powers of g commute with each other: g^a · g^b = g^b · g^a. *)
  Lemma SL2_pow_pow_commute : forall (g : SL2_carrier fld) (a b : nat),
      SL2_mul fld (SL2_pow g a) (SL2_pow g b) =
      SL2_mul fld (SL2_pow g b) (SL2_pow g a).
  Proof.
    intros g a b.
    rewrite SL2_pow_mul_pow. rewrite SL2_pow_mul_pow.
    rewrite Nat.add_comm. reflexivity.
  Qed.

  (** Inverse of a power: SL2_inv (g^k) = (SL2_inv g)^k. *)
  Lemma SL2_inv_pow : forall (g : SL2_carrier fld) (k : nat),
      SL2_inv fld (SL2_pow g k) = SL2_pow (SL2_inv fld g) k.
  Proof.
    intros g k. induction k as [|k IH].
    - simpl. apply SL2_inv_id.
    - simpl.
      (* SL2_inv (g · g^k) = SL2_inv (g^k) · SL2_inv g  [by inv_mul]
                            = (SL2_inv g)^k · SL2_inv g  [by IH]
                            = SL2_inv g · (SL2_inv g)^k  [by SL2_pow_commute] *)
      pose proof (inv_mul SL2 g (SL2_pow g k)) as Hinv.
      simpl in Hinv.
      rewrite Hinv.
      rewrite IH.
      symmetry. apply SL2_pow_commute.
  Qed.

  (** g^k · (g^{-1})^k = SL2_id (right cancellation across powers). *)
  Lemma SL2_pow_inv_right : forall (g : SL2_carrier fld) (k : nat),
      SL2_mul fld (SL2_pow g k) (SL2_pow (SL2_inv fld g) k) = SL2_id fld.
  Proof.
    intros g k.
    rewrite <- SL2_inv_pow.
    apply SL2_inv_right.
  Qed.

  (** (g^{-1})^k · g^k = SL2_id (left cancellation across powers). *)
  Lemma SL2_pow_inv_left : forall (g : SL2_carrier fld) (k : nat),
      SL2_mul fld (SL2_pow (SL2_inv fld g) k) (SL2_pow g k) = SL2_id fld.
  Proof.
    intros g k.
    rewrite <- SL2_inv_pow.
    apply SL2_inv_left.
  Qed.

End SL2_Group.

Arguments SL2_carrier {F} _.
Arguments SL2_mk {F} _ _ _.
Arguments SL2_mat {F} _ _.
Arguments SL2_id {F} _.
Arguments SL2_mul {F} _ _ _.
Arguments SL2_inv {F} _ _.
Arguments SL2_trace {F} _ _.
Arguments SL2 {F} _.
Arguments SL2_as_MG {F} _.
