(** * DecisionProblems/HallTheorem.v

    Hall's theorem on subgroup separability of free groups.

    Addresses [G6] from OpenProblems.v.

    Hall (1949): every finitely generated subgroup of a free group
    is a free factor of a finite-index subgroup. Equivalently: free
    groups are LERF (locally extended residually finite, or
    "subgroup separable").

    For us, the relevant consequence is:
    [Hall_free_factor]: for any γ ∈ F_r and any nontrivial element,
    there exists a finite-index normal subgroup ∆ ≤ F_r such that
    F_r = ⟨γ⟩ * ∆ as a free product.

    This is used in the proof of Theorem 1.6 (free groups have
    property B):
    1. Pick γ; find Δ such that ⟨γ⟩ ∗ Δ = F_r (Hall).
    2. Define ρ_⟨γ⟩ : ⟨γ⟩ → SL(2, F) sending γ to a non-trivial
       element with chosen trace.
    3. Extend by trivial action on Δ to get ρ_F_r : F_r → SL(...).
    4. Induced representation Ind ρ : F_r → SL(2·[F_r:Δ⟨γ⟩], F)
       separates γ from non-conjugate η by Frobenius trace formula. *)

From CAG Require Import Group FreeGroup.
From CAG Require Import DecisionProblems.TraceProperties.
From CAG Require Import DecisionProblems.OpenProblems.
From CAG Require Import DecisionProblems.WordLengthFreeGroup.
From CAG Require Import DecisionProblems.InducedRep.
From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* ================================================================== *)
(** * 1. Hall's theorem (axiomatized)                                   *)
(* ================================================================== *)

(** Hall's theorem (1949) on free groups.

    For every nontrivial γ ∈ F_r, there exists a finite-index normal
    subgroup Δ ⊴ F_r such that:
        F_r = ⟨γ⟩ ∗ Δ  (free product structure)

    Stated in our framework: [hall_finite_index_free_factor] gives
    the existence of such a Δ as a [FiniteIndexSubgroup]. *)

(** Power of gamma in F_r: gamma^i. *)
Fixpoint gamma_pow {r : nat} (gamma : RWord r) (i : nat) : RWord r :=
  match i with
  | 0 => @rword_e r
  | S k => rword_mul gamma (gamma_pow gamma k)
  end.

(** gamma^0 = e. *)
Lemma gamma_pow_zero : forall {r : nat} (gamma : RWord r),
    gamma_pow gamma 0 = @rword_e r.
Proof. intros. reflexivity. Qed.

(** gamma^1 = gamma. *)
Lemma gamma_pow_one : forall {r : nat} (gamma : RWord r),
    gamma_pow gamma 1 = rword_mul gamma (@rword_e r).
Proof. intros. reflexivity. Qed.

(** Successor unfolding. *)
Lemma gamma_pow_succ : forall {r : nat} (gamma : RWord r) (k : nat),
    gamma_pow gamma (S k) = rword_mul gamma (gamma_pow gamma k).
Proof. intros. reflexivity. Qed.

(** Identity has trivial powers: e^k = e. *)
Lemma gamma_pow_id : forall {r : nat} (k : nat),
    gamma_pow (@rword_e r) k = @rword_e r.
Proof.
  intros r k. induction k as [|k IH].
  - reflexivity.
  - simpl. rewrite IH. apply rword_id_left.
Qed.

(** Power addition: gamma^(a+b) = gamma^a * gamma^b. *)
Lemma gamma_pow_add : forall {r : nat} (gamma : RWord r) (a b : nat),
    gamma_pow gamma (a + b) =
    rword_mul (gamma_pow gamma a) (gamma_pow gamma b).
Proof.
  intros r gamma a. induction a as [|a IH]; intro b.
  - simpl. rewrite rword_id_left. reflexivity.
  - simpl. rewrite IH. rewrite rword_assoc. reflexivity.
Qed.

(** Power multiplication: gamma^(a*b) = (gamma^b)^a. *)
Lemma gamma_pow_mul : forall {r : nat} (gamma : RWord r) (a b : nat),
    gamma_pow gamma (a * b) = gamma_pow (gamma_pow gamma b) a.
Proof.
  intros r gamma a. induction a as [|a IH]; intro b.
  - reflexivity.
  - simpl. rewrite gamma_pow_add. rewrite IH. reflexivity.
Qed.

(** Inverse of identity is identity. *)
Lemma rword_inv_e : forall {r : nat},
    @rword_inv r (@rword_e r) = @rword_e r.
Proof.
  intros r.
  apply rword_eq. simpl. reflexivity.
Qed.

(** Powers commute: γ^a · γ^b = γ^b · γ^a (since both equal γ^(a+b)). *)
Lemma gamma_pow_commute : forall {r : nat} (gamma : RWord r) (a b : nat),
    rword_mul (gamma_pow gamma a) (gamma_pow gamma b) =
    rword_mul (gamma_pow gamma b) (gamma_pow gamma a).
Proof.
  intros r gamma a b.
  rewrite <- gamma_pow_add.
  rewrite <- gamma_pow_add.
  rewrite Nat.add_comm. reflexivity.
Qed.

(** Inverse of a product in F_r: (a·b)^{-1} = b^{-1} · a^{-1}.
    Specialization of the general group [inv_mul] to the free group. *)
Lemma rword_inv_mul : forall {r : nat} (a b : RWord r),
    rword_inv (rword_mul a b) = rword_mul (rword_inv b) (rword_inv a).
Proof.
  intros r a b.
  exact (inv_mul (FreeGroup r) a b).
Qed.

(** Inverse of a power: (γ^k)^{-1} = (γ^{-1})^k. *)
Lemma gamma_pow_inv : forall {r : nat} (gamma : RWord r) (k : nat),
    rword_inv (gamma_pow gamma k) = gamma_pow (rword_inv gamma) k.
Proof.
  intros r gamma k. induction k as [|k IH].
  - apply rword_inv_e.
  - simpl.
    (* (γ · γ^k)^{-1} = (γ^k)^{-1} · γ^{-1} *)
    rewrite rword_inv_mul.
    rewrite IH.
    (* now: (γ^{-1})^k · γ^{-1} = γ^{-1} · (γ^{-1})^k *)
    pose proof (gamma_pow_commute (rword_inv gamma) k 1) as Hcomm.
    simpl in Hcomm. rewrite rword_id_right in Hcomm. exact Hcomm.
Qed.

(** γ^k * γ = γ * γ^k (γ commutes with its own powers). *)
Lemma gamma_pow_succ_right : forall {r : nat} (gamma : RWord r) (k : nat),
    rword_mul (gamma_pow gamma k) gamma = gamma_pow gamma (S k).
Proof.
  intros r gamma k.
  pose proof (gamma_pow_add gamma k 1) as H.
  replace (k + 1) with (S k) in H by lia.
  simpl in H. rewrite rword_id_right in H.
  symmetry. exact H.
Qed.

(** Inverse of inverse is identity (in F_r). *)
Lemma rword_inv_inv : forall {r : nat} (w : RWord r),
    rword_inv (rword_inv w) = w.
Proof.
  intros r w. exact (double_inverse (FreeGroup r) w).
Qed.

(** γ^2 = γ · γ. *)
Lemma gamma_pow_two_eq : forall {r : nat} (gamma : RWord r),
    gamma_pow gamma 2 = rword_mul gamma gamma.
Proof.
  intros r gamma. simpl. rewrite rword_id_right. reflexivity.
Qed.

(** γ^3 = γ · γ · γ. *)
Lemma gamma_pow_three_eq : forall {r : nat} (gamma : RWord r),
    gamma_pow gamma 3 = rword_mul gamma (rword_mul gamma gamma).
Proof.
  intros r gamma. simpl. rewrite rword_id_right. reflexivity.
Qed.

(** Powers of inverse-inverse equal powers of original. *)
Lemma gamma_pow_inv_inv : forall {r : nat} (gamma : RWord r) (k : nat),
    gamma_pow (rword_inv (rword_inv gamma)) k = gamma_pow gamma k.
Proof.
  intros r gamma k.
  pose proof (rword_inv_inv gamma) as Hinv.
  rewrite Hinv. reflexivity.
Qed.

(** Double inverse of a power: ((γ^k)^{-1})^{-1} = γ^k. *)
Lemma gamma_pow_inv_inv_eq : forall {r : nat} (gamma : RWord r) (k : nat),
    rword_inv (rword_inv (gamma_pow gamma k)) = gamma_pow gamma k.
Proof.
  intros r gamma k. apply rword_inv_inv.
Qed.

(** Inverse of inverted power: ((γ^{-1})^k)^{-1} = γ^k. *)
Lemma gamma_pow_inv_inv_pow : forall {r : nat} (gamma : RWord r) (k : nat),
    rword_inv (gamma_pow (rword_inv gamma) k) = gamma_pow gamma k.
Proof.
  intros r gamma k.
  rewrite (gamma_pow_inv (rword_inv gamma) k).
  apply gamma_pow_inv_inv.
Qed.

(* ================================================================== *)
(** * 1.5. Cyclic subgroup language ⟨γ⟩                                *)
(* ================================================================== *)

(** The cyclic subgroup ⟨γ⟩ ⊆ F_r consists of all positive and negative
    powers of γ. We encode "γ^n for n ∈ Z" as a disjunction of positive
    powers of γ and positive powers of γ^{-1}. *)

Definition in_cyclic {r : nat} (gamma w : RWord r) : Prop :=
  (exists k : nat, w = gamma_pow gamma k) \/
  (exists k : nat, w = gamma_pow (rword_inv gamma) k).

(** ⟨γ⟩ contains the identity. *)
Lemma in_cyclic_id : forall {r : nat} (gamma : RWord r),
    in_cyclic gamma (@rword_e r).
Proof.
  intros r gamma. left. exists 0. reflexivity.
Qed.

(** ⟨γ⟩ contains γ. *)
Lemma in_cyclic_gen : forall {r : nat} (gamma : RWord r),
    in_cyclic gamma gamma.
Proof.
  intros r gamma. left. exists 1.
  simpl. symmetry. apply rword_id_right.
Qed.

(** ⟨γ⟩ contains γ^k for all k. *)
Lemma in_cyclic_pow : forall {r : nat} (gamma : RWord r) (k : nat),
    in_cyclic gamma (gamma_pow gamma k).
Proof.
  intros r gamma k. left. exists k. reflexivity.
Qed.

(** ⟨γ⟩ contains (γ^{-1})^k for all k. *)
Lemma in_cyclic_inv_pow : forall {r : nat} (gamma : RWord r) (k : nat),
    in_cyclic gamma (gamma_pow (rword_inv gamma) k).
Proof.
  intros r gamma k. right. exists k. reflexivity.
Qed.

(** ⟨γ⟩ contains γ^{-1}. *)
Lemma in_cyclic_gen_inv : forall {r : nat} (gamma : RWord r),
    in_cyclic gamma (rword_inv gamma).
Proof.
  intros r gamma. right. exists 1.
  simpl. symmetry. apply rword_id_right.
Qed.

(** γ · (γ^{-1})^(S k) = (γ^{-1})^k (telescoping). *)
Lemma gamma_inv_cancel_left : forall {r : nat} (gamma : RWord r) (k : nat),
    rword_mul gamma (gamma_pow (rword_inv gamma) (S k)) =
    gamma_pow (rword_inv gamma) k.
Proof.
  intros r gamma k. simpl.
  rewrite rword_assoc.
  rewrite rword_inv_right.
  apply rword_id_left.
Qed.

(** γ^{-1} · γ^(S k) = γ^k (telescoping the other way). *)
Lemma gamma_inv_cancel_right : forall {r : nat} (gamma : RWord r) (k : nat),
    rword_mul (rword_inv gamma) (gamma_pow gamma (S k)) =
    gamma_pow gamma k.
Proof.
  intros r gamma k. simpl.
  rewrite rword_assoc.
  rewrite rword_inv_left.
  apply rword_id_left.
Qed.

(** Inverse-pow add: (γ^{-1})^(a+b) = (γ^{-1})^a · (γ^{-1})^b. *)
Lemma gamma_inv_pow_add : forall {r : nat} (gamma : RWord r) (a b : nat),
    gamma_pow (rword_inv gamma) (a + b) =
    rword_mul (gamma_pow (rword_inv gamma) a) (gamma_pow (rword_inv gamma) b).
Proof.
  intros r gamma a b. apply gamma_pow_add.
Qed.

(** γ · (γ^{-1})^k decomposes by case on k. *)
Lemma gamma_mul_inv_pow : forall {r : nat} (gamma : RWord r) (k : nat),
    rword_mul gamma (gamma_pow (rword_inv gamma) k) =
    match k with
    | 0 => gamma
    | S k' => gamma_pow (rword_inv gamma) k'
    end.
Proof.
  intros r gamma k. destruct k as [|k'].
  - simpl. apply rword_id_right.
  - apply gamma_inv_cancel_left.
Qed.

(** γ^{-1} · γ^k decomposes by case on k. *)
Lemma gamma_inv_mul_pow : forall {r : nat} (gamma : RWord r) (k : nat),
    rword_mul (rword_inv gamma) (gamma_pow gamma k) =
    match k with
    | 0 => rword_inv gamma
    | S k' => gamma_pow gamma k'
    end.
Proof.
  intros r gamma k. destruct k as [|k'].
  - simpl. apply rword_id_right.
  - apply gamma_inv_cancel_right.
Qed.

(** γ^(S k) · γ^{-1} = γ^k (right cancellation by γ^{-1}). *)
Lemma gamma_pow_mul_inv : forall {r : nat} (gamma : RWord r) (k : nat),
    rword_mul (gamma_pow gamma (S k)) (rword_inv gamma) = gamma_pow gamma k.
Proof.
  intros r gamma k. induction k as [|k IH].
  - simpl. rewrite rword_id_right.
    apply rword_inv_right.
  - simpl. simpl in IH.
    rewrite <- rword_assoc.
    f_equal. exact IH.
Qed.

(** (γ^{-1})^(S k) · γ = (γ^{-1})^k (left direction analogue). *)
Lemma gamma_inv_pow_mul_gamma : forall {r : nat} (gamma : RWord r) (k : nat),
    rword_mul (gamma_pow (rword_inv gamma) (S k)) gamma =
    gamma_pow (rword_inv gamma) k.
Proof.
  intros r gamma k.
  pose proof (gamma_pow_mul_inv (rword_inv gamma) k) as H.
  rewrite rword_inv_inv in H. exact H.
Qed.

(** (γ^{-1})^a · γ^a = e (left-side cancellation). *)
Lemma gamma_pow_inv_pow_mul_same : forall {r : nat} (gamma : RWord r) (a : nat),
    rword_mul (gamma_pow (rword_inv gamma) a) (gamma_pow gamma a) = @rword_e r.
Proof.
  intros r gamma a.
  rewrite <- (gamma_pow_inv gamma a).
  apply rword_inv_left.
Qed.

(** γ^a · (γ^{-1})^a = e (cyclic group cancellation). *)
Lemma gamma_pow_mul_inv_pow_same : forall {r : nat} (gamma : RWord r) (a : nat),
    rword_mul (gamma_pow gamma a) (gamma_pow (rword_inv gamma) a) = @rword_e r.
Proof.
  intros r gamma a. induction a as [|a IH].
  - simpl. apply rword_id_left.
  - (* γ^(S a) · (γ^{-1})^(S a) *)
    (* unfold inv side: (γ^{-1})^(S a) = γ^{-1} · (γ^{-1})^a *)
    change (gamma_pow (rword_inv gamma) (S a))
      with (rword_mul (rword_inv gamma) (gamma_pow (rword_inv gamma) a)).
    rewrite rword_assoc.
    (* now: (γ^(S a) · γ^{-1}) · (γ^{-1})^a *)
    rewrite gamma_pow_mul_inv.
    exact IH.
Qed.

(** Mixed product γ^a · (γ^{-1})^b is in the cyclic subgroup. *)
Lemma in_cyclic_pow_mul_inv_pow : forall {r : nat} (gamma : RWord r) (a b : nat),
    in_cyclic gamma (rword_mul (gamma_pow gamma a) (gamma_pow (rword_inv gamma) b)).
Proof.
  intros r gamma a. induction a as [|a IH]; intro b.
  - change (gamma_pow gamma 0) with (@rword_e r).
    rewrite rword_id_left. apply in_cyclic_inv_pow.
  - destruct b as [|b].
    + change (gamma_pow (rword_inv gamma) 0) with (@rword_e r).
      rewrite rword_id_right. apply in_cyclic_pow.
    + (* γ^(S a) · (γ^{-1})^(S b) → γ^a · (γ^{-1})^b via cancellation *)
      change (gamma_pow (rword_inv gamma) (S b))
        with (rword_mul (rword_inv gamma) (gamma_pow (rword_inv gamma) b)).
      rewrite rword_assoc.
      rewrite gamma_pow_mul_inv.
      apply IH.
Qed.

(** Symmetric: (γ^{-1})^a · γ^b is in the cyclic subgroup. *)
Lemma in_cyclic_inv_pow_mul_pow : forall {r : nat} (gamma : RWord r) (a b : nat),
    in_cyclic gamma (rword_mul (gamma_pow (rword_inv gamma) a) (gamma_pow gamma b)).
Proof.
  intros r gamma a. induction a as [|a IH]; intro b.
  - change (gamma_pow (rword_inv gamma) 0) with (@rword_e r).
    rewrite rword_id_left. apply in_cyclic_pow.
  - destruct b as [|b].
    + change (gamma_pow gamma 0) with (@rword_e r).
      rewrite rword_id_right. apply in_cyclic_inv_pow.
    + (* (γ^{-1})^(S a) · γ^(S b) → (γ^{-1})^a · γ^b via cancellation *)
      change (gamma_pow gamma (S b))
        with (rword_mul gamma (gamma_pow gamma b)).
      rewrite rword_assoc.
      rewrite gamma_inv_pow_mul_gamma.
      apply IH.
Qed.

(** Closure of ⟨γ⟩ under multiplication. *)
Lemma in_cyclic_mul : forall {r : nat} (gamma : RWord r) (u v : RWord r),
    in_cyclic gamma u -> in_cyclic gamma v ->
    in_cyclic gamma (rword_mul u v).
Proof.
  intros r gamma u v Hu Hv.
  destruct Hu as [[a Hu] | [a Hu]];
  destruct Hv as [[b Hv] | [b Hv]];
  subst u v.
  - (* pos × pos *)
    rewrite <- gamma_pow_add. apply in_cyclic_pow.
  - (* pos × neg *)
    apply in_cyclic_pow_mul_inv_pow.
  - (* neg × pos *)
    apply in_cyclic_inv_pow_mul_pow.
  - (* neg × neg *)
    rewrite <- gamma_inv_pow_add. apply in_cyclic_inv_pow.
Qed.

(** Closure of ⟨γ⟩ under powers: w ∈ ⟨γ⟩ ⟹ w^n ∈ ⟨γ⟩. *)
Lemma in_cyclic_pow_closed : forall {r : nat} (gamma w : RWord r) (n : nat),
    in_cyclic gamma w -> in_cyclic gamma (gamma_pow w n).
Proof.
  intros r gamma w n Hw. induction n as [|n IH].
  - simpl. apply in_cyclic_id.
  - simpl. apply in_cyclic_mul.
    + exact Hw.
    + exact IH.
Qed.


(** Closure of ⟨γ⟩ under inverse. *)
Lemma in_cyclic_inv : forall {r : nat} (gamma : RWord r) (u : RWord r),
    in_cyclic gamma u -> in_cyclic gamma (rword_inv u).
Proof.
  intros r gamma u Hu.
  destruct Hu as [[k Hu] | [k Hu]]; subst u.
  - (* (γ^k)^{-1} = (γ^{-1})^k ∈ negative side *)
    rewrite gamma_pow_inv. apply in_cyclic_inv_pow.
  - (* ((γ^{-1})^k)^{-1} = γ^k ∈ positive side *)
    rewrite gamma_pow_inv_inv_pow. apply in_cyclic_pow.
Qed.

(** ⟨e⟩ = {e}. *)
Lemma in_cyclic_e : forall {r : nat} (w : RWord r),
    in_cyclic (@rword_e r) w -> w = @rword_e r.
Proof.
  intros r w Hw. destruct Hw as [[k Hk] | [k Hk]].
  - rewrite Hk. apply gamma_pow_id.
  - rewrite Hk. rewrite rword_inv_e. apply gamma_pow_id.
Qed.

(** Bidirectional: in_cyclic e w ↔ w = e. *)
Lemma in_cyclic_e_iff : forall {r : nat} (w : RWord r),
    in_cyclic (@rword_e r) w <-> w = @rword_e r.
Proof.
  intros r w. split.
  - apply in_cyclic_e.
  - intros ->. apply in_cyclic_id.
Qed.

(** ⟨γ⟩ is a subgroup of F_r. *)
Theorem in_cyclic_is_subgroup : forall {r : nat} (gamma : RWord r),
    is_subgroup (StrictGroup_to_Group (FreeGroup r)) (in_cyclic gamma).
Proof.
  intros r gamma. split; [| split].
  - (* contains_id *)
    apply in_cyclic_id.
  - (* closed_under_mul *)
    intros a b Ha Hb. apply in_cyclic_mul; assumption.
  - (* closed_under_inv *)
    intros a Ha. exists (rword_inv a).
    split.
    + apply in_cyclic_inv. exact Ha.
    + split; simpl.
      * apply rword_inv_right.
      * apply rword_inv_left.
Qed.

(* ================================================================== *)
(** * 1.6. Trivial FiniteIndexSubgroup (full group)                    *)
(* ================================================================== *)

(** The whole free group F_r as a (trivial) finite-index subgroup of
    itself, with index 1 and transversal [e]. Useful as a witness
    that FiniteIndexSubgroups exist non-vacuously. *)

Definition trivial_FIS (r : nat) : FiniteIndexSubgroup (FreeGroup r).
Proof.
  refine (mkFIS _ (FreeGroup r)
    (fun _ : RWord r => True)        (* fis_pred: everything *)
    1                                 (* fis_index = 1 *)
    [@rword_e r]                      (* fis_trans = [e] *)
    eq_refl                           (* fis_trans_len: length [e] = 1 *)
    _                                 (* fis_trans_dec *)
    I                                 (* fis_id_in_H *)
    (fun _ _ _ _ => I)                (* fis_mul_closed *)
    (fun _ _ => I)                    (* fis_inv_closed *)
    (fun _ => left I)                 (* fis_pred_dec: True is decidable *)
    _).                               (* fis_trans_unique *)
  - (* fis_trans_dec: forall g, ∃ i h. i < 1 ∧ True ∧ nth_error [e] i = Some (g·h^{-1}) *)
    intro g. exists 0, g. split; [|split].
    + lia.
    + exact I.
    + simpl. f_equal.
      (* need: rword_e = rword_mul g (rword_inv g) *)
      pose proof (sinv_right (RWord r) (FreeGroup r) g) as Hinv.
      simpl in Hinv. symmetry. exact Hinv.
  - (* fis_trans_unique: with fis_index = 1, only valid index is 0,
       so i = j = 0 trivially. *)
    intros i j t_i t_j Hi Hj _ _ _.
    assert (i = 0) by lia. assert (j = 0) by lia. subst. reflexivity.
Defined.

(** Sanity: trivial_FIS has index 1. *)
Lemma trivial_FIS_index : forall (r : nat),
    fis_index (trivial_FIS r) = 1.
Proof. intros. reflexivity. Qed.

(** Sanity: trivial_FIS contains every element. *)
Lemma trivial_FIS_pred : forall (r : nat) (g : RWord r),
    fis_pred (trivial_FIS r) g.
Proof. intros r g. exact I. Qed.

(** Sanity: transversal of trivial_FIS is [rword_e]. *)
Lemma trivial_FIS_trans : forall (r : nat),
    fis_trans (trivial_FIS r) = [@rword_e r].
Proof. intros. reflexivity. Qed.

(** For trivial_FIS, σ_g(0) = 0 since 0 is the only valid index. *)
Lemma trivial_FIS_sigma : forall (r : nat) (g : RWord r),
    coset_sigma (trivial_FIS r) g 0 = 0.
Proof.
  intros r g.
  pose proof (coset_sigma_bound (trivial_FIS r) g 0) as Hbnd.
  rewrite trivial_FIS_index in Hbnd.
  pose proof (Hbnd ltac:(lia)) as Hlt. lia.
Qed.

(** For trivial_FIS, the cocycle h_{g, 0} equals g (provable from
    coset_action_eq with t_0 = e and σ_g(0) = 0). *)
Lemma trivial_FIS_cocycle : forall (r : nat) (g : RWord r),
    coset_cocycle (trivial_FIS r) g 0 = g.
Proof.
  intros r g.
  assert (Hi : 0 < fis_index (trivial_FIS r)).
  { rewrite trivial_FIS_index. lia. }
  assert (Hsi : coset_sigma (trivial_FIS r) g 0 = 0)
    by apply trivial_FIS_sigma.
  pose proof (coset_action_eq (trivial_FIS r) g 0
                              (@rword_e r) (@rword_e r) Hi
                              eq_refl) as Heq0.
  rewrite Hsi in Heq0.
  specialize (Heq0 eq_refl).
  (* Heq0 : g · e = e · h, where h = coset_cocycle (trivial_FIS r) g 0. *)
  (* Simplify on the FreeGroup: smul (FreeGroup r) g e = g, etc. *)
  change (smul (RWord r) (FreeGroup r)) with (@rword_mul r) in Heq0.
  rewrite rword_id_right in Heq0.
  rewrite rword_id_left in Heq0.
  symmetry. exact Heq0.
Qed.

(* ================================================================== *)
(** * 1.7. ⟨γ⟩ is the smallest subgroup of F_r containing γ            *)
(* ================================================================== *)

(** A subgroup H ⊆ F_r containing γ must contain γ^k for all k. *)
Lemma subgroup_contains_gamma_pow :
  forall {r : nat} (H : RWord r -> Prop) (gamma : RWord r),
    is_subgroup (StrictGroup_to_Group (FreeGroup r)) H ->
    H gamma ->
    forall k, H (gamma_pow gamma k).
Proof.
  intros r H gamma [Hid [Hmul Hinv]] Hgamma k.
  induction k as [|k IH].
  - exact Hid.
  - simpl. apply (Hmul gamma (gamma_pow gamma k) Hgamma IH).
Qed.

(** A subgroup H ⊆ F_r containing γ must contain γ^{-1}. *)
Lemma subgroup_contains_gamma_inv :
  forall {r : nat} (H : RWord r -> Prop) (gamma : RWord r),
    is_subgroup (StrictGroup_to_Group (FreeGroup r)) H ->
    H gamma ->
    H (rword_inv gamma).
Proof.
  intros r H gamma [Hid [Hmul Hinv]] Hgamma.
  destruct (Hinv gamma Hgamma) as [b [Hb Hinvof]].
  destruct Hinvof as [Hbg Hgb].
  simpl in Hbg, Hgb.
  (* Hbg: rword_mul gamma b = rword_e ; Hgb: rword_mul b gamma = rword_e *)
  (* By unique_inverse, b = rword_inv gamma. *)
  pose proof (unique_inverse (FreeGroup r) gamma b Hbg Hgb) as Heq.
  simpl in Heq. rewrite <- Heq. exact Hb.
Qed.

(** ⟨γ⟩ is contained in any subgroup containing γ.
    Together with `in_cyclic_is_subgroup`, this characterizes ⟨γ⟩
    as the smallest such subgroup. *)
Theorem in_cyclic_minimal :
  forall {r : nat} (H : RWord r -> Prop) (gamma : RWord r),
    is_subgroup (StrictGroup_to_Group (FreeGroup r)) H ->
    H gamma ->
    forall w, in_cyclic gamma w -> H w.
Proof.
  intros r H gamma Hsubgrp Hgamma w Hw.
  destruct Hw as [[k Hk] | [k Hk]]; subst w.
  - apply subgroup_contains_gamma_pow; assumption.
  - apply subgroup_contains_gamma_pow.
    + exact Hsubgrp.
    + apply subgroup_contains_gamma_inv; assumption.
Qed.

(** Any FiniteIndexSubgroup containing γ contains all of ⟨γ⟩. *)
Theorem fis_contains_cyclic :
  forall {r : nat} (FIS : FiniteIndexSubgroup (FreeGroup r))
         (gamma : RWord r),
    fis_pred FIS gamma ->
    forall w, in_cyclic gamma w -> fis_pred FIS w.
Proof.
  intros r FIS gamma Hgamma w Hw.
  apply (in_cyclic_minimal (fis_pred FIS) gamma).
  - (* fis_pred FIS is a subgroup *)
    split; [|split].
    + exact (fis_id_in_H FIS).
    + intros a b Ha Hb. exact (fis_mul_closed FIS a b Ha Hb).
    + intros a Ha.
      exists (rword_inv a). split.
      * exact (fis_inv_closed FIS a Ha).
      * split; simpl.
        -- apply rword_inv_right.
        -- apply rword_inv_left.
  - exact Hgamma.
  - exact Hw.
Qed.

(** Powers of γ are in any FIS containing γ. *)
Corollary fis_contains_gamma_pow :
  forall {r : nat} (FIS : FiniteIndexSubgroup (FreeGroup r))
         (gamma : RWord r) (k : nat),
    fis_pred FIS gamma -> fis_pred FIS (gamma_pow gamma k).
Proof.
  intros r FIS gamma k Hgamma.
  apply (fis_contains_cyclic FIS gamma Hgamma).
  apply in_cyclic_pow.
Qed.

(** Inverse-powers of γ are in any FIS containing γ. *)
Corollary fis_contains_gamma_inv_pow :
  forall {r : nat} (FIS : FiniteIndexSubgroup (FreeGroup r))
         (gamma : RWord r) (k : nat),
    fis_pred FIS gamma -> fis_pred FIS (gamma_pow (rword_inv gamma) k).
Proof.
  intros r FIS gamma k Hgamma.
  apply (fis_contains_cyclic FIS gamma Hgamma).
  apply in_cyclic_inv_pow.
Qed.

(* ================================================================== *)
(** * 1.8. F_0 is trivial                                               *)
(* ================================================================== *)

(** F_0 has no generators, so it's the trivial group: every element
    is the identity. *)
Lemma F_0_word_nil : forall (w : Word 0), w = [].
Proof.
  intros w. destruct w as [|x rest].
  - reflexivity.
  - exfalso. destruct x as [i b]. inversion i.
Qed.

Lemma F_0_trivial : forall (w : RWord 0), w = @rword_e 0.
Proof.
  intros [w Hw]. apply rword_eq. apply F_0_word_nil.
Qed.

(** In F_0, every element is in ⟨γ⟩ for any γ (vacuously, since
    everything = e and ⟨γ⟩ ∋ e). *)
Corollary F_0_in_cyclic : forall (gamma w : RWord 0),
    in_cyclic gamma w.
Proof.
  intros gamma w. rewrite (F_0_trivial w). apply in_cyclic_id.
Qed.

(** No nontrivial element exists in F_0. *)
Lemma F_0_no_nontrivial : forall (gamma : RWord 0),
    gamma <> @rword_e 0 -> False.
Proof.
  intros gamma Hne. apply Hne. apply F_0_trivial.
Qed.

(** Hall's axiom is vacuously discharged for r = 0 (no nontrivial γ). *)
Lemma hall_finite_index_free_factor_r0 :
  forall (gamma : RWord 0),
    gamma <> @rword_e 0 ->
    exists (FIS : FiniteIndexSubgroup (FreeGroup 0)),
      forall i : nat,
        i < fis_index FIS ->
        nth_error (fis_trans FIS) i = Some (gamma_pow gamma i).
Proof.
  intros gamma Hne. exfalso. exact (F_0_no_nontrivial gamma Hne).
Qed.

(** Every element of Fin.t 1 equals F1 (Fin.t 1 is contractible).
    Standard inversion via Fin.caseS'. *)
Lemma Fin_t_1_unique : forall (x : Fin.t 1), x = Fin.F1.
Proof.
  intros x.
  apply (Fin.caseS' x); [reflexivity|].
  intros y. inversion y.
Qed.

(** Every Letter 1 is either (F1, false) or (F1, true). *)
Lemma Letter_1_dichotomy : forall (l : Letter 1),
    l = (Fin.F1, false) \/ l = (Fin.F1, true).
Proof.
  intros [i b].
  rewrite (Fin_t_1_unique i).
  destruct b.
  - right. reflexivity.
  - left. reflexivity.
Qed.

(** In F_1, the generator is gen 0 := free_gen_RWord 1 F1.
    The two letters are generator and its inverse. *)
Lemma Letter_1_is_gen_or_inv : forall (l : Letter 1),
    l = free_gen_letter 1 Fin.F1 \/ l = letter_inv (free_gen_letter 1 Fin.F1).
Proof.
  intros l. unfold free_gen_letter, letter_inv. simpl.
  apply Letter_1_dichotomy.
Qed.

(** Adjacent letters in a reduced F_1 word are equal. *)
Lemma F_1_adjacent_equal : forall (l l' : Letter 1) (rest : Word 1),
    reduced (l :: l' :: rest) -> l' = l.
Proof.
  intros l l' rest Hred.
  unfold reduced in Hred.
  destruct (letter_eq_dec l' (letter_inv l)) as [Heq|Hne].
  - rewrite cancel_step_cancel in Hred by exact Heq. discriminate.
  - destruct (Letter_1_dichotomy l) as [Hl|Hl];
    destruct (Letter_1_dichotomy l') as [Hl'|Hl'];
    rewrite Hl, Hl' in *.
    + reflexivity.
    + exfalso. apply Hne. unfold letter_inv. simpl. reflexivity.
    + exfalso. apply Hne. unfold letter_inv. simpl. reflexivity.
    + reflexivity.
Qed.

(** Tail of a reduced word is reduced. *)
Lemma reduced_tail : forall {r : nat} (l : Letter r) (rest : Word r),
    reduced (l :: rest) -> reduced rest.
Proof.
  intros r l rest Hred. unfold reduced in *.
  pose proof (cancel_step_none_suffix [l] rest) as Hsuf.
  cbn [List.app] in Hsuf. apply Hsuf. exact Hred.
Qed.

(** A list whose every element is l equals repeat l (length list). *)
Lemma list_all_equal_eq_repeat :
  forall {A : Type} (w : list A) (l : A),
    (forall l', List.In l' w -> l' = l) ->
    w = List.repeat l (List.length w).
Proof.
  intros A w l Hall.
  induction w as [|h rest IH].
  - reflexivity.
  - simpl. f_equal.
    + apply Hall. left. reflexivity.
    + apply IH. intros l' Hin. apply Hall. right. exact Hin.
Qed.

(** A reduced F_1 word has all letters equal (or is empty). *)
Lemma F_1_reduced_all_equal : forall (w : Word 1),
    reduced w ->
    forall l1 l2, List.In l1 w -> List.In l2 w -> l1 = l2.
Proof.
  intros w Hred.
  induction w as [|h rest IH]; intros l1 l2 H1 H2.
  - inversion H1.
  - pose proof (reduced_tail h rest Hred) as Hred'.
    destruct H1 as [H1|H1]; destruct H2 as [H2|H2].
    + congruence.
    + (* l1 = h, l2 ∈ rest *)
      destruct rest as [|h' rest'].
      * inversion H2.
      * pose proof (F_1_adjacent_equal h h' rest' Hred) as Hh'.
        rewrite <- H1, <- Hh'.
        apply (IH Hred' h' l2); [left; reflexivity|exact H2].
    + destruct rest as [|h' rest'].
      * inversion H1.
      * pose proof (F_1_adjacent_equal h h' rest' Hred) as Hh'.
        rewrite <- H2, <- Hh'.
        symmetry.
        apply (IH Hred' h' l1); [left; reflexivity|exact H1].
    + apply (IH Hred' l1 l2 H1 H2).
Qed.


(** Hall's axiom for r = 1 is dischargeable using trivial_FIS:
    fis_index = 1, fis_trans = [rword_e] = [gamma^0]. The condition
    holds vacuously beyond i = 0, since fis_index = 1 means i < 1
    forces i = 0. *)
Lemma hall_finite_index_free_factor_r1 :
  forall (gamma : RWord 1),
    gamma <> @rword_e 1 ->
    exists (FIS : FiniteIndexSubgroup (FreeGroup 1)),
      forall i : nat,
        i < fis_index FIS ->
        nth_error (fis_trans FIS) i = Some (gamma_pow gamma i).
Proof.
  intros gamma Hne. exists (trivial_FIS 1).
  intros i Hi. rewrite trivial_FIS_index in Hi.
  destruct i; [|lia].
  rewrite trivial_FIS_trans. simpl. reflexivity.
Qed.

(** Stronger r = 1 statement: works without γ ≠ e hypothesis. *)
Lemma hall_finite_index_free_factor_r1_general :
  forall (gamma : RWord 1),
    exists (FIS : FiniteIndexSubgroup (FreeGroup 1)),
      forall i : nat,
        i < fis_index FIS ->
        nth_error (fis_trans FIS) i = Some (gamma_pow gamma i).
Proof.
  intros gamma. exists (trivial_FIS 1).
  intros i Hi. rewrite trivial_FIS_index in Hi.
  destruct i; [|lia].
  rewrite trivial_FIS_trans. simpl. reflexivity.
Qed.

(** Property B for F_0: trivially holds since F_0 is the trivial group. *)
Theorem F_0_property_B :
  forall (F : Type) (MG_family : nat -> MatrixGroup F),
    property_B (FreeGroup 0) MG_family.
Proof.
  intros F MG_family. unfold property_B.
  intros gamma. exists 0, (trivial_rep_general (FreeGroup 0) (MG_family 0)).
  intros eta Hnotconj.
  exfalso. apply Hnotconj.
  rewrite (F_0_trivial gamma). rewrite (F_0_trivial eta).
  apply are_conjugate_refl.
Qed.

(** Identity-separating rep for F_0: vacuously true. *)
Theorem free_id_separating_rep_r0 :
  forall (F : Type) (MG_family : nat -> MatrixGroup F),
    exists (n : nat) (rho : Representation (FreeGroup 0) (MG_family n)),
      forall eta : RWord 0,
        ~ are_conjugate (FreeGroup 0) (@rword_e 0) eta ->
        trace_at rho (@rword_e 0) <> trace_at rho eta.
Proof.
  intros F MG_family.
  exists 0, (trivial_rep_general (FreeGroup 0) (MG_family 0)).
  intros eta Hnotconj.
  exfalso. apply Hnotconj.
  rewrite (F_0_trivial eta).
  apply are_conjugate_refl.
Qed.

(** Property D for F_0: corollary of F_0_property_B + property_B_implies_D. *)
Theorem F_0_property_D :
  forall (F : Type) (MG_family : nat -> MatrixGroup F),
    property_D (FreeGroup 0) MG_family.
Proof.
  intros F MG_family.
  apply property_B_implies_D. apply F_0_property_B.
Qed.

(** Property A for F_0: trivially holds (no non-conjugate pairs in F_0). *)
Theorem F_0_property_A :
  forall (F : Type) (MG_family : nat -> MatrixGroup F),
    property_A (FreeGroup 0) MG_family.
Proof.
  intros F MG_family. unfold property_A.
  exists 0, (trivial_rep_general (FreeGroup 0) (MG_family 0)).
  intros gamma eta Hnotconj.
  exfalso. apply Hnotconj.
  rewrite (F_0_trivial gamma), (F_0_trivial eta).
  apply are_conjugate_refl.
Qed.

(** Property C for F_0: trivially holds. *)
Theorem F_0_property_C :
  forall (F : Type) (MG_family : nat -> MatrixGroup F),
    property_C (FreeGroup 0) MG_family.
Proof.
  intros F MG_family. unfold property_C.
  intros gammas.
  exists 0, (trivial_rep_general (FreeGroup 0) (MG_family 0)).
  intros gamma eta _ _ Hnotconj.
  exfalso. apply Hnotconj.
  rewrite (F_0_trivial gamma), (F_0_trivial eta).
  apply are_conjugate_refl.
Qed.

(** Uniform Property D for F_0: trivially holds. *)
Theorem F_0_uniform_D :
  forall (F : Type) (MG_family : nat -> MatrixGroup F),
    uniform_D (FreeGroup 0) MG_family.
Proof.
  intros F MG_family. unfold uniform_D.
  exists 0. intros gamma eta Hnotconj.
  exists (trivial_rep_general (FreeGroup 0) (MG_family 0)).
  exfalso. apply Hnotconj.
  rewrite (F_0_trivial gamma), (F_0_trivial eta).
  apply are_conjugate_refl.
Qed.

(** Uniform Property C for F_0: trivially holds. *)
Theorem F_0_uniform_C :
  forall (F : Type) (MG_family : nat -> MatrixGroup F),
    uniform_C (FreeGroup 0) MG_family.
Proof.
  intros F MG_family. unfold uniform_C.
  exists 0. intros gammas.
  exists (trivial_rep_general (FreeGroup 0) (MG_family 0)).
  intros gamma eta _ _ Hnotconj.
  exfalso. apply Hnotconj.
  rewrite (F_0_trivial gamma), (F_0_trivial eta).
  apply are_conjugate_refl.
Qed.

(** Property D' for F_0: holds for any MatrixGroup family. *)
Theorem F_0_property_D' :
  property_D' (FreeGroup 0).
Proof.
  unfold property_D'.
  intros F MG_family. apply F_0_property_D.
Qed.

(** Hall construction separates: vacuous for r = 0. *)
Theorem hall_construction_separates_r0 :
  forall (F : Type) (MG_family : nat -> MatrixGroup F)
         (gamma : RWord 0),
    gamma <> @rword_e 0 ->
    exists (n : nat) (rho : Representation (FreeGroup 0) (MG_family n)),
      forall eta : RWord 0,
        ~ are_conjugate (FreeGroup 0) gamma eta ->
        trace_at rho gamma <> trace_at rho eta.
Proof.
  intros F MG_family gamma Hne. exfalso.
  exact (F_0_no_nontrivial gamma Hne).
Qed.

(** Combined: full property_B for F_0 derived without Hall axioms.
    [free_groups_property_B] specialized to r = 0. *)
Corollary free_groups_property_B_r0 :
  forall (F : Type) (MG_family : nat -> MatrixGroup F),
    property_B (FreeGroup 0) MG_family.
Proof. apply F_0_property_B. Qed.

(** Hall free-factor decomposition for r = 0: vacuous. *)
Theorem hall_free_factor_decomp_r0 :
  forall (gamma : RWord 0) (Hgamma : gamma <> @rword_e 0)
         (FIS : FiniteIndexSubgroup (FreeGroup 0))
         (g : RWord 0),
    exists (k : nat) (delta : RWord 0),
      fis_pred FIS delta /\
      g = rword_mul (gamma_pow gamma k) delta.
Proof.
  intros gamma Hgamma FIS g.
  exfalso. exact (F_0_no_nontrivial gamma Hgamma).
Qed.

(** Hall free-factor decomposition for r = 1 + trivial_FIS:
    Take k = 0, delta = g. delta ∈ trivial_FIS trivially. *)
Theorem hall_free_factor_decomp_r1_trivial_FIS :
  forall (gamma : RWord 1) (Hgamma : gamma <> @rword_e 1)
         (g : RWord 1),
    exists (k : nat) (delta : RWord 1),
      fis_pred (trivial_FIS 1) delta /\
      g = rword_mul (gamma_pow gamma k) delta.
Proof.
  intros gamma Hgamma g.
  exists 0, g. split.
  - apply trivial_FIS_pred.
  - simpl. rewrite rword_id_left. reflexivity.
Qed.

(** γ^1 = γ in F_r. *)
Lemma gamma_pow_one_eq : forall {r : nat} (gamma : RWord r),
    gamma_pow gamma 1 = gamma.
Proof.
  intros r gamma. simpl. apply rword_id_right.
Qed.

(** γ^k ∈ FIS iff γ ∈ FIS, for all k ≥ 1. The k = 0 case gives e ∈ FIS
    unconditionally; we focus on the substantive direction. *)
Lemma fis_pred_iff_pow_one :
  forall {r : nat} (FIS : FiniteIndexSubgroup (FreeGroup r))
         (gamma : RWord r),
    fis_pred FIS gamma <-> fis_pred FIS (gamma_pow gamma 1).
Proof.
  intros r FIS gamma.
  rewrite gamma_pow_one_eq. reflexivity.
Qed.

(** Bidirectional: γ ∈ FIS implies all powers in FIS, and γ ∈ FIS
    follows from γ^1 ∈ FIS. *)
Theorem fis_pred_pow_iff :
  forall {r : nat} (FIS : FiniteIndexSubgroup (FreeGroup r))
         (gamma : RWord r),
    fis_pred FIS gamma <->
    forall k : nat, fis_pred FIS (gamma_pow gamma k).
Proof.
  intros r FIS gamma. split.
  - intros Hg k. exact (fis_contains_gamma_pow FIS gamma k Hg).
  - intros H. specialize (H 1). rewrite gamma_pow_one_eq in H. exact H.
Qed.

(** γ^a · γ^b = γ^b · γ^a in F_r (powers commute). This is a clean
    restatement of [gamma_pow_commute] for direct use. *)
Lemma gamma_pow_pow_commute :
  forall {r : nat} (gamma : RWord r) (a b : nat),
    rword_mul (gamma_pow gamma a) (gamma_pow gamma b) =
    rword_mul (gamma_pow gamma b) (gamma_pow gamma a).
Proof.
  intros r gamma a b. apply gamma_pow_commute.
Qed.

(** Conjugacy of powers: γ^a · γ^b · (γ^a)^{-1} = γ^b. The cyclic
    subgroup is abelian, so conjugation is trivial. *)
Lemma gamma_pow_conjugate_self :
  forall {r : nat} (gamma : RWord r) (a b : nat),
    rword_mul (rword_mul (gamma_pow gamma a) (gamma_pow gamma b))
              (rword_inv (gamma_pow gamma a)) =
    gamma_pow gamma b.
Proof.
  intros r gamma a b.
  rewrite (gamma_pow_commute gamma a b).
  rewrite <- rword_assoc.
  rewrite rword_inv_right.
  apply rword_id_right.
Qed.

(** γ commutes with any power of γ^{-1}. *)
Lemma gamma_commute_inv_pow :
  forall {r : nat} (gamma : RWord r) (b : nat),
    rword_mul gamma (gamma_pow (rword_inv gamma) b) =
    rword_mul (gamma_pow (rword_inv gamma) b) gamma.
Proof.
  intros r gamma b. induction b as [|b IH].
  - simpl. rewrite rword_id_left, rword_id_right. reflexivity.
  - (* γ · (γ^{-1})^(S b) = γ · γ^{-1} · (γ^{-1})^b = (γ^{-1})^b
       (γ^{-1})^(S b) · γ = γ^{-1} · ((γ^{-1})^b · γ)
                          = γ^{-1} · (γ · (γ^{-1})^b)   [by IH backward]
                          = (γ^{-1} · γ) · (γ^{-1})^b = (γ^{-1})^b *)
    rewrite gamma_inv_cancel_left.
    change (gamma_pow (rword_inv gamma) (S b))
      with (rword_mul (rword_inv gamma) (gamma_pow (rword_inv gamma) b)).
    (* Goal: (γ^{-1})^b = ((γ^{-1}) · (γ^{-1})^b) · γ *)
    rewrite <- (rword_assoc (rword_inv gamma) (gamma_pow (rword_inv gamma) b) gamma).
    rewrite <- IH.
    rewrite (rword_assoc (rword_inv gamma) gamma (gamma_pow (rword_inv gamma) b)).
    rewrite rword_inv_left.
    rewrite rword_id_left. reflexivity.
Qed.

(** γ^a commutes with γ^{-1}: extending gamma_commute_inv_pow. *)
Lemma gamma_pow_commute_inv :
  forall {r : nat} (gamma : RWord r) (a : nat),
    rword_mul (gamma_pow gamma a) (rword_inv gamma) =
    rword_mul (rword_inv gamma) (gamma_pow gamma a).
Proof.
  intros r gamma a.
  induction a as [|a IH].
  - simpl. rewrite rword_id_left, rword_id_right. reflexivity.
  - change (gamma_pow gamma (S a)) with (rword_mul gamma (gamma_pow gamma a)).
    (* LHS: (γ · γ^a) · γ^{-1}, RHS: γ^{-1} · (γ · γ^a).
       Move LHS: → γ · (γ^a · γ^{-1}) → γ · (γ^{-1} · γ^a) [IH]
                → (γ · γ^{-1}) · γ^a → e · γ^a → γ^a.
       Move RHS: γ^{-1} · (γ · γ^a) → (γ^{-1} · γ) · γ^a → e · γ^a → γ^a. *)
    rewrite <- (rword_assoc gamma (gamma_pow gamma a) (rword_inv gamma)).
    rewrite IH.
    rewrite (rword_assoc gamma (rword_inv gamma) (gamma_pow gamma a)).
    rewrite rword_inv_right. rewrite rword_id_left.
    rewrite (rword_assoc (rword_inv gamma) gamma (gamma_pow gamma a)).
    rewrite rword_inv_left. rewrite rword_id_left.
    reflexivity.
Qed.

(** γ^a commutes with (γ^{-1})^b. *)
Lemma gamma_pow_commute_inv_pow :
  forall {r : nat} (gamma : RWord r) (a b : nat),
    rword_mul (gamma_pow gamma a) (gamma_pow (rword_inv gamma) b) =
    rword_mul (gamma_pow (rword_inv gamma) b) (gamma_pow gamma a).
Proof.
  intros r gamma a. induction a as [|a IH]; intro b.
  - change (gamma_pow gamma 0) with (@rword_e r).
    rewrite rword_id_left, rword_id_right. reflexivity.
  - change (gamma_pow gamma (S a)) with (rword_mul gamma (gamma_pow gamma a)).
    (* LHS: (γ · γ^a) · (γ^{-1})^b → γ · (γ^a · (γ^{-1})^b) [<- assoc]
                                  → γ · ((γ^{-1})^b · γ^a)  [IH]
                                  → (γ · (γ^{-1})^b) · γ^a  [forward assoc]
                                  → ((γ^{-1})^b · γ) · γ^a  [gamma_commute_inv_pow]
       RHS: (γ^{-1})^b · (γ · γ^a) → ((γ^{-1})^b · γ) · γ^a [forward assoc] *)
    rewrite <- (rword_assoc gamma (gamma_pow gamma a) (gamma_pow (rword_inv gamma) b)).
    rewrite (IH b).
    rewrite (rword_assoc gamma (gamma_pow (rword_inv gamma) b) (gamma_pow gamma a)).
    rewrite gamma_commute_inv_pow.
    rewrite (rword_assoc (gamma_pow (rword_inv gamma) b) gamma (gamma_pow gamma a)).
    reflexivity.
Qed.

(** ⟨γ⟩ is abelian: any two elements commute. *)
Lemma in_cyclic_abelian :
  forall {r : nat} (gamma a b : RWord r),
    in_cyclic gamma a -> in_cyclic gamma b ->
    rword_mul a b = rword_mul b a.
Proof.
  intros r gamma a b Ha Hb.
  destruct Ha as [[na Hna] | [na Hna]];
  destruct Hb as [[nb Hnb] | [nb Hnb]];
  subst a b.
  - apply gamma_pow_commute.
  - apply gamma_pow_commute_inv_pow.
  - symmetry. apply gamma_pow_commute_inv_pow.
  - apply gamma_pow_commute.
Qed.

(** For any g ∈ ⟨γ⟩ and any h ∈ ⟨γ⟩, conjugation by g is trivial
    (since ⟨γ⟩ is abelian). *)
Lemma in_cyclic_conjugate_trivial :
  forall {r : nat} (gamma g h : RWord r),
    in_cyclic gamma g ->
    in_cyclic gamma h ->
    rword_mul (rword_mul g h) (rword_inv g) = h.
Proof.
  intros r gamma g h Hg Hh.
  rewrite (in_cyclic_abelian gamma g h Hg Hh).
  rewrite <- rword_assoc.
  rewrite rword_inv_right.
  apply rword_id_right.
Qed.

(** Closure under conjugation by ⟨γ⟩-elements: if g ∈ ⟨γ⟩ and h ∈ ⟨γ⟩,
    then g · h · g^{-1} = h ∈ ⟨γ⟩. Trivial since ⟨γ⟩ is abelian. *)
Lemma in_cyclic_conj_closed : forall {r : nat} (gamma g h : RWord r),
    in_cyclic gamma g ->
    in_cyclic gamma h ->
    in_cyclic gamma (rword_mul (rword_mul g h) (rword_inv g)).
Proof.
  intros r gamma g h Hg Hh.
  rewrite (in_cyclic_conjugate_trivial gamma g h Hg Hh).
  exact Hh.
Qed.

(** Conjugation of γ^b by γ^a (both in ⟨γ⟩) is trivial. *)
Corollary gamma_pow_conjugate_pow :
  forall {r : nat} (gamma : RWord r) (a b : nat),
    rword_mul (rword_mul (gamma_pow gamma a) (gamma_pow gamma b))
              (rword_inv (gamma_pow gamma a)) =
    gamma_pow gamma b.
Proof.
  intros r gamma a b.
  apply (in_cyclic_conjugate_trivial gamma).
  - apply in_cyclic_pow.
  - apply in_cyclic_pow.
Qed.

(** gamma_pow gamma is a homomorphism from (nat, +) to F_r. *)
Theorem gamma_pow_is_homomorphism :
  forall {r : nat} (gamma : RWord r),
    (* gamma^0 = e *)
    gamma_pow gamma 0 = @rword_e r /\
    (* gamma^(a+b) = gamma^a · gamma^b *)
    forall a b : nat,
      gamma_pow gamma (a + b) =
      rword_mul (gamma_pow gamma a) (gamma_pow gamma b).
Proof.
  intros r gamma. split.
  - reflexivity.
  - apply gamma_pow_add.
Qed.

(** Conjugation distributes over multiplication:
    (g · a · g^{-1}) · (g · b · g^{-1}) = g · (a · b) · g^{-1}. *)
Lemma rword_conj_distribute :
  forall {r : nat} (g a b : RWord r),
    rword_mul (rword_mul (rword_mul g a) (rword_inv g))
              (rword_mul (rword_mul g b) (rword_inv g)) =
    rword_mul (rword_mul g (rword_mul a b)) (rword_inv g).
Proof.
  intros r g a b.
  (* X = g·a, Y = g·b, X·g^{-1} · Y·g^{-1} = ... *)
  set (X := rword_mul g a). set (Y := rword_mul g b).
  (* LHS: (X · g^{-1}) · (Y · g^{-1}) *)
  rewrite <- (rword_assoc X (rword_inv g) (rword_mul Y (rword_inv g))).
  (* X · (g^{-1} · (Y · g^{-1})) *)
  rewrite (rword_assoc (rword_inv g) Y (rword_inv g)).
  (* X · ((g^{-1} · Y) · g^{-1}) *)
  unfold Y.
  rewrite (rword_assoc (rword_inv g) g b).
  (* X · (((g^{-1} · g) · b) · g^{-1}) *)
  rewrite rword_inv_left.
  (* X · ((rword_e · b) · g^{-1}) *)
  rewrite (rword_id_left).
  (* X · (b · g^{-1}) *)
  unfold X.
  (* (g · a) · (b · g^{-1}) → ((g · a) · b) · g^{-1} *)
  rewrite (rword_assoc (rword_mul g a) b (rword_inv g)).
  (* ((g · a) · b) · g^{-1} → (g · (a · b)) · g^{-1} *)
  rewrite <- (rword_assoc g a b).
  reflexivity.
Qed.

(** Conjugation maps ⟨γ⟩ to ⟨gγg^{-1}⟩ for any g. *)
Lemma in_cyclic_conjugate_image :
  forall {r : nat} (gamma g : RWord r) (k : nat),
    rword_mul (rword_mul g (gamma_pow gamma k)) (rword_inv g) =
    gamma_pow (rword_mul (rword_mul g gamma) (rword_inv g)) k.
Proof.
  intros r gamma g k. induction k as [|k IH].
  - simpl. rewrite rword_id_right. apply rword_inv_right.
  - simpl. rewrite <- IH.
    symmetry. apply rword_conj_distribute.
Qed.

(** rword_length of gamma_pow is bounded by k * length gamma. *)
Lemma rword_length_gamma_pow_le :
  forall {r : nat} (gamma : RWord r) (k : nat),
    rword_length (gamma_pow gamma k) <= k * rword_length gamma.
Proof.
  intros r gamma k. induction k as [|k IH].
  - simpl. unfold rword_length, rword_e. simpl. lia.
  - simpl.
    pose proof (rword_mul_length_le gamma (gamma_pow gamma k)) as Hmul.
    lia.
Qed.

(** Cancel-step on a list of all the same non-self-inverse letter is None. *)
Lemma cancel_step_repeat_same :
  forall {r : nat} (l : Letter r),
    l <> letter_inv l ->
    forall k, cancel_step (List.repeat l k) = None.
Proof.
  intros r l Hne k.
  induction k as [|k IH].
  { reflexivity. }
  destruct k as [|k'].
  { reflexivity. }
  simpl in *.
  destruct (letter_eq_dec l (letter_inv l)) as [Heq|_].
  { contradiction. }
  rewrite IH. reflexivity.
Qed.

(** A list of all the same generator-letter is reduced. *)
Lemma reduced_repeat_gen : forall (n : nat) (i : Fin.t n) (k : nat),
    reduced (List.repeat (free_gen_letter n i) k).
Proof.
  intros n i k. unfold reduced.
  apply cancel_step_repeat_same.
  unfold free_gen_letter, letter_inv. simpl.
  intro H. inversion H. (* (i, false) ≠ (i, true) since false ≠ true *)
Qed.

(** Powers of a generator have length equal to the exponent. *)
Lemma gamma_pow_gen_proj :
  forall (n : nat) (i : Fin.t n) (k : nat),
    proj1_sig (gamma_pow (free_gen_RWord n i) k) =
    List.repeat (free_gen_letter n i) k.
Proof.
  intros n i k. induction k as [|k IH].
  - reflexivity.
  - simpl. unfold rword_mul. simpl.
    rewrite IH.
    (* reduce (gen i :: repeat (gen i) k) = gen i :: repeat (gen i) k *)
    apply reduce_self.
    pose proof (reduced_repeat_gen n i (S k)) as Hred.
    simpl in Hred. exact Hred.
Qed.

(** Length of γ^k for γ a generator is exactly k. *)
Lemma rword_length_gamma_pow_gen :
  forall (n : nat) (i : Fin.t n) (k : nat),
    rword_length (gamma_pow (free_gen_RWord n i) k) = k.
Proof.
  intros n i k.
  unfold rword_length.
  rewrite gamma_pow_gen_proj.
  apply List.repeat_length.
Qed.

(** Powers of a generator are nontrivial (positive powers ≠ identity). *)
Lemma gamma_pow_gen_ne_e : forall (n : nat) (i : Fin.t n) (k : nat),
    k >= 1 ->
    gamma_pow (free_gen_RWord n i) k <> @rword_e n.
Proof.
  intros n i k Hk Hcontra.
  pose proof (rword_length_gamma_pow_gen n i k) as Hlen.
  rewrite Hcontra in Hlen.
  unfold rword_length, rword_e in Hlen. simpl in Hlen. lia.
Qed.

(** Generator power is identity iff exponent is zero. *)
Lemma gamma_pow_gen_eq_e_iff : forall (n : nat) (i : Fin.t n) (k : nat),
    gamma_pow (free_gen_RWord n i) k = @rword_e n <-> k = 0.
Proof.
  intros n i k. split.
  - intros Heq.
    destruct k as [|k']; [reflexivity|].
    exfalso. apply (gamma_pow_gen_ne_e n i (S k') ltac:(lia)). exact Heq.
  - intros ->. reflexivity.
Qed.

(** Generators have infinite order: distinct exponents give distinct powers. *)
Theorem gamma_pow_gen_inj :
  forall (n : nat) (i : Fin.t n) (a b : nat),
    gamma_pow (free_gen_RWord n i) a =
    gamma_pow (free_gen_RWord n i) b ->
    a = b.
Proof.
  intros n i a b Heq.
  pose proof (rword_length_gamma_pow_gen n i a) as Ha.
  pose proof (rword_length_gamma_pow_gen n i b) as Hb.
  rewrite Heq in Ha. lia.
Qed.

(** Distinct generators yield distinct (nontrivial) powers.
    The cyclic subgroups generated by distinct generators are
    "trivially intersecting" (well, just on the identity). *)
Lemma gamma_pow_gen_distinct :
  forall (n : nat) (i j : Fin.t n) (a b : nat),
    i <> j ->
    1 <= a ->
    1 <= b ->
    gamma_pow (free_gen_RWord n i) a <>
    gamma_pow (free_gen_RWord n j) b.
Proof.
  intros n i j a b Hij Ha Hb Heq.
  apply (f_equal (@proj1_sig _ _)) in Heq.
  rewrite gamma_pow_gen_proj in Heq.
  rewrite gamma_pow_gen_proj in Heq.
  (* repeat (i, false) a = repeat (j, false) b *)
  destruct a as [|a']; [lia|].
  destruct b as [|b']; [lia|].
  simpl in Heq.
  inversion Heq as [Hij'].
  apply Hij. exact Hij'.
Qed.

(** All powers of a generator are positive RWords. *)
Lemma gamma_pow_gen_is_positive :
  forall (n : nat) (i : Fin.t n) (k : nat),
    is_positive_RWord (gamma_pow (free_gen_RWord n i) k).
Proof.
  intros n i k. unfold is_positive_RWord.
  rewrite gamma_pow_gen_proj.
  induction k as [|k IH].
  - constructor.
  - simpl. constructor.
    + reflexivity.
    + exact IH.
Qed.

(** Distinct generators have distinct length-1 elements. *)
Lemma free_gen_RWord_inj :
  forall (n : nat) (i j : Fin.t n),
    i <> j ->
    free_gen_RWord n i <> free_gen_RWord n j.
Proof.
  intros n i j Hij Heq.
  apply (f_equal (@proj1_sig _ _)) in Heq.
  unfold free_gen_RWord in Heq. simpl in Heq.
  inversion Heq as [Hij'].
  apply Hij. exact Hij'.
Qed.

(** rword_inv of a generator: explicit form. *)
Lemma rword_inv_gen_proj :
  forall (n : nat) (i : Fin.t n),
    proj1_sig (rword_inv (free_gen_RWord n i)) = [(i, true)].
Proof.
  intros n i. unfold rword_inv, free_gen_RWord. simpl. reflexivity.
Qed.

(** Length 1 of rword_inv of a generator. *)
Lemma rword_length_inv_gen :
  forall (n : nat) (i : Fin.t n),
    rword_length (rword_inv (free_gen_RWord n i)) = 1.
Proof.
  intros n i. unfold rword_length. rewrite rword_inv_gen_proj. reflexivity.
Qed.

(** Generator and its inverse are distinct. *)
Lemma free_gen_RWord_ne_inv :
  forall (n : nat) (i : Fin.t n),
    free_gen_RWord n i <> rword_inv (free_gen_RWord n i).
Proof.
  intros n i Heq.
  pose proof (f_equal (@proj1_sig _ _) Heq) as Heq'.
  rewrite rword_inv_gen_proj in Heq'.
  unfold free_gen_RWord in Heq'. simpl in Heq'.
  inversion Heq'.
Qed.

(** Generator is never equal to inverse of any (other) generator. *)
Lemma free_gen_RWord_ne_inv_any :
  forall (n : nat) (i j : Fin.t n),
    free_gen_RWord n i <> rword_inv (free_gen_RWord n j).
Proof.
  intros n i j Heq.
  pose proof (f_equal (@proj1_sig _ _) Heq) as Heq'.
  rewrite rword_inv_gen_proj in Heq'.
  unfold free_gen_RWord in Heq'. simpl in Heq'.
  inversion Heq'.
Qed.

(** Generator is never the identity (concrete corollary). *)
Lemma free_gen_RWord_concrete_ne_e :
  forall (n : nat) (i : Fin.t n),
    proj1_sig (free_gen_RWord n i) <> [].
Proof.
  intros n i. simpl. discriminate.
Qed.

(** A list of repeated inverted-generator letter is reduced. *)
Lemma reduced_repeat_gen_inv : forall (n : nat) (i : Fin.t n) (k : nat),
    reduced (List.repeat (i, true) k).
Proof.
  intros n i k. unfold reduced.
  apply cancel_step_repeat_same.
  unfold letter_inv. simpl.
  intro H. inversion H. (* (i, true) ≠ (i, false) since true ≠ false *)
Qed.

(** Powers of the inverted generator: explicit form. *)
Lemma gamma_pow_gen_inv_proj :
  forall (n : nat) (i : Fin.t n) (k : nat),
    proj1_sig (gamma_pow (rword_inv (free_gen_RWord n i)) k) =
    List.repeat (i, true) k.
Proof.
  intros n i k. induction k as [|k IH].
  - reflexivity.
  - simpl. unfold rword_mul. simpl.
    rewrite IH.
    apply reduce_self.
    pose proof (reduced_repeat_gen_inv n i (S k)) as Hred.
    simpl in Hred. exact Hred.
Qed.

(** Length of (γ_gen^{-1})^k = k. *)
Lemma rword_length_gamma_pow_gen_inv :
  forall (n : nat) (i : Fin.t n) (k : nat),
    rword_length (gamma_pow (rword_inv (free_gen_RWord n i)) k) = k.
Proof.
  intros n i k.
  unfold rword_length.
  rewrite gamma_pow_gen_inv_proj.
  apply List.repeat_length.
Qed.

(** Inverted generator has infinite order. *)
Lemma gamma_pow_gen_inv_ne_e : forall (n : nat) (i : Fin.t n) (k : nat),
    k >= 1 ->
    gamma_pow (rword_inv (free_gen_RWord n i)) k <> @rword_e n.
Proof.
  intros n i k Hk Hcontra.
  pose proof (rword_length_gamma_pow_gen_inv n i k) as Hlen.
  rewrite Hcontra in Hlen.
  unfold rword_length, rword_e in Hlen. simpl in Hlen. lia.
Qed.

Lemma gamma_pow_gen_inv_eq_e_iff : forall (n : nat) (i : Fin.t n) (k : nat),
    gamma_pow (rword_inv (free_gen_RWord n i)) k = @rword_e n <-> k = 0.
Proof.
  intros n i k. split.
  - intros Heq. destruct k as [|k']; [reflexivity|].
    exfalso. apply (gamma_pow_gen_inv_ne_e n i (S k') ltac:(lia)). exact Heq.
  - intros ->. reflexivity.
Qed.

(** Decidable equality on RWord r (any r). *)
Lemma rword_eq_dec : forall {r : nat} (a b : RWord r),
    {a = b} + {a <> b}.
Proof.
  intros r [wa Ha] [wb Hb].
  destruct (list_eq_dec letter_eq_dec wa wb) as [Heq|Hne].
  - left. apply rword_eq. exact Heq.
  - right. intros Hcontra.
    apply Hne.
    apply (f_equal (@proj1_sig _ _)) in Hcontra.
    simpl in Hcontra. exact Hcontra.
Qed.

(** Conjugacy in F_0 is decidable (trivially). *)
Lemma F_0_conjugacy_decidable :
  forall (a b : RWord 0),
    {are_conjugate (FreeGroup 0) a b} + {~ are_conjugate (FreeGroup 0) a b}.
Proof.
  intros a b. left.
  rewrite (F_0_trivial a), (F_0_trivial b).
  apply are_conjugate_refl.
Qed.

Theorem gamma_pow_gen_inv_inj :
  forall (n : nat) (i : Fin.t n) (a b : nat),
    gamma_pow (rword_inv (free_gen_RWord n i)) a =
    gamma_pow (rword_inv (free_gen_RWord n i)) b ->
    a = b.
Proof.
  intros n i a b Heq.
  pose proof (rword_length_gamma_pow_gen_inv n i a) as Ha.
  pose proof (rword_length_gamma_pow_gen_inv n i b) as Hb.
  rewrite Heq in Ha. lia.
Qed.

(** Positive and negative powers (≥ 1) of a generator are distinct. *)
Lemma gamma_pow_gen_pos_ne_neg :
  forall (n : nat) (i : Fin.t n) (a b : nat),
    1 <= a -> 1 <= b ->
    gamma_pow (free_gen_RWord n i) a <>
    gamma_pow (rword_inv (free_gen_RWord n i)) b.
Proof.
  intros n i a b Ha Hb Heq.
  apply (f_equal (@proj1_sig _ _)) in Heq.
  rewrite gamma_pow_gen_proj in Heq.
  rewrite gamma_pow_gen_inv_proj in Heq.
  destruct a as [|a']; [lia|].
  destruct b as [|b']; [lia|].
  simpl in Heq.
  inversion Heq.
Qed.

(** Cross-generator pos-vs-inv distinctness: positive powers of γ_i and
    inverse powers of γ_j (any i, j) are distinct when both ≥ 1, since
    they project to lists with opposite polarity letters. *)
Lemma gamma_pow_gen_diff_pos_ne_inv :
  forall (n : nat) (i j : Fin.t n) (a b : nat),
    1 <= a -> 1 <= b ->
    gamma_pow (free_gen_RWord n i) a <>
    gamma_pow (rword_inv (free_gen_RWord n j)) b.
Proof.
  intros n i j a b Ha Hb Heq.
  apply (f_equal (@proj1_sig _ _)) in Heq.
  rewrite gamma_pow_gen_proj in Heq.
  rewrite gamma_pow_gen_inv_proj in Heq.
  destruct a as [|a']; [lia|].
  destruct b as [|b']; [lia|].
  simpl in Heq.
  inversion Heq.
Qed.

(** Inverse-power injectivity for distinct generators: (γ_i^{-1})^a vs
    (γ_j^{-1})^b are distinct when i ≠ j and a, b ≥ 1. *)
Lemma gamma_pow_gen_inv_distinct :
  forall (n : nat) (i j : Fin.t n) (a b : nat),
    i <> j ->
    1 <= a ->
    1 <= b ->
    gamma_pow (rword_inv (free_gen_RWord n i)) a <>
    gamma_pow (rword_inv (free_gen_RWord n j)) b.
Proof.
  intros n i j a b Hij Ha Hb Heq.
  apply (f_equal (@proj1_sig _ _)) in Heq.
  rewrite gamma_pow_gen_inv_proj in Heq.
  rewrite gamma_pow_gen_inv_proj in Heq.
  destruct a as [|a']; [lia|].
  destruct b as [|b']; [lia|].
  simpl in Heq.
  inversion Heq as [Hij'].
  apply Hij. exact Hij'.
Qed.

(** F_1 classification: every element of F_1 is e, γ^k, or (γ^{-1})^k for
    γ = gen 0 (the unique generator). *)
Theorem F_1_classification : forall (w : RWord 1),
    w = @rword_e 1 \/
    (exists k, k >= 1 /\ w = gamma_pow (free_gen_RWord 1 Fin.F1) k) \/
    (exists k, k >= 1 /\
               w = gamma_pow (rword_inv (free_gen_RWord 1 Fin.F1)) k).
Proof.
  intros [w Hred].
  destruct w as [|h rest].
  - left. apply rword_eq. reflexivity.
  - (* w = h :: rest, all letters equal h by F_1_reduced_all_equal *)
    pose proof (F_1_reduced_all_equal (h :: rest) Hred) as Hall.
    assert (Hw : h :: rest = List.repeat h (S (List.length rest))).
    { pose proof (list_all_equal_eq_repeat (h :: rest) h) as Heq.
      simpl in Heq. apply Heq.
      intros l' Hin. specialize (Hall h l').
      symmetry. apply Hall.
      - left. reflexivity.
      - exact Hin. }
    destruct (Letter_1_dichotomy h) as [Hh|Hh].
    + (* h = (F1, false), so w is positive: γ^k *)
      right. left.
      exists (S (List.length rest)). split.
      * lia.
      * pose proof (gamma_pow_gen_proj 1 Fin.F1 (S (List.length rest))) as Hgp.
        destruct (gamma_pow (free_gen_RWord 1 Fin.F1) (S (List.length rest)))
          as [w' Hred'] eqn:Egp.
        simpl in Hgp.
        apply rword_eq. rewrite Hw, Hh.
        change (Fin.F1, false) with (free_gen_letter 1 Fin.F1).
        symmetry. exact Hgp.
    + (* h = (F1, true), so w is negative: (γ^{-1})^k *)
      right. right.
      exists (S (List.length rest)). split.
      * lia.
      * pose proof (gamma_pow_gen_inv_proj 1 Fin.F1 (S (List.length rest)))
          as Hgp.
        destruct (gamma_pow (rword_inv (free_gen_RWord 1 Fin.F1))
                            (S (List.length rest)))
          as [w' Hred'] eqn:Egp.
        simpl in Hgp.
        apply rword_eq. rewrite Hw, Hh.
        symmetry. exact Hgp.
Qed.

(** Every element of F_1 is in ⟨γ⟩ for γ = gen 0. *)
Corollary F_1_eq_cyclic_gen :
  forall (w : RWord 1),
    in_cyclic (free_gen_RWord 1 Fin.F1) w.
Proof.
  intros w. destruct (F_1_classification w) as [He | [[k [Hk Hw]] | [k [Hk Hw]]]].
  - rewrite He. apply in_cyclic_id.
  - rewrite Hw. apply in_cyclic_pow.
  - rewrite Hw. apply in_cyclic_inv_pow.
Qed.

(** F_1 is abelian: a · b = b · a. *)
Theorem F_1_abelian : forall (a b : RWord 1),
    rword_mul a b = rword_mul b a.
Proof.
  intros a b.
  apply (in_cyclic_abelian (free_gen_RWord 1 Fin.F1) a b).
  - apply F_1_eq_cyclic_gen.
  - apply F_1_eq_cyclic_gen.
Qed.

(** F_0 is abelian (trivially). *)
Theorem F_0_abelian : forall (a b : RWord 0),
    rword_mul a b = rword_mul b a.
Proof.
  intros a b.
  rewrite (F_0_trivial a). rewrite (F_0_trivial b).
  reflexivity.
Qed.

(** F_0 conjugacy = equality (since F_0 has only one element). *)
Theorem F_0_are_conjugate_iff_eq : forall (a b : RWord 0),
    are_conjugate (FreeGroup 0) a b <-> a = b.
Proof.
  intros a b. split.
  - intros _. rewrite (F_0_trivial a), (F_0_trivial b). reflexivity.
  - intros ->. apply are_conjugate_refl.
Qed.

(** F_1 commutator is trivial. *)
Theorem F_1_commutator_trivial : forall (a b : RWord 1),
    rword_mul (rword_mul (rword_mul a b) (rword_inv a)) (rword_inv b) =
    @rword_e 1.
Proof.
  intros a b.
  rewrite (F_1_abelian a b).
  rewrite <- (rword_assoc b a (rword_inv a)).
  rewrite rword_inv_right. rewrite rword_id_right.
  apply rword_inv_right.
Qed.

(** F_1 generator ≠ its inverse (different elements). *)
Lemma F_1_gen_ne_inv : free_gen_RWord 1 Fin.F1 <>
                        rword_inv (free_gen_RWord 1 Fin.F1).
Proof.
  apply free_gen_RWord_ne_inv.
Qed.

(** F_1 generator is non-trivial. *)
Lemma F_1_gen_ne_e : free_gen_RWord 1 Fin.F1 <> @rword_e 1.
Proof.
  apply free_gen_RWord_ne_e.
Qed.

(** Every subgroup of F_1 is normal (since F_1 is abelian).
    Specialized: ⟨γ⟩ is normal in F_1. *)
Theorem F_1_in_cyclic_normal :
  forall (gamma g h : RWord 1),
    in_cyclic gamma h ->
    in_cyclic gamma (rword_mul (rword_mul g h) (rword_inv g)).
Proof.
  intros gamma g h Hh.
  rewrite (F_1_abelian g h).
  rewrite <- rword_assoc.
  rewrite rword_inv_right.
  rewrite rword_id_right. exact Hh.
Qed.

(** F_0 commutator is trivial. *)
Theorem F_0_commutator_trivial : forall (a b : RWord 0),
    rword_mul (rword_mul (rword_mul a b) (rword_inv a)) (rword_inv b) =
    @rword_e 0.
Proof.
  intros a b.
  rewrite (F_0_abelian a b).
  rewrite <- (rword_assoc b a (rword_inv a)).
  rewrite rword_inv_right. rewrite rword_id_right.
  apply rword_inv_right.
Qed.

(** Conjugation in F_0 is trivial: (g·h)·g^{-1} = h. *)
Theorem F_0_conjugate_trivial : forall (g h : RWord 0),
    rword_mul (rword_mul g h) (rword_inv g) = h.
Proof.
  intros g h.
  rewrite (F_0_abelian g h).
  rewrite <- rword_assoc.
  rewrite rword_inv_right.
  apply rword_id_right.
Qed.

(** Conjugation in F_1 is trivial: (g·h)·g^{-1} = h. *)
Theorem F_1_conjugate_trivial : forall (g h : RWord 1),
    rword_mul (rword_mul g h) (rword_inv g) = h.
Proof.
  intros g h.
  rewrite (F_1_abelian g h).
  rewrite <- rword_assoc.
  rewrite rword_inv_right.
  apply rword_id_right.
Qed.

(** Conjugacy in F_1 = equality (since F_1 is abelian). *)
Theorem F_1_are_conjugate_iff_eq : forall (a b : RWord 1),
    are_conjugate (FreeGroup 1) a b <-> a = b.
Proof.
  intros a b. split.
  - intros [g Hg]. simpl in Hg.
    rewrite (F_1_abelian g a) in Hg.
    rewrite <- rword_assoc in Hg.
    rewrite rword_inv_right in Hg.
    rewrite rword_id_right in Hg.
    exact Hg.
  - intros ->. apply are_conjugate_refl.
Qed.

(** Conjugacy is preserved under taking powers: γ ~ η ⟹ γ^k ~ η^k. *)
Lemma are_conjugate_gamma_pow :
  forall {r : nat} (gamma eta : RWord r) (k : nat),
    are_conjugate (FreeGroup r) gamma eta ->
    are_conjugate (FreeGroup r) (gamma_pow gamma k) (gamma_pow eta k).
Proof.
  intros r gamma eta k [g Hg].
  exists g.
  simpl in Hg.
  change (smul (RWord r) (FreeGroup r)) with (@rword_mul r).
  change (sinv (RWord r) (FreeGroup r)) with (@rword_inv r).
  rewrite (in_cyclic_conjugate_image gamma g k).
  rewrite Hg. reflexivity.
Qed.

(** Hall's theorem: every nontrivial element of F_r lies in a
    finite-index subgroup as a free factor.
    Source: Hall, "Coset representations in free groups"
    (Trans. AMS 67, 1949, 421–432). Modern graph-theoretic proof:
    Stallings, "Topology of finite graphs" (Invent. Math., 1983).
    See AXIOMS_AUDIT.md.

    ✅ COMPLIANCE: Sound (deferred). Discharged for r=0 and r=1 in
    [hall_finite_index_free_factor_r0] and [hall_finite_index_free_factor_r1]. *)
Conjecture hall_finite_index_free_factor :
  forall (r : nat) (gamma : RWord r),
    gamma <> @rword_e r ->
    exists (FIS : FiniteIndexSubgroup (FreeGroup r)),
      fis_index FIS >= 1 /\
      fis_pred FIS gamma /\
      fis_pred FIS (@rword_e r).

(** Stronger version: the FIS has index at least 2 when r ≥ 2. *)

Conjecture hall_construction_separates :
  forall (r : nat) (F : Type) (MG_family : nat -> MatrixGroup F)
         (gamma : RWord r),
    gamma <> @rword_e r ->
    exists (n : nat) (rho : Representation (FreeGroup r) (MG_family n)),
      forall eta : RWord r,
        ~ are_conjugate (FreeGroup r) gamma eta ->
        trace_at rho gamma <> trace_at rho eta.

(* ================================================================== *)
(** * 4. Theorem 1.6 (free groups have property B) — derived            *)
(* ================================================================== *)

(** Combining Hall + the construction gives property (B) for F_r,
    DERIVED rather than axiomatized.

    Note: the trivial case γ = e is handled separately (e is conjugate
    only to itself, and ρ(e) = id has fixed trace, so this case is
    moot for property (B): it requires a separating rep for each γ;
    when γ = e there's nothing to separate). *)

(** Self-conjugacy of identity. *)
Lemma conjugate_trivial : forall (r : nat),
    are_conjugate (FreeGroup r) (@rword_e r) (@rword_e r).
Proof.
  intros r. exists (@rword_e r).
  rewrite <- (sassoc _ (FreeGroup r)).
  rewrite (sinv_right _ (FreeGroup r)).
  apply (sid_right _ (FreeGroup r)).
Qed.

(** Hall + induced rep + Frobenius is the proof strategy for paper
    Theorem 1.6. The full construction also has to handle γ = e
    (which requires a faithful trace-separating rep on F_r — known to
    exist via SL(2, Z) embeddings, etc.). We axiomatize the full
    conclusion here for the non-identity case via
    [hall_construction_separates], and the identity case via:

    [free_id_separating_rep]: there exists ρ on F_r with
        tr(ρ(e)) ≠ tr(ρ(η)) for all η ≠ e.

    For F_2 → SL(2, Z), this is classical (image is non-elementary,
    and for hyperbolic elements tr(η) ≠ 2 = tr(e)).

    Source: McReynolds–Lawton–Louder, "Decision problems, complexity,
    traces, and representations" (preprint), Theorem 1.6 and surrounding
    discussion. The classical SL(2, Z) embedding of free groups goes back
    to Sanov (1947) and Brenner (1955).
    See AXIOMS_AUDIT.md.

    ⚠️ COMPLIANCE: Suspect — quantification over arbitrary `MG_family`
    is too strong (a trivial 1-element matrix group admits no separating
    rep). The correct SL2 form for F_1 is
    [free_id_separating_rep_F1_SL2] in HallFreeGroup/InducedRepresentation.v,
    which discharges the result conditional on existence of a hyperbolic
    generator image. *)

Conjecture free_id_separating_rep :
  forall (r : nat) (F : Type) (MG_family : nat -> MatrixGroup F),
    exists (n : nat) (rho : Representation (FreeGroup r) (MG_family n)),
      forall eta : RWord r,
        ~ are_conjugate (FreeGroup r) (@rword_e r) eta ->
        trace_at rho (@rword_e r) <> trace_at rho eta.

(** Decidability of equality with identity in F_r — proven via
    decidable equality of the underlying Word + proof irrelevance for
    the reducedness witness. *)
From Stdlib Require Import Logic.ProofIrrelevance.

Lemma rword_eq_id_dec : forall {r : nat} (g : RWord r),
    {g = @rword_e r} + {g <> @rword_e r}.
Proof.
  intros r [w Hred].
  destruct (list_eq_dec letter_eq_dec w (@nil (Letter r))) as [Heq | Hne].
  - subst w. left.
    unfold rword_e.
    f_equal. apply proof_irrelevance.
  - right. intro Hcontra.
    apply (f_equal (@proj1_sig _ _)) in Hcontra.
    simpl in Hcontra. unfold rword_e in Hcontra.
    simpl in Hcontra. apply Hne. exact Hcontra.
Defined.

(** Theorem 1.6 (free groups have property B), now derivable. *)
Theorem free_groups_property_B :
  forall (r : nat) (F : Type) (MG_family : nat -> MatrixGroup F),
    property_B (FreeGroup r) MG_family.
Proof.
  intros r F MG_family.
  unfold property_B. intros gamma.
  destruct (rword_eq_id_dec gamma) as [Heq | Hne].
  - (* gamma = e *)
    subst gamma. apply (free_id_separating_rep r F MG_family).
  - (* gamma ≠ e *)
    apply (hall_construction_separates r F MG_family gamma Hne).
Qed.

(** Conjugacy in F_1 is decidable (= equality which is decidable). *)
Lemma F_1_conjugacy_decidable :
  forall (a b : RWord 1),
    {are_conjugate (FreeGroup 1) a b} + {~ are_conjugate (FreeGroup 1) a b}.
Proof.
  intros a b. destruct (rword_eq_dec a b) as [Heq|Hne].
  - left. apply F_1_are_conjugate_iff_eq. exact Heq.
  - right. intros Hcontra. apply Hne.
    apply F_1_are_conjugate_iff_eq. exact Hcontra.
Qed.

(** F_1 is torsion-free: any nontrivial element has infinite order. *)
Theorem F_1_torsion_free :
  forall (gamma : RWord 1) (k : nat),
    gamma <> @rword_e 1 ->
    gamma_pow gamma k = @rword_e 1 ->
    k = 0.
Proof.
  intros gamma k Hne Heq.
  destruct (F_1_classification gamma) as [He | [[a [Ha Hg]] | [a [Ha Hg]]]].
  - exfalso. apply Hne. exact He.
  - rewrite Hg in Heq.
    rewrite <- (gamma_pow_mul (free_gen_RWord 1 Fin.F1) k a) in Heq.
    apply gamma_pow_gen_eq_e_iff in Heq.
    destruct k as [|k']; [reflexivity|].
    exfalso. apply (Nat.neq_succ_0 (k' * a)). lia.
  - rewrite Hg in Heq.
    rewrite <- (gamma_pow_mul (rword_inv (free_gen_RWord 1 Fin.F1)) k a)
      in Heq.
    apply gamma_pow_gen_inv_eq_e_iff in Heq.
    destruct k as [|k']; [reflexivity|].
    exfalso. apply (Nat.neq_succ_0 (k' * a)). lia.
Qed.

(** F_1 powers are injective for any nontrivial γ: γ^a = γ^b ⟹ a = b. *)
Theorem F_1_pow_inj :
  forall (gamma : RWord 1) (a b : nat),
    gamma <> @rword_e 1 ->
    gamma_pow gamma a = gamma_pow gamma b ->
    a = b.
Proof.
  intros gamma a b Hne Heq.
  destruct (F_1_classification gamma) as [He | [[c [Hc Hg]] | [c [Hc Hg]]]].
  - exfalso. apply Hne. exact He.
  - rewrite Hg in Heq.
    rewrite <- (gamma_pow_mul (free_gen_RWord 1 Fin.F1) a c) in Heq.
    rewrite <- (gamma_pow_mul (free_gen_RWord 1 Fin.F1) b c) in Heq.
    apply gamma_pow_gen_inj in Heq.
    nia.
  - rewrite Hg in Heq.
    rewrite <- (gamma_pow_mul (rword_inv (free_gen_RWord 1 Fin.F1)) a c)
      in Heq.
    rewrite <- (gamma_pow_mul (rword_inv (free_gen_RWord 1 Fin.F1)) b c)
      in Heq.
    apply gamma_pow_gen_inv_inj in Heq.
    nia.
Qed.

(** In F_1, the cyclic subgroup ⟨γ⟩ for γ ≠ e is infinite (no two
    distinct exponents give the same element). *)
Theorem F_1_cyclic_subgroup_infinite :
  forall (gamma : RWord 1),
    gamma <> @rword_e 1 ->
    forall a b : nat, a <> b ->
      gamma_pow gamma a <> gamma_pow gamma b.
Proof.
  intros gamma Hne a b Hab Heq.
  apply Hab. apply (F_1_pow_inj gamma a b Hne Heq).
Qed.

(** Conjugation respects taking powers: are_conjugate g g' implies
    are_conjugate g^k g'^k for any natural k. Uses the existing
    [in_cyclic_conjugate_image]: g · γ^k · g^{-1} = (gγg^{-1})^k. *)
Theorem are_conjugate_pow_F :
  forall {r : nat} (g g' : RWord r) (k : nat),
    are_conjugate (FreeGroup r) g g' ->
    are_conjugate (FreeGroup r) (gamma_pow g k) (gamma_pow g' k).
Proof.
  intros r g g' k [h Hh].
  exists h.
  change (smul (RWord r) (FreeGroup r))
    with (@rword_mul r) in *.
  change (sinv (RWord r) (FreeGroup r))
    with (@rword_inv r) in *.
  rewrite (in_cyclic_conjugate_image g h k).
  rewrite Hh. reflexivity.
Qed.

(** Conjugation respects taking inverses: are_conjugate g g' implies
    are_conjugate g^{-1} g'^{-1}. Same witness h: (hgh^{-1})^{-1} =
    h · g^{-1} · h^{-1} via inv_mul-distributivity. *)
Theorem are_conjugate_inv_F :
  forall {r : nat} (g g' : RWord r),
    are_conjugate (FreeGroup r) g g' ->
    are_conjugate (FreeGroup r) (rword_inv g) (rword_inv g').
Proof.
  intros r g g' [h Hh]. exists h.
  change (smul (RWord r) (FreeGroup r))
    with (@rword_mul r) in *.
  change (sinv (RWord r) (FreeGroup r))
    with (@rword_inv r) in *.
  rewrite <- Hh.
  rewrite rword_inv_mul. rewrite rword_inv_mul.
  rewrite rword_inv_inv. rewrite rword_assoc. reflexivity.
Qed.

(** Contrapositive of [are_conjugate_pow_F]: if some pair of powers is
    non-conjugate, the originals are non-conjugate. Useful as the
    detection lemma for property-A-style separations. *)
Corollary not_are_conjugate_from_pow_F :
  forall {r : nat} (g g' : RWord r) (k : nat),
    ~ are_conjugate (FreeGroup r) (gamma_pow g k) (gamma_pow g' k) ->
    ~ are_conjugate (FreeGroup r) g g'.
Proof.
  intros r g g' k Hnc Hc.
  apply Hnc. apply (are_conjugate_pow_F g g' k Hc).
Qed.

(** Contrapositive of [are_conjugate_inv_F]. *)
Corollary not_are_conjugate_from_inv_F :
  forall {r : nat} (g g' : RWord r),
    ~ are_conjugate (FreeGroup r) (rword_inv g) (rword_inv g') ->
    ~ are_conjugate (FreeGroup r) g g'.
Proof.
  intros r g g' Hnc Hc.
  apply Hnc. apply (are_conjugate_inv_F g g' Hc).
Qed.

(** Conjugacy by g and by g^{-1} are inverses: if h conjugates a to b,
    then h^{-1} conjugates b back to a. Used as a building block for
    are_conjugate_sym / inverse-image arguments. *)
Lemma rword_conj_inverse_witness :
  forall {r : nat} (h a : RWord r),
    rword_mul (rword_mul (rword_inv h)
                          (rword_mul (rword_mul h a) (rword_inv h)))
              (rword_inv (rword_inv h)) = a.
Proof.
  intros r h a.
  rewrite rword_inv_inv.
  (* Goal: (h^{-1} · ((h·a)·h^{-1})) · h = a;
     rword_assoc is u·(v·w) = (u·v)·w, so we rewrite backwards. *)
  rewrite <- (rword_assoc (rword_inv h)
                          (rword_mul (rword_mul h a) (rword_inv h)) h).
  rewrite <- (rword_assoc (rword_mul h a) (rword_inv h) h).
  rewrite rword_inv_left. rewrite rword_id_right.
  rewrite (rword_assoc (rword_inv h) h a).
  rewrite rword_inv_left. rewrite rword_id_left. reflexivity.
Qed.

(** Inverse of a conjugation is the conjugation of the inverse:
    (g · a · g^{-1})^{-1} = g · a^{-1} · g^{-1}. *)
Lemma rword_inv_conj :
  forall {r : nat} (g a : RWord r),
    rword_inv (rword_mul (rword_mul g a) (rword_inv g)) =
    rword_mul (rword_mul g (rword_inv a)) (rword_inv g).
Proof.
  intros r g a.
  rewrite (rword_inv_mul (rword_mul g a) (rword_inv g)).
  rewrite rword_inv_inv.
  rewrite (rword_inv_mul g a).
  apply rword_assoc.
Qed.

(** Conjugation maps cyclic subgroups: h ∈ ⟨γ⟩ implies ghg^{-1} ∈ ⟨gγg^{-1}⟩. *)
Theorem in_cyclic_conjugate :
  forall {r : nat} (gamma g h : RWord r),
    in_cyclic gamma h ->
    in_cyclic (rword_mul (rword_mul g gamma) (rword_inv g))
              (rword_mul (rword_mul g h) (rword_inv g)).
Proof.
  intros r gamma g h Hh.
  destruct Hh as [[k Hk] | [k Hk]]; subst h.
  - left. exists k. apply in_cyclic_conjugate_image.
  - right. exists k.
    rewrite (in_cyclic_conjugate_image (rword_inv gamma) g k).
    rewrite <- rword_inv_conj. reflexivity.
Qed.

(** Conjugacy is closed under the iff form: are_conjugate γ γ' implies
    that ⟨γ⟩ and ⟨γ'⟩ are conjugate as subgroups (one is the image of
    the other under conjugation). *)
Corollary in_cyclic_conjugate_subgroups :
  forall {r : nat} (gamma gamma' : RWord r),
    are_conjugate (FreeGroup r) gamma gamma' ->
    forall h, in_cyclic gamma h ->
    exists h', in_cyclic gamma' h' /\
               are_conjugate (FreeGroup r) h h'.
Proof.
  intros r gamma gamma' [g Hgg'] h Hh.
  exists (rword_mul (rword_mul g h) (rword_inv g)).
  change (smul (RWord r) (FreeGroup r))
    with (@rword_mul r) in Hgg'.
  change (sinv (RWord r) (FreeGroup r))
    with (@rword_inv r) in Hgg'.
  split.
  - rewrite <- Hgg'. apply in_cyclic_conjugate. exact Hh.
  - exists g. exact eq_refl.
Qed.

(** Conjugacy is preserved under taking the inverse generator
    (renamed alias for ergonomics). *)
Lemma are_conjugate_gen_inv :
  forall {r : nat} (gamma gamma' : RWord r),
    are_conjugate (FreeGroup r) gamma gamma' ->
    are_conjugate (FreeGroup r) (rword_inv gamma) (rword_inv gamma').
Proof. intros r. exact (@are_conjugate_inv_F r). Qed.

(** Conjugacy of negative-power pairs: are_conjugate γ γ' implies
    are_conjugate (γ^{-1})^k (γ'^{-1})^k. Combines inv + pow. *)
Theorem are_conjugate_inv_pow_F :
  forall {r : nat} (g g' : RWord r) (k : nat),
    are_conjugate (FreeGroup r) g g' ->
    are_conjugate (FreeGroup r) (gamma_pow (rword_inv g) k)
                                (gamma_pow (rword_inv g') k).
Proof.
  intros r g g' k Hc.
  apply (are_conjugate_pow_F (rword_inv g) (rword_inv g') k).
  apply are_conjugate_inv_F. exact Hc.
Qed.

(** Symmetric package: conjugacy of γ, γ' gives conjugacy of all
    corresponding power pairs (positive and negative simultaneously). *)
Theorem are_conjugate_cyclic_pair :
  forall {r : nat} (gamma gamma' : RWord r) (k : nat),
    are_conjugate (FreeGroup r) gamma gamma' ->
    are_conjugate (FreeGroup r) (gamma_pow gamma k) (gamma_pow gamma' k) /\
    are_conjugate (FreeGroup r) (gamma_pow (rword_inv gamma) k)
                                (gamma_pow (rword_inv gamma') k).
Proof.
  intros r gamma gamma' k Hc. split.
  - apply are_conjugate_pow_F. exact Hc.
  - apply are_conjugate_inv_pow_F. exact Hc.
Qed.

(** Cross-substitution: if two elements of ⟨γ⟩ are matched by are_conjugate
    γ ~ γ', then for every h ∈ ⟨γ⟩ there is a conjugate h' ∈ ⟨γ'⟩. *)
Theorem in_cyclic_conjugate_pairing :
  forall {r : nat} (gamma gamma' : RWord r),
    are_conjugate (FreeGroup r) gamma gamma' ->
    forall h : RWord r, in_cyclic gamma h ->
    exists h' : RWord r, in_cyclic gamma' h' /\
                         are_conjugate (FreeGroup r) h h'.
Proof.
  intros r gamma gamma' Hc h Hh.
  destruct Hh as [[k Hk] | [k Hk]]; subst h.
  - exists (gamma_pow gamma' k). split.
    + left. exists k. reflexivity.
    + apply are_conjugate_pow_F. exact Hc.
  - exists (gamma_pow (rword_inv gamma') k). split.
    + right. exists k. reflexivity.
    + apply are_conjugate_inv_pow_F. exact Hc.
Qed.

(** Helper: a 2-letter word with both letters of the same polarity (both
    "false" / positive direction) is reduced. *)
Lemma reduced_two_pos_letters :
  forall (n : nat) (i j : Fin.t n),
    reduced [(i, false); (j, false)].
Proof.
  intros n i j. unfold reduced. simpl.
  destruct (letter_eq_dec (j, false) (letter_inv (i, false))) as [Habs|_].
  - exfalso. unfold letter_inv in Habs. cbn in Habs. inversion Habs.
  - reflexivity.
Qed.

(** Distinct generators do not commute in F_n: γ_i · γ_j ≠ γ_j · γ_i
    when i ≠ j. The word γ_i · γ_j has reduced form [(i,false),(j,false)],
    while γ_j · γ_i has reduced form [(j,false),(i,false)] — different
    in the first component since i ≠ j. *)
Lemma free_gens_non_commute :
  forall (n : nat) (i j : Fin.t n),
    i <> j ->
    rword_mul (free_gen_RWord n i) (free_gen_RWord n j) <>
    rword_mul (free_gen_RWord n j) (free_gen_RWord n i).
Proof.
  intros n i j Hij Heq.
  apply (f_equal (@proj1_sig _ _)) in Heq.
  pose proof (reduce_self _ (reduced_two_pos_letters n i j)) as Hr1.
  pose proof (reduce_self _ (reduced_two_pos_letters n j i)) as Hr2.
  unfold rword_mul, free_gen_RWord, free_gen_letter in Heq.
  cbn [proj1_sig List.app] in Heq.
  change (reduce ((i, false) :: (j, false) :: nil))
    with (reduce [(i, false); (j, false)]) in Heq.
  change (reduce ((j, false) :: (i, false) :: nil))
    with (reduce [(j, false); (i, false)]) in Heq.
  rewrite Hr1 in Heq. rewrite Hr2 in Heq.
  inversion Heq as [Hij'].
  apply Hij. exact Hij'.
Qed.

(** Existence form: F_n with n ≥ 2 admits non-commuting elements. *)
Theorem F_n_non_abelian :
  forall (n : nat),
    2 <= n ->
    exists a b : RWord n,
      rword_mul a b <> rword_mul b a.
Proof.
  intros n Hn.
  destruct n as [|[|n']]; try lia.
  exists (free_gen_RWord (S (S n')) Fin.F1).
  exists (free_gen_RWord (S (S n')) (Fin.FS Fin.F1)).
  apply (free_gens_non_commute (S (S n')) Fin.F1 (Fin.FS Fin.F1)).
  intro Hcontra. inversion Hcontra.
Qed.

(** Commutator [γ_i, γ_j] = γ_i · γ_j · γ_i^{-1} · γ_j^{-1} is non-trivial
    in F_n when i ≠ j: equality to e would force γ_i and γ_j to commute,
    contradicting [free_gens_non_commute]. *)
Theorem free_gens_commutator_nontrivial :
  forall (n : nat) (i j : Fin.t n),
    i <> j ->
    rword_mul (rword_mul (rword_mul (free_gen_RWord n i) (free_gen_RWord n j))
                          (rword_inv (free_gen_RWord n i)))
              (rword_inv (free_gen_RWord n j)) <>
    @rword_e n.
Proof.
  intros n i j Hij Hcomm.
  apply (free_gens_non_commute n i j Hij).
  (* From [γ_i, γ_j] = e, derive γ_i · γ_j = γ_j · γ_i. *)
  set (a := free_gen_RWord n i).
  set (b := free_gen_RWord n j).
  fold a in Hcomm. fold b in Hcomm.
  fold a. fold b.
  (* Hcomm: ((a·b)·a^{-1})·b^{-1} = e — multiply right by b. *)
  apply (f_equal (fun x => rword_mul x b)) in Hcomm.
  rewrite rword_id_left in Hcomm.
  rewrite <- (rword_assoc (rword_mul (rword_mul a b) (rword_inv a))
                          (rword_inv b) b) in Hcomm.
  rewrite rword_inv_left in Hcomm.
  rewrite rword_id_right in Hcomm.
  (* Hcomm: (a·b)·a^{-1} = b — multiply right by a. *)
  apply (f_equal (fun x => rword_mul x a)) in Hcomm.
  rewrite <- (rword_assoc (rword_mul a b) (rword_inv a) a) in Hcomm.
  rewrite rword_inv_left in Hcomm.
  rewrite rword_id_right in Hcomm.
  exact Hcomm.
Qed.

(** Distinct generators do not lie in each other's cyclic subgroup:
    γ_j ∉ ⟨γ_i⟩ for i ≠ j. Combines gamma_pow_gen_distinct (positive case)
    with gamma_pow_gen_diff_pos_ne_inv (inverse case). *)
Lemma free_gens_not_in_cyclic :
  forall (n : nat) (i j : Fin.t n),
    i <> j ->
    ~ in_cyclic (free_gen_RWord n i) (free_gen_RWord n j).
Proof.
  intros n i j Hij Hin.
  destruct Hin as [[k Hk] | [k Hk]].
  - destruct k as [|k'].
    + simpl in Hk. apply (free_gen_RWord_ne_e n j). exact Hk.
    + symmetry in Hk.
      rewrite <- (gamma_pow_one_eq (free_gen_RWord n j)) in Hk.
      apply (gamma_pow_gen_distinct n i j (S k') 1
                                    Hij ltac:(lia) ltac:(lia)).
      exact Hk.
  - destruct k as [|k'].
    + simpl in Hk. apply (free_gen_RWord_ne_e n j). exact Hk.
    + symmetry in Hk.
      rewrite <- (gamma_pow_one_eq (free_gen_RWord n j)) in Hk.
      apply (gamma_pow_gen_diff_pos_ne_inv n j i 1 (S k')
                                           ltac:(lia) ltac:(lia)).
      symmetry. exact Hk.
Qed.

(** Conjugation distributes over multiplication when sharing a witness. *)
Theorem are_conjugate_mul_F :
  forall {r : nat} (a b a' b' : RWord r),
    (exists g : RWord r,
       rword_mul (rword_mul g a) (rword_inv g) = a' /\
       rword_mul (rword_mul g b) (rword_inv g) = b') ->
    are_conjugate (FreeGroup r) (rword_mul a b) (rword_mul a' b').
Proof.
  intros r a b a' b' [g [Ha Hb]].
  exists g.
  change (smul (RWord r) (FreeGroup r))
    with (@rword_mul r).
  change (sinv (RWord r) (FreeGroup r))
    with (@rword_inv r).
  rewrite <- rword_conj_distribute.
  rewrite Ha, Hb. reflexivity.
Qed.

(** ⟨γ_i⟩ ∩ ⟨γ_j⟩ = {e} for distinct generators γ_i, γ_j. *)
Theorem in_cyclic_distinct_gen_intersection :
  forall (n : nat) (i j : Fin.t n) (h : RWord n),
    i <> j ->
    in_cyclic (free_gen_RWord n i) h ->
    in_cyclic (free_gen_RWord n j) h ->
    h = @rword_e n.
Proof.
  intros n i j h Hij Hi Hj.
  (* If h = e directly via either side, done. Otherwise derive contradiction. *)
  destruct Hi as [[a Ha] | [a Ha]].
  - destruct a as [|a'].
    + simpl in Ha. exact Ha.
    + (* h = γ_i^(S a') is non-trivial; combine with Hj to contradict. *)
      exfalso. destruct Hj as [[b Hb] | [b Hb]].
      * destruct b as [|b'].
        -- simpl in Hb. apply (gamma_pow_gen_ne_e n i (S a') ltac:(lia)).
           rewrite <- Ha. exact Hb.
        -- apply (gamma_pow_gen_distinct n i j (S a') (S b')
                                          Hij ltac:(lia) ltac:(lia)).
           rewrite <- Ha. exact Hb.
      * destruct b as [|b'].
        -- simpl in Hb. apply (gamma_pow_gen_ne_e n i (S a') ltac:(lia)).
           rewrite <- Ha. exact Hb.
        -- apply (gamma_pow_gen_diff_pos_ne_inv n i j (S a') (S b')
                                                 ltac:(lia) ltac:(lia)).
           rewrite <- Ha. exact Hb.
  - destruct a as [|a'].
    + simpl in Ha. exact Ha.
    + exfalso. destruct Hj as [[b Hb] | [b Hb]].
      * destruct b as [|b'].
        -- simpl in Hb.
           pose proof (rword_length_gamma_pow_gen_inv n i (S a')) as Hl.
           assert (rword_length h = 0).
           { rewrite Hb. unfold rword_length, rword_e. reflexivity. }
           rewrite Ha in H. rewrite Hl in H. lia.
        -- apply (gamma_pow_gen_diff_pos_ne_inv n j i (S b') (S a')
                                                 ltac:(lia) ltac:(lia)).
           rewrite <- Hb. exact Ha.
      * destruct b as [|b'].
        -- simpl in Hb.
           pose proof (rword_length_gamma_pow_gen_inv n i (S a')) as Hl.
           assert (rword_length h = 0).
           { rewrite Hb. unfold rword_length, rword_e. reflexivity. }
           rewrite Ha in H. rewrite Hl in H. lia.
        -- apply (gamma_pow_gen_inv_distinct n i j (S a') (S b')
                                              Hij ltac:(lia) ltac:(lia)).
           rewrite <- Ha. exact Hb.
Qed.

(** Contrapositive: a non-trivial element common to two generator-cyclic
    subgroups forces the generators to coincide. *)
Corollary nontrivial_in_two_gens_implies_eq :
  forall (n : nat) (i j : Fin.t n) (h : RWord n),
    h <> @rword_e n ->
    in_cyclic (free_gen_RWord n i) h ->
    in_cyclic (free_gen_RWord n j) h ->
    i = j.
Proof.
  intros n i j h Hne Hi Hj.
  destruct (Fin.eq_dec i j) as [Hij | Hij].
  - exact Hij.
  - exfalso. apply Hne.
    apply (in_cyclic_distinct_gen_intersection n i j h Hij Hi Hj).
Qed.

(** ⟨γ_0⟩ is a proper subgroup of F_(2+m) for any m: γ_1 ∉ ⟨γ_0⟩. The
    statement uses S(S m) form because Fin.F1 cannot type-check at an
    arbitrary nat. *)
Theorem F_n_cyclic_proper :
  forall (m : nat),
    exists w : RWord (S (S m)),
      ~ in_cyclic (free_gen_RWord (S (S m)) Fin.F1) w.
Proof.
  intros m.
  exists (free_gen_RWord (S (S m)) (Fin.FS Fin.F1)).
  apply (free_gens_not_in_cyclic (S (S m)) Fin.F1 (Fin.FS Fin.F1)).
  intro Hcontra. inversion Hcontra.
Qed.

(** F_n is non-trivial for n ≥ 1: there is a non-identity element. *)
Theorem F_n_nontrivial :
  forall (m : nat),
    exists w : RWord (S m), w <> @rword_e (S m).
Proof.
  intros m.
  exists (free_gen_RWord (S m) Fin.F1).
  apply (free_gen_RWord_ne_e (S m) Fin.F1).
Qed.

(** F_n is infinite for n ≥ 1: distinct exponents of γ_0 give distinct
    elements (γ_0 has infinite order). *)
Theorem F_n_infinite :
  forall (m : nat) (a b : nat),
    a <> b ->
    gamma_pow (free_gen_RWord (S m) Fin.F1) a <>
    gamma_pow (free_gen_RWord (S m) Fin.F1) b.
Proof.
  intros m a b Hab Heq.
  apply Hab.
  apply (gamma_pow_gen_inj (S m) Fin.F1 a b Heq).
Qed.

(** Length of γ_i · γ_j is exactly 2 when i ≠ j: no cancellation occurs. *)
Lemma rword_length_two_distinct_gens :
  forall (n : nat) (i j : Fin.t n),
    i <> j ->
    rword_length (rword_mul (free_gen_RWord n i) (free_gen_RWord n j)) = 2.
Proof.
  intros n i j Hij.
  unfold rword_length, rword_mul, free_gen_RWord, free_gen_letter.
  cbn [proj1_sig List.app].
  pose proof (reduce_self _ (reduced_two_pos_letters n i j)) as Hr.
  unfold Word in Hr.
  change ((i, false) :: (j, false) :: nil)
    with [(i, false); (j, false)].
  rewrite Hr. reflexivity.
Qed.

(** γ_i · γ_j is not in ⟨γ_i⟩ for distinct i, j: the product has
    polarity-distinct letters, while powers of γ_i are all-positive
    repeats and (γ_i^{-1}) powers are all-negative repeats. *)
Lemma free_gens_mul_not_in_cyclic :
  forall (n : nat) (i j : Fin.t n),
    i <> j ->
    ~ in_cyclic (free_gen_RWord n i)
                (rword_mul (free_gen_RWord n i) (free_gen_RWord n j)).
Proof.
  intros n i j Hij Hin.
  pose proof (rword_length_two_distinct_gens n i j Hij) as Hl.
  destruct Hin as [[k Hk] | [k Hk]].
  - rewrite Hk in Hl.
    rewrite (rword_length_gamma_pow_gen n i k) in Hl.
    subst k. (* k = 2 *)
    apply (f_equal (@proj1_sig _ _)) in Hk.
    rewrite (gamma_pow_gen_proj n i 2) in Hk.
    unfold rword_mul, free_gen_RWord, free_gen_letter in Hk.
    cbn [proj1_sig List.app] in Hk.
    pose proof (reduce_self _ (reduced_two_pos_letters n i j)) as Hr.
    unfold Word in Hr.
    change ((i, false) :: (j, false) :: nil)
      with [(i, false); (j, false)] in Hk.
    rewrite Hr in Hk. cbn in Hk. inversion Hk as [Hij']. apply Hij. symmetry. exact Hij'.
  - rewrite Hk in Hl.
    rewrite (rword_length_gamma_pow_gen_inv n i k) in Hl.
    subst k. (* k = 2 *)
    apply (f_equal (@proj1_sig _ _)) in Hk.
    rewrite (gamma_pow_gen_inv_proj n i 2) in Hk.
    unfold rword_mul, free_gen_RWord, free_gen_letter in Hk.
    cbn [proj1_sig List.app] in Hk.
    pose proof (reduce_self _ (reduced_two_pos_letters n i j)) as Hr.
    unfold Word in Hr.
    change ((i, false) :: (j, false) :: nil)
      with [(i, false); (j, false)] in Hk.
    rewrite Hr in Hk. cbn in Hk. inversion Hk.
Qed.

(** F_n contains elements of every word length k for n ≥ 1. *)
Theorem F_n_arbitrary_length :
  forall (m : nat) (k : nat),
    exists w : RWord (S m), rword_length w = k.
Proof.
  intros m k.
  exists (gamma_pow (free_gen_RWord (S m) Fin.F1) k).
  apply rword_length_gamma_pow_gen.
Qed.

(** Corollary: rword_length is unbounded on F_n for n ≥ 1. *)
Corollary F_n_unbounded_length :
  forall (m : nat) (N : nat),
    exists w : RWord (S m), N <= rword_length w.
Proof.
  intros m N.
  destruct (F_n_arbitrary_length m N) as [w Hw].
  exists w. lia.
Qed.

(** Conjugation preserves the identity bidirectionally. Forward
    direction uses [rword_conj_inverse_witness]: substituting e for
    gxg^{-1} reduces to x = h^{-1} · e · h = e. *)
Lemma rword_conj_eq_e_iff :
  forall {n : nat} (g x : RWord n),
    rword_mul (rword_mul g x) (rword_inv g) = @rword_e n <-> x = @rword_e n.
Proof.
  intros n g x. split.
  - intro Hc.
    pose proof (rword_conj_inverse_witness g x) as Hw.
    rewrite Hc in Hw.
    rewrite rword_id_right in Hw.
    rewrite rword_inv_inv in Hw.
    rewrite rword_inv_left in Hw.
    symmetry. exact Hw.
  - intros ->. rewrite rword_id_right. apply rword_inv_right.
Qed.

(** Contrapositive: conjugate is non-identity iff original is. *)
Corollary rword_conj_ne_e_iff :
  forall {n : nat} (g x : RWord n),
    rword_mul (rword_mul g x) (rword_inv g) <> @rword_e n <-> x <> @rword_e n.
Proof.
  intros n g x. split.
  - intros Hne Hcontra. apply Hne.
    apply (proj2 (rword_conj_eq_e_iff g x)). exact Hcontra.
  - intros Hne Hcontra. apply Hne.
    apply (proj1 (rword_conj_eq_e_iff g x)). exact Hcontra.
Qed.

(** General cyclic-rotation conjugacy: a·b and b·a are conjugate in F_n
    for any a, b. Witness: a^{-1}. *)
Theorem rword_mul_conjugate_swap :
  forall {n : nat} (a b : RWord n),
    are_conjugate (FreeGroup n) (rword_mul a b) (rword_mul b a).
Proof.
  intros n a b.
  exists (rword_inv a).
  change (smul (RWord n) (FreeGroup n)) with (@rword_mul n).
  change (sinv (RWord n) (FreeGroup n)) with (@rword_inv n).
  rewrite rword_inv_inv.
  rewrite (rword_assoc (rword_inv a) a b).
  rewrite rword_inv_left.
  rewrite rword_id_left.
  reflexivity.
Qed.

(** γ_i · γ_j and γ_j · γ_i are conjugate in F_n: cyclic rotation by γ_i^{-1}.
    Concretely: γ_i^{-1} · (γ_i · γ_j) · γ_i = γ_j · γ_i. *)
Lemma free_gens_mul_conjugate_swap :
  forall (n : nat) (i j : Fin.t n),
    are_conjugate (FreeGroup n)
      (rword_mul (free_gen_RWord n i) (free_gen_RWord n j))
      (rword_mul (free_gen_RWord n j) (free_gen_RWord n i)).
Proof.
  intros n i j.
  exists (rword_inv (free_gen_RWord n i)).
  change (smul (RWord n) (FreeGroup n)) with (@rword_mul n).
  change (sinv (RWord n) (FreeGroup n)) with (@rword_inv n).
  rewrite rword_inv_inv.
  (* Goal: (γ_i^{-1} · (γ_i · γ_j)) · γ_i = γ_j · γ_i *)
  rewrite (rword_assoc (rword_inv (free_gen_RWord n i))
                       (free_gen_RWord n i) (free_gen_RWord n j)).
  rewrite rword_inv_left.
  rewrite rword_id_left.
  reflexivity.
Qed.

(** Distinct two-generator product is non-trivial. *)
Lemma free_gens_mul_distinct_ne_e :
  forall (n : nat) (i j : Fin.t n),
    i <> j ->
    rword_mul (free_gen_RWord n i) (free_gen_RWord n j) <> @rword_e n.
Proof.
  intros n i j Hij Hcontra.
  pose proof (rword_length_two_distinct_gens n i j Hij) as Hl.
  rewrite Hcontra in Hl.
  unfold rword_length, rword_e in Hl. simpl in Hl. lia.
Qed.

(** Decomposition: γ_i · γ_j (i ≠ j) is neither a positive nor a
    negative power of γ_i. Direct corollary of [free_gens_mul_not_in_cyclic]
    by case-splitting in_cyclic. *)
Corollary free_gens_mul_not_pow_pair :
  forall (n : nat) (i j : Fin.t n),
    i <> j ->
    (forall k : nat,
        rword_mul (free_gen_RWord n i) (free_gen_RWord n j) <>
        gamma_pow (free_gen_RWord n i) k) /\
    (forall k : nat,
        rword_mul (free_gen_RWord n i) (free_gen_RWord n j) <>
        gamma_pow (rword_inv (free_gen_RWord n i)) k).
Proof.
  intros n i j Hij. split.
  - intros k Heq.
    apply (free_gens_mul_not_in_cyclic n i j Hij).
    left. exists k. exact Heq.
  - intros k Heq.
    apply (free_gens_mul_not_in_cyclic n i j Hij).
    right. exists k. exact Heq.
Qed.

Conjecture hall_M_strong_free_factor :
  forall (r : nat) (gamma : RWord r),
    r >= 2 ->
    gamma <> @rword_e r ->
    exists (FIS : FiniteIndexSubgroup (FreeGroup r)),
      fis_index FIS >= 2 /\
      fis_pred FIS gamma /\
      fis_pred FIS (@rword_e r).

(** The free factor theorem in the decomposition form:
    for any γ ≠ e there is Δ ≤ F_r such that F_r = ⟨γ⟩ * Δ. *)

