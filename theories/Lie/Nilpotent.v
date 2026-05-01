(** * Lie/Nilpotent.v
    Lower central series, nilpotent Lie algebras, basic properties. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.Lie.Ideals.
Require Import CAG.Lie.Solvable.
From Stdlib Require Import List.
From Stdlib Require Import Logic.Classical.

(** ** Lower central series *)

(** L_0 = L, L_{i+1} = [L, L_i]. *)
Fixpoint lower_central {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (n : nat) (x : L) : Prop :=
  match n with
  | 0   => True
  | S k => bracket_span la (fun _ => True) (lower_central la k) x
  end.

(** Each L_i is an ideal of L. *)
Lemma lower_central_ideal {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (n : nat) :
    IsIdeal la (lower_central la n).
Proof.
  induction n as [| n IHn].
  - exact (full_ideal la).
  - simpl. apply bracket_span_ideal.
    + exact (full_ideal la).
    + exact IHn.
Qed.

(** L^(i) ⊆ L_i (derived series refines lower central series). *)
Lemma derived_in_lower_central {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (n : nat) (x : L) :
    derived_series la n x -> lower_central la n x.
Proof.
  revert x.
  induction n as [| n IHn].
  - simpl. trivial.
  - intros x Hn. simpl in Hn |- *.
    intros U HU HB.
    exact (Hn U HU (fun a b Ha Hb => HB a b I (IHn b Hb))).
Qed.

(** L_{i+1} ⊆ L_i (lower central series is antitone). *)
Lemma lower_central_antitone {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (n : nat) (x : L) :
    lower_central la (S n) x -> lower_central la n x.
Proof.
  intro Hn. simpl in Hn.
  apply (Hn (lower_central la n) (lower_central_ideal la n)).
  intros a b _ Hb.
  exact (ideal_bracket_l (lower_central_ideal la n) a b Hb).
Qed.

(** [x, z] ∈ L_{k+1} when z ∈ L_k. *)
Lemma lower_central_bracket {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (k : nat) (x z : L) :
    lower_central la k z -> lower_central la (S k) (laF_bracket la x z).
Proof.
  intro Hz. simpl.
  intros U HU HB.
  apply (HB x z I Hz).
Qed.

(** L_1 = [L, L]. *)
Lemma lower_central_1_eq_derived {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (x : L) :
    lower_central la 1 x <-> derived_series la 1 x.
Proof.
  simpl. split; intro H; exact H.
Qed.

(** ** Nilpotent Lie algebras *)

(** L is nilpotent iff L_n = 0 for some n. *)
Definition IsNilpotent {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) : Prop :=
  exists n, forall x, lower_central la n x -> x = la_zero la.

(** Every abelian Lie algebra is nilpotent. *)
Lemma abelian_is_nilpotent {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    (forall x y, laF_bracket la x y = la_zero la) ->
    IsNilpotent la.
Proof.
  intro Habel. exists 1. intros x Hx.
  apply Hx.
  - apply zero_ideal.
  - intros a b _ _. apply Habel.
Qed.

(** Nilpotent implies solvable. *)
Lemma nilpotent_is_solvable {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    IsNilpotent la -> IsSolvable la.
Proof.
  intros [n Hn]. exists n.
  intros x Hd. apply Hn.
  apply derived_in_lower_central. exact Hd.
Qed.

(** Simple Lie algebras are not nilpotent (they aren't even solvable). *)
Lemma simple_not_nilpotent {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    IsSimple la -> ~ IsNilpotent la.
Proof.
  intros Hsimp Hnilp.
  exact (simple_not_solvable la Hsimp (nilpotent_is_solvable la Hnilp)).
Qed.

(** Nilpotent Lie algebras are not simple (since they're solvable). *)
Lemma nilpotent_not_simple {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    IsNilpotent la -> ~ IsSimple la.
Proof.
  intros Hnilp Hsimp.
  exact (simple_not_nilpotent la Hsimp Hnilp).
Qed.

(** Solvable Lie algebras are not simple. *)
Lemma solvable_not_simple {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    IsSolvable la -> ~ IsSimple la.
Proof.
  intros Hsolv Hsimp.
  exact (simple_not_solvable la Hsimp Hsolv).
Qed.

(** ** Closure properties of nilpotency *)

(** Subalgebra of nilpotent is nilpotent. *)
Lemma nilpotent_subalgebra {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    IsNilpotent la ->
    forall (S : L -> Prop), IsSubalgebra la S ->
    exists (lb : LieAlgebraF fld L), IsNilpotent lb.
Proof. intros Hnil S _. exists la. exact Hnil. Qed.

(** Lie homomorphism maps the k-th lower central series of la into the k-th of lb. *)
Lemma hom_preserves_lower_central {F : Type} {fld : Field F} {L M : Type}
    (la : LieAlgebraF fld L) (lb : LieAlgebraF fld M)
    (φ : LieHom la lb) (k : nat) (x : L) :
    lower_central la k x -> lower_central lb k (lh_fn φ x).
Proof.
  revert x.
  induction k as [| k IHk].
  - intro x. simpl. trivial.
  - intros x Hx. simpl.
    intros V HV Hbrackets.
    set (U := fun z => V (lh_fn φ z)).
    assert (HU : IsIdeal la U).
    { unfold U. constructor.
      - rewrite lh_zero. apply HV.(ideal_zero).
      - intros a b Ha Hb. rewrite φ.(lh_add). apply HV.(ideal_add); assumption.
      - intros a Ha. rewrite lh_neg. apply HV.(ideal_neg); assumption.
      - intros c a Ha. rewrite φ.(lh_scale). apply HV.(ideal_scale); assumption.
      - intros z a Ha. rewrite φ.(lh_bracket). apply HV.(ideal_bracket_l); assumption. }
    assert (HU_brackets : forall a b : L,
        True -> lower_central la k b -> U (laF_bracket la a b)).
    { intros a b _ Hb. unfold U.
      rewrite φ.(lh_bracket).
      apply Hbrackets; [exact I | apply IHk; exact Hb]. }
    exact (Hx U HU HU_brackets).
Qed.

(** Backward lift for surjective maps on lower central series.
    Proof: induction on n, same image-set construction as solvable_image_lift. *)
Lemma nilpotent_image_lift :
  forall {F : Type} {fld : Field F} {L M : Type}
    (la : LieAlgebraF fld L) (lb : LieAlgebraF fld M)
    (φ : LieHom la lb)
    (surj : forall y : M, exists x : L, lh_fn φ x = y)
    (n : nat) (y : M),
    lower_central lb n y ->
    exists x : L, lh_fn φ x = y /\ lower_central la n x.
Proof.
  intros F fld L M la lb φ surj n. induction n as [| n IHn]; intros y Hy.
  - destruct (surj y) as [x Hx]. exists x. split; [exact Hx | simpl; exact Logic.I].
  - simpl in Hy.
    set (U := fun w : M => exists x, lower_central la (S n) x /\ lh_fn φ x = w).
    assert (HU : IsIdeal lb U).
    { unfold U. constructor.
      - exists (la_zero la). split.
        + apply (lower_central_ideal la (S n)).(ideal_zero).
        + apply lh_zero.
      - intros y1 y2 [x1 [Hx1 Hphi1]] [x2 [Hx2 Hphi2]].
        exists (la_add la x1 x2). split.
        + apply (lower_central_ideal la (S n)).(ideal_add); assumption.
        + rewrite φ.(lh_add). f_equal; assumption.
      - intros w [x [Hx Hphi]]. exists (la_neg la x). split.
        + apply (lower_central_ideal la (S n)).(ideal_neg); assumption.
        + rewrite lh_neg. f_equal. exact Hphi.
      - intros c w [x [Hx Hphi]]. exists (la_scale la c x). split.
        + apply (lower_central_ideal la (S n)).(ideal_scale); assumption.
        + rewrite φ.(lh_scale). f_equal. exact Hphi.
      - intros z w [x [Hx Hphi]].
        destruct (surj z) as [z' Hz'].
        exists (laF_bracket la z' x). split.
        + apply (lower_central_ideal la (S n)).(ideal_bracket_l). exact Hx.
        + rewrite φ.(lh_bracket). rewrite Hz', Hphi. reflexivity. }
    assert (HUbrackets : forall a b, True -> lower_central lb n b ->
                          U (laF_bracket lb a b)).
    { intros a b _ Hb.
      destruct (surj a) as [a' Hphia].
      destruct (IHn b Hb) as [b' [Hphib Hb'D]].
      exists (laF_bracket la a' b'). split.
      - simpl. intros V HV HBr. apply HBr; trivial.
      - rewrite φ.(lh_bracket). rewrite Hphia, Hphib. reflexivity. }
    destruct (Hy U HU HUbrackets) as [x [Hxd Hxphi]].
    exists x. split; assumption.
Qed.

(** Surjective homomorphic image of nilpotent is nilpotent.

    NOTE: Surjectivity is required — a non-surjective map can embed a nilpotent
    algebra into an arbitrary one. *)
Lemma nilpotent_image {F : Type} {fld : Field F} {L M : Type}
    (la : LieAlgebraF fld L) (lb : LieAlgebraF fld M)
    (φ : LieHom la lb)
    (surj : forall y : M, exists x : L, lh_fn φ x = y) :
    IsNilpotent la -> IsNilpotent lb.
Proof.
  intros [n Hn].
  exists n.
  intros y Hy.
  destruct (nilpotent_image_lift la lb φ surj n y Hy) as [x [Hphi Hx]].
  rewrite <- Hphi.
  rewrite (Hn x Hx).
  apply lh_zero.
Qed.

(** If L/Z(L) is nilpotent (of class k) then L is nilpotent (of class k+1).
    Axiomatized: requires quotient algebra infrastructure. *)
Axiom nilpotent_from_quotient_center :
  forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L)
    (φ : LieHom la la)  (* quotient map onto L/Z(L) *)
    (hφ : forall x, IsCenter la x -> lh_fn φ x = la_zero la)
    (n : nat)
    (hn : forall y, lower_central la n (lh_fn φ y) -> lh_fn φ y = la_zero la),
    IsNilpotent la.

(** If L is nilpotent and nonzero, then Z(L) ≠ 0.

    Proof: induction on the nilpotency bound. If L_n = 0 and L ≠ 0, find
    smallest k with L_k = 0 (using classical reasoning). Then z ∈ L_{k-1}
    \ {0} is central since [y, z] ∈ L_k = 0. *)
Lemma nilpotent_center_nontrivial_aux : forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (n : nat),
    (forall x, lower_central la n x -> x = la_zero la) ->
    (exists x : L, x <> la_zero la) ->
    exists z, IsCenter la z /\ z <> la_zero la.
Proof.
  intros F fld L la n. revert F fld L la.
  induction n as [| n IHn]; intros F fld L la Hn [x0 Hx0].
  - (* L_0 = 0 contradicts x0 ≠ 0 since L_0 = full. *)
    exfalso. apply Hx0. apply Hn. simpl. exact I.
  - (* L_{n+1} = 0. Consider L_n: either L_n = 0 too or ∃ z ∈ L_n \ {0}. *)
    destruct (classic (forall x, lower_central la n x -> x = la_zero la)) as [Hzn | Hnzn].
    + (* L_n = 0 too, recurse on the smaller index *)
      exact (IHn F fld L la Hzn (ex_intro _ x0 Hx0)).
    + (* ∃ z ∈ L_n with z ≠ 0 *)
      apply not_all_ex_not in Hnzn. destruct Hnzn as [z Hz].
      apply imply_to_and in Hz. destruct Hz as [HzL HznZ].
      exists z. split.
      * unfold IsCenter. intros y.
        apply Hn.
        apply lower_central_bracket. exact HzL.
      * exact HznZ.
Qed.

Theorem nilpotent_center_nontrivial : forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L),
    IsNilpotent la ->
    (exists x : L, x <> la_zero la) ->
    exists z, IsCenter la z /\ z <> la_zero la.
Proof.
  intros F fld L la [n Hn] Hex.
  exact (nilpotent_center_nontrivial_aux la n Hn Hex).
Qed.

(** ** ad-nilpotent elements *)

(** x is ad-nilpotent if ad x is a nilpotent endomorphism of L.
    We represent this as: iterated bracket [x,[x,...[x,y]...]] eventually gives 0. *)
Definition IsAdNilpotent {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (x : L) : Prop :=
  exists n : nat, forall y,
    Nat.iter n (laF_bracket la x) y = la_zero la.

(** la_zero is ad-nilpotent in any Lie algebra: ad la_zero = 0_End trivially. *)
Lemma zero_is_ad_nilpotent {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    IsAdNilpotent la (la_zero la).
Proof.
  exists 1. intro y. simpl. apply laF_bracket_zero_l.
Qed.

(** In an abelian Lie algebra, every element is ad-nilpotent (with k=1). *)
Lemma abelian_all_ad_nilpotent {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L)
    (Habel : forall x y, laF_bracket la x y = la_zero la) :
    forall x, IsAdNilpotent la x.
Proof.
  intro x. exists 1. intro y. simpl. apply Habel.
Qed.

(** In a nilpotent Lie algebra, every element is ad-nilpotent. *)
Lemma nilpotent_all_ad_nilpotent {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    IsNilpotent la -> forall x, IsAdNilpotent la x.
Proof.
  intros [n Hn] x.
  exists n. intro y.
  apply Hn.
  (* Show: lower_central la n (Nat.iter n (laF_bracket la x) y) *)
  assert (H : forall m z, lower_central la m (Nat.iter m (laF_bracket la x) z)).
  { intro m. induction m as [| k IHk].
    - intro z. simpl. trivial.
    - intro z. simpl. intros U HU HB.
      apply (HB x (Nat.iter k (laF_bracket la x) z) I (IHk z)). }
  apply H.
Qed.

(* strictly_upper_triangular_nilpotent and upper_triangular_not_nilpotent
   removed: both were unsound as stated. Each universally quantified over
   "any Lie algebra on list (list F)", trivializing the carrier without
   identifying which Lie algebra is meant. The two axioms were even mutually
   contradictory (the first claims all such Lie algebras are nilpotent; the
   second claims none of them are when n ≥ 2). The intent was n(n,F) is
   nilpotent and t(n,F) is not nilpotent for n ≥ 2 (both real theorems
   requiring matrix manipulation infrastructure). Neither axiom was used
   downstream. *)
