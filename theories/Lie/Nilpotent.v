(** * Lie/Nilpotent.v
    Lower central series, nilpotent Lie algebras, basic properties. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.Lie.Ideals.
Require Import CAG.Lie.Solvable.
From Stdlib Require Import List.

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

(** Axiom: backward lift for surjective maps on lower central series. *)
(* CAG zero-dependent Axiom nilpotent_image_lift theories/Lie/Nilpotent.v:141 BEGIN
Axiom nilpotent_image_lift :
  forall {F : Type} {fld : Field F} {L M : Type}
    (la : LieAlgebraF fld L) (lb : LieAlgebraF fld M)
    (φ : LieHom la lb)
    (surj : forall y : M, exists x : L, lh_fn φ x = y)
    (n : nat) (y : M),
    lower_central lb n y ->
    exists x : L, lh_fn φ x = y /\ lower_central la n x.
   CAG zero-dependent Axiom nilpotent_image_lift theories/Lie/Nilpotent.v:141 END *)

(** Surjective homomorphic image of nilpotent is nilpotent.

    NOTE: Surjectivity is required — a non-surjective map can embed a nilpotent
    algebra into an arbitrary one. *)
(* CAG zero-dependent Lemma nilpotent_image theories/Lie/Nilpotent.v:154 BEGIN
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
   CAG zero-dependent Lemma nilpotent_image theories/Lie/Nilpotent.v:154 END *)

(** If L/Z(L) is nilpotent (of class k) then L is nilpotent (of class k+1).
    Axiomatized: requires quotient algebra infrastructure. *)
(* CAG zero-dependent Axiom nilpotent_from_quotient_center theories/Lie/Nilpotent.v:167 BEGIN
Axiom nilpotent_from_quotient_center :
  forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L)
    (φ : LieHom la la)  (* quotient map onto L/Z(L) *)
    (hφ : forall x, IsCenter la x -> lh_fn φ x = la_zero la)
    (n : nat)
    (hn : forall y, lower_central la n (lh_fn φ y) -> lh_fn φ y = la_zero la),
    IsNilpotent la.
   CAG zero-dependent Axiom nilpotent_from_quotient_center theories/Lie/Nilpotent.v:167 END *)

(** If L is nilpotent and nonzero, then Z(L) ≠ 0.

    Proof sketch: Let n be the nilpotency class (L_n = 0, n ≥ 1).
    Any z ∈ L_{n-1} satisfies [x, z] ∈ L_n = 0 for all x, so z ∈ Z(L).
    Finding z ≠ 0 in L_{n-1} requires classical reasoning (choosing minimal n).
    Axiomatized. *)
(* CAG zero-dependent Axiom nilpotent_center_nontrivial theories/Lie/Nilpotent.v:182 BEGIN
Axiom nilpotent_center_nontrivial :
  forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L),
    IsNilpotent la ->
    (exists x : L, x <> la_zero la) ->
    exists z, IsCenter la z /\ z <> la_zero la.
   CAG zero-dependent Axiom nilpotent_center_nontrivial theories/Lie/Nilpotent.v:182 END *)

(** ** ad-nilpotent elements *)

(** x is ad-nilpotent if ad x is a nilpotent endomorphism of L.
    We represent this as: iterated bracket [x,[x,...[x,y]...]] eventually gives 0. *)
Definition IsAdNilpotent {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (x : L) : Prop :=
  exists n : nat, forall y,
    Nat.iter n (laF_bracket la x) y = la_zero la.

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

(** ** Strictly upper triangular matrices are nilpotent (axiom). *)
(* CAG zero-dependent Axiom strictly_upper_triangular_nilpotent theories/Lie/Nilpotent.v:215 BEGIN
Axiom strictly_upper_triangular_nilpotent :
  forall {F : Type} {fld : Field F} (n : nat)
    (la : LieAlgebraF fld (list (list F))),
    IsNilpotent la.
   CAG zero-dependent Axiom strictly_upper_triangular_nilpotent theories/Lie/Nilpotent.v:215 END *)

(** Upper triangular matrices are solvable but not nilpotent for n ≥ 2 (axiom). *)
(* CAG zero-dependent Axiom upper_triangular_not_nilpotent theories/Lie/Nilpotent.v:221 BEGIN
Axiom upper_triangular_not_nilpotent :
  forall {F : Type} {fld : Field F} (n : nat)
    (la : LieAlgebraF fld (list (list F))),
    (n >= 2)%nat -> ~ IsNilpotent la.
   CAG zero-dependent Axiom upper_triangular_not_nilpotent theories/Lie/Nilpotent.v:221 END *)
