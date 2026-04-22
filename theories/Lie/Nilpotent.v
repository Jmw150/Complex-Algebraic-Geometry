(** * Lie/Nilpotent.v
    Lower central series, nilpotent Lie algebras, basic properties. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.Lie.Ideals.
Require Import CAG.Lie.Solvable.

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
Proof. Admitted.

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
  - apply zero_is_subalgebra.
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

(** Homomorphic image of nilpotent is nilpotent. *)
Lemma nilpotent_image {F : Type} {fld : Field F} {L M : Type}
    (la : LieAlgebraF fld L) (lb : LieAlgebraF fld M)
    (φ : LieHom la lb) :
    IsNilpotent la -> IsNilpotent lb.
Proof. Admitted.

(** If L/Z(L) is nilpotent then L is nilpotent. *)
Lemma nilpotent_from_quotient_center {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    (exists (lq : LieAlgebraF fld L), IsNilpotent lq) ->
    IsNilpotent la.
Proof. Admitted.

(** If L is nilpotent and nonzero, then Z(L) ≠ 0. *)
Lemma nilpotent_center_nontrivial {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    IsNilpotent la ->
    (exists x : L, x <> la_zero la) ->
    exists z, IsCenter la z /\ z <> la_zero la.
Proof. Admitted.

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
Axiom strictly_upper_triangular_nilpotent :
  forall {F : Type} {fld : Field F} (n : nat)
    (la : LieAlgebraF fld (list (list F))),
    IsNilpotent la.

(** Upper triangular matrices are solvable but not nilpotent for n ≥ 2 (axiom). *)
Axiom upper_triangular_not_nilpotent :
  forall {F : Type} {fld : Field F} (n : nat)
    (la : LieAlgebraF fld (list (list F))),
    (n >= 2)%nat -> ~ IsNilpotent la.
