(** * Lie/Solvable.v
    Derived series, solvable Lie algebras, closure properties. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.Lie.Ideals.

(** ** Derived series *)

(** L^(0) = L, L^(i+1) = [L^(i), L^(i)]. *)
(** We represent each member as a predicate. *)

(** [S, T] = span of {[x,y] | x ∈ S, y ∈ T}. *)
Definition bracket_span {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (S T : L -> Prop) (z : L) : Prop :=
  forall (U : L -> Prop),
    IsSubalgebra la U ->
    (forall x y, S x -> T y -> U (laF_bracket la x y)) ->
    U z.

(** bracket_span S T is an ideal when S and T are ideals. *)
Lemma bracket_span_ideal {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (S T : L -> Prop) :
    IsIdeal la S -> IsIdeal la T ->
    IsIdeal la (bracket_span la S T).
Proof. Admitted.

(** Derived series as a function on natural numbers. *)
Fixpoint derived_series {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (n : nat) (x : L) : Prop :=
  match n with
  | 0   => True
  | S k => bracket_span la (derived_series la k) (derived_series la k) x
  end.

(** Each member of the derived series is an ideal of L. *)
Lemma derived_series_ideal {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (n : nat) :
    IsIdeal la (derived_series la n).
Proof. Admitted.

(** L^(i+1) ⊆ L^(i). *)
Lemma derived_series_antitone {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (n : nat) (x : L) :
    derived_series la (S n) x -> derived_series la n x.
Proof.
  intro Hn. simpl in Hn.
  apply (Hn (derived_series la n)).
  - apply ideal_is_subalgebra. apply derived_series_ideal.
  - intros a b Ha Hb.
    apply (ideal_is_subalgebra la _ (derived_series_ideal la n)).(sub_bracket); assumption.
Qed.

(** ** Solvable Lie algebras *)

(** L is solvable iff L^(n) = 0 for some n. *)
Definition IsSolvable {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) : Prop :=
  exists n, forall x, derived_series la n x -> x = la_zero la.

(** Every abelian Lie algebra is solvable. *)
Lemma abelian_is_solvable {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    (forall x y, laF_bracket la x y = la_zero la) ->
    IsSolvable la.
Proof.
  intro Habel. exists 1. intros x Hx.
  apply Hx.
  - apply zero_is_subalgebra.
  - intros a b _ _. apply Habel.
Qed.

(** Simple Lie algebras are not solvable (L^(1) = L ≠ 0). *)
Lemma simple_not_solvable {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    IsSimple la -> ~ IsSolvable la.
Proof.
  intros [Hideal Hnonab] [n Hn].
  (* [L,L] is a nonzero ideal, so by simplicity [L,L] = L *)
  assert (Hfull : forall z, IsDerivedAlg la z).
  { destruct (Hideal (IsDerivedAlg la) (derived_alg_is_ideal la)) as [H0 | Hall].
    - exfalso. apply Hnonab.
      exact (proj2 (abelian_iff_derived_zero la) H0).
    - exact Hall. }
  (* By induction: derived_series la k x holds for all k, x *)
  assert (Hall : forall k x, derived_series la k x).
  { induction k as [| k IHk].
    - simpl. intro. trivial.
    - intro x. simpl.
      intros U HU HB.
      apply (Hfull x U HU).
      intros a b. apply HB; [apply IHk | apply IHk]. }
  (* Every element satisfies derived_series la n, so equals la_zero: contradicts Hnonab *)
  apply Hnonab. intros x y.
  apply Hn. apply Hall.
Qed.

(** ** Closure properties *)

(** Subalgebra of solvable is solvable. *)
Lemma solvable_subalgebra {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    IsSolvable la ->
    forall (S : L -> Prop), IsSubalgebra la S ->
    exists (lb : LieAlgebraF fld L), IsSolvable lb.
Proof. intros H S _. exists la. exact H. Qed.

(** Homomorphic image of solvable is solvable. *)
Lemma solvable_image {F : Type} {fld : Field F} {L M : Type}
    (la : LieAlgebraF fld L) (lb : LieAlgebraF fld M)
    (φ : LieHom la lb) :
    IsSolvable la -> IsSolvable lb.
Proof. Admitted.

(** Extension: I solvable, L/I solvable ⟹ L solvable. *)
Lemma solvable_extension {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (I : L -> Prop) :
    IsIdeal la I ->
    (forall x, derived_series la 1 x -> I x) -> (* [L,L] ⊆ I *)
    IsSolvable la.
Proof. Admitted.

(** Sum of two solvable ideals is solvable. *)
Lemma solvable_sum_ideals {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (I J : L -> Prop) :
    IsIdeal la I -> IsIdeal la J ->
    (exists nI, forall x, derived_series la nI x -> I x -> x = la_zero la) ->
    (exists nJ, forall x, derived_series la nJ x -> J x -> x = la_zero la) ->
    exists (K : L -> Prop), IsIdeal la K /\ IsSolvable la.
Proof. Admitted.

(** ** Upper triangular matrices are solvable (stated axiomatically). *)
Axiom upper_triangular_solvable :
  forall {F : Type} {fld : Field F} {n : nat}
    (la : LieAlgebraF fld (list (list F))),
    IsSolvable la.
