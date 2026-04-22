(** * Lie/Engel.v
    Engel's theorem: every ad-nilpotent Lie algebra is nilpotent.
    Also: linear Engel theorem, flag corollary, consequences. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.Lie.Ideals.
Require Import CAG.Lie.Solvable.
Require Import CAG.Lie.Nilpotent.

(** ** Linear Engel theorem *)

(** Stated for a Lie algebra L ⊆ gl(V) of nilpotent endomorphisms.
    We axiomatize since the proof requires linear algebra infrastructure. *)

(** If every element of a subalgebra L ⊆ gl(V) acts nilpotently on V ≠ 0,
    there exists a nonzero v ∈ V killed by all of L. *)
Axiom engel_linear :
  forall {F : Type} {fld : Field F} {L V : Type}
    (la : LieAlgebraF fld L)
    (act : L -> V -> V)   (* the action of L on V *)
    (hnil : forall x, IsAdNilpotent la x)
    (hV : exists v : V, v <> (act (la_zero la) v)),
  exists v : V, forall x, act x v = act (la_zero la) v.

(** ** Engel's theorem *)

(** If every element of L is ad-nilpotent, then L is nilpotent. *)
Theorem engel_theorem {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    (forall x, IsAdNilpotent la x) ->
    IsNilpotent la.
Proof. Admitted.

(** ** Flag corollary *)

(** A complete flag in a vector space V is a chain
    0 = V_0 ⊂ V_1 ⊂ ... ⊂ V_n = V with dim(V_i) = i. *)
(** We axiomatize the corollary. *)

Axiom engel_flag :
  forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L)
    (hnil : forall x, IsAdNilpotent la x),
  (** There exists a basis relative to which all elements are strictly
      upper triangular. *)
  True.

(** ** Key consequences for nilpotent Lie algebras *)

(** If L is nilpotent and I ◁ L with I ≠ 0, then I ∩ Z(L) ≠ 0. *)
Lemma nilpotent_ideal_meets_center {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (I : L -> Prop) :
    IsNilpotent la ->
    IsIdeal la I ->
    (exists x, I x /\ x <> la_zero la) ->
    exists z, I z /\ IsCenter la z /\ z <> la_zero la.
Proof. Admitted.

(** If L is nilpotent and K < L properly, then K < N_L(K). *)
Lemma nilpotent_normalizer_grows {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (K : L -> Prop) :
    IsNilpotent la ->
    IsSubalgebra la K ->
    (exists x, ~ K x) ->
    exists x, IsNormalizer la K x /\ ~ K x.
Proof. Admitted.

(** Every nonzero nilpotent Lie algebra has an ideal of codimension 1.
    (Stated as existence of a maximal proper sub-ideal.) *)
Lemma nilpotent_codim1_ideal {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    IsNilpotent la ->
    (exists x : L, x <> la_zero la) ->
    exists (I : L -> Prop), IsIdeal la I /\
      (exists x, ~ I x) /\
      (forall J, IsIdeal la J -> (forall y, I y -> J y) -> (exists x, ~ J x) -> False).
Proof. Admitted.

(** ** Exercises *)

(** Exercise: if I ◁ L, then members of derived/lower central series of I
    are ideals of L. *)
Lemma series_of_ideal_are_ideals {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (I : L -> Prop) (n : nat) :
    IsIdeal la I ->
    IsIdeal la (fun x => I x /\ derived_series la n x).
Proof.
  intro hI.
  exact (inter_ideal la I (derived_series la n) hI (derived_series_ideal la n)).
Qed.

(** Exercise: L solvable iff ad(L) solvable; L nilpotent iff ad(L) nilpotent. *)
Axiom lie_solvable_iff_ad_solvable :
  forall {F : Type} {fld : Field F} {L : Type} (la : LieAlgebraF fld L),
    IsSolvable la <-> True. (* placeholder *)

Axiom lie_nilpotent_iff_ad_nilpotent_alg :
  forall {F : Type} {fld : Field F} {L : Type} (la : LieAlgebraF fld L),
    IsNilpotent la <-> (forall x, IsAdNilpotent la x).
