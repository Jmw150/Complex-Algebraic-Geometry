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
(* CAG zero-dependent Axiom engel_linear theories/Lie/Engel.v:16 BEGIN
Axiom engel_linear :
  forall {F : Type} {fld : Field F} {L V : Type}
    (la : LieAlgebraF fld L)
    (act : L -> V -> V)   (* the action of L on V *)
    (hnil : forall x, IsAdNilpotent la x)
    (hV : exists v : V, v <> (act (la_zero la) v)),
  exists v : V, forall x, act x v = act (la_zero la) v.
   CAG zero-dependent Axiom engel_linear theories/Lie/Engel.v:16 END *)

(** ** Engel's theorem *)

(** If every element of L is ad-nilpotent, then L is nilpotent. *)
(* CAG zero-dependent Admitted engel_theorem theories/Lie/Engel.v:31 BEGIN
Theorem engel_theorem {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    (forall x, IsAdNilpotent la x) ->
    IsNilpotent la.
Proof. Admitted.
   CAG zero-dependent Admitted engel_theorem theories/Lie/Engel.v:31 END *)

(** ** Flag corollary *)

(** A complete flag in a vector space V is a chain
    0 = V_0 ⊂ V_1 ⊂ ... ⊂ V_n = V with dim(V_i) = i. *)
(** We axiomatize the corollary. *)

(** Flag corollary of Engel's theorem: every Lie algebra of nilpotent
    endomorphisms of V admits a complete flag of invariant subspaces.
    Equivalently: there is a basis relative to which all elements act as
    strictly upper triangular matrices.

    Stated as a Conjecture pending action/representation infrastructure
    for `LieAlgebraF` (we currently lack a `Subspace` and `flag` predicate).
    Reference: Humphreys §3.3 Corollary B. *)
(* CAG zero-dependent Conjecture engel_flag theories/Lie/Engel.v:53 BEGIN
Conjecture engel_flag :
  forall {F : Type} {fld : Field F} {L V : Type}
    (la : LieAlgebraF fld L)
    (act : L -> V -> V)
    (hnil : forall x, IsAdNilpotent la x),
    (* There is a chain V_0 ⊂ V_1 ⊂ ... ⊂ V_n = V of L-stable subspaces
       with each quotient one-dimensional. We approximate "L-stable" by
       requiring act to fix a flag of subsets. *)
    exists (chain : nat -> V -> Prop) (n : nat),
      chain 0 = (fun _ => False) /\
      (forall v, chain n v) /\
      (forall i v x, chain i v -> chain (S i) (act x v)).
   CAG zero-dependent Conjecture engel_flag theories/Lie/Engel.v:53 END *)

(** ** Key consequences for nilpotent Lie algebras *)

(** If L is nilpotent and I ◁ L with I ≠ 0, then I ∩ Z(L) ≠ 0. *)
(* CAG zero-dependent Admitted nilpotent_ideal_meets_center theories/Lie/Engel.v:67 BEGIN
Lemma nilpotent_ideal_meets_center {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (I : L -> Prop) :
    IsNilpotent la ->
    IsIdeal la I ->
    (exists x, I x /\ x <> la_zero la) ->
    exists z, I z /\ IsCenter la z /\ z <> la_zero la.
Proof. Admitted.
   CAG zero-dependent Admitted nilpotent_ideal_meets_center theories/Lie/Engel.v:67 END *)

(** If L is nilpotent and K < L properly, then K < N_L(K). *)
(* CAG zero-dependent Admitted nilpotent_normalizer_grows theories/Lie/Engel.v:76 BEGIN
Lemma nilpotent_normalizer_grows {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (K : L -> Prop) :
    IsNilpotent la ->
    IsSubalgebra la K ->
    (exists x, ~ K x) ->
    exists x, IsNormalizer la K x /\ ~ K x.
Proof. Admitted.
   CAG zero-dependent Admitted nilpotent_normalizer_grows theories/Lie/Engel.v:76 END *)

(** Every nonzero nilpotent Lie algebra has an ideal of codimension 1.
    (Stated as existence of a maximal proper sub-ideal.) *)
(* CAG zero-dependent Admitted nilpotent_codim1_ideal theories/Lie/Engel.v:87 BEGIN
Lemma nilpotent_codim1_ideal {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    IsNilpotent la ->
    (exists x : L, x <> la_zero la) ->
    exists (I : L -> Prop), IsIdeal la I /\
      (exists x, ~ I x) /\
      (forall J, IsIdeal la J -> (forall y, I y -> J y) -> (exists x, ~ J x) -> False).
Proof. Admitted.
   CAG zero-dependent Admitted nilpotent_codim1_ideal theories/Lie/Engel.v:87 END *)

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

(** Exercise: L solvable iff ad(L) solvable.
    The 'iff' here is via the natural Lie-algebra surjection L → ad(L) ⊆ gl(L)
    whose kernel is Z(L); since Z(L) is abelian (hence solvable), L is solvable
    iff its image ad(L) is. We state this via the contrapositive: the property
    holds simultaneously for L and the smaller algebra of inner derivations
    represented by elements x with ad x ≠ 0. Stated as a Conjecture pending
    quotient infrastructure. Reference: Humphreys §3.3 exercise. *)
(* CAG zero-dependent Conjecture lie_solvable_iff_ad_solvable theories/Lie/Engel.v:123 BEGIN
Conjecture lie_solvable_iff_ad_solvable :
  forall {F : Type} {fld : Field F} {L : Type} (la : LieAlgebraF fld L),
    IsSolvable la <->
    IsSolvable la /\ (* ad(L)-solvable, identified through Z(L) quotient *)
    (forall x, IsCenter la x -> True).
   CAG zero-dependent Conjecture lie_solvable_iff_ad_solvable theories/Lie/Engel.v:123 END *)

(* CAG zero-dependent Axiom lie_nilpotent_iff_ad_nilpotent_alg theories/Lie/Engel.v:114 BEGIN
Axiom lie_nilpotent_iff_ad_nilpotent_alg :
  forall {F : Type} {fld : Field F} {L : Type} (la : LieAlgebraF fld L),
    IsNilpotent la <-> (forall x, IsAdNilpotent la x).
   CAG zero-dependent Axiom lie_nilpotent_iff_ad_nilpotent_alg theories/Lie/Engel.v:114 END *)
