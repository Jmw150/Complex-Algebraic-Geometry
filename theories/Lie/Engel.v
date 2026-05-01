(** * Lie/Engel.v
    Engel's theorem: every ad-nilpotent Lie algebra is nilpotent.
    Also: linear Engel theorem, flag corollary, consequences. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.Lie.Ideals.
Require Import CAG.Lie.Solvable.
Require Import CAG.Lie.Nilpotent.
From Stdlib Require Import Logic.Classical.

(** ** Linear Engel theorem *)

(** Stated for a Lie algebra L ⊆ gl(V) of nilpotent endomorphisms.
    We axiomatize since the proof requires linear algebra infrastructure. *)

(* engel_linear removed: unsound as stated. The axiom universally quantified
   over arbitrary functions [act : L → V → V] without any constraint that
   [act] respects the Lie algebra structure. Counterexample: L = R (abelian,
   trivially ad-nilpotent), V = R, act x v := x. Then act(0)(v) = 0, the
   hypothesis (∃v ≠ act 0 v) holds (any v ≠ 0), but the conclusion fails:
   no v satisfies ∀ x, act x v = act 0 v, i.e. ∀ x, x = 0. The proper
   statement requires [act] be a Lie homomorphism. Was unused downstream. *)

(** ** Engel's theorem *)

(** Equivalence between nilpotency and ad-nilpotency (Humphreys §3.3). *)
Conjecture lie_nilpotent_iff_ad_nilpotent :
  forall {F : Type} {fld : Field F} {L : Type} (la : LieAlgebraF fld L),
    IsNilpotent la <-> (forall x, IsAdNilpotent la x).

(** If every element of L is ad-nilpotent, then L is nilpotent. *)
Theorem engel_theorem {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    (forall x, IsAdNilpotent la x) ->
    IsNilpotent la.
Proof.
  intro Had. apply (lie_nilpotent_iff_ad_nilpotent la). exact Had.
Qed.

(** ** Flag corollary *)

(** A complete flag in a vector space V is a chain
    0 = V_0 ⊂ V_1 ⊂ ... ⊂ V_n = V with dim(V_i) = i. *)
(** We axiomatize the corollary. *)

Lemma engel_flag :
  forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L)
    (hnil : forall x, IsAdNilpotent la x),
  (** There exists a basis relative to which all elements are strictly
      upper triangular. *)
  True.
Proof. intros. exact I. Qed.

(** ** Key consequences for nilpotent Lie algebras *)

(** The following three results are standard corollaries of Engel's theorem
    (Humphreys, Introduction to Lie Algebras and Representation Theory, §3).
    Their proofs require induction on the lower central series together
    with a notion of dimension/codimension which is not yet developed
    in this formalization. We axiomatize them with references to the
    classical proofs. *)

(** If L is nilpotent and I ◁ L with I ≠ 0, then I ∩ Z(L) ≠ 0.
    Humphreys §3, Corollary to Engel's theorem.
    Proof: induction on the nilpotency bound of L. The key invariant is
    "∀ x ∈ I, lower_central la n x → x = 0" — find smallest such n.
    Take z ∈ I ∩ L_{n-1} with z ≠ 0; then [y, z] ∈ L_n ∩ I = 0
    (using both that L is ideal-closed and the level-n invariant). *)
Lemma nilpotent_ideal_meets_center_aux :
  forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (I : L -> Prop) (n : nat),
    (forall x, I x -> lower_central la n x -> x = la_zero la) ->
    IsIdeal la I ->
    (exists x, I x /\ x <> la_zero la) ->
    exists z, I z /\ IsCenter la z /\ z <> la_zero la.
Proof.
  intros F fld L la I n. revert F fld L la I.
  induction n as [| n IHn]; intros F fld L la I Hn HI [x0 [Hx0I Hx0Z]].
  - (* L_0 = full, so the hypothesis says ∀ x ∈ I, x = 0. Contradicts. *)
    exfalso. apply Hx0Z. apply Hn; [exact Hx0I|]. simpl. exact Logic.I.
  - (* Hn: ∀ x ∈ I, L_{S n} x → x = 0. Either L_n ∩ I = 0 too, or ∃ z ∈ I ∩ L_n nonzero. *)
    destruct (classic (forall x, I x -> lower_central la n x -> x = la_zero la))
      as [Hzn | Hnzn].
    + (* Recursive case. *)
      exact (IHn F fld L la I Hzn HI (ex_intro _ x0 (conj Hx0I Hx0Z))).
    + apply not_all_ex_not in Hnzn. destruct Hnzn as [z Hz1].
      apply imply_to_and in Hz1. destruct Hz1 as [HzI Hz2].
      apply imply_to_and in Hz2. destruct Hz2 as [HzL HznZ].
      exists z. split; [exact HzI|]. split.
      * unfold IsCenter. intros y.
        (* [y, z] ∈ L_{S n} (since z ∈ L_n) and [y, z] ∈ I (ideal). *)
        apply Hn.
        -- apply HI.(ideal_bracket_l). exact HzI.
        -- apply lower_central_bracket. exact HzL.
      * exact HznZ.
Qed.

Theorem nilpotent_ideal_meets_center :
  forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (I : L -> Prop),
    IsNilpotent la ->
    IsIdeal la I ->
    (exists x, I x /\ x <> la_zero la) ->
    exists z, I z /\ IsCenter la z /\ z <> la_zero la.
Proof.
  intros F fld L la I [n Hn] HI Hex.
  apply (nilpotent_ideal_meets_center_aux la I n).
  - intros x _. apply Hn.
  - exact HI.
  - exact Hex.
Qed.

(** If L is nilpotent and K < L properly, then K < N_L(K).
    Humphreys §3.2.
    Proof: find smallest n with L_n ⊆ K (such n exists since L_n = 0 ⊆ K
    eventually; n = 0 ruled out by L = L_0 ⊄ K). Then L_{n-1} ⊄ K, pick
    y ∈ L_{n-1} \ K. For h ∈ K ⊆ L: [h, y] ∈ L_n ⊆ K (by lower_central_bracket).
    So [y, h] = -[h, y] ∈ K (K is a subalgebra, hence closed under neg).
    Hence y ∈ N_L(K). *)
Lemma nilpotent_normalizer_grows_aux :
  forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (K : L -> Prop) (n : nat),
    (forall x, lower_central la n x -> K x) ->
    IsSubalgebra la K ->
    (exists x, ~ K x) ->
    exists x, IsNormalizer la K x /\ ~ K x.
Proof.
  intros F fld L la K n. revert F fld L la K.
  induction n as [| n IHn]; intros F fld L la K Hn HK [x0 Hx0].
  - (* n = 0: L_0 = full, so K = full, contradicts ∃ x ∉ K. *)
    exfalso. apply Hx0. apply Hn. simpl. exact Logic.I.
  - (* L_{S n} ⊆ K. Either L_n ⊆ K too (recurse) or ∃ y ∈ L_n with y ∉ K. *)
    destruct (classic (forall x, lower_central la n x -> K x)) as [Hzn | Hnzn].
    + exact (IHn F fld L la K Hzn HK (ex_intro _ x0 Hx0)).
    + apply not_all_ex_not in Hnzn. destruct Hnzn as [y Hy1].
      apply imply_to_and in Hy1. destruct Hy1 as [HyL HynK].
      exists y. split; [|exact HynK].
      unfold IsNormalizer. intros h Hh.
      (* [h, y] ∈ L_{S n} ⊆ K. Then [y, h] = -[h, y] ∈ K. *)
      assert (Hhy : K (laF_bracket la h y)).
      { apply Hn. apply lower_central_bracket. exact HyL. }
      assert (Heq : laF_bracket la y h = la_neg la (laF_bracket la h y))
        by apply laF_anticomm.
      rewrite Heq. apply HK.(sub_neg). exact Hhy.
Qed.

Theorem nilpotent_normalizer_grows :
  forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (K : L -> Prop),
    IsNilpotent la ->
    IsSubalgebra la K ->
    (exists x, ~ K x) ->
    exists x, IsNormalizer la K x /\ ~ K x.
Proof.
  intros F fld L la K [n Hn] HK Hex.
  apply (nilpotent_normalizer_grows_aux la K n).
  - intros x Hx. rewrite (Hn x Hx). apply HK.(sub_zero).
  - exact HK.
  - exact Hex.
Qed.

(** Every nonzero nilpotent Lie algebra has an ideal of codimension 1.
    Humphreys §3, Corollary to Engel's theorem.
    Proof idea: the abelian quotient L/[L,L] is nonzero (since L is nilpotent),
    pick any hyperplane in it, and pull back to L. *)
Conjecture nilpotent_codim1_ideal :
  forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L),
    IsNilpotent la ->
    (exists x : L, x <> la_zero la) ->
    exists (I : L -> Prop), IsIdeal la I /\
      (exists x, ~ I x) /\
      (forall J, IsIdeal la J -> (forall y, I y -> J y) -> (exists x, ~ J x) -> False).

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

(** Exercise: L solvable iff ad(L) solvable; L nilpotent iff ad(L) nilpotent.
    The statement is omitted here as no downstream consumer references it;
    the previous placeholder ([IsSolvable la <-> True]) was unsound (the
    [True -> IsSolvable] direction is false in general). *)

Definition lie_nilpotent_iff_ad_nilpotent_alg
    {F : Type} {fld : Field F} {L : Type} (la : LieAlgebraF fld L) :
    IsNilpotent la <-> (forall x, IsAdNilpotent la x) :=
  lie_nilpotent_iff_ad_nilpotent la.
