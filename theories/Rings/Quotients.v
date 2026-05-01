(** * Quotients.v — Quotient rings *)

From CAG Require Import Rings.Ring Rings.Ideals.
From Stdlib Require Import FunctionalExtensionality PropExtensionality.

(* ================================================================== *)
(** ** Congruence relation mod an ideal *)
(* ================================================================== *)

(** a ≡ b (mod I) iff ∃ d ∈ I, a + d = b *)
Definition quotient_rel {R : Type} (r : Ring R) (I : R -> Prop) (a b : R) : Prop :=
  exists d, I d /\ radd R r a d = b.

(* ================================================================== *)
(** ** Quotient ring construction
    Carrier: equivalence classes represented as predicates on R.
    Uses FunctionalExtensionality + PropExtensionality (from Stdlib). *)
(* ================================================================== *)

Definition class_of {R : Type} (r : Ring R) (I : R -> Prop) (a : R) : R -> Prop :=
  quotient_rel r I a.

(** The quotient carrier as a sigma type of "witnessed equivalence classes". *)
Definition QuotientCarrier {R : Type} (r : Ring R) (I : R -> Prop) : Type :=
  { S : R -> Prop | exists a, S = class_of r I a }.

(* ------------------------------------------------------------------ *)
(** ** Section: facts about the congruence and the carrier *)
(* ------------------------------------------------------------------ *)

Section QuotientFacts.
  Context {R : Type} (r : Ring R) (I : R -> Prop) (HI : is_ideal r I).

  (* Convenient notations *)
  Local Notation "a + b" := (radd R r a b).
  Local Notation "a * b" := (rmul R r a b).
  Local Notation "- a"   := (rneg R r a).
  Local Notation "0"     := (rzero R r).
  Local Notation "1"     := (rone R r).

  (* Project ideal-hypotheses *)
  Lemma HI_zero : I 0.
  Proof. destruct HI as [[[H _] _] _]. exact H. Qed.

  Lemma HI_add : forall a b, I a -> I b -> I (a + b).
  Proof. destruct HI as [[[_ [Hh _]] _] _]. exact Hh. Qed.

  Lemma HI_neg : forall a, I a -> I (- a).
  Proof. destruct HI as [[[_ [_ Hh]] _] _]. exact Hh. Qed.

  Lemma HI_left : forall x a, I a -> I (x * a).
  Proof. destruct HI as [[_ Hh] _]. exact Hh. Qed.

  Lemma HI_right : forall a x, I a -> I (a * x).
  Proof. destruct HI as [_ [_ Hh]]. exact Hh. Qed.

  (* ~ is an equivalence relation *)
  Lemma qr_refl : forall a, quotient_rel r I a a.
  Proof.
    intro a. exists 0. split.
    - apply HI_zero.
    - apply radd_zero_r.
  Qed.

  Lemma qr_sym : forall a b, quotient_rel r I a b -> quotient_rel r I b a.
  Proof.
    intros a b [d [Hd Heq]].
    exists (- d). split.
    - apply HI_neg. exact Hd.
    - rewrite <- Heq.
      rewrite <- (radd_assoc R r a d (- d)).
      rewrite (radd_neg_r R r d).
      apply radd_zero_r.
  Qed.

  Lemma qr_trans : forall a b c,
      quotient_rel r I a b -> quotient_rel r I b c -> quotient_rel r I a c.
  Proof.
    intros a b c [d1 [Hd1 H1]] [d2 [Hd2 H2]].
    exists (d1 + d2). split.
    - apply HI_add; assumption.
    - rewrite (radd_assoc R r a d1 d2). rewrite H1. exact H2.
  Qed.

  (* Compatibility with ring operations *)

  Lemma qr_add_compat : forall a a' b b',
      quotient_rel r I a a' -> quotient_rel r I b b' ->
      quotient_rel r I (a + b) (a' + b').
  Proof.
    intros a a' b b' [d1 [Hd1 H1]] [d2 [Hd2 H2]].
    exists (d1 + d2). split.
    - apply HI_add; assumption.
    - (* (a+b) + (d1+d2) = (a+d1)+(b+d2) = a' + b' *)
      rewrite <- H1, <- H2.
      apply (radd_swap4 r).
  Qed.

  Lemma qr_mul_compat : forall a a' b b',
      quotient_rel r I a a' -> quotient_rel r I b b' ->
      quotient_rel r I (a * b) (a' * b').
  Proof.
    intros a a' b b' [d1 [Hd1 H1]] [d2 [Hd2 H2]].
    (* a' = a + d1, b' = b + d2, so a' * b' = a*b + a*d2 + d1*b + d1*d2 *)
    exists (a * d2 + (d1 * b + d1 * d2)). split.
    - apply HI_add.
      + apply HI_left. exact Hd2.
      + apply HI_add.
        * apply HI_right. exact Hd1.
        * apply HI_left. exact Hd2.
    - rewrite <- H1, <- H2.
      (* Goal: a*b + (a*d2 + (d1*b + d1*d2)) = (a+d1) * (b+d2) *)
      rewrite (rmul_distrib_r R r a d1 (radd R r b d2)).
      rewrite (rmul_distrib_l R r a b d2).
      rewrite (rmul_distrib_l R r d1 b d2).
      rewrite (radd_assoc R r (a * b) (a * d2) (radd R r (d1 * b) (d1 * d2))).
      reflexivity.
  Qed.

  Lemma qr_neg_compat : forall a a',
      quotient_rel r I a a' -> quotient_rel r I (- a) (- a').
  Proof.
    intros a a' [d [Hd Heq]].
    exists (- d). split.
    - apply HI_neg. exact Hd.
    - rewrite <- Heq.
      rewrite (rneg_add r a d). reflexivity.
  Qed.

  (* class_of equality lemma *)
  Lemma class_eq_iff : forall a b,
      class_of r I a = class_of r I b <-> quotient_rel r I a b.
  Proof.
    intros a b. unfold class_of. split.
    - intro Heq.
      assert (Hb : quotient_rel r I b b) by apply qr_refl.
      rewrite <- Heq in Hb. exact Hb.
    - intro Hab.
      apply functional_extensionality. intro x.
      apply propositional_extensionality. split.
      + intro Hax. apply (qr_trans b a x).
        * apply qr_sym. exact Hab.
        * exact Hax.
      + intro Hbx. apply (qr_trans a b x); assumption.
  Qed.

  (* Membership in class_of *)
  Lemma class_of_mem : forall a x,
      class_of r I a x <-> quotient_rel r I a x.
  Proof. intros. reflexivity. Qed.

  Lemma class_of_self : forall a, class_of r I a a.
  Proof. intro a. apply qr_refl. Qed.

  (* ---------------------------------------------------------------- *)
  (** ** Building elements of QuotientCarrier *)
  (* ---------------------------------------------------------------- *)

  Definition mk_class (a : R) : QuotientCarrier r I :=
    exist _ (class_of r I a) (ex_intro _ a eq_refl).

  Lemma mk_class_eq : forall a b,
      mk_class a = mk_class b <-> quotient_rel r I a b.
  Proof.
    intros a b. split.
    - intro Heq.
      assert (Hpred : class_of r I a = class_of r I b).
      { apply (f_equal (@proj1_sig _ _) ) in Heq. exact Heq. }
      apply class_eq_iff. exact Hpred.
    - intro Hab.
      assert (Hpred : class_of r I a = class_of r I b).
      { apply class_eq_iff. exact Hab. }
      unfold mk_class.
      (* exist _ (class_of r I a) p1 = exist _ (class_of r I b) p2 *)
      apply eq_sig_uncurried. simpl.
      exists Hpred. apply proof_irrelevance.
  Qed.

  (* Surjectivity: every element of QuotientCarrier is mk_class of something *)
  Lemma mk_class_surj : forall x : QuotientCarrier r I,
      exists a : R, mk_class a = x.
  Proof.
    intros [S HS]. destruct HS as [a Ha]. exists a.
    unfold mk_class.
    apply eq_sig_uncurried. simpl.
    exists (eq_sym Ha).
    apply proof_irrelevance.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** Operations on QuotientCarrier
      Operations are defined on predicates without extracting
      representatives. The witness existence is then derived in Prop. *)
  (* ---------------------------------------------------------------- *)

  Definition add_pred (S T : R -> Prop) : R -> Prop :=
    fun x => exists a b, S a /\ T b /\ quotient_rel r I (a + b) x.

  Definition mul_pred (S T : R -> Prop) : R -> Prop :=
    fun x => exists a b, S a /\ T b /\ quotient_rel r I (a * b) x.

  Definition neg_pred (S : R -> Prop) : R -> Prop :=
    fun x => exists a, S a /\ quotient_rel r I (- a) x.

  (* When S = class_of a, T = class_of b, add_pred S T = class_of (a+b). *)
  Lemma add_pred_class : forall a b,
      add_pred (class_of r I a) (class_of r I b) = class_of r I (a + b).
  Proof.
    intros a b. apply functional_extensionality. intro x.
    apply propositional_extensionality. unfold add_pred. split.
    - intros [a' [b' [Ha' [Hb' Hsum]]]].
      apply (qr_trans (a + b) (a' + b') x).
      + apply qr_add_compat; assumption.
      + exact Hsum.
    - intro Hx.
      exists a, b. split; [apply qr_refl | split; [apply qr_refl | exact Hx]].
  Qed.

  Lemma mul_pred_class : forall a b,
      mul_pred (class_of r I a) (class_of r I b) = class_of r I (a * b).
  Proof.
    intros a b. apply functional_extensionality. intro x.
    apply propositional_extensionality. unfold mul_pred. split.
    - intros [a' [b' [Ha' [Hb' Hprod]]]].
      apply (qr_trans (a * b) (a' * b') x).
      + apply qr_mul_compat; assumption.
      + exact Hprod.
    - intro Hx.
      exists a, b. split; [apply qr_refl | split; [apply qr_refl | exact Hx]].
  Qed.

  Lemma neg_pred_class : forall a,
      neg_pred (class_of r I a) = class_of r I (- a).
  Proof.
    intros a. apply functional_extensionality. intro x.
    apply propositional_extensionality. unfold neg_pred. split.
    - intros [a' [Ha' Hneg]].
      apply (qr_trans (- a) (- a') x).
      + apply qr_neg_compat. exact Ha'.
      + exact Hneg.
    - intro Hx.
      exists a. split; [apply qr_refl | exact Hx].
  Qed.

  (* Build QuotientCarrier elements by pairing a predicate with a Prop-witness. *)
  Definition q_add (x y : QuotientCarrier r I) : QuotientCarrier r I.
  Proof.
    refine (exist _ (add_pred (proj1_sig x) (proj1_sig y)) _).
    destruct x as [S [a Ha]]; destruct y as [T [b Hb]]; simpl.
    exists (a + b). subst S T. apply add_pred_class.
  Defined.

  Definition q_mul (x y : QuotientCarrier r I) : QuotientCarrier r I.
  Proof.
    refine (exist _ (mul_pred (proj1_sig x) (proj1_sig y)) _).
    destruct x as [S [a Ha]]; destruct y as [T [b Hb]]; simpl.
    exists (a * b). subst S T. apply mul_pred_class.
  Defined.

  Definition q_neg (x : QuotientCarrier r I) : QuotientCarrier r I.
  Proof.
    refine (exist _ (neg_pred (proj1_sig x)) _).
    destruct x as [S [a Ha]]; simpl.
    exists (- a). subst S. apply neg_pred_class.
  Defined.

  Definition q_zero : QuotientCarrier r I := mk_class 0.
  Definition q_one  : QuotientCarrier r I := mk_class 1.

  (* Computational lemmas: operations on representatives. *)
  Lemma q_add_mk : forall a b,
      q_add (mk_class a) (mk_class b) = mk_class (a + b).
  Proof.
    intros a b. unfold q_add, mk_class.
    apply eq_sig_uncurried. simpl.
    exists (add_pred_class a b).
    apply proof_irrelevance.
  Qed.

  Lemma q_mul_mk : forall a b,
      q_mul (mk_class a) (mk_class b) = mk_class (a * b).
  Proof.
    intros a b. unfold q_mul, mk_class.
    apply eq_sig_uncurried. simpl.
    exists (mul_pred_class a b).
    apply proof_irrelevance.
  Qed.

  Lemma q_neg_mk : forall a,
      q_neg (mk_class a) = mk_class (- a).
  Proof.
    intros a. unfold q_neg, mk_class.
    apply eq_sig_uncurried. simpl.
    exists (neg_pred_class a).
    apply proof_irrelevance.
  Qed.


  (* ---------------------------------------------------------------- *)
  (** ** Ring laws on the quotient *)
  (* ---------------------------------------------------------------- *)

  Lemma q_add_assoc : forall x y z,
      q_add x (q_add y z) = q_add (q_add x y) z.
  Proof.
    intros x y z.
    destruct (mk_class_surj x) as [a Ha]. subst x.
    destruct (mk_class_surj y) as [b Hb]. subst y.
    destruct (mk_class_surj z) as [c Hc]. subst z.
    rewrite !q_add_mk. apply mk_class_eq.
    rewrite (radd_assoc R r a b c). apply qr_refl.
  Qed.

  Lemma q_add_comm : forall x y, q_add x y = q_add y x.
  Proof.
    intros x y.
    destruct (mk_class_surj x) as [a Ha]. subst x.
    destruct (mk_class_surj y) as [b Hb]. subst y.
    rewrite !q_add_mk. apply mk_class_eq.
    rewrite (radd_comm R r a b). apply qr_refl.
  Qed.

  Lemma q_add_zero_r : forall x, q_add x q_zero = x.
  Proof.
    intros x.
    destruct (mk_class_surj x) as [a Ha]. subst x.
    unfold q_zero. rewrite q_add_mk. apply mk_class_eq.
    rewrite (radd_zero_r R r a). apply qr_refl.
  Qed.

  Lemma q_add_neg_r : forall x, q_add x (q_neg x) = q_zero.
  Proof.
    intros x.
    destruct (mk_class_surj x) as [a Ha]. subst x.
    rewrite q_neg_mk, q_add_mk. unfold q_zero. apply mk_class_eq.
    rewrite (radd_neg_r R r a). apply qr_refl.
  Qed.

  Lemma q_mul_assoc : forall x y z,
      q_mul x (q_mul y z) = q_mul (q_mul x y) z.
  Proof.
    intros x y z.
    destruct (mk_class_surj x) as [a Ha]. subst x.
    destruct (mk_class_surj y) as [b Hb]. subst y.
    destruct (mk_class_surj z) as [c Hc]. subst z.
    rewrite !q_mul_mk. apply mk_class_eq.
    rewrite (rmul_assoc R r a b c). apply qr_refl.
  Qed.

  Lemma q_mul_one_r : forall x, q_mul x q_one = x.
  Proof.
    intros x.
    destruct (mk_class_surj x) as [a Ha]. subst x.
    unfold q_one. rewrite q_mul_mk. apply mk_class_eq.
    rewrite (rmul_one_r R r a). apply qr_refl.
  Qed.

  Lemma q_mul_one_l : forall x, q_mul q_one x = x.
  Proof.
    intros x.
    destruct (mk_class_surj x) as [a Ha]. subst x.
    unfold q_one. rewrite q_mul_mk. apply mk_class_eq.
    rewrite (rmul_one_l R r a). apply qr_refl.
  Qed.

  Lemma q_mul_distrib_l : forall x y z,
      q_mul x (q_add y z) = q_add (q_mul x y) (q_mul x z).
  Proof.
    intros x y z.
    destruct (mk_class_surj x) as [a Ha]. subst x.
    destruct (mk_class_surj y) as [b Hb]. subst y.
    destruct (mk_class_surj z) as [c Hc]. subst z.
    rewrite !q_add_mk, !q_mul_mk, !q_add_mk. apply mk_class_eq.
    rewrite (rmul_distrib_l R r a b c). apply qr_refl.
  Qed.

  Lemma q_mul_distrib_r : forall x y z,
      q_mul (q_add x y) z = q_add (q_mul x z) (q_mul y z).
  Proof.
    intros x y z.
    destruct (mk_class_surj x) as [a Ha]. subst x.
    destruct (mk_class_surj y) as [b Hb]. subst y.
    destruct (mk_class_surj z) as [c Hc]. subst z.
    rewrite !q_add_mk, !q_mul_mk, !q_add_mk. apply mk_class_eq.
    rewrite (rmul_distrib_r R r a b c). apply qr_refl.
  Qed.

  Definition QuotientRing_local : Ring (QuotientCarrier r I) :=
    {| radd := q_add;
       rmul := q_mul;
       rzero := q_zero;
       rone := q_one;
       rneg := q_neg;
       radd_assoc := q_add_assoc;
       radd_comm := q_add_comm;
       radd_zero_r := q_add_zero_r;
       radd_neg_r := q_add_neg_r;
       rmul_assoc := q_mul_assoc;
       rmul_one_r := q_mul_one_r;
       rmul_one_l := q_mul_one_l;
       rmul_distrib_l := q_mul_distrib_l;
       rmul_distrib_r := q_mul_distrib_r;
    |}.

  (* The projection map *)
  Definition quot_proj_local : RingHom r QuotientRing_local.
  Proof.
    refine {| rhom_fn := mk_class;
              rhom_add := _;
              rhom_mul := _;
              rhom_one := _ |}.
    - intros a b. simpl. symmetry. apply q_add_mk.
    - intros a b. simpl. symmetry. apply q_mul_mk.
    - simpl. reflexivity.
  Defined.

  Lemma quot_proj_surj_local : forall x : QuotientCarrier r I,
      exists a : R, rhom_fn quot_proj_local a = x.
  Proof.
    intros x. simpl. apply mk_class_surj.
  Qed.

  Lemma quot_proj_kernel_local : forall a : R,
      rhom_fn quot_proj_local a = rzero (QuotientCarrier r I) QuotientRing_local
      <-> I a.
  Proof.
    intros a. simpl. unfold q_zero. split.
    - intro Heq. apply mk_class_eq in Heq.
      destruct Heq as [d [Hd Heq]].
      (* a + d = 0, so d = -a, hence -a ∈ I, hence a ∈ I (using rneg_neg) *)
      assert (Hd' : d = - a).
      { apply (radd_inv_uniq r a d). exact Heq. }
      subst d.
      assert (Ha : a = - (- a)) by (symmetry; apply (rneg_neg r)).
      rewrite Ha. apply HI_neg. exact Hd.
    - intro Ha.
      apply mk_class_eq.
      exists (- a). split.
      + apply HI_neg. exact Ha.
      + apply (radd_neg_r R r).
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** Universal property *)
  (* ---------------------------------------------------------------- *)

  Section Universal.
    Context {S : Type} (s : Ring S) (phi : RingHom r s)
            (Hker : forall a, I a -> rhom_fn phi a = rzero S s).

    (* Given a class, define φ-bar by picking a representative. We use
       constructive surjectivity (which gives a Prop existential) but
       phrase the function via the universal-existence pattern. We need
       the *function* to be definable, not just existentially proved.
       Approach: use the predicate to extract via the witness. *)

    (* Key observation: since QuotientCarrier is a sigma type with a Prop
       second component, we cannot directly destruct to extract the
       representative computationally. Instead, we define φbar
       relationally: φbar(x) = φ(a) for *any* a with mk_class a = x.
       The result is well-defined because of Hker. *)

    (* The induced function phibar : QuotientCarrier -> S is constructed
       in the [quotient_universal] lemma below using
       [constructive_definite_description] from Stdlib.Logic.Description.
       This is necessary because extracting a representative [a] from
       [x : QuotientCarrier] requires going from a Prop existential to
       a Type-level element. Definite description is consistent with
       PropExt+FunExt (already used here). *)

  End Universal.

End QuotientFacts.

(* ================================================================== *)
(** ** Top-level definitions matching the original axiom signatures *)
(* ================================================================== *)

Definition QuotientRing {R : Type} (r : Ring R) (I : R -> Prop)
    (HI : is_ideal r I) : Ring (QuotientCarrier r I) :=
  QuotientRing_local r I HI.

Definition quot_proj {R : Type} (r : Ring R) (I : R -> Prop)
    (HI : is_ideal r I) : RingHom r (QuotientRing r I HI) :=
  quot_proj_local r I HI.

Lemma quot_proj_surj : forall {R : Type} (r : Ring R) (I : R -> Prop)
    (HI : is_ideal r I) (x : QuotientCarrier r I),
    exists a : R, rhom_fn (quot_proj r I HI) a = x.
Proof. intros. apply quot_proj_surj_local. Qed.

Lemma quot_proj_kernel : forall {R : Type} (r : Ring R) (I : R -> Prop)
    (HI : is_ideal r I) (a : R),
    rhom_fn (quot_proj r I HI) a =
      rzero (QuotientCarrier r I) (QuotientRing r I HI) <-> I a.
Proof. intros. apply quot_proj_kernel_local. Qed.

(* ================================================================== *)
(** ** Universal property of the quotient
    The function phibar is constructed using Stdlib's
    [constructive_definite_description] (Description axiom), which
    follows from FunExt+PropExt+ClassicalEpsilon. We use the lighter
    [Description] from Stdlib.Logic.Description. *)
(* ================================================================== *)

From Stdlib Require Import Description.

Lemma quotient_universal :
  forall {R S : Type} (r : Ring R) (s : Ring S) (I : R -> Prop)
         (HI : is_ideal r I)
         (phi : RingHom r s)
         (Hker : forall a, I a -> rhom_fn phi a = rzero S s),
  exists! phibar : RingHom (QuotientRing r I HI) s,
    forall a : R,
      rhom_fn phibar (rhom_fn (quot_proj r I HI) a) = rhom_fn phi a.
Proof.
  intros R S r s I HI phi Hker.
  (* For each x : QuotientCarrier, use definite description to pick the
     unique y such that phibar_pred x y. *)
  pose (P := fun x y => exists a : R, mk_class r I a = x /\ rhom_fn phi a = y).
  assert (Hexists_unique : forall x : QuotientCarrier r I,
              exists! y : S, P x y).
  { intro x. unfold P.
    destruct (mk_class_surj r I x) as [a Ha].
    exists (rhom_fn phi a). split.
    - exists a. split; [exact Ha | reflexivity].
    - intros y' [a' [Ha' Hy']].
      assert (Heq : mk_class r I a = mk_class r I a').
      { rewrite Ha, Ha'. reflexivity. }
      apply (mk_class_eq r I HI) in Heq.
      destruct Heq as [d [Hd Hd_eq]].
      assert (Hphi_d : rhom_fn phi d = rzero S s) by (apply Hker; exact Hd).
      assert (Hphi_eq : rhom_fn phi a = rhom_fn phi a').
      { rewrite <- Hd_eq. rewrite (rhom_add phi a d).
        rewrite Hphi_d. symmetry. apply (radd_zero_r S s). }
      rewrite Hphi_eq. exact Hy'. }
  pose (phibar_fn := fun x : QuotientCarrier r I =>
          proj1_sig (constructive_definite_description (P x) (Hexists_unique x))).
  assert (Hphibar_spec : forall x, P x (phibar_fn x)).
  { intro x. unfold phibar_fn.
    exact (proj2_sig (constructive_definite_description (P x) (Hexists_unique x))). }
  (* Compute phibar on mk_class a = phi a *)
  assert (Hphibar_mk : forall a, phibar_fn (mk_class r I a) = rhom_fn phi a).
  { intro a.
    destruct (Hphibar_spec (mk_class r I a)) as [a' [Ha' Hy']].
    (* Hy' : phi a' = phibar_fn (mk_class a) *)
    (* Ha' : mk_class a' = mk_class a, so a' ~ a *)
    rewrite <- Hy'.
    apply (mk_class_eq r I HI) in Ha'.
    destruct Ha' as [d [Hd Hd_eq]].
    assert (Hphi_d : rhom_fn phi d = rzero S s) by (apply Hker; exact Hd).
    rewrite <- Hd_eq.
    rewrite (rhom_add phi a' d), Hphi_d.
    symmetry. apply (radd_zero_r S s). }
  (* Build the homomorphism *)
  assert (Hphibar_add : forall x y,
              phibar_fn (radd (QuotientCarrier r I) (QuotientRing r I HI) x y)
              = radd S s (phibar_fn x) (phibar_fn y)).
  { intros x y.
    destruct (mk_class_surj r I x) as [a Ha]. subst x.
    destruct (mk_class_surj r I y) as [b Hb]. subst y.
    simpl radd at 1. unfold QuotientRing, QuotientRing_local. simpl.
    rewrite (q_add_mk r I HI a b).
    rewrite !Hphibar_mk.
    apply (rhom_add phi). }
  assert (Hphibar_mul : forall x y,
              phibar_fn (rmul (QuotientCarrier r I) (QuotientRing r I HI) x y)
              = rmul S s (phibar_fn x) (phibar_fn y)).
  { intros x y.
    destruct (mk_class_surj r I x) as [a Ha]. subst x.
    destruct (mk_class_surj r I y) as [b Hb]. subst y.
    simpl rmul at 1. unfold QuotientRing, QuotientRing_local. simpl.
    rewrite (q_mul_mk r I HI a b).
    rewrite !Hphibar_mk.
    apply (rhom_mul phi). }
  assert (Hphibar_one :
              phibar_fn (rone (QuotientCarrier r I) (QuotientRing r I HI))
              = rone S s).
  { simpl. unfold QuotientRing, QuotientRing_local. simpl.
    unfold q_one. rewrite Hphibar_mk. apply (rhom_one phi). }
  pose (phibar :=
          {| rhom_fn := phibar_fn;
             rhom_add := Hphibar_add;
             rhom_mul := Hphibar_mul;
             rhom_one := Hphibar_one
          |}).
  exists phibar. split.
  - intros a. simpl. unfold quot_proj, quot_proj_local. simpl.
    apply Hphibar_mk.
  - intros phibar' Hphibar'.
    (* Two ring homs that agree on the image of quot_proj and the
       image is everything (surjectivity) must be equal. *)
    assert (Hfn_eq : rhom_fn phibar' = phibar_fn).
    { apply functional_extensionality. intros x.
      destruct (mk_class_surj r I x) as [a Ha]. subst x.
      rewrite Hphibar_mk.
      specialize (Hphibar' a). simpl in Hphibar'.
      unfold quot_proj, quot_proj_local in Hphibar'. simpl in Hphibar'.
      exact Hphibar'. }
    destruct phibar' as [fn' add' mul' one']. simpl in Hfn_eq.
    subst fn'.
    assert (add'_eq : add' = Hphibar_add) by apply proof_irrelevance.
    assert (mul'_eq : mul' = Hphibar_mul) by apply proof_irrelevance.
    assert (one'_eq : one' = Hphibar_one) by apply proof_irrelevance.
    subst add' mul' one'. reflexivity.
Qed.
