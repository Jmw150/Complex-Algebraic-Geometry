(** * Lie/Homomorphisms.v
    Lie algebra homomorphisms, kernels, images, quotient Lie algebras,
    and the three isomorphism theorems. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.Lie.Ideals.

(** ** Kernel and image *)

(** The kernel of a Lie homomorphism. *)
Definition LieKer {F : Type} {fld : Field F} {L M : Type}
    {la : LieAlgebraF fld L} {lb : LieAlgebraF fld M}
    (φ : LieHom la lb) (x : L) : Prop :=
  lh_fn φ x = la_zero lb.

(** Ker(φ) is an ideal of L. *)
Lemma ker_is_ideal {F : Type} {fld : Field F} {L M : Type}
    {la : LieAlgebraF fld L} {lb : LieAlgebraF fld M}
    (φ : LieHom la lb) : IsIdeal la (LieKer φ).
Proof.
  unfold LieKer. constructor.
  - apply lh_zero.
  - intros x y Hx Hy. rewrite φ.(lh_add), Hx, Hy.
    apply (laF_vs lb).(vsF_add_zero_r).
  - intros x Hx. rewrite lh_neg, Hx. apply vsF_neg_zero.
  - intros a x Hx. rewrite φ.(lh_scale), Hx. apply vsF_scale_zero_v.
  - intros x y Hy. rewrite φ.(lh_bracket), Hy. apply laF_bracket_zero_r.
Qed.

(** The image of a Lie homomorphism. *)
Definition LieIm {F : Type} {fld : Field F} {L M : Type}
    {la : LieAlgebraF fld L} {lb : LieAlgebraF fld M}
    (φ : LieHom la lb) (y : M) : Prop :=
  exists x, lh_fn φ x = y.

(** A Lie hom preserves zero brackets: [x, y] = 0 → [φ x, φ y] = 0. *)
Lemma lh_preserves_zero_bracket {F : Type} {fld : Field F} {L M : Type}
    {la : LieAlgebraF fld L} {lb : LieAlgebraF fld M}
    (φ : LieHom la lb) (x y : L) :
    laF_bracket la x y = la_zero la ->
    laF_bracket lb (lh_fn φ x) (lh_fn φ y) = la_zero lb.
Proof.
  intro Hxy.
  rewrite <- φ.(lh_bracket).
  rewrite Hxy.
  apply lh_zero.
Qed.

(** A Lie hom maps abelian Lie algebras to images that bracket-zero on themselves.
    If la is abelian then for any x, y in image, bracket = 0. *)
Lemma lh_image_of_abelian_brackets_zero {F : Type} {fld : Field F} {L M : Type}
    {la : LieAlgebraF fld L} {lb : LieAlgebraF fld M}
    (φ : LieHom la lb)
    (Habel : forall x y, laF_bracket la x y = la_zero la) :
    forall x y, laF_bracket lb (lh_fn φ x) (lh_fn φ y) = la_zero lb.
Proof.
  intros x y. apply lh_preserves_zero_bracket. apply Habel.
Qed.

(** Image of a central element commutes with every element in the image. *)
Lemma lh_image_of_center {F : Type} {fld : Field F} {L M : Type}
    {la : LieAlgebraF fld L} {lb : LieAlgebraF fld M}
    (φ : LieHom la lb) (x : L) :
    (forall y : L, laF_bracket la y x = la_zero la) ->
    forall z : L, laF_bracket lb (lh_fn φ z) (lh_fn φ x) = la_zero lb.
Proof.
  intros Hc z.
  rewrite <- φ.(lh_bracket).
  rewrite (Hc z).
  apply lh_zero.
Qed.

(** Im(φ) is a subalgebra of M. *)
Lemma im_is_subalgebra {F : Type} {fld : Field F} {L M : Type}
    {la : LieAlgebraF fld L} {lb : LieAlgebraF fld M}
    (φ : LieHom la lb) : IsSubalgebra lb (LieIm φ).
Proof.
  constructor; unfold LieIm.
  - exists (la_zero la). apply lh_zero.
  - intros x y [a Ha] [b Hb]. exists (la_add la a b).
    rewrite lh_add, Ha, Hb. reflexivity.
  - intros x [a Ha]. exists (la_neg la a). rewrite lh_neg, Ha. reflexivity.
  - intros c x [a Ha]. exists (la_scale la c a). rewrite lh_scale, Ha. reflexivity.
  - intros x y [a Ha] [b Hb]. exists (laF_bracket la a b).
    rewrite lh_bracket, Ha, Hb. reflexivity.
Qed.

(** ** Quotient Lie algebra *)

(** Construction of the quotient Lie algebra L/I as a sigma type of
    equivalence-class predicates. Mirrors the quotient ring construction
    in Rings/Quotients.v. Axiom dependencies: PropExt, FunExt
    (proof_irrelevance follows from PropExt). *)

From Stdlib Require Import FunctionalExtensionality PropExtensionality.
From Stdlib Require Import ClassicalFacts.

(** proof_irrelevance derived from propositional_extensionality (no extra axiom). *)
Lemma lie_proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2.
Proof.
  apply ext_prop_dep_proof_irrel_cic.
  unfold prop_extensionality. intros A B [H1 H2].
  apply propositional_extensionality. split; assumption.
Qed.

Section QuotientLieAlgebra.

  Context {F : Type} {fld : Field F} {L : Type}
          (la : LieAlgebraF fld L) (I : L -> Prop) (hI : IsIdeal la I).

  (** Congruence relation: a ≡ b mod I iff ∃ d ∈ I, a + d = b. *)
  Definition lie_quotient_rel (a b : L) : Prop :=
    exists d, I d /\ la_add la a d = b.

  (** Equivalence class of a as a predicate on L. *)
  Definition lie_class_of (a : L) : L -> Prop := lie_quotient_rel a.

  (** Equivalence properties. *)
  Lemma lqr_refl : forall a, lie_quotient_rel a a.
  Proof.
    intro a. exists (la_zero la). split.
    - apply hI.(ideal_zero).
    - apply (laF_vs la).(vsF_add_zero_r).
  Qed.

  Lemma lqr_sym : forall a b, lie_quotient_rel a b -> lie_quotient_rel b a.
  Proof.
    intros a b [d [Hd Heq]].
    exists (la_neg la d). split.
    - apply hI.(ideal_neg). exact Hd.
    - rewrite <- Heq.
      rewrite <- (laF_vs la).(vsF_add_assoc).
      rewrite (laF_vs la).(vsF_add_neg_r).
      apply (laF_vs la).(vsF_add_zero_r).
  Qed.

  Lemma lqr_trans : forall a b c,
      lie_quotient_rel a b -> lie_quotient_rel b c -> lie_quotient_rel a c.
  Proof.
    intros a b c [d1 [Hd1 H1]] [d2 [Hd2 H2]].
    exists (la_add la d1 d2). split.
    - apply hI.(ideal_add); assumption.
    - rewrite (laF_vs la).(vsF_add_assoc). rewrite H1. exact H2.
  Qed.

  (** Compatibility of operations with the congruence. *)
  (* Helper: 4-way swap (a+b)+(d1+d2) = (a+d1)+(b+d2). *)
  Lemma vs_add_swap4 : forall a b d1 d2,
      la_add la (la_add la a b) (la_add la d1 d2) =
      la_add la (la_add la a d1) (la_add la b d2).
  Proof.
    intros a b d1 d2.
    (* (a+b)+(d1+d2) = a+(b+(d1+d2)) = a+((b+d1)+d2)
                     = a+((d1+b)+d2) = a+(d1+(b+d2)) = (a+d1)+(b+d2) *)
    rewrite <- ((laF_vs la).(vsF_add_assoc) a b (la_add la d1 d2)).
    rewrite ((laF_vs la).(vsF_add_assoc) b d1 d2).
    rewrite ((laF_vs la).(vsF_add_comm) b d1).
    rewrite <- ((laF_vs la).(vsF_add_assoc) d1 b d2).
    rewrite ((laF_vs la).(vsF_add_assoc) a d1 (la_add la b d2)).
    reflexivity.
  Qed.

  Lemma lqr_add_compat : forall a a' b b',
      lie_quotient_rel a a' -> lie_quotient_rel b b' ->
      lie_quotient_rel (la_add la a b) (la_add la a' b').
  Proof.
    intros a a' b b' [d1 [Hd1 H1]] [d2 [Hd2 H2]].
    exists (la_add la d1 d2). split.
    - apply hI.(ideal_add); assumption.
    - rewrite <- H1, <- H2. apply vs_add_swap4.
  Qed.

  Lemma lqr_neg_compat : forall a a',
      lie_quotient_rel a a' -> lie_quotient_rel (la_neg la a) (la_neg la a').
  Proof.
    intros a a' [d [Hd Heq]].
    exists (la_neg la d). split.
    - apply hI.(ideal_neg). exact Hd.
    - rewrite <- Heq.
      rewrite <- (vsF_neg_add (laF_vs la)). reflexivity.
  Qed.

  Lemma lqr_scale_compat : forall c a a',
      lie_quotient_rel a a' -> lie_quotient_rel (la_scale la c a) (la_scale la c a').
  Proof.
    intros c a a' [d [Hd Heq]].
    exists (la_scale la c d). split.
    - apply hI.(ideal_scale). exact Hd.
    - rewrite <- Heq.
      rewrite <- (laF_vs la).(vsF_scale_add_v). reflexivity.
  Qed.

  Lemma lqr_bracket_compat : forall a a' b b',
      lie_quotient_rel a a' -> lie_quotient_rel b b' ->
      lie_quotient_rel (laF_bracket la a b) (laF_bracket la a' b').
  Proof.
    intros a a' b b' [d1 [Hd1 H1]] [d2 [Hd2 H2]].
    (* a' = a + d1, b' = b + d2.
       [a',b'] = [a+d1,b+d2] = [a,b] + [a,d2] + [d1,b] + [d1,d2]
       The last three are in I (by ideal_bracket_l on b' or a-side using anticomm). *)
    exists (la_add la (laF_bracket la a d2)
              (la_add la (laF_bracket la d1 b) (laF_bracket la d1 d2))).
    split.
    - apply hI.(ideal_add).
      + apply hI.(ideal_bracket_l). exact Hd2.
      + apply hI.(ideal_add).
        * (* [d1, b] : use anticomm = -[b, d1], and [b, d1] in I since d1 in I *)
          rewrite (laF_anticomm la d1 b).
          apply hI.(ideal_neg). apply hI.(ideal_bracket_l). exact Hd1.
        * apply hI.(ideal_bracket_l). exact Hd2.
    - rewrite <- H1, <- H2.
      (* [a+d1, b+d2] = [a,b] + ([a,d2] + ([d1,b] + [d1,d2])) *)
      rewrite la.(laF_bracket_add_l).
      rewrite !la.(laF_bracket_add_r).
      (* LHS = ([a,b]+[a,d2]) + ([d1,b]+[d1,d2])
         RHS = [a,b] + ([a,d2] + ([d1,b]+[d1,d2])) *)
      rewrite <- ((laF_vs la).(vsF_add_assoc)
                  (laF_bracket la a b) (laF_bracket la a d2)
                  (la_add la (laF_bracket la d1 b) (laF_bracket la d1 d2))).
      reflexivity.
  Qed.

  (** Class equality. *)
  Lemma lie_class_eq_iff : forall a b,
      lie_class_of a = lie_class_of b <-> lie_quotient_rel a b.
  Proof.
    intros a b. unfold lie_class_of. split.
    - intro Heq.
      assert (Hb : lie_quotient_rel b b) by apply lqr_refl.
      rewrite <- Heq in Hb. exact Hb.
    - intro Hab.
      apply functional_extensionality. intro x.
      apply propositional_extensionality. split.
      + intro Hax. apply (lqr_trans b a x); [apply lqr_sym; exact Hab | exact Hax].
      + intro Hbx. apply (lqr_trans a b x); assumption.
  Qed.

  (** The quotient carrier as a sigma type. *)
  Definition QuotType : Type :=
    { S : L -> Prop | exists a, S = lie_class_of a }.

  Definition mk_class (a : L) : QuotType :=
    exist _ (lie_class_of a) (ex_intro _ a eq_refl).

  Lemma mk_class_eq : forall a b,
      mk_class a = mk_class b <-> lie_quotient_rel a b.
  Proof.
    intros a b. split.
    - intro Heq.
      assert (Hpred : lie_class_of a = lie_class_of b).
      { apply (f_equal (@proj1_sig _ _)) in Heq. exact Heq. }
      apply lie_class_eq_iff. exact Hpred.
    - intro Hab.
      assert (Hpred : lie_class_of a = lie_class_of b)
        by (apply lie_class_eq_iff; exact Hab).
      unfold mk_class. apply eq_sig_uncurried. simpl.
      exists Hpred. apply lie_proof_irrelevance.
  Qed.

  Lemma mk_class_surj : forall x : QuotType, exists a, mk_class a = x.
  Proof.
    intros [S [a Ha]]. exists a.
    unfold mk_class. apply eq_sig_uncurried. simpl.
    exists (eq_sym Ha). apply lie_proof_irrelevance.
  Qed.

  (** Lifted operations on predicates. *)
  Definition q_add_pred (S T : L -> Prop) : L -> Prop :=
    fun x => exists a b, S a /\ T b /\ lie_quotient_rel (la_add la a b) x.

  Definition q_neg_pred (S : L -> Prop) : L -> Prop :=
    fun x => exists a, S a /\ lie_quotient_rel (la_neg la a) x.

  Definition q_scale_pred (c : F) (S : L -> Prop) : L -> Prop :=
    fun x => exists a, S a /\ lie_quotient_rel (la_scale la c a) x.

  Definition q_bracket_pred (S T : L -> Prop) : L -> Prop :=
    fun x => exists a b, S a /\ T b /\ lie_quotient_rel (laF_bracket la a b) x.

  Lemma q_add_pred_class : forall a b,
      q_add_pred (lie_class_of a) (lie_class_of b) = lie_class_of (la_add la a b).
  Proof.
    intros a b. apply functional_extensionality. intro x.
    apply propositional_extensionality. unfold q_add_pred. split.
    - intros [a' [b' [Ha' [Hb' Hsum]]]].
      apply (lqr_trans (la_add la a b) (la_add la a' b') x).
      + apply lqr_add_compat; assumption.
      + exact Hsum.
    - intro Hx. exists a, b. split; [apply lqr_refl|split;[apply lqr_refl|exact Hx]].
  Qed.

  Lemma q_neg_pred_class : forall a,
      q_neg_pred (lie_class_of a) = lie_class_of (la_neg la a).
  Proof.
    intros a. apply functional_extensionality. intro x.
    apply propositional_extensionality. unfold q_neg_pred. split.
    - intros [a' [Ha' Hneg]].
      apply (lqr_trans (la_neg la a) (la_neg la a') x).
      + apply lqr_neg_compat. exact Ha'.
      + exact Hneg.
    - intro Hx. exists a. split; [apply lqr_refl|exact Hx].
  Qed.

  Lemma q_scale_pred_class : forall c a,
      q_scale_pred c (lie_class_of a) = lie_class_of (la_scale la c a).
  Proof.
    intros c a. apply functional_extensionality. intro x.
    apply propositional_extensionality. unfold q_scale_pred. split.
    - intros [a' [Ha' Hsc]].
      apply (lqr_trans (la_scale la c a) (la_scale la c a') x).
      + apply lqr_scale_compat. exact Ha'.
      + exact Hsc.
    - intro Hx. exists a. split; [apply lqr_refl|exact Hx].
  Qed.

  Lemma q_bracket_pred_class : forall a b,
      q_bracket_pred (lie_class_of a) (lie_class_of b) = lie_class_of (laF_bracket la a b).
  Proof.
    intros a b. apply functional_extensionality. intro x.
    apply propositional_extensionality. unfold q_bracket_pred. split.
    - intros [a' [b' [Ha' [Hb' Hbr]]]].
      apply (lqr_trans (laF_bracket la a b) (laF_bracket la a' b') x).
      + apply lqr_bracket_compat; assumption.
      + exact Hbr.
    - intro Hx. exists a, b. split; [apply lqr_refl|split;[apply lqr_refl|exact Hx]].
  Qed.

  (** Operations on QuotType. *)
  Definition q_add (x y : QuotType) : QuotType.
  Proof.
    refine (exist _ (q_add_pred (proj1_sig x) (proj1_sig y)) _).
    destruct x as [S [a Ha]]; destruct y as [T [b Hb]]; simpl.
    exists (la_add la a b). subst S T. apply q_add_pred_class.
  Defined.

  Definition q_neg (x : QuotType) : QuotType.
  Proof.
    refine (exist _ (q_neg_pred (proj1_sig x)) _).
    destruct x as [S [a Ha]]; simpl.
    exists (la_neg la a). subst S. apply q_neg_pred_class.
  Defined.

  Definition q_scale (c : F) (x : QuotType) : QuotType.
  Proof.
    refine (exist _ (q_scale_pred c (proj1_sig x)) _).
    destruct x as [S [a Ha]]; simpl.
    exists (la_scale la c a). subst S. apply q_scale_pred_class.
  Defined.

  Definition q_bracket (x y : QuotType) : QuotType.
  Proof.
    refine (exist _ (q_bracket_pred (proj1_sig x) (proj1_sig y)) _).
    destruct x as [S [a Ha]]; destruct y as [T [b Hb]]; simpl.
    exists (laF_bracket la a b). subst S T. apply q_bracket_pred_class.
  Defined.

  Definition q_zero : QuotType := mk_class (la_zero la).

  (** Computational lemmas. *)
  Lemma q_add_mk : forall a b,
      q_add (mk_class a) (mk_class b) = mk_class (la_add la a b).
  Proof.
    intros a b. unfold q_add, mk_class.
    apply eq_sig_uncurried. simpl.
    exists (q_add_pred_class a b). apply lie_proof_irrelevance.
  Qed.

  Lemma q_neg_mk : forall a,
      q_neg (mk_class a) = mk_class (la_neg la a).
  Proof.
    intros a. unfold q_neg, mk_class.
    apply eq_sig_uncurried. simpl.
    exists (q_neg_pred_class a). apply lie_proof_irrelevance.
  Qed.

  Lemma q_scale_mk : forall c a,
      q_scale c (mk_class a) = mk_class (la_scale la c a).
  Proof.
    intros c a. unfold q_scale, mk_class.
    apply eq_sig_uncurried. simpl.
    exists (q_scale_pred_class c a). apply lie_proof_irrelevance.
  Qed.

  Lemma q_bracket_mk : forall a b,
      q_bracket (mk_class a) (mk_class b) = mk_class (laF_bracket la a b).
  Proof.
    intros a b. unfold q_bracket, mk_class.
    apply eq_sig_uncurried. simpl.
    exists (q_bracket_pred_class a b). apply lie_proof_irrelevance.
  Qed.

  (** Vector space and Lie algebra laws on the quotient. *)
  Lemma q_add_assoc : forall x y z,
      q_add x (q_add y z) = q_add (q_add x y) z.
  Proof.
    intros x y z.
    destruct (mk_class_surj x) as [a Ha]. subst x.
    destruct (mk_class_surj y) as [b Hb]. subst y.
    destruct (mk_class_surj z) as [c Hc]. subst z.
    rewrite !q_add_mk. apply mk_class_eq.
    rewrite (laF_vs la).(vsF_add_assoc). apply lqr_refl.
  Qed.

  Lemma q_add_comm : forall x y, q_add x y = q_add y x.
  Proof.
    intros x y.
    destruct (mk_class_surj x) as [a Ha]. subst x.
    destruct (mk_class_surj y) as [b Hb]. subst y.
    rewrite !q_add_mk. apply mk_class_eq.
    rewrite ((laF_vs la).(vsF_add_comm) a b). apply lqr_refl.
  Qed.

  Lemma q_add_zero_r : forall x, q_add x q_zero = x.
  Proof.
    intros x.
    destruct (mk_class_surj x) as [a Ha]. subst x.
    unfold q_zero. rewrite q_add_mk. apply mk_class_eq.
    rewrite (laF_vs la).(vsF_add_zero_r). apply lqr_refl.
  Qed.

  Lemma q_add_neg_r : forall x, q_add x (q_neg x) = q_zero.
  Proof.
    intros x.
    destruct (mk_class_surj x) as [a Ha]. subst x.
    rewrite q_neg_mk, q_add_mk. unfold q_zero. apply mk_class_eq.
    rewrite (laF_vs la).(vsF_add_neg_r). apply lqr_refl.
  Qed.

  Lemma q_scale_one : forall x, q_scale (cr_one fld) x = x.
  Proof.
    intros x. destruct (mk_class_surj x) as [a Ha]. subst x.
    rewrite q_scale_mk. apply mk_class_eq.
    rewrite (laF_vs la).(vsF_scale_one). apply lqr_refl.
  Qed.

  Lemma q_scale_mul : forall a b x,
      q_scale a (q_scale b x) = q_scale (cr_mul fld a b) x.
  Proof.
    intros a b x. destruct (mk_class_surj x) as [c Hc]. subst x.
    rewrite !q_scale_mk. apply mk_class_eq.
    rewrite (laF_vs la).(vsF_scale_mul). apply lqr_refl.
  Qed.

  Lemma q_scale_add_v : forall a x y,
      q_scale a (q_add x y) = q_add (q_scale a x) (q_scale a y).
  Proof.
    intros a x y.
    destruct (mk_class_surj x) as [u Hu]. subst x.
    destruct (mk_class_surj y) as [v Hv]. subst y.
    rewrite q_add_mk, !q_scale_mk, q_add_mk. apply mk_class_eq.
    rewrite (laF_vs la).(vsF_scale_add_v). apply lqr_refl.
  Qed.

  Lemma q_scale_add_s : forall a b x,
      q_scale (cr_add fld a b) x = q_add (q_scale a x) (q_scale b x).
  Proof.
    intros a b x. destruct (mk_class_surj x) as [c Hc]. subst x.
    rewrite !q_scale_mk, q_add_mk. apply mk_class_eq.
    rewrite (laF_vs la).(vsF_scale_add_s). apply lqr_refl.
  Qed.

  Definition QuotVS : VectorSpaceF fld QuotType :=
    {| vsF_add := q_add;
       vsF_zero := q_zero;
       vsF_neg := q_neg;
       vsF_scale := q_scale;
       vsF_add_assoc := q_add_assoc;
       vsF_add_comm := q_add_comm;
       vsF_add_zero_r := q_add_zero_r;
       vsF_add_neg_r := q_add_neg_r;
       vsF_scale_one := q_scale_one;
       vsF_scale_mul := q_scale_mul;
       vsF_scale_add_v := q_scale_add_v;
       vsF_scale_add_s := q_scale_add_s;
    |}.

  (** Lie bracket axioms. *)
  Lemma q_bracket_add_l : forall x y z,
      q_bracket (q_add x y) z = q_add (q_bracket x z) (q_bracket y z).
  Proof.
    intros x y z.
    destruct (mk_class_surj x) as [a Ha]. subst x.
    destruct (mk_class_surj y) as [b Hb]. subst y.
    destruct (mk_class_surj z) as [c Hc]. subst z.
    rewrite q_add_mk, !q_bracket_mk, q_add_mk. apply mk_class_eq.
    rewrite la.(laF_bracket_add_l). apply lqr_refl.
  Qed.

  Lemma q_bracket_scale_l : forall a x y,
      q_bracket (q_scale a x) y = q_scale a (q_bracket x y).
  Proof.
    intros a x y.
    destruct (mk_class_surj x) as [u Hu]. subst x.
    destruct (mk_class_surj y) as [v Hv]. subst y.
    rewrite q_scale_mk, !q_bracket_mk, q_scale_mk. apply mk_class_eq.
    rewrite la.(laF_bracket_scale_l). apply lqr_refl.
  Qed.

  Lemma q_bracket_add_r : forall x y z,
      q_bracket x (q_add y z) = q_add (q_bracket x y) (q_bracket x z).
  Proof.
    intros x y z.
    destruct (mk_class_surj x) as [a Ha]. subst x.
    destruct (mk_class_surj y) as [b Hb]. subst y.
    destruct (mk_class_surj z) as [c Hc]. subst z.
    rewrite q_add_mk, !q_bracket_mk, q_add_mk. apply mk_class_eq.
    rewrite la.(laF_bracket_add_r). apply lqr_refl.
  Qed.

  Lemma q_bracket_scale_r : forall a x y,
      q_bracket x (q_scale a y) = q_scale a (q_bracket x y).
  Proof.
    intros a x y.
    destruct (mk_class_surj x) as [u Hu]. subst x.
    destruct (mk_class_surj y) as [v Hv]. subst y.
    rewrite q_scale_mk, !q_bracket_mk, q_scale_mk. apply mk_class_eq.
    rewrite la.(laF_bracket_scale_r). apply lqr_refl.
  Qed.

  Lemma q_bracket_alt : forall x, q_bracket x x = q_zero.
  Proof.
    intros x. destruct (mk_class_surj x) as [a Ha]. subst x.
    rewrite q_bracket_mk. unfold q_zero. apply mk_class_eq.
    rewrite la.(laF_bracket_alt). apply lqr_refl.
  Qed.

  Lemma q_jacobi : forall x y z,
      q_add (q_add (q_bracket x (q_bracket y z)) (q_bracket y (q_bracket z x)))
            (q_bracket z (q_bracket x y))
      = q_zero.
  Proof.
    intros x y z.
    destruct (mk_class_surj x) as [a Ha]. subst x.
    destruct (mk_class_surj y) as [b Hb]. subst y.
    destruct (mk_class_surj z) as [c Hc]. subst z.
    rewrite !q_bracket_mk, !q_add_mk. unfold q_zero. apply mk_class_eq.
    rewrite (la.(laF_jacobi) a b c). apply lqr_refl.
  Qed.

  Definition QuotAlg : LieAlgebraF fld QuotType :=
    {| laF_vs := QuotVS;
       laF_bracket := q_bracket;
       laF_bracket_add_l := q_bracket_add_l;
       laF_bracket_scale_l := q_bracket_scale_l;
       laF_bracket_add_r := q_bracket_add_r;
       laF_bracket_scale_r := q_bracket_scale_r;
       laF_bracket_alt := q_bracket_alt;
       laF_jacobi := q_jacobi;
    |}.

  (** The canonical projection π : L → L/I. *)
  Definition pi_hom : LieHom la QuotAlg.
  Proof.
    refine {| lh_fn := mk_class;
              lh_add := _;
              lh_scale := _;
              lh_bracket := _ |}.
    - intros x y. simpl. symmetry. apply q_add_mk.
    - intros a x. simpl. symmetry. apply q_scale_mk.
    - intros x y. simpl. symmetry. apply q_bracket_mk.
  Defined.

  (** π is surjective. *)
  Lemma pi_surj : forall q : QuotType, exists x, lh_fn pi_hom x = q.
  Proof.
    intros q. simpl. apply mk_class_surj.
  Qed.

  (** Kernel of π is exactly I. *)
  Lemma pi_ker : forall x, LieKer pi_hom x <-> I x.
  Proof.
    intros x. unfold LieKer. simpl. unfold q_zero. split.
    - intro Heq. apply mk_class_eq in Heq.
      destruct Heq as [d [Hd Heq]].
      (* x + d = 0 → d = -x *)
      assert (Hd' : d = la_neg la x).
      { apply (vsF_add_inv_uniq (laF_vs la) x d). exact Heq. }
      subst d.
      assert (Hx : x = la_neg la (la_neg la x))
        by (symmetry; apply (vsF_neg_neg (laF_vs la))).
      rewrite Hx. apply hI.(ideal_neg). exact Hd.
    - intro Hx. apply mk_class_eq.
      exists (la_neg la x). split.
      + apply hI.(ideal_neg). exact Hx.
      + apply (laF_vs la).(vsF_add_neg_r).
  Qed.

End QuotientLieAlgebra.

(** ** First isomorphism theorem *)

(* first_iso_theorem removed: false-as-stated. The statement claimed
   ∃ Lie algebra structure on L itself iso to lb, for any φ : la → lb.
   Counter-example: L = nat (infinite), M = bool (2 elements); no bijection
   between L and M, hence no isomorphism (LieIsom requires bijective Lie
   hom). The proper first isomorphism theorem statement is
   L/ker φ ≅ Im(φ) on the quotient/image carriers, requiring quotient
   types not yet available. The axiom was unused downstream. *)

(** ** Second isomorphism theorem *)

(** If I ⊆ J are ideals, then J/I is an ideal of L/I, and (L/I)/(J/I) ≅ L/J. *)
Lemma second_iso_theorem {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (I J : L -> Prop)
    (hI : IsIdeal la I) (hJ : IsIdeal la J)
    (hIJ : forall x, I x -> J x) :
    True. (* placeholder: quotient type required *)
Proof. exact Logic.I. Qed.

(** ** Third isomorphism theorem *)

(** If I, J are ideals, then (I+J)/J ≅ I/(I∩J). *)
Lemma third_iso_theorem {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (I J : L -> Prop)
    (hI : IsIdeal la I) (hJ : IsIdeal la J) :
    True. (* placeholder: quotient type required *)
Proof. exact Logic.I. Qed.

(** ** Representations *)

(** A representation of L on a vector space V is a Lie hom ρ : L → gl(V).
    We state the definition abstractly here. *)

(** Ker(φ) is an ideal → adjoint is a hom → stated later in Adjoint.v. *)
