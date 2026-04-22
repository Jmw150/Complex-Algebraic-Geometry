(** * Lie/Ideals.v
    Ideals, center, derived algebra, normalizers, centralizers. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.

(** ** Ideals *)

(** A subspace I of L is an ideal if [x,y] ∈ I for all x ∈ L, y ∈ I. *)
Record IsIdeal {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (I : L -> Prop) : Prop := {
  ideal_zero    : I (la_zero la);
  ideal_add     : forall x y, I x -> I y -> I (la_add la x y);
  ideal_neg     : forall x, I x -> I (la_neg la x);
  ideal_scale   : forall a x, I x -> I (la_scale la a x);
  ideal_bracket_l : forall x y, I y -> I (laF_bracket la x y);
}.

Arguments ideal_zero      {F fld L la I}.
Arguments ideal_add       {F fld L la I}.
Arguments ideal_neg       {F fld L la I}.
Arguments ideal_scale     {F fld L la I}.
Arguments ideal_bracket_l {F fld L la I}.

(** Every ideal is a subalgebra. *)
Lemma ideal_is_subalgebra {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (I : L -> Prop) :
    IsIdeal la I -> IsSubalgebra la I.
Proof.
  intro HI. constructor.
  - apply HI.(ideal_zero).
  - apply HI.(ideal_add).
  - apply HI.(ideal_neg).
  - apply HI.(ideal_scale).
  - intros x y _ Hy. apply HI.(ideal_bracket_l). exact Hy.
Qed.

(** 0 is an ideal. *)
Lemma zero_ideal {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) : IsIdeal la (fun x => x = la_zero la).
Proof.
  constructor.
  - reflexivity.
  - intros x y Hx Hy. rewrite Hx, Hy. apply (laF_vs la).(vsF_add_zero_r).
  - intros x Hx. rewrite Hx. apply vsF_neg_zero.
  - intros a x Hx. rewrite Hx. apply vsF_scale_zero_v.
  - intros x y Hy. rewrite Hy. apply laF_bracket_zero_r.
Qed.

(** L is an ideal of itself. *)
Lemma full_ideal {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) : IsIdeal la (fun _ => True).
Proof. constructor; intros; exact I. Qed.

(** Intersection of two ideals is an ideal. *)
Lemma inter_ideal {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (I J : L -> Prop) :
    IsIdeal la I -> IsIdeal la J -> IsIdeal la (fun x => I x /\ J x).
Proof.
  intros HI HJ. constructor.
  - split; [apply HI.(ideal_zero) | apply HJ.(ideal_zero)].
  - intros x y [Hix Hjx] [Hiy Hjy]. split.
    + apply HI.(ideal_add); assumption.
    + apply HJ.(ideal_add); assumption.
  - intros x [Hix Hjx]. split.
    + apply HI.(ideal_neg); assumption.
    + apply HJ.(ideal_neg); assumption.
  - intros a x [Hix Hjx]. split.
    + apply HI.(ideal_scale); assumption.
    + apply HJ.(ideal_scale); assumption.
  - intros x y [Hiy Hjy]. split.
    + apply HI.(ideal_bracket_l); assumption.
    + apply HJ.(ideal_bracket_l); assumption.
Qed.

(** ** Center *)

(** The center Z(L) = { z | [x,z] = 0 for all x }. *)
Definition IsCenter {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (z : L) : Prop :=
  forall x, laF_bracket la x z = la_zero la.

(** The center is an ideal. *)
Lemma center_is_ideal {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) : IsIdeal la (IsCenter la).
Proof.
  unfold IsCenter. constructor.
  - intro x. apply laF_bracket_zero_r.
  - intros u v Hu Hv x.
    rewrite la.(laF_bracket_add_r).
    rewrite (Hu x), (Hv x).
    apply (laF_vs la).(vsF_add_zero_r).
  - intros u Hu x.
    rewrite laF_bracket_neg_r, (Hu x).
    apply vsF_neg_zero.
  - intros a u Hu x.
    rewrite la.(laF_bracket_scale_r), (Hu x).
    apply vsF_scale_zero_v.
  - intros x y Hy w.
    rewrite (Hy x). apply laF_bracket_zero_r.
Qed.

(** L is abelian iff Z(L) = L. *)
Lemma abelian_iff_center_full {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    (forall x y, laF_bracket la x y = la_zero la) <->
    (forall z, IsCenter la z).
Proof.
  unfold IsCenter. split.
  - intros H z x. apply H.
  - intros H x y. apply (H y x).
Qed.

(** ** Derived algebra *)

(** [L,L] is the smallest subspace containing all brackets [x,y]. *)
(** We represent it as the predicate: z ∈ [L,L] iff z is in the span of brackets. *)
Definition IsDerivedAlg {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (z : L) : Prop :=
  forall (S : L -> Prop),
    IsSubalgebra la S ->
    (forall x y, S (laF_bracket la x y)) ->
    S z.

(** [L,L] is an ideal of L. *)
Lemma derived_alg_is_ideal {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) : IsIdeal la (IsDerivedAlg la).
Proof.
  constructor.
  - intros S HS _. apply HS.(sub_zero).
  - intros u v Hu Hv S HS HB.
    apply HS.(sub_add); [apply Hu | apply Hv]; assumption.
  - intros u Hu S HS HB.
    apply HS.(sub_neg); apply Hu; assumption.
  - intros a u Hu S HS HB.
    apply HS.(sub_scale); apply Hu; assumption.
  - intros x y _ S HS HB. apply HB.
Qed.

(** L is abelian iff [L,L] = 0. *)
Lemma abelian_iff_derived_zero {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    (forall x y, laF_bracket la x y = la_zero la) <->
    (forall z, IsDerivedAlg la z -> z = la_zero la).
Proof.
  split.
  - intros Habel z Hz.
    apply Hz.
    + apply zero_is_subalgebra.
    + intros x y. apply Habel.
  - intros H x y.
    apply H. intros S _ HB. apply HB.
Qed.

(** ** Normalizer *)

(** N_L(K) = { x ∈ L | [x,K] ⊆ K }. *)
Definition IsNormalizer {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (K : L -> Prop) (x : L) : Prop :=
  forall y, K y -> K (laF_bracket la x y).

(** The normalizer of K is a subalgebra (uses Jacobi). *)
Lemma normalizer_is_subalgebra {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (K : L -> Prop) :
    IsSubalgebra la K ->
    IsSubalgebra la (IsNormalizer la K).
Proof.
  intro HK. constructor.
  - intros y Hy. rewrite laF_bracket_zero_l. apply HK.(sub_zero).
  - intros x x' HNx HNx' y Hy.
    rewrite la.(laF_bracket_add_l).
    apply HK.(sub_add); [apply HNx | apply HNx']; exact Hy.
  - intros x HNx y Hy.
    rewrite laF_bracket_neg_l. apply HK.(sub_neg). apply HNx. exact Hy.
  - intros a x HNx y Hy.
    rewrite la.(laF_bracket_scale_l). apply HK.(sub_scale). apply HNx. exact Hy.
  - intros x x' HNx HNx' y Hy.
    (* [[x,x'],y] = [x,[x',y]] + [x',[y,x]] by Jacobi + anticomm *)
    assert (HKx'y : K (laF_bracket la x' y)) by (apply HNx'; exact Hy).
    assert (HKxy  : K (laF_bracket la x  y)) by (apply HNx;  exact Hy).
    assert (HKAB  : K (la_add la (laF_bracket la x (laF_bracket la x' y))
                                  (laF_bracket la x' (laF_bracket la y x)))).
    { apply HK.(sub_add).
      - apply HNx. exact HKx'y.
      - apply HNx'. rewrite laF_anticomm. apply HK.(sub_neg). exact HKxy. }
    assert (Hjac : la_add la
                     (la_add la (laF_bracket la x (laF_bracket la x' y))
                                (laF_bracket la x' (laF_bracket la y x)))
                     (laF_bracket la y (laF_bracket la x x')) = la_zero la)
      by exact (la.(laF_jacobi) x x' y).
    (* A + B = -C, i.e. [[x,x'],y] = A+B *)
    assert (eq : la_add la (laF_bracket la x (laF_bracket la x' y))
                            (laF_bracket la x' (laF_bracket la y x))
               = la_neg la (laF_bracket la y (laF_bracket la x x'))).
    { rewrite <- (vsF_add_zero_r (laF_vs la) _).
      rewrite <- (vsF_add_neg_r (laF_vs la) (laF_bracket la y (laF_bracket la x x'))).
      rewrite (laF_vs la).(vsF_add_assoc).
      rewrite Hjac. apply vsF_add_zero_l. }
    rewrite laF_anticomm. rewrite <- eq. exact HKAB.
Qed.

(** K is an ideal of its normalizer. *)
Lemma ideal_of_normalizer {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (K : L -> Prop) :
    IsSubalgebra la K ->
    forall x, IsNormalizer la K x -> forall y, K y -> K (laF_bracket la x y).
Proof. intros _ x Hx y Hy. apply Hx. exact Hy. Qed.

(** ** Centralizer *)

(** C_L(X) = { x ∈ L | [x,y]=0 for all y ∈ X }. *)
Definition IsCentralizer {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (X : L -> Prop) (x : L) : Prop :=
  forall y, X y -> laF_bracket la x y = la_zero la.

(** The centralizer of X is a subalgebra (uses Jacobi). *)
Lemma centralizer_is_subalgebra {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (X : L -> Prop) :
    IsSubalgebra la (IsCentralizer la X).
Proof.
  unfold IsCentralizer. constructor.
  - intros y _. apply laF_bracket_zero_l.
  - intros u v Hu Hv y Hy.
    rewrite la.(laF_bracket_add_l), (Hu y Hy), (Hv y Hy).
    apply (laF_vs la).(vsF_add_zero_r).
  - intros u Hu y Hy.
    rewrite laF_bracket_neg_l, (Hu y Hy). apply vsF_neg_zero.
  - intros a u Hu y Hy.
    rewrite la.(laF_bracket_scale_l), (Hu y Hy). apply vsF_scale_zero_v.
  - intros x x' Hx Hx' y Hy.
    (* [[x,x'],y] = 0 via Jacobi: [x,[x',y]] + [x',[y,x]] + [y,[x,x']] = 0 *)
    (* and all three summands are 0 *)
    assert (Hx'y : laF_bracket la x' y = la_zero la) by (apply Hx'; exact Hy).
    assert (Hxy  : laF_bracket la x  y = la_zero la) by (apply Hx;  exact Hy).
    assert (Hyx  : laF_bracket la y x = la_zero la).
    { rewrite laF_anticomm, Hxy. apply vsF_neg_zero. }
    assert (Hjac := la.(laF_jacobi) x x' y).
    rewrite Hx'y, laF_bracket_zero_r in Hjac.
    rewrite Hyx,  laF_bracket_zero_r in Hjac.
    rewrite (laF_vs la).(vsF_add_zero_r), vsF_add_zero_l in Hjac.
    rewrite laF_anticomm, Hjac. apply vsF_neg_zero.
Qed.

(** C_L(L) = Z(L). *)
Lemma centralizer_full_is_center {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    forall x, IsCentralizer la (fun _ => True) x <-> IsCenter la x.
Proof.
  intro x. unfold IsCentralizer, IsCenter. split.
  - intros H y. rewrite (laF_anticomm la y x), (H y I). apply vsF_neg_zero.
  - intros H y _. rewrite (laF_anticomm la x y), (H y). apply vsF_neg_zero.
Qed.

(** ** Simple Lie algebras *)

Definition IsSimple {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) : Prop :=
  (* Only ideals are 0 and L *)
  (forall I : L -> Prop, IsIdeal la I ->
    (forall x, I x -> x = la_zero la) \/
    (forall x, I x)) /\
  (* [L,L] ≠ 0 *)
  ~ (forall x y, laF_bracket la x y = la_zero la).

(** If L is simple, then Z(L) = 0. *)
Lemma simple_center_zero {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    IsSimple la ->
    forall z, IsCenter la z -> z = la_zero la.
Proof.
  intros [Hideal Hnonab] z Hz.
  destruct (Hideal (IsCenter la) (center_is_ideal la)) as [H0 | Hall].
  - apply H0. exact Hz.
  - exfalso. apply Hnonab. intros x y. apply (Hall y x).
Qed.

(** If L is simple, then [L,L] = L. *)
Lemma simple_derived_full {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    IsSimple la ->
    forall z, IsDerivedAlg la z.
Proof.
  intros [Hideal Hnonab] z.
  destruct (Hideal (IsDerivedAlg la) (derived_alg_is_ideal la)) as [H0 | Hall].
  - exfalso. apply Hnonab. intros x y.
    apply H0. intros S _ HB. apply HB.
  - apply Hall.
Qed.
