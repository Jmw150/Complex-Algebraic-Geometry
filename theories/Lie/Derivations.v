(** * Lie/Derivations.v
    Derivations of algebras, Der(A), inner derivations, adjoint representation. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.Lie.Ideals.
Require Import CAG.Lie.Linear.

(** ** Derivations of an F-algebra *)

(** An F-algebra A is a vector space with an associative multiplication. *)
Record FAlgebra {F : Type} (fld : Field F) (A : Type) : Type := {
  fa_vs     :> VectorSpaceF fld A;
  fa_mul    : A -> A -> A;
  fa_mul_assoc : forall x y z,
    fa_mul x (fa_mul y z) = fa_mul (fa_mul x y) z;
  fa_mul_add_l : forall x y z,
    fa_mul x (fa_vs.(vsF_add) y z) =
    fa_vs.(vsF_add) (fa_mul x y) (fa_mul x z);
  fa_mul_add_r : forall x y z,
    fa_mul (fa_vs.(vsF_add) x y) z =
    fa_vs.(vsF_add) (fa_mul x z) (fa_mul y z);
}.

Arguments fa_mul      {F fld A} _ _ _.
Arguments fa_vs       {F fld A} _.
Arguments fa_mul_add_l {F fld A} _ _ _ _.
Arguments fa_mul_add_r {F fld A} _ _ _ _.
Arguments fa_mul_assoc {F fld A} _ _ _ _.

(** A derivation of A is a linear map δ : A → A satisfying δ(ab) = aδ(b) + δ(a)b. *)
Record IsDerivation {F : Type} {fld : Field F} {A : Type}
    (alg : FAlgebra fld A) (δ : A -> A) : Prop := {
  deriv_add   : forall x y,
    δ (alg.(fa_vs).(vsF_add) x y) =
    alg.(fa_vs).(vsF_add) (δ x) (δ y);
  deriv_scale : forall a x,
    δ (alg.(fa_vs).(vsF_scale) a x) =
    alg.(fa_vs).(vsF_scale) a (δ x);
  deriv_leibniz : forall x y,
    δ (fa_mul alg x y) =
    alg.(fa_vs).(vsF_add)
      (fa_mul alg x (δ y))
      (fa_mul alg (δ x) y);
}.

Arguments deriv_add     {F fld A alg δ}.
Arguments deriv_scale   {F fld A alg δ}.
Arguments deriv_leibniz {F fld A alg δ}.

(** Der(A) = set of all derivations of A. *)
Definition IsDer {F : Type} {fld : Field F} {A : Type}
    (alg : FAlgebra fld A) (δ : A -> A) : Prop :=
  IsDerivation alg δ.

(** Der(A) is a vector subspace of End(A). *)
Lemma der_is_subspace {F : Type} {fld : Field F} {A : Type}
    (alg : FAlgebra fld A) :
    (forall δ₁ δ₂, IsDerivation alg δ₁ -> IsDerivation alg δ₂ ->
      IsDerivation alg (fun x => alg.(fa_vs).(vsF_add) (δ₁ x) (δ₂ x))) /\
    (forall a δ, IsDerivation alg δ ->
      IsDerivation alg (fun x => alg.(fa_vs).(vsF_scale) a (δ x))).
Proof. Admitted.

(** Commutator of derivations is a derivation. *)
Lemma der_commutator_is_der {F : Type} {fld : Field F} {A : Type}
    (alg : FAlgebra fld A) (δ₁ δ₂ : A -> A) :
    IsDerivation alg δ₁ -> IsDerivation alg δ₂ ->
    IsDerivation alg (fun x =>
      alg.(fa_vs).(vsF_add)
        (δ₁ (δ₂ x))
        (alg.(fa_vs).(vsF_neg) (δ₂ (δ₁ x)))).
Proof.
  intros Hd1 Hd2.
  set (vs := alg.(fa_vs)).
  set (mul := fa_mul alg).

  (** Helper: uniqueness of additive inverse. *)
  assert (inv_uniq : forall u v : A,
      vsF_add vs u v = vsF_zero vs -> v = vsF_neg vs u).
  { intros u v H.
    assert (K : vsF_add vs (vsF_neg vs u) (vsF_add vs u v) = vsF_neg vs u).
    { rewrite H. apply vs.(vsF_add_zero_r). }
    rewrite vs.(vsF_add_assoc) in K.
    rewrite (vs.(vsF_add_comm) (vsF_neg vs u) u) in K.
    rewrite vs.(vsF_add_neg_r) in K.
    rewrite vsF_add_zero_l in K. exact K. }

  (** Helper: neg distributes over add. *)
  assert (neg_add : forall u v : A,
      vsF_neg vs (vsF_add vs u v) = vsF_add vs (vsF_neg vs u) (vsF_neg vs v)).
  { intros u v. symmetry. apply inv_uniq.
    rewrite <- vs.(vsF_add_assoc).
    rewrite (vs.(vsF_add_assoc) v (vsF_neg vs u) (vsF_neg vs v)).
    rewrite (vs.(vsF_add_comm) v (vsF_neg vs u)).
    rewrite <- (vs.(vsF_add_assoc) (vsF_neg vs u) v (vsF_neg vs v)).
    rewrite vs.(vsF_add_neg_r). rewrite vs.(vsF_add_zero_r).
    apply vs.(vsF_add_neg_r). }

  (** Helper: neg commutes with scale. *)
  assert (neg_scale : forall a (v : A),
      vsF_neg vs (vsF_scale vs a v) = vsF_scale vs a (vsF_neg vs v)).
  { intros a v. symmetry. apply inv_uniq.
    rewrite <- vs.(vsF_scale_add_v), vs.(vsF_add_neg_r).
    apply vsF_scale_zero_v. }

  (** Helper: mul x 0 = 0. *)
  assert (mul_zero_r : forall (x : A), mul x (vsF_zero vs) = vsF_zero vs).
  { intro x. apply vsF_add_cancel_double.
    rewrite <- alg.(fa_mul_add_l), vs.(vsF_add_zero_r). reflexivity. }

  (** Helper: mul 0 y = 0. *)
  assert (mul_zero_l : forall (y : A), mul (vsF_zero vs) y = vsF_zero vs).
  { intro y. apply vsF_add_cancel_double.
    rewrite <- alg.(fa_mul_add_r), vs.(vsF_add_zero_r). reflexivity. }

  (** Helper: mul x (neg v) = neg (mul x v). *)
  assert (mul_neg_r : forall (x v : A),
      mul x (vsF_neg vs v) = vsF_neg vs (mul x v)).
  { intros x v. apply inv_uniq.
    rewrite <- alg.(fa_mul_add_l), vs.(vsF_add_neg_r).
    apply mul_zero_r. }

  (** Helper: mul (neg u) y = neg (mul u y). *)
  assert (mul_neg_l : forall (u y : A),
      mul (vsF_neg vs u) y = vsF_neg vs (mul u y)).
  { intros u y. apply inv_uniq.
    rewrite <- alg.(fa_mul_add_r), vs.(vsF_add_neg_r).
    apply mul_zero_l. }

  (** Helper: (a+b)+(c+d) = (a+c)+(b+d). *)
  assert (add4 : forall a b c d : A,
      vsF_add vs (vsF_add vs a b) (vsF_add vs c d) =
      vsF_add vs (vsF_add vs a c) (vsF_add vs b d)).
  { intros a b c d.
    rewrite <- vs.(vsF_add_assoc).
    rewrite (vs.(vsF_add_assoc) b c d).
    rewrite (vs.(vsF_add_comm) b c).
    rewrite <- (vs.(vsF_add_assoc) c b d).
    apply vs.(vsF_add_assoc). }

  constructor.

  (** ── deriv_add ──────────────────────────────────────────────── *)
  - intros x y. simpl.
    rewrite (Hd2.(deriv_add) x y).
    rewrite (Hd1.(deriv_add) (δ₂ x) (δ₂ y)).
    rewrite (Hd1.(deriv_add) x y).
    rewrite (Hd2.(deriv_add) (δ₁ x) (δ₁ y)).
    rewrite (neg_add (δ₂ (δ₁ x)) (δ₂ (δ₁ y))).
    apply add4.

  (** ── deriv_scale ────────────────────────────────────────────── *)
  - intros a x. simpl.
    rewrite (Hd2.(deriv_scale) a x).
    rewrite (Hd1.(deriv_scale) a (δ₂ x)).
    rewrite (Hd1.(deriv_scale) a x).
    rewrite (Hd2.(deriv_scale) a (δ₁ x)).
    rewrite (neg_scale a (δ₂ (δ₁ x))).
    symmetry. apply vs.(vsF_scale_add_v).

  (** ── deriv_leibniz ──────────────────────────────────────────── *)
  - intros x y. simpl.
    (** Expand δ₁(δ₂(x·y)) *)
    assert (H1 : δ₁ (δ₂ (mul x y)) =
                 vsF_add vs (vsF_add vs (mul x (δ₁ (δ₂ y))) (mul (δ₁ x) (δ₂ y)))
                            (vsF_add vs (mul (δ₂ x) (δ₁ y)) (mul (δ₁ (δ₂ x)) y))).
    { rewrite (Hd2.(deriv_leibniz) x y).
      rewrite (Hd1.(deriv_add) (mul x (δ₂ y)) (mul (δ₂ x) y)).
      rewrite (Hd1.(deriv_leibniz) x (δ₂ y)).
      rewrite (Hd1.(deriv_leibniz) (δ₂ x) y). reflexivity. }
    (** Expand δ₂(δ₁(x·y)) *)
    assert (H2 : δ₂ (δ₁ (mul x y)) =
                 vsF_add vs (vsF_add vs (mul x (δ₂ (δ₁ y))) (mul (δ₂ x) (δ₁ y)))
                            (vsF_add vs (mul (δ₁ x) (δ₂ y)) (mul (δ₂ (δ₁ x)) y))).
    { rewrite (Hd1.(deriv_leibniz) x y).
      rewrite (Hd2.(deriv_add) (mul x (δ₁ y)) (mul (δ₁ x) y)).
      rewrite (Hd2.(deriv_leibniz) x (δ₁ y)).
      rewrite (Hd2.(deriv_leibniz) (δ₁ x) y). reflexivity. }
    rewrite H1, H2.
    (** Expand neg and RHS *)
    rewrite (neg_add (vsF_add vs (mul x (δ₂ (δ₁ y))) (mul (δ₂ x) (δ₁ y))) _).
    rewrite (neg_add (mul x (δ₂ (δ₁ y))) (mul (δ₂ x) (δ₁ y))).
    rewrite (neg_add (mul (δ₁ x) (δ₂ y)) (mul (δ₂ (δ₁ x)) y)).
    rewrite alg.(fa_mul_add_l), alg.(fa_mul_add_r).
    rewrite mul_neg_r, mul_neg_l.
    (** LHS: ((xP + Q) + (S + Ay)) + ((neg(xD) + neg S) + (neg Q + neg(Cy)))
        RHS: (xP + neg(xD)) + (Ay + neg(Cy))
        where Q = mul(δ₁x)(δ₂y), S = mul(δ₂x)(δ₁y) cancel.
        Set: a = mul x (δ₁(δ₂y)), b = mul(δ₁x)(δ₂y), c = mul(δ₂x)(δ₁y), d = mul(δ₁(δ₂x)) y,
             e = neg(mul x (δ₂(δ₁y))), f = neg c, g = neg b, h = neg(mul(δ₂(δ₁x)) y). *)
    set (a_ := mul x (δ₁ (δ₂ y))).
    set (b_ := mul (δ₁ x) (δ₂ y)).
    set (c_ := mul (δ₂ x) (δ₁ y)).
    set (d_ := mul (δ₁ (δ₂ x)) y).
    set (e_ := vsF_neg vs (mul x (δ₂ (δ₁ y)))).
    set (h_ := vsF_neg vs (mul (δ₂ (δ₁ x)) y)).
    (** Goal: ((a_+b_)+(c_+d_)) + ((e_ + neg c_) + (neg b_ + h_))
              = (a_ + e_) + (d_ + h_) *)
    (** Step 1: apply add4 on outer *)
    rewrite (add4 (vsF_add vs a_ b_) (vsF_add vs c_ d_)
                  (vsF_add vs e_ (vsF_neg vs c_))
                  (vsF_add vs (vsF_neg vs b_) h_)).
    (** Step 2: apply add4 on left inner: (a_+b_)+(e_+neg c_) = (a_+e_)+(b_+neg c_) *)
    rewrite (add4 a_ b_ e_ (vsF_neg vs c_)).
    (** Step 3: apply add4 on right inner: (c_+d_)+(neg b_+h_) = (c_+neg b_)+(d_+h_) *)
    rewrite (add4 c_ d_ (vsF_neg vs b_) h_).
    (** Goal: ((a_+e_)+(b_+neg c_)) + ((c_+neg b_)+(d_+h_)) = (a_+e_)+(d_+h_) *)
    (** Step 4: reverse outer assoc: u+v+w → u+(v+w) where u=(a_+e_) *)
    rewrite <- (vs.(vsF_add_assoc) (vsF_add vs a_ e_) _ _).
    (** Goal: (a_+e_) + ((b_+neg c_) + ((c_+neg b_)+(d_+h_))) = (a_+e_)+(d_+h_) *)
    (** Step 5: inner assoc: (b_+neg c_)+((c_+neg b_)+(d_+h_)) = ((b_+neg c_)+(c_+neg b_))+(d_+h_) *)
    rewrite (vs.(vsF_add_assoc) (vsF_add vs b_ (vsF_neg vs c_))
                                (vsF_add vs c_ (vsF_neg vs b_)) _).
    (** Goal: (a_+e_) + (((b_+neg c_)+(c_+neg b_)) + (d_+h_)) = (a_+e_)+(d_+h_) *)
    (** Step 6: show (b_+neg c_)+(c_+neg b_) = 0 *)
    assert (Hcancel : vsF_add vs (vsF_add vs b_ (vsF_neg vs c_))
                                 (vsF_add vs c_ (vsF_neg vs b_))
                    = vsF_zero vs).
    { rewrite <- vs.(vsF_add_assoc).
      rewrite (vs.(vsF_add_assoc) (vsF_neg vs c_) c_ (vsF_neg vs b_)).
      rewrite (vs.(vsF_add_comm) (vsF_neg vs c_) c_).
      rewrite vs.(vsF_add_neg_r).
      rewrite vsF_add_zero_l.
      apply vs.(vsF_add_neg_r). }
    rewrite Hcancel.
    rewrite vsF_add_zero_l.
    apply vs.(vsF_add_assoc).
Qed.

(** Product of derivations need not be a derivation. *)
Lemma der_product_not_der {F : Type} {fld : Field F} {A : Type}
    (alg : FAlgebra fld A) :
    ~ (forall δ₁ δ₂, IsDerivation alg δ₁ -> IsDerivation alg δ₂ ->
       IsDerivation alg (fun x => δ₁ (δ₂ x))).
Proof. Admitted.

(** ** Inner and outer derivations *)

(** An inner derivation is one of the form ad x for some x ∈ L.
    For a general F-algebra A, inner derivations are not defined in the same way,
    but for Lie algebras the definition is: δ is inner if δ = ad x for some x. *)
Definition IsInnerDerivation {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (δ : L -> L) : Prop :=
  exists x : L, forall z : L, δ z = laF_bracket la x z.

(** An outer derivation is a Lie algebra derivation that is not inner. *)
Definition IsOuterDerivation {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (δ : L -> L) : Prop :=
  (forall x y, δ (laF_bracket la x y) =
               la_add la (laF_bracket la (δ x) y) (laF_bracket la x (δ y))) /\
  ~ IsInnerDerivation la δ.

(** ** Adjoint representation *)

(** For a Lie algebra L, ad x : L → L is y ↦ [x, y]. *)
Definition ad {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (x : L) : L -> L :=
  fun y => laF_bracket la x y.

(** ad x is a derivation of the Lie algebra (viewed as an F-algebra via bracket). *)
(** This is a direct reformulation of Jacobi. *)
Lemma ad_is_derivation {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (x : L) :
    (** For all y z: ad x [y,z] = [y, ad x z] + [ad x y, z] *)
    forall y z,
      laF_bracket la x (laF_bracket la y z) =
      la_add la
        (laF_bracket la y (laF_bracket la x z))
        (laF_bracket la (laF_bracket la x y) z).
Proof.
  intros y z.
  (* From Jacobi: (P + (-Q)) + (-R) = 0, where P = [x,[y,z]], Q = [y,[x,z]], R = [[x,y],z] *)
  assert (Hjac := la.(laF_jacobi) x y z).
  (* Rewrite [y,[z,x]] = -[y,[x,z]] *)
  assert (H1 : laF_bracket la y (laF_bracket la z x) =
               la_neg la (laF_bracket la y (laF_bracket la x z))).
  { rewrite (laF_anticomm la z x). apply laF_bracket_neg_r. }
  (* Rewrite [z,[x,y]] = -[[x,y],z] *)
  assert (H2 : laF_bracket la z (laF_bracket la x y) =
               la_neg la (laF_bracket la (laF_bracket la x y) z)).
  { apply laF_anticomm. }
  rewrite H1, H2 in Hjac.
  (* Hjac : (P + (-Q)) + (-R) = 0 *)
  (* Step 1: P + (-Q) = R (from (P+(-Q))+(-R) = 0 by adding R) *)
  assert (HnegR_R : la_add la (la_neg la (laF_bracket la (laF_bracket la x y) z))
                               (laF_bracket la (laF_bracket la x y) z) = la_zero la).
  { rewrite (laF_vs la).(vsF_add_comm). apply (laF_vs la).(vsF_add_neg_r). }
  assert (HeqPQ_R : la_add la (laF_bracket la x (laF_bracket la y z))
                               (la_neg la (laF_bracket la y (laF_bracket la x z)))
                  = laF_bracket la (laF_bracket la x y) z).
  { rewrite <- (vsF_add_zero_r (laF_vs la) _).
    rewrite <- HnegR_R.
    rewrite (laF_vs la).(vsF_add_assoc).
    rewrite Hjac. apply vsF_add_zero_l. }
  (* Step 2: P = Q + R (from P + (-Q) = R by adding Q) *)
  assert (HnegQ_Q : la_add la (la_neg la (laF_bracket la y (laF_bracket la x z)))
                               (laF_bracket la y (laF_bracket la x z)) = la_zero la).
  { rewrite (laF_vs la).(vsF_add_comm). apply (laF_vs la).(vsF_add_neg_r). }
  rewrite <- (vsF_add_zero_r (laF_vs la) (laF_bracket la x (laF_bracket la y z))).
  rewrite <- HnegQ_Q.
  rewrite (laF_vs la).(vsF_add_assoc).
  rewrite HeqPQ_R.
  apply (laF_vs la).(vsF_add_comm).
Qed.

(** ad is linear: ad(ax+by) = a·ad(x) + b·ad(y). *)
Lemma ad_linear {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (a : F) (x y : L) :
    forall z,
      ad la (la_add la (la_scale la a x) y) z =
      la_add la (la_scale la a (ad la x z)) (ad la y z).
Proof.
  intro z. unfold ad.
  rewrite la.(laF_bracket_add_l).
  rewrite la.(laF_bracket_scale_l).
  reflexivity.
Qed.

(** ad is a Lie algebra homomorphism: ad[x,y] = [ad x, ad y]. *)
Lemma ad_hom {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (x y z : L) :
    ad la (laF_bracket la x y) z =
    la_add la
      (ad la x (ad la y z))
      (la_neg la (ad la y (ad la x z))).
Proof.
  unfold ad.
  (* [[x,y],z] = [x,[y,z]] + (-[y,[x,z]]) from ad_is_derivation *)
  assert (Hder := ad_is_derivation la x y z).
  (* Hder : [x,[y,z]] = [y,[x,z]] + [[x,y],z] *)
  (* We need [[x,y],z] = [x,[y,z]] + (-[y,[x,z]]) *)
  (* From Hder: [[x,y],z] = [x,[y,z]] + (-[y,[x,z]]) *)
  symmetry. rewrite Hder.
  rewrite <- (laF_vs la).(vsF_add_assoc).
  rewrite (vsF_add_comm (laF_vs la) (laF_bracket la (laF_bracket la x y) z) (la_neg la (laF_bracket la y (laF_bracket la x z)))).
  rewrite (laF_vs la).(vsF_add_assoc).
  rewrite (laF_vs la).(vsF_add_neg_r).
  apply vsF_add_zero_l.
Qed.

(** Ker(ad) = Z(L). *)
Lemma ad_ker_is_center {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (x : L) :
    (forall y, ad la x y = la_zero la) <-> IsCenter la x.
Proof.
  unfold ad, IsCenter. split.
  - intros H y. rewrite (laF_anticomm la y x), (H y). apply vsF_neg_zero.
  - intros H y. rewrite (laF_anticomm la x y), (H y). apply vsF_neg_zero.
Qed.

(** If L is simple, then ad : L → gl(L) is injective. *)
Lemma simple_ad_injective {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    IsSimple la ->
    forall x, (forall y, ad la x y = la_zero la) -> x = la_zero la.
Proof.
  intros Hsimp x Hx.
  apply (simple_center_zero la Hsimp).
  apply ad_ker_is_center. exact Hx.
Qed.
