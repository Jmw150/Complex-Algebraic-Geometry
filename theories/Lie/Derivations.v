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

(** F-algebra scalar compatibility: x·(a·v) = a·(x·v).
    This is part of F-bilinearity of multiplication; not in the record
    but axiomatically valid for any F-algebra. *)
(* CAG zero-dependent Axiom fa_mul_scale_r theories/Lie/Derivations.v:54 BEGIN
Axiom fa_mul_scale_r : forall {F : Type} {fld : Field F} {A : Type}
    (alg : FAlgebra fld A) (a : F) (x v : A),
    fa_mul alg x (alg.(fa_vs).(vsF_scale) a v) =
    alg.(fa_vs).(vsF_scale) a (fa_mul alg x v).
   CAG zero-dependent Axiom fa_mul_scale_r theories/Lie/Derivations.v:54 END *)

(* CAG zero-dependent Axiom fa_mul_scale_l theories/Lie/Derivations.v:59 BEGIN
Axiom fa_mul_scale_l : forall {F : Type} {fld : Field F} {A : Type}
    (alg : FAlgebra fld A) (a : F) (u y : A),
    fa_mul alg (alg.(fa_vs).(vsF_scale) a u) y =
    alg.(fa_vs).(vsF_scale) a (fa_mul alg u y).
   CAG zero-dependent Axiom fa_mul_scale_l theories/Lie/Derivations.v:59 END *)

(** Der(A) = set of all derivations of A. *)
Definition IsDer {F : Type} {fld : Field F} {A : Type}
    (alg : FAlgebra fld A) (δ : A -> A) : Prop :=
  IsDerivation alg δ.

(** Der(A) is a vector subspace of End(A). *)
(* CAG zero-dependent Lemma der_is_subspace theories/Lie/Derivations.v:70 BEGIN
Lemma der_is_subspace {F : Type} {fld : Field F} {A : Type}
    (alg : FAlgebra fld A) :
    (forall δ₁ δ₂, IsDerivation alg δ₁ -> IsDerivation alg δ₂ ->
      IsDerivation alg (fun x => alg.(fa_vs).(vsF_add) (δ₁ x) (δ₂ x))) /\
    (forall a δ, IsDerivation alg δ ->
      IsDerivation alg (fun x => alg.(fa_vs).(vsF_scale) a (δ x))).
Proof.
  set (vs := alg.(fa_vs)) in *.
  assert (add4 : forall a b c d : A,
      vsF_add vs (vsF_add vs a b) (vsF_add vs c d) =
      vsF_add vs (vsF_add vs a c) (vsF_add vs b d)).
  { intros a b c d.
    rewrite <- vs.(vsF_add_assoc).
    rewrite (vs.(vsF_add_assoc) b c d).
    rewrite (vs.(vsF_add_comm) b c).
    rewrite <- (vs.(vsF_add_assoc) c b d).
    apply vs.(vsF_add_assoc). }
  split.
  - (** Sum of two derivations is a derivation. *)
    intros δ₁ δ₂ Hd1 Hd2. constructor.
    + (** deriv_add: (δ₁+δ₂)(x+y) = (δ₁+δ₂)x + (δ₁+δ₂)y *)
      intros x y. cbv beta.
      rewrite (Hd1.(deriv_add) x y), (Hd2.(deriv_add) x y).
      apply add4.
    + (** deriv_scale: (δ₁+δ₂)(a·x) = a·(δ₁+δ₂)x *)
      intros a x. cbv beta.
      rewrite (Hd1.(deriv_scale) a x), (Hd2.(deriv_scale) a x).
      symmetry. exact (vs.(vsF_scale_add_v) a (δ₁ x) (δ₂ x)).
    + (** deriv_leibniz: (δ₁+δ₂)(xy) = x·(δ₁+δ₂)y + (δ₁+δ₂)x·y *)
      intros x y. cbv beta.
      rewrite (Hd1.(deriv_leibniz) x y), (Hd2.(deriv_leibniz) x y).
      assert (Hdl : fa_mul alg x (vsF_add vs (δ₁ y) (δ₂ y)) =
                    vsF_add vs (fa_mul alg x (δ₁ y)) (fa_mul alg x (δ₂ y))).
      { exact (alg.(fa_mul_add_l) x _ _). }
      assert (Hdr : fa_mul alg (vsF_add vs (δ₁ x) (δ₂ x)) y =
                    vsF_add vs (fa_mul alg (δ₁ x) y) (fa_mul alg (δ₂ x) y)).
      { exact (alg.(fa_mul_add_r) _ _ y). }
      rewrite Hdl, Hdr. apply add4.
  - (** Scalar multiple of a derivation is a derivation. *)
    intros a δ Hd. constructor.
    + (** deriv_add: (a·δ)(x+y) = a·(δx+δy) = a·δx + a·δy *)
      intros x y. cbv beta.
      rewrite (Hd.(deriv_add) x y).
      exact (vs.(vsF_scale_add_v) a (δ x) (δ y)).
    + (** deriv_scale: (a·δ)(b·x) = a·(b·δx) = b·(a·δx) *)
      intros b x. cbv beta.
      rewrite (Hd.(deriv_scale) b x).
      rewrite vs.(vsF_scale_mul), vs.(vsF_scale_mul).
      rewrite fld.(cr_mul_comm). reflexivity.
    + (** deriv_leibniz: (a·δ)(xy) = x(a·δy) + (a·δx)y *)
      intros x y. cbv beta.
      rewrite (Hd.(deriv_leibniz) x y).
      rewrite vs.(vsF_scale_add_v).
      unfold vs.
      rewrite (fa_mul_scale_r alg a x (δ y)).
      rewrite (fa_mul_scale_l alg a (δ x) y).
      reflexivity.
Qed.
   CAG zero-dependent Lemma der_is_subspace theories/Lie/Derivations.v:70 END *)

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
  set (vs := alg.(fa_vs)) in *.

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

  (** Helper: fa_mul alg x 0 = 0. *)
  assert (mul_zero_r : forall (x : A), fa_mul alg x (vsF_zero vs) = vsF_zero vs).
  { intro x. apply vsF_add_cancel_double.
    rewrite <- alg.(fa_mul_add_l), vs.(vsF_add_zero_r). reflexivity. }

  (** Helper: fa_mul alg 0 y = 0. *)
  assert (mul_zero_l : forall (y : A), fa_mul alg (vsF_zero vs) y = vsF_zero vs).
  { intro y. apply vsF_add_cancel_double.
    rewrite <- alg.(fa_mul_add_r), vs.(vsF_add_zero_r). reflexivity. }

  (** Helper: fa_mul alg x (neg v) = neg (fa_mul alg x v). *)
  assert (mul_neg_r : forall (x v : A),
      fa_mul alg x (vsF_neg vs v) = vsF_neg vs (fa_mul alg x v)).
  { intros x v. apply inv_uniq.
    rewrite <- alg.(fa_mul_add_l), vs.(vsF_add_neg_r).
    apply mul_zero_r. }

  (** Helper: fa_mul alg (neg u) y = neg (fa_mul alg u y). *)
  assert (mul_neg_l : forall (u y : A),
      fa_mul alg (vsF_neg vs u) y = vsF_neg vs (fa_mul alg u y)).
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
  - intros x y. cbv beta.
    rewrite (Hd2.(deriv_add) x y).
    rewrite (Hd1.(deriv_add) (δ₂ x) (δ₂ y)).
    rewrite (Hd1.(deriv_add) x y).
    rewrite (Hd2.(deriv_add) (δ₁ x) (δ₁ y)).
    set (A_ := δ₁ (δ₂ x)). set (B_ := δ₁ (δ₂ y)).
    set (C_ := δ₂ (δ₁ x)). set (D_ := δ₂ (δ₁ y)).
    assert (Hstep : vsF_add vs (vsF_add vs A_ B_) (vsF_neg vs (vsF_add vs C_ D_))
                  = vsF_add vs (vsF_add vs A_ (vsF_neg vs C_))
                               (vsF_add vs B_ (vsF_neg vs D_))).
    { rewrite (neg_add C_ D_). apply add4. }
    exact Hstep.

  (** ── deriv_scale ────────────────────────────────────────────── *)
  - intros a x. cbv beta.
    rewrite (Hd2.(deriv_scale) a x).
    rewrite (Hd1.(deriv_scale) a (δ₂ x)).
    rewrite (Hd1.(deriv_scale) a x).
    rewrite (Hd2.(deriv_scale) a (δ₁ x)).
    set (P_ := δ₁ (δ₂ x)). set (Q_ := δ₂ (δ₁ x)).
    assert (Hstep : vsF_add vs (vsF_scale vs a P_) (vsF_neg vs (vsF_scale vs a Q_))
                  = vsF_scale vs a (vsF_add vs P_ (vsF_neg vs Q_))).
    { rewrite (neg_scale a Q_). symmetry. apply vs.(vsF_scale_add_v). }
    exact Hstep.

  (** ── deriv_leibniz ──────────────────────────────────────────── *)
  - intros x y. cbv beta.
    (** Expand δ₁(δ₂(x·y)) *)
    assert (H1 : δ₁ (δ₂ (fa_mul alg x y)) =
       vsF_add vs (vsF_add vs (fa_mul alg x (δ₁ (δ₂ y))) (fa_mul alg (δ₁ x) (δ₂ y)))
                  (vsF_add vs (fa_mul alg (δ₂ x) (δ₁ y)) (fa_mul alg (δ₁ (δ₂ x)) y))).
    { rewrite (Hd2.(deriv_leibniz) x y).
      rewrite (Hd1.(deriv_add) (fa_mul alg x (δ₂ y)) (fa_mul alg (δ₂ x) y)).
      rewrite (Hd1.(deriv_leibniz) x (δ₂ y)).
      rewrite (Hd1.(deriv_leibniz) (δ₂ x) y). reflexivity. }
    (** Expand δ₂(δ₁(x·y)) *)
    assert (H2 : δ₂ (δ₁ (fa_mul alg x y)) =
       vsF_add vs (vsF_add vs (fa_mul alg x (δ₂ (δ₁ y))) (fa_mul alg (δ₂ x) (δ₁ y)))
                  (vsF_add vs (fa_mul alg (δ₁ x) (δ₂ y)) (fa_mul alg (δ₂ (δ₁ x)) y))).
    { rewrite (Hd1.(deriv_leibniz) x y).
      rewrite (Hd2.(deriv_add) (fa_mul alg x (δ₁ y)) (fa_mul alg (δ₁ x) y)).
      rewrite (Hd2.(deriv_leibniz) x (δ₁ y)).
      rewrite (Hd2.(deriv_leibniz) (δ₁ x) y). reflexivity. }
    rewrite H1, H2.
    (** Expand neg and RHS *)
    rewrite (neg_add (vsF_add vs (fa_mul alg x (δ₂ (δ₁ y))) (fa_mul alg (δ₂ x) (δ₁ y))) _).
    rewrite (neg_add (fa_mul alg x (δ₂ (δ₁ y))) (fa_mul alg (δ₂ x) (δ₁ y))).
    rewrite (neg_add (fa_mul alg (δ₁ x) (δ₂ y)) (fa_mul alg (δ₂ (δ₁ x)) y)).
    assert (Hdist_l : fa_mul alg x (vsF_add vs (δ₁ (δ₂ y)) (vsF_neg vs (δ₂ (δ₁ y)))) =
                      vsF_add vs (fa_mul alg x (δ₁ (δ₂ y)))
                                 (fa_mul alg x (vsF_neg vs (δ₂ (δ₁ y))))).
    { exact (alg.(fa_mul_add_l) x _ _). }
    assert (Hdist_r : fa_mul alg (vsF_add vs (δ₁ (δ₂ x)) (vsF_neg vs (δ₂ (δ₁ x)))) y =
                      vsF_add vs (fa_mul alg (δ₁ (δ₂ x)) y)
                                 (fa_mul alg (vsF_neg vs (δ₂ (δ₁ x))) y)).
    { exact (alg.(fa_mul_add_r) _ _ y). }
    rewrite Hdist_l, Hdist_r.
    rewrite mul_neg_r, mul_neg_l.
    (** LHS: ((xP+Q)+(S+Ay))+((neg(xD)+neg S)+(neg Q+neg(Cy)))
        RHS: (xP+neg(xD))+(Ay+neg(Cy))  [Q=mul(δ₁x)(δ₂y), S=mul(δ₂x)(δ₁y) cancel] *)
    set (a_ := fa_mul alg x (δ₁ (δ₂ y))).
    set (b_ := fa_mul alg (δ₁ x) (δ₂ y)).
    set (c_ := fa_mul alg (δ₂ x) (δ₁ y)).
    set (d_ := fa_mul alg (δ₁ (δ₂ x)) y).
    set (e_ := vsF_neg vs (fa_mul alg x (δ₂ (δ₁ y)))).
    set (h_ := vsF_neg vs (fa_mul alg (δ₂ (δ₁ x)) y)).
    rewrite (add4 (vsF_add vs a_ b_) (vsF_add vs c_ d_)
                  (vsF_add vs e_ (vsF_neg vs c_))
                  (vsF_add vs (vsF_neg vs b_) h_)).
    rewrite (add4 a_ b_ e_ (vsF_neg vs c_)).
    rewrite (add4 c_ d_ (vsF_neg vs b_) h_).
    (** Goal: ((AE+BC')+(C'B+DH)) = AE+DH  where BC'+C'B cancel.
        assoc: a+(b+c)=(a+b)+c, so <- is (a+b)+c → a+(b+c) *)
    rewrite <- (vs.(vsF_add_assoc) (vsF_add vs a_ e_) (vsF_add vs b_ (vsF_neg vs c_)) _).
    apply f_equal.
    rewrite (vs.(vsF_add_assoc) (vsF_add vs b_ (vsF_neg vs c_))
                                (vsF_add vs c_ (vsF_neg vs b_)) _).
    assert (Hcancel : vsF_add vs (vsF_add vs b_ (vsF_neg vs c_))
                                 (vsF_add vs c_ (vsF_neg vs b_))
                    = vsF_zero vs).
    { rewrite <- vs.(vsF_add_assoc).
      rewrite (vs.(vsF_add_assoc) (vsF_neg vs c_) c_ (vsF_neg vs b_)).
      rewrite (vs.(vsF_add_comm) (vsF_neg vs c_) c_).
      rewrite vs.(vsF_add_neg_r).
      rewrite vsF_add_zero_l.
      apply vs.(vsF_add_neg_r). }
    rewrite Hcancel. apply vsF_add_zero_l.
Qed.

(** Product of derivations need not be a derivation. *)
(* CAG zero-dependent Admitted der_product_not_der theories/Lie/Derivations.v:302 BEGIN
Lemma der_product_not_der {F : Type} {fld : Field F} {A : Type}
    (alg : FAlgebra fld A) :
    ~ (forall δ₁ δ₂, IsDerivation alg δ₁ -> IsDerivation alg δ₂ ->
       IsDerivation alg (fun x => δ₁ (δ₂ x))).
Proof. Admitted.
   CAG zero-dependent Admitted der_product_not_der theories/Lie/Derivations.v:302 END *)

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
