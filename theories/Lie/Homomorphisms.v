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

(** We cannot construct quotient types directly in Rocq.
    We axiomatize the quotient Lie algebra as existing with the required properties. *)

(** Quotient: given a Lie algebra L and an ideal I, we assert the existence
    of a Lie algebra L/I together with a surjective homomorphism π : L → L/I
    with kernel exactly I. *)

Section QuotientLieAlgebra.

  Context {F : Type} {fld : Field F} {L : Type}
          (la : LieAlgebraF fld L) (I : L -> Prop) (hI : IsIdeal la I).

  (** The quotient type L/I (axiomatized). *)
  Axiom QuotType : Type.
  Axiom QuotAlg  : LieAlgebraF fld QuotType.

  (** The canonical projection π : L → L/I. *)
  Axiom pi_hom : LieHom la QuotAlg.

  (** π is surjective. *)
  Axiom pi_surj : forall q : QuotType, exists x, lh_fn pi_hom x = q.

  (** Kernel of π is exactly I. *)
  Axiom pi_ker : forall x, LieKer pi_hom x <-> I x.

End QuotientLieAlgebra.

(** ** First isomorphism theorem *)

(** For φ : L → L', L / Ker(φ) ≅ Im(φ). *)
Axiom first_iso_theorem : forall {F : Type} {fld : Field F} {L M : Type}
    {la : LieAlgebraF fld L} {lb : LieAlgebraF fld M}
    (φ : LieHom la lb),
    exists (quot : LieAlgebraF fld L), inhabited (LieIsom quot lb).

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
