(** * LinAlg/LinearMap.v
    Linear maps between vector spaces, their composition, and basic
    structural lemmas. Built on top of the existing [VectorSpaceF]
    record.

    A linear map [φ : V → W] satisfies φ(u + v) = φ(u) + φ(v) and
    φ(c · v) = c · φ(v). *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.LinAlg.Basis.
From Stdlib Require Import List.
Import ListNotations.

(* ================================================================== *)
(** * 1. Linear maps as a Record                                      *)
(* ================================================================== *)

Record LinearMapF {F : Type} {fld : Field F} {V W : Type}
    (vsV : VectorSpaceF fld V) (vsW : VectorSpaceF fld W) : Type := {
  lm_fn      : V -> W;
  lm_add     : forall u v, lm_fn (vsF_add vsV u v) =
                           vsF_add vsW (lm_fn u) (lm_fn v);
  lm_scale   : forall a v, lm_fn (vsF_scale vsV a v) =
                           vsF_scale vsW a (lm_fn v);
}.

Arguments lm_fn      {F fld V W vsV vsW}.
Arguments lm_add     {F fld V W vsV vsW}.
Arguments lm_scale   {F fld V W vsV vsW}.

(** Linear map preserves the zero vector. *)
Lemma lm_zero {F : Type} {fld : Field F} {V W : Type}
    {vsV : VectorSpaceF fld V} {vsW : VectorSpaceF fld W}
    (φ : LinearMapF vsV vsW) :
    lm_fn φ (vsF_zero vsV) = vsF_zero vsW.
Proof.
  apply (vsF_add_cancel_double vsW).
  rewrite <- φ.(lm_add). f_equal. apply vsF_add_zero_r.
Qed.

(** Linear map preserves negation. *)
Lemma lm_neg {F : Type} {fld : Field F} {V W : Type}
    {vsV : VectorSpaceF fld V} {vsW : VectorSpaceF fld W}
    (φ : LinearMapF vsV vsW) (v : V) :
    lm_fn φ (vsF_neg vsV v) = vsF_neg vsW (lm_fn φ v).
Proof.
  rewrite (vsF_neg_eq_scale_neg_one vsV).
  rewrite (vsF_neg_eq_scale_neg_one vsW).
  apply φ.(lm_scale).
Qed.

(* ================================================================== *)
(** * 2. Identity and composition                                     *)
(* ================================================================== *)

(** Identity linear map. *)
Definition lm_id {F : Type} {fld : Field F} {V : Type}
    (vs : VectorSpaceF fld V) : LinearMapF vs vs :=
  {| lm_fn  := fun v => v;
     lm_add := fun u v => eq_refl;
     lm_scale := fun a v => eq_refl; |}.

(** Composition of linear maps. *)
Definition lm_comp {F : Type} {fld : Field F} {V W X : Type}
    {vsV : VectorSpaceF fld V} {vsW : VectorSpaceF fld W} {vsX : VectorSpaceF fld X}
    (g : LinearMapF vsW vsX) (f : LinearMapF vsV vsW) : LinearMapF vsV vsX.
Proof.
  refine {| lm_fn := fun v => lm_fn g (lm_fn f v); |}.
  - intros u v. rewrite f.(lm_add). apply g.(lm_add).
  - intros a v. rewrite f.(lm_scale). apply g.(lm_scale).
Defined.

(* ================================================================== *)
(** * 3. Endomorphisms (linear maps V → V)                            *)
(* ================================================================== *)

(** End(V) = LinearMapF vs vs. *)
Definition EndF {F : Type} {fld : Field F} {V : Type}
    (vs : VectorSpaceF fld V) : Type := LinearMapF vs vs.

(** End(V) addition: pointwise. *)
Definition end_add {F : Type} {fld : Field F} {V : Type}
    {vs : VectorSpaceF fld V}
    (f g : EndF vs) : EndF vs.
Proof.
  refine {| lm_fn := fun v => vsF_add vs (lm_fn f v) (lm_fn g v); |}.
  - intros u v.
    rewrite f.(lm_add), g.(lm_add).
    (* (fu + fv) + (gu + gv) = (fu + gu) + (fv + gv) *)
    set (a := lm_fn f u). set (b := lm_fn f v).
    set (c := lm_fn g u). set (d := lm_fn g v).
    rewrite <- (vs.(vsF_add_assoc) a b (vsF_add vs c d)).
    rewrite (vs.(vsF_add_assoc) b c d).
    rewrite (vs.(vsF_add_comm) b c).
    rewrite <- (vs.(vsF_add_assoc) c b d).
    apply vs.(vsF_add_assoc).
  - intros a v. rewrite f.(lm_scale), g.(lm_scale).
    symmetry. apply (vsF_scale_add_v vs).
Defined.

(** End(V) zero: constant zero map. *)
Definition end_zero {F : Type} {fld : Field F} {V : Type}
    (vs : VectorSpaceF fld V) : EndF vs.
Proof.
  refine {| lm_fn := fun _ => vsF_zero vs; |}.
  - intros u v. symmetry. apply vs.(vsF_add_zero_r).
  - intros a v. symmetry. apply vsF_scale_zero_v.
Defined.

(** End(V) scaling: pointwise. *)
Definition end_scale {F : Type} {fld : Field F} {V : Type}
    {vs : VectorSpaceF fld V}
    (a : F) (f : EndF vs) : EndF vs.
Proof.
  refine {| lm_fn := fun v => vsF_scale vs a (lm_fn f v); |}.
  - intros u v. rewrite f.(lm_add). apply (vsF_scale_add_v vs).
  - intros b v. rewrite f.(lm_scale).
    rewrite (vs.(vsF_scale_mul) a b (lm_fn f v)).
    rewrite (vs.(vsF_scale_mul) b a (lm_fn f v)).
    f_equal. apply (cr_mul_comm fld).
Defined.

(** End(V) negation. *)
Definition end_neg {F : Type} {fld : Field F} {V : Type}
    {vs : VectorSpaceF fld V}
    (f : EndF vs) : EndF vs.
Proof.
  refine {| lm_fn := fun v => vsF_neg vs (lm_fn f v); |}.
  - intros u v. rewrite f.(lm_add). apply vsF_neg_add.
  - intros a v. rewrite f.(lm_scale).
    rewrite (vsF_neg_eq_scale_neg_one vs (vsF_scale vs a (lm_fn f v))).
    rewrite (vs.(vsF_scale_mul) (cr_neg fld (cr_one fld)) a (lm_fn f v)).
    rewrite (vsF_neg_eq_scale_neg_one vs (lm_fn f v)).
    rewrite (vs.(vsF_scale_mul) a (cr_neg fld (cr_one fld)) (lm_fn f v)).
    f_equal. apply (cr_mul_comm fld).
Defined.
