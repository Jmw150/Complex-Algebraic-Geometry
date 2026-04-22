(** Kahler/sl2/Basic.v — Abstract sl2 representation theory

    Define the sl2 Lie algebra and its modules.  Prove the foundational
    lemmas about weight spaces and primitive vectors that are needed for
    Hard Lefschetz.

    References: ag.org Part I §sl2 representation theory *)

From Stdlib Require Import List Arith Lia QArith ZArith.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyRealsMult.
From CAG Require Import Complex.
From CAG Require Import LieAlgebra.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. sl2-modules                                                   *)
(* ================================================================== *)

(** An sl2-module is a vector space V equipped with three linear
    operators X (raising), Y (lowering), H (grading) satisfying the
    sl2 commutation relations:

      [H, X] = 2 X   i.e.  H(X v) - X(H v) = 2 X v
      [H, Y] = -2 Y  i.e.  H(Y v) - Y(H v) = -2 Y v
      [X, Y] = H     i.e.  X(Y v) - Y(X v) = H v          *)

Record SL2Module (V : Type) (vs : VectorSpace V) : Type :=
{ sl2_X : V -> V   (** raising / E operator *)
; sl2_Y : V -> V   (** lowering / F operator *)
; sl2_H : V -> V   (** grading / Cartan operator *)

  (** X is C-linear *)
; sl2_X_add   : forall u v,
    sl2_X (vs_add vs u v) = vs_add vs (sl2_X u) (sl2_X v)
; sl2_X_scale : forall c v,
    sl2_X (vs_scale vs c v) = vs_scale vs c (sl2_X v)

  (** Y is C-linear *)
; sl2_Y_add   : forall u v,
    sl2_Y (vs_add vs u v) = vs_add vs (sl2_Y u) (sl2_Y v)
; sl2_Y_scale : forall c v,
    sl2_Y (vs_scale vs c v) = vs_scale vs c (sl2_Y v)

  (** H is C-linear *)
; sl2_H_add   : forall u v,
    sl2_H (vs_add vs u v) = vs_add vs (sl2_H u) (sl2_H v)
; sl2_H_scale : forall c v,
    sl2_H (vs_scale vs c v) = vs_scale vs c (sl2_H v)

  (** sl2 commutation relations *)
; sl2_rel_HX : forall v,
    vs_add vs (sl2_H (sl2_X v)) (vs_neg vs (sl2_X (sl2_H v))) =
    vs_scale vs (Cadd C1 C1) (sl2_X v)
; sl2_rel_HY : forall v,
    vs_add vs (sl2_H (sl2_Y v)) (vs_neg vs (sl2_Y (sl2_H v))) =
    vs_scale vs (Cneg (Cadd C1 C1)) (sl2_Y v)
; sl2_rel_XY : forall v,
    vs_add vs (sl2_X (sl2_Y v)) (vs_neg vs (sl2_Y (sl2_X v))) =
    sl2_H v
}.

Arguments sl2_X {V vs} _.
Arguments sl2_Y {V vs} _.
Arguments sl2_H {V vs} _.
Arguments sl2_X_add   {V vs} _ _ _.
Arguments sl2_X_scale {V vs} _ _ _.
Arguments sl2_Y_add   {V vs} _ _ _.
Arguments sl2_Y_scale {V vs} _ _ _.
Arguments sl2_H_add   {V vs} _ _ _.
Arguments sl2_H_scale {V vs} _ _ _.
Arguments sl2_rel_HX  {V vs} _ _.
Arguments sl2_rel_HY  {V vs} _ _.
Arguments sl2_rel_XY  {V vs} _ _.

(* ================================================================== *)
(** * 2. Weight spaces                                                 *)
(* ================================================================== *)

(** v has weight lambda if H(v) = lambda * v. *)
Definition is_weight {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs) (lambda : CComplex) (v : V) : Prop :=
  sl2_H m v = vs_scale vs lambda v.

(** Weight-lambda subspace (as a predicate). *)
Definition WeightSpace {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs) (lambda : CComplex) : V -> Prop :=
  is_weight m lambda.

(* ================================================================== *)
(** * 3. Weight shift lemmas                                           *)
(* ================================================================== *)

(** If H(v) = λ·v then H(X(v)) = (λ+2)·X(v).
    Proof: H(X(v)) = X(H(v)) + 2·X(v) = X(λ·v) + 2·X(v)
                   = λ·X(v) + 2·X(v) = (λ+2)·X(v). *)
Lemma X_shifts_weight {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs) (lambda : CComplex) (v : V) :
    is_weight m lambda v ->
    is_weight m (Cadd lambda (Cadd C1 C1)) (sl2_X m v).
Proof.
  unfold is_weight. intro Hv.
  (* H(X v) = X(H v) + 2·X(v)  by sl2_rel_HX *)
  assert (Hrel := sl2_rel_HX m v).
  (* Hrel : H(X v) - X(H v) = 2·X v  i.e.  H(X v) = X(H v) + 2·X v *)
  (* In our notation: vs_add (H(X v)) (neg (X(H v))) = scale 2 (X v) *)
  (* So H(X v) = X(H v) + 2·X v *)
  (* Substituting H v = λ·v: X(H v) = X(λ·v) = λ·X(v)  by linearity *)
  assert (HXHv : sl2_X m (sl2_H m v) = vs_scale vs lambda (sl2_X m v)).
  { rewrite Hv. exact (sl2_X_scale m lambda v). }
  (* From Hrel: H(Xv) = X(Hv) + 2·Xv = λ·Xv + 2·Xv = (λ+2)·Xv *)
  (* We need to extract H(Xv) from Hrel *)
  (* Hrel says: H(Xv) + neg(X(Hv)) = 2·Xv
     So H(Xv) = X(Hv) + 2·Xv = λ·Xv + 2·Xv *)
  (* Use: a + neg b = c  ↔  a = b + c  in any abelian group *)
  assert (Hstep :
    sl2_H m (sl2_X m v) =
    vs_add vs (sl2_X m (sl2_H m v)) (vs_scale vs (Cadd C1 C1) (sl2_X m v))).
  { (* From Hrel: H(Xv) + neg(X(Hv)) = 2·Xv
       Add X(Hv) to both sides, then use associativity + neg_r *)
    assert (H1 :
      vs_add vs (vs_add vs (sl2_H m (sl2_X m v)) (vs_neg vs (sl2_X m (sl2_H m v))))
                (sl2_X m (sl2_H m v)) =
      vs_add vs (vs_scale vs (Cadd C1 C1) (sl2_X m v)) (sl2_X m (sl2_H m v))).
    { rewrite Hrel. reflexivity. }
    rewrite <- vs_add_assoc in H1.
    assert (Hneg : vs_add vs (vs_neg vs (sl2_X m (sl2_H m v))) (sl2_X m (sl2_H m v)) =
                   vs_zero vs).
    { rewrite vs_add_comm. apply vs_add_neg_r. }
    rewrite Hneg in H1.
    rewrite vs_add_zero_r in H1.
    rewrite vs_add_comm in H1.
    exact H1. }
  rewrite Hstep, HXHv.
  rewrite <- vs_scale_add_s.
  reflexivity.
Qed.

(** If H(v) = λ·v then H(Y(v)) = (λ-2)·Y(v). *)
Lemma Y_shifts_weight {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs) (lambda : CComplex) (v : V) :
    is_weight m lambda v ->
    is_weight m (Csub lambda (Cadd C1 C1)) (sl2_Y m v).
Proof.
  unfold is_weight. intro Hv.
  assert (Hrel := sl2_rel_HY m v).
  assert (HYHv : sl2_Y m (sl2_H m v) = vs_scale vs lambda (sl2_Y m v)).
  { rewrite Hv. exact (sl2_Y_scale m lambda v). }
  assert (Hstep :
    sl2_H m (sl2_Y m v) =
    vs_add vs (sl2_Y m (sl2_H m v)) (vs_scale vs (Cneg (Cadd C1 C1)) (sl2_Y m v))).
  { assert (H1 :
      vs_add vs (vs_add vs (sl2_H m (sl2_Y m v)) (vs_neg vs (sl2_Y m (sl2_H m v))))
                (sl2_Y m (sl2_H m v)) =
      vs_add vs (vs_scale vs (Cneg (Cadd C1 C1)) (sl2_Y m v)) (sl2_Y m (sl2_H m v))).
    { rewrite Hrel. reflexivity. }
    rewrite <- vs_add_assoc in H1.
    assert (Hneg : vs_add vs (vs_neg vs (sl2_Y m (sl2_H m v))) (sl2_Y m (sl2_H m v)) =
                   vs_zero vs).
    { rewrite vs_add_comm. apply vs_add_neg_r. }
    rewrite Hneg in H1.
    rewrite vs_add_zero_r in H1.
    rewrite vs_add_comm in H1.
    exact H1. }
  rewrite Hstep, HYHv.
  rewrite <- vs_scale_add_s.
  unfold Csub. reflexivity.
Qed.

(** Iterating: H(Y^n v) = (λ - 2n)·Y^n v for a weight-λ vector v. *)
Lemma Y_power_weight {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs) (lambda : CComplex) (v : V) :
    is_weight m lambda v ->
    forall (n : nat),
    is_weight m (Csub lambda (Cmul (Cinject_Q (QArith_base.inject_Z (Z.of_nat n))) (Cadd C1 C1)))
              (Nat.iter n (sl2_Y m) v).
Proof.
  intro Hv. induction n as [| n IH].
  - (** Base case: n = 0.
        Goal: is_weight m (lambda - 0*2) v.
        We have Hv: is_weight m lambda v.
        Since lambda - 0*2 ~~C lambda (by Csub_C0mul_r), use vs_scale_creal_eq. *)
    simpl. unfold is_weight. rewrite Hv. symmetry.
    apply vs_scale_creal_eq.
    + exact (proj1 (Csub_C0mul_r lambda (Cadd C1 C1))).
    + exact (proj2 (Csub_C0mul_r lambda (Cadd C1 C1))).
  - (** Inductive step: n → S n.
        IH: is_weight m (lambda - n*2) (Y^n v).
        By Y_shifts_weight: is_weight m ((lambda - n*2) - 2) (Y^{n+1} v).
        By Csub_two_succ: (lambda - n*2) - 2 ~~C lambda - (S n)*2. *)
    simpl. unfold is_weight in *.
    pose proof (Y_shifts_weight m
        (Csub lambda (Cmul (Cinject_Q (QArith_base.inject_Z (Z.of_nat n))) (Cadd C1 C1)))
        (Nat.iter n (sl2_Y m) v) IH) as Hn1.
    rewrite Hn1.
    apply vs_scale_creal_eq.
    + exact (proj1 (Csub_two_succ lambda n)).
    + exact (proj2 (Csub_two_succ lambda n)).
Qed.

(* ================================================================== *)
(** * 4. Primitive vectors                                             *)
(* ================================================================== *)

(** v is X-primitive (or just primitive) if X(v) = 0. *)
Definition is_primitive {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs) (v : V) : Prop :=
  sl2_X m v = vs_zero vs.

(** A primitive weight-λ vector v generates the submodule
      { v, Yv, Y^2v, ..., Y^n v }
    for some n with Y^{n+1} v = 0.
    This is stated as a predicate. *)
Definition primitive_orbit {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs) (v : V) (n : nat) : Prop :=
  is_primitive m v /\
  Nat.iter (S n) (sl2_Y m) v = vs_zero vs.

(* ================================================================== *)
(** * 5. Key identity: X(Y^{n+1} v) for primitive v                   *)
(* ================================================================== *)

(** For a primitive weight-λ vector v:
      X(Y^k v) = k·(λ - k + 1)·Y^{k-1} v

    This is the key identity relating X and Y on a primitive orbit.
    It implies that if Y^{n+1} v = 0 and Y^n v ≠ 0, then λ = n. *)

(** Base case of the key identity: X(Y v) = H v = λ v. *)
Lemma XY_primitive_base {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs) (v : V) :
    is_primitive m v ->
    sl2_X m (sl2_Y m v) = sl2_H m v.
Proof.
  unfold is_primitive. intro Hprim.
  assert (Hrel := sl2_rel_XY m v).
  (* Y(0) = 0 by linearity: Y(0) = Y(0+0) = Y(0)+Y(0) => Y(0) = 0 *)
  assert (HYzero : sl2_Y m (vs_zero vs) = vs_zero vs).
  { assert (Hstep : sl2_Y m (vs_zero vs) =
                    vs_add vs (sl2_Y m (vs_zero vs)) (sl2_Y m (vs_zero vs))).
    { rewrite <- sl2_Y_add. rewrite vs_add_zero_r. reflexivity. }
    assert (Hn : vs_add vs (sl2_Y m (vs_zero vs)) (vs_neg vs (sl2_Y m (vs_zero vs))) = vs_zero vs).
    { apply vs_add_neg_r. }
    rewrite Hstep in Hn at 1.
    rewrite <- vs_add_assoc in Hn.
    rewrite vs_add_neg_r in Hn.
    rewrite vs_add_zero_r in Hn.
    exact Hn. }
  (* neg(vs_zero) = vs_zero *)
  assert (neg_zero : vs_neg vs (vs_zero vs) = vs_zero vs).
  { assert (h : vs_add vs (vs_zero vs) (vs_neg vs (vs_zero vs)) = vs_zero vs).
    { apply vs_add_neg_r. }
    rewrite vs_add_comm in h. rewrite vs_add_zero_r in h.
    exact h. }
  (* Y(X v) = Y(0) = 0 *)
  assert (HYXv : sl2_Y m (sl2_X m v) = vs_zero vs).
  { rewrite Hprim. exact HYzero. }
  (* From Hrel: X(Yv) + neg(Y(Xv)) = Hv
                X(Yv) + neg(0) = Hv
                X(Yv) + 0 = Hv
                X(Yv) = Hv *)
  rewrite HYXv, neg_zero in Hrel.
  rewrite vs_add_zero_r in Hrel.
  exact Hrel.
Qed.

(** The full XY identity for primitive orbits is standard but requires
    working through an inductive computation.  We state it as an axiom
    (to be proved from the inductive argument in FiniteDimensional.v). *)
Theorem XY_primitive_identity : forall {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs) (lambda : CComplex) (v : V) (k : nat),
    is_primitive m v ->
    is_weight m lambda v ->
    sl2_X m (Nat.iter (S k) (sl2_Y m) v) =
    vs_scale vs
      (Cmul (Cinject_Q (QArith_base.inject_Z (Z.of_nat (S k))))
            (Csub lambda (Cinject_Q (QArith_base.inject_Z (Z.of_nat k)))))
      (Nat.iter k (sl2_Y m) v).
Proof.
  intros V vs m lambda v k Hprim Hweight.
  induction k as [| k IH].
  - (** Base case k = 0: X(Y v) = H v = lambda * v = 1*(lambda - 0) * v *)
    change (Nat.iter (S 0) (sl2_Y m) v) with (sl2_Y m v).
    change (Nat.iter 0 (sl2_Y m) v) with v.
    rewrite (XY_primitive_base m v Hprim), Hweight.
    assert (H0 : inject_Q (QArith_base.inject_Z (Z.of_nat 0)) == (0:CReal)) by apply CRealEq_refl.
    assert (H1 : inject_Q (QArith_base.inject_Z (Z.of_nat 1)) == (1:CReal)) by apply inject_Q_one.
    apply vs_scale_creal_eq.
    + unfold Cmul, Csub, Cadd, Cneg, Cinject_Q.
      cbn [re im].
      rewrite H0, H1. ring.
    + unfold Cmul, Csub, Cadd, Cneg, Cinject_Q.
      cbn [re im].
      rewrite H0, H1. ring.
  - (** Inductive case: assume the identity at k, prove at S k. *)
    set (w := Nat.iter (S k) (sl2_Y m) v).
    change (Nat.iter (S (S k)) (sl2_Y m) v) with (sl2_Y m w).
    (** CRealEq key: inject_Q(inject_Z(S k)) == inject_Q(inject_Z k) + 1 *)
    assert (HQk1 : QArith_base.inject_Z (Z.of_nat (S k)) =
                   (QArith_base.inject_Z (Z.of_nat k) + 1)%Q).
    { rewrite Nat2Z.inj_succ. apply QArith_base.inject_Z_plus. }
    assert (Hk1 : inject_Q (QArith_base.inject_Z (Z.of_nat (S k))) ==
                  inject_Q (QArith_base.inject_Z (Z.of_nat k)) + 1).
    { rewrite HQk1.
      apply (CRealEq_trans _ (inject_Q (QArith_base.inject_Z (Z.of_nat k)) + inject_Q 1) _).
      - apply inject_Q_plus.
      - apply CReal_plus_proper_l. apply inject_Q_one. }
    (** CRealEq key: inject_Q(inject_Z(S(S k))) == inject_Q(inject_Z k) + 1 + 1 *)
    assert (HQk2 : QArith_base.inject_Z (Z.of_nat (S (S k))) =
                   (QArith_base.inject_Z (Z.of_nat (S k)) + 1)%Q).
    { rewrite Nat2Z.inj_succ. apply QArith_base.inject_Z_plus. }
    assert (Hk2 : inject_Q (QArith_base.inject_Z (Z.of_nat (S (S k)))) ==
                  inject_Q (QArith_base.inject_Z (Z.of_nat k)) + 1 + 1).
    { apply (CRealEq_trans _ (inject_Q (QArith_base.inject_Z (Z.of_nat (S k))) + 1) _).
      - rewrite HQk2.
        apply (CRealEq_trans _ (inject_Q (QArith_base.inject_Z (Z.of_nat (S k))) + inject_Q 1) _).
        + apply inject_Q_plus.
        + apply CReal_plus_proper_l. apply inject_Q_one.
      - rewrite Hk1. ring. }
    (** Step 1: X(Y w) = H w + Y(X w)  (from sl2_rel_XY). *)
    assert (HXY : sl2_X m (sl2_Y m w) =
                  vs_add vs (sl2_H m w) (sl2_Y m (sl2_X m w))).
    { pose proof (sl2_rel_XY m w) as Hrel.
      assert (H1 :
        vs_add vs (vs_add vs (sl2_X m (sl2_Y m w))
                             (vs_neg vs (sl2_Y m (sl2_X m w))))
                  (sl2_Y m (sl2_X m w)) =
        vs_add vs (sl2_H m w) (sl2_Y m (sl2_X m w))).
      { rewrite Hrel. reflexivity. }
      rewrite <- vs_add_assoc in H1.
      assert (Hneg : vs_add vs (vs_neg vs (sl2_Y m (sl2_X m w)))
                              (sl2_Y m (sl2_X m w)) = vs_zero vs).
      { rewrite vs_add_comm. apply vs_add_neg_r. }
      rewrite Hneg in H1.
      rewrite vs_add_zero_r in H1.
      exact H1. }
    (** Step 2: H w = (λ - 2(k+1)) * w  (weight of Y^{k+1} v). *)
    assert (Hw_weight : sl2_H m w =
        vs_scale vs (Csub lambda (Cmul (Cinject_Q (QArith_base.inject_Z (Z.of_nat (S k)))) (Cadd C1 C1))) w).
    { exact (Y_power_weight m lambda v Hweight (S k)). }
    (** Step 3: Y(X w) = (k+1)*(λ-k) * w  (by IH + Y-linearity). *)
    assert (HYXw : sl2_Y m (sl2_X m w) =
        vs_scale vs (Cmul (Cinject_Q (QArith_base.inject_Z (Z.of_nat (S k))))
                          (Csub lambda (Cinject_Q (QArith_base.inject_Z (Z.of_nat k))))) w).
    { unfold w. rewrite IH, sl2_Y_scale. reflexivity. }
    (** Step 4: combine via vs_scale_add_s. *)
    rewrite HXY, Hw_weight, HYXw.
    rewrite <- vs_scale_add_s.
    apply vs_scale_creal_eq.
    + (** re: (λ_re - (k+1)*2) + (k+1)*(λ_re - k) = (k+2)*(λ_re - (k+1)) *)
      unfold Cadd, Csub, Cneg, Cmul, Cinject_Q, C0, C1. simpl.
      rewrite Hk1, Hk2. ring.
    + (** im component — same ring arithmetic *)
      unfold Cadd, Csub, Cneg, Cmul, Cinject_Q, C0, C1. simpl.
      rewrite Hk1, Hk2. ring.
Qed.

(* ================================================================== *)
(** * 6. Submodule generated by primitive vector                       *)
(* ================================================================== *)

(** Proposition (ag.org NEXT item): if v is a primitive weight-λ vector,
    then the span of {v, Yv, ..., Y^n v} (for Y^{n+1} v = 0)
    is a submodule isomorphic to the irreducible module V(n).

    We express this as: the orbit under Y is H-stable and X-stable. *)

(** H maps the orbit to itself (weight shift). *)
Lemma orbit_H_stable {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs) (lambda : CComplex) (v : V) (n : nat) :
    is_primitive m v ->
    is_weight m lambda v ->
    forall k, (k <= n)%nat ->
    is_weight m (Csub lambda (Cmul (Cinject_Q (QArith_base.inject_Z (Z.of_nat k))) (Cadd C1 C1)))
              (Nat.iter k (sl2_Y m) v).
Proof.
  intros Hprim Hw k Hk.
  exact (Y_power_weight m lambda v Hw k).
Qed.

(* ================================================================== *)
(** * 7. Direct sum of sl2-modules                                     *)
(* ================================================================== *)

(** We state but do not fully formalize the direct sum structure here.
    The FiniteDimensional.v file handles the decomposition theorem. *)

(** Two sl2-modules are isomorphic if there is a linear bijection
    intertwining X, Y, H. *)
Record SL2Iso {V W : Type} {vsV : VectorSpace V} {vsW : VectorSpace W}
    (mV : SL2Module V vsV) (mW : SL2Module W vsW) : Type :=
{ sl2iso_map     : V -> W
; sl2iso_inv     : W -> V
; sl2iso_linear_add   : forall u v,
    sl2iso_map (vs_add vsV u v) = vs_add vsW (sl2iso_map u) (sl2iso_map v)
; sl2iso_linear_scale : forall c v,
    sl2iso_map (vs_scale vsV c v) = vs_scale vsW c (sl2iso_map v)
; sl2iso_X : forall v,
    sl2iso_map (sl2_X mV v) = sl2_X mW (sl2iso_map v)
; sl2iso_Y : forall v,
    sl2iso_map (sl2_Y mV v) = sl2_Y mW (sl2iso_map v)
; sl2iso_H : forall v,
    sl2iso_map (sl2_H mV v) = sl2_H mW (sl2iso_map v)
; sl2iso_left_inv  : forall v, sl2iso_inv (sl2iso_map v) = v
; sl2iso_right_inv : forall w, sl2iso_map (sl2iso_inv w) = w
}.

(* ================================================================== *)
(** * 8. Weight space is a subspace                                    *)
(* ================================================================== *)

(** A nonzero weight vector (weight vector ≠ 0). *)
Definition is_weight_vector {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs) (lambda : CComplex) (v : V) : Prop :=
  is_weight m lambda v /\ v <> vs_zero vs.

(** V_λ is closed under addition. *)
Lemma weight_space_add {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs) (lambda : CComplex) (u v : V) :
    is_weight m lambda u ->
    is_weight m lambda v ->
    is_weight m lambda (vs_add vs u v).
Proof.
  unfold is_weight. intros Hu Hv.
  (* H(u+v) = H u + H v = λu + λv = λ(u+v) *)
  rewrite sl2_H_add, Hu, Hv.
  symmetry. apply vs_scale_add_v.
Qed.

(** V_λ is closed under scalar multiplication. *)
Lemma weight_space_scale {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs) (lambda c : CComplex) (v : V) :
    is_weight m lambda v ->
    is_weight m lambda (vs_scale vs c v).
Proof.
  unfold is_weight. intro Hv.
  (* H(c·v) = c·H(v) = c·(λ·v) = (c·λ)·v *)
  rewrite sl2_H_scale, Hv, vs_scale_assoc.
  (* RHS: λ·(c·v) = (λ·c)·v, so need Cmul c lambda = Cmul lambda c *)
  rewrite vs_scale_assoc.
  apply vs_scale_creal_eq.
  - unfold Cmul. simpl. ring.
  - unfold Cmul. simpl. ring.
Qed.

(** V_λ contains 0. *)
Lemma weight_space_zero {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs) (lambda : CComplex) :
    is_weight m lambda (vs_zero vs).
Proof.
  unfold is_weight.
  (* H(0) = 0  and  λ·0 = 0  — both need linearity *)
  (* H is linear, so H(0) = H(0+0) = H(0)+H(0), hence H(0) = 0 *)
  assert (HH0 : sl2_H m (vs_zero vs) = vs_zero vs).
  { assert (Hstep : sl2_H m (vs_zero vs) =
                    vs_add vs (sl2_H m (vs_zero vs)) (sl2_H m (vs_zero vs))).
    { rewrite <- sl2_H_add. rewrite vs_add_zero_r. reflexivity. }
    assert (Hn : vs_add vs (sl2_H m (vs_zero vs)) (vs_neg vs (sl2_H m (vs_zero vs))) =
                 vs_zero vs) by apply vs_add_neg_r.
    rewrite Hstep in Hn at 1.
    rewrite <- vs_add_assoc in Hn.
    rewrite vs_add_neg_r in Hn. rewrite vs_add_zero_r in Hn.
    exact Hn. }
  rewrite HH0.
  (* λ·0 = 0 *)
  assert (Hscale0 : vs_scale vs lambda (vs_zero vs) = vs_zero vs).
  { assert (Hstep : vs_scale vs lambda (vs_zero vs) =
                    vs_add vs (vs_scale vs lambda (vs_zero vs))
                               (vs_scale vs lambda (vs_zero vs))).
    { rewrite <- vs_scale_add_v. rewrite vs_add_zero_r. reflexivity. }
    assert (Hn : vs_add vs (vs_scale vs lambda (vs_zero vs))
                            (vs_neg vs (vs_scale vs lambda (vs_zero vs))) =
                 vs_zero vs) by apply vs_add_neg_r.
    rewrite Hstep in Hn at 1.
    rewrite <- vs_add_assoc in Hn.
    rewrite vs_add_neg_r in Hn. rewrite vs_add_zero_r in Hn.
    exact Hn. }
  symmetry. exact Hscale0.
Qed.

(** V_λ is closed under negation.
    Proof: H(neg v) = neg(H v) = neg(λv) = λ(neg v), using linearity. *)
Lemma weight_space_neg {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs) (lambda : CComplex) (v : V) :
    is_weight m lambda v ->
    is_weight m lambda (vs_neg vs v).
Proof.
  unfold is_weight. intro Hv.
  (* Step 1: H(neg v) = neg(H v)  using  H(neg v) + H(v) = H(0) = 0 *)
  assert (HHneg : sl2_H m (vs_neg vs v) = vs_neg vs (sl2_H m v)).
  { assert (H1 : vs_add vs (sl2_H m (vs_neg vs v)) (sl2_H m v) = vs_zero vs).
    { rewrite <- sl2_H_add.
      assert (Hnn : vs_add vs (vs_neg vs v) v = vs_zero vs).
      { rewrite vs_add_comm. apply vs_add_neg_r. }
      rewrite Hnn.
      (* H(0) = 0 *)
      assert (Hstep : sl2_H m (vs_zero vs) =
                      vs_add vs (sl2_H m (vs_zero vs)) (sl2_H m (vs_zero vs))).
      { rewrite <- sl2_H_add. rewrite vs_add_zero_r. reflexivity. }
      assert (Hn : vs_add vs (sl2_H m (vs_zero vs)) (vs_neg vs (sl2_H m (vs_zero vs))) =
                   vs_zero vs) by apply vs_add_neg_r.
      rewrite Hstep in Hn at 1. rewrite <- vs_add_assoc in Hn.
      rewrite vs_add_neg_r in Hn. rewrite vs_add_zero_r in Hn. exact Hn. }
    assert (H2 : vs_add vs (vs_add vs (sl2_H m (vs_neg vs v)) (sl2_H m v))
                            (vs_neg vs (sl2_H m v)) =
                 vs_add vs (vs_zero vs) (vs_neg vs (sl2_H m v))).
    { rewrite H1. reflexivity. }
    rewrite <- vs_add_assoc in H2. rewrite vs_add_neg_r in H2.
    rewrite vs_add_zero_r in H2.
    assert (H3 : vs_add vs (vs_zero vs) (vs_neg vs (sl2_H m v)) = vs_neg vs (sl2_H m v)).
    { rewrite vs_add_comm. apply vs_add_zero_r. }
    rewrite H3 in H2. exact H2. }
  (* Step 2: neg(scale lambda v) = scale lambda (neg v) *)
  assert (Hscale_neg : vs_scale vs lambda (vs_neg vs v) = vs_neg vs (vs_scale vs lambda v)).
  { assert (Hscale0 : vs_scale vs lambda (vs_zero vs) = vs_zero vs).
    { assert (Hst : vs_scale vs lambda (vs_zero vs) =
                    vs_add vs (vs_scale vs lambda (vs_zero vs))
                               (vs_scale vs lambda (vs_zero vs))).
      { rewrite <- vs_scale_add_v. rewrite vs_add_zero_r. reflexivity. }
      assert (Hn : vs_add vs (vs_scale vs lambda (vs_zero vs))
                              (vs_neg vs (vs_scale vs lambda (vs_zero vs))) = vs_zero vs).
      { apply vs_add_neg_r. }
      rewrite Hst in Hn at 1. rewrite <- vs_add_assoc in Hn.
      rewrite vs_add_neg_r in Hn. rewrite vs_add_zero_r in Hn. exact Hn. }
    assert (H1 : vs_add vs (vs_scale vs lambda (vs_neg vs v)) (vs_scale vs lambda v) = vs_zero vs).
    { rewrite <- vs_scale_add_v.
      assert (Hnn : vs_add vs (vs_neg vs v) v = vs_zero vs).
      { rewrite vs_add_comm. apply vs_add_neg_r. }
      rewrite Hnn. exact Hscale0. }
    assert (H2 : vs_add vs (vs_add vs (vs_scale vs lambda (vs_neg vs v)) (vs_scale vs lambda v))
                            (vs_neg vs (vs_scale vs lambda v)) =
                 vs_add vs (vs_zero vs) (vs_neg vs (vs_scale vs lambda v))).
    { rewrite H1. reflexivity. }
    rewrite <- vs_add_assoc in H2. rewrite vs_add_neg_r in H2.
    rewrite vs_add_zero_r in H2.
    assert (H3 : vs_add vs (vs_zero vs) (vs_neg vs (vs_scale vs lambda v)) =
                 vs_neg vs (vs_scale vs lambda v)).
    { rewrite vs_add_comm. apply vs_add_zero_r. }
    rewrite H3 in H2. exact H2. }
  (* Combine: H(neg v) = neg(H v) = neg(lambda * v) = lambda * neg v *)
  rewrite HHneg, Hv, Hscale_neg.
  reflexivity.
Qed.

(* ================================================================== *)
(** * 9. Maximal vectors (Humphreys terminology)                       *)
(* ================================================================== *)

(** A maximal vector of weight λ is a nonzero X-annihilated weight vector.
    This is what we call is_primitive with the additional nonzero condition. *)
Definition is_maximal_vector {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs) (lambda : CComplex) (v : V) : Prop :=
  is_weight m lambda v /\
  is_primitive m v /\
  v <> vs_zero vs.

(** X maps each weight-λ space into the weight-(λ+2) space. *)
Lemma X_maps_weight_space {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs) (lambda : CComplex) (u : V) :
    is_weight m lambda u ->
    is_weight m (Cadd lambda (Cadd C1 C1)) (sl2_X m u).
Proof.
  exact (X_shifts_weight m lambda u).
Qed.

(** Y maps each weight-λ space into the weight-(λ-2) space. *)
Lemma Y_maps_weight_space {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs) (lambda : CComplex) (u : V) :
    is_weight m lambda u ->
    is_weight m (Csub lambda (Cadd C1 C1)) (sl2_Y m u).
Proof.
  exact (Y_shifts_weight m lambda u).
Qed.

(* ================================================================== *)
(** * 10. Y-orbit as a subspace                                        *)
(* ================================================================== *)

(** The Y-orbit of v through index k: Y^k v. *)
Notation Y_iter m k v := (Nat.iter k (sl2_Y m) v).

(** The span predicate: u is in the span of the Y-orbit of v up to step n. *)
(** Formally: u = sum_{k=0}^{n} c_k * Y^k v for some scalars c_k. *)
(** We leave the span as a predicate for now and work with individual orbit vectors. *)

(** Each orbit vector Y^k v is a weight vector of weight λ - 2k. *)
Lemma orbit_weight {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs) (lambda : CComplex) (v : V) (k : nat) :
    is_weight m lambda v ->
    is_weight m (Csub lambda (Cmul (Cinject_Q (QArith_base.inject_Z (Z.of_nat k)))
                                    (Cadd C1 C1)))
              (Y_iter m k v).
Proof.
  intro Hw. exact (Y_power_weight m lambda v Hw k).
Qed.

(** Y maps Y^k v to Y^{k+1} v (trivial by definition). *)
Lemma orbit_Y_step {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs) (v : V) (k : nat) :
    sl2_Y m (Y_iter m k v) = Y_iter m (S k) v.
Proof.
  reflexivity.
Qed.

(** X maps Y^{k+1} v back to a scalar multiple of Y^k v.
    This is the key identity relating X and Y on the orbit. *)
Lemma orbit_X_step {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs) (lambda : CComplex) (v : V) (k : nat) :
    is_primitive m v ->
    is_weight m lambda v ->
    sl2_X m (Y_iter m (S k) v) =
    vs_scale vs
      (Cmul (Cinject_Q (QArith_base.inject_Z (Z.of_nat (S k))))
            (Csub lambda (Cinject_Q (QArith_base.inject_Z (Z.of_nat k)))))
      (Y_iter m k v).
Proof.
  exact (XY_primitive_identity m lambda v k).
Qed.
