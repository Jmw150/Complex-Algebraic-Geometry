(** * Partial Derivatives for Cⁿ → C and Cⁿ → Cⁿ functions

    Building on Complex.v (CComplex, Cn, freeze_except, Rderiv_at,
    partial_x_at / partial_y_at) and ComplexAnalysis.v (dbar_value,
    del_value, Cderiv_at), this file develops a Prop-level theory of
    partial derivatives of multivariate complex functions:

      ∂u/∂xⱼ , ∂u/∂yⱼ                    (real partials of the real
                                          and imaginary parts of a
                                          Cⁿ → C function)
      ∂f/∂zⱼ , ∂f/∂z̄ⱼ                    (Wirtinger partials of a
                                          Cⁿ → C function)

    These extend the one-variable [partial_x_at] / [partial_y_at] /
    [dbar_at] / [del_at] from [Complex.v] / [ComplexAnalysis.v] to
    arbitrary [n] and to component functions.

    Why Prop-level?  The constructive Cauchy-real setting (CReal /
    CComplex) does not give a total derivative function
    [Cderiv : (C → C) → C → C]: extracting a witness from
    [exists L, Cderiv_at f z L] requires definite description over
    CReal-valued limits, which is not available without choice.  We
    therefore parallel the existing project idiom: derivatives are
    Prop-level relations, and computational consequences (Jacobian
    matrices, ∂̄-operators on forms) are captured by specification
    predicates [is_complex_jacobian], [is_pqf_dbar] living alongside
    the Parameter being characterised.

    All lemmas proved here are axiom-free in the strict sense: they
    depend only on the Stdlib CReal axioms and the project's
    [CRealEq_eq] bridge axiom (used implicitly via the [ring] tactic
    on CReal).  No new project-level axioms are introduced. *)

From Stdlib Require Import QArith ZArith.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyRealsMult.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyAbs.

From CAG Require Import Reals_extra.
From CAG Require Import Complex.
From CAG Require Import ComplexAnalysis.

Set Warnings "-warn-library-file-stdlib-vector".
From Stdlib Require Import Vectors.Fin.
Set Warnings "+warn-library-file-stdlib-vector".

Local Open Scope CReal_scope.

(* ------------------------------------------------------------------ *)
(** * 1. Coordinate-section maps                                        *)
(* ------------------------------------------------------------------ *)

(** [section_R v j t]: replace the j-th real coordinate of [v] by [t],
    keeping the imaginary part of that coordinate and all other
    coordinates fixed.  This is the line through [v] in the j-th
    real-direction. *)
Definition section_R {n : nat} (v : Cn n) (j : Fin.t n) (t : CReal) : Cn n :=
  cupd v j (mkC t (im (v j))).

(** [section_I v j t]: replace the j-th imaginary coordinate of [v] by [t],
    keeping the real part of that coordinate fixed. *)
Definition section_I {n : nat} (v : Cn n) (j : Fin.t n) (t : CReal) : Cn n :=
  cupd v j (mkC (re (v j)) t).

(** Sanity: at the original parameter, the section returns the original point. *)
Lemma section_R_id : forall {n} (v : Cn n) (j : Fin.t n),
    section_R v j (re (v j)) = cupd v j (mkC (re (v j)) (im (v j))).
Proof. intros. reflexivity. Qed.

Lemma section_I_id : forall {n} (v : Cn n) (j : Fin.t n),
    section_I v j (im (v j)) = cupd v j (mkC (re (v j)) (im (v j))).
Proof. intros. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * 2. Real partials of a Cn → CReal function                         *)
(* ------------------------------------------------------------------ *)

(** [partial_R_at u v j L]: the partial derivative of [u : Cn n → CReal]
    at the point [v], with respect to the real part of the j-th
    coordinate, equals [L].

    Defined by reducing along the real-direction section to a one-real-
    variable derivative, then invoking [Rderiv_at]. *)
Definition partial_R_at {n : nat}
    (u : Cn n -> CReal) (v : Cn n) (j : Fin.t n) (L : CReal) : Prop :=
  Rderiv_at (fun t => u (section_R v j t)) (re (v j)) L.

(** [partial_I_at u v j L]: partial of [u] w.r.t. the imaginary
    part of the j-th coordinate. *)
Definition partial_I_at {n : nat}
    (u : Cn n -> CReal) (v : Cn n) (j : Fin.t n) (L : CReal) : Prop :=
  Rderiv_at (fun t => u (section_I v j t)) (im (v j)) L.

(* ------------------------------------------------------------------ *)
(** * 3. Wirtinger partials of a Cn → C function                        *)
(* ------------------------------------------------------------------ *)

(** Wirtinger ∂/∂zⱼ on [f : Cⁿ → C]:

      ∂f/∂zⱼ = (1/2) ((∂u/∂xⱼ + ∂v/∂yⱼ) + i (∂v/∂xⱼ − ∂u/∂yⱼ))

    where [u = re ∘ f], [v = im ∘ f]. *)
Definition partial_z_at {n : nat}
    (f : Cn n -> CComplex) (v : Cn n) (j : Fin.t n) (L : CComplex) : Prop :=
  exists ux uy vx vy : CReal,
    partial_R_at (fun w => re (f w)) v j ux /\
    partial_I_at (fun w => re (f w)) v j uy /\
    partial_R_at (fun w => im (f w)) v j vx /\
    partial_I_at (fun w => im (f w)) v j vy /\
    re L = half * (ux + vy) /\
    im L = half * (vx - uy).

(** Wirtinger ∂/∂z̄ⱼ:

      ∂f/∂z̄ⱼ = (1/2) ((∂u/∂xⱼ − ∂v/∂yⱼ) + i (∂u/∂yⱼ + ∂v/∂xⱼ))
*)
Definition partial_zbar_at {n : nat}
    (f : Cn n -> CComplex) (v : Cn n) (j : Fin.t n) (L : CComplex) : Prop :=
  exists ux uy vx vy : CReal,
    partial_R_at (fun w => re (f w)) v j ux /\
    partial_I_at (fun w => re (f w)) v j uy /\
    partial_R_at (fun w => im (f w)) v j vx /\
    partial_I_at (fun w => im (f w)) v j vy /\
    re L = half * (ux - vy) /\
    im L = half * (uy + vx).

(** Sanity check: in the n = 1 case, [partial_z_at] is exactly the
    one-variable Wirtinger [del_at], modulo the section construction.
    The corresponding bridge requires that [section_R v Fin.F1 t]
    walk the real x-axis through [v Fin.F1] — which it does by
    construction. *)

(* ------------------------------------------------------------------ *)
(** * 4. Linearity lemmas                                               *)
(* ------------------------------------------------------------------ *)

(** ** 4.1  Linearity of the underlying [Rderiv_at]                     *)

(** A *uniform-tube* version of [Rderiv_at]: the derivative bound is
    witnessed by a single [delta] valid for every [eps].  Equivalent
    in classical settings, but constructively useful: it makes adding
    two derivatives mechanical (no minimum-of-two-CReals needed). *)
Definition Rderiv_at_uniform (f : CReal -> CReal) (x0 L : CReal)
    (delta : CReal) : Prop :=
  CRpositive delta /\
  forall eps : CReal,
    CRpositive eps ->
    forall x : CReal,
      (CReal_abs (x - x0) # 0) ->
      CRealLtProp (CReal_abs (x - x0)) delta ->
      CRealLtProp
        (CReal_abs ((f x - f x0) - (L * (x - x0))))
        (eps * CReal_abs (x - x0)).

(** Identity function has derivative 1: [Rderiv_at id x0 1]. *)
Lemma Rderiv_at_id :
  forall (x0 : CReal), Rderiv_at (fun x => x) x0 1.
Proof.
  intros x0 eps Heps.
  exists (inject_Q 1). split.
  - apply CRealLtForget. apply CRealLt_0_1.
  - intros x Hapart Hlt.
    apply CRealLtForget.
    assert (Heq : (x - x0) - 1 * (x - x0) == 0). { ring. }
    assert (Habs : CReal_abs ((x - x0) - 1 * (x - x0)) == 0).
    { rewrite Heq. apply CReal_abs_right. apply CRealLe_refl. }
    rewrite Habs.
    apply CReal_mult_lt_0_compat.
    + exact (CRealLtEpsilon _ _ Heps).
    + destruct Hapart as [h | h].
      * exfalso. exact (CRealLt_irrefl 0
          (CReal_le_lt_trans _ _ _ (CReal_abs_pos (x - x0)) h)).
      * exact h.
Qed.

(** Trivial sanity lemma: zero is the derivative of the constant
    function (analogue of Rderiv_const_at_zero already in
    ComplexAnalysis2.v, restated here for completeness). *)
Lemma Rderiv_at_const :
  forall (a x0 : CReal), Rderiv_at (fun _ => a) x0 0.
Proof.
  intros a x0 eps Heps.
  exists (inject_Q 1). split.
  - apply CRealLtForget. apply CRealLt_0_1.
  - intros x Hapart Hlt.
    apply CRealLtForget.
    assert (Heq : (a - a) - 0 * (x - x0) == 0). { ring. }
    assert (Habs : CReal_abs ((a - a) - 0 * (x - x0)) == 0).
    { rewrite Heq. apply CReal_abs_right. apply CRealLe_refl. }
    rewrite Habs.
    apply CReal_mult_lt_0_compat.
    + exact (CRealLtEpsilon _ _ Heps).
    + destruct Hapart as [h | h].
      * exfalso. exact (CRealLt_irrefl 0
          (CReal_le_lt_trans _ _ _ (CReal_abs_pos (x - x0)) h)).
      * exact h.
Qed.

(** ** 4.2  Linearity at the [partial_R_at] / [partial_I_at] level     *)

(** Constants have zero partial in every coordinate. *)
Lemma partial_R_at_const :
  forall {n} (c : CReal) (v : Cn n) (j : Fin.t n),
    partial_R_at (fun _ => c) v j 0.
Proof.
  intros n c v j. unfold partial_R_at.
  apply Rderiv_at_const.
Qed.

Lemma partial_I_at_const :
  forall {n} (c : CReal) (v : Cn n) (j : Fin.t n),
    partial_I_at (fun _ => c) v j 0.
Proof.
  intros n c v j. unfold partial_I_at.
  apply Rderiv_at_const.
Qed.

(** ** 4.3  Linearity at the Wirtinger level                            *)

(** [partial_z_at] of a constant: zero. *)
Lemma partial_z_at_const :
  forall {n} (c : CComplex) (v : Cn n) (j : Fin.t n),
    partial_z_at (fun _ => c) v j C0.
Proof.
  intros n c v j. unfold partial_z_at.
  exists 0, 0, 0, 0. repeat split.
  - apply (partial_R_at_const (re c) v j).
  - apply (partial_I_at_const (re c) v j).
  - apply (partial_R_at_const (im c) v j).
  - apply (partial_I_at_const (im c) v j).
  - simpl. apply CRealEq_eq. unfold half. ring.
  - simpl. apply CRealEq_eq. unfold half. ring.
Qed.

Lemma partial_zbar_at_const :
  forall {n} (c : CComplex) (v : Cn n) (j : Fin.t n),
    partial_zbar_at (fun _ => c) v j C0.
Proof.
  intros n c v j. unfold partial_zbar_at.
  exists 0, 0, 0, 0. repeat split.
  - apply (partial_R_at_const (re c) v j).
  - apply (partial_I_at_const (re c) v j).
  - apply (partial_R_at_const (im c) v j).
  - apply (partial_I_at_const (im c) v j).
  - simpl. apply CRealEq_eq. unfold half. ring.
  - simpl. apply CRealEq_eq. unfold half. ring.
Qed.

(** ** 4.4  Recovering Wirtinger values from real partials              *)

(** If the four real partials of [f] at [v] in coordinate [j] are
    [ux, uy, vx, vy], then [partial_z_at] holds at the value
    [del_value ux uy vx vy]. *)
Lemma partial_z_at_from_partials :
  forall {n} (f : Cn n -> CComplex) (v : Cn n) (j : Fin.t n)
         (ux uy vx vy : CReal),
    partial_R_at (fun w => re (f w)) v j ux ->
    partial_I_at (fun w => re (f w)) v j uy ->
    partial_R_at (fun w => im (f w)) v j vx ->
    partial_I_at (fun w => im (f w)) v j vy ->
    partial_z_at f v j (del_value ux uy vx vy).
Proof.
  intros n f v j ux uy vx vy Hux Huy Hvx Hvy.
  unfold partial_z_at, del_value.
  exists ux, uy, vx, vy. repeat split; assumption.
Qed.

(** Symmetric version for [partial_zbar_at]: the value is [dbar_value]. *)
Lemma partial_zbar_at_from_partials :
  forall {n} (f : Cn n -> CComplex) (v : Cn n) (j : Fin.t n)
         (ux uy vx vy : CReal),
    partial_R_at (fun w => re (f w)) v j ux ->
    partial_I_at (fun w => re (f w)) v j uy ->
    partial_R_at (fun w => im (f w)) v j vx ->
    partial_I_at (fun w => im (f w)) v j vy ->
    partial_zbar_at f v j (dbar_value ux uy vx vy).
Proof.
  intros n f v j ux uy vx vy Hux Huy Hvx Hvy.
  unfold partial_zbar_at, dbar_value.
  exists ux, uy, vx, vy. repeat split; assumption.
Qed.

(** A round-trip lemma: an L produced by [del_value] applied to four
    real partials does indeed witness [partial_z_at f v j].  This is
    just [partial_z_at_from_partials] re-packaged. *)
Lemma partial_z_at_del_value_witness :
  forall {n} (f : Cn n -> CComplex) (v : Cn n) (j : Fin.t n)
         (ux uy vx vy : CReal),
    partial_R_at (fun w => re (f w)) v j ux ->
    partial_I_at (fun w => re (f w)) v j uy ->
    partial_R_at (fun w => im (f w)) v j vx ->
    partial_I_at (fun w => im (f w)) v j vy ->
    re (del_value ux uy vx vy) = half * (ux + vy) /\
    im (del_value ux uy vx vy) = half * (vx - uy) /\
    partial_z_at f v j (del_value ux uy vx vy).
Proof.
  intros n f v j ux uy vx vy Hux Huy Hvx Hvy.
  split; [reflexivity|]. split; [reflexivity|].
  apply partial_z_at_from_partials; assumption.
Qed.

Lemma partial_zbar_at_dbar_value_witness :
  forall {n} (f : Cn n -> CComplex) (v : Cn n) (j : Fin.t n)
         (ux uy vx vy : CReal),
    partial_R_at (fun w => re (f w)) v j ux ->
    partial_I_at (fun w => re (f w)) v j uy ->
    partial_R_at (fun w => im (f w)) v j vx ->
    partial_I_at (fun w => im (f w)) v j vy ->
    re (dbar_value ux uy vx vy) = half * (ux - vy) /\
    im (dbar_value ux uy vx vy) = half * (uy + vx) /\
    partial_zbar_at f v j (dbar_value ux uy vx vy).
Proof.
  intros n f v j ux uy vx vy Hux Huy Hvx Hvy.
  split; [reflexivity|]. split; [reflexivity|].
  apply partial_zbar_at_from_partials; assumption.
Qed.

(** Helper: [(1/2) · 2 = 1] in CReal.  Used by the diagonal Wirtinger
    identities below. *)
Lemma half_times_two : half * (1 + 1) == 1.
Proof.
  unfold half.
  setoid_replace ((1 : CReal) + 1) with (inject_Q 2).
  - rewrite <- inject_Q_mult.
    transitivity (inject_Q 1).
    + apply inject_Q_morph. reflexivity.
    + reflexivity.
  - transitivity (inject_Q 1 + inject_Q 1).
    + reflexivity.
    + symmetry. transitivity (inject_Q (1 + 1)).
      * apply inject_Q_morph. reflexivity.
      * apply inject_Q_plus.
Qed.

(** ** 4.5  Coordinate-projection partials                              *)

(** Projection function [π_k : Cⁿ → C], [w ↦ w_k]. *)
Definition coord_proj {n : nat} (k : Fin.t n) : Cn n -> CComplex :=
  fun w => w k.

(** When [k ≠ j], [section_R v j t] leaves the k-th coordinate fixed:
    [(section_R v j t) k = v k]. *)
Lemma section_R_off_diag :
  forall {n} (v : Cn n) (j k : Fin.t n) (t : CReal),
    j <> k -> (section_R v j t) k = v k.
Proof.
  intros n v j k t Hne.
  unfold section_R, cupd.
  destruct (Fin.eq_dec k j) as [Heq | _].
  - subst k. exfalso. apply Hne. reflexivity.
  - reflexivity.
Qed.

Lemma section_I_off_diag :
  forall {n} (v : Cn n) (j k : Fin.t n) (t : CReal),
    j <> k -> (section_I v j t) k = v k.
Proof.
  intros n v j k t Hne.
  unfold section_I, cupd.
  destruct (Fin.eq_dec k j) as [Heq | _].
  - subst k. exfalso. apply Hne. reflexivity.
  - reflexivity.
Qed.

(** When [k = j], the section reads off [t] (resp. [im (v j)]). *)
Lemma section_R_diag_re :
  forall {n} (v : Cn n) (j : Fin.t n) (t : CReal),
    re ((section_R v j t) j) = t.
Proof.
  intros n v j t.
  unfold section_R, cupd.
  destruct (Fin.eq_dec j j) as [_ | Hne]; [reflexivity|].
  exfalso. apply Hne. reflexivity.
Qed.

Lemma section_R_diag_im :
  forall {n} (v : Cn n) (j : Fin.t n) (t : CReal),
    im ((section_R v j t) j) = im (v j).
Proof.
  intros n v j t.
  unfold section_R, cupd.
  destruct (Fin.eq_dec j j) as [_ | Hne]; [reflexivity|].
  exfalso. apply Hne. reflexivity.
Qed.

Lemma section_I_diag_re :
  forall {n} (v : Cn n) (j : Fin.t n) (t : CReal),
    re ((section_I v j t) j) = re (v j).
Proof.
  intros n v j t.
  unfold section_I, cupd.
  destruct (Fin.eq_dec j j) as [_ | Hne]; [reflexivity|].
  exfalso. apply Hne. reflexivity.
Qed.

Lemma section_I_diag_im :
  forall {n} (v : Cn n) (j : Fin.t n) (t : CReal),
    im ((section_I v j t) j) = t.
Proof.
  intros n v j t.
  unfold section_I, cupd.
  destruct (Fin.eq_dec j j) as [_ | Hne]; [reflexivity|].
  exfalso. apply Hne. reflexivity.
Qed.

(** ∂(πk)/∂xⱼ = 1 if j = k, else 0; at the real-part component. *)
Lemma partial_R_at_coord_proj_diag_re :
  forall {n} (v : Cn n) (j : Fin.t n),
    partial_R_at (fun w => re (coord_proj j w)) v j 1.
Proof.
  intros n v j. unfold partial_R_at.
  (* the function (fun t => re (coord_proj j (section_R v j t)))
     reduces to (fun t => t) by section_R_diag_re. *)
  assert (Hext : forall t, re (coord_proj j (section_R v j t)) = t).
  { intro t. unfold coord_proj. apply section_R_diag_re. }
  (* Use Rderiv_at_id with this substitution. *)
  intros eps Heps.
  destruct (Rderiv_at_id (re (v j)) eps Heps) as [delta [Hd Hbnd]].
  exists delta. split; [exact Hd|].
  intros x Hap Hlt.
  rewrite Hext.
  rewrite (Hext (re (v j))).
  exact (Hbnd x Hap Hlt).
Qed.

Lemma partial_R_at_coord_proj_off_diag_re :
  forall {n} (v : Cn n) (j k : Fin.t n),
    j <> k ->
    partial_R_at (fun w => re (coord_proj k w)) v j 0.
Proof.
  intros n v j k Hne. unfold partial_R_at.
  (* re (coord_proj k (section_R v j t)) = re (v k) — constant in t. *)
  assert (Hext : forall t, re (coord_proj k (section_R v j t)) = re (v k)).
  { intro t. unfold coord_proj. f_equal. apply section_R_off_diag. exact Hne. }
  intros eps Heps.
  destruct (Rderiv_at_const (re (v k)) (re (v j)) eps Heps) as [delta [Hd Hbnd]].
  exists delta. split; [exact Hd|].
  intros x Hap Hlt.
  rewrite Hext, (Hext (re (v j))).
  exact (Hbnd x Hap Hlt).
Qed.

(** Diagonal imaginary partial: ∂(re πj)/∂yⱼ = 0
    (real part of πj depends only on x_j, not y_j). *)
Lemma partial_I_at_coord_proj_diag_re :
  forall {n} (v : Cn n) (j : Fin.t n),
    partial_I_at (fun w => re (coord_proj j w)) v j 0.
Proof.
  intros n v j. unfold partial_I_at.
  assert (Hext : forall t, re (coord_proj j (section_I v j t)) = re (v j)).
  { intro t. unfold coord_proj. apply section_I_diag_re. }
  intros eps Heps.
  destruct (Rderiv_at_const (re (v j)) (im (v j)) eps Heps) as [delta [Hd Hbnd]].
  exists delta. split; [exact Hd|].
  intros x Hap Hlt.
  rewrite Hext, (Hext (im (v j))).
  exact (Hbnd x Hap Hlt).
Qed.

(** ∂(im πj)/∂xⱼ = 0 (imaginary part of πj depends only on y_j). *)
Lemma partial_R_at_coord_proj_diag_im :
  forall {n} (v : Cn n) (j : Fin.t n),
    partial_R_at (fun w => im (coord_proj j w)) v j 0.
Proof.
  intros n v j. unfold partial_R_at.
  assert (Hext : forall t, im (coord_proj j (section_R v j t)) = im (v j)).
  { intro t. unfold coord_proj. apply section_R_diag_im. }
  intros eps Heps.
  destruct (Rderiv_at_const (im (v j)) (re (v j)) eps Heps) as [delta [Hd Hbnd]].
  exists delta. split; [exact Hd|].
  intros x Hap Hlt.
  rewrite Hext, (Hext (re (v j))).
  exact (Hbnd x Hap Hlt).
Qed.

(** ∂(im πj)/∂yⱼ = 1. *)
Lemma partial_I_at_coord_proj_diag_im :
  forall {n} (v : Cn n) (j : Fin.t n),
    partial_I_at (fun w => im (coord_proj j w)) v j 1.
Proof.
  intros n v j. unfold partial_I_at.
  assert (Hext : forall t, im (coord_proj j (section_I v j t)) = t).
  { intro t. unfold coord_proj. apply section_I_diag_im. }
  intros eps Heps.
  destruct (Rderiv_at_id (im (v j)) eps Heps) as [delta [Hd Hbnd]].
  exists delta. split; [exact Hd|].
  intros x Hap Hlt.
  rewrite Hext, (Hext (im (v j))).
  exact (Hbnd x Hap Hlt).
Qed.

(** Off-diagonal real-of-projection partials are zero (k ≠ j). *)
Lemma partial_R_at_coord_proj_off_diag_im :
  forall {n} (v : Cn n) (j k : Fin.t n),
    j <> k ->
    partial_R_at (fun w => im (coord_proj k w)) v j 0.
Proof.
  intros n v j k Hne. unfold partial_R_at.
  assert (Hext : forall t, im (coord_proj k (section_R v j t)) = im (v k)).
  { intro t. unfold coord_proj. f_equal. apply section_R_off_diag. exact Hne. }
  intros eps Heps.
  destruct (Rderiv_at_const (im (v k)) (re (v j)) eps Heps) as [delta [Hd Hbnd]].
  exists delta. split; [exact Hd|].
  intros x Hap Hlt.
  rewrite Hext, (Hext (re (v j))).
  exact (Hbnd x Hap Hlt).
Qed.

Lemma partial_I_at_coord_proj_off_diag_re :
  forall {n} (v : Cn n) (j k : Fin.t n),
    j <> k ->
    partial_I_at (fun w => re (coord_proj k w)) v j 0.
Proof.
  intros n v j k Hne. unfold partial_I_at.
  assert (Hext : forall t, re (coord_proj k (section_I v j t)) = re (v k)).
  { intro t. unfold coord_proj. f_equal. apply section_I_off_diag. exact Hne. }
  intros eps Heps.
  destruct (Rderiv_at_const (re (v k)) (im (v j)) eps Heps) as [delta [Hd Hbnd]].
  exists delta. split; [exact Hd|].
  intros x Hap Hlt.
  rewrite Hext, (Hext (im (v j))).
  exact (Hbnd x Hap Hlt).
Qed.

Lemma partial_I_at_coord_proj_off_diag_im :
  forall {n} (v : Cn n) (j k : Fin.t n),
    j <> k ->
    partial_I_at (fun w => im (coord_proj k w)) v j 0.
Proof.
  intros n v j k Hne. unfold partial_I_at.
  assert (Hext : forall t, im (coord_proj k (section_I v j t)) = im (v k)).
  { intro t. unfold coord_proj. f_equal. apply section_I_off_diag. exact Hne. }
  intros eps Heps.
  destruct (Rderiv_at_const (im (v k)) (im (v j)) eps Heps) as [delta [Hd Hbnd]].
  exists delta. split; [exact Hd|].
  intros x Hap Hlt.
  rewrite Hext, (Hext (im (v j))).
  exact (Hbnd x Hap Hlt).
Qed.

(** The Kronecker δ at the Wirtinger level:

      ∂(πj)/∂zj = 1                ∂(πj)/∂z̄j = 0
      ∂(πk)/∂zj = 0   (k ≠ j)      ∂(πk)/∂z̄j = 0    (k ≠ j)

    These are the holomorphic identities that build every entry of
    the complex Jacobian of the identity Cⁿ → Cⁿ map. *)
Lemma partial_z_at_coord_proj_diag :
  forall {n} (v : Cn n) (j : Fin.t n),
    partial_z_at (coord_proj j) v j C1.
Proof.
  intros n v j. unfold partial_z_at.
  exists 1, 0, 0, 1. repeat split.
  - apply partial_R_at_coord_proj_diag_re.
  - apply partial_I_at_coord_proj_diag_re.
  - apply partial_R_at_coord_proj_diag_im.
  - apply partial_I_at_coord_proj_diag_im.
  - simpl. apply CRealEq_eq. symmetry. apply half_times_two.
  - simpl. apply CRealEq_eq. unfold half. ring.
Qed.

Lemma partial_zbar_at_coord_proj_diag :
  forall {n} (v : Cn n) (j : Fin.t n),
    partial_zbar_at (coord_proj j) v j C0.
Proof.
  intros n v j. unfold partial_zbar_at.
  exists 1, 0, 0, 1. repeat split.
  - apply partial_R_at_coord_proj_diag_re.
  - apply partial_I_at_coord_proj_diag_re.
  - apply partial_R_at_coord_proj_diag_im.
  - apply partial_I_at_coord_proj_diag_im.
  - simpl. apply CRealEq_eq. unfold half. ring.
  - simpl. apply CRealEq_eq. unfold half. ring.
Qed.

Lemma partial_z_at_coord_proj_off_diag :
  forall {n} (v : Cn n) (j k : Fin.t n),
    j <> k ->
    partial_z_at (coord_proj k) v j C0.
Proof.
  intros n v j k Hne. unfold partial_z_at.
  exists 0, 0, 0, 0. repeat split.
  - apply partial_R_at_coord_proj_off_diag_re. exact Hne.
  - apply partial_I_at_coord_proj_off_diag_re. exact Hne.
  - apply partial_R_at_coord_proj_off_diag_im. exact Hne.
  - apply partial_I_at_coord_proj_off_diag_im. exact Hne.
  - simpl. apply CRealEq_eq. unfold half. ring.
  - simpl. apply CRealEq_eq. unfold half. ring.
Qed.

Lemma partial_zbar_at_coord_proj_off_diag :
  forall {n} (v : Cn n) (j k : Fin.t n),
    j <> k ->
    partial_zbar_at (coord_proj k) v j C0.
Proof.
  intros n v j k Hne. unfold partial_zbar_at.
  exists 0, 0, 0, 0. repeat split.
  - apply partial_R_at_coord_proj_off_diag_re. exact Hne.
  - apply partial_I_at_coord_proj_off_diag_re. exact Hne.
  - apply partial_R_at_coord_proj_off_diag_im. exact Hne.
  - apply partial_I_at_coord_proj_off_diag_im. exact Hne.
  - simpl. apply CRealEq_eq. unfold half. ring.
  - simpl. apply CRealEq_eq. unfold half. ring.
Qed.

(* ------------------------------------------------------------------ *)
(** * 5. Cauchy–Riemann at the Wirtinger level                          *)
(* ------------------------------------------------------------------ *)

(** A function [f : Cⁿ → C] is holomorphic in the j-th coordinate
    at [v] iff its j-th Wirtinger ∂̄-partial vanishes there. *)
Definition holomorphic_in_var_wirtinger {n : nat}
    (f : Cn n -> CComplex) (v : Cn n) (j : Fin.t n) : Prop :=
  partial_zbar_at f v j C0.

(** Sanity: a constant function is holomorphic in every coordinate. *)
Lemma holomorphic_in_var_const :
  forall {n} (c : CComplex) (v : Cn n) (j : Fin.t n),
    holomorphic_in_var_wirtinger (fun _ => c) v j.
Proof.
  intros n c v j. unfold holomorphic_in_var_wirtinger.
  apply partial_zbar_at_const.
Qed.

(* ------------------------------------------------------------------ *)
(** * 6. Matrix-of-partials helper                                      *)
(* ------------------------------------------------------------------ *)

From Stdlib Require Import Lists.List.
Import ListNotations.

(** Build an n×n matrix from a function [Fin.t n → Fin.t n → CComplex].
    Used by [complex_jacobian_of] to turn an explicit derivative oracle
    into a [Mat CComplex]. *)
Fixpoint fin_seq (n : nat) : list (Fin.t n) :=
  match n with
  | O => []
  | S n' => Fin.F1 :: List.map Fin.FS (fin_seq n')
  end.

Definition mat_of_fn (n : nat) (g : Fin.t n -> Fin.t n -> CComplex)
    : list (list CComplex) :=
  List.map (fun i => List.map (fun j => g i j) (fin_seq n)) (fin_seq n).

(** Sanity: the matrix has [n] rows. *)
Lemma mat_of_fn_length :
  forall n g, List.length (mat_of_fn n g) = List.length (fin_seq n).
Proof.
  intros n g. unfold mat_of_fn. apply List.length_map.
Qed.

(** Sanity: every row has [n] entries. *)
Lemma mat_of_fn_row_length :
  forall n g row, List.In row (mat_of_fn n g) ->
                  List.length row = List.length (fin_seq n).
Proof.
  intros n g row Hin.
  unfold mat_of_fn in Hin.
  apply List.in_map_iff in Hin.
  destruct Hin as [i [Heq _]].
  subst row.
  apply List.length_map.
Qed.

Lemma fin_seq_length : forall n, List.length (fin_seq n) = n.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - simpl. rewrite List.length_map. f_equal. exact IH.
Qed.

(** The standard [n × n] shape of [mat_of_fn n g]. *)
Lemma mat_of_fn_shape :
  forall n g,
    List.length (mat_of_fn n g) = n /\
    forall row, List.In row (mat_of_fn n g) -> List.length row = n.
Proof.
  intros n g. split.
  - rewrite mat_of_fn_length. apply fin_seq_length.
  - intros row Hin. rewrite (mat_of_fn_row_length n g row Hin).
    apply fin_seq_length.
Qed.
