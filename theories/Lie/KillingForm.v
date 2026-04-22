(** * Lie/KillingForm.v
    Killing form, semisimplicity criterion, and radical.

    K(x, y) := Tr(ad x ∘ ad y)

    Main results:
    - K bilinear, symmetric, and invariant: K([x,y],z) = K(x,[y,z])
    - radK(L) is an ideal
    - L semisimple iff K nondegenerate

    References: Humphreys §5, representations.org Part XVI. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.Lie.Ideals.
Require Import CAG.Lie.Derivations.
Require Import CAG.Lie.Nilpotent.
Require Import CAG.Lie.Solvable.
Require Import CAG.Lie.Radical.

(* ================================================================== *)
(** * 1. Field arithmetic helpers                                      *)
(* ================================================================== *)

(** neg 0 = 0. *)
Lemma ring_neg_zero : forall {F : Type} (fld : Field F),
    fld.(cr_neg) fld.(cr_zero) = fld.(cr_zero).
Proof.
  intros F fld.
  (* 0 + neg(0) = 0, so neg(0) = 0 *)
  assert (H := fld.(cr_add_neg) fld.(cr_zero)).
  (* H : cr_add (cr_zero) (cr_neg cr_zero) = cr_zero *)
  rewrite fld.(cr_add_comm) in H.
  (* H : cr_add (cr_neg cr_zero) cr_zero = cr_zero *)
  rewrite fld.(cr_add_zero) in H.
  (* H : cr_neg cr_zero = cr_zero *)
  exact H.
Qed.

(** a * 0 = 0. *)
Lemma ring_mul_zero_r : forall {F : Type} (fld : Field F) (a : F),
    fld.(cr_mul) a fld.(cr_zero) = fld.(cr_zero).
Proof.
  intros F fld a.
  (* a*0 = a*(0+0) = a*0 + a*0, so by cancellation a*0 = 0 *)
  assert (Hd : fld.(cr_mul) a fld.(cr_zero) =
               fld.(cr_add) (fld.(cr_mul) a fld.(cr_zero)) (fld.(cr_mul) a fld.(cr_zero))).
  { rewrite <- fld.(cr_distrib). rewrite fld.(cr_add_zero). reflexivity. }
  assert (Hn := fld.(cr_add_neg) (fld.(cr_mul) a fld.(cr_zero))).
  assert (Heq :
    fld.(cr_add)
      (fld.(cr_add) (fld.(cr_mul) a fld.(cr_zero)) (fld.(cr_mul) a fld.(cr_zero)))
      (fld.(cr_neg) (fld.(cr_mul) a fld.(cr_zero))) = fld.(cr_zero)).
  { rewrite <- Hd. exact Hn. }
  rewrite <- fld.(cr_add_assoc) in Heq.
  rewrite Hn in Heq.
  rewrite fld.(cr_add_zero) in Heq.
  exact Heq.
Qed.

(** 0 * a = 0. *)
Lemma ring_mul_zero_l : forall {F : Type} (fld : Field F) (a : F),
    fld.(cr_mul) fld.(cr_zero) a = fld.(cr_zero).
Proof.
  intros F fld a.
  rewrite fld.(cr_mul_comm). apply ring_mul_zero_r.
Qed.

(** 0 + a = a. *)
Lemma ring_add_zero_l : forall {F : Type} (fld : Field F) (a : F),
    fld.(cr_add) fld.(cr_zero) a = a.
Proof.
  intros F fld a.
  rewrite fld.(cr_add_comm). apply fld.(cr_add_zero).
Qed.

(* ================================================================== *)
(** * 2. Trace on endomorphisms                                        *)
(* ================================================================== *)

(** Axiomatized trace functional on endomorphisms of L. *)
Parameter trace_end : forall {F : Type} (fld : Field F) {L : Type}
    (la : LieAlgebraF fld L), (L -> L) -> F.

Axiom trace_end_add : forall {F : Type} (fld : Field F) {L : Type}
    (la : LieAlgebraF fld L) (f g : L -> L),
    trace_end fld la (fun z => vsF_add (laF_vs la) (f z) (g z)) =
    fld.(cr_add) (trace_end fld la f) (trace_end fld la g).

Axiom trace_end_scale : forall {F : Type} (fld : Field F) {L : Type}
    (la : LieAlgebraF fld L) (c : F) (f : L -> L),
    trace_end fld la (fun z => vsF_scale (laF_vs la) c (f z)) =
    fld.(cr_mul) c (trace_end fld la f).

Axiom trace_end_neg : forall {F : Type} (fld : Field F) {L : Type}
    (la : LieAlgebraF fld L) (f : L -> L),
    trace_end fld la (fun z => vsF_neg (laF_vs la) (f z)) =
    fld.(cr_neg) (trace_end fld la f).

Axiom trace_end_cyclic : forall {F : Type} (fld : Field F) {L : Type}
    (la : LieAlgebraF fld L) (f g : L -> L),
    trace_end fld la (fun z => f (g z)) =
    trace_end fld la (fun z => g (f z)).

Axiom trace_end_ext : forall {F : Type} (fld : Field F) {L : Type}
    (la : LieAlgebraF fld L) (f g : L -> L),
    (forall z, f z = g z) ->
    trace_end fld la f = trace_end fld la g.

(** scale 0_F v = 0_V (scale by zero scalar). *)
Lemma vsF_scale_zero_s : forall {F : Type} (fld : Field F) {V : Type}
    (vs : VectorSpaceF fld V) (v : V),
    vsF_scale vs fld.(cr_zero) v = vsF_zero vs.
Proof.
  intros F fld V vs v.
  (* 0*v = (0+0)*v = 0*v + 0*v, so 0*v = 0 by cancellation *)
  assert (Hd : vsF_scale vs fld.(cr_zero) v =
               vsF_add vs (vsF_scale vs fld.(cr_zero) v) (vsF_scale vs fld.(cr_zero) v)).
  { rewrite <- vs.(vsF_scale_add_s). rewrite fld.(cr_add_zero). reflexivity. }
  apply vsF_add_cancel_double. symmetry. exact Hd.
Qed.

(** Tr(const 0) = 0. *)
Lemma trace_end_zero : forall {F : Type} (fld : Field F) {L : Type}
    (la : LieAlgebraF fld L),
    trace_end fld la (fun _ => vsF_zero (laF_vs la)) = fld.(cr_zero).
Proof.
  intros F fld L la.
  rewrite (trace_end_ext fld la _ (fun z => vsF_scale (laF_vs la) fld.(cr_zero) z)).
  - rewrite trace_end_scale. apply ring_mul_zero_l.
  - intro z. symmetry. apply vsF_scale_zero_s.
Qed.

(* ================================================================== *)
(** * 3. The Killing form                                              *)
(* ================================================================== *)

Definition killing_form {F : Type} (fld : Field F) {L : Type}
    (la : LieAlgebraF fld L) (x y : L) : F :=
  trace_end fld la (fun z => ad la x (ad la y z)).

(* ================================================================== *)
(** * 4. Bilinearity of K                                             *)
(* ================================================================== *)

Lemma killing_linear_l : forall {F : Type} (fld : Field F) {L : Type}
    (la : LieAlgebraF fld L) (a : F) (x y z : L),
    killing_form fld la (vsF_add (laF_vs la) (vsF_scale (laF_vs la) a x) y) z =
    fld.(cr_add) (fld.(cr_mul) a (killing_form fld la x z)) (killing_form fld la y z).
Proof.
  intros F fld L la a x y z. unfold killing_form, ad.
  rewrite (trace_end_ext fld la
    (fun w => laF_bracket la
      (vsF_add (laF_vs la) (vsF_scale (laF_vs la) a x) y) (laF_bracket la z w))
    (fun w => vsF_add (laF_vs la)
      (vsF_scale (laF_vs la) a (laF_bracket la x (laF_bracket la z w)))
      (laF_bracket la y (laF_bracket la z w)))).
  - rewrite trace_end_add, trace_end_scale. reflexivity.
  - intro w. rewrite la.(laF_bracket_add_l), la.(laF_bracket_scale_l). reflexivity.
Qed.

Lemma killing_linear_r : forall {F : Type} (fld : Field F) {L : Type}
    (la : LieAlgebraF fld L) (a : F) (x y z : L),
    killing_form fld la x (vsF_add (laF_vs la) (vsF_scale (laF_vs la) a y) z) =
    fld.(cr_add) (fld.(cr_mul) a (killing_form fld la x y)) (killing_form fld la x z).
Proof.
  intros F fld L la a x y z. unfold killing_form, ad.
  rewrite (trace_end_ext fld la
    (fun w => laF_bracket la x
      (laF_bracket la (vsF_add (laF_vs la) (vsF_scale (laF_vs la) a y) z) w))
    (fun w => vsF_add (laF_vs la)
      (vsF_scale (laF_vs la) a (laF_bracket la x (laF_bracket la y w)))
      (laF_bracket la x (laF_bracket la z w)))).
  - rewrite trace_end_add, trace_end_scale. reflexivity.
  - intro w.
    rewrite la.(laF_bracket_add_l), la.(laF_bracket_scale_l).
    rewrite la.(laF_bracket_add_r), la.(laF_bracket_scale_r). reflexivity.
Qed.

(* ================================================================== *)
(** * 5. Symmetry of K                                                *)
(* ================================================================== *)

Lemma killing_symm : forall {F : Type} (fld : Field F) {L : Type}
    (la : LieAlgebraF fld L) (x y : L),
    killing_form fld la x y = killing_form fld la y x.
Proof.
  intros F fld L la x y. unfold killing_form, ad. apply trace_end_cyclic.
Qed.

(* ================================================================== *)
(** * 6. Invariance of K                                              *)
(* ================================================================== *)

Lemma killing_invariant : forall {F : Type} (fld : Field F) {L : Type}
    (la : LieAlgebraF fld L) (x y z : L),
    killing_form fld la (laF_bracket la x y) z =
    killing_form fld la x (laF_bracket la y z).
Proof.
  intros F fld L la x y z. unfold killing_form, ad.
  rewrite (trace_end_ext fld la
    (fun w => laF_bracket la (laF_bracket la x y) (laF_bracket la z w))
    (fun w => vsF_add (laF_vs la)
      (laF_bracket la x (laF_bracket la y (laF_bracket la z w)))
      (vsF_neg (laF_vs la)
        (laF_bracket la y (laF_bracket la x (laF_bracket la z w)))))).
  2: { intro w. apply ad_hom. }
  rewrite (trace_end_ext fld la
    (fun w => laF_bracket la x (laF_bracket la (laF_bracket la y z) w))
    (fun w => vsF_add (laF_vs la)
      (laF_bracket la x (laF_bracket la y (laF_bracket la z w)))
      (vsF_neg (laF_vs la)
        (laF_bracket la x (laF_bracket la z (laF_bracket la y w)))))).
  2: { intro w.
       rewrite ad_hom, la.(laF_bracket_add_r), laF_bracket_neg_r.
       reflexivity. }
  rewrite trace_end_add, trace_end_add. f_equal.
  rewrite trace_end_neg, trace_end_neg. f_equal.
  (* Tr(ady∘adx∘adz) = Tr(adx∘adz∘ady) by cyclic *)
  symmetry.
  exact (trace_end_cyclic fld la
    (fun w => laF_bracket la x (laF_bracket la z w))
    (fun w => laF_bracket la y w)).
Qed.

(* ================================================================== *)
(** * 7. Radical of K                                                 *)
(* ================================================================== *)

Definition IsKillingRadical {F : Type} (fld : Field F) {L : Type}
    (la : LieAlgebraF fld L) (x : L) : Prop :=
  forall y : L, killing_form fld la x y = fld.(cr_zero).

Lemma killing_zero_l : forall {F : Type} (fld : Field F) {L : Type}
    (la : LieAlgebraF fld L) (y : L),
    killing_form fld la (la_zero la) y = fld.(cr_zero).
Proof.
  intros F fld L la y. unfold killing_form, ad.
  rewrite (trace_end_ext fld la _ (fun _ => vsF_zero (laF_vs la))).
  - apply trace_end_zero.
  - intro z. rewrite laF_bracket_zero_l. reflexivity.
Qed.

Lemma killing_neg_l : forall {F : Type} (fld : Field F) {L : Type}
    (la : LieAlgebraF fld L) (x y : L),
    killing_form fld la (la_neg la x) y =
    fld.(cr_neg) (killing_form fld la x y).
Proof.
  intros F fld L la x y. unfold killing_form, ad.
  rewrite (trace_end_ext fld la _
    (fun z => vsF_neg (laF_vs la) (laF_bracket la x (laF_bracket la y z)))).
  - apply trace_end_neg.
  - intro z. apply laF_bracket_neg_l.
Qed.

Lemma killing_scale_l : forall {F : Type} (fld : Field F) {L : Type}
    (la : LieAlgebraF fld L) (a : F) (x y : L),
    killing_form fld la (vsF_scale (laF_vs la) a x) y =
    fld.(cr_mul) a (killing_form fld la x y).
Proof.
  intros F fld L la a x y. unfold killing_form, ad.
  rewrite (trace_end_ext fld la _
    (fun z => vsF_scale (laF_vs la) a (laF_bracket la x (laF_bracket la y z)))).
  - apply trace_end_scale.
  - intro z. apply la.(laF_bracket_scale_l).
Qed.

(** radK(L) is an ideal of L. *)
Lemma killing_radical_ideal : forall {F : Type} (fld : Field F) {L : Type}
    (la : LieAlgebraF fld L),
    IsIdeal la (IsKillingRadical fld la).
Proof.
  intros F fld L la. constructor.
  - intro y. apply killing_zero_l.
  - intros x x' Hx Hx' y.
    unfold IsKillingRadical in *.
    unfold killing_form, ad.
    rewrite (trace_end_ext fld la _
      (fun z => vsF_add (laF_vs la)
        (laF_bracket la x (laF_bracket la y z))
        (laF_bracket la x' (laF_bracket la y z)))).
    + rewrite trace_end_add.
      unfold killing_form, ad in Hx, Hx'.
      rewrite (Hx y), (Hx' y).
      apply fld.(cr_add_zero).
    + intro z. rewrite <- la.(laF_bracket_add_l). reflexivity.
  - intros x Hx y.
    unfold IsKillingRadical in *.
    rewrite killing_neg_l, (Hx y).
    apply ring_neg_zero.
  - intros a x Hx y.
    unfold IsKillingRadical in *.
    rewrite killing_scale_l, (Hx y).
    apply ring_mul_zero_r.
  - intros x z Hx y.
    unfold IsKillingRadical in *.
    rewrite killing_invariant, killing_symm, killing_invariant.
    apply Hx.
Qed.

(* ================================================================== *)
(** * 8. Semisimplicity criterion                                      *)
(* ================================================================== *)

Definition KillingNondegenerate {F : Type} (fld : Field F) {L : Type}
    (la : LieAlgebraF fld L) : Prop :=
  forall x, IsKillingRadical fld la x -> x = vsF_zero (laF_vs la).

(** Cartan's criterion: L semisimple iff K nondegenerate. *)
Axiom killing_nondeg_iff_semisimple :
  forall {F : Type} (fld : Field F) {L : Type}
    (la : LieAlgebraF fld L),
    KillingNondegenerate fld la <-> IsSemisimple la.

Lemma killing_nondeg_implies_semisimple :
  forall {F : Type} (fld : Field F) {L : Type}
    (la : LieAlgebraF fld L),
    KillingNondegenerate fld la -> IsSemisimple la.
Proof.
  intros F fld L la H.
  exact (proj1 (killing_nondeg_iff_semisimple fld la) H).
Qed.

Lemma semisimple_implies_killing_nondeg :
  forall {F : Type} (fld : Field F) {L : Type}
    (la : LieAlgebraF fld L),
    IsSemisimple la -> KillingNondegenerate fld la.
Proof.
  intros F fld L la H.
  exact (proj2 (killing_nondeg_iff_semisimple fld la) H).
Qed.

(* ================================================================== *)
(** * 9. Killing form and nilpotency/solvability                      *)
(* ================================================================== *)

(** Trace of a nilpotent endomorphism is zero (characteristic 0). *)
Axiom trace_nilpotent_zero : forall {F : Type} (fld : Field F) {L : Type}
    (la : LieAlgebraF fld L) (f : L -> L),
    (exists n, forall z, Nat.iter (S n) f z = vsF_zero (laF_vs la)) ->
    trace_end fld la f = fld.(cr_zero).

(** Exercise 5.1 (Humphreys): Killing form of nilpotent L is identically zero.
    Proof: by Engel's theorem, choose basis making all adx strictly upper
    triangular; products of such matrices also have trace 0. *)
Axiom killing_nilpotent_zero : forall {F : Type} (fld : Field F) {L : Type}
    (la : LieAlgebraF fld L),
    IsNilpotent la ->
    forall x y, killing_form fld la x y = fld.(cr_zero).

(** Exercise 5.2 (Humphreys): L solvable iff [L,L] ⊆ radK(L). *)
Axiom solvable_iff_derived_in_radical :
  forall {F : Type} (fld : Field F) {L : Type}
    (la : LieAlgebraF fld L),
    IsSolvable la <->
    (forall x y z : L, killing_form fld la (laF_bracket la x y) z = fld.(cr_zero)).

(* ================================================================== *)
(** * 10. Restriction of the Killing form to ideals                    *)
(* ================================================================== *)

(** Key linear-algebra fact: if f : L → L maps into a subspace I (stable
    subspace, i.e., I is an ideal), then Tr_L(f) = Tr_I(f|_I).
    This is the fact Humphreys uses without proof in §5.1.
    We axiomatize it here; it holds in any finite-dimensional vector space. *)
Axiom trace_restrict :
  forall {F : Type} (fld : Field F) {L I : Type}
    (la   : LieAlgebraF fld L)
    (la_I : LieAlgebraF fld I)
    (emb  : I -> L)
    (f    : L -> L)
    (f_I  : I -> I)
    (Hemb : forall i j, emb (laF_bracket la_I i j) = laF_bracket la (emb i) (emb j))
    (Himg : forall z, exists i, emb i = f z)
    (Hcom : forall i, emb (f_I i) = f (emb i)),
    trace_end fld la f = trace_end fld la_I f_I.

(** Restriction lemma (Humphreys §5.1):
    If I is an ideal of L and la_I is the inherited Lie algebra structure on I,
    then K_L(x, y) = K_I(x, y) for all x, y ∈ I.

    Proof sketch:
    - For x, y ∈ I, ad_L x ∘ ad_L y maps L into I
      (since [y,z] ∈ L and then [x,[y,z]] ∈ I as x ∈ I is an ideal element).
    - By trace_restrict, Tr_L(ad_L x ∘ ad_L y) = Tr_I(ad_I x ∘ ad_I y). *)
Lemma killing_ideal_restrict :
  forall {F : Type} (fld : Field F) {L I : Type}
    (la   : LieAlgebraF fld L)
    (la_I : LieAlgebraF fld I)
    (emb  : I -> L)
    (Hemb : forall i j, emb (laF_bracket la_I i j) = laF_bracket la (emb i) (emb j))
    (HI   : IsIdeal la (fun x => exists i, emb i = x))
    (x y  : I),
    killing_form fld la (emb x) (emb y) = killing_form fld la_I x y.
Proof.
  intros F fld L I la la_I emb Hemb HI x y.
  unfold killing_form, ad.
  (* The endomorphism f := (z ↦ [emb x, [emb y, z]]) maps L into image(emb).
     The corresponding endomorphism on I is (i ↦ [x, [y, i]]). *)
  apply (trace_restrict fld la la_I emb
    (fun z => laF_bracket la (emb x) (laF_bracket la (emb y) z))
    (fun i => laF_bracket la_I x (laF_bracket la_I y i))).
  - exact Hemb.
  - intro z.
    (* emb x ∈ image(emb), so by ideal_bracket_l: [[emb y,z], emb x] ∈ I *)
    pose proof HI.(ideal_bracket_l) (laF_bracket la (emb y) z) (emb x)
      (ex_intro _ x eq_refl) as H1.
    (* By anticomm: [emb x, [emb y, z]] = -[[emb y,z], emb x] *)
    pose proof HI.(ideal_neg) _ H1 as H2.
    rewrite <- (laF_anticomm la (emb x) (laF_bracket la (emb y) z)) in H2.
    exact H2.
  - intro i.
    (* emb ([x, [y, i]]) = [emb x, emb ([y, i])] = [emb x, [emb y, emb i]] *)
    rewrite Hemb, Hemb. reflexivity.
Qed.

(** Corollary: in a solvable algebra, the derived algebra lies in radK. *)
Corollary solvable_derived_in_killing_radical :
  forall {F : Type} (fld : Field F) {L : Type}
    (la : LieAlgebraF fld L),
    IsSolvable la ->
    forall x y : L, IsKillingRadical fld la (laF_bracket la x y).
Proof.
  intros F fld L la Hsol x y z.
  exact (proj1 (solvable_iff_derived_in_radical fld la) Hsol x y z).
Qed.
