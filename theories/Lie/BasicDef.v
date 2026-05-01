(** * Lie/BasicDef.v
    Abstract Lie algebras over a commutative field F. *)

Require Import CAG.Galois.Field.

Record VectorSpaceF {F : Type} (fld : Field F) (V : Type) : Type := {
  vsF_add   : V -> V -> V;
  vsF_zero  : V;
  vsF_neg   : V -> V;
  vsF_scale : F -> V -> V;
  vsF_add_assoc  : forall u v w,
    vsF_add u (vsF_add v w) = vsF_add (vsF_add u v) w;
  vsF_add_comm   : forall u v, vsF_add u v = vsF_add v u;
  vsF_add_zero_r : forall v, vsF_add v vsF_zero = v;
  vsF_add_neg_r  : forall v, vsF_add v (vsF_neg v) = vsF_zero;
  vsF_scale_one   : forall v, vsF_scale (cr_one fld) v = v;
  vsF_scale_mul   : forall a b v,
    vsF_scale a (vsF_scale b v) = vsF_scale (cr_mul fld a b) v;
  vsF_scale_add_v : forall a u v,
    vsF_scale a (vsF_add u v) = vsF_add (vsF_scale a u) (vsF_scale a v);
  vsF_scale_add_s : forall a b v,
    vsF_scale (cr_add fld a b) v = vsF_add (vsF_scale a v) (vsF_scale b v);
}.

Arguments vsF_add   {F fld V} _ _ _.
Arguments vsF_zero  {F fld V} _.
Arguments vsF_neg   {F fld V} _ _.
Arguments vsF_scale {F fld V} _ _ _.

(* Make VectorSpaceF lemma projections usable with dot notation *)
Arguments vsF_add_assoc  {F fld V} _ _ _ _.
Arguments vsF_add_comm   {F fld V} _ _ _.
Arguments vsF_add_zero_r {F fld V} _ _.
Arguments vsF_add_neg_r  {F fld V} _ _.
Arguments vsF_scale_one  {F fld V} _ _.
Arguments vsF_scale_mul  {F fld V} _ _ _ _.
Arguments vsF_scale_add_v {F fld V} _ _ _ _.
Arguments vsF_scale_add_s {F fld V} _ _ _ _.

(** ** Derived vector-space lemmas *)

(** scale 0 v = 0. Proof: scale 0 v = scale (0+0) v = scale 0 v + scale 0 v.
    From x = x + x, deduce x = 0 (using neg). *)
Lemma vsF_scale_zero {F : Type} {fld : Field F} {V : Type}
    (vs : VectorSpaceF fld V) (v : V) :
  vsF_scale vs (cr_zero fld) v = vsF_zero vs.
Proof.
  set (x := vsF_scale vs (cr_zero fld) v).
  assert (Hxx : vsF_add vs x x = x).
  { unfold x.
    rewrite <- (vsF_scale_add_s vs (cr_zero fld) (cr_zero fld) v).
    rewrite (cr_add_zero (fld_ring fld) (cr_zero fld)). reflexivity. }
  (* Now: x + x = x. Add neg x to both sides. *)
  assert (H : vsF_add vs (vsF_add vs x x) (vsF_neg vs x) = vsF_add vs x (vsF_neg vs x)).
  { rewrite Hxx. reflexivity. }
  rewrite <- (vsF_add_assoc vs) in H.
  rewrite (vsF_add_neg_r vs x) in H.
  rewrite (vsF_add_zero_r vs x) in H.
  rewrite H. reflexivity.
Qed.

(** scale (-1) v = neg v. Proof: scale (-1) v + v = scale (-1+1) v = scale 0 v = 0.
    Then by uniqueness of additive inverse, scale (-1) v = neg v. *)
Lemma vsF_neg_eq_scale_neg_one {F : Type} {fld : Field F} {V : Type}
    (vs : VectorSpaceF fld V) (v : V) :
  vsF_neg vs v = vsF_scale vs (cr_neg fld (cr_one fld)) v.
Proof.
  (* Show: scale (-1) v + v = 0, so scale (-1) v = neg v. *)
  assert (Hsum : vsF_add vs (vsF_scale vs (cr_neg fld (cr_one fld)) v) v
               = vsF_zero vs).
  { rewrite <- (vsF_scale_one vs v) at 2.
    rewrite <- (vsF_scale_add_s vs (cr_neg fld (cr_one fld)) (cr_one fld) v).
    rewrite (cr_add_neg_l (fld_ring fld) (cr_one fld)).
    apply vsF_scale_zero. }
  (* From a + v = 0 and v + neg v = 0, conclude a = neg v. *)
  assert (Hsum' : vsF_add vs v (vsF_neg vs v) = vsF_zero vs)
    by apply vsF_add_neg_r.
  (* a = a + 0 = a + (v + neg v) = (a + v) + neg v = 0 + neg v = neg v *)
  symmetry.
  rewrite <- (vsF_add_zero_r vs (vsF_scale vs (cr_neg fld (cr_one fld)) v)).
  rewrite <- Hsum'. rewrite (vsF_add_assoc vs).
  rewrite Hsum.
  rewrite (vsF_add_comm vs).
  apply vsF_add_zero_r.
Qed.

(** Additive inverse is unique. *)
Lemma vsF_add_inv_uniq {F : Type} {fld : Field F} {V : Type}
    (vs : VectorSpaceF fld V) (v w : V) :
  vsF_add vs v w = vsF_zero vs -> w = vsF_neg vs v.
Proof.
  intro Hvw.
  symmetry.
  rewrite <- (vsF_add_zero_r vs (vsF_neg vs v)).
  rewrite <- Hvw.
  rewrite (vsF_add_assoc vs).
  rewrite (vsF_add_comm vs (vsF_neg vs v) v).
  rewrite (vsF_add_neg_r vs v).
  rewrite (vsF_add_comm vs).
  apply vsF_add_zero_r.
Qed.

(** Double negation: neg (neg v) = v. *)
Lemma vsF_neg_neg {F : Type} {fld : Field F} {V : Type}
    (vs : VectorSpaceF fld V) (v : V) :
  vsF_neg vs (vsF_neg vs v) = v.
Proof.
  symmetry. apply vsF_add_inv_uniq.
  rewrite (vsF_add_comm vs).
  apply vsF_add_neg_r.
Qed.

(** Add is left-neg: vsF_add (neg v) v = 0. *)
Lemma vsF_add_neg_l {F : Type} {fld : Field F} {V : Type}
    (vs : VectorSpaceF fld V) (v : V) :
  vsF_add vs (vsF_neg vs v) v = vsF_zero vs.
Proof. rewrite (vsF_add_comm vs). apply vsF_add_neg_r. Qed.

(** neg distributes over add: -(u + v) = -u + -v. *)
Lemma vsF_neg_add {F : Type} {fld : Field F} {V : Type}
    (vs : VectorSpaceF fld V) (u v : V) :
  vsF_neg vs (vsF_add vs u v) = vsF_add vs (vsF_neg vs u) (vsF_neg vs v).
Proof.
  symmetry. apply vsF_add_inv_uniq.
  (* (u+v) + ((-u) + (-v)) = ... = 0 *)
  rewrite (vsF_add_assoc vs).
  rewrite (vsF_add_comm vs (vsF_add vs u v) (vsF_neg vs u)).
  rewrite (vsF_add_assoc vs (vsF_neg vs u) u v).
  rewrite (vsF_add_comm vs (vsF_neg vs u) u).
  rewrite (vsF_add_neg_r vs u).
  rewrite (vsF_add_comm vs (vsF_zero vs) v).
  rewrite (vsF_add_zero_r vs v).
  apply (vsF_add_neg_r vs v).
Qed.

(** Cancellation: u + w = v + w → u = v. *)
Lemma vsF_add_cancel_r {F : Type} {fld : Field F} {V : Type}
    (vs : VectorSpaceF fld V) (u v w : V) :
  vsF_add vs u w = vsF_add vs v w -> u = v.
Proof.
  intro Heq.
  assert (H : vsF_add vs (vsF_add vs u w) (vsF_neg vs w)
            = vsF_add vs (vsF_add vs v w) (vsF_neg vs w)).
  { rewrite Heq. reflexivity. }
  rewrite <- (vsF_add_assoc vs u w (vsF_neg vs w)) in H.
  rewrite <- (vsF_add_assoc vs v w (vsF_neg vs w)) in H.
  rewrite (vsF_add_neg_r vs w) in H.
  rewrite (vsF_add_zero_r vs u) in H.
  rewrite (vsF_add_zero_r vs v) in H.
  exact H.
Qed.

Record LieAlgebraF {F : Type} (fld : Field F) (L : Type) : Type := {
  laF_vs      :> VectorSpaceF fld L;
  laF_bracket : L -> L -> L;
  laF_bracket_add_l : forall x y z,
    laF_bracket (vsF_add laF_vs x y) z =
    vsF_add laF_vs (laF_bracket x z) (laF_bracket y z);
  laF_bracket_scale_l : forall a x y,
    laF_bracket (vsF_scale laF_vs a x) y =
    vsF_scale laF_vs a (laF_bracket x y);
  laF_bracket_add_r : forall x y z,
    laF_bracket x (vsF_add laF_vs y z) =
    vsF_add laF_vs (laF_bracket x y) (laF_bracket x z);
  laF_bracket_scale_r : forall a x y,
    laF_bracket x (vsF_scale laF_vs a y) =
    vsF_scale laF_vs a (laF_bracket x y);
  laF_bracket_alt : forall x,
    laF_bracket x x = vsF_zero laF_vs;
  laF_jacobi : forall x y z,
    vsF_add laF_vs
      (vsF_add laF_vs
         (laF_bracket x (laF_bracket y z))
         (laF_bracket y (laF_bracket z x)))
      (laF_bracket z (laF_bracket x y))
    = vsF_zero laF_vs;
}.

Arguments laF_vs      {F fld L} _.
Arguments laF_bracket {F fld L} _ _ _.

(* Make LieAlgebraF lemma projections usable with dot notation *)
Arguments laF_bracket_add_l   {F fld L} _ _ _ _.
Arguments laF_bracket_scale_l {F fld L} _ _ _ _.
Arguments laF_bracket_add_r   {F fld L} _ _ _ _.
Arguments laF_bracket_scale_r {F fld L} _ _ _ _.
Arguments laF_bracket_alt     {F fld L} _ _.
Arguments laF_jacobi          {F fld L} _ _ _ _.

(* Abbreviations: transparent notations so rewrites can see through them *)
Notation la_add   la := (vsF_add   (laF_vs la)).
Notation la_zero  la := (vsF_zero  (laF_vs la)).
Notation la_neg   la := (vsF_neg   (laF_vs la)).
Notation la_scale la := (vsF_scale (laF_vs la)).

(** *** Basic vector space helpers *)

(** v + v = v → v = 0. *)
Lemma vsF_add_cancel_double {F : Type} {fld : Field F} {V : Type}
    (vs : VectorSpaceF fld V) (v : V) :
    vsF_add vs v v = v -> v = vsF_zero vs.
Proof.
  intro H.
  assert (H0 : vsF_add vs v (vsF_neg vs v) = vsF_zero vs) by apply vs.(vsF_add_neg_r).
  assert (H1 : vsF_add vs (vsF_add vs v v) (vsF_neg vs v) = vsF_zero vs)
    by (rewrite H; exact H0).
  rewrite <- vs.(vsF_add_assoc) in H1.
  rewrite H0 in H1.
  rewrite vs.(vsF_add_zero_r) in H1.
  exact H1.
Qed.

(** 0 + v = v. *)
Lemma vsF_add_zero_l {F : Type} {fld : Field F} {V : Type}
    (vs : VectorSpaceF fld V) (v : V) :
    vsF_add vs (vsF_zero vs) v = v.
Proof.
  rewrite vs.(vsF_add_comm). apply vs.(vsF_add_zero_r).
Qed.

(** neg 0 = 0. *)
Lemma vsF_neg_zero {F : Type} {fld : Field F} {V : Type}
    (vs : VectorSpaceF fld V) :
    vsF_neg vs (vsF_zero vs) = vsF_zero vs.
Proof.
  assert (H : vsF_add vs (vsF_zero vs) (vsF_neg vs (vsF_zero vs)) = vsF_zero vs)
    by apply vs.(vsF_add_neg_r).
  rewrite vs.(vsF_add_comm) in H.
  rewrite vs.(vsF_add_zero_r) in H.
  exact H.
Qed.

(** a * 0 = 0. *)
Lemma vsF_scale_zero_v {F : Type} {fld : Field F} {V : Type}
    (vs : VectorSpaceF fld V) (a : F) :
    vsF_scale vs a (vsF_zero vs) = vsF_zero vs.
Proof.
  apply vsF_add_cancel_double.
  rewrite <- vs.(vsF_scale_add_v).
  f_equal.
  apply vs.(vsF_add_zero_r).
Qed.

Lemma laF_bracket_zero_r {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (x : L) :
    laF_bracket la x (la_zero la) = la_zero la.
Proof.
  apply (vsF_add_cancel_double (laF_vs la)).
  rewrite <- la.(laF_bracket_add_r).
  f_equal.
  apply (laF_vs la).(vsF_add_zero_r).
Qed.

Lemma laF_bracket_zero_l {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (x : L) :
    laF_bracket la (la_zero la) x = la_zero la.
Proof.
  apply (vsF_add_cancel_double (laF_vs la)).
  rewrite <- la.(laF_bracket_add_l).
  f_equal.
  apply (laF_vs la).(vsF_add_zero_r).
Qed.

Lemma laF_bracket_neg_r {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (x y : L) :
    laF_bracket la x (la_neg la y) = la_neg la (laF_bracket la x y).
Proof.
  assert (Hsum : la_add la (laF_bracket la x y) (laF_bracket la x (la_neg la y)) = la_zero la).
  { rewrite <- la.(laF_bracket_add_r).
    rewrite (laF_vs la).(vsF_add_neg_r).
    apply laF_bracket_zero_r. }
  assert (Hsum2 : la_add la (laF_bracket la x (la_neg la y)) (laF_bracket la x y) = la_zero la).
  { rewrite (laF_vs la).(vsF_add_comm). exact Hsum. }
  rewrite <- (vsF_add_zero_r (laF_vs la) (laF_bracket la x (la_neg la y))).
  rewrite <- (vsF_add_neg_r (laF_vs la) (laF_bracket la x y)).
  rewrite (laF_vs la).(vsF_add_assoc).
  rewrite Hsum2.
  rewrite (laF_vs la).(vsF_add_comm).
  apply (laF_vs la).(vsF_add_zero_r).
Qed.

Lemma laF_bracket_neg_l {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (x y : L) :
    laF_bracket la (la_neg la x) y = la_neg la (laF_bracket la x y).
Proof.
  assert (Hsum : la_add la (laF_bracket la (la_neg la x) y) (laF_bracket la x y) = la_zero la).
  { rewrite <- la.(laF_bracket_add_l).
    rewrite (laF_vs la).(vsF_add_comm).
    rewrite (laF_vs la).(vsF_add_neg_r).
    apply laF_bracket_zero_l. }
  rewrite <- (vsF_add_zero_r (laF_vs la) (laF_bracket la (la_neg la x) y)).
  rewrite <- (vsF_add_neg_r (laF_vs la) (laF_bracket la x y)).
  rewrite (laF_vs la).(vsF_add_assoc).
  rewrite Hsum.
  rewrite (laF_vs la).(vsF_add_comm).
  apply (laF_vs la).(vsF_add_zero_r).
Qed.

Lemma laF_anticomm {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (x y : L) :
    laF_bracket la x y = la_neg la (laF_bracket la y x).
Proof.
  assert (H : la_add la (laF_bracket la x y) (laF_bracket la y x) = la_zero la).
  { assert (H0 : laF_bracket la (la_add la x y) (la_add la x y) = la_zero la)
      by apply la.(laF_bracket_alt).
    rewrite la.(laF_bracket_add_l) in H0.
    rewrite ! la.(laF_bracket_add_r) in H0.
    rewrite (la.(laF_bracket_alt) x) in H0.
    rewrite (la.(laF_bracket_alt) y) in H0.
    rewrite (vsF_add_zero_l (laF_vs la)) in H0.
    rewrite (laF_vs la).(vsF_add_zero_r) in H0.
    exact H0. }
  rewrite <- (vsF_add_zero_r (laF_vs la) (laF_bracket la x y)).
  rewrite <- (vsF_add_neg_r (laF_vs la) (laF_bracket la y x)).
  rewrite (laF_vs la).(vsF_add_assoc).
  rewrite H.
  rewrite (laF_vs la).(vsF_add_comm).
  apply (laF_vs la).(vsF_add_zero_r).
Qed.

Record IsSubalgebra {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (S : L -> Prop) : Prop := {
  sub_zero    : S (la_zero la);
  sub_add     : forall x y, S x -> S y -> S (la_add la x y);
  sub_neg     : forall x, S x -> S (la_neg la x);
  sub_scale   : forall a x, S x -> S (la_scale la a x);
  sub_bracket : forall x y, S x -> S y -> S (laF_bracket la x y);
}.

Arguments sub_zero    {F fld L la S}.
Arguments sub_add     {F fld L la S}.
Arguments sub_neg     {F fld L la S}.
Arguments sub_scale   {F fld L la S}.
Arguments sub_bracket {F fld L la S}.

Lemma full_is_subalgebra {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) : IsSubalgebra la (fun _ => True).
Proof. constructor; intros; exact I. Qed.

Lemma zero_is_subalgebra {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    IsSubalgebra la (fun x => x = la_zero la).
Proof.
  constructor.
  - reflexivity.
  - intros x y Hx Hy. rewrite Hx, Hy. apply (laF_vs la).(vsF_add_zero_r).
  - intros x Hx. rewrite Hx. apply vsF_neg_zero.
  - intros a x Hx. rewrite Hx. apply vsF_scale_zero_v.
  - intros x y Hx Hy. rewrite Hx, Hy. apply la.(laF_bracket_alt).
Qed.

Lemma inter_subalgebra {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (S T : L -> Prop) :
    IsSubalgebra la S -> IsSubalgebra la T ->
    IsSubalgebra la (fun x => S x /\ T x).
Proof.
  intros HS HT. constructor.
  - split; [apply HS.(sub_zero) | apply HT.(sub_zero)].
  - intros x y [Hsx Htx] [Hsy Hty]. split.
    + apply HS.(sub_add); assumption.
    + apply HT.(sub_add); assumption.
  - intros x [Hsx Htx]. split.
    + apply HS.(sub_neg); assumption.
    + apply HT.(sub_neg); assumption.
  - intros a x [Hsx Htx]. split.
    + apply HS.(sub_scale); assumption.
    + apply HT.(sub_scale); assumption.
  - intros x y [Hsx Htx] [Hsy Hty]. split.
    + apply HS.(sub_bracket); assumption.
    + apply HT.(sub_bracket); assumption.
Qed.

Record LieHom {F : Type} {fld : Field F} {L M : Type}
    (la : LieAlgebraF fld L) (lb : LieAlgebraF fld M) : Type := {
  lh_fn      : L -> M;
  lh_add     : forall x y,
    lh_fn (la_add la x y) = la_add lb (lh_fn x) (lh_fn y);
  lh_scale   : forall a x,
    lh_fn (la_scale la a x) = la_scale lb a (lh_fn x);
  lh_bracket : forall x y,
    lh_fn (laF_bracket la x y) = laF_bracket lb (lh_fn x) (lh_fn y);
}.

Arguments lh_fn     {F fld L M la lb}.
Arguments lh_add    {F fld L M la lb}.
Arguments lh_scale  {F fld L M la lb}.
Arguments lh_bracket {F fld L M la lb}.

Lemma lh_zero {F : Type} {fld : Field F} {L M : Type}
    {la : LieAlgebraF fld L} {lb : LieAlgebraF fld M}
    (φ : LieHom la lb) :
    lh_fn φ (la_zero la) = la_zero lb.
Proof.
  apply (vsF_add_cancel_double (laF_vs lb)).
  rewrite <- φ.(lh_add).
  f_equal.
  apply (laF_vs la).(vsF_add_zero_r).
Qed.

Lemma lh_neg {F : Type} {fld : Field F} {L M : Type}
    {la : LieAlgebraF fld L} {lb : LieAlgebraF fld M}
    (φ : LieHom la lb) (x : L) :
    lh_fn φ (la_neg la x) = la_neg lb (lh_fn φ x).
Proof.
  assert (Hsum : la_add lb (lh_fn φ x) (lh_fn φ (la_neg la x)) = la_zero lb).
  { rewrite <- φ.(lh_add).
    rewrite (laF_vs la).(vsF_add_neg_r).
    apply lh_zero. }
  assert (Hsum2 : la_add lb (lh_fn φ (la_neg la x)) (lh_fn φ x) = la_zero lb).
  { rewrite (laF_vs lb).(vsF_add_comm). exact Hsum. }
  rewrite <- (vsF_add_zero_r (laF_vs lb) (lh_fn φ (la_neg la x))).
  rewrite <- (vsF_add_neg_r (laF_vs lb) (lh_fn φ x)).
  rewrite (laF_vs lb).(vsF_add_assoc).
  rewrite Hsum2.
  rewrite (laF_vs lb).(vsF_add_comm).
  apply (laF_vs lb).(vsF_add_zero_r).
Qed.

Record LieIsom {F : Type} {fld : Field F} {L M : Type}
    (la : LieAlgebraF fld L) (lb : LieAlgebraF fld M) : Type := {
  li_hom    :> LieHom la lb;
  li_inv    : M -> L;
  li_fn_inv : forall x, lh_fn li_hom (li_inv x) = x;
  li_inv_fn : forall x, li_inv (lh_fn li_hom x) = x;
}.

Arguments li_hom    {F fld L M la lb}.
Arguments li_inv    {F fld L M la lb}.
Arguments li_fn_inv {F fld L M la lb}.
Arguments li_inv_fn {F fld L M la lb}.

Definition lie_isom_id {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) : LieIsom la la.
Proof.
  refine {| li_hom  := {| lh_fn := fun x => x;
                           lh_add := fun x y => eq_refl;
                           lh_scale := fun a x => eq_refl;
                           lh_bracket := fun x y => eq_refl |};
            li_inv  := fun x => x;
            li_fn_inv := fun x => eq_refl;
            li_inv_fn := fun x => eq_refl; |}.
Defined.

Definition lie_isom_comp {F : Type} {fld : Field F} {L M N : Type}
    {la : LieAlgebraF fld L} {lb : LieAlgebraF fld M} {lc : LieAlgebraF fld N}
    (g : LieIsom lb lc) (f : LieIsom la lb) : LieIsom la lc :=
  {| li_hom := {|
       lh_fn      := fun x => lh_fn (li_hom g) (lh_fn (li_hom f) x);
       lh_add     := fun x y =>
         eq_trans (f_equal (lh_fn (li_hom g)) (lh_add (li_hom f) x y))
                  (lh_add (li_hom g) _ _);
       lh_scale   := fun a x =>
         eq_trans (f_equal (lh_fn (li_hom g)) (lh_scale (li_hom f) a x))
                  (lh_scale (li_hom g) a _);
       lh_bracket := fun x y =>
         eq_trans (f_equal (lh_fn (li_hom g)) (lh_bracket (li_hom f) x y))
                  (lh_bracket (li_hom g) _ _);
     |};
     li_inv    := fun y => li_inv f (li_inv g y);
     li_fn_inv := fun y =>
       eq_trans (f_equal (lh_fn (li_hom g)) (li_fn_inv f (li_inv g y)))
                (li_fn_inv g y);
     li_inv_fn := fun x =>
       eq_trans (f_equal (li_inv f) (li_inv_fn g (lh_fn (li_hom f) x)))
                (li_inv_fn f x);
  |}.

(** Anticommutativity of bracket: [y, x] = -[x, y].
    Derived from alternating + bilinearity. *)
Lemma laF_bracket_anticomm {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (x y : L) :
  laF_bracket la y x = vsF_neg (laF_vs la) (laF_bracket la x y).
Proof.
  apply vsF_add_inv_uniq.
  (* Goal: vsF_add (laF_bracket la x y) (laF_bracket la y x) = vsF_zero. *)
  (* Key fact: [x+y, x+y] = 0 expands to [x,x] + [x,y] + [y,x] + [y,y] = 0. *)
  pose proof (laF_bracket_alt la (vsF_add (laF_vs la) x y)) as Halt.
  rewrite (laF_bracket_add_l la x y (vsF_add (laF_vs la) x y)) in Halt.
  rewrite (laF_bracket_add_r la x x y) in Halt.
  rewrite (laF_bracket_add_r la y x y) in Halt.
  rewrite (laF_bracket_alt la x) in Halt.
  rewrite (laF_bracket_alt la y) in Halt.
  (* Now: 0 + [x,y] + ([y,x] + 0) = 0 *)
  rewrite (vsF_add_zero_l (laF_vs la)) in Halt.
  rewrite (vsF_add_zero_r (laF_vs la)) in Halt.
  exact Halt.
Qed.
