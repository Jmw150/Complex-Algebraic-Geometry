
From Stdlib Require Import QArith ZArith.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyRealsMult.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyAbs.


(*Local Open Scope Z_scope.*)
(*Local Open Scope Q_scope.*)
Local Open Scope CReal_scope.

From CAG Require Import Reals_extra.



(* Turn a rational into a pair (num, den) in Z×Z so OCaml printing 
   is easy *)
Definition q_as_Zpair (q : Q) : Z * Z :=
  (Qnum q, Zpos (Qden q)).

(** Constructive Complex numbers *)
Record CComplex : Type := mkC {
  re : CReal ;
  im : CReal
}.                             

(* constants *)
Definition C0 : CComplex := mkC 0 0.
Definition C1 : CComplex := mkC 1 0.
Definition Ci : CComplex := mkC 0 1.

(* embedding rationals *)
Definition Cinject_Q (q : Q) : CComplex := mkC (inject_Q q) 0.


Definition Cadd (z w : CComplex) : CComplex := 
  mkC (re z + re w) (im z + im w).

Definition Cneg (z : CComplex) : CComplex :=
  mkC (- re z) (- im z).

Definition Csub (z w : CComplex) : CComplex := Cadd z (Cneg w).

(* Multiplication: (a+bi)(c+di) = (ac - bd) + (ad + bc)i *)
Definition Cmul (z w : CComplex) : CComplex :=
  mkC (re z * re w - im z * im w)
      (re z * im w + im z * re w).

(* natural exponent *)
Fixpoint Cpow (z : CComplex) (n : nat) : CComplex :=
  match n with
  | O => C1
  | S n' => Cmul z (Cpow z n')
  end.

(*
  ===============================================================
  FUTURE WORK: Singularities and Constructive Division on CComplex
  ===============================================================

  In classical complex analysis, an isolated singularity of f at a point a
  is one of three types:

  (1) Removable singularity:
        lim_{z -> a} f(z) exists and is finite.
        The function can be redefined at a to become holomorphic.

        Example:
            f(z) = z^2 / z at z = 0.
            Simplifies to f(z) = z for z ≠ 0.
            The "hole" disappears after algebraic cancellation.

  (2) Pole (order n):
        |f(z)| -> ∞ as z -> a.
        The Laurent expansion has finitely many negative terms.

        Example:
            f(z) = 1 / z at z = 0.

  (3) Essential singularity:
        Neither removable nor pole.
        The Laurent expansion has infinitely many negative terms.
        Behavior is chaotic (Picard).

        Example:
            f(z) = exp(1/z) at z = 0.
*)

Definition Cnorm2 (z : CComplex) : CReal :=
  (re z * re z) + (im z * im z).

Definition Cdist2 (z w : CComplex) : CReal :=
  Cnorm2 (Csub z w).

Definition Cconj (a : CComplex) : CComplex :=
  mkC (re a) (im (Cneg a)).

(* Equal in general. Need many methods for computatble forms *)
Definition Cequal (a b : CComplex) : Prop :=
  and (re a = re b) (im a = im b).

(** CRealEq-level equality on complex components: z ~~ w iff
    re(z) == re(w) and im(z) == im(w) in CRealEq sense. *)
Definition CComplex_req (z w : CComplex) : Prop :=
  CRealEq (re z) (re w) /\ CRealEq (im z) (im w).

Notation "z ~~C w" := (CComplex_req z w) (at level 70).

(* CAG zero-dependent Lemma CComplex_eq theories/Complex.v:109 BEGIN
Lemma CComplex_eq : forall z w : CComplex, z ~~C w -> z = w.
Proof.
  intros [zr zi] [wr wi] [Hr Hi].
  simpl in *.
  apply CRealEq_eq in Hr.
  apply CRealEq_eq in Hi.
  subst. reflexivity.
Qed.
   CAG zero-dependent Lemma CComplex_eq theories/Complex.v:109 END *)

Lemma CComplex_req_refl : forall z : CComplex, z ~~C z.
Proof.
  intro z. split; reflexivity.
Qed.

Lemma CComplex_req_sym : forall z w : CComplex, z ~~C w -> w ~~C z.
Proof.
  intros z w [Hr Hi]. split; symmetry; assumption.
Qed.

Lemma CComplex_req_trans : forall x y z : CComplex,
    x ~~C y -> y ~~C z -> x ~~C z.
Proof.
  intros x y z [Hr1 Hi1] [Hr2 Hi2].
  split; eapply CRealEq_trans; eassumption.
Qed.

Lemma Cadd_C0_l_req : forall z : CComplex, Cadd C0 z ~~C z.
Proof.
  intro z. unfold CComplex_req, Cadd, C0. simpl. split; ring.
Qed.

(* CAG zero-dependent Lemma Cadd_C0_l theories/Complex.v:140 BEGIN
Lemma Cadd_C0_l : forall z : CComplex, Cadd C0 z = z.
Proof.
  intro z. apply CComplex_eq, Cadd_C0_l_req.
Qed.
   CAG zero-dependent Lemma Cadd_C0_l theories/Complex.v:140 END *)

Lemma Cadd_C0_r_req : forall z : CComplex, Cadd z C0 ~~C z.
Proof.
  intro z. unfold CComplex_req, Cadd, C0. simpl. split; ring.
Qed.

(* CAG zero-dependent Lemma Cadd_C0_r theories/Complex.v:150 BEGIN
Lemma Cadd_C0_r : forall z : CComplex, Cadd z C0 = z.
Proof.
  intro z. apply CComplex_eq, Cadd_C0_r_req.
Qed.
   CAG zero-dependent Lemma Cadd_C0_r theories/Complex.v:150 END *)

Lemma Cadd_assoc_req : forall x y z : CComplex,
    Cadd x (Cadd y z) ~~C Cadd (Cadd x y) z.
Proof.
  intros x y z. unfold CComplex_req, Cadd. simpl. split; ring.
Qed.

Lemma Cadd_neg_l_req : forall z : CComplex, Cadd (Cneg z) z ~~C C0.
Proof.
  intro z. unfold CComplex_req, Cadd, Cneg, C0. simpl. split; ring.
Qed.

(** C0 * z ~~ C0.
    Proof: re(C0*z) = 0*re(z) - 0*im(z) == 0 and im(C0*z) = 0*im(z) + 0*re(z) == 0. *)
Lemma Cmul_C0_l : forall (z : CComplex), (Cmul C0 z) ~~C C0.
Proof.
  intro z. unfold CComplex_req, Cmul, C0. simpl. split; ring.
Qed.

(* CAG zero-dependent Lemma Cmul_C0_l_eq theories/Complex.v:173 BEGIN
Lemma Cmul_C0_l_eq : forall (z : CComplex), Cmul C0 z = C0.
Proof.
  intro z. apply CComplex_eq, Cmul_C0_l.
Qed.
   CAG zero-dependent Lemma Cmul_C0_l_eq theories/Complex.v:173 END *)

Lemma Cmul_C0_r_req : forall (z : CComplex), (Cmul z C0) ~~C C0.
Proof.
  intro z. unfold CComplex_req, Cmul, C0. simpl. split; ring.
Qed.

(* CAG zero-dependent Lemma Cmul_C0_r theories/Complex.v:183 BEGIN
Lemma Cmul_C0_r : forall (z : CComplex), Cmul z C0 = C0.
Proof.
  intro z. apply CComplex_eq, Cmul_C0_r_req.
Qed.
   CAG zero-dependent Lemma Cmul_C0_r theories/Complex.v:183 END *)

(* CAG zero-dependent Lemma Cmul_C1_l theories/Complex.v:188 BEGIN
Lemma Cmul_C1_l : forall (z : CComplex), Cmul C1 z = z.
Proof.
  intro z. apply CComplex_eq.
  unfold CComplex_req, Cmul, C1. simpl. split; ring.
Qed.
   CAG zero-dependent Lemma Cmul_C1_l theories/Complex.v:188 END *)

(* CAG zero-dependent Lemma Cmul_C1_r theories/Complex.v:194 BEGIN
Lemma Cmul_C1_r : forall (z : CComplex), Cmul z C1 = z.
Proof.
  intro z. apply CComplex_eq.
  unfold CComplex_req, Cmul, C1. simpl. split; ring.
Qed.
   CAG zero-dependent Lemma Cmul_C1_r theories/Complex.v:194 END *)

(* CAG zero-dependent Lemma Cmul_assoc_eq theories/Complex.v:200 BEGIN
Lemma Cmul_assoc_eq : forall a b c : CComplex,
    Cmul (Cmul a b) c = Cmul a (Cmul b c).
Proof.
  intros a b c. apply CComplex_eq.
  unfold CComplex_req, Cmul. simpl. split; ring.
Qed.
   CAG zero-dependent Lemma Cmul_assoc_eq theories/Complex.v:200 END *)

Lemma Cconj_add_req : forall z w : CComplex,
    Cconj (Cadd z w) ~~C Cadd (Cconj z) (Cconj w).
Proof.
  intros z w. unfold CComplex_req, Cconj, Cadd, Cneg. simpl. split; ring.
Qed.

Lemma Cconj_mul_req : forall z w : CComplex,
    Cconj (Cmul z w) ~~C Cmul (Cconj z) (Cconj w).
Proof.
  intros z w. unfold CComplex_req, Cconj, Cmul, Cadd, Cneg. simpl. split; ring.
Qed.

(** z - C0 ~~ z.
    Proof: re(z - 0) = re(z) + (-0) == re(z) and similarly for im. *)
Lemma Csub_C0_r : forall (z : CComplex), (Csub z C0) ~~C z.
Proof.
  intro z. unfold CComplex_req, Csub, Cadd, Cneg, C0. simpl. split; ring.
Qed.

(** z - C0*w ~~ z, used in Y_power_weight base case. *)
Lemma Csub_C0mul_r : forall (z w : CComplex), (Csub z (Cmul C0 w)) ~~C z.
Proof.
  intros z w. unfold CComplex_req, Csub, Cadd, Cneg, Cmul, C0. simpl. split; ring.
Qed.

(** (z - n*2) - 2 ~~ z - (n+1)*2, used in Y_power_weight inductive step. *)
Theorem Csub_two_succ : forall (z : CComplex) (n : nat),
    (Csub (Csub z (Cmul (Cinject_Q (QArith_base.inject_Z (Z.of_nat n))) (Cadd C1 C1)))
          (Cadd C1 C1)) ~~C
    (Csub z (Cmul (Cinject_Q (QArith_base.inject_Z (Z.of_nat (S n)))) (Cadd C1 C1))).
Proof.
  intros z n.
  (* Step 1: propositional equality in Q *)
  assert (HQ : QArith_base.inject_Z (Z.of_nat (S n)) =
               (QArith_base.inject_Z (Z.of_nat n) + 1)%Q).
  { rewrite Nat2Z.inj_succ. apply QArith_base.inject_Z_plus. }
  (* Step 2: CRealEq fact — inject_Q(inject_Z(S n)) == inject_Q(inject_Z n) + 1 *)
  assert (Hkey : inject_Q (QArith_base.inject_Z (Z.of_nat (S n))) ==
                 inject_Q (QArith_base.inject_Z (Z.of_nat n)) + 1).
  { rewrite HQ.
    apply (CRealEq_trans (inject_Q (QArith_base.inject_Z (Z.of_nat n) + 1%Q))
                         (inject_Q (QArith_base.inject_Z (Z.of_nat n)) + inject_Q 1)
                         (inject_Q (QArith_base.inject_Z (Z.of_nat n)) + 1)).
    - apply inject_Q_plus.
    - apply CReal_plus_proper_l. apply inject_Q_one. }
  unfold CComplex_req, Csub, Cadd, Cneg, Cmul, Cinject_Q, C0, C1. simpl.
  split.
  - rewrite Hkey. ring.
  - ring.
Qed.

(*
  ===============================================================
  FUTURE WORK: Equality Testing, Approximation, and Reflection
  ===============================================================

  Problem:
    CReal / CComplex equality is not decidable in general.
    Therefore we cannot have a total boolean test ceqb : CComplex -> CComplex -> bool
    that is both:
      - sound: ceqb z w = true  -> z = w
      - complete: z = w -> ceqb z w = true
    while always terminating.

  Practical solution ("timeout on sequences"):
    Define bounded/approximate equality at precision k:

        approx_eqR (k : Z) (x y : CReal) : Prop
        approx_eqRb (k : Z) (x y : CReal) : bool

        approx_eqC (k : Z) (z w : CComplex) : Prop
        approx_eqCb (k : Z) (z w : CComplex) : bool

    Intuition:
      - k is a timeout / precision parameter (bigger k => stricter test).
      - approx_eqRb k x y computes by comparing rational approximants
        seq x N and seq y N for some N derived from k (or just N = k),
        and checking |seq x N - seq y N| <= 2^{-k}.
      - approx_eqRb is *sound* for approximate equality:
            approx_eqRb k x y = true  -> approx_eqR k x y
        but generally not complete.

  Reflection bridge:
    Use Bool.reflect / reflect to connect bool evidence to Prop:

        Lemma approx_eqR_reflect :
          forall k x y,
            reflect (approx_eqR k x y) (approx_eqRb k x y).

        Lemma approx_eqC_reflect :
          forall k z w,
            reflect (approx_eqC k z w) (approx_eqCb k z w).

    This enables rewriting / case splitting on the boolean test while
    keeping a precise Prop statement about what was established.

  Notes:
    - This "equality test" is not mathematical equality; it is a
      computable closeness predicate.
    - True equality can remain as Prop-level equality of Cauchy reals,
      while algorithms use approx_eq* for branching/termination.

*)


Definition Climit_at (f : CComplex -> CComplex) (z0 L : CComplex) : Prop :=
  forall eps : CReal,
    (CRealLtProp (inject_Q 0) eps) ->
    exists delta : CReal,
      (CRealLtProp (inject_Q 0) delta) /\
      forall z : CComplex,
        (Cdist2 z z0 # 0) ->    (* z ≠ z0, written with apartness *)
CRealLtProp (Cdist2 z z0) delta ->         (* close enough *)
        CRealLtProp (Cdist2 (f z) L) eps.          (* close in image *)


(* Complex derivatives *)
Definition partial_x_at 
  (u : CComplex -> CReal) 
  (x0 y0 ux : CReal) 
  : Prop :=
  Rderiv_at (fun x => u (mkC x y0)) x0 ux.

Definition partial_y_at 
  (u : CComplex -> CReal) (x0 y0 uy : CReal) : Prop 
  := Rderiv_at (fun y => u (mkC x0 y)) y0 uy.

Definition u_of (f : CComplex -> CComplex) : CComplex -> CReal :=
  fun p => re (f p).

Definition v_of (f : CComplex -> CComplex) : CComplex -> CReal :=
  fun p => im (f p).

Definition CR_at (f : CComplex -> CComplex) (x0 y0 : CReal) : Prop :=
  let u := u_of f in
  let v := v_of f in
  exists ux uy vx vy : CReal,
    partial_x_at u x0 y0 ux /\
    partial_y_at u x0 y0 uy /\
    partial_x_at v x0 y0 vx /\
    partial_y_at v x0 y0 vy /\
    ux = vy /\
    uy = - vx.

(* holomorphic at a point *)
Definition holomorphic_at_CR 
  (f : CComplex -> CComplex) (z0 : CComplex) 
  : Prop :=
  CR_at f (re z0) (im z0).

(* holomorphic in some domain *)
Definition holomorphic_on_CR 
  (U : CComplex -> Prop) (* A given domain U, i.e. some disk *)
  (f : CComplex -> CComplex) 
  : Prop :=
  forall z0, U z0 -> holomorphic_at_CR f z0.

(* Derivatives at C^n *)

(* ~/.opam/default/lib/coq/user-contrib/Stdlib/Vectors/Fin.v *)
Set Warnings "-warn-library-file-stdlib-vector".
From Stdlib Require Import Vectors.Fin.
Set Warnings "+warn-library-file-stdlib-vector".

Definition Cn (n : nat) : Type := Fin.t n -> CComplex.
Definition Rn (n : nat) : Type := Fin.t n -> CReal.

Definition re_n {n} (z : Cn n) : Rn n := fun i => re (z i).
Definition im_n {n} (z : Cn n) : Rn n := fun i => im (z i).

Definition mkCn {n} (x y : Rn n) : Cn n :=
  fun i => mkC (x i) (y i).

(* index v[i] *)
Definition ind {n}
  (v : Cn n)
  (i : Fin.t n)
  : CComplex 
  := (v i).

(* Update an index of a vector *)
Definition upd {n} 
  (v : Fin.t n -> CReal) 
  (i : Fin.t n) 
  (a : CReal) 
  : Fin.t n -> CReal 
  := fun j => if Fin.eq_dec j i then a else v j.

Definition cupd {n}
  (z : Cn n) 
  (i : Fin.t n) 
  (a : CComplex) 
  : Cn n 
  := fun j => if Fin.eq_dec j i then a else z j.

(* Freeze all variables in f except for i *)
Definition freeze_except {n}
  (f : Cn n -> CComplex)
  (v : Cn n)
  (i : Fin.t n)
  : CComplex -> CComplex 
  := fun w => f (cupd v i w).

(* Holomorphic for some domain U in some dimension i *)
Definition holomorphic_in_var_at {n}
  (U : Cn n -> Prop)
  (f : Cn n -> CComplex)
  (v : Cn n)
  (i : Fin.t n)
  : Prop 
  := U v -> holomorphic_at_CR (freeze_except f v i) (v i).

(* Holomorphic for some domain U in all dimensions *)
Definition holomorphic_each_at {n}
  (U : Cn n -> Prop)
  (f : Cn n -> CComplex)
  (v : Cn n)
  : Prop 
  := U v -> forall i : Fin.t n,
    holomorphic_at_CR (freeze_except f v i) (v i).

(* restrict domain of function *)
Definition restrict {X Y}
  (U : X -> Prop)
  (f : X -> Y)
  : { x : X | U x } -> Y 
  := fun x => f (proj1_sig x).


(* Complex manifolds *)
(*
Record Biholomorphism {n}
  (U V : Cn n -> Prop) := {

  f : Cn n -> Cn n;
  g : Cn n -> Cn n;

  (* domain mapping *)
  f_maps : forall z, U z -> V (f z);
  g_maps : forall w, V w -> U (g w);

  (* inverse laws on the subsets *)
  left_inv  : forall z, U z -> g (f z) = z;
  right_inv : forall w, V w -> f (g w) = w;

  (* holomorphicity *)
  f_holo : forall z, holomorphic_each_at U f z;
  g_holo : forall w, holomorphic_each_at V g w;
}.
*)


Definition CComplex_apart (z w : CComplex) : Set :=
  Cnorm2 (Csub z w) # 0.
(*  (re z # re w) + (im z # im w).*)

Infix "#C" := CComplex_apart (at level 70).

(* How subtypes are made *)
(*Definition CReal_nonzero := { x : CReal | x <> inject_Q 0 }.*)

(* But Coercion breaks if we use that... *)
(* Constructive complex numbers, not including 0, and without cauchy seuqences approaching 0 *)

(** a dependent pair packaged as a record:

- cnz_val is the complex number z : CComplex

- cnz_neq0 is evidence (a witness, living in Set) that z is apart from 0: z #C C0
*)
Record CComplex_nonzero : Type := mkCnz
{
  cnz_val : CComplex ;
  cnz_neq0 : cnz_val #C C0
}.

Coercion cnz_val : CComplex_nonzero >-> CComplex.

(*Check (fun (z : CComplex_nonzero) => re z).*)
(*Check (fun (z : CComplex_nonzero) => Cnorm2 z).*)
(*Check (fun (z : CComplex_nonzero) => Cconj z).*)


Definition CReal_div (x y : CReal) (ynz : y # 0) : CReal :=
  x * ((/ y) ynz).


Definition Capprox (z : CComplex) (n : Z) : Q * Q :=
  (seq (re z) n, seq (im z) n).
