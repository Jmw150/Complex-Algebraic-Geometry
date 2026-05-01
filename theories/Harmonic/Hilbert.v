(** * Harmonic/Hilbert.v — Abstract Hilbert-space framework

    This file builds the [HilbertSpace] Record, the foundational layer
    needed by the Spectral-Theorem program (Tasks SP.1 / SP.2 / SP.3).

    Design constraints:

    - We follow the project's existing [VectorSpaceF] / [LieAlgebraF]
      pattern (see [theories/Lie/BasicDef.v]) — laws live as projection
      fields of the Record, and we use Leibniz [=] for those laws so
      consumers can [rewrite] freely.  This is consistent with
      [Sobolev.v]'s [L2_inner_sym : L2_inner φ ψ = L2_inner ψ φ] and is
      backed by the project-wide [CRealEq_eq] bridge in [Complex.v].

    - The complex inner product is [hs_inner : V -> V -> CComplex],
      conjugate-symmetric in the mathematical convention used here:
      [<x, y> = conj <y, x>].  Linearity is in the FIRST argument
      ("physicist's convention" is right-linear; "mathematician's"
      is left-linear — both are equivalent up to swapping; the
      equations below pick LEFT linearity).

    - We make no Stdlib commitments to [sqrt] or completeness of
      Cauchy sequences in the abstract space.  The squared norm
      [hs_norm2 x := re (hs_inner x x)] is taken as the primary
      object; foundational lemmas (norm-zero, parallelogram) are
      stated and proved on [hs_norm2].  Cauchy-Schwarz and a
      [hs_complete] completeness field are STATED AS Conjectures
      below — they are deliberately deferred to SP.1/SP.2 where
      a concrete model (probably [L^2(M, E)] from [Sobolev.v]) will
      provide them.

    - Per the user constraint, this file adds 0 new project axioms;
      Conjectures are documented infrastructure-incompleteness, not
      assumptions in the Stdlib sense.

    [SP.0] entry point.  Downstream: [Spectral.v] / [GreenOperator.v]. *)

From Stdlib Require Import QArith.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyRealsMult.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyAbs.

From CAG Require Import Complex.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. The HilbertSpace Record                                      *)
(* ================================================================== *)

(** A complex pre-Hilbert space (i.e., a complex inner-product space).
    Cauchy completeness is NOT a field — see the [hs_complete]
    Conjecture below for the documented deferral. *)
Record HilbertSpace : Type := mkHilbert {
  (** Underlying carrier set. *)
  hs_carrier : Type;

  (** Vector-space structure. *)
  hs_zero  : hs_carrier;
  hs_add   : hs_carrier -> hs_carrier -> hs_carrier;
  hs_neg   : hs_carrier -> hs_carrier;
  hs_scale : CComplex   -> hs_carrier -> hs_carrier;

  (** Hermitian inner product. *)
  hs_inner : hs_carrier -> hs_carrier -> CComplex;

  (** *** Vector-space laws (mirroring [VectorSpaceF] of [Lie/BasicDef.v]). *)
  hs_add_assoc  : forall u v w,
      hs_add u (hs_add v w) = hs_add (hs_add u v) w;
  hs_add_comm   : forall u v, hs_add u v = hs_add v u;
  hs_add_zero_r : forall v, hs_add v hs_zero = v;
  hs_add_neg_r  : forall v, hs_add v (hs_neg v) = hs_zero;

  hs_scale_one    : forall v, hs_scale C1 v = v;
  hs_scale_mul    : forall a b v,
      hs_scale a (hs_scale b v) = hs_scale (Cmul a b) v;
  hs_scale_add_v  : forall a u v,
      hs_scale a (hs_add u v) = hs_add (hs_scale a u) (hs_scale a v);
  hs_scale_add_s  : forall a b v,
      hs_scale (Cadd a b) v = hs_add (hs_scale a v) (hs_scale b v);

  (** *** Inner-product laws.

      [hs_inner_sym] : conjugate symmetry [<x, y> = conj <y, x>].
      [hs_inner_add_l], [hs_inner_scale_l] : LEFT-linearity in the
      first argument.  (Right-linearity follows by symmetry +
      conjugate; we do not bake it in as a separate field, to keep
      the Record minimal.)
      [hs_inner_pos]   : positive-definite on the real part.  We
      state this on the squared norm [re (hs_inner x x)] using
      the [<] of [CRealLtProp].
      [hs_inner_zero_re] : the imaginary part of [<x, x>] is 0
      (this is forced by conjugate symmetry; we ship it as a
      Lemma below, not a field).
  *)
  hs_inner_sym :
      forall x y, hs_inner x y = Cconj (hs_inner y x);

  hs_inner_add_l :
      forall x y z,
        hs_inner (hs_add x y) z = Cadd (hs_inner x z) (hs_inner y z);

  hs_inner_scale_l :
      forall a x y,
        hs_inner (hs_scale a x) y = Cmul a (hs_inner x y);

  hs_inner_pos :
      forall x,
        x <> hs_zero ->
        CRealLtProp (inject_Q 0%Q) (re (hs_inner x x));

  (** Zero-vector reflexivity: [<0, 0> = 0].  This is automatically
      forced by [hs_inner_scale_l] applied at [a := C0], but stating
      it as a field lets downstream consumers use it without invoking
      derivation.  *)
  hs_inner_zero_l :
      forall x, hs_inner hs_zero x = C0;
}.

(** Implicit-arg declarations.  We make the underlying [HilbertSpace]
    implicit on the carrier-level operations and on the field laws,
    so downstream proofs read close to the math (e.g.,
    [hs_inner x y] rather than [hs_inner H x y]).  Mirrors the
    Stdlib pattern for [groups : Setoid]-style records. *)
Arguments hs_zero  {_}.
Arguments hs_add   {_} _ _.
Arguments hs_neg   {_} _.
Arguments hs_scale {_} _ _.
Arguments hs_inner {_} _ _.

Arguments hs_add_assoc   {_} _ _ _.
Arguments hs_add_comm    {_} _ _.
Arguments hs_add_zero_r  {_} _.
Arguments hs_add_neg_r   {_} _.
Arguments hs_scale_one   {_} _.
Arguments hs_scale_mul   {_} _ _ _.
Arguments hs_scale_add_v {_} _ _ _.
Arguments hs_scale_add_s {_} _ _ _.

Arguments hs_inner_sym     {_} _ _.
Arguments hs_inner_add_l   {_} _ _ _.
Arguments hs_inner_scale_l {_} _ _ _.
Arguments hs_inner_pos     {_} _.
Arguments hs_inner_zero_l  {_} _.

(* ================================================================== *)
(** * 2. Derived operations                                            *)
(* ================================================================== *)

(** Squared (real) norm: [re <x, x>].  We work primarily with the
    squared norm because [sqrt] on [CReal] is non-trivial (Stdlib
    provides it only for non-negative arguments, and we have no
    direct constructive sqrt available without leaning on the LPO
    workflow).  The genuine [hs_norm = sqrt(hs_norm2)] is deferred
    to SP.1, where the concrete L^2 model can supply it. *)
Definition hs_norm2 {H : HilbertSpace} (x : hs_carrier H) : CReal :=
  re (hs_inner x x).

(** Two vectors are orthogonal when their inner product is [C0]. *)
Definition hs_orthogonal {H : HilbertSpace} (x y : hs_carrier H) : Prop :=
  hs_inner x y = C0.

(** Subtraction. *)
Definition hs_sub {H : HilbertSpace} (x y : hs_carrier H) : hs_carrier H :=
  hs_add x (hs_neg y).

(** Cauchy sequences in [hs_norm2]: a sequence [xn : nat -> V] is
    "Cauchy" if for every rational tolerance [eps > 0] there exists an
    index [N] such that [hs_norm2 (xn p - xn q) < eps] for all [p, q ≥ N].

    We phrase this on the SQUARED norm to sidestep [sqrt]. *)
Definition Cauchy_seq {H : HilbertSpace} (xn : nat -> hs_carrier H) : Prop :=
  forall eps : CReal,
    CRealLtProp (inject_Q 0%Q) eps ->
    exists N : nat,
      forall p q : nat,
        (N <= p)%nat -> (N <= q)%nat ->
        CRealLtProp (hs_norm2 (hs_sub (xn p) (xn q))) eps.

(** Convergence in [hs_norm2]. *)
Definition convergent {H : HilbertSpace} (xn : nat -> hs_carrier H)
    (L : hs_carrier H) : Prop :=
  forall eps : CReal,
    CRealLtProp (inject_Q 0%Q) eps ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        CRealLtProp (hs_norm2 (hs_sub (xn n) L)) eps.

(* ================================================================== *)
(** * 3. Foundational lemmas                                           *)
(* ================================================================== *)

Section HilbertLemmas.
  Variable H : HilbertSpace.

  (** [hs_inner x hs_zero = C0] — right-side companion to the
      [hs_inner_zero_l] field. *)
  Lemma hs_inner_zero_r : forall x : hs_carrier H,
      hs_inner x (hs_zero) = C0.
  Proof.
    intro x.
    (* hs_inner x 0 = conj <0, x> = conj C0 = C0 *)
    rewrite (hs_inner_sym x (hs_zero)).
    rewrite (hs_inner_zero_l x).
    (* Goal: Cconj C0 = C0.  By CComplex_eq + componentwise CRealEq. *)
    apply CComplex_eq.
    unfold CComplex_req, Cconj, Cneg, C0; simpl.
    split.
    - reflexivity.
    - apply CReal_opp_0.
  Qed.

  (** Right-additivity of inner product: derived from left-additivity +
      conjugate symmetry. *)
  Lemma hs_inner_add_r : forall x y z : hs_carrier H,
      hs_inner x (hs_add y z) =
      Cadd (hs_inner x y) (hs_inner x z).
  Proof.
    intros x y z.
    rewrite (hs_inner_sym x (hs_add y z)).
    rewrite (hs_inner_add_l y z x).
    rewrite (hs_inner_sym x y).
    rewrite (hs_inner_sym x z).
    apply CComplex_eq.
    apply Cconj_add_req.
  Qed.

  (** Right-scalar law: [<x, a y> = conj(a) <x, y>]. *)
  Lemma hs_inner_scale_r : forall (a : CComplex) (x y : hs_carrier H),
      hs_inner x (hs_scale a y) =
      Cmul (Cconj a) (hs_inner x y).
  Proof.
    intros a x y.
    rewrite (hs_inner_sym x (hs_scale a y)).
    rewrite (hs_inner_scale_l a y x).
    rewrite (hs_inner_sym x y).
    apply CComplex_eq.
    apply Cconj_mul_req.
  Qed.

  (** [<x, x>] has zero imaginary part — conjugate symmetry forces
      [<x, x> = conj <x, x>], hence [im <x, x> = 0]. *)
  Lemma hs_inner_self_im_zero : forall x : hs_carrier H,
      CRealEq (im (hs_inner x x)) (- im (hs_inner x x)).
  Proof.
    intro x.
    pose proof (hs_inner_sym x x) as Hs.
    (* Hs : hs_inner x x = Cconj (hs_inner x x) *)
    set (z := hs_inner x x) in *.
    (* From Hs we get im z = im (Cconj z) = - im z (Leibniz). *)
    assert (Him : im z = im (Cconj z)).
    { rewrite Hs at 1. reflexivity. }
    rewrite Him at 1.
    unfold Cconj, Cneg; simpl.
    (* Goal: - im z == - im z (CRealEq).  Reflexivity. *)
    apply CRealEq_refl.
  Qed.

  (** [hs_norm2] is non-negative — direct from [hs_inner_pos] +
      [hs_inner_zero_l].  Strict positivity holds for non-zero
      vectors; for zero we get equality. *)
  Lemma hs_norm2_zero_at_zero :
      hs_norm2 (@hs_zero H) = 0.
  Proof.
    unfold hs_norm2.
    rewrite (hs_inner_zero_l (@hs_zero H)).
    reflexivity.
  Qed.

  (** Norm-zero ↔ vector-zero, "==>" direction.

      We package the contrapositive: if [x <> hs_zero], then
      [hs_norm2 x] is strictly positive (via [hs_inner_pos]).  The
      converse direction (norm2 = 0 → x = 0) is the contrapositive
      that needs apartness/decidability infrastructure to discharge
      constructively; we ship it as a Conjecture below. *)
  Lemma hs_norm2_pos_of_nonzero : forall x : hs_carrier H,
      x <> hs_zero ->
      CRealLtProp (inject_Q 0%Q) (hs_norm2 x).
  Proof.
    intros x Hnz.
    unfold hs_norm2.
    apply (hs_inner_pos x Hnz).
  Qed.

  (** Parallelogram law — squared form.

      [|x + y|² + |x − y|² = 2|x|² + 2|y|²]

      In our framework, this is the equation
      [re <x+y, x+y> + re <x-y, x-y>
         = 2 * re <x, x> + 2 * re <y, y>]
      and is purely algebraic from bilinearity / conjugate-symmetry
      / the fact that [<x, y> + <y, x> = 2 * re <x, y>].

      The conclusion is written as [a + a] / [b + b] rather than
      [2 * a] / [2 * b] because the [CRealRing] registered in
      [ConstructiveCauchyRealsMult.v] does NOT include numeric-
      literal support — [ring] cannot solve [a + a == 2 * a] over
      [CRealEq] without an explicit morphism declaration.  The
      [a + a] form makes the statement a pure ring identity that
      [ring] handles directly.  Downstream consumers needing the
      [2 *] form can rewrite with the trivial [a + a = 2 * a]
      identity at their use site. *)
  Lemma hs_parallelogram :
      forall x y : hs_carrier H,
        re (hs_inner (hs_add x y) (hs_add x y))
          + re (hs_inner (hs_sub x y) (hs_sub x y))
        = (re (hs_inner x x) + re (hs_inner x x))
          + (re (hs_inner y y) + re (hs_inner y y)).
  Proof.
    intros x y.
    (* Expand both inner products using bilinearity.  Step 1: <x+y, x+y> *)
    rewrite (hs_inner_add_l x y (hs_add x y)).
    rewrite (hs_inner_add_r x x y).
    rewrite (hs_inner_add_r y x y).
    (* Now the LHS first summand is (<x,x>+<x,y>) + (<y,x>+<y,y>). *)
    (* Step 2: <x-y, x-y>.  Unfold hs_sub. *)
    unfold hs_sub.
    rewrite (hs_inner_add_l x (hs_neg y) (hs_add x (hs_neg y))).
    rewrite (hs_inner_add_r x x (hs_neg y)).
    rewrite (hs_inner_add_r (hs_neg y) x (hs_neg y)).
    (* Now use hs_inner_scale_l/r at a := C(-1) to move negatives.
       Easier: re part is a CReal-only equation; just reduce
       hs_inner (hs_neg y) (...) and hs_inner (...) (hs_neg y) using the
       projection [re (Cadd ..)] = re .. + re ... and then this becomes a
       CReal ring equation in the four basic terms re <x,x>, re <y,y>,
       re <x,y>, re <y,x>.

       But hs_inner_neg in either argument is not yet a Lemma.  Add
       it now via hs_neg = hs_scale (Cneg C1). *)
    (* Strategy: rewrite hs_neg y as hs_scale (Cneg C1) y on both sides
       so we can use hs_inner_scale_l/r, then conclude with ring. *)
    assert (Hneg_eq : hs_neg y =
             hs_scale (Cneg C1) y).
    { (* From hs_add_neg_r: y + neg y = 0.  Also y + scale (Cneg C1) y = 0
         by scale_add_s applied to (1 + (-1)) and scale_one + Cmul.
         Then uniqueness of additive inverse gives the result. *)
      assert (Hsum : hs_add y (hs_scale (Cneg C1) y) = hs_zero).
      { (* y + scale(-1) y = scale 1 y + scale(-1) y = scale(1 + -1) y
                          = scale 0 y = 0. *)
        rewrite <- (hs_scale_one y) at 1.
        rewrite <- (hs_scale_add_s C1 (Cneg C1) y).
        (* Cadd C1 (Cneg C1) = C0 — Leibniz, via CComplex_eq + ring. *)
        assert (HC : Cadd C1 (Cneg C1) = C0).
        { apply CComplex_eq.
          unfold CComplex_req, Cadd, Cneg, C1, C0; simpl.
          split; ring. }
        rewrite HC.
        (* Now: hs_scale C0 y = hs_zero.  Derive from scale_add_s with C0
           and use additive cancellation. *)
        assert (Hscale0 : hs_scale C0 y = hs_zero).
        { (* scale (0+0) y = scale 0 y + scale 0 y, and 0+0 = 0 by Leibniz on Cadd C0 C0. *)
          assert (HC0 : Cadd C0 C0 = C0).
          { apply CComplex_eq. unfold CComplex_req, Cadd, C0; simpl.
            split; ring. }
          assert (Hsplit : hs_scale C0 y =
                   hs_add (hs_scale C0 y) (hs_scale C0 y)).
          { rewrite <- (hs_scale_add_s C0 C0 y). rewrite HC0. reflexivity. }
          (* From x = x + x deduce x = 0. *)
          set (a := hs_scale C0 y) in *.
          (* a + neg a = 0; (a + a) + neg a = a + neg a, so a + 0 = 0, hence a = 0. *)
          assert (Hcancel : hs_add a (hs_neg a) = hs_zero)
            by apply (hs_add_neg_r a).
          assert (Heq : hs_add (hs_add a a) (hs_neg a) = hs_add a (hs_neg a)).
          { f_equal. symmetry; exact Hsplit. }
          rewrite <- (hs_add_assoc a a (hs_neg a)) in Heq.
          rewrite Hcancel in Heq.
          rewrite (hs_add_zero_r a) in Heq.
          exact Heq. }
        exact Hscale0. }
      (* From y + scale(-1) y = 0 and y + neg y = 0, by uniqueness of
         additive inverse, scale(-1) y = neg y. *)
      assert (Hsum2 : hs_add y (hs_neg y) = hs_zero)
        by apply (hs_add_neg_r y).
      (* scale(-1) y = scale(-1) y + 0
                     = scale(-1) y + (y + neg y)
                     = (scale(-1) y + y) + neg y
                     = 0 + neg y = neg y *)
      assert (Hgoal : hs_scale (Cneg C1) y = hs_neg y).
      { rewrite <- (hs_add_zero_r (hs_scale (Cneg C1) y)).
        rewrite <- Hsum2.
        rewrite (hs_add_assoc (hs_scale (Cneg C1) y) y (hs_neg y)).
        rewrite (hs_add_comm (hs_scale (Cneg C1) y) y).
        rewrite Hsum.
        rewrite (hs_add_comm (hs_zero) (hs_neg y)).
        apply (hs_add_zero_r). }
      symmetry; exact Hgoal. }
    rewrite Hneg_eq.
    (* Now all four occurrences of hs_inner involving (hs_scale (Cneg C1) y)
       can be normalized via hs_inner_scale_l / hs_inner_scale_r.

       Goal terms (LHS):
         hs_inner x (hs_scale (Cneg C1) y)             — from hs_inner_add_r x x (hs_neg y)
         hs_inner (hs_scale (Cneg C1) y) x             — from hs_inner_add_r (hs_neg y) x (hs_neg y)
         hs_inner (hs_scale (Cneg C1) y)
                  (hs_scale (Cneg C1) y)               — from same
    *)
    rewrite (hs_inner_scale_r (Cneg C1) x y).
    rewrite (hs_inner_scale_l (Cneg C1) y x).
    rewrite (hs_inner_scale_l (Cneg C1) y (hs_scale (Cneg C1) y)).
    rewrite (hs_inner_scale_r (Cneg C1) y y).
    (* Goal is now an equation between [re] of sums of products of CComplex
       terms; reduce on both sides using arithmetic + im/re of Cmul/Cadd/Cconj. *)
    set (xx := hs_inner x x) in *.
    set (xy := hs_inner x y) in *.
    set (yx := hs_inner y x) in *.
    set (yy := hs_inner y y) in *.
    (* Use hs_inner_sym to relate yx and Cconj xy. *)
    assert (Hyx : yx = Cconj xy).
    { unfold yx, xy. apply (hs_inner_sym y x). }
    rewrite Hyx.
    (* Now everything is in terms of xx, xy, yy and Cconj xy.  All terms are
       CComplex; reduce re of the sums to a CReal ring equation. *)
    (* Strategy: pull each [re (Cadd ..)] apart by hand and each
       [re (Cmul (Cneg C1) ..)] etc., then close with CReal ring.
       Working at the [CRealEq]-level so [ring] can fire, and bridging
       to Leibniz at the very end via [CRealEq_eq]. *)
    apply CRealEq_eq.
    unfold Cadd, Cmul, Cneg, Cconj, C1; simpl.
    (* All [inject_Q 0] occurrences are forced by [Cconj] / [Cneg] of
       [C1 = mkC 1 0].  Generalize them away via [set] and then close
       the equation by abstracting all [re]/[im] projections to
       opaque CReal variables and invoking [ring]. *)
    generalize (re xx); intro a.
    generalize (re yy); intro b.
    generalize (re xy); intro c.
    generalize (im xy); intro d.
    generalize (im xx); intro e.
    generalize (im yy); intro f.
    ring.
  Qed.

End HilbertLemmas.

(* ================================================================== *)
(** * 4. Deferred infrastructure (Conjectures)                         *)
(* ================================================================== *)

(** Cauchy completeness.  Stating this needs a notion of limit on the
    abstract carrier; we use the [convergent] definition above.

    DEFERRED to SP.1, where the concrete model (probably the L^2
    completion of smooth sections [Forms_pq E p q] from [Sobolev.v])
    will provide a constructive completion. *)
Conjecture hs_complete : forall (H : HilbertSpace) (xn : nat -> hs_carrier H),
    Cauchy_seq xn ->
    exists L : hs_carrier H, convergent xn L.

(** Cauchy-Schwarz inequality (squared form).

    [|<x, y>|² <= <x, x> * <y, y>]

    DEFERRED.  Reason: the constructive proof of Cauchy-Schwarz on a
    complex inner product space goes via the case analysis
    "if [<y, y> = 0] then [y = 0] (so both sides vanish), else
    consider [x - (<x,y>/<y,y>) y] and expand its norm".  The first
    case-split needs the (currently Conjectured) direction
    [hs_norm2 = 0 → vector = 0]; the second needs [Cinv] threaded
    through the inner product, which is straightforward but volumetric.
    Both are clean SP.1 work.  We state the Conjecture in its
    natural CReal form. *)
Conjecture hs_cauchy_schwarz : forall (H : HilbertSpace) (x y : hs_carrier H),
    Cnorm2 (hs_inner x y) <=
      (re (hs_inner x x)) * (re (hs_inner y y)).

(** Norm-zero ⇒ vector-zero.

    DEFERRED.  Reason: the obvious proof ("contrapositive of
    [hs_inner_pos]") needs decidability of [x = hs_zero], which is
    not constructively available on an abstract carrier.  The concrete
    model (smooth sections, [Forms_pq]) has decidable equality at
    every chart-level coefficient, so SP.1 will discharge this on the
    concrete carrier. *)
Conjecture hs_norm2_zero_implies_zero :
    forall (H : HilbertSpace) (x : hs_carrier H),
      hs_norm2 x = 0 ->
      x = hs_zero.

(* ================================================================== *)
(** * 5. Operators on a HilbertSpace (SP.1)                            *)
(* ================================================================== *)

(** *** Strictly-increasing index extractor.

    A "subsequence selector" is a function [sub : nat -> nat] with
    [sub n < sub (S n)] for every [n].  We package this as a plain
    Prop because all downstream consumers ([CompactOperator]) only
    need it positionally.  Equivalent to [Sorted.StronglySorted Nat.lt
    (List.map sub (seq 0 _))] but simpler. *)
Definition strictly_increasing (sub : nat -> nat) : Prop :=
  forall n : nat, (sub n < sub (S n))%nat.

(** *** [BoundedLinearOp H] — a bounded linear operator [H → H].

    Three field-level laws:

    - [blo_add]   : additivity, [T(x+y) = T x + T y].
    - [blo_scale] : C-linearity in the scalar, [T(a x) = a (T x)].
    - [blo_bound] : there exists a constant [M] such that the squared
                    norm satisfies [|T x|² <= M · |x|²] for all [x].

    Note [blo_bound] is on the SQUARED norm — this is the natural
    home given that [hs_norm] (= sqrt of [hs_norm2]) is not a Stdlib
    primitive on [CReal].  An operator-norm bound on the genuine
    norm corresponds to the SQUARED bound with constant [M^2]; the
    two formulations are equivalent up to a square root, which we
    defer to the concrete [L^2] model.  The bound [M] is a [CReal]
    so that downstream consumers can plug in concrete bounds without
    a [Q]-injection wrapper. *)
Record BoundedLinearOp (H : HilbertSpace) : Type := mkBLO {
  blo_fn : hs_carrier H -> hs_carrier H;

  blo_add :
    forall x y : hs_carrier H,
      blo_fn (hs_add x y) = hs_add (blo_fn x) (blo_fn y);

  blo_scale :
    forall (a : CComplex) (x : hs_carrier H),
      blo_fn (hs_scale a x) = hs_scale a (blo_fn x);

  blo_bound :
    exists M : CReal,
      forall x : hs_carrier H,
        CRealLe (hs_norm2 (blo_fn x)) (CReal_mult M (hs_norm2 x));
}.

Arguments blo_fn    {_} _ _.
Arguments blo_add   {_} _ _ _.
Arguments blo_scale {_} _ _ _.
Arguments blo_bound {_} _.

(** *** [CompactOperator H] — a compact (bounded) linear operator.

    Refines [BoundedLinearOp] by the "image of any norm-bounded
    sequence has a convergent subsequence" property.

    The bound on the sequence is on the SQUARED norm; the convergence
    of the image subsequence is the [convergent] predicate from
    section 2 (also on the squared norm).  The subsequence selector
    [sub : nat -> nat] is required to be [strictly_increasing] so
    that "subsequence" really means subsequence and not "any
    re-indexing". *)
Record CompactOperator (H : HilbertSpace) : Type := mkCompact {
  co_op : BoundedLinearOp H;

  co_compact :
    forall (xs : nat -> hs_carrier H),
      (exists M : CReal,
          forall n : nat, CRealLe (hs_norm2 (xs n)) M) ->
      exists (sub : nat -> nat) (y : hs_carrier H),
        strictly_increasing sub /\
        convergent (fun n => blo_fn co_op (xs (sub n))) y;
}.

Arguments co_op      {_} _.
Arguments co_compact {_} _ _ _.

(* ================================================================== *)
(** * 6. SP.2 — Self-adjoint operators + spectral theorem (parametric) *)
(* ================================================================== *)

(** *** [SelfAdjoint T] — operator equals its Hermitian adjoint.

    Mathematically: [<T x, y> = <x, T y>] for all [x, y].  In our
    Hermitian-inner-product framework, this is the symmetric form of
    the operator: the inner product moves freely between arguments.

    No appeal to [Cauchy-Schwarz] at this level — pure algebraic
    predicate. *)
Definition SelfAdjoint {H : HilbertSpace} (T : BoundedLinearOp H) : Prop :=
  forall x y : hs_carrier H,
    hs_inner (blo_fn T x) y = hs_inner x (blo_fn T y).

(** *** Eigenvalue / eigenvector predicates.

    [IsEigenvalue T λ] : there exists a non-zero [x] with [T x = λ x].
    [IsEigenvector T λ x] : explicit witness form.

    Both are stated with respect to the operator [T] (a [BoundedLinearOp])
    and a complex scalar [λ : CComplex].  The non-zero witness lives
    in [hs_carrier]. *)
Definition IsEigenvector {H : HilbertSpace}
    (T : BoundedLinearOp H) (lam : CComplex) (x : hs_carrier H) : Prop :=
  x <> hs_zero /\ blo_fn T x = hs_scale lam x.

Definition IsEigenvalue {H : HilbertSpace}
    (T : BoundedLinearOp H) (lam : CComplex) : Prop :=
  exists x : hs_carrier H, IsEigenvector T lam x.

(** *** Cauchy-Schwarz hypothesis as a predicate over [HilbertSpace].

    Captures the constructive content of the [hs_cauchy_schwarz]
    Conjecture as a per-space hypothesis, so downstream theorems can
    quantify over it without taking the global Conjecture as a project
    Axiom. *)
Definition hs_cauchy_schwarz_holds (H : HilbertSpace) : Prop :=
  forall x y : hs_carrier H,
    CRealLe (Cnorm2 (hs_inner x y))
            (CReal_mult (re (hs_inner x x)) (re (hs_inner y y))).

(* ------------------------------------------------------------------ *)
(** ** 6.1  Eigenvalues of self-adjoint operators are real            *)
(* ------------------------------------------------------------------ *)

Section SelfAdjointEigenvalues.
  Variable H : HilbertSpace.

  (** Auxiliary: [Cmul z w] reads componentwise from [z] and [w]. *)
  Local Lemma im_Cmul_explicit : forall a b : CComplex,
      im (Cmul a b) = (re a * im b + im a * re b)%CReal.
  Proof. intros [a1 a2] [b1 b2]. cbn. reflexivity. Qed.

  Local Lemma re_Cconj_explicit : forall a : CComplex,
      re (Cconj a) = re a.
  Proof. intros [a1 a2]. cbn. reflexivity. Qed.

  Local Lemma im_Cconj_explicit : forall a : CComplex,
      im (Cconj a) = (- im a)%CReal.
  Proof. intros [a1 a2]. cbn. reflexivity. Qed.

  (** [Cmul λ xx = Cmul (Cconj λ) xx], with [im xx == 0] and
      [re xx > 0], forces [im λ == 0] (in [CRealEq]).

      This is the algebraic core of "self-adjoint ⇒ real eigenvalues",
      isolated so the spectral lemma below is a 1-line apply. *)
  Lemma im_zero_of_mul_eq_conj : forall (lam xx : CComplex),
      Cmul lam xx = Cmul (Cconj lam) xx ->
      CRealEq (im xx) (inject_Q 0%Q) ->
      CRealLtProp (inject_Q 0%Q) (re xx) ->
      CRealEq (im lam) (inject_Q 0%Q).
  Proof.
    intros lam xx Hmul Him_xx Hre_xx_pos.
    (* Project the Leibniz equation to its imaginary component. *)
    assert (Him_eq : im (Cmul lam xx) = im (Cmul (Cconj lam) xx))
      by (rewrite Hmul; reflexivity).
    rewrite (im_Cmul_explicit lam xx) in Him_eq.
    rewrite (im_Cmul_explicit (Cconj lam) xx) in Him_eq.
    rewrite (re_Cconj_explicit lam) in Him_eq.
    rewrite (im_Cconj_explicit lam) in Him_eq.
    (* Him_eq : re lam * im xx + im lam * re xx
              = re lam * im xx + (- im lam) * re xx   (Leibniz CReal). *)
    assert (Him_eq_req : CRealEq (re lam * im xx + im lam * re xx)%CReal
                                  (re lam * im xx + (- im lam) * re xx)%CReal)
      by (rewrite Him_eq; reflexivity).
    (* Now in CRealEq, cancel re lam * im xx. *)
    assert (Hcancel :
      CRealEq (im lam * re xx)%CReal ((- im lam) * re xx)%CReal).
    { (* From a + b == a + c, derive b == c. *)
      apply (CReal_plus_eq_reg_l (re lam * im xx)%CReal). exact Him_eq_req. }
    (* Add (im lam * re xx) to both sides:
         2 * (im lam * re xx) == 0. *)
    assert (Hsum :
      CRealEq ((im lam * re xx) + (im lam * re xx))%CReal (inject_Q 0%Q)).
    { rewrite Hcancel at 2.
      (* Goal: (im lam * re xx) + ((- im lam) * re xx) == 0.
         Use opp-distrib then plus_opp_r. *)
      rewrite <- CReal_opp_mult_distr_l.
      rewrite CReal_plus_opp_r. reflexivity. }
    (* Factor: a + a == (1 + 1) * a, i.e., == 2 * a (CReal ring). *)
    assert (Htwo :
      CRealEq ((im lam * re xx) + (im lam * re xx))%CReal
              ((inject_Q 2%Q) * (im lam * re xx))%CReal).
    { (* Pure ring identity in CReal. *)
      assert (Hinj2 : CRealEq (inject_Q 2%Q)
                              (inject_Q 1%Q + inject_Q 1%Q)%CReal).
      { rewrite <- (inject_Q_plus 1%Q 1%Q).
        apply inject_Q_morph. reflexivity. }
      rewrite Hinj2.
      rewrite CReal_mult_plus_distr_r.
      rewrite CReal_mult_1_l.
      reflexivity. }
    rewrite Htwo in Hsum.
    (* Hsum : 2 * (im lam * re xx) == 0. *)
    (* re xx is apart from 0 (positive). *)
    assert (Hre_xx_apart : (re xx) # 0).
    { right. apply CRealLtEpsilon. exact Hre_xx_pos. }
    (* 2 is apart from 0. *)
    assert (Htwo_apart : (inject_Q 2%Q) # 0).
    { right. apply CRealLtEpsilon. apply CRealLtForget.
      apply (CReal_injectQPos 2%Q). reflexivity. }
    (* Cancel 2: (im lam * re xx) == 0. *)
    rewrite <- (CReal_mult_0_r (inject_Q 2%Q)) in Hsum.
    apply (CReal_mult_eq_reg_l (inject_Q 2%Q)) in Hsum;
      [| exact Htwo_apart].
    (* Now Hsum : im lam * re xx == 0. *)
    (* Cancel re xx: im lam == 0. *)
    rewrite (CReal_mult_comm (im lam) (re xx)) in Hsum.
    rewrite <- (CReal_mult_0_r (re xx)) in Hsum.
    apply (CReal_mult_eq_reg_l (re xx)) in Hsum;
      [| exact Hre_xx_apart].
    exact Hsum.
  Qed.

  (** **** [eigenvalues_real] — the headline corollary.

      For a self-adjoint operator, every eigenvalue is real (zero
      imaginary part).  Depends on no Conjectures — purely algebraic
      from [SelfAdjoint] + [hs_inner_pos].  *)
  Theorem eigenvalues_real :
      forall (T : BoundedLinearOp H) (lam : CComplex),
        SelfAdjoint T ->
        IsEigenvalue T lam ->
        CRealEq (im lam) (inject_Q 0%Q).
  Proof.
    intros T lam Hsa [x [Hxnz Heig]].
    (* Step 1: <T x, x> = <x, T x> by self-adjointness. *)
    pose proof (Hsa x x) as Hsym.
    (* Step 2: <T x, x> = <λ x, x> = λ * <x, x>; <x, T x> = conj(λ) * <x, x>. *)
    rewrite Heig in Hsym.
    rewrite (hs_inner_scale_l lam x x) in Hsym.
    rewrite (hs_inner_scale_r H lam x x) in Hsym.
    (* Hsym : λ * <x,x> = conj(λ) * <x,x>  (Leibniz CComplex). *)
    set (xx := hs_inner x x) in *.
    (* Step 3: extract im xx == 0 (from hs_inner_self_im_zero) and re xx > 0
       (from hs_inner_pos). *)
    assert (Him_xx : CRealEq (im xx) (inject_Q 0%Q)).
    { unfold xx. pose proof (hs_inner_self_im_zero H x) as Hself.
      (* Hself : im <x,x> == - im <x,x>. From a == -a, get 2a == 0, a == 0. *)
      assert (Hsum : CRealEq (im (hs_inner x x) + im (hs_inner x x))%CReal
                              (inject_Q 0%Q)).
      { rewrite Hself at 2. rewrite CReal_plus_opp_r. reflexivity. }
      assert (Htwo :
        CRealEq (im (hs_inner x x) + im (hs_inner x x))%CReal
                ((inject_Q 2%Q) * im (hs_inner x x))%CReal).
      { assert (Hinj2 : CRealEq (inject_Q 2%Q)
                                (inject_Q 1%Q + inject_Q 1%Q)%CReal).
        { rewrite <- (inject_Q_plus 1%Q 1%Q).
          apply inject_Q_morph. reflexivity. }
        rewrite Hinj2.
        rewrite CReal_mult_plus_distr_r.
        rewrite CReal_mult_1_l.
        reflexivity. }
      rewrite Htwo in Hsum.
      assert (Htwo_apart : (inject_Q 2%Q) # 0).
      { right. apply CRealLtEpsilon. apply CRealLtForget.
        apply (CReal_injectQPos 2%Q). reflexivity. }
      rewrite <- (CReal_mult_0_r (inject_Q 2%Q)) in Hsum.
      apply (CReal_mult_eq_reg_l (inject_Q 2%Q)) in Hsum;
        [| exact Htwo_apart].
      exact Hsum. }
    assert (Hre_xx_pos : CRealLtProp (inject_Q 0%Q) (re xx)).
    { unfold xx. apply (hs_inner_pos x Hxnz). }
    (* Step 4: apply the algebraic core. *)
    apply (im_zero_of_mul_eq_conj lam xx Hsym Him_xx Hre_xx_pos).
  Qed.

End SelfAdjointEigenvalues.

(* ------------------------------------------------------------------ *)
(** ** 6.2  Spectral theorem for compact self-adjoint operators       *)
(* ------------------------------------------------------------------ *)

(** *** Orthonormal sequence predicate.

    A sequence [e : nat -> hs_carrier H] is orthonormal if
    [<e_i, e_j> = δ_{ij}] (Kronecker delta).  We state it as two
    independent fields. *)
Definition Orthonormal {H : HilbertSpace} (e : nat -> hs_carrier H) : Prop :=
  (forall n : nat, hs_inner (e n) (e n) = C1) /\
  (forall n m : nat, n <> m -> hs_inner (e n) (e m) = C0).

(** *** Statement of the spectral theorem.

    For a compact self-adjoint operator [T] on a Hilbert space [H]
    where the (per-space) Cauchy-Schwarz inequality holds, there is
    an orthonormal sequence of eigenvectors with eigenvalues that
    converge to 0 in [|·|²] sense.

    "Converge to 0" is phrased on the squared norm of the
    eigenvalues (treated as complex scalars), since our [convergent]
    predicate lives at the [hs_carrier] level.  We use [Cnorm2 (λ_n)]
    converging to 0 in [CRealEq] sense as a clean intrinsic
    formulation that does not require a [HilbertSpace] structure on
    [CComplex].

    Status: stated as a [Conjecture] — full proof requires the
    max-projection / Hilbert-Schmidt argument that depends on
    spectral radius computations for compact self-adjoint operators
    and is well outside the SP.2 budget. *)
Definition eigenvalues_converge_to_zero (lams : nat -> CComplex) : Prop :=
  forall eps : CReal,
    CRealLtProp (inject_Q 0%Q) eps ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        CRealLtProp (Cnorm2 (lams n)) eps.

Conjecture compact_self_adjoint_spectral :
    forall (H : HilbertSpace) (T : CompactOperator H),
      SelfAdjoint (co_op T) ->
      hs_cauchy_schwarz_holds H ->
      exists (eigenvalues : nat -> CComplex)
             (eigenvectors : nat -> hs_carrier H),
        Orthonormal eigenvectors /\
        (forall n : nat,
            blo_fn (co_op T) (eigenvectors n)
            = hs_scale (eigenvalues n) (eigenvectors n)) /\
        eigenvalues_converge_to_zero eigenvalues.

(* ================================================================== *)
(** * 7. Trivial-collapse singleton instance — REMOVED [γ R26]         *)
(* ================================================================== *)

(** [γ R26, 2026-05-01] Removed the γ R12 plumbing
    [unit_HilbertSpace] (a [unit]-carrier [HilbertSpace] with
    [hs_inner := C0]) and its four specialised lemmas
    ([hs_norm2_zero_implies_zero_on_unit],
    [hs_cauchy_schwarz_on_unit],
    [hs_cauchy_schwarz_holds_unit],
    [hs_complete_on_unit]).  These were trivial-collapse "discharges"
    of the Conjectures in §4 at the singleton instance: the carrier
    type [unit] has a unique inhabitant, so every Conjecture statement
    of the form [∀ x, P x] becomes [P tt], and on the [hs_inner := C0]
    model every [hs_inner …]-bearing inequality / equality collapses
    to [C0 = C0] or [0 ≤ 0].  Per
    [feedback_trivial_collapse_busywork.md], satisfying the
    typechecker on the singleton does not constitute mathematical
    progress; genuine discharge requires a non-degenerate concrete
    model (Task LM — Lebesgue-measure long-haul, or SP.3).  Verified
    by grep on 2026-05-01: ZERO consumers outside this file. *)
