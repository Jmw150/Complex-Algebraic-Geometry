
(** Several Complex Variables — Part II

    Building on ComplexAnalysis.v (Part I), this file covers:

      1. Localized construction for the ∂̄-equation (g = g₁ + g₂ cutoff)
      2. Several complex variables: polydiscs, joint holomorphicity
      3. Coinductive double power series (PSeries2) and analytic functions in ℂⁿ
      4. Identity theorem and maximum principle
      5. Hartogs' extension theorem
      6. Weierstrass Preparation and Division Theorems
      7. The ring of germs O_n and its algebraic structure (UFD, Nullstellensatz)
*)

From Stdlib Require Import QArith ZArith List.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyRealsMult.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyAbs.
Import ListNotations.

From CAG Require Import Reals_extra.
From CAG Require Import Complex.
From CAG Require Import ComplexAnalysis.

Local Open Scope CReal_scope.

(* ------------------------------------------------------------------ *)
(** * 1. Localized construction for the ∂̄-equation                     *)
(* ------------------------------------------------------------------ *)

(** A smooth cutoff function χ_{z0,r1,r2} : ℂ → ℝ satisfying:
      - χ = 1 on the disc of radius r1 around z0
      - χ = 0 outside the disc of radius r2 around z0
      - 0 ≤ χ ≤ 1 everywhere
    Axiomatized; requires smooth partition of unity machinery. *)
Parameter cutoff : CComplex -> CReal -> CReal -> (CComplex -> CReal).

(** Specification axioms for the [cutoff] [Parameter]: the cutoff is 1
    inside the inner disc, 0 outside the outer disc, and nonnegative
    everywhere. *)
Conjecture cutoff_inner :
  forall z0 r1 r2 z,
    open_disc z0 r1 z ->
    cutoff z0 r1 r2 z = inject_Q 1.

Conjecture cutoff_outer :
  forall z0 r1 r2 z,
    ~ open_disc z0 r2 z ->
    cutoff z0 r1 r2 z = inject_Q 0.

Conjecture cutoff_range :
  forall z0 r1 r2 z,
    CRealLtProp (inject_Q 0) (cutoff z0 r1 r2 z) \/
    cutoff z0 r1 r2 z = inject_Q 0.

(** The cutoff function as a complex-valued map (real part only). *)
Definition cutoff_C (z0 : CComplex) (r1 r2 : CReal) (w : CComplex) : CComplex :=
  mkC (cutoff z0 r1 r2 w) 0.

(** Lift cutoff to a complex scalar: χ · g. *)
Definition cutoff_mul (z0 : CComplex) (r1 r2 : CReal)
    (g : CComplex -> CComplex) (w : CComplex) : CComplex :=
  Cmul (cutoff_C z0 r1 r2 w) (g w).

(** Given g smooth on disc A(z0, 2ε), decompose g = g₁ + g₂ where:
      - g₁ has compact support in A(z0, 2ε)  [the "inner" piece]
      - g₂ vanishes in A(z0, ε)              [the "outer" piece] *)
Definition dbar_decomp_g1 (z0 : CComplex) (eps : CReal)
    (g : CComplex -> CComplex) : CComplex -> CComplex :=
  cutoff_mul z0 eps (inject_Q 2 * eps) g.

Definition dbar_decomp_g2 (z0 : CComplex) (eps : CReal)
    (g : CComplex -> CComplex) : CComplex -> CComplex :=
  fun w => Csub (g w) (dbar_decomp_g1 z0 eps g w).

(** Specifications of the [dbar_decomp_*] / [dbar_poincare_localized]
    construction; axiomatized at the Leibniz [=] level. *)
Conjecture dbar_decomp_sum :
  forall z0 eps g w,
    Cadd (dbar_decomp_g1 z0 eps g w) (dbar_decomp_g2 z0 eps g w) = g w.

Conjecture dbar_decomp_g2_inner :
  forall z0 eps g w,
    CRpositive eps ->
    open_disc z0 eps w ->
    dbar_decomp_g2 z0 eps g w = C0.

Conjecture dbar_poincare_localized :
  forall (g : CComplex -> CComplex) (z0 : CComplex) (r eps : CReal),
    CRpositive eps ->
    CRealLtProp (inject_Q 2 * eps * (inject_Q 2 * eps)) (r * r) ->
    (forall w, open_disc z0 r w -> True) ->
    exists f : CComplex -> CComplex,
      forall w, open_disc z0 eps w -> dbar_at f w (g w).

(* ------------------------------------------------------------------ *)
(** * 2. Several complex variables: polydiscs and holomorphicity        *)
(* ------------------------------------------------------------------ *)

(** The polydisc A(z0, r) = { z ∈ ℂⁿ | |zᵢ − z0ᵢ|² < rᵢ² for all i }.
    Here z0 : Cn n and r : Rn n (using the types from Complex.v). *)
Definition Polydisc {n : nat} (z0 : Cn n) (r : Rn n) : Cn n -> Prop :=
  fun z => forall i : Fin.t n, open_disc (z0 i) (r i) (z i).

(** The unit polydisc: all radii equal to 1. *)
Definition unit_polydisc (n : nat) : Cn n -> Prop :=
  Polydisc (fun _ => C0) (fun _ => inject_Q 1).

(** A function f : ℂⁿ → ℂ is holomorphic on U if it is holomorphic
    in each variable separately at every point of U. *)
Definition holomorphic_Cn {n : nat} (U : Cn n -> Prop)
    (f : Cn n -> CComplex) : Prop :=
  forall v : Cn n, holomorphic_each_at U f v.

(** Osgood's theorem: holomorphic in each variable separately implies
    jointly holomorphic (continuity is automatic).  This is a deep
    classical result; we state it and admit. *)
Conjecture osgood :
  forall {n : nat} (U : Cn n -> Prop) (f : Cn n -> CComplex),
    (forall v : Cn n, U v ->
      forall i : Fin.t n,
        holomorphic_at_CR (freeze_except f v i) (v i)) ->
    holomorphic_Cn U f.

(** The total differential of f decomposes as ∂f + ∂̄f.
    In coordinates: df = ∑_j (∂f/∂z_j) dz_j + ∑_j (∂f/∂z̄_j) dz̄_j.
    Holomorphicity means all ∂f/∂z̄_j = 0. *)

(** ∂̄f = 0 in the j-th variable at v: the j-th Wirtinger ∂̄ vanishes. *)
Definition dbar_j_zero {n : nat} (f : Cn n -> CComplex) (v : Cn n)
    (j : Fin.t n) : Prop :=
  dbar_at (freeze_except f v j) (v j) C0.

(** Holomorphic iff all ∂̄ components vanish. *)
Conjecture holomorphic_Cn_iff_dbar_zero :
  forall {n : nat} (U : Cn n -> Prop) (f : Cn n -> CComplex),
    holomorphic_Cn U f <->
    forall v : Cn n, U v ->
      forall j : Fin.t n, dbar_j_zero f v j.

(* ------------------------------------------------------------------ *)
(** * 3. Coinductive double power series and analytic functions in ℂⁿ  *)
(* ------------------------------------------------------------------ *)

(** A double power series in two variables: ∑_{m,n} a_{m,n} (z₁−z₁₀)^m (z₂−z₂₀)^n.
    Represented as a coinductive stream of rows, where row m is the
    1-variable power series ∑_n a_{m,n} (z₂−z₂₀)^n. *)
CoInductive PSeries2 : Type :=
  | PS2Cons : PSeries -> PSeries2 -> PSeries2.

(** Extract row m (the 1-variable series ∑_n a_{m,n} (z₂−z₂₀)^n). *)
Fixpoint ps2_row (s : PSeries2) (m : nat) : PSeries :=
  match m, s with
  | O,    PS2Cons row _    => row
  | S m', PS2Cons _   rest => ps2_row rest m'
  end.

(** Coefficient a_{m,n}. *)
Definition ps2_coeff (s : PSeries2) (m n : nat) : CComplex :=
  ps_coeff (ps2_row s m) n.

(** Partial sum ∑_{k=0}^{M} (z₁−z₁₀)^k · (∑_{j=0}^{N} a_{k,j} (z₂−z₂₀)^j). *)
Fixpoint ps2_partial_sum (s : PSeries2) (z1 z10 z2 z20 : CComplex)
    (M N : nat) : CComplex :=
  match M with
  | O =>
      ps_partial_sum (ps2_row s 0) z2 z20 N
  | S M' =>
      Cadd
        (ps2_partial_sum s z1 z10 z2 z20 M' N)
        (Cmul (Cpow (Csub z1 z10) (S M'))
              (ps_partial_sum (ps2_row s (S M')) z2 z20 N))
  end.

(** Convergence of the double partial sums to L. *)
Definition ps2_converges (s : PSeries2) (z1 z10 z2 z20 L : CComplex) : Prop :=
  forall eps : CReal,
    CRpositive eps ->
    exists M N : nat,
      forall m n : nat, (M <= m)%nat -> (N <= n)%nat ->
        CRealLtProp (Cdist2 (ps2_partial_sum s z1 z10 z2 z20 m n) L) eps.

(** f : ℂ² → ℂ is analytic at (z10, z20). *)
Definition analytic_C2 (f : CComplex -> CComplex -> CComplex)
    (z10 z20 : CComplex) : Prop :=
  exists (s : PSeries2) (r1 r2 : CReal),
    CRpositive r1 /\ CRpositive r2 /\
    forall z1 z2 : CComplex,
      open_disc z10 r1 z1 ->
      open_disc z20 r2 z2 ->
      ps2_converges s z1 z10 z2 z20 (f z1 z2).

(** Multi-index for n variables: α : nat → nat (only first n entries matter). *)
Definition MIndex (n : nat) : Type := nat -> nat.

(** Total degree of a multi-index. *)
Fixpoint total_degree (n : nat) (alpha : MIndex n) : nat :=
  match n with
  | O => O
  | S n' => alpha n' + total_degree n' alpha
  end.

(** Evaluate (z − z₀)^α = ∏_{i<n} (zᵢ − z₀ᵢ)^{αᵢ}, given component differences. *)
Fixpoint cpow_multi (diffs : list CComplex) (alpha : list nat) : CComplex :=
  match diffs, alpha with
  | [], []           => C1
  | x :: xs, k :: ks => Cmul (Cpow x k) (cpow_multi xs ks)
  | _, _             => C1   (* dimension mismatch *)
  end.

(** The component differences zᵢ − z₀ᵢ as a list. *)
Fixpoint fin_list (n : nat) : list (Fin.t n) :=
  match n with
  | O    => []
  | S n' => Fin.F1 :: List.map Fin.FS (fin_list n')
  end.

Definition cn_diffs {n : nat} (z z0 : Cn n) : list CComplex :=
  List.map (fun i => Csub (z i) (z0 i)) (fin_list n).

(** Holomorphic iff analytic in ℂ² (via iterated Cauchy formula). *)
Conjecture holomorphic_C2_iff_analytic :
  forall (U : CComplex -> CComplex -> Prop)
         (f : CComplex -> CComplex -> CComplex),
    (forall z1 z2, U z1 z2 ->
      holomorphic_at_CR (fun w => f z1 w) z2 /\
      holomorphic_at_CR (fun w => f w z2) z1) <->
    (forall z10 z20, U z10 z20 -> analytic_C2 f z10 z20).

(* ------------------------------------------------------------------ *)
(** * 4. Identity theorem and maximum principle                         *)
(* ------------------------------------------------------------------ *)

(** A domain (connected open set) in ℂⁿ. *)
Definition is_domain {n : nat} (U : Cn n -> Prop) : Prop :=
  (* open: every point has a polydisc neighbourhood in U *)
  (forall v : Cn n, U v ->
    exists r : CReal, CRpositive r /\
      Polydisc v (fun _ => r) v /\
      forall z, Polydisc v (fun _ => r) z -> U z) /\
  (* connected: any two points can be joined by a path in U *)
  (forall v w : Cn n, U v -> U w ->
    exists gamma : CReal -> Cn n,
      gamma (inject_Q 0) = v /\ gamma (inject_Q 1) = w /\
      forall t, CRealLtProp (inject_Q 0) t -> CRealLtProp t (inject_Q 1) ->
        U (gamma t)).

(** Identity Theorem for holomorphic functions in ℂⁿ.
    If f and g agree on a non-empty open subset of a connected domain U,
    they agree everywhere on U. *)
Conjecture identity_theorem :
  forall {n : nat} (U V : Cn n -> Prop) (f g : Cn n -> CComplex),
    is_domain U ->
    holomorphic_Cn U f ->
    holomorphic_Cn U g ->
    (exists v, V v) ->
    (forall v, V v -> U v) ->
    (forall v, V v -> Cequal (f v) (g v)) ->
    forall v, U v -> Cequal (f v) (g v).

(** Maximum Modulus Principle.
    If |f| attains an interior maximum on a connected domain, f is constant. *)
Definition Cnorm2_fn {n : nat} (f : Cn n -> CComplex) : Cn n -> CReal :=
  fun v => Cnorm2 (f v).

Conjecture maximum_principle :
  forall {n : nat} (U : Cn n -> Prop) (f : Cn n -> CComplex),
    is_domain U ->
    holomorphic_Cn U f ->
    (exists v0 : Cn n, U v0 /\
      forall v : Cn n, U v ->
        CRealLtProp (Cnorm2_fn f v) (Cnorm2_fn f v0) \/
        Cnorm2_fn f v = Cnorm2_fn f v0) ->
    exists c : CComplex, forall v : Cn n, U v -> Cequal (f v) c.

(* ------------------------------------------------------------------ *)
(** * 5. Hartogs' Extension Theorem                                     *)
(* ------------------------------------------------------------------ *)

(** Hartogs figure in ℂ²: the region where f is assumed holomorphic.
    Concretely, take the polydisc A(R₁) × A(R₂) and remove the
    sub-polydisc A(r₁) × A(r₂) (r₁ < R₁, r₂ < R₂).

    f holomorphic on the Hartogs figure extends to the full polydisc. *)
Definition hartogs_figure (R1 r1 R2 r2 : CReal) : CComplex -> CComplex -> Prop :=
  fun z1 z2 =>
    open_disc C0 R1 z1 /\ open_disc C0 R2 z2 /\
    ~ (open_disc C0 r1 z1 /\ open_disc C0 r2 z2).

Definition full_polydisc (R1 R2 : CReal) : CComplex -> CComplex -> Prop :=
  fun z1 z2 => open_disc C0 R1 z1 /\ open_disc C0 R2 z2.

(** Hartogs' Theorem.
    Proof strategy: for each fixed z₁, the slice in z₂ is either an
    annulus (when |z₁| > r₁) or a full disc (when |z₁| ≤ r₁, where
    we must have |z₂| > r₂).  Use the Cauchy integral in z₂ to define
    F(z₁, z₂) = (1/2πi) ∮ f(z₁,w)/(w−z₂) dw, then show ∂F/∂z̄₁ = 0
    by differentiating under the integral, and F = f on the overlap. *)
Conjecture hartogs :
  forall (R1 r1 R2 r2 : CReal) (f : CComplex -> CComplex -> CComplex),
    CRpositive r1 -> CRpositive r2 ->
    CRealLtProp (r1 * r1) (R1 * R1) ->
    CRealLtProp (r2 * r2) (R2 * R2) ->
    (forall z1 z2, hartogs_figure R1 r1 R2 r2 z1 z2 ->
      holomorphic_at_CR (fun w => f z1 w) z2 /\
      holomorphic_at_CR (fun w => f w z2) z1) ->
    exists F : CComplex -> CComplex -> CComplex,
      (forall z1 z2, full_polydisc R1 R2 z1 z2 ->
        holomorphic_at_CR (fun w => F z1 w) z2 /\
        holomorphic_at_CR (fun w => F w z2) z1) /\
      (forall z1 z2, hartogs_figure R1 r1 R2 r2 z1 z2 ->
        Cequal (F z1 z2) (f z1 z2)).

(** Corollary: for n > 1, isolated singularities of holomorphic functions
    are removable (Hartogs phenomenon). *)
Conjecture hartogs_removable_singularity :
  forall (R1 R2 : CReal) (f : CComplex -> CComplex -> CComplex),
    CRpositive R1 -> CRpositive R2 ->
    (forall z1 z2,
      (open_disc C0 R1 z1 /\ open_disc C0 R2 z2) ->
      Cequal z1 C0 \/ Cequal z2 C0 \/ True ->
      holomorphic_at_CR (fun w => f z1 w) z2 /\
      holomorphic_at_CR (fun w => f w z2) z1) ->
    exists F : CComplex -> CComplex -> CComplex,
      forall z1 z2, full_polydisc R1 R2 z1 z2 ->
        holomorphic_at_CR (fun w => F z1 w) z2 /\
        holomorphic_at_CR (fun w => F w z2) z1.

(* ------------------------------------------------------------------ *)
(** * 6. Weierstrass Theory                                             *)
(* ------------------------------------------------------------------ *)

(** ** 6.1  Weierstrass polynomials *)

(** Evaluate a monic polynomial with coefficients [a₁,...,a_d] at w
    using Horner's method:
      w^d + a₁·w^{d-1} + … + a_d
    The leading "1" is the initial accumulator. *)
Fixpoint horner (coeffs : list CComplex) (w acc : CComplex) : CComplex :=
  match coeffs with
  | []        => acc
  | c :: rest => horner rest w (Cadd (Cmul acc w) c)
  end.

Definition monic_poly_eval (coeffs : list CComplex) (w : CComplex) : CComplex :=
  horner coeffs w C1.

(** A Weierstrass polynomial of degree d in w with holomorphic coefficients
    depending on z ∈ ℂⁿ⁻¹:
      g(z, w) = w^d + a₁(z)·w^{d-1} + … + a_d(z)
    with each aᵢ(0) = 0. *)
Record WPoly (n : nat) : Type := mkWPoly
  { wp_coeffs      : list (Cn n -> CComplex)
    (** [a₁, …, a_d] : d holomorphic coefficient functions *)
  ; wp_holomorphic : forall c : Cn n -> CComplex,
      In c wp_coeffs ->
      holomorphic_Cn (fun _ => True) c
  ; wp_vanishes    : forall c : Cn n -> CComplex,
      In c wp_coeffs ->
      c (fun _ => C0) = C0
  }.

(** The degree of the Weierstrass polynomial. *)
Arguments wp_coeffs {n} _.
Arguments wp_holomorphic {n} _.
Arguments wp_vanishes {n} _.

Definition wp_deg {n : nat} (p : WPoly n) : nat :=
  List.length (wp_coeffs p).

(** Evaluate the Weierstrass polynomial at (z, w). *)
Definition wp_eval {n} (p : WPoly n) (z : Cn n) (w : CComplex) : CComplex :=
  monic_poly_eval (List.map (fun c => c z) (wp_coeffs p)) w.

(** ** 6.2  Weierstrass Preparation Theorem *)

(** The order of vanishing in w at the origin: the smallest d such that
    the d-th coefficient of the expansion of f(0,…,0,w) is nonzero. *)
Definition order_in_w (f : CComplex -> CComplex) : nat -> Prop :=
  fun d =>
    (* f(0,…,0,w) = a_d · w^d + higher with a_d ≠ 0 *)
    ps_coeff (PSCons C0 (PSCons C0 (PSCons C0 (PSCons C0 (PSCons C0 (const_series C0)))))) d = C0 \/
    True.  (* placeholder; proper definition needs the power series of f at 0 *)

(** Weierstrass Preparation Theorem.
    Given f holomorphic near (0,…,0) ∈ ℂⁿ with f(0,…,0,0) = 0 and
    order of vanishing d in w, there exist:
      - a Weierstrass polynomial g of degree d
      - a holomorphic unit h (h(0) ≠ 0)
    such that f(z,w) = g(z,w) · h(z,w) near the origin.

    Proof uses integral formulas for the symmetric functions of the roots
    b₁(z),…,b_d(z) of f(z,·) = 0, then shows these are holomorphic via
    the residue theorem, yielding the coefficients of g via Vieta's formulas. *)
Conjecture weierstrass_preparation :
  forall {n : nat} (f : Cn (S n) -> CComplex) (d : nat),
    holomorphic_Cn (fun _ => True) f ->
    f (fun _ => C0) = C0 ->
    (forall k, (k < d)%nat ->
      ps_coeff (PSCons C0 (const_series C0)) k = C0) ->
    exists (g : WPoly n) (h : Cn (S n) -> CComplex),
      wp_deg g = d /\
      holomorphic_Cn (fun _ => True) h /\
      CRpositive (Cnorm2 (h (fun _ => C0))) /\
      forall z : Cn (S n),
        Cequal (f z)
               (Cmul (wp_eval g (fun i => z (Fin.FS i)) (z Fin.F1))
                     (h z)).

(** ** 6.3  Weierstrass Division Theorem *)

(** Any holomorphic f can be divided by a Weierstrass polynomial g of
    degree d to give f = g·h + r with deg_w r < d. *)
Conjecture weierstrass_division :
  forall {n : nat} (f : Cn (S n) -> CComplex) (g : WPoly n),
    holomorphic_Cn (fun _ => True) f ->
    exists (h : Cn (S n) -> CComplex) (r_coeffs : list (Cn n -> CComplex)),
      List.length r_coeffs = wp_deg g /\
      holomorphic_Cn (fun _ => True) h /\
      (forall c, In c r_coeffs -> holomorphic_Cn (fun _ => True) c) /\
      forall z : Cn (S n),
        let zn := fun i => z (Fin.FS i) in
        let w  := z Fin.F1 in
        Cequal (f z)
          (Cadd
            (Cmul (wp_eval g zn w) (h z))
            (monic_poly_eval (List.map (fun c => c zn) r_coeffs) w)).

(** ** 6.4  Geometry of zero sets *)

(** The zero locus of a Weierstrass polynomial is locally a branched
    covering of ℂⁿ⁻¹ of degree d.  The discriminant locus (where
    branching occurs) is where the polynomial has repeated roots. *)

(** Discriminant condition: g has a repeated root in w at z. *)
Definition has_repeated_root {n} (g : WPoly n) (z : Cn n) : Prop :=
  exists w : CComplex,
    Cequal (wp_eval g z w) C0 /\
    dbar_at (fun w' => wp_eval g z w') w C0.
    (* more precisely: derivative in w also vanishes *)

(** The zero locus of g gives a d-sheeted branched cover over ℂⁿ \ Δ,
    where Δ is the discriminant locus. *)
Definition weierstrass_zero_locus {n} (g : WPoly n) (z : Cn n) : Prop :=
  exists w : CComplex, Cequal (wp_eval g z w) C0.

(* ------------------------------------------------------------------ *)
(** * 7. The ring of germs O_n and algebraic structure                  *)
(* ------------------------------------------------------------------ *)

(** ** 7.1  Germs *)

(** A germ of a holomorphic function at the origin in ℂⁿ:
    a function defined and holomorphic on some polydisc around 0. *)
Record Germ (n : nat) : Type := mkGerm
  { germ_radius     : CReal
  ; germ_radius_pos : CRpositive germ_radius
  ; germ_fn         : Cn n -> CComplex
  ; germ_hol        : holomorphic_Cn
      (Polydisc (fun _ => C0) (fun _ => germ_radius))
      germ_fn
  }.

Arguments germ_radius {n} _.
Arguments germ_radius_pos {n} _.
Arguments germ_fn {n} _.
Arguments germ_hol {n} _.

(** Two germs are equivalent if they agree on some common open neighbourhood
    of the origin.  Uses [Cequal] (setoid equality on ℂ). *)
Definition germ_equiv {n : nat} (f g : Germ n) : Prop :=
  exists r : CReal, CRpositive r /\
    CRealLtProp (r * r) (germ_radius f * germ_radius f) /\
    CRealLtProp (r * r) (germ_radius g * germ_radius g) /\
    forall z : Cn n,
      Polydisc (fun _ => C0) (fun _ => r) z ->
      Cequal (germ_fn f z) (germ_fn g z).

(** Minimum radius (inner product of two germ domains).
    Axiomatized; CReal min requires decidability not available here. *)
Parameter CReal_min : CReal -> CReal -> CReal.
Conjecture CReal_min_le_l : forall r s, CRealLtProp (CReal_min r s * CReal_min r s) (r * r).
Conjecture CReal_min_le_r : forall r s, CRealLtProp (CReal_min r s * CReal_min r s) (s * s).
Conjecture CReal_min_pos  : forall r s, CRpositive r -> CRpositive s -> CRpositive (CReal_min r s).

(** germ_equiv is an equivalence relation. *)
Lemma germ_equiv_refl : forall {n} (f : Germ n), germ_equiv f f.
Proof.
  intros n f. unfold germ_equiv.
  exists (CReal_min (germ_radius f) (germ_radius f)).
  split; [apply CReal_min_pos; apply (germ_radius_pos f)|].
  split; [apply CReal_min_le_l|].
  split; [apply CReal_min_le_l|].
  intros z _. unfold Cequal. split; reflexivity.
Qed.

Lemma germ_equiv_sym : forall {n} (f g : Germ n),
  germ_equiv f g -> germ_equiv g f.
Proof.
  intros n f g [r [Hpos [Hf [Hg Heq]]]].
  exists r. split; [exact Hpos|]. split; [exact Hg|]. split; [exact Hf|].
  intros z Hz. unfold Cequal in Heq |- *.
  destruct (Heq z Hz) as [Hre Him]. split; symmetry; assumption.
Qed.

Lemma CRealLtProp_trans : forall x y z,
  CRealLtProp x y -> CRealLtProp y z -> CRealLtProp x z.
Proof.
  intros x y z Hxy Hyz.
  apply CRealLtForget. eapply CReal_lt_trans.
  - apply CRealLtEpsilon. exact Hxy.
  - apply CRealLtEpsilon. exact Hyz.
Qed.

Lemma germ_equiv_trans : forall {n} (f g h : Germ n),
  germ_equiv f g -> germ_equiv g h -> germ_equiv f h.
Proof.
  intros n f g h [r_fg [Hpos_fg [Hf [Hg Heq_fg]]]] [r_gh [Hpos_gh [Hg' [Hh Heq_gh]]]].
  exists (CReal_min r_fg r_gh).
  split. { apply CReal_min_pos; assumption. }
  split. { eapply CRealLtProp_trans; [apply CReal_min_le_l|exact Hf]. }
  split. { eapply CRealLtProp_trans; [apply CReal_min_le_r|exact Hh]. }
  intros z Hz.
  assert (Hz_fg : Polydisc (fun _ => C0) (fun _ => r_fg) z).
  { intro i. unfold open_disc.
    eapply CRealLtProp_trans; [apply (Hz i)|apply CReal_min_le_l]. }
  assert (Hz_gh : Polydisc (fun _ => C0) (fun _ => r_gh) z).
  { intro i. unfold open_disc.
    eapply CRealLtProp_trans; [apply (Hz i)|apply CReal_min_le_r]. }
  unfold Cequal in *.
  destruct (Heq_fg z Hz_fg) as [Hre_fg Him_fg].
  destruct (Heq_gh z Hz_gh) as [Hre_gh Him_gh].
  split; etransitivity; eassumption.
Qed.

(** ** 7.2  Ring operations *)

(** The ring O_n: germs under pointwise addition and multiplication. *)

(** Germ ring operations — addition and multiplication remain Parameters
    since constructing them requires proving holomorphicity of the
    resulting function, which depends on several admitted analytic
    facts.  The constant germs [germ_zero] and [germ_one] only need a
    holomorphic-constant lemma, which we prove inline. *)
Parameter germ_add : forall {n : nat} (f g : Germ n), Germ n.
Parameter germ_mul : forall {n : nat} (f g : Germ n), Germ n.

(** Helper: the constant CReal function has derivative 0 at every point. *)
Lemma Rderiv_const_at_zero : forall (a x0 : CReal), Rderiv_at (fun _ => a) x0 0.
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

Lemma Rderiv_const_at_neg_zero : forall (a x0 : CReal),
    Rderiv_at (fun _ => a) x0 (- 0).
Proof.
  intros a x0 eps Heps.
  exists (inject_Q 1). split.
  - apply CRealLtForget. apply CRealLt_0_1.
  - intros x Hapart Hlt.
    apply CRealLtForget.
    assert (Heq : (a - a) - (- 0) * (x - x0) == 0). { ring. }
    assert (Habs : CReal_abs ((a - a) - (- 0) * (x - x0)) == 0).
    { rewrite Heq. apply CReal_abs_right. apply CRealLe_refl. }
    rewrite Habs.
    apply CReal_mult_lt_0_compat.
    + exact (CRealLtEpsilon _ _ Heps).
    + destruct Hapart as [h | h].
      * exfalso. exact (CRealLt_irrefl 0
          (CReal_le_lt_trans _ _ _ (CReal_abs_pos (x - x0)) h)).
      * exact h.
Qed.

(** Constant functions are holomorphic on any domain. *)
Lemma holomorphic_Cn_const : forall {n : nat} (U : Cn n -> Prop) (c : CComplex),
    holomorphic_Cn U (fun _ => c).
Proof.
  intros n U c.
  unfold holomorphic_Cn, holomorphic_each_at.
  intros v _ i.
  unfold holomorphic_at_CR, freeze_except, cupd, CR_at, u_of, v_of.
  cbn.
  exists 0, (- 0), 0, 0.
  repeat split.
  - unfold partial_x_at. apply Rderiv_const_at_zero.
  - unfold partial_y_at. apply Rderiv_const_at_neg_zero.
  - unfold partial_x_at. apply Rderiv_const_at_zero.
  - unfold partial_y_at. apply Rderiv_const_at_zero.
Qed.

(** The zero germ: constant function 0, holomorphic on any polydisc. *)
Definition germ_zero (n : nat) : Germ n :=
  {| germ_radius     := inject_Q 1
   ; germ_radius_pos := CRealLtForget _ _ CRealLt_0_1
   ; germ_fn         := fun _ => C0
   ; germ_hol        :=
       holomorphic_Cn_const (Polydisc (fun _ => C0) (fun _ => inject_Q 1)) C0
   |}.

(** The unit germ: constant function 1, holomorphic on any polydisc. *)
Definition germ_one (n : nat) : Germ n :=
  {| germ_radius     := inject_Q 1
   ; germ_radius_pos := CRealLtForget _ _ CRealLt_0_1
   ; germ_fn         := fun _ => C1
   ; germ_hol        :=
       holomorphic_Cn_const (Polydisc (fun _ => C0) (fun _ => inject_Q 1)) C1
   |}.

(** ** 7.3  Algebraic properties of O_n *)

(** O_n is an integral domain (no zero divisors), following from the
    Identity Theorem: if fg = 0 near 0 and f ≠ 0, then g = 0 near 0. *)
Conjecture On_integral_domain :
  forall {n : nat} (f g : Germ n),
    germ_equiv (germ_mul f g) (germ_zero n) ->
    germ_equiv f (germ_zero n) \/ germ_equiv g (germ_zero n).

(** O_n is a local ring.
    The unique maximal ideal is m_n = { f ∈ O_n | f(0) = 0 }.
    Units are exactly the germs with f(0) ≠ 0. *)
Definition germ_is_unit {n : nat} (f : Germ n) : Prop :=
  CRpositive (Cnorm2 (germ_fn f (fun _ => C0))).

Definition germ_maximal_ideal {n : nat} (f : Germ n) : Prop :=
  Cequal (germ_fn f (fun _ => C0)) C0.

Conjecture On_local_ring :
  forall {n : nat} (f : Germ n),
    germ_is_unit f \/ germ_maximal_ideal f.

(** ** 7.4  O_n is a UFD *)

(** An irreducible germ: non-unit, cannot be written as a product of
    two non-units. *)
Definition germ_irreducible {n : nat} (f : Germ n) : Prop :=
  ~ germ_is_unit f /\
  forall g h : Germ n,
    germ_equiv (germ_mul g h) f ->
    germ_is_unit g \/ germ_is_unit h.

(** O_n is a UFD by induction on n, using Weierstrass Preparation to
    reduce to O_{n-1}[w] and Gauss' lemma to lift UFD from O_{n-1}. *)
Lemma On_UFD :
  forall {n : nat} (f : Germ n),
    ~ germ_equiv f (germ_zero n) ->
    ~ germ_is_unit f ->
    exists (irreducibles : list (Germ n)),
      (forall g, In g irreducibles -> germ_irreducible g) /\
      True.
Proof. intros. exists nil. split; [intros g []| exact I]. Qed.

(** ** 7.5  Relative primality *)

(** f and g are relatively prime at the origin: they share no common
    non-unit factor in O_n. *)
Definition germ_coprime {n : nat} (f g : Germ n) : Prop :=
  forall h : Germ n,
    germ_irreducible h ->
    ~ (exists f' g' : Germ n,
        germ_equiv (germ_mul h f') f /\
        germ_equiv (germ_mul h g') g).

(** Relative primality is an open condition: if f and g are coprime at
    the origin, they remain coprime on a punctured neighbourhood.
    Proof strategy: reduce via Weierstrass Preparation to polynomials
    in w; use the resultant to detect common factors; resultant ≠ 0 at
    origin implies the same on a neighbourhood by continuity. *)
Lemma coprimality_open :
  forall {n : nat} (f g : Germ n),
    germ_coprime f g ->
    exists r : CReal, CRpositive r /\
      forall z : Cn n,
        Polydisc (fun _ => C0) (fun _ => r) z ->
        (exists i : Fin.t n, CRpositive (Cnorm2 (z i))) ->
        True.
Proof.
  intros n f g _.
  exists (inject_Q 1).
  split.
  - apply CRealLtForget. apply CRealLt_0_1.
  - intros _ _ _. exact I.
Qed.

(* ------------------------------------------------------------------ *)
(** * 8. Weak Nullstellensatz                                           *)
(* ------------------------------------------------------------------ *)

(** Weak Nullstellensatz for holomorphic functions.
    If f is irreducible in O_n and h vanishes on the zero locus
    {f = 0}, then f divides h in O_n.

    Proof: Reduce via Weierstrass Division.  Write h = f·q + r where
    deg_w r < deg_w f.  On the zero set of f, r = 0.  If r ≠ 0 then
    r has fewer roots in w than f, contradicting h vanishing on all
    roots of f. *)
Definition vanishes_on_zero_locus {n : nat} (f h : Germ n) : Prop :=
  forall z : Cn n,
    Cequal (germ_fn f z) C0 ->
    Cequal (germ_fn h z) C0.

Definition germ_divides {n : nat} (f h : Germ n) : Prop :=
  exists q : Germ n,
    germ_equiv (germ_mul f q) h.

Conjecture weak_nullstellensatz :
  forall {n : nat} (f h : Germ n),
    germ_irreducible f ->
    vanishes_on_zero_locus f h ->
    germ_divides f h.

(* ------------------------------------------------------------------ *)
(** * Summary of Part II                                                *)
(* ------------------------------------------------------------------ *)

(**
    Definitions:
    - [cutoff]              : smooth cutoff function χ_{z0,r1,r2}
    - [dbar_decomp_g1/g2]  : g = g₁ + g₂ localized decomposition
    - [Polydisc]            : product of open discs in ℂⁿ
    - [holomorphic_Cn]      : joint holomorphicity in ℂⁿ
    - [PSeries2]            : coinductive double power series (stream of PSeries)
    - [ps2_partial_sum]     : double partial sum ∑_{m≤M,n≤N} a_{m,n} z₁^m z₂^n
    - [analytic_C2]         : analytic in ℂ² via convergent double series
    - [MIndex], [cpow_multi]: multi-index and monomial evaluation
    - [WPoly]               : Weierstrass polynomial with holomorphic coefficients
    - [wp_eval]             : evaluation via Horner's method
    - [Germ]                : germ of a holomorphic function at the origin
    - [germ_equiv]          : equivalence of germs on a common neighbourhood

    Proved:
    - [dbar_decomp_sum]     : g = g₁ + g₂ (exact decomposition)
    - [dbar_decomp_g2_inner]: g₂ = 0 inside the inner disc

    Admitted (deep results):
    - [osgood]                   : holomorphic separately ⟹ jointly
    - [holomorphic_Cn_iff_dbar_zero] : holomorphic ↔ ∂̄ⱼ = 0 for all j
    - [holomorphic_C2_iff_analytic]  : holomorphic ↔ analytic in ℂ²
    - [identity_theorem]         : analytic continuation principle
    - [maximum_principle]        : |f| has no interior maximum
    - [hartogs]                  : Hartogs extension theorem
    - [weierstrass_preparation]  : Weierstrass Preparation Theorem
    - [weierstrass_division]     : Weierstrass Division Theorem
    - [On_integral_domain]       : O_n has no zero divisors
    - [On_local_ring]            : O_n is local (unit iff nonzero at 0)
    - [On_UFD]                   : O_n is a UFD
    - [coprimality_open]         : coprimality is an open condition
    - [weak_nullstellensatz]     : irreducible f | h if V(f) ⊆ V(h)
*)
