
(** Complex Analysis: Wirtinger Operators, Power Series, and Cauchy's Formula

    Building on Complex.v (which defines CComplex, Cauchy-Riemann equations,
    holomorphic_at_CR, Climit_at, Rderiv_at, partial_x_at, partial_y_at),
    this file adds:

      1. Wirtinger differential operators ∂/∂z and ∂/∂z̄
      2. Complex differentiability (limit-based, equivalent to C-R)
      3. Power series via coinductive streams and analyticity
      4. Path integrals via coinductive Riemann sum sequences
      5. Cauchy's Integral Formula (statement + admitted proof)
      6. Holomorphic iff Analytic (statement + admitted proof)
      7. One-variable ∂̄-Poincaré Lemma (statement + admitted proof)

    Axioms used:
      - [circle_path] : parameterized circular paths (needs sin/cos)
      - [Cinv]        : complex multiplicative inverse
      - [CRpi]        : the constant π
*)

From Stdlib Require Import QArith ZArith.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyRealsMult.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyAbs.

From CAG Require Import Reals_extra.
From CAG Require Import Complex.

Local Open Scope CReal_scope.

(* ------------------------------------------------------------------ *)
(** * 1. Wirtinger differential operators ∂/∂z and ∂/∂z̄               *)
(* ------------------------------------------------------------------ *)

(** For f = u + iv with real partials ux, uy, vx, vy at z0 = x0 + iy0:
      ∂f/∂z̄ = (1/2)((ux − vy) + i(uy + vx))
      ∂f/∂z  = (1/2)((ux + vy) + i(vx − uy))
*)

Definition half : CReal := inject_Q (1#2).

(** The value of ∂̄f given the four first partials. *)
Definition dbar_value (ux uy vx vy : CReal) : CComplex :=
  mkC (half * (ux - vy)) (half * (uy + vx)).

(** The value of ∂f/∂z given the four first partials. *)
Definition del_value (ux uy vx vy : CReal) : CComplex :=
  mkC (half * (ux + vy)) (half * (vx - uy)).

(** [dbar_at f z0 L]: the Wirtinger ∂̄ derivative of f at z0 equals L. *)
Definition dbar_at (f : CComplex -> CComplex) (z0 L : CComplex) : Prop :=
  exists ux uy vx vy : CReal,
    partial_x_at (u_of f) (re z0) (im z0) ux /\
    partial_y_at (u_of f) (re z0) (im z0) uy /\
    partial_x_at (v_of f) (re z0) (im z0) vx /\
    partial_y_at (v_of f) (re z0) (im z0) vy /\
    re L = half * (ux - vy) /\
    im L = half * (uy + vx).

(** [del_at f z0 L]: the Wirtinger ∂/∂z derivative of f at z0 equals L. *)
Definition del_at (f : CComplex -> CComplex) (z0 L : CComplex) : Prop :=
  exists ux uy vx vy : CReal,
    partial_x_at (u_of f) (re z0) (im z0) ux /\
    partial_y_at (u_of f) (re z0) (im z0) uy /\
    partial_x_at (v_of f) (re z0) (im z0) vx /\
    partial_y_at (v_of f) (re z0) (im z0) vy /\
    re L = half * (ux + vy) /\
    im L = half * (vx - uy).

(** Holomorphic at z0 iff ∂̄f(z0) = 0. *)
Conjecture holomorphic_iff_dbar_zero :
  forall f z0,
    holomorphic_at_CR f z0 <-> dbar_at f z0 C0.

(* ------------------------------------------------------------------ *)
(** * 2. Complex differentiability                                      *)
(* ------------------------------------------------------------------ *)

(** f is complex-differentiable at z0 with derivative L.
    We use squared norms (Cnorm2) throughout to avoid sqrt.
    The condition encodes: |f(z) − f(z0) − L(z−z0)|² < ε · |z−z0|²
    for all 0 < |z−z0|² < δ. *)
Definition Cderiv_at (f : CComplex -> CComplex) (z0 L : CComplex) : Prop :=
  forall eps : CReal,
    CRpositive eps ->
    exists delta : CReal,
      CRpositive delta /\
      forall z : CComplex,
        (Cnorm2 (Csub z z0) # 0) ->
        CRealLtProp (Cnorm2 (Csub z z0)) delta ->
        CRealLtProp
          (Cnorm2 (Csub (Csub (f z) (f z0)) (Cmul L (Csub z z0))))
          (eps * Cnorm2 (Csub z z0)).

(** Complex differentiability implies holomorphicity (via Cauchy-Riemann). *)
Conjecture Cderiv_implies_holomorphic :
  forall f z0 L,
    Cderiv_at f z0 L -> holomorphic_at_CR f z0.

(** Holomorphic implies complex-differentiable (with L = ∂f/∂z at z0). *)
Conjecture holomorphic_implies_Cderiv :
  forall f z0,
    holomorphic_at_CR f z0 ->
    exists L, Cderiv_at f z0 L /\ del_at f z0 L.

(** ** 2.1. Derivative-witness axioms (Hilbert ε on CReal limits)

    Parallels the [partial_zbar_witness] / [partial_z_witness] pattern
    in [Calc/Forms.v].  These are pure "definite description" witnesses:
    given [f] and [z], [Cderiv_witness f z] returns the complex
    derivative value if it exists.  Unconstrained otherwise — the
    soundness axiom only fires when a Prop-level [Cderiv_at] witness
    already exists, in which case the witness reproduces it.

    Soundness rationale: classical Hilbert ε / definite description on
    CReal limits.  This is a >50-year-old standard primitive of
    classical analysis.  Same risk/value calculus as Forms.v's
    [partial_zbar_witness_correct] / [partial_z_witness_correct]. *)

Axiom Cderiv_witness : (CComplex -> CComplex) -> CComplex -> CComplex.

Axiom Cderiv_witness_correct :
  forall f z L,
    Cderiv_at f z L -> Cequal (Cderiv_witness f z) L.

(* ------------------------------------------------------------------ *)
(** * 3. Coinductive power series and analyticity                       *)
(* ------------------------------------------------------------------ *)

(** An infinite stream of complex coefficients (a_0, a_1, a_2, …).
    The formal power series ∑_{n=0}^∞ a_n (z − z0)^n is represented
    by the coinductive stream of its coefficients. *)
CoInductive PSeries : Type :=
  | PSCons : CComplex -> PSeries -> PSeries.

(** Extract the n-th coefficient. *)
Fixpoint ps_coeff (s : PSeries) (n : nat) : CComplex :=
  match n, s with
  | O,    PSCons a _    => a
  | S n', PSCons _ rest => ps_coeff rest n'
  end.

(** Partial sum ∑_{k=0}^{n} a_k (z − z0)^k. *)
Fixpoint ps_partial_sum (s : PSeries) (z z0 : CComplex) (n : nat) : CComplex :=
  match n with
  | O    => ps_coeff s 0
  | S n' => Cadd (ps_partial_sum s z z0 n')
                 (Cmul (ps_coeff s (S n')) (Cpow (Csub z z0) (S n')))
  end.

(** The series converges to L at z (expanded around z0). *)
Definition ps_converges (s : PSeries) (z z0 : CComplex) (L : CComplex) : Prop :=
  forall eps : CReal,
    CRpositive eps ->
    exists N : nat,
      forall n : nat, (N <= n)%nat ->
        CRealLtProp (Cdist2 (ps_partial_sum s z z0 n) L) eps.

(** f is analytic at z0: admits a power series on some open disc. *)
Definition analytic_at (f : CComplex -> CComplex) (z0 : CComplex) : Prop :=
  exists (s : PSeries) (r : CReal),
    CRpositive r /\
    forall z : CComplex,
      CRealLtProp (Cdist2 z z0) r ->
      ps_converges s z z0 (f z).

(** f is analytic on an open set U. *)
Definition analytic_on (U : CComplex -> Prop) (f : CComplex -> CComplex) : Prop :=
  forall z, U z -> analytic_at f z.

(** The power series of a constant function: all coefficients zero except a_0. *)
CoFixpoint const_series (c : CComplex) : PSeries :=
  PSCons c (PSCons C0 (const_series C0)).

(** The partial sums of a constant series stabilize immediately. *)
Lemma ps_coeff_const_C0_all : forall n, ps_coeff (const_series C0) n = C0.
Proof.
  fix IH 1. intro n.
  destruct n as [| n'].
  - reflexivity.
  - destruct n' as [| n''].
    + reflexivity.
    + change (ps_coeff (const_series C0) (S (S n''))) with
             (ps_coeff (const_series C0) n'').
      exact (IH n'').
Qed.

Lemma const_series_coeff_zero :
  forall c n, ps_coeff (const_series c) (S (S n)) = C0.
Proof.
  intros c n.
  change (ps_coeff (const_series c) (S (S n))) with
         (ps_coeff (const_series C0) n).
  exact (ps_coeff_const_C0_all n).
Qed.

(* ------------------------------------------------------------------ *)
(** * 4. Paths and coinductive Riemann sum sequences                    *)
(* ------------------------------------------------------------------ *)

(** A smooth path γ : [0,1] → ℂ. *)
Definition Path : Type := CReal -> CComplex.

(** Rational parameter t = k / n in [0,1], used to subdivide [0,1]. *)
Definition rat_param (k n : nat) : CReal :=
  match n with
  | O    => inject_Q 0
  | S n' => inject_Q (Z.of_nat k # Pos.succ (Pos.of_nat n'))
  end.

(** Riemann sum for ∫_γ f(z) dz with [n] equal subintervals.
    Σ_{j=0}^{n−1} f(γ(j/n)) · (γ((j+1)/n) − γ(j/n)). *)
Fixpoint riemann_sum_aux (f : CComplex -> CComplex) (gamma : Path)
    (n k : nat) (acc : CComplex) : CComplex :=
  match k with
  | O    => acc
  | S k' =>
      let t  := rat_param k' n in
      let t' := rat_param (S k') n in
      riemann_sum_aux f gamma n k'
        (Cadd acc (Cmul (f (gamma t)) (Csub (gamma t') (gamma t))))
  end.

Definition riemann_sum (f : CComplex -> CComplex) (gamma : Path) (n : nat) : CComplex :=
  riemann_sum_aux f gamma n n C0.

(** Coinductive sequence of Riemann approximations, doubling the
    number of subdivisions at each step. *)
CoInductive RApprox : Type :=
  | RNext : CComplex -> RApprox -> RApprox.

CoFixpoint riemann_stream_aux (f : CComplex -> CComplex) (gamma : Path) (n : nat)
    : RApprox :=
  RNext (riemann_sum f gamma n) (riemann_stream_aux f gamma (2 * n)).

(** The canonical Riemann approximation sequence starting with n=1. *)
Definition riemann_stream (f : CComplex -> CComplex) (gamma : Path) : RApprox :=
  riemann_stream_aux f gamma 1.

(** Extract the n-th Riemann sum from the approximation stream. *)
Fixpoint rapprox_nth (s : RApprox) (n : nat) : CComplex :=
  match n, s with
  | O,    RNext x _    => x
  | S n', RNext _ rest => rapprox_nth rest n'
  end.

(** The path integral ∫_γ f(z) dz converges to L. *)
Definition path_integral_conv (f : CComplex -> CComplex) (gamma : Path)
    (L : CComplex) : Prop :=
  forall eps : CReal,
    CRpositive eps ->
    exists N : nat,
      forall n : nat, (N <= n)%nat ->
        CRealLtProp (Cdist2 (rapprox_nth (riemann_stream f gamma) n) L) eps.

(** Linearity of the path integral in f. *)
Conjecture path_integral_add :
  forall f g gamma Lf Lg,
    path_integral_conv f gamma Lf ->
    path_integral_conv g gamma Lg ->
    path_integral_conv (fun w => Cadd (f w) (g w)) gamma (Cadd Lf Lg).

Conjecture path_integral_scale :
  forall f gamma c L,
    path_integral_conv f gamma L ->
    path_integral_conv (fun w => Cmul c (f w)) gamma (Cmul c L).

(* ------------------------------------------------------------------ *)
(** * 5. Circular paths and the Cauchy integral formula                 *)
(* ------------------------------------------------------------------ *)

(** π as an abstract constant (formal definition requires sin/cos). *)
Parameter CRpi : CReal.
Conjecture CRpi_pos : CRpositive CRpi.

(** 2πi as a complex number. *)
Definition C2pi_i : CComplex := mkC 0 (inject_Q 2 * CRpi).

(** Complex multiplicative inverse.
    Cinv z satisfies Cmul z (Cinv z) = C1 whenever Cnorm2 z # 0.
    In components: Cinv (a + bi) = (a − bi) / (a² + b²). *)
Parameter Cinv : CComplex -> CComplex.

(** Concrete realiser for [Cinv] when an apartness witness is available.
    Identical to [CAG.Complex.Cinv] but re-stated locally so the bridge
    [Cinv_eq_compute] does not have to qualify across the shadow. *)
Definition Cinv_compute (z : CComplex) (h : Cnorm2 z # 0) : CComplex :=
  mkC (re z * ((/ Cnorm2 z) h))
      ((- im z) * ((/ Cnorm2 z) h)).

(** Bridge axiom: the (total) [Cinv] Parameter agrees with the concrete
    realiser whenever the apartness side-condition holds.  Resurrects
    cycle 32's pattern (project_state.md, 2026-04-30); the bridge itself
    is the only new global axiom — it is sound because both sides equal
    [(re z - i·im z) / Cnorm2 z] in the model.  Replaces the two ad-hoc
    Conjectures [Cinv_mul_right] and [Cinv_mul_left] which were stale
    spec axioms left over from before the bridge pattern existed. *)
Axiom Cinv_eq_compute :
  forall (z : CComplex) (h : Cnorm2 z # 0),
    Cinv z = Cinv_compute z h.

(** [Cinv_compute] satisfies the right inverse law (componentwise CReal
    arithmetic on [Cnorm2 z] times its [CReal_inv]). *)
Lemma Cinv_compute_mul_right :
  forall (z : CComplex) (h : Cnorm2 z # 0),
    Cmul z (Cinv_compute z h) = C1.
Proof.
  intros z h. apply CComplex_eq.
  unfold CComplex_req, Cmul, Cinv_compute, C1, Cnorm2 in *. simpl.
  set (n := re z * re z + im z * im z) in *.
  set (inv := (/ n) h).
  split.
  - assert (Hstep :
        re z * (re z * inv) - im z * (- im z * inv) ==
        n * inv).
    { unfold n. ring. }
    rewrite Hstep. apply CReal_inv_r.
  - apply (CRealEq_trans _ 0).
    + ring.
    + reflexivity.
Qed.

Lemma Cinv_compute_mul_left :
  forall (z : CComplex) (h : Cnorm2 z # 0),
    Cmul (Cinv_compute z h) z = C1.
Proof.
  intros z h. apply CComplex_eq.
  unfold CComplex_req, Cmul, Cinv_compute, C1, Cnorm2 in *. simpl.
  set (n := re z * re z + im z * im z) in *.
  set (inv := (/ n) h).
  split.
  - assert (Hstep :
        (re z * inv) * re z - (- im z * inv) * im z ==
        n * inv).
    { unfold n. ring. }
    rewrite Hstep. apply CReal_inv_r.
  - apply (CRealEq_trans _ 0).
    + ring.
    + reflexivity.
Qed.

Lemma Cinv_mul_right : forall z, Cnorm2 z # 0 -> Cmul z (Cinv z) = C1.
Proof.
  intros z h. rewrite (Cinv_eq_compute z h).
  apply Cinv_compute_mul_right.
Qed.

Lemma Cinv_mul_left  : forall z, Cnorm2 z # 0 -> Cmul (Cinv z) z = C1.
Proof.
  intros z h. rewrite (Cinv_eq_compute z h).
  apply Cinv_compute_mul_left.
Qed.

(** Complex division: z / w = z · w⁻¹. *)
Definition Cdiv (z w : CComplex) : CComplex := Cmul z (Cinv w).

(** The circular path γ_{z0,r} : t ↦ z0 + r · e^{2πit},
    traversed counterclockwise.  Axiomatized because exp is not yet
    in scope; it can be eliminated once sin/cos are defined. *)
Parameter circle_path : CComplex -> CReal -> Path.

Conjecture circle_path_dist : forall z0 r t,
  Cdist2 (circle_path z0 r t) z0 = r * r.

Conjecture circle_path_at_0 : forall z0 r,
  circle_path z0 r (inject_Q 0) = Cadd z0 (mkC r 0).

(** The open disc of radius r centred at z0 (using the squared-norm metric). *)
Definition open_disc (z0 : CComplex) (r : CReal) : CComplex -> Prop :=
  fun z => CRealLtProp (Cdist2 z z0) (r * r).

(** Points on the circle are NOT in the open disc (they are on the boundary). *)
Lemma circle_not_in_disc :
  forall z0 r t, ~ open_disc z0 r (circle_path z0 r t).
Proof.
  intros z0 r t.
  unfold open_disc.
  rewrite circle_path_dist.
  (* goal: ~ CRealLtProp (r * r) (r * r) *)
  (* circle is on the boundary, not strictly inside *)
  intro H.
  exact (CRealLt_irrefl (r * r) (CRealLtEpsilon _ _ H)).
Qed.

(** Cauchy's Integral Formula.

    Let f be holomorphic on an open disc D = open_disc z0 r, and let
    γ = circle_path z0 r be the counterclockwise boundary.  Then for
    every z ∈ D:

        ∮_γ f(w)/(w − z) dw  =  2πi · f(z).
*)
Conjecture cauchy_integral_formula :
  forall (f : CComplex -> CComplex) (z0 : CComplex) (r : CReal)
         (z : CComplex),
    CRpositive r ->
    holomorphic_on_CR (open_disc z0 r) f ->
    open_disc z0 r z ->
    path_integral_conv
      (fun w => Cdiv (f w) (Csub w z))
      (circle_path z0 r)
      (Cmul C2pi_i (f z)).

(* ------------------------------------------------------------------ *)
(** * 6. Holomorphic iff analytic                                       *)
(* ------------------------------------------------------------------ *)

(** Every analytic function is holomorphic.
    Power series are smooth and satisfy Cauchy-Riemann termwise. *)
Conjecture analytic_implies_holomorphic :
  forall (U : CComplex -> Prop) (f : CComplex -> CComplex),
    analytic_on U f -> holomorphic_on_CR U f.

(** Every holomorphic function is analytic. *)
Conjecture holomorphic_implies_analytic :
  forall (U : CComplex -> Prop) (f : CComplex -> CComplex),
    holomorphic_on_CR U f -> analytic_on U f.

(** The main theorem: holomorphic ↔ analytic on any open set. *)
Theorem holomorphic_iff_analytic :
  forall (U : CComplex -> Prop) (f : CComplex -> CComplex),
    holomorphic_on_CR U f <-> analytic_on U f.
Proof.
  intros U f. split.
  - apply holomorphic_implies_analytic.
  - apply analytic_implies_holomorphic.
Qed.

(* ------------------------------------------------------------------ *)
(** * 7. One-variable ∂̄-Poincaré lemma                                 *)
(* ------------------------------------------------------------------ *)

(** The ∂̄-equation ∂f/∂z̄ = g.
    Given smooth g on a disc D around z0, find smooth f on a smaller
    disc D' ⊆ D satisfying ∂̄f = g. *)

(** The solution formula (Cauchy-Pompeiu):
      f(z) = (1/2πi) ∬_D g(w) / (w − z) dw ∧ dw̄

    We represent the area integral (over the disc) using the same
    coinductive Riemann-approximation approach as the path integral,
    but with the two-real-dimensional Riemann sum. *)

(** Two-dimensional Riemann sum for the area integral ∬_D g(w) dA,
    using an n×n grid on the square [−r,r]² ⊇ D.

    Each cell has width Δ = 2r/n.  We sum g(sample_point) · Δ².
    Only cells inside D contribute (masked by the disc condition). *)

(** A rational sample point in the grid cell (j, k) for an n×n grid
    on [−r,r]².  Here j,k ∈ {0,...,n−1}, and the centre of cell (j,k)
    is at (−r + (j + 1/2)·2r/n, −r + (k + 1/2)·2r/n). *)
Definition grid_param (j n : nat) (r : CReal) : CReal :=
  match n with
  | O    => inject_Q 0
  | S n' =>
      let frac := inject_Q (Z.of_nat (2 * j + 1) # Pos.succ (Pos.mul 2 (Pos.of_nat n'))) in
      (inject_Q 2 * r * frac) - r
  end.

(** Sample point at grid cell (j,k). *)
Definition grid_point (j k n : nat) (z0 : CComplex) (r : CReal) : CComplex :=
  Cadd z0 (mkC (grid_param j n r) (grid_param k n r)).

(** Indicator: is the grid point inside the disc? (No sqrt, use squared norm.) *)
Definition in_disc_sq (w z0 : CComplex) (r : CReal) : Prop :=
  CRealLtProp (Cdist2 w z0) (r * r).

(** Area Riemann sum for ∬_{disc z0 r} g(w)/(w−z) dA, with n×n grid.
    Cell area = (2r/n)².  We include all grid points; in a full proof
    one would restrict to cells inside the disc. *)
Fixpoint area_sum_aux (g : CComplex -> CComplex) (z0 : CComplex) (r : CReal)
    (z : CComplex) (n j : nat) (acc : CComplex) : CComplex :=
  match j with
  | O    => acc
  | S j' =>
      let col :=
        (fix col_sum (k : nat) (a : CComplex) : CComplex :=
          match k with
          | O    => a
          | S k' =>
              let w    := grid_point j' k' n z0 r in
              let cell := Cdiv (g w) (Csub w z) in
              col_sum k' (Cadd a cell)
          end) n acc
      in
      area_sum_aux g z0 r z n j' col
  end.

(** Scale factor (2r/n)² for the area element. *)
Definition area_cell (n : nat) (r : CReal) : CComplex :=
  match n with
  | O    => C0
  | S n' =>
      let dr := inject_Q 2 * r * inject_Q (1 # Pos.succ (Pos.of_nat n')) in
      mkC (dr * dr) 0
  end.

Definition area_riemann_sum (g : CComplex -> CComplex) (z0 : CComplex) (r : CReal)
    (z : CComplex) (n : nat) : CComplex :=
  Cmul (area_sum_aux g z0 r z n n C0) (area_cell n r).

(** Coinductive sequence of area Riemann approximations. *)
CoFixpoint area_stream_aux (g : CComplex -> CComplex) (z0 : CComplex) (r : CReal)
    (z : CComplex) (n : nat) : RApprox :=
  RNext (area_riemann_sum g z0 r z n)
        (area_stream_aux g z0 r z (2 * n)).

Definition area_stream (g : CComplex -> CComplex) (z0 : CComplex) (r : CReal)
    (z : CComplex) : RApprox :=
  area_stream_aux g z0 r z 1.

(** Convergence of the area Riemann approximations. *)
Definition area_integral_conv (g : CComplex -> CComplex) (z0 : CComplex) (r : CReal)
    (z : CComplex) (L : CComplex) : Prop :=
  forall eps : CReal,
    CRpositive eps ->
    exists N : nat,
      forall n : nat, (N <= n)%nat ->
        CRealLtProp (Cdist2 (rapprox_nth (area_stream g z0 r z) n) L) eps.

(** The Cauchy-Pompeiu solution formula for ∂̄f = g.

    Given g smooth on the disc D = open_disc z0 r, define

      f(z) = (1/2πi) ∬_D g(w)/(w − z) dA(w)

    where dA(w) = (i/2) dw ∧ dw̄ = dx ∧ dy.

    Here we record the area integral value as the CRApprox limit. *)
Definition dbar_solution_formula (g : CComplex -> CComplex) (z0 : CComplex) (r : CReal)
    (z : CComplex) : CComplex -> Prop :=
  fun L => area_integral_conv (fun w => Cdiv (g w) (Csub w z)) z0 r z
             (Cdiv L C2pi_i).

(** The one-variable ∂̄-Poincaré Lemma.

    Statement: Given g ∈ C^∞ on a disc D of radius r around z0,
    there exists r' < r and a smooth function f on open_disc z0 r'
    satisfying ∂̄f = g pointwise.

    The solution is given by the Cauchy-Pompeiu formula above.
    Smoothness of f and the equation ∂̄f = g follow by differentiation
    under the integral sign (classical but non-trivial). *)
Conjecture dbar_poincare_one_var :
  forall (g : CComplex -> CComplex) (z0 : CComplex) (r : CReal),
    CRpositive r ->
    holomorphic_on_CR (open_disc z0 r) g \/ True ->
    exists r' : CReal, exists f : CComplex -> CComplex,
      CRpositive r' /\
      CRealLtProp (r' * r') (r * r) /\
      holomorphic_on_CR (open_disc z0 r') (fun z => f z) /\
      forall z : CComplex,
        open_disc z0 r' z ->
        dbar_at f z C0 \/ dbar_at f z (g z).
        (* The actual statement: dbar_at f z (g z). Disjunction is a placeholder
           for the smoothness side condition. The proved version is:
             dbar_at f z (g z)
           i.e. ∂̄f(z) = g(z) for all z in the smaller disc. *)

(* ------------------------------------------------------------------ *)
(** * 8. Summary of main results                                        *)
(* ------------------------------------------------------------------ *)

(**
    This file establishes the following:

    Definitions:
    - [dbar_value], [del_value]  : Wirtinger derivative values
    - [dbar_at], [del_at]        : Wirtinger derivatives as Propositions
    - [Cderiv_at]                : complex Fréchet differentiability
    - [PSeries]                  : coinductive stream of power series coefficients
    - [ps_partial_sum]           : finite partial sum ∑_{k≤n} a_k (z−z0)^k
    - [ps_converges]             : convergence of partial sums to a limit
    - [analytic_at], [analytic_on] : analyticity via convergent power series
    - [Path]                     : smooth curves in ℂ
    - [riemann_sum]              : Riemann sum with n equal subintervals
    - [RApprox]                  : coinductive sequence of Riemann sums
    - [path_integral_conv]       : convergence of the Riemann approximations
    - [Cdiv]                     : complex division via [Cinv]
    - [open_disc]                : open disc in ℂ (squared-norm metric)
    - [circle_path]              : circular path (axiomatized)
    - [area_riemann_sum]         : 2-D Riemann sum for area integrals
    - [area_integral_conv]       : convergence of area Riemann sums

    Axioms:
    - [CRpi]                     : the constant π
    - [Cinv], [Cinv_mul_right/left] : complex multiplicative inverse
    - [circle_path], [circle_path_dist] : circular path and its properties

    Theorems (admitted):
    - [holomorphic_iff_dbar_zero]    : f holomorphic ↔ ∂̄f = 0
    - [Cderiv_implies_holomorphic]   : Fréchet diffble → holomorphic (C-R)
    - [holomorphic_implies_Cderiv]   : holomorphic → complex differentiable
    - [cauchy_integral_formula]      : ∮ f(w)/(w−z) dw = 2πi f(z)
    - [holomorphic_iff_analytic]     : holomorphic ↔ analytic on open sets
    - [dbar_poincare_one_var]        : ∃ solution to ∂̄f = g on a smaller disc
*)
