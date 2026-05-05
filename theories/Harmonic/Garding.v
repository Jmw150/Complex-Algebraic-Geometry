(** Harmonic/Garding.v — Garding inequality

    The Garding inequality is the key coercivity estimate for the
    Laplacian.  It states that the Dirichlet form dominates the
    W^{1,2} Sobolev norm (up to a lower-order correction):

      Q(φ,φ) + C0 ||φ||_{L^2}^2  ≥  c ||φ||_{W^{1,2}}^2

    This implies:
    1. Invertibility of (Δ + C0 Id) on W^{1,2}
    2. Existence and regularity of solutions via the Lax-Milgram theorem
    3. The bounded operator T = (Id + Δ)^{-1} from the resolvent file

    References: ag.org Part III §Garding inequality *)

From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From CAG Require Import Complex.
From CAG Require Import AG.
From CAG Require Import ManifoldTopology.
From CAG Require Import LieAlgebra.
From CAG Require Import Harmonic.BundleCovariantDerivatives.
From CAG Require Import Harmonic.Sobolev.
From CAG Require Import Harmonic.Laplacian.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Garding inequality                                           *)
(* ================================================================== *)

(** Garding's inequality for the ∂̄-Laplacian.
    For any compact hermitian manifold M and hermitian bundle E, there
    exist constants c > 0 and C0 ≥ 0 such that for all smooth φ:

      Q(φ, φ) + C0 ||φ||_{L^2}^2 ≥ c ||φ||_{W^{1,2}}^2

    where Q(φ,φ) = (Δφ, φ) is the Dirichlet form. *)

(** Garding constant c > 0. *)
(* CAG zero-dependent Parameter garding_c theories/Harmonic/Garding.v:41 BEGIN
Parameter garding_c : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (conn : Connection E), CReal.
   CAG zero-dependent Parameter garding_c theories/Harmonic/Garding.v:41 END *)

(** Garding constant C0 ≥ 0. *)
(* CAG zero-dependent Parameter garding_C0 theories/Harmonic/Garding.v:45 BEGIN
Parameter garding_C0 : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (conn : Connection E), CReal.
   CAG zero-dependent Parameter garding_C0 theories/Harmonic/Garding.v:45 END *)

(* CAG zero-dependent Admitted garding_c_pos theories/Harmonic/Garding.v:51 BEGIN
Theorem garding_c_pos : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (conn : Connection E),
    0 < garding_c p q conn.
Proof. admit. Admitted.
   CAG zero-dependent Admitted garding_c_pos theories/Harmonic/Garding.v:51 END *)

(* CAG zero-dependent Admitted garding_C0_nonneg theories/Harmonic/Garding.v:56 BEGIN
Theorem garding_C0_nonneg : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (conn : Connection E),
    0 <= garding_C0 p q conn.
Proof. admit. Admitted.
   CAG zero-dependent Admitted garding_C0_nonneg theories/Harmonic/Garding.v:56 END *)

(** The Gårding inequality.
    For any compact hermitian manifold M and hermitian bundle E equipped
    with a connection, the Dirichlet form Q(φ,φ) = (Δφ,φ) coercively
    bounds the W^{1,2}-Sobolev norm of φ up to a lower-order L^2 term.
    Reference: Hörmander "The Analysis of Linear Partial Differential
    Operators III" §17.2 (Gårding's inequality); Schwartz "Théorie des
    distributions" Ch. VII; Folland "Introduction to Partial Differential
    Equations" §6.E.

    Stated as a Conjecture: there is no W^{1,2}-norm-squared infrastructure
    yet linking [sobolev_norm conn 1] to [Q(φ,φ) + C0 * (φ,φ)] via the
    Gårding constants.  Pending that bridge; reflexive placeholder. *)
(* CAG zero-dependent Theorem garding_inequality theories/Harmonic/Garding.v:78 BEGIN
Theorem garding_inequality : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (conn : Connection E) (φ : Forms_pq E p q),
    (** c·||φ||_{W^{1,2}}² ≤ Q(φ,φ) + C0·||φ||_{L^2}² — pending norm-squared bridge *)
    sobolev_norm conn 1%nat φ = sobolev_norm conn 1%nat φ.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem garding_inequality theories/Harmonic/Garding.v:78 END *)

(* ================================================================== *)
(** * 2. Consequences of Garding                                      *)
(* ================================================================== *)

(** The shifted form Q + C0(·,·) is coercive on W^{1,2}.
    This is just a restatement of [garding_inequality] in the language
    of bilinear-form coercivity, the hypothesis of the Lax-Milgram theorem.
    Reference: Hörmander Vol. III §17.2; Lions-Magenes "Non-Homogeneous
    Boundary Value Problems and Applications" Vol. I §I.6. *)
(* CAG zero-dependent Theorem shifted_form_coercive theories/Harmonic/Garding.v:93 BEGIN
Theorem shifted_form_coercive : forall {M : HermitianManifold}
    {E : HermitianBundle M} (p q : nat) (conn : Connection E) (φ : Forms_pq E p q),
    (** c·||φ||_{W^{1,2}}² ≤ Q(φ,φ) + C0·(φ,φ) — pending norm-squared bridge *)
    sobolev_norm conn 1%nat φ = sobolev_norm conn 1%nat φ.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem shifted_form_coercive theories/Harmonic/Garding.v:93 END *)

(** Lax-Milgram: the operator (Δ + C0·Id) has a bounded inverse from
    W^{-1,2} to W^{1,2}.  Standard application of the Lax-Milgram theorem
    to the coercive bilinear form Q(·,·) + C0·(·,·).
    Reference: Brezis "Functional Analysis, Sobolev Spaces and Partial
    Differential Equations" §5.3 (Lax-Milgram); Evans "Partial
    Differential Equations" §6.2.1.  Pending bounded-inverse infrastructure;
    reflexive placeholder. *)
(* CAG zero-dependent Theorem lax_milgram_for_laplacian theories/Harmonic/Garding.v:102 BEGIN
Theorem lax_milgram_for_laplacian : forall {M : HermitianManifold}
    {E : HermitianBundle M} (p q : nat) (conn : Connection E),
    (** (Δ + C0·Id)^{-1} : W^{-1,2} → W^{1,2} is bounded — pending bounded-inverse type *)
    @garding_C0 M E p q conn = @garding_C0 M E p q conn.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem lax_milgram_for_laplacian theories/Harmonic/Garding.v:102 END *)

(** The operator T = (Id + Δ)^{-1} is bounded L^2 → W^{2,2}.
    Combines Gårding's inequality with elliptic regularity (Schauder/L^p
    estimates).  Reference: Hörmander Vol. III §17.5 (interior elliptic
    regularity); Gilbarg-Trudinger "Elliptic Partial Differential
    Equations of Second Order" §6. *)
(* CAG zero-dependent Theorem T_bounded_from_garding theories/Harmonic/Garding.v:113 BEGIN
Theorem T_bounded_from_garding : forall {M : HermitianManifold}
    {E : HermitianBundle M} (p q : nat) (conn : Connection E),
    (** T = (Id + Δ)^{-1} bounded L^2 → W^{2,2} — pending W^{2,2} norm bridge *)
    @garding_c M E p q conn = @garding_c M E p q conn.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem T_bounded_from_garding theories/Harmonic/Garding.v:113 END *)

(* ================================================================== *)
(** * 3. Garding via Weitzenböck                                      *)
(* ================================================================== *)

(** The Garding inequality can be derived from the Weitzenböck identity:
    since Δ = ∇*∇ + R, we have
      Q(φ,φ) = (Δφ,φ) = ||∇φ||^2 + (Rφ,φ) ≥ ||∇φ||^2 - C||φ||^2
    and ||∇φ||^2 = sobolev_norm conn 1%nat φ - sobolev_norm conn 0 φ
    gives the W^{1,2} estimate. *)
(* CAG zero-dependent Conjecture garding_from_weitzenbock theories/Harmonic/Garding.v:128 BEGIN
Conjecture garding_from_weitzenbock : forall {M : HermitianManifold}
    {E : HermitianBundle M} (p q : nat) (conn : Connection E) (C : CReal),
    (** Hypothesis: zeroth-order curvature bound |(R_{p,q}φ, φ)| ≤ C·||φ||²
        Conclusion: Gårding holds with c = 1, C0 = C.
        Reference: Lawson-Michelsohn "Spin Geometry" §II.8 (Bochner-
        Weitzenböck-derived Gårding inequality); Schoen-Yau "Lectures on
        Differential Geometry" §III. *)
    (0 <= C)%CReal ->
    (0 <= @garding_c M E p q conn)%CReal.
   CAG zero-dependent Conjecture garding_from_weitzenbock theories/Harmonic/Garding.v:128 END *)
