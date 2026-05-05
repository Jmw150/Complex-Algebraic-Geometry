(** Harmonic/Weitzenbock.v — Weitzenböck formula

    The Weitzenböck formula relates the ∂̄-Laplacian to the rough
    Laplacian ∇*∇ via zeroth-order curvature terms:

      Δ_{∂̄} = ∇*∇ + curvature terms

    This is used to:
    1. Show Δ_{∂̄} is elliptic (same principal symbol as ∇*∇)
    2. Derive vanishing theorems via curvature positivity

    References: ag.org Part II §Weitzenböck identity *)

From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From CAG Require Import Complex.
From CAG Require Import AG.
From CAG Require Import ManifoldTopology.
From CAG Require Import LieAlgebra.
From CAG Require Import Harmonic.BundleCovariantDerivatives.
From CAG Require Import Harmonic.Sobolev.
From CAG Require Import Harmonic.Laplacian.
From CAG Require Import Harmonic.RieszResolvent.
From CAG Require Import Harmonic.Spectral.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Rough Laplacian                                              *)
(* ================================================================== *)

(** The rough (Bochner) Laplacian ∇*∇ associated to a connection.
    ∇*∇ = - Σ_i ∇_i ∇_i  (in a local orthonormal frame). *)
(* CAG zero-dependent Parameter rough_laplacian theories/Harmonic/Weitzenbock.v:34 BEGIN
Parameter rough_laplacian : forall {M : HermitianManifold} {E : HermitianBundle M}
    (conn : Connection E) (p q : nat),
    Forms_pq E p q -> Forms_pq E p q.
   CAG zero-dependent Parameter rough_laplacian theories/Harmonic/Weitzenbock.v:34 END *)

(** The rough Laplacian is non-negative: (∇*∇φ, φ) ≥ 0. *)
(* CAG zero-dependent Admitted rough_laplacian_nonneg theories/Harmonic/Weitzenbock.v:42 BEGIN
Theorem rough_laplacian_nonneg : forall {M : HermitianManifold} {E : HermitianBundle M}
    (conn : Connection E) (p q : nat) (φ : Forms_pq E p q),
    0 <= L2_inner (rough_laplacian conn p q φ) φ.
Proof. admit. Admitted.
   CAG zero-dependent Admitted rough_laplacian_nonneg theories/Harmonic/Weitzenbock.v:42 END *)

(** The rough Laplacian is self-adjoint. *)
(* CAG zero-dependent Admitted rough_laplacian_self_adjoint theories/Harmonic/Weitzenbock.v:50 BEGIN
Theorem rough_laplacian_self_adjoint : forall {M : HermitianManifold}
    {E : HermitianBundle M} (conn : Connection E) (p q : nat)
    (φ ψ : Forms_pq E p q),
    L2_inner (rough_laplacian conn p q φ) ψ =
    L2_inner φ (rough_laplacian conn p q ψ).
Proof. admit. Admitted.
   CAG zero-dependent Admitted rough_laplacian_self_adjoint theories/Harmonic/Weitzenbock.v:50 END *)

(* ================================================================== *)
(** * 2. Curvature endomorphism                                       *)
(* ================================================================== *)

(** The curvature endomorphism R_{p,q} acting on E-valued (p,q)-forms.
    This is a zeroth-order operator built from the curvature of E
    and the Riemann curvature of M. *)
(* CAG zero-dependent Parameter curv_endomorphism theories/Harmonic/Weitzenbock.v:63 BEGIN
Parameter curv_endomorphism : forall {M : HermitianManifold} {E : HermitianBundle M}
    (conn : Connection E) (p q : nat),
    Forms_pq E p q -> Forms_pq E p q.
   CAG zero-dependent Parameter curv_endomorphism theories/Harmonic/Weitzenbock.v:63 END *)

(** The curvature endomorphism is self-adjoint. *)
(* CAG zero-dependent Admitted curv_endomorphism_self_adjoint theories/Harmonic/Weitzenbock.v:69 BEGIN
Theorem curv_endomorphism_self_adjoint : forall {M : HermitianManifold}
    {E : HermitianBundle M} (conn : Connection E) (p q : nat)
    (φ ψ : Forms_pq E p q),
    L2_inner (curv_endomorphism conn p q φ) ψ =
    L2_inner φ (curv_endomorphism conn p q ψ).
Proof. admit. Admitted.
   CAG zero-dependent Admitted curv_endomorphism_self_adjoint theories/Harmonic/Weitzenbock.v:69 END *)

(* ================================================================== *)
(** * 3. Weitzenböck identity                                         *)
(* ================================================================== *)

(** The Weitzenböck formula:
      Δ_{∂̄} φ = ∇*∇ φ + R_{p,q} φ
    where R_{p,q} is a zeroth-order operator depending on the curvatures
    of E and M.

    This is a local computation in an orthonormal frame using the
    Kähler identities and the commutator formula for curvature. *)
(* CAG zero-dependent Admitted weitzenbock theories/Harmonic/Weitzenbock.v:90 BEGIN
Theorem weitzenbock : forall {M : HermitianManifold} {E : HermitianBundle M}
    (conn : Connection E) (p q : nat) (φ : Forms_pq E p q),
    dbar_laplacian p q φ =
    forms_pq_add (rough_laplacian conn p q φ) (curv_endomorphism conn p q φ).
Proof. admit. Admitted.
   CAG zero-dependent Admitted weitzenbock theories/Harmonic/Weitzenbock.v:90 END *)

(* ================================================================== *)
(** * 4. Ellipticity of Δ from Weitzenböck                           *)
(* ================================================================== *)

(** The rough Laplacian ∇*∇ is elliptic of order 2 in any local frame.
    Since the difference Δ_{∂̄} - ∇*∇ = R_{p,q} is zeroth order,
    Δ_{∂̄} is also elliptic of order 2. *)
(* CAG constructive-remove Theorem dbar_laplacian_elliptic_via_weitzenbock theories/Harmonic/Weitzenbock.v:107 BEGIN -- repair partially commented declaration
Theorem dbar_laplacian_elliptic_via_weitzenbock :
    forall {M : HermitianManifold} {E : HermitianBundle M}
    (* CAG constructive-remove Command (conn theories/Harmonic/Weitzenbock.v:109 BEGIN -- missing Connection
(conn : Connection E) (p q : nat),
    (** Δ_{∂̄} is an elliptic operator of order 2 *)
    True.

   CAG constructive-remove Command (conn theories/Harmonic/Weitzenbock.v:109 END *)
(* CAG constructive-remove Command Proof. theories/Harmonic/Weitzenbock.v:115 BEGIN -- compile error
Proof.

   CAG constructive-remove Command Proof. theories/Harmonic/Weitzenbock.v:115 END *)
  (* CAG constructive-remove Command exact theories/Harmonic/Weitzenbock.v:119 BEGIN -- compile error
exact (fun _ _ _ _ _ => I).

   CAG constructive-remove Command exact theories/Harmonic/Weitzenbock.v:119 END *)
(* CAG constructive-remove Command Qed. theories/Harmonic/Weitzenbock.v:123 BEGIN -- compile error
Qed.

   CAG constructive-remove Command Qed. theories/Harmonic/Weitzenbock.v:123 END *)
   CAG constructive-remove Theorem dbar_laplacian_elliptic_via_weitzenbock theories/Harmonic/Weitzenbock.v:107 END *)

(* ================================================================== *)
(** * 5. Bochner-Kodaira vanishing (setup)                           *)
(* ================================================================== *)

(** If the curvature endomorphism R_{p,q} is strictly positive, meaning
    (R_{p,q}φ, φ) ≤ 0 implies φ = 0 (equivalently: for φ ≠ 0, (Rφ,φ) > 0),
    then Harm^{p,q}(M,E) = 0.
    Proof: 0 = (Δφ,φ) = (∇*∇φ,φ) + (Rφ,φ); since (∇*∇φ,φ) ≥ 0, we get
    (Rφ,φ) ≤ 0, hence φ = 0 by the positivity hypothesis. *)
(* CAG zero-dependent Theorem bochner_vanishing_setup theories/Harmonic/Weitzenbock.v:117 BEGIN
Theorem bochner_vanishing_setup : forall {M : HermitianManifold}
    {E : HermitianBundle M} (conn : Connection E) (p q : nat),
    (** curvature is strictly positive: (Rφ,φ) ≤ 0 implies φ = 0 *)
    (forall (φ : Forms_pq E p q),
       L2_inner (curv_endomorphism conn p q φ) φ <= 0 -> φ = forms_pq_zero) ->
    (** Then every harmonic form vanishes *)
    forall (φ : Forms_pq E p q), is_harmonic φ -> φ = forms_pq_zero.
Proof.
  intros M E conn p q Hcurv_pos φ Hharm.
  (** Step 1: (Δφ,φ) = 0 since Δφ = 0 *)
  assert (Hinner_zero : L2_inner (dbar_laplacian p q φ) φ = 0).
  { unfold is_harmonic in Hharm. rewrite Hharm. apply L2_inner_zero_left. }
  (** Step 2: By Weitzenböck, (Δφ,φ) = (∇*∇φ,φ) + (Rφ,φ) *)
  rewrite (weitzenbock conn p q φ) in Hinner_zero.
  rewrite L2_inner_add_left in Hinner_zero.
  (** Step 3: (∇*∇φ,φ) ≥ 0, so (Rφ,φ) ≤ 0 *)
  pose proof (rough_laplacian_nonneg conn p q φ) as Hrl_nn.
  assert (Hcurv_le : L2_inner (curv_endomorphism conn p q φ) φ <= 0).
  { apply (CReal_nonneg_add_zero_rhs_le (L2_inner (rough_laplacian conn p q φ) φ)).
    - exact Hrl_nn.
    - exact Hinner_zero. }
  (** Step 4: (Rφ,φ) ≤ 0 and strict positivity → φ = 0 *)
  exact (Hcurv_pos φ Hcurv_le).
Qed.
   CAG zero-dependent Theorem bochner_vanishing_setup theories/Harmonic/Weitzenbock.v:117 END *)
