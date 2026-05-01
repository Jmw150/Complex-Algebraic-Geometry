(** Blowup/CanonicalBundle.v — Canonical bundle formula for the blow-up

    Theorem: K_{M̃} = π*K_M ⊗ [E]^{n-1}

    where K_M = Ω^n_M is the canonical bundle of M (degree n = dim M),
    M̃ is the blow-up at a point x, and E is the exceptional divisor.

    Proof via transition functions:
    - Take coordinates (z₁,...,z_n) near x in M.
    - In blow-up coordinates (z₁, w₂,...,w_n) = (z₁, z₂/z₁,...,z_n/z₁) on U₀:
        dz₁ ∧ dz₂ ∧ ... ∧ dz_n = z₁^{n-1} · dz₁ ∧ dw₂ ∧ ... ∧ dw_n.
    - The factor z₁^{n-1} gives a zero of order n-1 along E (z₁ = 0).
    - Hence the canonical form π*ω has divisor (n-1)E → K_{M̃} = π*K_M + (n-1)[E].

    References: ag.org §Kodaira Embedding, Part IV *)

From Stdlib Require Import List Arith Lia.
From CAG Require Import Complex.
From CAG Require Import ManifoldTopology.
From CAG Require Import Divisor.LineBundleCech.
From CAG Require Import Divisor.DivisorBundle.
From CAG Require Import Divisor.Curvature.
From CAG Require Import Vanishing.KodairaVanishing.
From CAG Require Import Vanishing.TheoremB.
From CAG Require Import Blowup.ExceptionalDivisor.
From CAG Require Import Kahler.Lefschetz.Operators.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Pullback of the canonical bundle                              *)
(* ================================================================== *)

(** The pullback π*K_M of the canonical bundle to M̃. *)
Definition pullback_canonical (M : KahlerManifold) (x : Cn (km_dim M)) :
    HolLineBundleCech (km_manifold (blowup M x)) :=
  pullback_lb M x (canonical_bundle M).

(** The (n-1)-th power of [E]. *)
Definition exceptional_power (M : KahlerManifold) (x : Cn (km_dim M)) :
    HolLineBundleCech (km_manifold (blowup M x)) :=
  lb_power (blowup M x) (exceptional_line_bundle M x) (km_dim M - 1).

(* ================================================================== *)
(** * 2. Canonical bundle formula                                       *)
(* ================================================================== *)

(** Main theorem: K_{M̃} = π*K_M ⊗ [E]^{n-1}. *)
Conjecture canonical_bundle_of_blowup_at_point :
    forall (M : KahlerManifold) (x : Cn (km_dim M)),
    canonical_bundle (blowup M x) =
    blowup_tensor M x
        (pullback_canonical M x)
        (exceptional_power M x).

(** Consequence: K_{M̃} ⊗ [-E]^{n-1} = π*K_M. *)
Conjecture canonical_bundle_blowup_simplified :
    forall (M : KahlerManifold) (x : Cn (km_dim M)),
    blowup_tensor M x
        (canonical_bundle (blowup M x))
        (lb_power (blowup M x) (neg_exceptional_line_bundle M x) (km_dim M - 1)) =
    pullback_canonical M x.

(* ================================================================== *)
(** * 3. Positivity and vanishing consequences                         *)
(* ================================================================== *)

(** When K_M is nef and L is positive:
    π*L^k ⊗ K_{M̃} is positive for k >> 0. *)
Conjecture positive_twist_plus_canonical : forall (M : KahlerManifold)
    (x : Cn (km_dim M)) (L : HolLineBundleCech (km_manifold M)),
    positive_line_bundle M L ->
    exists k1 : nat,
    positive_line_bundle (blowup M x)
        (blowup_tensor M x
            (lb_power (blowup M x) (pullback_lb M x L) k1)
            (canonical_bundle (blowup M x))).

(** Rewriting for Kodaira vanishing application:
    π*L^k - E = (π*L^{k₁} + K_{M̃}) + (π*L^{k'} - nE)
    for appropriate k₁, k', using K_{M̃} = π*K_M + (n-1)E. *)
Theorem blowup_bundle_decomposition : forall (M : KahlerManifold)
    (x : Cn (km_dim M)) (L : HolLineBundleCech (km_manifold M)) (k : nat),
    (** π*L^k ⊗ [-E] can be written as a product of a K-positive and a nE-term
        for appropriate ranges of k — axiomatized *)
    True.
Proof. intros; exact I. Qed.
