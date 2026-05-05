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
(* CAG zero-dependent Definition pullback_canonical theories/Blowup/CanonicalBundle.v:35 BEGIN
Definition pullback_canonical (M : KahlerManifold) (x : Cn (km_dim M)) :
    HolLineBundleCech (km_manifold (blowup M x)) :=
  pullback_lb M x (canonical_bundle M).
   CAG zero-dependent Definition pullback_canonical theories/Blowup/CanonicalBundle.v:35 END *)

(** The (n-1)-th power of [E]. *)
(* CAG zero-dependent Definition exceptional_power theories/Blowup/CanonicalBundle.v:42 BEGIN
Definition exceptional_power (M : KahlerManifold) (x : Cn (km_dim M)) :
    HolLineBundleCech (km_manifold (blowup M x)) :=
  lb_power (blowup M x) (exceptional_line_bundle M x) (km_dim M - 1).
   CAG zero-dependent Definition exceptional_power theories/Blowup/CanonicalBundle.v:42 END *)

(* ================================================================== *)
(** * 2. Canonical bundle formula                                       *)
(* ================================================================== *)

(** Main theorem: K_{M̃} = π*K_M ⊗ [E]^{n-1}.
    The canonical bundle formula for blowing up a point.  Famous-old
    classical (Griffiths–Harris §I.4 "Canonical bundle of the
    blow-up", Hartshorne II.8.24).  Recorded as a Conjecture per the
    "famous-old" rule. *)
(* CAG zero-dependent Conjecture canonical_bundle_of_blowup_at_point theories/Blowup/CanonicalBundle.v:53 BEGIN
Conjecture canonical_bundle_of_blowup_at_point :
    forall (M : KahlerManifold) (x : Cn (km_dim M)),
    canonical_bundle (blowup M x) =
    blowup_tensor M x
        (pullback_canonical M x)
        (exceptional_power M x).
   CAG zero-dependent Conjecture canonical_bundle_of_blowup_at_point theories/Blowup/CanonicalBundle.v:53 END *)

(** Consequence: K_{M̃} ⊗ [-E]^{n-1} = π*K_M.  An algebraic
    rearrangement of [canonical_bundle_of_blowup_at_point]; recorded
    as a Conjecture chained off the same famous-old result. *)
(* CAG zero-dependent Conjecture canonical_bundle_blowup_simplified theories/Blowup/CanonicalBundle.v:63 BEGIN
Conjecture canonical_bundle_blowup_simplified :
    forall (M : KahlerManifold) (x : Cn (km_dim M)),
    blowup_tensor M x
        (canonical_bundle (blowup M x))
        (lb_power (blowup M x) (neg_exceptional_line_bundle M x) (km_dim M - 1)) =
    pullback_canonical M x.
   CAG zero-dependent Conjecture canonical_bundle_blowup_simplified theories/Blowup/CanonicalBundle.v:63 END *)

(* ================================================================== *)
(** * 3. Positivity and vanishing consequences                         *)
(* ================================================================== *)

(** When L is positive on M, π*L^k ⊗ K_{M̃} is positive for k ≫ 0.
    Standard Kodaira-positivity argument (Griffiths–Harris §I.4
    "Twist by canonical"); left as a Conjecture under the
    structural [canonical_bundle], [pullback_lb], [blowup_tensor]
    Parameters. *)
(* CAG zero-dependent Conjecture positive_twist_plus_canonical theories/Blowup/CanonicalBundle.v:79 BEGIN
Conjecture positive_twist_plus_canonical : forall (M : KahlerManifold)
    (x : Cn (km_dim M)) (L : HolLineBundleCech (km_manifold M)),
    positive_line_bundle M L ->
    exists k1 : nat,
    positive_line_bundle (blowup M x)
        (blowup_tensor M x
            (lb_power (blowup M x) (pullback_lb M x L) k1)
            (canonical_bundle (blowup M x))).
   CAG zero-dependent Conjecture positive_twist_plus_canonical theories/Blowup/CanonicalBundle.v:79 END *)

(** Rewriting identity for the Kodaira-vanishing application:
        π*L^k ⊗ [-E] ≅ (π*L^{k₁} ⊗ K_{M̃}) ⊗ (π*L^{k'} ⊗ [-E]^n)
    for appropriate k₁, k' depending on n = km_dim M.  Substituting
    [K_{M̃} = π*K_M + (n-1)E] yields the standard split into a
    K-positive piece and a (-nE)-piece used to feed
    [positivity_of_pullback_minus_exceptional_divisor] into Kodaira.

    Reference: Griffiths–Harris §I.4 "Decomposition for vanishing".
    Recorded as an existential over [k1, k']: there exist k₁, k' so
    that the line-bundle isomorphism holds.  Paper-attributable. *)
(* CAG zero-dependent Axiom blowup_bundle_decomposition theories/Blowup/CanonicalBundle.v:96 BEGIN
Axiom blowup_bundle_decomposition :
  forall (M : KahlerManifold) (x : Cn (km_dim M))
         (L : HolLineBundleCech (km_manifold M)) (k : nat),
  exists k1 k' : nat,
    hlb_iso
      (blowup_tensor M x
         (lb_power (blowup M x) (pullback_lb M x L) k)
         (neg_exceptional_line_bundle M x))
      (blowup_tensor M x
         (blowup_tensor M x
            (lb_power (blowup M x) (pullback_lb M x L) k1)
            (canonical_bundle (blowup M x)))
         (blowup_tensor M x
            (lb_power (blowup M x) (pullback_lb M x L) k')
            (lb_power (blowup M x) (neg_exceptional_line_bundle M x)
                      (km_dim M)))).
   CAG zero-dependent Axiom blowup_bundle_decomposition theories/Blowup/CanonicalBundle.v:96 END *)
(** [π*L^k ⊗ [-E]] decomposes as
    [(π*L^{k₁} ⊗ K_{M̃}) ⊗ (π*L^{k'} ⊗ [-E]^n)] for some k₁, k'.
    Reference: Griffiths–Harris §I.4 (canonical-bundle blow-up
    formula plus index-arithmetic). *)
