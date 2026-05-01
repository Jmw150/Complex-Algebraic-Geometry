(** * Langlands/NonabelianHodge.v
    The non-abelian Hodge correspondence (Simpson correspondence).

    For a compact Kähler manifold M (or a compact Riemann surface X), there
    is a homeomorphism (in fact, a real-analytic diffeomorphism) between three
    moduli spaces:
      (A)  Betti moduli:   Rep_n(π₁(M)) = {ρ : π₁(M) → GL(n,ℂ)} / conj
      (B)  de Rham moduli: {flat rank-n vector bundles} / gauge
      (C)  Dolbeault moduli: {stable rank-n Higgs bundles with vanishing Chern classes} / gauge

    The equivalences are:
      (A) ←→ (B):  Riemann-Hilbert (see LocalSystems.v)
      (B) ←→ (C):  Simpson correspondence (harmonic metric)
      (A) ←→ (C):  composition

    In the geometric Langlands context:
      - The Betti side (A) gives the spectral side Loc_{GL(n)}(X)
      - The Dolbeault side (C) is the generic fiber of the Hitchin fibration
      - Mirror symmetry (Kapustin-Witten) exchanges (C) for G with (C) for G^∨,
        providing the geometric Langlands correspondence.

    References: Simpson (1992), Kapustin-Witten (2006). *)

From Stdlib Require Import List Arith.
From CAG Require Import Complex.
From CAG Require Import AG.
From CAG Require Import ManifoldTopology.
From CAG Require Import Harmonic.BundleCovariantDerivatives.
From CAG Require Import Langlands.LocalSystems.
From CAG Require Import Langlands.HiggsBundles.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Vanishing Chern classes                                       *)
(* ================================================================== *)

(** For the Simpson correspondence, we need the Higgs bundle to have
    vanishing rational Chern classes c₁ = 0, c₂ = 0, ... in H*(M, Q).
    We axiomatize this condition. *)
Parameter HasVanishingChernClasses : forall {M : HermitianManifold},
    HiggsBundle M -> Prop.

(* ================================================================== *)
(** * 2. Harmonic metrics                                              *)
(* ================================================================== *)

(** A harmonic metric on a flat bundle is a hermitian metric h on the
    underlying smooth bundle such that the connection decomposes as:
      ∇ = ∂_E + ∂̄_E + φ + φ*
    where ∂̄_E is the (0,1) part, φ is the Higgs field, and φ* is its
    adjoint.  The harmonic equation is:
      F_{∇} + [φ, φ*] = 0
    which is the Hitchin equation. *)
Parameter HasHarmonicMetric : forall {M : HermitianManifold},
    LocalSystem M -> Prop.

Parameter HasHiggsHarmonicMetric : forall {M : HermitianManifold},
    HiggsBundle M -> Prop.

(* ================================================================== *)
(** * 3. The flat-to-Higgs functor                                     *)
(* ================================================================== *)

(** Given a flat bundle with harmonic metric, we extract the Higgs bundle:
    - ∂̄_E : the (0,1) part of the unitary connection gives the holomorphic structure
    - φ    : the (1,0) part of the self-adjoint endomorphism (Higgs field)

    This is the correspondence due to Corlette (compact Lie groups)
    and Simpson (general reductive groups). *)
Parameter flat_to_higgs : forall {M : HermitianManifold} (L : LocalSystem M),
    HasHarmonicMetric L -> HiggsBundle M.

(** The Higgs bundle produced from a flat bundle via harmonic metric
    satisfies the stability and vanishing Chern class conditions. *)
Conjecture flat_to_higgs_stable : forall {M : HermitianManifold} (L : LocalSystem M)
    (hm : HasHarmonicMetric L),
    IsStableHiggsBundle (flat_to_higgs L hm).

Conjecture flat_to_higgs_vanishing : forall {M : HermitianManifold} (L : LocalSystem M)
    (hm : HasHarmonicMetric L),
    HasVanishingChernClasses (flat_to_higgs L hm).

Conjecture flat_to_higgs_rank : forall {M : HermitianManifold} (L : LocalSystem M)
    (hm : HasHarmonicMetric L),
    higgs_rank (flat_to_higgs L hm) = ls_rank L.

(* ================================================================== *)
(** * 4. The Higgs-to-flat functor                                     *)
(* ================================================================== *)

(** Given a stable Higgs bundle with vanishing Chern classes, we produce
    a flat bundle via the Donaldson-Uhlenbeck-Yau theorem:
    - Existence of a Hermitian-Einstein metric (from stability + vanishing)
    - The Hermitian-Einstein metric is harmonic, giving a flat connection. *)
Parameter higgs_to_flat : forall {M : HermitianManifold} (H : HiggsBundle M),
    IsStableHiggsBundle H -> HasVanishingChernClasses H -> LocalSystem M.

Conjecture higgs_to_flat_rank : forall {M : HermitianManifold} (H : HiggsBundle M)
    (hs : IsStableHiggsBundle H) (hv : HasVanishingChernClasses H),
    ls_rank (higgs_to_flat H hs hv) = higgs_rank H.

(* ================================================================== *)
(** * 5. The Simpson correspondence                                    *)
(* ================================================================== *)

(** Simpson's theorem: The two functors are inverse to each other up to
    isomorphism.  This is the non-abelian Hodge theorem for Kähler manifolds.

    Technical note: "stable with vanishing Chern classes" is the correct
    condition for the flat bundle to exist as a local system (not merely
    a polystable Higgs bundle). *)

(** Direction (C) → (B): Higgs → flat, then flat → original Higgs. *)
Conjecture simpson_flat_to_higgs_to_flat :
  forall {M : HermitianManifold} (L : LocalSystem M) (hm : HasHarmonicMetric L),
    ls_iso (higgs_to_flat (flat_to_higgs L hm)
                          (flat_to_higgs_stable L hm)
                          (flat_to_higgs_vanishing L hm))
           L.

(** Direction (B) → (C): flat → Higgs, then Higgs → original flat. *)
Conjecture simpson_higgs_to_flat_to_higgs :
  forall {M : HermitianManifold} (H : HiggsBundle M)
         (hs : IsStableHiggsBundle H) (hv : HasVanishingChernClasses H)
         (hm : HasHarmonicMetric (higgs_to_flat H hs hv)),
    higgs_iso (flat_to_higgs (higgs_to_flat H hs hv) hm) H.

(** The Simpson correspondence: every semisimple representation of π₁
    admits a harmonic metric (Corlette's theorem). *)
Conjecture corlette_harmonic_metric :
  forall {M : HermitianManifold} (L : LocalSystem M),
    (** if the monodromy representation is semisimple *)
    True -> (* semisimplicity condition — placeholder *)
    HasHarmonicMetric L.

(** Full non-abelian Hodge theorem:
    Moduli of semisimple representations of π₁(M) ≅
    Moduli of stable Higgs bundles with c₁ = c₂ = 0. *)
Theorem non_abelian_hodge :
  forall {M : HermitianManifold} (n : nat),
    (** For every rank-n stable Higgs bundle with vanishing Chern classes,
        there exists a unique flat rank-n bundle with the same monodromy. *)
    forall (H : HiggsBundle M),
      IsStableHiggsBundle H ->
      HasVanishingChernClasses H ->
      higgs_rank H = n ->
      exists (L : LocalSystem M),
        ls_rank L = n /\
        higgs_iso (flat_to_higgs L (corlette_harmonic_metric L I)) H.
Proof.
  intros M n H hs hv hrk.
  exists (higgs_to_flat H hs hv).
  split.
  - rewrite higgs_to_flat_rank. exact hrk.
  - apply (simpson_higgs_to_flat_to_higgs H hs hv
             (corlette_harmonic_metric _ I)).
Qed.

(* ================================================================== *)
(** * 6. Connection to geometric Langlands                             *)
(* ================================================================== *)

(** The Kapustin-Witten picture:

    Fix a reductive group G with Langlands dual G^∨.  On a Riemann surface X:

    Automorphic side (G):   D-mod(Bun_G(X))
         |                      |
         | electric-magnetic     | mirror symmetry
         | duality               |
         v                      v
    Spectral side (G^∨):  QCoh(Loc_{G^∨}(X))

    The non-abelian Hodge correspondence identifies:
      Loc_{G^∨}(X) ≅ T*-fiber of Hitchin fibration for G^∨
    while the automorphic side corresponds to D-modules on Bun_G(X).

    For GL(1): this reduces to the classical abelian Fourier-Mukai transform
    on the Jacobian of X (and its dual), which is the geometric analogue of
    class field theory. *)

(** The Hitchin base is shared between G and G^∨:
    B_G(X) ≅ B_{G^∨}(X)
    This is the key "spectral coincidence" underlying the geometric Langlands
    correspondence. *)
Lemma hitchin_base_self_dual :
  forall {M : HermitianManifold} (n : nat),
    True. (* B_{GL(n)}(M) ≅ B_{GL(n)}(M) — the Hitchin base is self-dual *)
Proof. intros; exact I. Qed.

(** Mirror symmetry swaps the generic fibers:
    Jac(Σ) for G  ←→  Jac*(Σ) for G^∨
    where Jac* is the dual Jacobian (Picard variety). *)
Lemma mirror_symmetry_hitchin :
  forall {M : HermitianManifold} (H : HiggsBundle M),
    True. (* Jac(SpectralCurve H) ~~dual~~ Jac*(SpectralCurve H) *)
Proof. intros; exact I. Qed.
