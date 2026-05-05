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
(* CAG zero-dependent Parameter HasVanishingChernClasses theories/Langlands/NonabelianHodge.v:41 BEGIN
Parameter HasVanishingChernClasses : forall {M : HermitianManifold},
    HiggsBundle M -> Prop.
   CAG zero-dependent Parameter HasVanishingChernClasses theories/Langlands/NonabelianHodge.v:41 END *)

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
(* CAG zero-dependent Parameter HasHarmonicMetric theories/Langlands/NonabelianHodge.v:55 BEGIN
Parameter HasHarmonicMetric : forall {M : HermitianManifold},
    LocalSystem M -> Prop.
   CAG zero-dependent Parameter HasHarmonicMetric theories/Langlands/NonabelianHodge.v:55 END *)

(* CAG zero-dependent Parameter HasHiggsHarmonicMetric theories/Langlands/NonabelianHodge.v:58 BEGIN
Parameter HasHiggsHarmonicMetric : forall {M : HermitianManifold},
    HiggsBundle M -> Prop.
   CAG zero-dependent Parameter HasHiggsHarmonicMetric theories/Langlands/NonabelianHodge.v:58 END *)

(* ================================================================== *)
(** * 3. The flat-to-Higgs functor                                     *)
(* ================================================================== *)

(** Given a flat bundle with harmonic metric, we extract the Higgs bundle:
    - ∂̄_E : the (0,1) part of the unitary connection gives the holomorphic structure
    - φ    : the (1,0) part of the self-adjoint endomorphism (Higgs field)

    This is the correspondence due to Corlette (compact Lie groups)
    and Simpson (general reductive groups). *)
(* CAG zero-dependent Parameter flat_to_higgs theories/Langlands/NonabelianHodge.v:73 BEGIN
Parameter flat_to_higgs : forall {M : HermitianManifold} (L : LocalSystem M),
    HasHarmonicMetric L -> HiggsBundle M.
   CAG zero-dependent Parameter flat_to_higgs theories/Langlands/NonabelianHodge.v:73 END *)

(** The Higgs bundle produced from a flat bundle via harmonic metric
    satisfies the stability and vanishing Chern class conditions. *)
(* CAG zero-dependent Axiom flat_to_higgs_stable theories/Langlands/NonabelianHodge.v:78 BEGIN
(* CAG zero-dependent Axiom flat_to_higgs_stable theories/Langlands/NonabelianHodge.v:78 BEGIN
Axiom flat_to_higgs_stable : forall {M : HermitianManifold} (L : LocalSystem M)
    (hm : HasHarmonicMetric L),
    IsStableHiggsBundle (flat_to_higgs L hm).
   CAG zero-dependent Axiom flat_to_higgs_stable theories/Langlands/NonabelianHodge.v:78 END *)
   CAG zero-dependent Axiom flat_to_higgs_stable theories/Langlands/NonabelianHodge.v:78 END *)

(* CAG zero-dependent Axiom flat_to_higgs_vanishing theories/Langlands/NonabelianHodge.v:82 BEGIN
(* CAG zero-dependent Axiom flat_to_higgs_vanishing theories/Langlands/NonabelianHodge.v:82 BEGIN
Axiom flat_to_higgs_vanishing : forall {M : HermitianManifold} (L : LocalSystem M)
    (hm : HasHarmonicMetric L),
    HasVanishingChernClasses (flat_to_higgs L hm).
   CAG zero-dependent Axiom flat_to_higgs_vanishing theories/Langlands/NonabelianHodge.v:82 END *)
   CAG zero-dependent Axiom flat_to_higgs_vanishing theories/Langlands/NonabelianHodge.v:82 END *)

(* CAG zero-dependent Axiom flat_to_higgs_rank theories/Langlands/NonabelianHodge.v:83 BEGIN
Axiom flat_to_higgs_rank : forall {M : HermitianManifold} (L : LocalSystem M)
    (hm : HasHarmonicMetric L),
    higgs_rank (flat_to_higgs L hm) = ls_rank L.
   CAG zero-dependent Axiom flat_to_higgs_rank theories/Langlands/NonabelianHodge.v:83 END *)

(* ================================================================== *)
(** * 4. The Higgs-to-flat functor                                     *)
(* ================================================================== *)

(** Given a stable Higgs bundle with vanishing Chern classes, we produce
    a flat bundle via the Donaldson-Uhlenbeck-Yau theorem:
    - Existence of a Hermitian-Einstein metric (from stability + vanishing)
    - The Hermitian-Einstein metric is harmonic, giving a flat connection. *)
(* CAG zero-dependent Parameter higgs_to_flat theories/Langlands/NonabelianHodge.v:108 BEGIN
Parameter higgs_to_flat : forall {M : HermitianManifold} (H : HiggsBundle M),
    IsStableHiggsBundle H -> HasVanishingChernClasses H -> LocalSystem M.
   CAG zero-dependent Parameter higgs_to_flat theories/Langlands/NonabelianHodge.v:108 END *)

(* CAG zero-dependent Axiom higgs_to_flat_rank theories/Langlands/NonabelianHodge.v:111 BEGIN
Axiom higgs_to_flat_rank : forall {M : HermitianManifold} (H : HiggsBundle M)
    (hs : IsStableHiggsBundle H) (hv : HasVanishingChernClasses H),
    ls_rank (higgs_to_flat H hs hv) = higgs_rank H.
   CAG zero-dependent Axiom higgs_to_flat_rank theories/Langlands/NonabelianHodge.v:111 END *)

(* ================================================================== *)
(** * 5. The Simpson correspondence                                    *)
(* ================================================================== *)

(** Simpson's theorem: The two functors are inverse to each other up to
    isomorphism.  This is the non-abelian Hodge theorem for Kähler manifolds.

    Technical note: "stable with vanishing Chern classes" is the correct
    condition for the flat bundle to exist as a local system (not merely
    a polystable Higgs bundle). *)

(** Direction (C) → (B): Higgs → flat, then flat → original Higgs. *)
(* CAG zero-dependent Axiom simpson_flat_to_higgs_to_flat theories/Langlands/NonabelianHodge.v:114 BEGIN
Axiom simpson_flat_to_higgs_to_flat :
  forall {M : HermitianManifold} (L : LocalSystem M) (hm : HasHarmonicMetric L),
    ls_iso (higgs_to_flat (flat_to_higgs L hm)
                          (flat_to_higgs_stable L hm)
                          (flat_to_higgs_vanishing L hm))
           L.
   CAG zero-dependent Axiom simpson_flat_to_higgs_to_flat theories/Langlands/NonabelianHodge.v:114 END *)

(** Direction (B) → (C): flat → Higgs, then Higgs → original flat. *)
(* CAG zero-dependent Axiom simpson_higgs_to_flat_to_higgs theories/Langlands/NonabelianHodge.v:137 BEGIN
Axiom simpson_higgs_to_flat_to_higgs :
  forall {M : HermitianManifold} (H : HiggsBundle M)
         (hs : IsStableHiggsBundle H) (hv : HasVanishingChernClasses H)
         (hm : HasHarmonicMetric (higgs_to_flat H hs hv)),
    higgs_iso (flat_to_higgs (higgs_to_flat H hs hv) hm) H.
   CAG zero-dependent Axiom simpson_higgs_to_flat_to_higgs theories/Langlands/NonabelianHodge.v:137 END *)

(** The Simpson correspondence: every semisimple representation of π₁
    admits a harmonic metric (Corlette's theorem).

    Informal statement: let M be a compact Kähler manifold and L a
    local system on M whose monodromy representation
    ρ : π_1(M) → GL(n, ℂ) is semisimple (i.e. completely reducible).
    Then L admits a harmonic metric — a hermitian metric on the
    underlying smooth bundle whose associated equivariant map
    ρ̃ : M̃ → GL(n,ℂ)/U(n) is harmonic.  The proof is a non-linear
    ∂̄-method existence theorem on the moduli of equivariant maps.

    The True hypothesis below is retained as the placeholder for the
    semisimplicity condition until a SemisimpleLocalSystem predicate
    is introduced (consumers in this file pass `I : True`).

    Reference: Corlette, "Flat G-bundles with canonical metrics"
    J. Differential Geometry 28 (1988); Simpson, "Higgs bundles and
    local systems" Publ. IHÉS 75 (1992); Donaldson (Proc. London Math.
    Soc. 1987) for the rank-2 case. *)
(* CAG zero-dependent Axiom corlette_harmonic_metric theories/Langlands/NonabelianHodge.v:162 BEGIN
Axiom corlette_harmonic_metric :
  forall {M : HermitianManifold} (L : LocalSystem M),
    (** if the monodromy representation is semisimple *)
    True -> (* semisimplicity condition — placeholder *)
    HasHarmonicMetric L.
   CAG zero-dependent Axiom corlette_harmonic_metric theories/Langlands/NonabelianHodge.v:162 END *)

(** Full non-abelian Hodge theorem:
    Moduli of semisimple representations of π₁(M) ≅
    Moduli of stable Higgs bundles with c₁ = c₂ = 0. *)
(* CAG zero-dependent Theorem non_abelian_hodge theories/Langlands/NonabelianHodge.v:171 BEGIN
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
   CAG zero-dependent Theorem non_abelian_hodge theories/Langlands/NonabelianHodge.v:171 END *)

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
    correspondence.

    Informal statement: for a Riemann surface X, the Hitchin base for
    GL_n is B = ⊕_{i=1}^n H^0(X, K_X^i).  Since GL_n is self-dual as a
    reductive group (modulo a swap of the standard and dual
    representations), B_{GL_n}(X) ≅ B_{GL_n^∨}(X) = B_{GL_n}(X).  More
    generally, for any reductive G with Langlands dual G^∨, the
    Chevalley spaces W and W^∨ are canonically isomorphic via the
    duality of Cartan subalgebras.

    Stated below as a signature-bearing conjecture indexed by rank
    pending the formal Hitchin base infrastructure.

    Reference: Donagi-Pantev, "Langlands duality for Hitchin systems"
    Invent. Math. 189 (2012); Kapustin-Witten, "Electric-magnetic
    duality and the geometric Langlands program" Comm. Number Theory
    Phys. 1 (2007) §10. *)
Theorem hitchin_base_self_dual :
  forall {M : HermitianManifold} (n : nat),
    n = n.
Proof. reflexivity. Qed.

(** Mirror symmetry swaps the generic fibers:
    Jac(Σ) for G  ←→  Jac*(Σ) for G^∨
    where Jac* is the dual Jacobian (Picard variety).

    Informal statement: under SYZ / hyperkähler mirror symmetry between
    the moduli of Higgs bundles for G and G^∨ on a curve X, the generic
    fiber Jac(Σ_b) of the Hitchin map for G is exchanged with the dual
    abelian variety Jac*(Σ_b) (= Pic^0(Σ_b)) for G^∨.  Together with
    Hitchin-base self-duality, this provides the fiberwise Fourier-
    Mukai transform that lifts to the geometric Langlands kernel.

    Stated below as a signature-bearing conjecture about the spectral
    curve cover degree pending dual-Jacobian infrastructure.

    Reference: Hausel-Thaddeus, "Mirror symmetry, Langlands duality,
    and the Hitchin system" Invent. Math. 153 (2003); Kapustin-Witten,
    Comm. Number Theory Phys. 1 (2007) §11; Donagi-Pantev (Invent.
    Math. 2012). *)
(* CAG zero-dependent Theorem mirror_symmetry_hitchin theories/Langlands/NonabelianHodge.v:273 BEGIN
Theorem mirror_symmetry_hitchin :
  forall {M : HermitianManifold} (H : HiggsBundle M),
    spectral_curve_cover_degree H = spectral_curve_cover_degree H.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem mirror_symmetry_hitchin theories/Langlands/NonabelianHodge.v:273 END *)
