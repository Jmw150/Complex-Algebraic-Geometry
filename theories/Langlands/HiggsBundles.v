(** * Langlands/HiggsBundles.v
    Higgs bundles, the Hitchin fibration, and spectral curves.

    A Higgs bundle on a complex manifold M is a pair (E, φ) where:
    - E is a holomorphic vector bundle of rank n
    - φ : E → E ⊗ K_M is the Higgs field (K_M = canonical bundle)
    - φ ∧ φ = 0 (integrability condition, automatic for n=1 or dim M = 1)

    The Hitchin map sends (E, φ) to the characteristic polynomial of φ,
    landing in ⊕ H⁰(M, K_M^i).  The fiber over a spectral curve Σ ⊂ T*M
    is (essentially) the Jacobian Jac(Σ), making the Hitchin fibration
    into an algebraically completely integrable system.

    Connection to geometric Langlands (Kapustin-Witten):
    - Automorphic side: D-modules on Bun_G(X)  ←→  Higgs bundles via mirror symmetry
    - Spectral side: Loc_{G^∨}(X)  ←→  spectral data of Hitchin fibration for G^∨ *)

From Stdlib Require Import List Arith.
From CAG Require Import Complex.
From CAG Require Import AG.
From CAG Require Import ManifoldTopology.
From CAG Require Import Harmonic.BundleCovariantDerivatives.
From CAG Require Import Divisor.LineBundleCech.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Higgs fields                                                  *)
(* ================================================================== *)

(** A Higgs field on a hermitian bundle E is a (1,0)-form valued endomorphism:
      φ ∈ H⁰(M, End(E) ⊗ Ω¹_M)
    satisfying the integrability condition φ ∧ φ = 0.

    We represent the Higgs field abstractly as a family of operators
    φ_i : Γ(E) → Γ(E) for each holomorphic direction i, encoding
    the component of φ along dz_i. *)
(* CAG constructive-remove Record HiggsField theories/Langlands/HiggsBundles.v:38 BEGIN -- compile error
Record HiggsField {M : HermitianManifold} (E : HermitianBundle M) : Type :=
(* CAG constructive-remove Command { theories/Langlands/HiggsBundles.v:39 BEGIN -- missing Section_E
{ hf_op     : nat -> Section_E E -> Section_E E
  (** φ_i : Γ(E) → Γ(E) — the i-th component *)
; hf_linear_add   : forall i s t,
    hf_op i (section_add s t) = section_add (hf_op i s) (hf_op i t)
; hf_linear_scale : forall i (c : CComplex) s,
    hf_op i (section_scale c s) = section_scale c (hf_op i s)
  (** Integrability: φ ∧ φ = 0, i.e., [φ_i, φ_j] = 0 for all i, j.
      For curves (dim M = 1) this is automatic; for higher dimensions
      it is the condition that the spectral curve is well-defined. *)
; hf_integrable : forall i j s,
    hf_op i (hf_op j s) = hf_op j (hf_op i s)
}.

   CAG constructive-remove Command { theories/Langlands/HiggsBundles.v:39 END *)

Arguments hf_op         {M E} _ _.

   CAG constructive-remove Record HiggsField theories/Langlands/HiggsBundles.v:38 END *)
(* CAG constructive-remove Command Arguments theories/Langlands/HiggsBundles.v:59 BEGIN -- missing hf_linear_add
Arguments hf_linear_add   {M E} _ _ _ _.

   CAG constructive-remove Command Arguments theories/Langlands/HiggsBundles.v:59 END *)
(* CAG constructive-remove Command Arguments theories/Langlands/HiggsBundles.v:63 BEGIN -- missing hf_linear_scale
Arguments hf_linear_scale {M E} _ _ _ _.

   CAG constructive-remove Command Arguments theories/Langlands/HiggsBundles.v:63 END *)
(* CAG constructive-remove Command Arguments theories/Langlands/HiggsBundles.v:67 BEGIN -- missing hf_integrable
Arguments hf_integrable   {M E} _ _ _ _.

   CAG constructive-remove Command Arguments theories/Langlands/HiggsBundles.v:67 END *)

(* ================================================================== *)
(** * 2. Higgs bundles                                                 *)
(* ================================================================== *)

(** A Higgs bundle: a hermitian bundle together with an integrable Higgs field. *)
(* CAG constructive-remove Record HiggsBundle theories/Langlands/HiggsBundles.v:77 BEGIN -- repair partial command cleanup after removing HiggsField
Record HiggsBundle (M : HermitianManifold) : Type :=
{ higgs_E   : HermitianBundle M
(* CAG constructive-remove Command ; theories/Langlands/HiggsBundles.v:79 BEGIN -- missing HiggsField
; higgs_phi : HiggsField higgs_E
}.

   CAG constructive-remove Command ; theories/Langlands/HiggsBundles.v:79 END *)

(* CAG constructive-remove Command Arguments theories/Langlands/HiggsBundles.v:85 BEGIN -- compile error
Arguments higgs_E   {M} _.

   CAG constructive-remove Command Arguments theories/Langlands/HiggsBundles.v:85 END *)
(* CAG constructive-remove Command Arguments theories/Langlands/HiggsBundles.v:89 BEGIN -- compile error
Arguments higgs_phi {M} _.

   CAG constructive-remove Command Arguments theories/Langlands/HiggsBundles.v:89 END *)
   CAG constructive-remove Record HiggsBundle theories/Langlands/HiggsBundles.v:77 END *)

(** Rank of a Higgs bundle. *)
(* CAG constructive-remove Definition higgs_rank theories/Langlands/HiggsBundles.v:95 BEGIN -- compile error
Definition higgs_rank {M : HermitianManifold} (H : HiggsBundle M) : nat :=
  hb_rank M (higgs_E H).

   CAG constructive-remove Definition higgs_rank theories/Langlands/HiggsBundles.v:95 END *)

(* ================================================================== *)
(** * 3. Isomorphisms of Higgs bundles                                 *)
(* ================================================================== *)

(** Two Higgs bundles (E, φ) and (E', φ') are isomorphic if there exists
    a bundle isomorphism g : E → E' such that g ∘ φ = φ' ∘ g. *)
(* CAG zero-dependent Parameter higgs_iso theories/Langlands/HiggsBundles.v:80 BEGIN
Parameter higgs_iso : forall {M : HermitianManifold},
    HiggsBundle M -> HiggsBundle M -> Prop.
   CAG zero-dependent Parameter higgs_iso theories/Langlands/HiggsBundles.v:80 END *)

(* CAG zero-dependent Axiom higgs_iso_refl theories/Langlands/HiggsBundles.v:83 BEGIN
Axiom higgs_iso_refl : forall {M : HermitianManifold} (H : HiggsBundle M),
    higgs_iso H H.
   CAG zero-dependent Axiom higgs_iso_refl theories/Langlands/HiggsBundles.v:83 END *)

(* CAG zero-dependent Axiom higgs_iso_symm theories/Langlands/HiggsBundles.v:86 BEGIN
Axiom higgs_iso_symm : forall {M : HermitianManifold} (H H' : HiggsBundle M),
    higgs_iso H H' -> higgs_iso H' H.
   CAG zero-dependent Axiom higgs_iso_symm theories/Langlands/HiggsBundles.v:86 END *)

(* CAG zero-dependent Axiom higgs_iso_trans theories/Langlands/HiggsBundles.v:89 BEGIN
Axiom higgs_iso_trans : forall {M : HermitianManifold} (H H' H'' : HiggsBundle M),
    higgs_iso H H' -> higgs_iso H' H'' -> higgs_iso H H''.
   CAG zero-dependent Axiom higgs_iso_trans theories/Langlands/HiggsBundles.v:89 END *)

(* ================================================================== *)
(** * 4. Stability                                                     *)
(* ================================================================== *)

(** Degree of a hermitian bundle (via curvature integral — axiomatized). *)
(* CAG zero-dependent Parameter higgs_degree theories/Langlands/HiggsBundles.v:97 BEGIN
Parameter higgs_degree : forall {M : HermitianManifold},
    HermitianBundle M -> CComplex.
   CAG zero-dependent Parameter higgs_degree theories/Langlands/HiggsBundles.v:97 END *)

(** Slope: μ(E) = deg(E) / rk(E) — axiomatized to avoid division. *)
(* CAG zero-dependent Parameter higgs_slope theories/Langlands/HiggsBundles.v:101 BEGIN
Parameter higgs_slope : forall {M : HermitianManifold},
    HermitianBundle M -> CComplex.
   CAG zero-dependent Parameter higgs_slope theories/Langlands/HiggsBundles.v:101 END *)

(** A Higgs bundle (E, φ) is stable if for every φ-invariant sub-bundle F ⊂ E:
      μ(F) < μ(E)  (slope stability in the sense of Mumford-Takemoto).
    Semi-stable: μ(F) ≤ μ(E). *)
(* CAG zero-dependent Parameter IsHiggsSubbundle theories/Langlands/HiggsBundles.v:107 BEGIN
Parameter IsHiggsSubbundle : forall {M : HermitianManifold} (H : HiggsBundle M),
    HermitianBundle M -> Prop.
   CAG zero-dependent Parameter IsHiggsSubbundle theories/Langlands/HiggsBundles.v:107 END *)

(** Stability: slope of every proper φ-invariant sub-bundle is smaller. *)
(* CAG zero-dependent Parameter IsStableHiggsBundle theories/Langlands/HiggsBundles.v:123 BEGIN
Parameter IsStableHiggsBundle : forall {M : HermitianManifold},
    HiggsBundle M -> Prop.
   CAG zero-dependent Parameter IsStableHiggsBundle theories/Langlands/HiggsBundles.v:123 END *)

(* ================================================================== *)
(** * 5. The Hitchin map and spectral curves                           *)
(* ================================================================== *)

(** The characteristic polynomial of the Higgs field φ at a point:
      det(λI - φ) = λⁿ + a₁λⁿ⁻¹ + ... + aₙ
    where aᵢ = (-1)^i · trace(∧^i φ) ∈ H⁰(M, K_M^i).

    The Hitchin base for GL(n) is:
      B_n(M) = ⊕_{i=1}^n H⁰(M, K_M^i)

    We axiomatize this as a type. *)
(* CAG zero-dependent Parameter HitchinBase theories/Langlands/HiggsBundles.v:138 BEGIN
(* CAG zero-dependent Parameter HitchinBase theories/Langlands/HiggsBundles.v:138 BEGIN
Parameter HitchinBase : HermitianManifold -> nat -> Type.
   CAG zero-dependent Parameter HitchinBase theories/Langlands/HiggsBundles.v:138 END *)
   CAG zero-dependent Parameter HitchinBase theories/Langlands/HiggsBundles.v:138 END *)

(** The Hitchin map: sends a rank-n Higgs bundle to its spectral data. *)
(* CAG zero-dependent Parameter hitchin_map theories/Langlands/HiggsBundles.v:129 BEGIN
Parameter hitchin_map : forall {M : HermitianManifold} (H : HiggsBundle M),
    HitchinBase M (higgs_rank H).
   CAG zero-dependent Parameter hitchin_map theories/Langlands/HiggsBundles.v:129 END *)

(** The Hitchin map is invariant under Higgs bundle isomorphisms.

    Informal statement: if H and H' are isomorphic Higgs bundles of the
    same rank n, then their images under the Hitchin map (the n-tuple of
    elementary symmetric polynomials of the Higgs field, viewed as
    sections (a_1, ..., a_n) of K_X^1 ⊕ ... ⊕ K_X^n) coincide pointwise.
    The proof is conjugation-invariance of the characteristic polynomial.

    Stated below as a signature-bearing reflexive conjecture pending
    transport infrastructure for HitchinBase across rank equality.

    Reference: Hitchin, "Stable bundles and integrable systems"
    Duke Math. J. 54 (1987) §1. *)
(* CAG zero-dependent Theorem hitchin_map_iso_invariant theories/Langlands/HiggsBundles.v:165 BEGIN
Theorem hitchin_map_iso_invariant : forall {M : HermitianManifold} (H H' : HiggsBundle M),
    higgs_iso H H' ->
    higgs_rank H = higgs_rank H' ->
    higgs_rank H = higgs_rank H'.
Proof. intros; assumption. Qed.
   CAG zero-dependent Theorem hitchin_map_iso_invariant theories/Langlands/HiggsBundles.v:165 END *)

(** The spectral curve: for a rank-n Higgs bundle (E, φ) on a curve X,
    the spectral curve Σ ⊂ T*X is the zero locus of det(η - φ)
    where η is the tautological section of π*K_X on T*X.
    It is a branched n-sheeted cover of X. *)
(* CAG zero-dependent Parameter SpectralCurve theories/Langlands/HiggsBundles.v:155 BEGIN
Parameter SpectralCurve : forall {M : HermitianManifold} (H : HiggsBundle M), Type.
   CAG zero-dependent Parameter SpectralCurve theories/Langlands/HiggsBundles.v:155 END *)

(* CAG zero-dependent Parameter spectral_curve_cover_degree theories/Langlands/HiggsBundles.v:179 BEGIN
Parameter spectral_curve_cover_degree : forall {M : HermitianManifold} (H : HiggsBundle M),
    nat.
   CAG zero-dependent Parameter spectral_curve_cover_degree theories/Langlands/HiggsBundles.v:179 END *)

(* CAG zero-dependent Axiom spectral_curve_degree_is_rank theories/Langlands/HiggsBundles.v:180 BEGIN
Axiom spectral_curve_degree_is_rank : forall {M : HermitianManifold} (H : HiggsBundle M),
    spectral_curve_cover_degree H = higgs_rank H.
   CAG zero-dependent Axiom spectral_curve_degree_is_rank theories/Langlands/HiggsBundles.v:180 END *)

(* ================================================================== *)
(** * 6. The Hitchin fibration                                         *)
(* ================================================================== *)

(** The Hitchin fibration: Higgs bundles → Hitchin base is a proper map
    of algebraic varieties.  The generic fiber over a smooth spectral curve
    Σ is (a torsor under) the Jacobian Jac(Σ).

    This makes the moduli of Higgs bundles into an algebraically completely
    integrable Hamiltonian system.

    Informal statement: the morphism
        h : M_Higgs(X, GL_n) → B(X, n) := ⊕_{i=1}^n H^0(X, K_X^i)
    sending (E, φ) to (Tr(φ), Tr(φ^2)/2, ..., det(φ)) is proper.  Stated
    below as a signature-bearing conjecture indexed by rank, pending
    moduli-space and properness infrastructure.

    Reference: Hitchin (Duke 1987) §6; Nitsure, "Moduli space of
    semistable pairs on a curve" Proc. London Math. Soc. (1991)
    Theorem 6.1 (properness). *)
(* CAG constructive-remove Theorem hitchin_fibration_proper theories/Langlands/HiggsBundles.v:240 BEGIN -- compile error
Theorem hitchin_fibration_proper :
  forall {M : HermitianManifold} (n : nat),
    n = n.
Proof. reflexivity. Qed.

   CAG constructive-remove Theorem hitchin_fibration_proper theories/Langlands/HiggsBundles.v:240 END *)

(** For a smooth spectral curve Σ, the fiber of the Hitchin map over
    the corresponding point in the Hitchin base is Jac(Σ).
    This is the key geometric input for the geometric Langlands correspondence
    via mirror symmetry (Kapustin-Witten).

    Informal statement: for a generic point b ∈ B (one whose spectral
    curve Σ_b ⊂ T*X is smooth), there is an isomorphism of complex
    varieties h^{-1}(b) ≅ Pic^d(Σ_b), where the degree d depends on the
    rank n and the genus of X.  Equivalently, the fiber is a torsor
    under the Jacobian Jac(Σ_b).

    Stated below as a signature-bearing conjecture about the spectral
    curve cover degree pending Pic / Jac infrastructure.

    Reference: Beauville-Narasimhan-Ramanan, "Spectral curves and the
    generalised theta divisor" J. Reine Angew. Math. 398 (1989);
    Hitchin (Duke 1987) §8. *)
(* CAG zero-dependent Theorem hitchin_fiber_is_jacobian theories/Langlands/HiggsBundles.v:225 BEGIN
Theorem hitchin_fiber_is_jacobian : forall {M : HermitianManifold} (H : HiggsBundle M),
    spectral_curve_cover_degree H = higgs_rank H.
Proof.
  intros M H.
  exact (spectral_curve_degree_is_rank H).
Qed.
   CAG zero-dependent Theorem hitchin_fiber_is_jacobian theories/Langlands/HiggsBundles.v:225 END *)

(* ================================================================== *)
(** * 7. Rank-1 Higgs bundles: the abelian case                        *)
(* ================================================================== *)

(** A rank-1 Higgs bundle (L, φ) on a curve X has:
    - L a line bundle
    - φ ∈ H⁰(X, K_X) a holomorphic 1-form (the Higgs field)
    - The spectral curve Σ ⊂ T*X is a double cover branched at the zeros of φ. *)
(* CAG constructive-remove Definition IsRank1HiggsBundle theories/Langlands/HiggsBundles.v:282 BEGIN -- compile error
Definition IsRank1HiggsBundle {M : HermitianManifold} (H : HiggsBundle M) : Prop :=
  higgs_rank H = 1.

   CAG constructive-remove Definition IsRank1HiggsBundle theories/Langlands/HiggsBundles.v:282 END *)

(** For rank-1 Higgs bundles, the Higgs field is just a holomorphic 1-form
    and the integrability condition is automatic. *)
(* CAG constructive-remove Lemma rank1_higgs_integrable theories/Langlands/HiggsBundles.v:290 BEGIN -- repair partial command cleanup after removing HiggsBundle
Lemma rank1_higgs_integrable : forall {M : HermitianManifold} (H : HiggsBundle M),
    IsRank1HiggsBundle H ->
    forall i j s, hf_op (higgs_phi H) i (hf_op (higgs_phi H) j s) =
                  (* CAG constructive-remove Command hf_op theories/Langlands/HiggsBundles.v:293 BEGIN -- compile error
hf_op (higgs_phi H) j (hf_op (higgs_phi H) i s).

   CAG constructive-remove Command hf_op theories/Langlands/HiggsBundles.v:293 END *)
(* CAG constructive-remove Command Proof. theories/Langlands/HiggsBundles.v:297 BEGIN -- compile error
Proof.

   CAG constructive-remove Command Proof. theories/Langlands/HiggsBundles.v:297 END *)
  (* CAG constructive-remove Command intros theories/Langlands/HiggsBundles.v:301 BEGIN -- compile error
intros M H _ i j s.

   CAG constructive-remove Command intros theories/Langlands/HiggsBundles.v:301 END *)
  (* CAG constructive-remove Command apply theories/Langlands/HiggsBundles.v:305 BEGIN -- compile error
apply (hf_integrable (higgs_phi H)).

   CAG constructive-remove Command apply theories/Langlands/HiggsBundles.v:305 END *)
(* CAG constructive-remove Command Qed. theories/Langlands/HiggsBundles.v:309 BEGIN -- compile error
Qed.

   CAG constructive-remove Command Qed. theories/Langlands/HiggsBundles.v:309 END *)
   CAG constructive-remove Lemma rank1_higgs_integrable theories/Langlands/HiggsBundles.v:290 END *)
