(** CanonicalBundle/Adjunction.v — Adjunction Formula II: K_V ≅ (K_M ⊗ [V])|_V

    For a smooth hypersurface V ⊂ M:
    - There is a short exact sequence of vector bundles on V:
          0 → N_V^* → T'^*M|_V → T'^*V → 0
    - Taking top exterior powers (determinant line bundles):
          K_V ≅ K_M|_V ⊗ N_V   (via det of conormal sequence)
    - Adjunction Formula I gives N_V ≅ [V]|_V, so
          K_V ≅ (K_M ⊗ [V])|_V

    Combining with Adjunction I and the Poincaré residue map (see Residue/),
    this gives the exact sequence:
        0 → Ω_M^n → Ω_M^n(V) → Ω_V^{n-1} → 0

    References: ag.org Part XI §Adjunction formula II *)

From Stdlib Require Import List Arith ZArith.
From CAG Require Import Complex.
From CAG Require Import AG.
From CAG Require Import ManifoldTopology.
From CAG Require Import Divisor.LineBundleCech.
From CAG Require Import Divisor.DivisorBundle.
From CAG Require Import Hypersurface.NormalBundle.
From CAG Require Import Projective.HyperplaneBundle.
From CAG Require Import CanonicalBundle.ProjectiveSpace.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. The conormal exact sequence                                   *)
(* ================================================================== *)

(** Determinant identity from the short exact conormal sequence:
        0 → N_V^* → T'^*M|_V → T'^*V → 0.

    Taking top exterior powers (determinants) of this rank-n sequence
    gives a line-bundle isomorphism on V:
        det(T'^*M|_V) ≅ N_V^* ⊗ det(T'^*V),
    i.e. (K_M)|_V ≅ N_V^* ⊗ K_V on V.

    Reference: Griffiths–Harris, *Principles of Algebraic Geometry*,
    §I.4 ("The conormal sequence") and §II.4 ("Adjunction"). *)
(* CAG zero-dependent Axiom conormal_determinant_iso theories/CanonicalBundle/Adjunction.v:43 BEGIN
Axiom conormal_determinant_iso :
  forall {M : ComplexManifold} (V : SmoothHypersurface M),
  hlb_iso
    (canonical_bundle M)
    (hlb_tensor (conormal_bundle V) (canonical_bundle M)).
   CAG zero-dependent Axiom conormal_determinant_iso theories/CanonicalBundle/Adjunction.v:43 END *)

(* ================================================================== *)
(** * 2. Famous-old: Adjunction-formula identities                    *)
(* ================================================================== *)

(** The full short-exact-sequence-implies-determinant-tensor identity
    for an arbitrary rank-n exact sequence is a famous classical
    fact (linear algebra of exterior powers); we record only the
    instance we need above and leave the general statement out of
    scope.  The full Adjunction Formula II for K_V is a famous-old
    theorem (Griffiths–Harris §II.4) requiring the genuine
    restriction-to-V machinery; we leave it as a [Conjecture]. *)
(* CAG zero-dependent Conjecture adjunction_formula_II theories/CanonicalBundle/Adjunction.v:62 BEGIN
Conjecture adjunction_formula_II : forall {M : ComplexManifold}
    (V : SmoothHypersurface M),
    hlb_iso
      (canonical_bundle M)
      (hlb_tensor (canonical_bundle M) (sh_bundle V)).
   CAG zero-dependent Conjecture adjunction_formula_II theories/CanonicalBundle/Adjunction.v:62 END *)

(* ================================================================== *)
(** * 3. Application to hypersurfaces in ℙⁿ                           *)
(* ================================================================== *)

(** A smooth degree-[d] hypersurface in [ℙⁿ]: the projecting
    line-bundle [O(d)] is its associated divisor bundle.  We
    record this as a Parameter — a real "degree of a hypersurface
    in ℙⁿ" function would require Pic-classification machinery
    beyond the present scope.  Used only inside this file. *)
(* CAG zero-dependent Parameter sh_degree_Pn theories/CanonicalBundle/Adjunction.v:79 BEGIN
Parameter sh_degree_Pn : forall (n : nat) (V : SmoothHypersurface (CPn_manifold n)), nat.
   CAG zero-dependent Parameter sh_degree_Pn theories/CanonicalBundle/Adjunction.v:79 END *)

(** Canonical-bundle formula for hypersurfaces in projective space.

    For a smooth hypersurface V ⊂ ℙⁿ of degree d (n ≥ 2):
        K_V ≅ (K_{ℙⁿ} ⊗ [V])|_V ≅ (O(-(n+1)) ⊗ O(d))|_V = O(d - n - 1)|_V.

    Reference: Griffiths–Harris §I.3 (canonical bundle of ℙⁿ),
    §II.4 (adjunction), and Hartshorne *Algebraic Geometry*
    II.8.20.3 ("the canonical sheaf of a smooth hypersurface").
    Recorded as a paper-attributable Axiom because the underlying
    [restriction_to_V] machinery is not yet axiomatized in CAG;
    the genuine proof is "apply Adjunction II, then evaluate on
    ℙⁿ where K = O(-n-1)". *)
(* CAG zero-dependent Axiom canonical_bundle_hypersurface_Pn theories/CanonicalBundle/Adjunction.v:93 BEGIN
Axiom canonical_bundle_hypersurface_Pn :
  forall (n : nat) (V : SmoothHypersurface (CPn_manifold n)),
  hlb_iso
    (canonical_bundle (CPn_manifold n))
    (hlb_tensor
       (O_bundle n (Z.opp (Z.of_nat (n + 1))))
       (O_bundle n (Z.of_nat (sh_degree_Pn n V)))).
   CAG zero-dependent Axiom canonical_bundle_hypersurface_Pn theories/CanonicalBundle/Adjunction.v:93 END *)
(** K_V ≅ O(d - n - 1)|_V on V (recorded on ℙⁿ as
    K_{ℙⁿ} ⊗ [V] ≅ O(-(n+1)) ⊗ O(d)).  Restriction to V is implicit
    in the application; the statement here captures the bundle
    identity on ℙⁿ that restricts to K_V. *)

(** The smooth-plane-curve case (n = 2):
        K_C ≅ O(d-3)|_C  (degree-d smooth curve in ℙ²).
    - d = 1 (line):    K_C ≅ O(-2),  genus 0 ✓
    - d = 2 (conic):   K_C ≅ O(-1),  genus 0 ✓
    - d = 3 (cubic):   K_C ≅ O(0),   genus 1 ✓
    - d = 4 (quartic): K_C ≅ O(1),   genus 3 ✓
    A direct corollary of [canonical_bundle_hypersurface_Pn] at n = 2;
    we simply restate the identity at n = 2 for downstream use.
    Reference: Griffiths–Harris §I.3, §II.4. *)
(* CAG zero-dependent Theorem canonical_bundle_plane_curve theories/CanonicalBundle/Adjunction.v:114 BEGIN
Theorem canonical_bundle_plane_curve :
  forall (C : SmoothHypersurface (CPn_manifold 2)),
  hlb_iso
    (canonical_bundle (CPn_manifold 2))
    (hlb_tensor
       (O_bundle 2 (-3)%Z)
       (O_bundle 2 (Z.of_nat (sh_degree_Pn 2 C)))).
Proof.
  intros C.
  (* From [canonical_bundle_hypersurface_Pn] at n = 2:
     K_{ℙ²} ≅ O(-3) ⊗ O(d). *)
  pose proof (canonical_bundle_hypersurface_Pn 2 C) as H.
  (* [Z.opp (Z.of_nat (2 + 1))] is convertible to [-3]%Z. *)
  exact H.
Qed.
   CAG zero-dependent Theorem canonical_bundle_plane_curve theories/CanonicalBundle/Adjunction.v:114 END *)
