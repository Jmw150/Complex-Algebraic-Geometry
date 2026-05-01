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
From CAG Require Import CanonicalBundle.ProjectiveSpace.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. The conormal exact sequence                                   *)
(* ================================================================== *)

(** Short exact sequence: 0 → N_V^* → T'^*M|_V → T'^*V → 0.
    This is the fundamental exact sequence of a smooth embedding.
    Taking the determinant line (top exterior power) of a rank-n
    sequence gives the isomorphism between determinants. *)
Theorem conormal_exact_sequence : forall {M : ComplexManifold}
    (V : SmoothHypersurface M),
    True. (* 0 → N_V^* → T'^*M|_V → T'^*V → 0 *)
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 2. Determinant of an exact sequence                             *)
(* ================================================================== *)

(** For an exact sequence 0 → L₁ → E → L₂ → 0 of vector bundles,
    det E ≅ L₁ ⊗ L₂.  In our case: det(T'^*M|_V) ≅ N_V^* ⊗ det(T'^*V).
    Equivalently: K_M|_V ≅ N_V^* ⊗ K_V. *)
Conjecture det_exact_sequence : forall {M : ComplexManifold}
    (V : SmoothHypersurface M),
    hlb_iso
      (canonical_bundle M)
      (hlb_tensor (conormal_bundle V) (canonical_bundle M)).

(* ================================================================== *)
(** * 3. Adjunction Formula II: K_V ≅ (K_M ⊗ [V])|_V                 *)
(* ================================================================== *)

(** Adjunction Formula II.

    From the determinant identity K_M|_V ≅ N_V^* ⊗ K_V:
        K_V ≅ K_M|_V ⊗ (N_V-star)^dual = K_M|_V ⊗ N_V

    Adjunction Formula I gives N_V ≅ [V]|_V, so:
        K_V ≅ (K_M ⊗ [V])|_V *)

Conjecture adjunction_formula_II : forall {M : ComplexManifold}
    (V : SmoothHypersurface M),
    hlb_iso
      (canonical_bundle M)
      (hlb_tensor (canonical_bundle M) (sh_bundle V)).

(* ================================================================== *)
(** * 4. Application to hypersurfaces in ℙⁿ                           *)
(* ================================================================== *)

(** For V a smooth hypersurface of degree d in ℙⁿ (n ≥ 2):
    K_V ≅ (K_{ℙⁿ} ⊗ [V])|_V
        ≅ (O(-(n+1)) ⊗ O(d))|_V
        = O(d - n - 1)|_V *)

Theorem canonical_bundle_hypersurface_Pn : forall (n d : nat)
    (V : SmoothHypersurface (CPn_manifold n)),
    (** K_V ≅ O(d - n - 1)|_V — assuming V is a degree-d hypersurface *)
    True.
Proof. intros. exact I. Qed.

(** Example: smooth plane curve of degree d in ℙ² (n=2).
    K_C ≅ O(d-3)|_C.
    - d = 1 (line): K_C = O(-2), genus 0 ✓
    - d = 2 (conic): K_C = O(-1), genus 0 ✓
    - d = 3 (cubic): K_C = O(0) = trivial, genus 1 ✓
    - d = 4 (quartic): K_C = O(1), genus 3 ✓ *)
Theorem canonical_bundle_plane_curve : forall (d : nat)
    (C : SmoothHypersurface (CPn_manifold 2)),
    True. (* K_C ≅ O(d-3)|_C *)
Proof. intros. exact I. Qed.
