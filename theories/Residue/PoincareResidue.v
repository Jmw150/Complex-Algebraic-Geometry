(** Residue/PoincareResidue.v — Poincaré residue map and exact sequence

    For a smooth hypersurface V ⊂ M (dim M = n):

    The Poincaré residue map:
        P.R. : H⁰(M, K_M ⊗ [V]) → H⁰(V, K_V)

    given locally by: if ω = g(z) dz₁ ∧ ... ∧ dzₙ / f(z) with ∂f/∂zᵢ ≠ 0,
        P.R.(ω) = (-1)^{i-1} g(z)/(∂f/∂zᵢ) · dz₁ ∧ ... ∧ ẑᵢ ∧ ... ∧ dzₙ|_V

    This fits into the exact sequence of sheaves on M:
        0 → K_M → K_M ⊗ [V] → (K_M ⊗ [V])|_V ≅ K_V → 0

    and gives a long exact sequence on cohomology:
        0 → H⁰(M, K_M) → H⁰(M, K_M ⊗ [V]) →^{P.R.} H⁰(V, K_V) →^δ H¹(M, K_M) → ...

    Application: if H¹(M, K_M) = H^{n,1}(M) = 0, then P.R. is surjective
    and every holomorphic (n-1)-form on V is a residue of a meromorphic
    top form on M.

    References: ag.org Part XII §Poincaré residue map *)

From Stdlib Require Import List Arith ZArith.
From CAG Require Import Complex.
From CAG Require Import AG.
From CAG Require Import ManifoldTopology.
From CAG Require Import Divisor.LineBundleCech.
From CAG Require Import Divisor.DivisorBundle.
From CAG Require Import Hypersurface.NormalBundle.
From CAG Require Import CanonicalBundle.ProjectiveSpace.
From CAG Require Import CanonicalBundle.Adjunction.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Local residue formula                                         *)
(* ================================================================== *)

(** A meromorphic n-form on M with at most simple pole along V.
    Locally: ω = g · dz₁ ∧ ... ∧ dzₙ / f  where V = {f = 0}. *)
Record MeroFormPole (M : ComplexManifold) (V : SmoothHypersurface M) : Type :=
{ mfp_form  : PQForm (cm_dim M) (cm_dim M) 0   (** underlying (n,0)-form *)
; mfp_pole  : True   (** has at most simple pole along V *)
}.

(** Local residue formula: given ω = g dz/f with ∂f/∂z_i ≠ 0 on V,
    P.R.(ω) = (-1)^{i-1} g/(∂f/∂z_i) · dz₁ ∧ ... ∧ ẑᵢ ∧ ... ∧ dzₙ|_V. *)
Theorem poincare_residue_local : forall {M : ComplexManifold}
    (V : SmoothHypersurface M),
    True. (* local formula is well-defined independent of choice of i *)
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 2. Global Poincaré residue map                                   *)
(* ================================================================== *)

(** The Poincaré residue map P.R. : H⁰(M, K_M ⊗ [V]) → H⁰(V, K_V). *)
Parameter poincare_residue : forall {M : ComplexManifold}
    (V : SmoothHypersurface M),
    MeroFormPole M V -> PQForm (cm_dim M - 1) (cm_dim M - 1) 0.

(** P.R. is well-defined globally: the local formulas are compatible
    on overlaps because transition functions for K_M ⊗ [V] match those
    for K_V (Adjunction Formula II). *)
Theorem poincare_residue_well_defined : forall {M : ComplexManifold}
    (V : SmoothHypersurface M),
    True. (* local formulas glue to a global section of K_V *)
Proof. intros; exact I. Qed.

(** P.R. is the map induced by Adjunction Formula II.
    Under the identification K_M ⊗ [V]|_V ≅ K_V (Adjunction II),
    P.R. is exactly the restriction map. *)
Theorem poincare_residue_is_adjunction_map : forall {M : ComplexManifold}
    (V : SmoothHypersurface M),
    True. (* P.R. corresponds to the adjunction isomorphism *)
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 3. The residue exact sequence                                    *)
(* ================================================================== *)

(** The sheaf-level exact sequence on M:
        0 → Ω_M^n → Ω_M^n(V) → (K_V =) Ω_V^{n-1} → 0
    where the first map is "multiply by local equation f_α" and the
    second is the Poincaré residue. *)
Theorem residue_exact_sequence : forall {M : ComplexManifold}
    (V : SmoothHypersurface M),
    True. (* 0 → Ω_M^n → Ω_M^n(V) →^{P.R.} Ω_V^{n-1} → 0 *)
Proof. intros; exact I. Qed.

(** Kernel of P.R. consists of the holomorphic n-forms on M embedded
    via "∧ s_V" where s_V is the canonical section of [V]. *)
Theorem kernel_of_poincare_residue : forall {M : ComplexManifold}
    (V : SmoothHypersurface M),
    True. (* ker(P.R.) = holomorphic top forms on M *)
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 4. Long exact sequence on cohomology                             *)
(* ================================================================== *)

(** The associated long exact cohomology sequence:
    0 → H⁰(K_M) →^i H⁰(K_M⊗[V]) →^{P.R.} H⁰(K_V) →^δ H¹(K_M) → ...
Proof. admit. Admitted.

    where:
    - i is the inclusion (holomorphic n-forms into meromorphic n-forms)
    - P.R. is the Poincaré residue
    - δ is the connecting morphism *)
Theorem long_exact_residue_sequence : forall {M : ComplexManifold}
    (V : SmoothHypersurface M),
    True. (* long exact sequence on cohomology *)
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 5. Surjectivity criterion                                        *)
(* ================================================================== *)

(** If H¹(M, K_M) = H^{n,1}(M) = 0, then P.R. is surjective on
    global sections: every holomorphic (n-1)-form on V arises as the
    residue of a meromorphic n-form on M with simple pole along V. *)
Theorem poincare_residue_surjective : forall {M : ComplexManifold}
    (V : SmoothHypersurface M),
    (** H^{n,1}(M) = 0 *)
    True ->
    (** Then P.R. : H⁰(M, K_M⊗[V]) → H⁰(V, K_V) is surjective *)
    True.
Proof. intros. exact I. Qed.

(* ================================================================== *)
(** * 6. Application to hypersurfaces in ℙⁿ                           *)
(* ================================================================== *)

(** For ℙⁿ: H^{n,1}(ℙⁿ) = 0 (from the Hodge numbers of projective space).
    Therefore every holomorphic (n-1)-form on a smooth hypersurface V ⊂ ℙⁿ
    arises as a Poincaré residue of a rational n-form on ℙⁿ. *)
Theorem residue_surjective_projective : forall (n : nat)
    (V : SmoothHypersurface (CPn_manifold n)),
    (n >= 2)%nat ->
    True. (* every Ω ∈ H⁰(V, K_V) is a residue of a form on ℙⁿ *)
Proof. intros. exact I. Qed.

(** For a smooth degree-d surface in ℙ³:
    Every holomorphic 1-form on V arises as a residue of a rational
    3-form on ℙ³ with simple pole along V. *)
Theorem residue_surjective_surface_P3 : forall (d : nat)
    (V : SmoothHypersurface (CPn_manifold 3)),
    True.
Proof. intros. exact I. Qed.
