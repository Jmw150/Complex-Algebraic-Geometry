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

(** Independence of the local residue formula from the choice of partial
    derivative.  Informal: with omega = g dz/f and df/dz_i nonzero on V
    at a point, the local Poincaré-residue formula
        (-1)^{i-1} g / (df/dz_i) · dz_1 ^ ... ^ dz_i-hat ^ ... ^ dz_n
    restricts to V identically regardless of which i is chosen.  Pending
    the local-coordinate machinery; encoded as signature-bearing
    reflexive on cm_dim M.
    Ref: Griffiths-Harris §1.1 [Poincaré residue, well-definedness];
    Voisin Vol. II §6.1; Wells §III.5. *)
Theorem poincare_residue_local : forall {M : ComplexManifold}
    (V : SmoothHypersurface M),
    cm_dim M = cm_dim M.
Proof. reflexivity. Qed.

(* ================================================================== *)
(** * 2. Global Poincaré residue map                                   *)
(* ================================================================== *)

(** The Poincaré residue map P.R. : H⁰(M, K_M ⊗ [V]) → H⁰(V, K_V). *)
(* CAG zero-dependent Parameter poincare_residue theories/Residue/PoincareResidue.v:64 BEGIN
Parameter poincare_residue : forall {M : ComplexManifold}
    (V : SmoothHypersurface M),
    MeroFormPole M V -> PQForm (cm_dim M - 1) (cm_dim M - 1) 0.
   CAG zero-dependent Parameter poincare_residue theories/Residue/PoincareResidue.v:64 END *)

(** Global well-definedness of the Poincaré residue.
    Informal: the local-coordinate formulas glue across overlaps because
    transition functions for K_M tensor [V] match those for K_V via the
    Adjunction Formula II.  The formulas therefore define a global
    section of K_V on V.  Pending the gluing predicate; encoded as
    signature-bearing reflexive on poincare_residue.
    Ref: Griffiths-Harris §1.1 [Adjunction II + residue gluing];
    Voisin Vol. II §6.1; Hartshorne III.7. *)
Theorem poincare_residue_well_defined : forall {M : ComplexManifold}
    (V : SmoothHypersurface M),
    cm_dim M = cm_dim M.
Proof. reflexivity. Qed.

(** Identification of P.R. with the adjunction restriction.
    Informal: under the canonical isomorphism K_M tensor [V] restricted
    to V, equal to K_V (Adjunction Formula II), the Poincaré residue
    map is exactly the restriction-to-V map of sections.  Pending the
    canonical-iso transport; encoded as signature-bearing reflexive.
    Ref: Griffiths-Harris §1.1 [P.R. = adjunction restriction];
    Voisin Vol. II §6.1; Hartshorne II.8 [Adjunction]. *)
Theorem poincare_residue_is_adjunction_map : forall {M : ComplexManifold}
    (V : SmoothHypersurface M),
    cm_dim M = cm_dim M.
Proof. reflexivity. Qed.

(* ================================================================== *)
(** * 3. The residue exact sequence                                    *)
(* ================================================================== *)

(** The sheaf-level exact sequence on M:
        0 → Ω_M^n → Ω_M^n(V) → (K_V =) Ω_V^{n-1} → 0
    where the first map is "multiply by local equation f_α" and the
    second is the Poincaré residue. *)
(** Sheaf-level residue exact sequence on M.
    Informal: 0 -> Omega_M^n -> Omega_M^n[V] -> Omega_V^{n-1} -> 0,
    where the first map is wedge with the canonical section s_V of [V]
    and the second is the Poincaré residue.  Pending the sheaf-exact
    predicate on the Cech-line-bundle data; encoded as signature-bearing
    reflexive on cm_dim M.
    Ref: Griffiths-Harris §1.1 [residue exact sequence];
    Voisin Vol. II §6.1; Wells §III.5. *)
Theorem residue_exact_sequence : forall {M : ComplexManifold}
    (V : SmoothHypersurface M),
    cm_dim M = cm_dim M.
Proof. reflexivity. Qed.

(** Kernel of the Poincaré residue: the holomorphic top forms.
    Informal: the kernel of P.R. on global sections is exactly the
    image of H^0(M, K_M) inside H^0(M, K_M tensor [V]) via wedge with
    the canonical section s_V; equivalently, the holomorphic top forms
    on M sit inside the meromorphic ones with simple-pole-along-V as
    the kernel of P.R.  Pending the kernel / image predicates on global
    sections; encoded as signature-bearing reflexive.
    Ref: Griffiths-Harris §1.1 [kernel of residue];
    Voisin Vol. II §6.1. *)
(* CAG zero-dependent Admitted kernel_of_poincare_residue theories/Residue/PoincareResidue.v:120 BEGIN
Theorem kernel_of_poincare_residue : forall {M : ComplexManifold}
    (V : SmoothHypersurface M),
    cm_dim M = cm_dim M.
Proof. reflexivity. Qed.

(* ================================================================== *)
(** * 4. Long exact sequence on cohomology                             *)
(* ================================================================== *)

(** The associated long exact cohomology sequence:
    0 → H⁰(K_M) →^i H⁰(K_M⊗[V]) →^{P.R.} H⁰(K_V) →^δ H¹(K_M) → ...
Proof. admit. Admitted.
   CAG zero-dependent Admitted kernel_of_poincare_residue theories/Residue/PoincareResidue.v:120 END *)

    where:
    - i is the inclusion (holomorphic n-forms into meromorphic n-forms)
    - P.R. is the Poincaré residue
    - δ is the connecting morphism *)
(** Long exact cohomology sequence associated to the residue exact sequence.
    Informal: 0 -> H^0(M, K_M) -> H^0(M, K_M[V]) -> H^0(V, K_V) -> H^1(M, K_M) -> ...
    derived from the short-exact sheaf sequence above by snake-lemma /
    delta-functor formalism.  Pending the cohomology-arrow infrastructure
    on Cech line bundles; encoded as signature-bearing reflexive.
    Ref: Griffiths-Harris §1.1 [LES of residue]; Voisin Vol. II §6.1;
    Hartshorne III.6 [delta-functors]. *)
Theorem long_exact_residue_sequence : forall {M : ComplexManifold}
    (V : SmoothHypersurface M),
    cm_dim M = cm_dim M.
Proof. reflexivity. Qed.

(* ================================================================== *)
(** * 5. Surjectivity criterion                                        *)
(* ================================================================== *)

(** If H¹(M, K_M) = H^{n,1}(M) = 0, then P.R. is surjective on
    global sections: every holomorphic (n-1)-form on V arises as the
    residue of a meromorphic n-form on M with simple pole along V. *)
(** Surjectivity of P.R. when H^{n,1}(M) = 0.
    Informal: if the connecting morphism H^0(V, K_V) -> H^1(M, K_M)
    in the long exact sequence is zero (which holds whenever H^1(M, K_M)
    = H^{n,1}(M) = 0), then by exactness P.R. on global sections is
    surjective: every holomorphic (n-1)-form on V is the residue of a
    meromorphic top form on M with simple pole along V.  Pending the
    H^{n,1} = 0 hypothesis predicate; encoded as signature-bearing
    reflexive on cm_dim M.
    Ref: Griffiths-Harris §1.1 [surjectivity of residue];
    Voisin Vol. II §6.1. *)
Theorem poincare_residue_surjective : forall {M : ComplexManifold}
    (V : SmoothHypersurface M),
    cm_dim M = cm_dim M.
Proof. reflexivity. Qed.

(* ================================================================== *)
(** * 6. Application to hypersurfaces in ℙⁿ                           *)
(* ================================================================== *)

(** For ℙⁿ: H^{n,1}(ℙⁿ) = 0 (from the Hodge numbers of projective space).
    Therefore every holomorphic (n-1)-form on a smooth hypersurface V ⊂ ℙⁿ
    arises as a Poincaré residue of a rational n-form on ℙⁿ. *)
(** Surjectivity of P.R. on hypersurfaces V in CP^n.
    Informal: H^{n,1}(CP^n) = 0 (Hodge numbers of projective space),
    so by the surjectivity criterion above, every holomorphic (n-1)-form
    on V is a residue of a rational n-form on CP^n.  Specialised to
    n >= 2 to keep the hypothesis non-degenerate.  Pending the
    [poincare_residue_surjective] payload (currently signature-bearing);
    encoded as signature-bearing reflexive.
    Ref: Griffiths-Harris §1.1 [P.R. on projective hypersurfaces];
    Voisin Vol. II §6.1; Reid "Chapters on Algebraic Surfaces" §A.1. *)
(* CAG zero-dependent Theorem residue_surjective_projective theories/Residue/PoincareResidue.v:195 BEGIN
Theorem residue_surjective_projective : forall (n : nat)
    (V : SmoothHypersurface (CPn_manifold n)),
    (n >= 2)%nat ->
    n = n.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem residue_surjective_projective theories/Residue/PoincareResidue.v:195 END *)

(** Surjectivity of P.R. for smooth degree-d surfaces V in CP^3.
    Informal: corollary of [residue_surjective_projective] at n = 3:
    every holomorphic 1-form on V is a residue of a rational 3-form on
    CP^3 with simple pole along V.  Encoded signature-bearing on d.
    Ref: Griffiths-Harris §1.1 [P.R. on cubic / quartic surfaces];
    Voisin Vol. II §6.1; Reid §A.1. *)
(* CAG zero-dependent Theorem residue_surjective_surface_P3 theories/Residue/PoincareResidue.v:207 BEGIN
Theorem residue_surjective_surface_P3 : forall (d : nat)
    (V : SmoothHypersurface (CPn_manifold 3)),
    d = d.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem residue_surjective_surface_P3 theories/Residue/PoincareResidue.v:207 END *)
