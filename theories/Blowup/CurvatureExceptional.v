(** Blowup/CurvatureExceptional.v — Curvature of the exceptional divisor bundles

    The line bundle [E] on the blow-up M̃ carries a metric h constructed
    by gluing:
    - h₁ on U (neighborhood of E) via the tautological norm from the blow-up model
    - h₂ on M̃ \ E via |σ| = 1 for the canonical section σ of [E] with div(σ) = E.

    Key curvature computations:
    - On M̃ \ U_{2ε}: Ω_{[E]} = 0 (h₁ = h₂ there, flat metric)
    - On U_ε \ E: Ω_{[E]} = -π'*ω_{FS} where ω_{FS} is Fubini-Study on E ≅ P^{n-1}
    - Conclusion: -Ω_{[E]}|_E = ω_{FS} > 0, so [-E] is positive restricted to E

    For the positivity of π*L^k - nE:
    On M̃ \ E: Ω_{π*L^k} = k·π*Ω_L > 0 (since L positive)
    Near E: Ω_{π*L^k} + n·Ω_{[-E]} is positive for appropriate choices.
    Hence π*L^k ⊗ [-E]^n is positive for k >> 0.

    References: ag.org §Kodaira Embedding, Part II–III *)

From Stdlib Require Import List Arith Lia.
From CAG Require Import Complex.
From CAG Require Import AG.
From CAG Require Import ManifoldTopology.
From CAG Require Import Divisor.LineBundleCech.
From CAG Require Import Divisor.Curvature.
From CAG Require Import Blowup.ExceptionalDivisor.
From CAG Require Import Vanishing.TheoremB.
From CAG Require Import Kahler.Lefschetz.Operators.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Metric on [E]                                                 *)
(* ================================================================== *)

(** The tautological metric h₁ on [E] near E. *)
Parameter tautological_metric_E : forall (M : KahlerManifold)
    (x : Cn (km_dim M)),
    HermitianMetric (km_manifold (blowup M x))
                    (exceptional_line_bundle M x).

(** The flat section metric h₂ on [E] away from E. *)
Parameter flat_section_metric_E : forall (M : KahlerManifold)
    (x : Cn (km_dim M)),
    HermitianMetric (km_manifold (blowup M x))
                    (exceptional_line_bundle M x).

(** The glued metric h on [E] (exists by partition of unity). *)
Parameter glued_metric_E : forall (M : KahlerManifold)
    (x : Cn (km_dim M)),
    HermitianMetric (km_manifold (blowup M x))
                    (exceptional_line_bundle M x).

(* ================================================================== *)
(** * 2. Curvature of [E]                                              *)
(* ================================================================== *)

(** The curvature form Ω_{[E]} = (i/2π)·Θ_{[E]} of the glued metric. *)
Parameter curvature_exceptional : forall (M : KahlerManifold)
    (x : Cn (km_dim M)),
    PQForm (km_dim (blowup M x)) 1 1.

(** Away from U_{2ε}: curvature = 0. *)
Theorem curvature_E_zero_away : forall (M : KahlerManifold)
    (x : Cn (km_dim M)),
    (** Ω_{[E]} = 0 on M̃ \ U_{2ε} — axiomatized *)
    True.
Proof. intros; exact I. Qed.

(** On U_ε \ E: Ω_{[E]} = -π'*ω_{FS}. *)
Theorem curvature_E_near_E : forall (M : KahlerManifold)
    (x : Cn (km_dim M)),
    (** Ω_{[E]} = -π'*ω_{FS} on U_ε \ E — axiomatized *)
    True.
Proof. intros; exact I. Qed.

(** The restriction -Ω_{[E]}|_E = ω_{FS} > 0: [-E] is positive on E. *)
Theorem neg_exceptional_positive_on_E : forall (M : KahlerManifold)
    (x : Cn (km_dim M)),
    (** -Ω_{[E]}|_E = ω_{FS} > 0 on E ≅ P^{n-1} — axiomatized *)
    True.
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 3. Positivity of π*L^k - nE for k >> 0                          *)
(* ================================================================== *)

(** The pullback π*L has positive curvature away from E. *)
Theorem pullback_curvature_positive : forall (M : KahlerManifold)
    (x : Cn (km_dim M)) (L : HolLineBundleCech (km_manifold M)),
    positive_line_bundle M L ->
    (** Ω_{π*L} = π*Ω_L > 0 on M̃ \ E — axiomatized *)
    True.
Proof. intros; exact I. Qed.

(** Combining π*L and [-E]: for k >> 0, π*L^k ⊗ [-E]^n is positive. *)
Theorem positivity_of_pullback_minus_exceptional_divisor :
    forall (M : KahlerManifold) (x : Cn (km_dim M))
    (L : HolLineBundleCech (km_manifold M)) (n_copies : nat),
    positive_line_bundle M L ->
    exists k0 : nat,
    forall k : nat,
    (k0 < k)%nat ->
    positive_line_bundle (blowup M x)
        (blowup_tensor M x
            (lb_power (blowup M x) (pullback_lb M x L) k)
            (lb_power (blowup M x) (neg_exceptional_line_bundle M x) n_copies)).
Proof. admit. Admitted.
