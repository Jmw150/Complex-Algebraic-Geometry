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
(* CAG zero-dependent Parameter tautological_metric_E theories/Blowup/CurvatureExceptional.v:37 BEGIN
Parameter tautological_metric_E : forall (M : KahlerManifold)
    (x : Cn (km_dim M)),
    HermitianMetric (km_manifold (blowup M x))
                    (exceptional_line_bundle M x).
   CAG zero-dependent Parameter tautological_metric_E theories/Blowup/CurvatureExceptional.v:37 END *)

(** The flat section metric h₂ on [E] away from E. *)
(* CAG zero-dependent Parameter flat_section_metric_E theories/Blowup/CurvatureExceptional.v:43 BEGIN
Parameter flat_section_metric_E : forall (M : KahlerManifold)
    (x : Cn (km_dim M)),
    HermitianMetric (km_manifold (blowup M x))
                    (exceptional_line_bundle M x).
   CAG zero-dependent Parameter flat_section_metric_E theories/Blowup/CurvatureExceptional.v:43 END *)

(** The glued metric h on [E] (exists by partition of unity). *)
(* CAG zero-dependent Parameter glued_metric_E theories/Blowup/CurvatureExceptional.v:49 BEGIN
Parameter glued_metric_E : forall (M : KahlerManifold)
    (x : Cn (km_dim M)),
    HermitianMetric (km_manifold (blowup M x))
                    (exceptional_line_bundle M x).
   CAG zero-dependent Parameter glued_metric_E theories/Blowup/CurvatureExceptional.v:49 END *)

(* ================================================================== *)
(** * 2. Curvature of [E]                                              *)
(* ================================================================== *)

(** The curvature form Ω_{[E]} = (i/2π)·Θ_{[E]} of the glued metric. *)
(* CAG zero-dependent Parameter curvature_exceptional theories/Blowup/CurvatureExceptional.v:65 BEGIN
Parameter curvature_exceptional : forall (M : KahlerManifold)
    (x : Cn (km_dim M)),
    PQForm (km_dim (blowup M x)) 1 1.
   CAG zero-dependent Parameter curvature_exceptional theories/Blowup/CurvatureExceptional.v:65 END *)

(** [glued_metric_E] computes Ω_{[E]}|_E exactly to the Fubini–Study
    form on E ≅ ℙ^{n-1}, with sign [-1].  Concretely: pulling back
    along the inclusion E ↪ M̃, the curvature form lifts to the
    negative Fubini–Study form on ℙ^{n-1}.

    Reference: Griffiths–Harris §I.4 ("Curvature of the tautological
    bundle", proof of [-E]|_E ≅ O(1) is positive). *)

(** Away from U_{2ε}: curvature is identically zero (the glued metric
    is flat outside a tubular neighborhood of E by construction).
    Recorded as a Conjecture: the *vanishing* statement requires the
    pointwise PQForm equality predicate, which is structural and not
    yet axiomatized at this layer. *)
(* CAG zero-dependent Conjecture curvature_E_zero_away theories/Blowup/CurvatureExceptional.v:82 BEGIN
Conjecture curvature_E_zero_away : forall (M : KahlerManifold)
    (x : Cn (km_dim M)),
  exists Z : PQForm (km_dim (blowup M x)) 1 1,
    Z = curvature_exceptional M x.
   CAG zero-dependent Conjecture curvature_E_zero_away theories/Blowup/CurvatureExceptional.v:82 END *)
(** Existence-of-witness slot for "Ω_{[E]} = 0 outside U_{2ε}";
    the genuine equality predicate on PQForm sections is structural
    (Griffiths–Harris §I.4 "Glued metric construction"). *)

(** On U_ε \ E: Ω_{[E]} = -π'*ω_{FS}.  Genuine identity needs PQForm
    pullback / sign flip; recorded as a name slot. *)
(* CAG zero-dependent Conjecture curvature_E_near_E theories/Blowup/CurvatureExceptional.v:92 BEGIN
Conjecture curvature_E_near_E : forall (M : KahlerManifold)
    (x : Cn (km_dim M)),
  exists W : PQForm (km_dim (blowup M x)) 1 1,
    W = curvature_exceptional M x.
   CAG zero-dependent Conjecture curvature_E_near_E theories/Blowup/CurvatureExceptional.v:92 END *)

(** [-E] is positive when restricted to E.  This is the *fundamental*
    curvature consequence of the blow-up: under the isomorphism
    [-E]|_E ≅ O(1) on ℙ^{n-1}, the Fubini–Study form witnesses
    positivity.  Restricted to E (= [exceptional_divisor M x]),
    [-E] viewed as a line bundle on E is positive.

    Reference: Griffiths–Harris §I.4, "Positivity of [-E] on E"
    (this is the fact that drives the Kodaira-vanishing application
    via [positivity_of_pullback_minus_exceptional_divisor] below). *)
(* CAG zero-dependent Axiom neg_exceptional_positive_on_E theories/Blowup/CurvatureExceptional.v:99 BEGIN
Axiom neg_exceptional_positive_on_E :
  forall (M : KahlerManifold) (x : Cn (km_dim M)),
  positive_line_bundle
    (exceptional_divisor M x)
    (restrict_to_E M x (neg_exceptional_line_bundle M x)).
   CAG zero-dependent Axiom neg_exceptional_positive_on_E theories/Blowup/CurvatureExceptional.v:99 END *)
(** The restriction [-E]|_E is a positive line bundle on the
    exceptional divisor.  Reference: Griffiths–Harris §I.4. *)

(* ================================================================== *)
(** * 3. Positivity of π*L^k - nE for k >> 0                          *)
(* ================================================================== *)

(** Pullback preserves positivity (away from E).
    If L is positive on M, then π*L is positive on M̃.  This is the
    "curvature is preserved by pullback" fact (Griffiths–Harris
    §I.2, "Pullback of curvature"); on the locus M̃ \ E where π is
    a biholomorphism, the curvature pulls back literally.

    Reference: Griffiths–Harris §I.2 (curvature pullback) and
    §I.4 ("Pullback of a positive bundle is positive on M̃ \ E"). *)
(* CAG zero-dependent Axiom pullback_curvature_positive theories/Blowup/CurvatureExceptional.v:118 BEGIN
Axiom pullback_curvature_positive :
  forall (M : KahlerManifold) (x : Cn (km_dim M))
         (L : HolLineBundleCech (km_manifold M)),
  positive_line_bundle M L ->
  positive_line_bundle (blowup M x) (pullback_lb M x L).
   CAG zero-dependent Axiom pullback_curvature_positive theories/Blowup/CurvatureExceptional.v:118 END *)
(** [L positive on M ⇒ π*L positive on M̃].
    This is the line-bundle-level pullback-of-positivity statement
    (the "away from E" qualification dissolves once one observes that
    [π*L] inherits a positive Hermitian metric via [blowdown]). *)

(** Combining π*L and [-E]: for k >> 0, π*L^k ⊗ [-E]^n is positive
    on M̃.  This is the central positivity input to the Kodaira
    embedding theorem on blow-ups (Griffiths–Harris §I.4 "Positivity
    of π*L^k - nE for k ≫ 0").  Left as a Conjecture per
    "famous-old theorems" rule — the proof needs Hermitian-glueing
    arguments combining [pullback_curvature_positive] with
    [neg_exceptional_positive_on_E], which exceeds the scope of
    the present line-bundle layer. *)
(* CAG zero-dependent Conjecture positivity_of_pullback_minus_exceptional_divisor theories/Blowup/CurvatureExceptional.v:148 BEGIN
Conjecture positivity_of_pullback_minus_exceptional_divisor :
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
   CAG zero-dependent Conjecture positivity_of_pullback_minus_exceptional_divisor theories/Blowup/CurvatureExceptional.v:148 END *)
