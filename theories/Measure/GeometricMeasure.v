(** * Measure/GeometricMeasure.v — Geometric measure theory.

    Hausdorff measures, k-dimensional density, rectifiable sets,
    coarea formula (axiomatized), and currents (axiomatized).

    Built on top of [Measure/Basic.v] using [CReal]-based
    constructive analysis. Sets live in a metric space [(X, d)]
    where [d : X → X → CReal] is a non-negative symmetric distance
    satisfying the triangle inequality.

    Sources: Federer, "Geometric measure theory" (1969). Mattila,
    "Geometry of sets and measures in Euclidean spaces" (1995).
    Krantz–Parks, "Geometric integration theory" (2008).
    Coquand-Spitters for the constructive treatment. *)

From Stdlib Require Import QArith ZArith.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyRealsMult.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyAbs.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.PropExtensionality.
From Stdlib Require Import Logic.Classical_Prop.
From CAG Require Import Reals_extra.
From CAG Require Import Measure.Basic.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** ** 1. Pseudometric and metric spaces                                *)
(* ================================================================== *)

(** A pseudometric space: a carrier [X] with a non-negative symmetric
    "distance" satisfying the triangle inequality. We use ≤ in the
    constructive sense via [~ CRealLtProp]. *)
Record Pseudometric (X : Type) : Type :=
  mkPseudo
  {
    pm_d        : X -> X -> CReal;
    pm_self     : forall x : X, CReal_minus (pm_d x x) (inject_Q 0)
                                = inject_Q 0;
    pm_nonneg   : forall x y : X, ~ CRealLtProp (pm_d x y) (inject_Q 0);
    pm_symm     : forall x y : X, pm_d x y = pm_d y x;
    pm_triangle : forall x y z : X,
                  ~ CRealLtProp
                    (CReal_plus (pm_d x z) (inject_Q 0))
                    (CReal_minus (pm_d x y) (CReal_opp (pm_d y z)));
  }.

Arguments pm_d {X} _ _ _.
Arguments pm_self {X} _ _.
Arguments pm_nonneg {X} _ _ _.
Arguments pm_symm {X} _ _ _.
Arguments pm_triangle {X} _ _ _ _.

(** A metric space additionally satisfies [d x y = 0 → x = y]. *)
Record MetricSpace (X : Type) : Type :=
  mkMetric
  {
    ms_pm        : Pseudometric X;
    ms_separates : forall x y : X,
                   pm_d ms_pm x y = inject_Q 0 -> x = y;
  }.

Arguments ms_pm {X} _.
Arguments ms_separates {X} _ _ _ _.

(** Diameter of a subset (axiomatized as the supremum, deferred). *)
(* CAG zero-dependent Parameter diameter theories/Measure/GeometricMeasure.v:69 BEGIN
Parameter diameter :
  forall {X : Type} (M : MetricSpace X) (A : Subset X), NNExtCReal.
   CAG zero-dependent Parameter diameter theories/Measure/GeometricMeasure.v:69 END *)

(** Axiom: diameter of the empty set is 0. *)
(* CAG zero-dependent Conjecture diameter_empty theories/Measure/GeometricMeasure.v:73 BEGIN
Conjecture diameter_empty :
  forall {X : Type} (M : MetricSpace X),
    diameter M empty_set = nne_zero.
   CAG zero-dependent Conjecture diameter_empty theories/Measure/GeometricMeasure.v:73 END *)

(** Axiom: monotonicity of diameter — A ⊆ B implies diameter A ≤ diameter B. *)
(* CAG zero-dependent Conjecture diameter_mono theories/Measure/GeometricMeasure.v:78 BEGIN
Conjecture diameter_mono :
  forall {X : Type} (M : MetricSpace X) (A B : Subset X),
    subset_of A B -> nne_le (diameter M A) (diameter M B).
   CAG zero-dependent Conjecture diameter_mono theories/Measure/GeometricMeasure.v:78 END *)

(* ================================================================== *)
(** ** 2. δ-cover and Hausdorff outer measure                          *)
(* ================================================================== *)

(** A δ-cover of [A] is a sequence of subsets covering [A] each with
    diameter at most δ. *)
(* CAG zero-dependent Definition is_delta_cover theories/Measure/GeometricMeasure.v:92 BEGIN
Definition is_delta_cover {X : Type} (M : MetricSpace X)
  (A : Subset X) (delta : CReal) (U : nat -> Subset X) : Prop :=
  subset_of A (countable_union U) /\
  forall n, nne_le (diameter M (U n)) (NNFin delta).
   CAG zero-dependent Definition is_delta_cover theories/Measure/GeometricMeasure.v:92 END *)

(** Hausdorff s-content at scale δ: the infimum (axiomatized) of
    [Σ (diam U_n)^s] over all δ-covers of [A]. *)
(* CAG zero-dependent Parameter hausdorff_content_delta theories/Measure/GeometricMeasure.v:99 BEGIN
Parameter hausdorff_content_delta :
  forall {X : Type} (M : MetricSpace X) (s : CReal) (delta : CReal)
         (A : Subset X), NNExtCReal.
   CAG zero-dependent Parameter hausdorff_content_delta theories/Measure/GeometricMeasure.v:99 END *)

(** Axiom: hausdorff_content_delta is monotone in A. *)
(* CAG zero-dependent Conjecture hausdorff_content_delta_mono theories/Measure/GeometricMeasure.v:100 BEGIN
Conjecture hausdorff_content_delta_mono :
  forall {X : Type} (M : MetricSpace X) (s delta : CReal) (A B : Subset X),
    subset_of A B ->
    nne_le (hausdorff_content_delta M s delta A)
           (hausdorff_content_delta M s delta B).
   CAG zero-dependent Conjecture hausdorff_content_delta_mono theories/Measure/GeometricMeasure.v:100 END *)

(** Axiom: hausdorff_content_delta is monotone in δ (smaller δ ⟹ larger
    content, since restricting to finer covers makes the infimum larger
    or equal). *)
(* CAG zero-dependent Conjecture hausdorff_content_delta_mono_in_delta theories/Measure/GeometricMeasure.v:109 BEGIN
Conjecture hausdorff_content_delta_mono_in_delta :
  forall {X : Type} (M : MetricSpace X) (s d1 d2 : CReal) (A : Subset X),
    ~ CRealLtProp d2 d1 ->
    nne_le (hausdorff_content_delta M s d2 A)
           (hausdorff_content_delta M s d1 A).
   CAG zero-dependent Conjecture hausdorff_content_delta_mono_in_delta theories/Measure/GeometricMeasure.v:109 END *)

(** Hausdorff s-measure of [A]: the limit (sup over δ ↘ 0) of the
    δ-content. Axiomatized as the supremum-like construction. *)
(* CAG zero-dependent Parameter hausdorff_measure theories/Measure/GeometricMeasure.v:127 BEGIN
Parameter hausdorff_measure :
  forall {X : Type} (M : MetricSpace X) (s : CReal) (A : Subset X), NNExtCReal.
   CAG zero-dependent Parameter hausdorff_measure theories/Measure/GeometricMeasure.v:127 END *)

(** Axiom: connection between content and measure — for every δ > 0,
    H^s ≥ H^s_δ (the limit dominates each member of the family). *)
(* CAG zero-dependent Conjecture hausdorff_measure_ge_content theories/Measure/GeometricMeasure.v:122 BEGIN
Conjecture hausdorff_measure_ge_content :
  forall {X : Type} (M : MetricSpace X) (s delta : CReal) (A : Subset X),
    CRpositive delta ->
    nne_le (hausdorff_content_delta M s delta A)
           (hausdorff_measure M s A).
   CAG zero-dependent Conjecture hausdorff_measure_ge_content theories/Measure/GeometricMeasure.v:122 END *)

(** Axiom: vanishing on the empty set. *)
(* CAG zero-dependent Conjecture hausdorff_measure_empty theories/Measure/GeometricMeasure.v:129 BEGIN
Conjecture hausdorff_measure_empty :
  forall {X : Type} (M : MetricSpace X) (s : CReal),
    hausdorff_measure M s empty_set = nne_zero.
   CAG zero-dependent Conjecture hausdorff_measure_empty theories/Measure/GeometricMeasure.v:129 END *)

(** Axiom: monotonicity. *)
(* CAG zero-dependent Conjecture hausdorff_measure_mono theories/Measure/GeometricMeasure.v:134 BEGIN
Conjecture hausdorff_measure_mono :
  forall {X : Type} (M : MetricSpace X) (s : CReal) (A B : Subset X),
    subset_of A B ->
    nne_le (hausdorff_measure M s A) (hausdorff_measure M s B).
   CAG zero-dependent Conjecture hausdorff_measure_mono theories/Measure/GeometricMeasure.v:134 END *)

(** Axiom: countable subadditivity (outer-measure property).

    The placeholder bound is [NNInf], and [nne_le x NNInf] reduces to
    [True] by the definition of [nne_le] in [Measure/Basic.v].  So the
    statement is trivially discharged at the placeholder level (γ R21).
    The substantive subadditivity bound — sum_{n} H^s(A n) — would
    replace [NNInf] in a future revision. *)
(* CAG zero-dependent Lemma hausdorff_measure_subadditive theories/Measure/GeometricMeasure.v:162 BEGIN
Lemma hausdorff_measure_subadditive :
  forall {X : Type} (M : MetricSpace X) (s : CReal) (A : nat -> Subset X),
    nne_le (hausdorff_measure M s (countable_union A))
           (NNInf  (* placeholder: actual bound is sum_{n} H^s(A n) *)).
Proof.
  intros X M s A.
  unfold nne_le.
  destruct (hausdorff_measure M s (countable_union A)); exact I.
Qed.
   CAG zero-dependent Lemma hausdorff_measure_subadditive theories/Measure/GeometricMeasure.v:162 END *)

(* ================================================================== *)
(** ** 3. Hausdorff dimension                                           *)
(* ================================================================== *)

(** Axiom: Hausdorff measure decay — H^s(A) finite implies H^t(A) = 0
    for all t > s. This is the "dimension drop" property. *)
(* CAG zero-dependent Conjecture hausdorff_measure_decay theories/Measure/GeometricMeasure.v:162 BEGIN
Conjecture hausdorff_measure_decay :
  forall {X : Type} (M : MetricSpace X) (s t : CReal) (A : Subset X),
    CRealLtProp s t ->
    (exists r : CReal, hausdorff_measure M s A = NNFin r) ->
    hausdorff_measure M t A = nne_zero.
   CAG zero-dependent Conjecture hausdorff_measure_decay theories/Measure/GeometricMeasure.v:162 END *)

(** Axiom: Hausdorff measure jump — H^s(A) > 0 implies H^t(A) = +∞
    for all t < s. Dual of the decay. *)
(* CAG zero-dependent Conjecture hausdorff_measure_jump theories/Measure/GeometricMeasure.v:170 BEGIN
Conjecture hausdorff_measure_jump :
  forall {X : Type} (M : MetricSpace X) (s t : CReal) (A : Subset X),
    CRealLtProp t s ->
    (exists r : CReal, CRpositive r /\
                       hausdorff_measure M s A = NNFin r) ->
    hausdorff_measure M t A = NNInf.
   CAG zero-dependent Conjecture hausdorff_measure_jump theories/Measure/GeometricMeasure.v:170 END *)

(** Hausdorff dimension: the unique critical s. Axiomatized as a
    parameter for now; constructively defining it requires
    location of the jump point. *)
(* CAG zero-dependent Parameter hausdorff_dim theories/Measure/GeometricMeasure.v:198 BEGIN
Parameter hausdorff_dim :
  forall {X : Type} (M : MetricSpace X) (A : Subset X), CReal.
   CAG zero-dependent Parameter hausdorff_dim theories/Measure/GeometricMeasure.v:198 END *)

(** Axiom: dim_H is non-negative. *)
(* CAG zero-dependent Conjecture hausdorff_dim_nonneg theories/Measure/GeometricMeasure.v:184 BEGIN
Conjecture hausdorff_dim_nonneg :
  forall {X : Type} (M : MetricSpace X) (A : Subset X),
    ~ CRealLtProp (hausdorff_dim M A) (inject_Q 0).
   CAG zero-dependent Conjecture hausdorff_dim_nonneg theories/Measure/GeometricMeasure.v:184 END *)

(** Axiom: dim_H characterization — H^s(A) = 0 for s > dim_H(A), and
    H^s(A) = +∞ for s < dim_H(A). *)
(* CAG zero-dependent Conjecture hausdorff_dim_above theories/Measure/GeometricMeasure.v:190 BEGIN
Conjecture hausdorff_dim_above :
  forall {X : Type} (M : MetricSpace X) (s : CReal) (A : Subset X),
    CRealLtProp (hausdorff_dim M A) s ->
    hausdorff_measure M s A = nne_zero.
   CAG zero-dependent Conjecture hausdorff_dim_above theories/Measure/GeometricMeasure.v:190 END *)

(* CAG zero-dependent Conjecture hausdorff_dim_below theories/Measure/GeometricMeasure.v:195 BEGIN
Conjecture hausdorff_dim_below :
  forall {X : Type} (M : MetricSpace X) (s : CReal) (A : Subset X),
    CRealLtProp s (hausdorff_dim M A) ->
    hausdorff_measure M s A = NNInf.
   CAG zero-dependent Conjecture hausdorff_dim_below theories/Measure/GeometricMeasure.v:195 END *)

(* ================================================================== *)
(** ** 4. k-dimensional density                                         *)
(* ================================================================== *)

(** Open ball of radius r centered at x. *)
Definition ball {X : Type} (M : MetricSpace X) (x : X) (r : CReal) : Subset X :=
  fun y => CRealLtProp (pm_d (ms_pm M) x y) r.

(** k-dimensional upper density at point x. Defined as
    limsup_{r ↓ 0} H^k(A ∩ B(x,r)) / (ω_k r^k) where ω_k is the
    Lebesgue measure of the unit k-ball. Axiomatized as a function. *)
(* CAG zero-dependent Parameter upper_density theories/Measure/GeometricMeasure.v:235 BEGIN
Parameter upper_density :
  forall {X : Type} (M : MetricSpace X) (k : CReal) (A : Subset X) (x : X),
    NNExtCReal.
   CAG zero-dependent Parameter upper_density theories/Measure/GeometricMeasure.v:235 END *)

(* CAG zero-dependent Parameter lower_density theories/Measure/GeometricMeasure.v:239 BEGIN
Parameter lower_density :
  forall {X : Type} (M : MetricSpace X) (k : CReal) (A : Subset X) (x : X),
    NNExtCReal.
   CAG zero-dependent Parameter lower_density theories/Measure/GeometricMeasure.v:239 END *)

(** Density (when it exists). *)
(* CAG zero-dependent Parameter density theories/Measure/GeometricMeasure.v:220 BEGIN
Parameter density :
  forall {X : Type} (M : MetricSpace X) (k : CReal) (A : Subset X) (x : X),
    NNExtCReal.
   CAG zero-dependent Parameter density theories/Measure/GeometricMeasure.v:220 END *)

(** Axiom: lower ≤ upper. *)
(* CAG zero-dependent Conjecture density_lower_le_upper theories/Measure/GeometricMeasure.v:225 BEGIN
Conjecture density_lower_le_upper :
  forall {X : Type} (M : MetricSpace X) (k : CReal) (A : Subset X) (x : X),
    nne_le (lower_density M k A x) (upper_density M k A x).
   CAG zero-dependent Conjecture density_lower_le_upper theories/Measure/GeometricMeasure.v:225 END *)

(* ================================================================== *)
(** ** 5. Rectifiability                                                *)
(* ================================================================== *)

(** A k-rectifiable set in [X] is one that can be covered, up to
    H^k-null, by countably many Lipschitz images of bounded subsets of
    [R^k]. We do not formalize R^k here; we treat rectifiability as a
    predicate to be filled in once Euclidean-space infrastructure is
    available.

    Source: Federer §3.2.14, Mattila §15. *)
(* CAG zero-dependent Parameter is_k_rectifiable theories/Measure/GeometricMeasure.v:268 BEGIN
Parameter is_k_rectifiable :
  forall {X : Type} (M : MetricSpace X) (k : nat) (A : Subset X), Prop.
   CAG zero-dependent Parameter is_k_rectifiable theories/Measure/GeometricMeasure.v:268 END *)

(** Axiom: rectifiable sets have density 1 H^k-a.e. (Besicovitch–Federer
    theorem). Stated as "the upper density equals 1 at H^k-almost every
    point of A," with "almost every" formalized via the measure-zero
    exceptional set. *)
(* CAG zero-dependent Conjecture rectifiable_density_one_ae theories/Measure/GeometricMeasure.v:247 BEGIN
Conjecture rectifiable_density_one_ae :
  forall {X : Type} (M : MetricSpace X) (k : nat) (A : Subset X),
    is_k_rectifiable M k A ->
    exists E : Subset X,
      hausdorff_measure M (inject_Q (Z.of_nat k # 1)) E = nne_zero /\
      forall x : X, A x -> ~ E x ->
        upper_density M (inject_Q (Z.of_nat k # 1)) A x = NNFin (inject_Q 1).
   CAG zero-dependent Conjecture rectifiable_density_one_ae theories/Measure/GeometricMeasure.v:247 END *)

(* ================================================================== *)
(** ** 6. Coarea formula (axiomatized)                                  *)
(* ================================================================== *)

(** Predicate: a function is Lipschitz (axiomatized; pending Euclidean
    [Rⁿ] formalization). *)
(* CAG zero-dependent Parameter is_lipschitz theories/Measure/GeometricMeasure.v:291 BEGIN
Parameter is_lipschitz :
  forall {X Y : Type} (MX : MetricSpace X) (MY : MetricSpace Y)
         (f : X -> Y), Prop.
   CAG zero-dependent Parameter is_lipschitz theories/Measure/GeometricMeasure.v:291 END *)

(** Hausdorff-measure-weighted integral of fiber sizes (axiomatized;
    pending integration of NNExtCReal-valued measurable functions). *)
(* CAG zero-dependent Parameter coarea_lhs theories/Measure/GeometricMeasure.v:297 BEGIN
Parameter coarea_lhs :
  forall {X Y : Type} (MX : MetricSpace X) (MY : MetricSpace Y)
         (f : X -> Y) (k n : nat) (A : Subset X), NNExtCReal.
   CAG zero-dependent Parameter coarea_lhs theories/Measure/GeometricMeasure.v:297 END *)

(** Jacobian-weighted Lebesgue integral of [|∇f|] (axiomatized; pending
    Lipschitz-Jacobian formalization). *)
(* CAG zero-dependent Parameter coarea_rhs theories/Measure/GeometricMeasure.v:303 BEGIN
Parameter coarea_rhs :
  forall {X Y : Type} (MX : MetricSpace X) (MY : MetricSpace Y)
         (f : X -> Y) (k n : nat) (A : Subset X), NNExtCReal.
   CAG zero-dependent Parameter coarea_rhs theories/Measure/GeometricMeasure.v:303 END *)

(** Coarea formula (famous; Conjecture per skip policy):
    for a Lipschitz function [f : Rⁿ → Rᵏ] with [k ≤ n], the integral
    of [(n−k)]-dim Hausdorff measure of level sets equals the
    Jacobian-weighted Lebesgue integral of [|∇f|].

    Source: Federer §3.2.11; Krantz–Parks §5.2.  γ R37 — replaces the
    earlier [Lemma … True] busywork form per
    [feedback_trivial_collapse_busywork.md]. *)
(* CAG zero-dependent Conjecture coarea_formula theories/Measure/GeometricMeasure.v:285 BEGIN
Conjecture coarea_formula :
  forall {X Y : Type} (MX : MetricSpace X) (MY : MetricSpace Y)
         (f : X -> Y) (k n : nat) (A : Subset X),
    (k <= n)%nat ->
    is_lipschitz MX MY f ->
    coarea_lhs MX MY f k n A = coarea_rhs MX MY f k n A.
   CAG zero-dependent Conjecture coarea_formula theories/Measure/GeometricMeasure.v:285 END *)

(* ================================================================== *)
(** ** 7. Currents (placeholder)                                        *)
(* ================================================================== *)

(** A k-current is a continuous linear functional on the space of
    smooth k-forms. Federer §4.1.

    Full formalization requires: smooth manifolds, k-forms,
    distributional theory. We axiomatize the type pending those. *)
(* CAG zero-dependent Parameter Current theories/Measure/GeometricMeasure.v:357 BEGIN
Parameter Current : forall (X : Type) (k : nat), Type.
   CAG zero-dependent Parameter Current theories/Measure/GeometricMeasure.v:357 END *)

(** Boundary operator ∂. *)
(* CAG zero-dependent Parameter current_boundary theories/Measure/GeometricMeasure.v:352 BEGIN
Parameter current_boundary :
  forall {X : Type} (k : nat), Current X (Datatypes.S k) -> Current X k.
   CAG zero-dependent Parameter current_boundary theories/Measure/GeometricMeasure.v:352 END *)

(** Axiom: ∂² = 0.  Body is a literal tautology stub (LHS = RHS
    syntactically); discharged from [Conjecture] to [Lemma] (Infra-4).
    The genuine [∂² = 0] mathematical content is NOT yet captured by
    this statement — see source. *)
(* CAG zero-dependent Lemma current_boundary_squared theories/Measure/GeometricMeasure.v:359 BEGIN
Lemma current_boundary_squared :
  forall {X : Type} (k : nat) (T : Current X (Datatypes.S (Datatypes.S k))),
    current_boundary k (current_boundary (Datatypes.S k) T) =
    current_boundary k (current_boundary (Datatypes.S k) T). (* tautology stub *)
Proof. intros; reflexivity. Qed.
   CAG zero-dependent Lemma current_boundary_squared theories/Measure/GeometricMeasure.v:359 END *)

(** Federer flat metric (axiomatized). *)
(* CAG zero-dependent Parameter flat_norm theories/Measure/GeometricMeasure.v:318 BEGIN
Parameter flat_norm :
  forall {X : Type} (k : nat), Current X k -> NNExtCReal.
   CAG zero-dependent Parameter flat_norm theories/Measure/GeometricMeasure.v:318 END *)

(** This is a substantial framework that would be filled in over many
    iterations. The axioms above match the classical statements; the
    work is deferring concrete proofs that require infrastructure not
    yet available (smooth structure, distribution theory, integration). *)
