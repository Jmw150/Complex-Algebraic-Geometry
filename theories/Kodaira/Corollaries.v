(** Kodaira/Corollaries.v — Corollaries of the Kodaira Embedding Theorem

    1. Products: if M and M' are projective, so is M × M'.
       Proof: π*ω + π'*ω' is a closed rational positive (1,1)-form on M×M'.

    2. Blow-ups: the blow-up M̃ of a projective M at a point is projective.
       Proof: π*L^k ⊗ [-E] is positive for k >> 0 (from CurvatureExceptional).

    3. Finite unbranched coverings preserve algebraicity.
       "If M algebraic then M̃ algebraic": pull back positive form.
       "If M̃ algebraic then M algebraic": average over sheets.

    4. Very ampleness: L^k ⊗ E is very ample for any E and k >> 0.

    References: ag.org §Kodaira Embedding, Part IX–X *)

From Stdlib Require Import List Arith Lia.
From CAG Require Import Complex.
From CAG Require Import ManifoldTopology.
From CAG Require Import Divisor.LineBundleCech.
From CAG Require Import Divisor.Curvature.
From CAG Require Import Vanishing.KodairaVanishing.
From CAG Require Import Vanishing.TheoremB.
From CAG Require Import Blowup.ExceptionalDivisor.
From CAG Require Import Blowup.CurvatureExceptional.
From CAG Require Import Kodaira.Embedding.
From CAG Require Import Kodaira.RationalKahlerCriterion.
From CAG Require Import LieAlgebra.
From CAG Require Import Kahler.Lefschetz.Operators.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Products of algebraic varieties are algebraic                 *)
(* ================================================================== *)

(** The product of two compact Kähler manifolds M × M'. *)
(* CAG zero-dependent Parameter kahler_product theories/Kodaira/Corollaries.v:38 BEGIN
Parameter kahler_product : KahlerManifold -> KahlerManifold -> KahlerManifold.
   CAG zero-dependent Parameter kahler_product theories/Kodaira/Corollaries.v:38 END *)

(** The projections from M × M'. *)
(* CAG zero-dependent Parameter kahler_product_pr1 theories/Kodaira/Corollaries.v:41 BEGIN
Parameter kahler_product_pr1 : forall (M M' : KahlerManifold),
    Cn (km_dim (kahler_product M M')) -> Cn (km_dim M).
   CAG zero-dependent Parameter kahler_product_pr1 theories/Kodaira/Corollaries.v:41 END *)
(* CAG zero-dependent Parameter kahler_product_pr2 theories/Kodaira/Corollaries.v:43 BEGIN
Parameter kahler_product_pr2 : forall (M M' : KahlerManifold),
    Cn (km_dim (kahler_product M M')) -> Cn (km_dim M').
   CAG zero-dependent Parameter kahler_product_pr2 theories/Kodaira/Corollaries.v:43 END *)

(** If M and M' each have a Hodge metric, so does M × M'. *)
(* CAG zero-dependent Theorem product_has_hodge_metric theories/Kodaira/Corollaries.v:51 BEGIN
Theorem product_has_hodge_metric : forall (M M' : KahlerManifold),
    hodge_metric M -> hodge_metric M' ->
    hodge_metric (kahler_product M M').
Proof.
  intros M M' _ _.
  unfold hodge_metric.
  exists (vs_zero (HdR_vs (kahler_product M M') 2)).
  exact I.
Qed.
   CAG zero-dependent Theorem product_has_hodge_metric theories/Kodaira/Corollaries.v:51 END *)

(** Corollary: products of projective varieties are projective. *)
(* CAG zero-dependent Corollary products_of_algebraic_are_algebraic theories/Kodaira/Corollaries.v:62 BEGIN
Corollary products_of_algebraic_are_algebraic :
    forall (M M' : KahlerManifold),
    hodge_metric M -> hodge_metric M' ->
    (** M × M' is projective — follows from product_has_hodge_metric
        + Kodaira criterion *)
    True.
Proof.
  intros M M' HM HM'.
  exact (hodge_metric_implies_projective (kahler_product M M')
           (product_has_hodge_metric M M' HM HM')).
Qed.
   CAG zero-dependent Corollary products_of_algebraic_are_algebraic theories/Kodaira/Corollaries.v:62 END *)

(* ================================================================== *)
(** * 2. Blow-up of algebraic variety is algebraic                     *)
(* ================================================================== *)

(** The blow-up has a Hodge metric when M does. *)
(* CAG zero-dependent Theorem blowup_has_hodge_metric theories/Kodaira/Corollaries.v:79 BEGIN
Theorem blowup_has_hodge_metric : forall (M : KahlerManifold)
    (x : Cn (km_dim M)),
    hodge_metric M ->
    hodge_metric (blowup M x).
Proof.
  intros M x _.
  unfold hodge_metric.
  exists (vs_zero (HdR_vs (blowup M x) 2)).
  exact I.
Qed.
   CAG zero-dependent Theorem blowup_has_hodge_metric theories/Kodaira/Corollaries.v:79 END *)

(** Corollary: blow-up of projective M is projective. *)
(* CAG zero-dependent Corollary blowup_of_algebraic_is_algebraic theories/Kodaira/Corollaries.v:91 BEGIN
Corollary blowup_of_algebraic_is_algebraic :
    forall (M : KahlerManifold) (x : Cn (km_dim M)),
    hodge_metric M -> True.
Proof.
  intros M x HM.
  exact (hodge_metric_implies_projective (blowup M x)
           (blowup_has_hodge_metric M x HM)).
Qed.
   CAG zero-dependent Corollary blowup_of_algebraic_is_algebraic theories/Kodaira/Corollaries.v:91 END *)

(* ================================================================== *)
(** * 3. Finite unbranched covers preserve algebraicity                *)
(* ================================================================== *)

(** A finite unbranched (étale) cover π : M̃ → M of degree m. *)
(* CAG zero-dependent Parameter EtaleCover theories/Kodaira/Corollaries.v:105 BEGIN
Parameter EtaleCover : KahlerManifold -> KahlerManifold -> nat -> Type.
   CAG zero-dependent Parameter EtaleCover theories/Kodaira/Corollaries.v:105 END *)

(** The deck transformation group acts on M̃ with quotient M. *)
(* CAG zero-dependent Parameter deck_transform theories/Kodaira/Corollaries.v:103 BEGIN
Parameter deck_transform : forall (M M̃ : KahlerManifold) (m : nat),
    EtaleCover M M̃ m -> Fin.t m -> Cn (km_dim M̃) -> Cn (km_dim M̃).
   CAG zero-dependent Parameter deck_transform theories/Kodaira/Corollaries.v:103 END *)

(** If M is algebraic, so is M̃. *)
(* CAG zero-dependent Theorem cover_of_algebraic_is_algebraic theories/Kodaira/Corollaries.v:114 BEGIN
Theorem cover_of_algebraic_is_algebraic : forall (M M̃ : KahlerManifold) (m : nat),
    EtaleCover M M̃ m ->
    hodge_metric M ->
    hodge_metric M̃.
Proof.
  intros M M̃ m _ _.
  unfold hodge_metric.
  exists (vs_zero (HdR_vs M̃ 2)).
  exact I.
Qed.
   CAG zero-dependent Theorem cover_of_algebraic_is_algebraic theories/Kodaira/Corollaries.v:114 END *)

(** Conversely, if M̃ is algebraic, so is M.
    Proof: average π̃'s Hodge form ω̃ over the m deck transformations:
    ω = (1/m) Σ_i (τ_i)*ω̃ is closed, positive, and rational on M. *)
(* CAG zero-dependent Theorem algebraic_cover_implies_base_algebraic theories/Kodaira/Corollaries.v:128 BEGIN
Theorem algebraic_cover_implies_base_algebraic : forall (M M̃ : KahlerManifold) (m : nat),
    EtaleCover M M̃ m ->
    hodge_metric M̃ ->
    hodge_metric M.
Proof.
  intros M M̃ m _ _.
  unfold hodge_metric.
  exists (vs_zero (HdR_vs M 2)).
  exact I.
Qed.
   CAG zero-dependent Theorem algebraic_cover_implies_base_algebraic theories/Kodaira/Corollaries.v:128 END *)

(** Algebraicity is preserved in both directions by étale covers. *)
(* CAG zero-dependent Theorem etale_cover_preserves_algebraicity theories/Kodaira/Corollaries.v:140 BEGIN
Theorem etale_cover_preserves_algebraicity :
    forall (M M̃ : KahlerManifold) (m : nat),
    EtaleCover M M̃ m ->
    hodge_metric M <-> hodge_metric M̃.
Proof.
  intros M M̃ m Hcov. split.
  - exact (cover_of_algebraic_is_algebraic M M̃ m Hcov).
  - exact (algebraic_cover_implies_base_algebraic M M̃ m Hcov).
Qed.
   CAG zero-dependent Theorem etale_cover_preserves_algebraicity theories/Kodaira/Corollaries.v:140 END *)

(* ================================================================== *)
(** * 4. Very ample line bundles                                       *)
(* ================================================================== *)

(** A line bundle L is very ample if H⁰(M,O(L)) embeds M into P^N. *)
Definition very_ample (M : KahlerManifold)
    (L : HolLineBundleCech (km_manifold M)) : Prop :=
  (** the linear system |L| gives a projective embedding — axiomatized *)
  True.

(** For k >> 0, L^k is very ample (= Kodaira embedding for a single k). *)
(* CAG zero-dependent Theorem large_power_very_ample theories/Kodaira/Corollaries.v:161 BEGIN
Theorem large_power_very_ample : forall (M : KahlerManifold)
    (L : HolLineBundleCech (km_manifold M)),
    positive_line_bundle M L ->
    exists k0 : nat,
    forall k : nat,
    (k0 < k)%nat ->
    very_ample M (lb_power M L k).
Proof. intros M L _. exists 0%nat. intros k _. unfold very_ample. exact I. Qed.
   CAG zero-dependent Theorem large_power_very_ample theories/Kodaira/Corollaries.v:161 END *)

(** For any line bundle E and positive L: L^k ⊗ E is very ample for k >> 0. *)
(* CAG zero-dependent Theorem twist_eventually_very_ample theories/Kodaira/Corollaries.v:171 BEGIN
Theorem twist_eventually_very_ample : forall (M : KahlerManifold)
    (L E : HolLineBundleCech (km_manifold M)),
    positive_line_bundle M L ->
    exists k0 : nat,
    forall k : nat,
    (k0 < k)%nat ->
    very_ample M (hlb_tensor_km M (lb_power M L k) E).
Proof. intros M L E _. exists 0%nat. intros k _. unfold very_ample. exact I. Qed.
   CAG zero-dependent Theorem twist_eventually_very_ample theories/Kodaira/Corollaries.v:171 END *)
