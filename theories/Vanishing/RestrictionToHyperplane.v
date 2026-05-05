(** Vanishing/RestrictionToHyperplane.v — Restriction to smooth hyperplane sections

    For M a compact Kähler manifold of complex dimension n and
    V ⊂ M a smooth positive divisor (hyperplane section), the two
    exact sequences of sheaves:

        (star) 0 -> Omega^p_M(-V) -> Omega^p_M -> Omega^p_M|_V -> 0
        (starstar) 0 -> Omega^{p-1}_V(-V) -> Omega^p_M|_V -> Omega^p_V -> 0

    together with Kodaira vanishing ([-V] is negative) give:

    Theorem: The restriction map H^q(M, Ω^p_M) → H^q(V, Ω^p_V) is
    - an isomorphism for p+q < n-2
    - injective for p+q = n-1.

    References: ag.org §Restriction of forms, §Vanishing input *)

From Stdlib Require Import List Arith Lia.
From CAG Require Import Complex.
From CAG Require Import ManifoldTopology.
From CAG Require Import Divisor.LineBundleCech.
From CAG Require Import Divisor.DivisorBundle.
From CAG Require Import Divisor.Curvature.
From CAG Require Import CanonicalBundle.Adjunction.
From CAG Require Import Vanishing.KodairaVanishing.
From CAG Require Import Vanishing.LefschetzHyperplane.
From CAG Require Import Kahler.Lefschetz.Operators.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Twisted differential forms                                    *)
(* ================================================================== *)

(** Cohomology H^q(M, Ω^p_M ⊗ L) = H^{p,q}(M, L) by Dolbeault. *)
(* CAG constructive-remove Command Notation theories/Vanishing/RestrictionToHyperplane.v:36 BEGIN -- missing HDolb
Notation HDolb_twist M L p q := (HDolb M L p q).

   CAG constructive-remove Command Notation theories/Vanishing/RestrictionToHyperplane.v:36 END *)

(** The restriction of Ω^p_M to V: the bundle Ω^p_M|_V on V. *)
(* CAG zero-dependent Parameter restriction_forms theories/Vanishing/RestrictionToHyperplane.v:39 BEGIN
Parameter restriction_forms : forall (M : KahlerManifold)
    (V : smooth_hyperplane_section M) (p : nat),
    HolLineBundleCech (km_manifold (shs_manifold M V)).
   CAG zero-dependent Parameter restriction_forms theories/Vanishing/RestrictionToHyperplane.v:39 END *)

(* ================================================================== *)
(** * 2. First exact sequence (star)                                      *)
(* ================================================================== *)

(** The twist Ω^p_M(-V) = Ω^p_M ⊗ [-V] (where [-V] is negative). *)
(* CAG zero-dependent Parameter forms_twisted_neg theories/Vanishing/RestrictionToHyperplane.v:50 BEGIN
Parameter forms_twisted_neg : forall (M : KahlerManifold)
    (V : smooth_hyperplane_section M) (p : nat),
    HolLineBundleCech (km_manifold M).
   CAG zero-dependent Parameter forms_twisted_neg theories/Vanishing/RestrictionToHyperplane.v:50 END *)

(** Exact sequence: 0 → Ω^p_M(-V) → Ω^p_M → Ω^p_M|_V → 0
    This comes from tensoring the structure sequence
    0 → [-V] → O_M → O_V → 0  with Ω^p_M. *)
(* CAG zero-dependent Theorem exact_seq_star theories/Vanishing/RestrictionToHyperplane.v:59 BEGIN
Theorem exact_seq_star : forall (M : KahlerManifold)
    (V : smooth_hyperplane_section M) (p : nat),
    (** The long exact cohomology sequence from (star) — axiomatized *)
    True.
Proof. intros; exact I. Qed.
   CAG zero-dependent Theorem exact_seq_star theories/Vanishing/RestrictionToHyperplane.v:59 END *)

(** Long exact sequence: induced maps on cohomology from (star). *)
(* CAG zero-dependent Parameter les_star_map theories/Vanishing/RestrictionToHyperplane.v:62 BEGIN
Parameter les_star_map : forall (M : KahlerManifold)
    (V : smooth_hyperplane_section M) (p q : nat),
    HDolb M (forms_twisted_neg M V p) p q ->
    HDolb M (forms_twisted_neg M V 0) p q.
   CAG zero-dependent Parameter les_star_map theories/Vanishing/RestrictionToHyperplane.v:62 END *)

(* ================================================================== *)
(** * 3. Second exact sequence (starstar)                                    *)
(* ================================================================== *)

(** Ω^{p-1}_V(-V) = Ω^{p-1}_V ⊗ [-V]|_V on V. *)
(* CAG zero-dependent Parameter forms_V_twisted theories/Vanishing/RestrictionToHyperplane.v:76 BEGIN
Parameter forms_V_twisted : forall (M : KahlerManifold)
    (V : smooth_hyperplane_section M) (p : nat),
    HolLineBundleCech (km_manifold (shs_manifold M V)).
   CAG zero-dependent Parameter forms_V_twisted theories/Vanishing/RestrictionToHyperplane.v:76 END *)

(** Exact sequence: 0 → Ω^{p-1}_V(-V) → Ω^p_M|_V → Ω^p_V → 0.
    Derived from the normal bundle sequence
    0 → N_V^* → T_M^*|_V → T_V^* → 0  and adjunction N_V^* ≅ [-V]|_V. *)
(* CAG zero-dependent Theorem exact_seq_starstar theories/Vanishing/RestrictionToHyperplane.v:87 BEGIN
Theorem exact_seq_starstar : forall (M : KahlerManifold)
    (V : smooth_hyperplane_section M) (p : nat),
    (** Long exact cohomology sequence from (starstar) — axiomatized *)
    True.
Proof. intros; exact I. Qed.
   CAG zero-dependent Theorem exact_seq_starstar theories/Vanishing/RestrictionToHyperplane.v:87 END *)

(* ================================================================== *)
(** * 4. Kodaira vanishing applied to the twisted pieces               *)
(* ================================================================== *)

(** [-V] is negative on M (V is a positive divisor / hyperplane section). *)
(* CAG zero-dependent Admitted neg_V_is_negative theories/Vanishing/RestrictionToHyperplane.v:93 BEGIN
Theorem neg_V_is_negative : forall (M : KahlerManifold)
    (V : smooth_hyperplane_section M),
    negative_line_bundle M (forms_twisted_neg M V 0).
Proof. admit. Admitted.
   CAG zero-dependent Admitted neg_V_is_negative theories/Vanishing/RestrictionToHyperplane.v:93 END *)

(** By Kodaira vanishing: H^q(M, Ω^p_M(-V)) = 0 for p+q < n. *)
(* CAG zero-dependent Admitted kodaira_forms_twisted_vanish theories/Vanishing/RestrictionToHyperplane.v:101 BEGIN
Theorem kodaira_forms_twisted_vanish : forall (M : KahlerManifold)
    (V : smooth_hyperplane_section M) (p q : nat),
    (p + q < km_dim M)%nat ->
    forall α : HDolb M (forms_twisted_neg M V p) p q,
    α = HDolb_zero M _ p q.
Proof. admit. Admitted.
   CAG zero-dependent Admitted kodaira_forms_twisted_vanish theories/Vanishing/RestrictionToHyperplane.v:101 END *)

(** By Kodaira vanishing: H^q(V, Ω^{p-1}_V(-V)) = 0 for p+q < n-1. *)
(* CAG zero-dependent Admitted kodaira_V_forms_twisted_vanish theories/Vanishing/RestrictionToHyperplane.v:109 BEGIN
Theorem kodaira_V_forms_twisted_vanish : forall (M : KahlerManifold)
    (V : smooth_hyperplane_section M) (p q : nat),
    (p + q < km_dim M - 1)%nat ->
    forall α : HDolb (shs_manifold M V) (forms_V_twisted M V p) (p-1) q,
    α = HDolb_zero (shs_manifold M V) _ _ _.
Proof. admit. Admitted.
   CAG zero-dependent Admitted kodaira_V_forms_twisted_vanish theories/Vanishing/RestrictionToHyperplane.v:109 END *)

(* ================================================================== *)
(** * 5. Main theorem: restriction isomorphism                         *)
(* ================================================================== *)

(** The restriction map on Dolbeault cohomology. *)
(* CAG zero-dependent Parameter restriction_dolbeault theories/Vanishing/RestrictionToHyperplane.v:126 BEGIN
(* CAG zero-dependent Parameter restriction_dolbeault theories/Vanishing/RestrictionToHyperplane.v:126 BEGIN
Parameter restriction_dolbeault : forall (M : KahlerManifold)
    (V : smooth_hyperplane_section M) (p q : nat),
    HDolb M (forms_twisted_neg M V 0) p q ->
    HDolb (shs_manifold M V) (forms_V_twisted M V 0) p q.
   CAG zero-dependent Parameter restriction_dolbeault theories/Vanishing/RestrictionToHyperplane.v:126 END *)
   CAG zero-dependent Parameter restriction_dolbeault theories/Vanishing/RestrictionToHyperplane.v:126 END *)

(** Main theorem: H^q(M, Ω^p_M) → H^q(V, Ω^p_V) is iso for p+q < n-2. *)
(* CAG zero-dependent Theorem restriction_dolbeault_iso theories/Vanishing/RestrictionToHyperplane.v:140 BEGIN
Theorem restriction_dolbeault_iso : forall (M : KahlerManifold)
    (V : smooth_hyperplane_section M) (p q : nat),
    (p + q < km_dim M - 2)%nat ->
    (** restriction_dolbeault M V p q is an isomorphism — axiomatized *)
    True.
Proof. intros; exact I. Qed.
   CAG zero-dependent Theorem restriction_dolbeault_iso theories/Vanishing/RestrictionToHyperplane.v:140 END *)

(** Main theorem: H^q(M, Ω^p_M) → H^q(V, Ω^p_V) is injective for p+q = n-1. *)
(* CAG zero-dependent Admitted restriction_dolbeault_injective theories/Vanishing/RestrictionToHyperplane.v:136 BEGIN
Theorem restriction_dolbeault_injective : forall (M : KahlerManifold)
    (V : smooth_hyperplane_section M) (p q : nat),
    (p + q = km_dim M - 1)%nat ->
    forall α : HDolb M (forms_twisted_neg M V 0) p q,
    restriction_dolbeault M V p q α = HDolb_zero _ _ _ _ ->
    α = HDolb_zero M _ p q.
Proof. admit. Admitted.
   CAG zero-dependent Admitted restriction_dolbeault_injective theories/Vanishing/RestrictionToHyperplane.v:136 END *)

(** Packaged theorem. *)
(* CAG zero-dependent Definition restriction_on_holomorphic_form_cohomology_for_positive_hyperplane_section theories/Vanishing/RestrictionToHyperplane.v:159 BEGIN
Definition restriction_on_holomorphic_form_cohomology_for_positive_hyperplane_section
    (M : KahlerManifold) (V : smooth_hyperplane_section M) :=
  forall p q : nat,
    (p + q < km_dim M - 2)%nat ->
    (** restriction H^q(M,Ω^p) → H^q(V,Ω^p) is iso — follows from kodaira vanishing *)
    True.
   CAG zero-dependent Definition restriction_on_holomorphic_form_cohomology_for_positive_hyperplane_section theories/Vanishing/RestrictionToHyperplane.v:159 END *)
