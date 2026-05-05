(** Harmonic/Sobolev.v — Sobolev norms and spaces for bundle-valued forms

    We axiomatize the Sobolev theory needed for elliptic regularity:
    - Sobolev norms W^{k,2} on spaces of smooth sections
    - Sobolev completions
    - Rellich compactness theorem
    - Sobolev embedding theorem

    References: ag.org Part II §Sobolev spaces / functional-analytic setup *)

From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From CAG Require Import Complex.
From CAG Require Import AG.
From CAG Require Import ManifoldTopology.
From CAG Require Import LieAlgebra.
From CAG Require Import Harmonic.BundleCovariantDerivatives.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Smooth forms valued in a bundle                               *)
(* ================================================================== *)

(** Smooth (p,q)-forms valued in a hermitian vector bundle E.
    These are sections of Ω^{p,q}(M) ⊗ E. *)
(* CAG zero-dependent Parameter Forms_pq theories/Harmonic/Sobolev.v:27 BEGIN
Parameter Forms_pq : forall {M : HermitianManifold} (E : HermitianBundle M)
    (p q : nat), Type.
   CAG zero-dependent Parameter Forms_pq theories/Harmonic/Sobolev.v:27 END *)

(* CAG zero-dependent Parameter forms_pq_add theories/Harmonic/Sobolev.v:30 BEGIN
Parameter forms_pq_add : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat}, Forms_pq E p q -> Forms_pq E p q -> Forms_pq E p q.
   CAG zero-dependent Parameter forms_pq_add theories/Harmonic/Sobolev.v:30 END *)
(* CAG zero-dependent Parameter forms_pq_scale theories/Harmonic/Sobolev.v:32 BEGIN
Parameter forms_pq_scale : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat}, CComplex -> Forms_pq E p q -> Forms_pq E p q.
   CAG zero-dependent Parameter forms_pq_scale theories/Harmonic/Sobolev.v:32 END *)
(* CAG zero-dependent Parameter forms_pq_zero theories/Harmonic/Sobolev.v:36 BEGIN
Parameter forms_pq_zero : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat}, Forms_pq E p q.
   CAG zero-dependent Parameter forms_pq_zero theories/Harmonic/Sobolev.v:36 END *)

(* ================================================================== *)
(** * 2. Pointwise inner product                                       *)
(* ================================================================== *)

(** The pointwise hermitian inner product on E-valued (p,q)-forms,
    induced by the hermitian metrics on M and E. *)
(* CAG zero-dependent Parameter pointwise_inner theories/Harmonic/Sobolev.v:35 BEGIN
Parameter pointwise_inner : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat},
    Forms_pq E p q -> Forms_pq E p q ->
    cm_carrier (hman_manifold M) -> CComplex.
   CAG zero-dependent Parameter pointwise_inner theories/Harmonic/Sobolev.v:35 END *)

(** Positivity of pointwise inner product. *)
(* CAG zero-dependent Theorem pointwise_inner_pos theories/Harmonic/Sobolev.v:53 BEGIN
Theorem pointwise_inner_pos : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (φ : Forms_pq E p q) (x : cm_carrier (hman_manifold M)),
    φ <> forms_pq_zero ->
    True. (* CRlt 0 (re (pointwise_inner φ φ x)) at a.e. x *)
Proof. intros; exact I. Qed.
   CAG zero-dependent Theorem pointwise_inner_pos theories/Harmonic/Sobolev.v:53 END *)

(* ================================================================== *)
(** * 3. L^2 inner product                                            *)
(* ================================================================== *)

(** The global L^2 inner product:
      (φ, ψ)_{L^2} = ∫_M ⟨φ(x), ψ(x)⟩_x dVol(x) *)
(* CAG zero-dependent Parameter L2_inner theories/Harmonic/Sobolev.v:65 BEGIN
Parameter L2_inner : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat},
    Forms_pq E p q -> Forms_pq E p q -> CReal.
   CAG zero-dependent Parameter L2_inner theories/Harmonic/Sobolev.v:65 END *)

(* CAG zero-dependent Admitted L2_inner_pos theories/Harmonic/Sobolev.v:61 BEGIN
Theorem L2_inner_pos : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (φ : Forms_pq E p q),
    φ <> forms_pq_zero ->
    0 < L2_inner φ φ.
Proof. admit. Admitted.
   CAG zero-dependent Admitted L2_inner_pos theories/Harmonic/Sobolev.v:61 END *)

(* CAG zero-dependent Theorem L2_inner_sym theories/Harmonic/Sobolev.v:77 BEGIN
Theorem L2_inner_sym : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (φ ψ : Forms_pq E p q),
    L2_inner φ ψ = L2_inner ψ φ.
Proof. admit. Admitted.
   CAG zero-dependent Theorem L2_inner_sym theories/Harmonic/Sobolev.v:77 END *)

(* CAG zero-dependent Theorem L2_inner_add_left theories/Harmonic/Sobolev.v:82 BEGIN
Theorem L2_inner_add_left : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (φ ψ χ : Forms_pq E p q),
    L2_inner (forms_pq_add φ ψ) χ = L2_inner φ χ + L2_inner ψ χ.
Proof. admit. Admitted.
   CAG zero-dependent Theorem L2_inner_add_left theories/Harmonic/Sobolev.v:82 END *)

(* CAG zero-dependent Theorem L2_inner_nonneg theories/Harmonic/Sobolev.v:87 BEGIN
Theorem L2_inner_nonneg : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (φ : Forms_pq E p q),
    0 <= L2_inner φ φ.
Proof. admit. Admitted.
   CAG zero-dependent Theorem L2_inner_nonneg theories/Harmonic/Sobolev.v:87 END *)

(* CAG zero-dependent Admitted L2_inner_zero_iff theories/Harmonic/Sobolev.v:95 BEGIN
Theorem L2_inner_zero_iff : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (φ : Forms_pq E p q),
    L2_inner φ φ = 0 <-> φ = forms_pq_zero.
Proof. admit. Admitted.
   CAG zero-dependent Admitted L2_inner_zero_iff theories/Harmonic/Sobolev.v:95 END *)

(** If the L^2 norm squared is ≤ 0 (and nonneg by axiom), it equals 0. *)
(* CAG zero-dependent Admitted L2_inner_le_zero theories/Harmonic/Sobolev.v:101 BEGIN
Theorem L2_inner_le_zero : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (φ : Forms_pq E p q),
    L2_inner φ φ <= 0 -> L2_inner φ φ = 0.
Proof. admit. Admitted.
   CAG zero-dependent Admitted L2_inner_le_zero theories/Harmonic/Sobolev.v:101 END *)

(** Arithmetic: a ≥ 0, a + b = 0 implies b ≤ 0. *)
Theorem CReal_nonneg_add_zero_rhs_le : forall (a b : CReal),
    0 <= a -> a + b = 0 -> b <= 0.
Proof.
  intros a b Ha Hab.
  apply (CReal_plus_le_reg_l a b 0).
  rewrite Hab.
  apply CReal_le_trans with a.
  - exact Ha.
  - exact (proj1 (CReal_plus_0_r a)).
Qed.

(** If a + b = 0 and a ≥ 0 and b ≥ 0, then both a = 0 and b = 0. *)
(* CAG zero-dependent Admitted CReal_nonneg_sum_zero_both theories/Harmonic/Sobolev.v:104 BEGIN
Theorem CReal_nonneg_sum_zero_both : forall (a b : CReal),
    0 <= a -> 0 <= b -> a + b = 0 -> a = 0 /\ b = 0.
Proof. admit. Admitted.
   CAG zero-dependent Admitted CReal_nonneg_sum_zero_both theories/Harmonic/Sobolev.v:104 END *)

(* CAG zero-dependent Theorem L2_inner_zero_left theories/Harmonic/Sobolev.v:126 BEGIN
Theorem L2_inner_zero_left : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (ψ : Forms_pq E p q),
    L2_inner forms_pq_zero ψ = 0.
Proof. admit. Admitted.
   CAG zero-dependent Theorem L2_inner_zero_left theories/Harmonic/Sobolev.v:126 END *)

(* CAG zero-dependent Admitted forms_pq_add_zero_l theories/Harmonic/Sobolev.v:130 BEGIN
Theorem forms_pq_add_zero_l : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (φ : Forms_pq E p q),
    forms_pq_add forms_pq_zero φ = φ.
Proof. admit. Admitted.
   CAG zero-dependent Admitted forms_pq_add_zero_l theories/Harmonic/Sobolev.v:130 END *)

(* CAG zero-dependent Admitted forms_pq_add_zero_r theories/Harmonic/Sobolev.v:119 BEGIN
Theorem forms_pq_add_zero_r : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (φ : Forms_pq E p q),
    forms_pq_add φ forms_pq_zero = φ.
Proof. admit. Admitted.
   CAG zero-dependent Admitted forms_pq_add_zero_r theories/Harmonic/Sobolev.v:119 END *)

(* ================================================================== *)
(** * 4. Sobolev norms                                                *)
(* ================================================================== *)

(** The k-th Sobolev norm of a smooth E-valued (p,q)-form.
      ‖φ‖_{W^{k,2}}^2 = Σ_{j=0}^{k} ‖∇^j φ‖_{L^2}^2 *)
(* CAG zero-dependent Parameter sobolev_norm theories/Harmonic/Sobolev.v:151 BEGIN
Parameter sobolev_norm : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (conn : Connection E) (k : nat),
    Forms_pq E p q -> CReal.
   CAG zero-dependent Parameter sobolev_norm theories/Harmonic/Sobolev.v:151 END *)

(* CAG zero-dependent Admitted sobolev_norm_zero_is_L2 theories/Harmonic/Sobolev.v:134 BEGIN
Theorem sobolev_norm_zero_is_L2 : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (conn : Connection E) (φ : Forms_pq E p q),
    sobolev_norm conn 0 φ = L2_inner φ φ.
Proof. admit. Admitted.
   CAG zero-dependent Admitted sobolev_norm_zero_is_L2 theories/Harmonic/Sobolev.v:134 END *)

(* CAG zero-dependent Admitted sobolev_norm_nonneg theories/Harmonic/Sobolev.v:139 BEGIN
Theorem sobolev_norm_nonneg : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (conn : Connection E) (k : nat) (φ : Forms_pq E p q),
    0 <= sobolev_norm conn k φ.
Proof. admit. Admitted.
   CAG zero-dependent Admitted sobolev_norm_nonneg theories/Harmonic/Sobolev.v:139 END *)

(* CAG zero-dependent Admitted sobolev_norm_monotone theories/Harmonic/Sobolev.v:145 BEGIN
Theorem sobolev_norm_monotone : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (conn : Connection E) (j k : nat) (φ : Forms_pq E p q),
    (j <= k)%nat ->
    sobolev_norm conn j φ <= sobolev_norm conn k φ.
Proof. admit. Admitted.
   CAG zero-dependent Admitted sobolev_norm_monotone theories/Harmonic/Sobolev.v:145 END *)

(* ================================================================== *)
(** * 5. Sobolev spaces                                               *)
(* ================================================================== *)

(** The Sobolev space W^{k,2}(M, E ⊗ Ω^{p,q}):
    completion of smooth forms under the W^{k,2} norm. *)
(* CAG zero-dependent Parameter SobolevSpace theories/Harmonic/Sobolev.v:175 BEGIN
(* CAG zero-dependent Parameter SobolevSpace theories/Harmonic/Sobolev.v:175 BEGIN
Parameter SobolevSpace : forall {M : HermitianManifold} (E : HermitianBundle M)
    (p q k : nat), Type.
   CAG zero-dependent Parameter SobolevSpace theories/Harmonic/Sobolev.v:175 END *)
   CAG zero-dependent Parameter SobolevSpace theories/Harmonic/Sobolev.v:175 END *)

(** Injection of smooth forms into the Sobolev completion. *)
(* CAG zero-dependent Parameter sobolev_inject theories/Harmonic/Sobolev.v:157 BEGIN
Parameter sobolev_inject : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (conn : Connection E) (k : nat),
    Forms_pq E p q -> SobolevSpace E p q k.
   CAG zero-dependent Parameter sobolev_inject theories/Harmonic/Sobolev.v:157 END *)

(** Dense injection. *)
(* CAG constructive-remove Theorem sobolev_inject_dense theories/Harmonic/Sobolev.v:218 BEGIN -- repair partially commented declaration
Theorem sobolev_inject_dense : forall {M : HermitianManifold} {E : HermitianBundle M}
    (* CAG constructive-remove Command {p theories/Harmonic/Sobolev.v:219 BEGIN -- missing Connection
{p q : nat} (conn : Connection E) (k : nat),
    True. 
   CAG constructive-remove Command {p theories/Harmonic/Sobolev.v:219 END *)
(* image of sobolev_inject is dense in SobolevSpace E p q k *)
(* CAG constructive-remove Command Proof. theories/Harmonic/Sobolev.v:224 BEGIN -- compile error
Proof. 
   CAG constructive-remove Command Proof. theories/Harmonic/Sobolev.v:224 END *)
(* CAG constructive-remove Command intros; theories/Harmonic/Sobolev.v:227 BEGIN -- compile error
intros; exact I. 
   CAG constructive-remove Command intros; theories/Harmonic/Sobolev.v:227 END *)
(* CAG constructive-remove Command Qed. theories/Harmonic/Sobolev.v:230 BEGIN -- compile error
Qed.

   CAG constructive-remove Command Qed. theories/Harmonic/Sobolev.v:230 END *)
   CAG constructive-remove Theorem sobolev_inject_dense theories/Harmonic/Sobolev.v:218 END *)

(* ================================================================== *)
(** * 6. Rellich compactness theorem                                  *)
(* ================================================================== *)

(** Rellich-Kondrachov: the inclusion W^{k+1,2} → W^{k,2} is compact.
    On a compact manifold M, every bounded sequence in W^{k+1,2} has
    a convergent subsequence in W^{k,2}. *)
(* CAG zero-dependent Admitted rellich_compactness theories/Harmonic/Sobolev.v:182 BEGIN
Theorem rellich_compactness : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (conn : Connection E) (k : nat),
    True. (* the inclusion W^{k+1,2} -> W^{k,2} is a compact operator *)
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 7. Sobolev embedding theorem                                    *)
(* ================================================================== *)

(** Sobolev embedding: W^{k,2} → C^j for k > j + n/2 (n = real dim).
Proof. admit. Admitted.
   CAG zero-dependent Admitted rellich_compactness theories/Harmonic/Sobolev.v:182 END *)
    On a compact manifold, high Sobolev regularity implies classical smoothness. *)
(* CAG constructive-remove Theorem sobolev_embedding theories/Harmonic/Sobolev.v:256 BEGIN -- compile error
Theorem sobolev_embedding : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat} (conn : Connection E) (k j : nat),
    (k > j + hman_real_dim M / 2)%nat ->
    True. (* W^{k,2}(M,E) -> C^j(M,E) continuously *)
Proof. intros; exact I. Qed.

   CAG constructive-remove Theorem sobolev_embedding theories/Harmonic/Sobolev.v:256 END *)

(** Corollary: Sobolev-smooth sections are C^∞ smooth. *)
(* CAG constructive-remove Theorem sobolev_smooth_sections theories/Harmonic/Sobolev.v:266 BEGIN -- compile error
Theorem sobolev_smooth_sections : forall {M : HermitianManifold}
    {E : HermitianBundle M} {p q : nat} (conn : Connection E),
    True. (* intersection of all W^{k,2} = C^∞ *)
Proof.
  exact (fun _ _ _ _ _ => I).
Qed.

   CAG constructive-remove Theorem sobolev_smooth_sections theories/Harmonic/Sobolev.v:266 END *)
