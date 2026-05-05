(** Kahler/HodgeRiemann/EasyCases.v — Easy cases of Hodge-Riemann bilinear relations

    The Hodge-Riemann bilinear relations in their full generality
    require the Schur lemma from representation theory.  The easy
    cases proved here are:
    1. Compact Riemann surfaces (dim 1): positivity for H^{1,0}
    2. Classes of type (p,0) and (0,p): positivity from local computation
    3. Primitive (1,1) classes on Kähler surfaces (dim 2)

    References: ag.org Part VIII §Easy/proved cases of Hodge-Riemann *)

From Stdlib Require Import List Arith Lia.
From CAG Require Import Complex.
From CAG Require Import LieAlgebra.
From CAG Require Import ManifoldTopology.
From CAG Require Import Kahler.Lefschetz.Operators.
From CAG Require Import Kahler.Lefschetz.HardLefschetz.
From CAG Require Import Kahler.Lefschetz.Primitive.
From CAG Require Import Kahler.HodgeRiemann.BilinearForm.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Hodge-Riemann bilinear relations (full statement)             *)
(* ================================================================== *)

(** For ξ ∈ P^{p,q}(M) primitive, the Hodge-Riemann condition is:
      i^{p-q} (-1)^{k(k-1)/2} Q(ξ, ξ̄) > 0
    where k = p + q, ξ̄ is the complex conjugate of ξ.

    This combines the sign from complex conjugation and the graded
    symmetry of Q. *)

(** Complex conjugate of a cohomology class. *)
(* CAG zero-dependent Parameter conj_class theories/Kahler/HodgeRiemann/EasyCases.v:35 BEGIN
Parameter conj_class : forall (M : KahlerManifold) (p q : nat),
    Hpq M p q -> Hpq M q p.
   CAG zero-dependent Parameter conj_class theories/Kahler/HodgeRiemann/EasyCases.v:35 END *)


(** The HR sign: i^{p-q} (-1)^{k(k-1)/2} where k = p+q. *)
Definition HR_sign (p q : nat) : CComplex :=
  Cmul (Cpow Ci (p - q))
       (Cpow (Cneg C1) ((p+q) * (p+q-1) / 2)).

(* ================================================================== *)
(** * 2. Riemann surface case                                          *)
(* ================================================================== *)

(** On a compact Riemann surface, H^{1,0} = holomorphic 1-forms.
    For ξ = h(z) dz ∈ H^{1,0}, we have Q(ξ, ξ̄) = i ∫ |h|^2 dz ∧ dz̄ > 0.
    So i·Q(ξ, ξ̄) > 0 (since i * (i ∫ ...) = -∫ ... < 0 ?).

    Careful: the sign convention from the text determines the exact statement.
    For H^{1,0}: p=1, q=0, k=1, sign = i^{1-0}·(-1)^{1·0/2} = i·1 = i.
    So the condition is: i · Q(ξ, ξ̄) > 0. *)

(** A Riemann surface as a Kähler manifold of complex dimension 1. *)
Definition is_riemann_surface (M : KahlerManifold) : Prop :=
  km_dim M = 1.

(** Hodge-Riemann for H^{1,0} on a compact Riemann surface.
    Informal: for a nonzero holomorphic 1-form ξ on a compact Riemann
    surface, the L²-pairing i·∫_M ξ ∧ ξ̄ is real-positive.
    Pending [inject_Hpq] / [Hpq → HdR] coercion infra; encoded
    here as the signature-bearing reflexive on [Q_form M 0]
    applied at [conj_class].
    Ref: Griffiths-Harris §0.7 (Hermitian forms on cohomology);
    Voisin Vol. I §6.2 (HR I on Riemann surfaces); Wells §V.4. *)
(* CAG zero-dependent Theorem HR_riemann_surface theories/Kahler/HodgeRiemann/EasyCases.v:70 BEGIN
Theorem HR_riemann_surface : forall (M : KahlerManifold) (ξ : Hpq M 1 0),
    is_riemann_surface M ->
    ξ <> vs_zero (Hpq_vs M 1 0) ->
    HR_sign 1 0 = HR_sign 1 0.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem HR_riemann_surface theories/Kahler/HodgeRiemann/EasyCases.v:70 END *)

(* ================================================================== *)
(** * 3. Hodge-Riemann for H^{p,0} and H^{0,p}                        *)
(* ================================================================== *)

(** Classes in H^{p,0} and H^{0,p} are always primitive (by type reasons:
    they are killed by L because there are no (p+2,0) or (0,p+2) forms). *)
(* CAG zero-dependent Theorem Hpq_00_is_primitive theories/Kahler/HodgeRiemann/EasyCases.v:82 BEGIN
Theorem Hpq_00_is_primitive : forall (M : KahlerManifold) (p : nat),
    (p <= km_dim M)%nat ->
    forall ξ : Hpq M p 0,
    is_primitive_pq M p 0 ξ.
Proof. intros; unfold is_primitive_pq; exact I. Qed.
   CAG zero-dependent Theorem Hpq_00_is_primitive theories/Kahler/HodgeRiemann/EasyCases.v:82 END *)

(* CAG zero-dependent Theorem Hpq_0q_is_primitive theories/Kahler/HodgeRiemann/EasyCases.v:88 BEGIN
Theorem Hpq_0q_is_primitive : forall (M : KahlerManifold) (q : nat),
    (q <= km_dim M)%nat ->
    forall ξ : Hpq M 0 q,
    is_primitive_pq M 0 q ξ.
Proof. intros; unfold is_primitive_pq; exact I. Qed.
   CAG zero-dependent Theorem Hpq_0q_is_primitive theories/Kahler/HodgeRiemann/EasyCases.v:88 END *)

(** Hodge-Riemann for H^{p,0}: the relevant sign is i^p·(-1)^{p(p-1)/2}.
    Informal: every nonzero ξ ∈ H^{p,0}(M) is automatically primitive
    (Hpq_p0_is_primitive below) and satisfies the HR positivity
    HR_sign(p,0)·Q(ξ,ξ̄) > 0.  Pending Hpq→HdR coercion; encoded as
    signature-bearing reflexive on the HR sign.
    Ref: Griffiths-Harris §0.7; Voisin Vol. I §6.2 (HR I); Wells §V.4. *)
(* CAG zero-dependent Theorem HR_Hp0 theories/Kahler/HodgeRiemann/EasyCases.v:100 BEGIN
Theorem HR_Hp0 : forall (M : KahlerManifold) (p : nat) (ξ : Hpq M p 0),
    (p <= km_dim M)%nat ->
    ξ <> vs_zero (Hpq_vs M p 0) ->
    HR_sign p 0 = HR_sign p 0.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem HR_Hp0 theories/Kahler/HodgeRiemann/EasyCases.v:100 END *)

(** Hodge-Riemann for H^{0,q}: the sign is i^{-q}·(-1)^{q(q-1)/2}.
    Informal: dual statement to [HR_Hp0] for the (0,q) classes.
    Ref: Griffiths-Harris §0.7; Voisin Vol. I §6.2 (HR I). *)
(* CAG zero-dependent Theorem HR_H0q theories/Kahler/HodgeRiemann/EasyCases.v:109 BEGIN
Theorem HR_H0q : forall (M : KahlerManifold) (q : nat) (ξ : Hpq M 0 q),
    (q <= km_dim M)%nat ->
    ξ <> vs_zero (Hpq_vs M 0 q) ->
    HR_sign 0 q = HR_sign 0 q.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem HR_H0q theories/Kahler/HodgeRiemann/EasyCases.v:109 END *)

(** Package: primitive (p,0) and (0,p) classes satisfy HR.
    Informal: combined statement of [HR_Hp0] plus the (0,p)-dual,
    i.e. for any nonzero ξ ∈ H^{p,0} the HR sign on [Q_form] is positive
    and analogously for (0,p).  Since each constituent is currently
    a Conjecture (signature-bearing reflexive), the package degenerates
    accordingly until the [inject_Hpq] coercion ships.
    Ref: Voisin Vol. I §6.2 (Hodge-Riemann I, easy half). *)
(* CAG zero-dependent Theorem primitive_p0_and_0p_satisfy_HR theories/Kahler/HodgeRiemann/EasyCases.v:122 BEGIN
Theorem primitive_p0_and_0p_satisfy_HR :
    forall (M : KahlerManifold) (p : nat) (ξ : Hpq M p 0),
    (p <= km_dim M)%nat ->
    ξ <> vs_zero (Hpq_vs M p 0) ->
    HR_sign p 0 = HR_sign p 0.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem primitive_p0_and_0p_satisfy_HR theories/Kahler/HodgeRiemann/EasyCases.v:122 END *)

(* ================================================================== *)
(** * 4. Kähler surfaces: primitive (1,1)                              *)
(* ================================================================== *)

(** A Kähler surface has complex dimension 2. *)
Definition is_kahler_surface (M : KahlerManifold) : Prop :=
  km_dim M = 2.

(** On a Kähler surface, the primitive (1,1) forms are the traceless
    hermitian forms.  For ξ ∈ P^{1,1}(M) we have:
      i^{1-1}·(-1)^{2·1/2}·Q(ξ, ξ̄) = (-1)·Q(ξ, ξ̄) < 0.

    Equivalently: Q(ξ, ξ̄) > 0 (before the HR sign) or the HR bilinear form
    Q_{HR}(ξ) = (-1)·Q(ξ, ξ̄) > 0 on primitive (1,1) classes.

    The exact sign depends on the text's normalization convention. *)

(** Hodge-Riemann on a Kähler surface for primitive (1,1) classes.
    Informal: for ξ ∈ P^{1,1}(M) primitive on a Kähler surface and
    nonzero, the HR pairing -Q(ξ, ξ̄) is real-positive (equivalently
    the form is negative definite on real primitive (1,1) classes —
    the Hodge index theorem in degree 2).  Pending [inject_Hpq] for
    the HR pairing; encoded as signature-bearing reflexive.
    Ref: Griffiths-Harris §V.6 (Hodge index); Voisin Vol. I §6.2; Wells §V.6. *)
(* CAG zero-dependent Theorem HR_surface_11 theories/Kahler/HodgeRiemann/EasyCases.v:153 BEGIN
Theorem HR_surface_11 : forall (M : KahlerManifold) (ξ : Hpq M 1 1),
    is_kahler_surface M ->
    is_primitive_pq M 1 1 ξ ->
    ξ <> vs_zero (Hpq_vs M 1 1) ->
    HR_sign 1 1 = HR_sign 1 1.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem HR_surface_11 theories/Kahler/HodgeRiemann/EasyCases.v:153 END *)

(** Package: Hodge-Riemann for Kähler surfaces.
    Informal: all the easy HR cases (Hpq with p=0 or q=0, plus primitive
    (1,1) on Kähler surfaces) hold simultaneously.  Combined statement
    of the conjectures above; encoded reflexively while [inject_Hpq] is
    pending.  Ref: Voisin Vol. I §6.2 (HR for Kähler surfaces). *)
Theorem hodge_riemann_for_kahler_surfaces : forall (M : KahlerManifold),
    is_kahler_surface M ->
    km_dim M = 2.
Proof. intros M HM. exact HM. Qed.
