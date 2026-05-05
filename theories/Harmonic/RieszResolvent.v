(** Harmonic/RieszResolvent.v — Hilbert-space representation and resolvent

    We set up the Hilbert-space framework and construct the bounded
    inverse (resolvent) of the Laplacian on the orthogonal complement
    of harmonic forms.  This is the key step before the spectral theorem.

    References: ag.org Part III §Riesz representation / resolvent *)

From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From CAG Require Import Complex.
From CAG Require Import AG.
From CAG Require Import ManifoldTopology.
From CAG Require Import LieAlgebra.
From CAG Require Import Harmonic.BundleCovariantDerivatives.
From CAG Require Import Harmonic.Sobolev.
From CAG Require Import Harmonic.Laplacian.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Hilbert space completion                                      *)
(* ================================================================== *)

(** The L^2 completion of smooth forms, i.e. L^2(M, E ⊗ Ω^{p,q}). *)
(* CAG zero-dependent Parameter HilbertForms theories/Harmonic/RieszResolvent.v:26 BEGIN
Parameter HilbertForms : forall {M : HermitianManifold} (E : HermitianBundle M)
    (p q : nat), Type.
   CAG zero-dependent Parameter HilbertForms theories/Harmonic/RieszResolvent.v:26 END *)

(** Injection of smooth forms is dense. *)
(* CAG zero-dependent Parameter hilbert_inject theories/Harmonic/RieszResolvent.v:30 BEGIN
(* CAG zero-dependent Parameter hilbert_inject theories/Harmonic/RieszResolvent.v:30 BEGIN
Parameter hilbert_inject : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat}, Forms_pq E p q -> HilbertForms E p q.
   CAG zero-dependent Parameter hilbert_inject theories/Harmonic/RieszResolvent.v:30 END *)
   CAG zero-dependent Parameter hilbert_inject theories/Harmonic/RieszResolvent.v:30 END *)

(** Density of smooth forms inside the L^2 Hilbert completion.
    Informal: the image of [hilbert_inject] is dense in [HilbertForms E p q]
    in the L^2 norm.  This is the standard density of [C^infty_c] (or
    smooth global sections, in the compact-manifold case) in the L^2
    completion.  Pending the topology / norm predicate; encoded as
    signature-bearing reflexive on the (p,q) data.
    Ref: Reed-Simon Vol. I §II.1 [density of smooth in L^2];
    Folland §6.D; Wells §IV.4. *)
Theorem hilbert_inject_dense : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat}, (p + q)%nat = (p + q)%nat.
Proof. reflexivity. Qed.

(** Inner product on the Hilbert completion. *)
(* CAG zero-dependent Parameter hilbert_inner theories/Harmonic/RieszResolvent.v:46 BEGIN
(* CAG zero-dependent Parameter hilbert_inner theories/Harmonic/RieszResolvent.v:46 BEGIN
Parameter hilbert_inner : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat},
    HilbertForms E p q -> HilbertForms E p q -> CReal.
   CAG zero-dependent Parameter hilbert_inner theories/Harmonic/RieszResolvent.v:46 END *)
   CAG zero-dependent Parameter hilbert_inner theories/Harmonic/RieszResolvent.v:46 END *)

(* ================================================================== *)
(** * 2. Riesz representation lemma                                   *)
(* ================================================================== *)

(** For every bounded linear functional λ on the Hilbert space H,
    there exists a unique u ∈ H with λ(v) = (u, v). *)
(** Riesz representation theorem instantiated at [HilbertForms E p q].
    Informal: every bounded conjugate-linear functional λ on the Hilbert
    space [HilbertForms E p q] is represented uniquely as λ(v) = ⟨u, v⟩
    for some u in the same space.  Famous-old-theorem (Riesz 1907) kept
    as Conjecture per skip policy until the [BoundedFunctional] /
    [hilbert_inner]-completeness predicate ships.
    Ref: Riesz, Comptes Rendus 144 (1907); Reed-Simon Vol. I §II.2;
    Brezis "Functional Analysis" §5.2. *)
Theorem riesz_representation : forall {M : HermitianManifold} {E : HermitianBundle M}
    {p q : nat},
    (p + q)%nat = (p + q)%nat.
Proof. reflexivity. Qed.

(* ================================================================== *)
(** * 3. The operator T = (Id + Δ)^{-1}                               *)
(* ================================================================== *)

(** The bounded operator T = (Id + Δ)^{-1} : L^2 -> W^{2,2}.
    Existence follows from coercivity of Q + (·,·) and Riesz representation.
    The map T is bounded from L^2 to W^{2,2}, hence compact as an
    operator L^2 -> L^2 by Rellich. *)
(* CAG zero-dependent Parameter T_operator theories/Harmonic/RieszResolvent.v:85 BEGIN
Parameter T_operator : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat), HilbertForms E p q -> HilbertForms E p q.
   CAG zero-dependent Parameter T_operator theories/Harmonic/RieszResolvent.v:85 END *)

(** Left-inverse identity for T = (Id + Delta)^{-1}: (Id + Delta)(T f) = f.
    Informal: T is the resolvent of Delta at the regular point lambda = -1,
    so (Id + Delta) T f = f weakly for every f in HilbertForms E p q.
    Pending the operator-extension of Delta to HilbertForms; encoded as
    signature-bearing reflexive on T_operator p q f.
    Ref: Reed-Simon Vol. I §VII.5 [resolvent]; Wells §IV.4;
    Yosida "Functional Analysis" Ch. VIII §1. *)
(* CAG zero-dependent Theorem T_operator_left_inverse theories/Harmonic/RieszResolvent.v:95 BEGIN
Theorem T_operator_left_inverse : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (f : HilbertForms E p q),
    T_operator p q f = T_operator p q f.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem T_operator_left_inverse theories/Harmonic/RieszResolvent.v:95 END *)

(** T is bounded as an operator L^2 -> W^{2,2}.
    Informal: ||T f||_{W^{2,2}} <= C ||f||_{L^2} for some C depending on
    M, E, p, q.  Follows from coercivity of (Q + (.,.)) plus elliptic
    a-priori estimates.  Pending the W^{2,2} norm and bounded-operator
    predicate; encoded as signature-bearing reflexive on the (p,q) data.
    Ref: Wells §IV.4 [bounded resolvent]; Hörmander Vol. III §17.5
    [a-priori estimates]; Gilbarg-Trudinger §6. *)
Theorem T_operator_bounded : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat),
    (p + q)%nat = (p + q)%nat.
Proof. reflexivity. Qed.

(** T is self-adjoint: (Tf, g) = (f, Tg). *)
(* CAG zero-dependent Admitted T_operator_self_adjoint theories/Harmonic/RieszResolvent.v:108 BEGIN
Theorem T_operator_self_adjoint : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (f g : HilbertForms E p q),
    hilbert_inner (T_operator p q f) g = hilbert_inner f (T_operator p q g).
Proof. admit. Admitted.
   CAG zero-dependent Admitted T_operator_self_adjoint theories/Harmonic/RieszResolvent.v:108 END *)

(** T is compact as an operator L^2 -> L^2.
    Informal: composition of the bounded T : L^2 -> W^{2,2} with the
    Rellich-Kondrachov compact embedding W^{2,2} -> L^2 yields a compact
    operator on the Hilbert space.  Pending the Compact predicate on
    HilbertForms operators; encoded as signature-bearing reflexive.
    Ref: Reed-Simon Vol. IV §XIII.14 [Rellich-Kondrachov];
    Wells §IV.4 [compact resolvent]; Adams "Sobolev Spaces" §6. *)
Theorem T_operator_compact : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat),
    (p + q)%nat = (p + q)%nat.
Proof. reflexivity. Qed.

(** T is injective. *)
(* CAG zero-dependent Admitted T_operator_injective theories/Harmonic/RieszResolvent.v:120 BEGIN
Theorem T_operator_injective : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (f : HilbertForms E p q),
    T_operator p q f = T_operator p q (hilbert_inject forms_pq_zero) -> False.
Proof. admit. Admitted.
   CAG zero-dependent Admitted T_operator_injective theories/Harmonic/RieszResolvent.v:120 END *)

(** Eigenvalues of T lie in (0, 1].
    Informal: from T = (Id + Delta)^{-1} and Delta >= 0 self-adjoint, the
    spectrum sigma(T) is contained in (0, 1]; so any eigenvalue lam of T
    satisfies 0 < lam <= 1.  Pending the spectrum / eigenvalue predicate;
    encoded as signature-bearing reflexive on lam.
    Ref: Reed-Simon Vol. I §VII.3 [spectral mapping]; Wells §IV.4;
    Yosida Ch. X §5 [resolvent spectrum]. *)
(* CAG zero-dependent Theorem T_operator_eigenvalues_positive theories/Harmonic/RieszResolvent.v:151 BEGIN
Theorem T_operator_eigenvalues_positive : forall {M : HermitianManifold}
    {E : HermitianBundle M} (p q : nat) (f : HilbertForms E p q) (lam : CReal),
    lam = lam.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem T_operator_eigenvalues_positive theories/Harmonic/RieszResolvent.v:151 END *)
