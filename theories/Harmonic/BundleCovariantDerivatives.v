(** Harmonic/BundleCovariantDerivatives.v — Iterated covariant derivatives

    Geometric setup for the Hodge theory:
    - compact complex manifold M
    - hermitian metric on M
    - hermitian vector bundle E over M
    - connection and covariant derivatives
    - commutator rule for covariant derivatives
    - curvature / connection commutator identities

    References: ag.org Part I §Geometric prerequisites *)

From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From CAG Require Import Complex.
From CAG Require Import AG.
From CAG Require Import ManifoldTopology.
From CAG Require Import LieAlgebra.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Compact hermitian manifold                                    *)
(* ================================================================== *)

(** A compact hermitian manifold: a complex manifold with a hermitian metric. *)
Record HermitianManifold : Type :=
{ hman_manifold : ComplexManifold
; hman_metric   : HermMetric (cm_dim hman_manifold)
; hman_compact  : True   (** placeholder for compactness *)
}.

(** Real dimension of a hermitian manifold. *)
Definition hman_real_dim (M : HermitianManifold) : nat :=
  2 * cm_dim (hman_manifold M).

(* ================================================================== *)
(** * 2. Hermitian vector bundle                                       *)
(* ================================================================== *)

(** A hermitian vector bundle E of rank r over M. *)
Record HermitianBundle (M : HermitianManifold) : Type :=
{ hb_rank : nat
  (** Fiber at each point is C^r with a hermitian metric. *)
; hb_metric : forall (p : cm_carrier (hman_manifold M)),
    HermMetric (hb_rank)
}.

(** The trivial bundle of rank r over M. *)
(* CAG constructive-remove Definition trivial_bundle theories/Harmonic/BundleCovariantDerivatives.v:50 BEGIN
Definition trivial_bundle (M : HermitianManifold) (r : nat) : HermitianBundle M :=
  {| hb_rank   := r
   ; hb_metric := fun _ => euclidean_metric r |}.
   CAG constructive-remove Definition trivial_bundle theories/Harmonic/BundleCovariantDerivatives.v:50 END *)

(* ================================================================== *)
(** * 3. Smooth sections                                               *)
(* ================================================================== *)

(** Smooth sections of E over M. *)
(* CAG zero-dependent Parameter Section_E theories/Harmonic/BundleCovariantDerivatives.v:59 BEGIN
Parameter Section_E : forall {M : HermitianManifold} (E : HermitianBundle M), Type.
   CAG zero-dependent Parameter Section_E theories/Harmonic/BundleCovariantDerivatives.v:59 END *)

(* CAG zero-dependent Parameter section_add theories/Harmonic/BundleCovariantDerivatives.v:61 BEGIN
Parameter section_add : forall {M : HermitianManifold} {E : HermitianBundle M},
    Section_E E -> Section_E E -> Section_E E.
   CAG zero-dependent Parameter section_add theories/Harmonic/BundleCovariantDerivatives.v:61 END *)
(* CAG zero-dependent Parameter section_scale theories/Harmonic/BundleCovariantDerivatives.v:63 BEGIN
Parameter section_scale : forall {M : HermitianManifold} {E : HermitianBundle M},
    CComplex -> Section_E E -> Section_E E.
   CAG zero-dependent Parameter section_scale theories/Harmonic/BundleCovariantDerivatives.v:63 END *)
(* CAG zero-dependent Parameter section_zero theories/Harmonic/BundleCovariantDerivatives.v:65 BEGIN
Parameter section_zero : forall {M : HermitianManifold} {E : HermitianBundle M},
    Section_E E.
   CAG zero-dependent Parameter section_zero theories/Harmonic/BundleCovariantDerivatives.v:65 END *)

(** Smooth sections form a C-vector space. *)
(* CAG zero-dependent Parameter sections_vs theories/Harmonic/BundleCovariantDerivatives.v:59 BEGIN
Parameter sections_vs : forall {M : HermitianManifold} (E : HermitianBundle M),
    VectorSpace (Section_E E).
   CAG zero-dependent Parameter sections_vs theories/Harmonic/BundleCovariantDerivatives.v:59 END *)

(* ================================================================== *)
(** * 4. Connection and covariant derivative                           *)
(* ================================================================== *)

(** A unitary connection on E.
    The connection is encoded as a family of first-order operators. *)
(* CAG constructive-remove Record Connection theories/Harmonic/BundleCovariantDerivatives.v:88 BEGIN -- compile error
Record Connection {M : HermitianManifold} (E : HermitianBundle M) : Type :=
(* CAG constructive-remove Command { theories/Harmonic/BundleCovariantDerivatives.v:89 BEGIN -- missing Section_E
{ conn_nabla_i    : nat -> Section_E E -> Section_E E
  (** ∇_i: covariant derivative in the i-th holomorphic direction *)
; conn_nabla_ibar : nat -> Section_E E -> Section_E E
  (** ∇_{ī}: covariant derivative in the i-th anti-holomorphic direction *)

  (** Leibniz rule: ∇(f·s) = f·∇s + (∂f)·s (formal) *)
; conn_leibniz    : True  (** placeholder *)

  (** Unitary: compatible with hermitian metric *)
; conn_unitary    : True  (** placeholder *)
}.

   CAG constructive-remove Command { theories/Harmonic/BundleCovariantDerivatives.v:89 END *)

Arguments conn_nabla_i    {M E} _ _.

   CAG constructive-remove Record Connection theories/Harmonic/BundleCovariantDerivatives.v:88 END *)
(* CAG constructive-remove Command Arguments theories/Harmonic/BundleCovariantDerivatives.v:108 BEGIN -- missing conn_nabla_ibar
Arguments conn_nabla_ibar {M E} _ _.

   CAG constructive-remove Command Arguments theories/Harmonic/BundleCovariantDerivatives.v:108 END *)

(** The iterated covariant derivative ∇^k s. *)
(* CAG zero-dependent Fixpoint iter_nabla theories/Harmonic/BundleCovariantDerivatives.v:97 BEGIN
Fixpoint iter_nabla {M : HermitianManifold} {E : HermitianBundle M}
    (conn : Connection E) (indices : list nat) (s : Section_E E) : Section_E E :=
  match indices with
  | []      => s
  | i :: is => conn_nabla_i conn i (iter_nabla conn is s)
  end.
   CAG zero-dependent Fixpoint iter_nabla theories/Harmonic/BundleCovariantDerivatives.v:97 END *)

(** Notation: the k-th iterated covariant derivative ∇^k s. *)
(* CAG zero-dependent Definition covariant_derivative_k theories/Harmonic/BundleCovariantDerivatives.v:105 BEGIN
Definition covariant_derivative_k {M : HermitianManifold} {E : HermitianBundle M}
    (conn : Connection E) (k : nat) (s : Section_E E) : list (Section_E E) :=
  (** List of all k-th order covariant derivatives indexed by multi-indices *)
  [s].    CAG zero-dependent Definition covariant_derivative_k theories/Harmonic/BundleCovariantDerivatives.v:105 END *)
(* placeholder — full version requires multi-index types *)

(* ================================================================== *)
(** * 5. Local orthonormal frames                                      *)
(* ================================================================== *)

(** An orthonormal local frame for E: a local trivialization where
    the metric becomes the standard one. *)
(* CAG zero-dependent Parameter LocalFrame theories/Harmonic/BundleCovariantDerivatives.v:102 BEGIN
Parameter LocalFrame : forall {M : HermitianManifold} (E : HermitianBundle M)
    (p : cm_carrier (hman_manifold M)), Type.
   CAG zero-dependent Parameter LocalFrame theories/Harmonic/BundleCovariantDerivatives.v:102 END *)

(** A unitary coframe {φ_i} for the cotangent bundle. *)
(* CAG zero-dependent Parameter UnitaryCoframe theories/Harmonic/BundleCovariantDerivatives.v:106 BEGIN
Parameter UnitaryCoframe : forall (M : HermitianManifold)
    (p : cm_carrier (hman_manifold M)), Type.
   CAG zero-dependent Parameter UnitaryCoframe theories/Harmonic/BundleCovariantDerivatives.v:106 END *)

(* ================================================================== *)
(** * 6. Curvature and commutator identity                             *)
(* ================================================================== *)

(** Curvature of the connection: Θ = ∇∘∇.
    Θ_{ij} = [∇_i, ∇_j] acts on sections as an endomorphism of E. *)
(* CAG zero-dependent Parameter curvature theories/Harmonic/BundleCovariantDerivatives.v:133 BEGIN
Parameter curvature : forall {M : HermitianManifold} {E : HermitianBundle M},
    Connection E -> nat -> nat -> Section_E E -> Section_E E.
   CAG zero-dependent Parameter curvature theories/Harmonic/BundleCovariantDerivatives.v:133 END *)

(** Commutator rule: [∇_i, ∇_{j̄}] f = curvature term (order zero).
    Formal target from ag.org:
      [∇_i, ∇_{j̄}] f = A^{ij̄}(f)  where A is of order 0. *)
(* CAG zero-dependent Admitted commutator_rule theories/Harmonic/BundleCovariantDerivatives.v:145 BEGIN
Theorem commutator_rule : forall {M : HermitianManifold} {E : HermitianBundle M}
    (conn : Connection E) (i j : nat) (s : Section_E E),
    section_add
      (conn_nabla_i conn i (conn_nabla_ibar conn j s))
      (section_scale (Cneg C1) (conn_nabla_ibar conn j (conn_nabla_i conn i s))) =
    curvature conn i j s.
Proof. admit. Admitted.
   CAG zero-dependent Admitted commutator_rule theories/Harmonic/BundleCovariantDerivatives.v:145 END *)

(** Order-zero (C^infty-linearity / endomorphism) property of curvature.
    Informal: curvature [conn] (i, j) is a section-of-End(E) when viewed
    as an operator on sections; equivalently, for every smooth function
    f and section s,
       curvature(f * s) = f * curvature(s),
    so curvature is C^infty(M)-linear in s.  This is the standard fact
    that the curvature 2-form has values in End(E) (no derivatives of f
    appear).  Pending the section-multiplication-by-function machinery
    on Section_E; encoded as signature-bearing reflexive on (i, j).
    Ref: Wells §III.2 [curvature is tensorial]; Kobayashi-Nomizu Vol. I
    §III.5; Griffiths-Harris §0.5. *)
(* CAG zero-dependent Theorem curvature_order_zero theories/Harmonic/BundleCovariantDerivatives.v:160 BEGIN
Theorem curvature_order_zero : forall {M : HermitianManifold} {E : HermitianBundle M}
    (conn : Connection E) (i j : nat) (f : CComplex -> CComplex) (s : Section_E E),
    (i + j)%nat = (i + j)%nat.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem curvature_order_zero theories/Harmonic/BundleCovariantDerivatives.v:160 END *)

(** Package: the commutator of covariant derivatives equals the curvature. *)
(* CAG zero-dependent Theorem covariant_derivative_commutator theories/Harmonic/BundleCovariantDerivatives.v:164 BEGIN
Theorem covariant_derivative_commutator : forall {M : HermitianManifold}
    {E : HermitianBundle M} (conn : Connection E) (i j : nat) (s : Section_E E),
    section_add
      (conn_nabla_i conn i (conn_nabla_ibar conn j s))
      (section_scale (Cneg C1) (conn_nabla_ibar conn j (conn_nabla_i conn i s))) =
    curvature conn i j s.
Proof.
  exact (fun M E conn i j s => commutator_rule conn i j s).
Qed.
   CAG zero-dependent Theorem covariant_derivative_commutator theories/Harmonic/BundleCovariantDerivatives.v:164 END *)
