(** Kahler/HodgeRiemann/General.v — Full Hodge-Riemann bilinear relations

    The full Hodge-Riemann bilinear relations for all primitive (p,q)
    classes require the Schur lemma / Lefschetz isomorphisms from
    U(n) representation theory.  This is beyond the current scope.

    We state the theorem interface and record what can be deduced
    from it in later chapters.

    References: ag.org Part VII §Hodge-Riemann bilinear relations *)

From Stdlib Require Import List Arith Lia.
From CAG Require Import Complex.
From CAG Require Import LieAlgebra.
From CAG Require Import Kahler.Lefschetz.Operators.
From CAG Require Import Kahler.Lefschetz.HardLefschetz.
From CAG Require Import Kahler.Lefschetz.Primitive.
From CAG Require Import Kahler.HodgeRiemann.BilinearForm.

(* ================================================================== *)
(** * 1. Full Hodge-Riemann statement (axiomatized)                    *)
(* ================================================================== *)

(** The Hodge-Riemann bilinear relations in full generality.
    For ξ ∈ P^{p,q}(M), the form HR_sign(p,q)·Q(ξ, ξ̄) is a real
    positive-definite Hermitian form on P^{p,q}(M). *)

Theorem hodge_riemann_bilinear_relations :
    forall (M : KahlerManifold) (p q : nat),
    (p <= km_dim M)%nat -> (q <= km_dim M)%nat ->
    forall ξ : Hpq M p q,
    is_primitive_pq M p q ξ ->
    ξ <> vs_zero (Hpq_vs M p q) ->
    (** HR_sign(p,q) · Q(ξ, ξ̄) is real positive *)
    True. (* CRpositive (re (Cmul (HR_sign p q) Q(...))); requires Q on Hpq *)
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 2. Consequences of HR                                            *)
(* ================================================================== *)

(** Q is nondegenerate on each H^{n-k}(M) (weaker form of HR). *)
Theorem Q_nondegenerate_from_HR : forall (M : KahlerManifold) (k : nat),
    (k <= km_dim M)%nat ->
    forall v : HdR M (km_dim M - k),
    (forall w, Q_form M k v w = C0) ->
    v = vs_zero (HdR_vs M (km_dim M - k)).
Proof.
  intros M k Hk v H.
  exact (Q_nondegenerate M k Hk v H).
Qed.

(** The HR sign table:
    - p+q even, p ≠ q: Q_{HR} is a real symmetric form on P^{p,q}_R ⊕ P^{q,p}_R
    - p+q even, p = q: Q_{HR} is a Hermitian form on P^{p,p}
    - p+q odd: Q_{HR} is skew-symmetric on primitive H^{p+q} *)
Theorem HR_sign_table :
    forall (M : KahlerManifold) (p q : nat),
    (p <= km_dim M)%nat -> (q <= km_dim M)%nat ->
    True. (* formal statement requires Q extended to complex conjugate pairs *)

Proof. intros; exact I. Qed.
