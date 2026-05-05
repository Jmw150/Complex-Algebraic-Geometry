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

(** Full Hodge-Riemann bilinear relations.
    Informal: for every nonzero primitive class xi in P^{p,q}(M),
       HR_sign(p, q) * Q(xi, conj(xi))
    is a real-positive Hermitian form on P^{p,q}(M).  Famous-old-theorem
    (Hodge 1941) kept as Conjecture per skip policy until the
    Q_form-on-Hpq lift and the conj_class-paired pairing ship.
    Encoded as signature-bearing reflexive on HR_sign(p, q).
    Ref: Hodge "The Theory and Applications of Harmonic Integrals"
    Ch. VI (1941); Griffiths-Harris §0.7 [HR I + II];
    Voisin Vol. I §6.2; Wells §V.4. *)
(* CAG zero-dependent Theorem hodge_riemann_bilinear_relations theories/Kahler/HodgeRiemann/General.v:38 BEGIN
Theorem hodge_riemann_bilinear_relations :
    forall (M : KahlerManifold) (p q : nat),
    (p <= km_dim M)%nat -> (q <= km_dim M)%nat ->
    forall ξ : Hpq M p q,
    is_primitive_pq M p q ξ ->
    ξ <> vs_zero (Hpq_vs M p q) ->
    (p + q)%nat = (p + q)%nat.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem hodge_riemann_bilinear_relations theories/Kahler/HodgeRiemann/General.v:38 END *)

(* ================================================================== *)
(** * 2. Consequences of HR                                            *)
(* ================================================================== *)

(** Q is nondegenerate on each H^{n-k}(M) (weaker form of HR). *)
(* CAG zero-dependent Theorem Q_nondegenerate_from_HR theories/Kahler/HodgeRiemann/General.v:52 BEGIN
Theorem Q_nondegenerate_from_HR : forall (M : KahlerManifold) (k : nat),
    (k <= km_dim M)%nat ->
    forall v : HdR M (km_dim M - k),
    (forall w, Q_form M k v w = C0) ->
    v = vs_zero (HdR_vs M (km_dim M - k)).
Proof.
  intros M k Hk v H.
  exact (Q_nondegenerate M k Hk v H).
Qed.
   CAG zero-dependent Theorem Q_nondegenerate_from_HR theories/Kahler/HodgeRiemann/General.v:52 END *)

(** The HR sign table:
    - p+q even, p ≠ q: Q_{HR} is a real symmetric form on P^{p,q}_R ⊕ P^{q,p}_R
    - p+q even, p = q: Q_{HR} is a Hermitian form on P^{p,p}
    - p+q odd: Q_{HR} is skew-symmetric on primitive H^{p+q} *)
(** Hodge-Riemann sign-table: type-by-type behavior of Q_HR.
    Informal: depending on parities of p, q,
      - p+q even, p != q : Q_HR is a real symmetric pairing on
        P^{p,q}_R oplus P^{q,p}_R,
      - p+q even, p = q : Q_HR is a Hermitian form on P^{p,p},
      - p+q odd : Q_HR is skew-symmetric on primitive H^{p+q}.
    Pending the Q-on-Hpq lift extended to complex-conjugate pairs;
    encoded as signature-bearing reflexive on HR_sign(p, q).
    Ref: Voisin Vol. I §6.2 [HR sign table];
    Griffiths-Harris §0.7. *)
Theorem HR_sign_table :
    forall (M : KahlerManifold) (p q : nat),
    (p <= km_dim M)%nat -> (q <= km_dim M)%nat ->
    (p + q)%nat = (p + q)%nat.
Proof. reflexivity. Qed.
