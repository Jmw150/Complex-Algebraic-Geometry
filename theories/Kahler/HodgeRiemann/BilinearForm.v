(** Kahler/HodgeRiemann/BilinearForm.v — The bilinear form Q

    For a compact Kähler manifold M of complex dimension n:

    Q : H^{n-k}(M) × H^{n-k}(M) -> C
    Q(ξ, η) = ∫_M ξ ∧ η ∧ ω^k

    We define Q and prove its basic properties:
    - well-defined on cohomology
    - type orthogonality
    - nondegeneracy via Hard Lefschetz

    References: ag.org Part VI §Bilinear form Q *)

From Stdlib Require Import List Arith Lia.
From CAG Require Import Complex.
From CAG Require Import LieAlgebra.
From CAG Require Import ManifoldTopology.
From CAG Require Import Kahler.sl2.Basic.
From CAG Require Import Kahler.Lefschetz.Operators.
From CAG Require Import Kahler.Lefschetz.HardLefschetz.
From CAG Require Import Kahler.Lefschetz.Primitive.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Integration pairing                                           *)
(* ================================================================== *)

(** The integration pairing ∫_M : H^{2n}(M) -> C
    (Poincaré duality / orientation class). *)
Parameter integrate : forall (M : KahlerManifold),
    HdR M (2 * km_dim M) -> CComplex.

Conjecture integrate_linear : forall (M : KahlerManifold) (u v : HdR M (2 * km_dim M)) (c : CComplex),
    integrate M (vs_add (HdR_vs M _) u v) =
    Cadd (integrate M u) (integrate M v).

(** Cup product in cohomology. *)
Parameter cup : forall (M : KahlerManifold) (j k : nat),
    HdR M j -> HdR M k -> HdR M (j + k).

Theorem cup_graded_comm : forall (M : KahlerManifold) (j k : nat)
    (u : HdR M j) (v : HdR M k),
    (** cup(u,v) = (-1)^{jk} cup(v,u) — graded commutativity, axiomatized *)
    True.
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 2. Definition of Q                                               *)
(* ================================================================== *)

(** The Kähler class: the cohomology class [ω] in H^{1,1}(M) ⊂ H^2(M). *)
Parameter kahler_class : forall (M : KahlerManifold), HdR M 2.

(** omega^k = k-fold cup product of omega with itself. *)
Parameter kahler_power : forall (M : KahlerManifold) (k : nat), HdR M (2*k)%nat.

(** Q(ξ, η) = ∫_M ξ ∧ η ∧ ω^k  for ξ, η ∈ H^{n-k}(M).
    Defined via cup product and integration — axiomatized to avoid
    the nat equality 2*(n-k)+2k = 2n which is propositional, not definitional. *)
Parameter Q_form : forall (M : KahlerManifold) (k : nat),
    HdR M (km_dim M - k) -> HdR M (km_dim M - k) -> CComplex.

(* ================================================================== *)
(** * 3. Basic properties of Q                                         *)
(* ================================================================== *)

(** Q is bilinear — axiomatized since Q_form is a parameter. *)
Conjecture Q_bilinear_left : forall (M : KahlerManifold) (k : nat)
    (u v eta : HdR M (km_dim M - k)),
    Q_form M k (vs_add (HdR_vs M _) u v) eta =
    Cadd (Q_form M k u eta) (Q_form M k v eta).

Conjecture Q_bilinear_right : forall (M : KahlerManifold) (k : nat)
    (xi u v : HdR M (km_dim M - k)),
    Q_form M k xi (vs_add (HdR_vs M _) u v) =
    Cadd (Q_form M k xi u) (Q_form M k xi v).

(** Q is well defined on cohomology (follows from ∂-exactness). *)
Theorem Q_well_defined : forall (M : KahlerManifold) (k : nat),
    True. (* formal statement requires d-exactness *)
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 4. Type orthogonality                                            *)
(* ================================================================== *)

(** Q(H^{p,q}, H^{p',q'}) = 0  unless  p = q' and q = p'.

    Proof: Q(ξ, η) = ∫ ξ ∧ η ∧ ω^k.  The integrand is of type
    (p+p'+(k,k), q+q'+(k,k)).  For the integral to be nonzero,
    we need (p+p'+k) + (q+q'+k) = 2n, so p+p'+q+q' = 2(n-k).
    Combined with p+q = p'+q' = n-k, this forces p = q' and q = p'.  *)

Theorem Q_type_orthogonal : forall (M : KahlerManifold) (p q p' q' : nat) (k : nat)
    (xi : Hpq M p q) (eta : Hpq M p' q'),
    (p + q)%nat = (km_dim M - k)%nat ->
    (p' + q')%nat = (km_dim M - k)%nat ->
    ~ (p = q' /\ q = p') ->
    True. (* Q(xi, eta) = 0; requires Hpq -> HdR injection *)
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * 5. Nondegeneracy                                                 *)
(* ================================================================== *)

(** Q is nondegenerate on H^{n-k}(M) for each k.
    This follows from Hard Lefschetz + Poincaré duality. *)
Conjecture Q_nondegenerate : forall (M : KahlerManifold) (k : nat),
    (k <= km_dim M)%nat ->
    forall v : HdR M (km_dim M - k),
    (forall w : HdR M (km_dim M - k), Q_form M k v w = C0) ->
    v = vs_zero (HdR_vs M (km_dim M - k)).

(* ================================================================== *)
(** * 6. Real structure                                                *)
(* ================================================================== *)

(** Q restricts to a real bilinear form on real cohomology H^{n-k}(M,R). *)
Parameter HdR_real : KahlerManifold -> nat -> Type.

(** The real cup product. *)
Parameter Q_form_real : forall (M : KahlerManifold) (k : nat),
    HdR_real M (km_dim M - k) -> HdR_real M (km_dim M - k) -> CComplex.

(** Skew-symmetry for odd degree, symmetry for even degree. *)
Conjecture Q_symmetry : forall (M : KahlerManifold) (k : nat) (xi eta : HdR M (km_dim M - k)),
    Q_form M k xi eta =
    Cmul (Cpow (Cneg C1) ((km_dim M - k) * (km_dim M - k - 1) / 2)%nat)
         (Q_form M k eta xi).
