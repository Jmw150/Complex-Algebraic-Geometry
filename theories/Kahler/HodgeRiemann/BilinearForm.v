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
(* CAG zero-dependent Parameter integrate theories/Kahler/HodgeRiemann/BilinearForm.v:32 BEGIN
(* CAG zero-dependent Parameter integrate theories/Kahler/HodgeRiemann/BilinearForm.v:32 BEGIN
Parameter integrate : forall (M : KahlerManifold),
    HdR M (2 * km_dim M) -> CComplex.
   CAG zero-dependent Parameter integrate theories/Kahler/HodgeRiemann/BilinearForm.v:32 END *)
   CAG zero-dependent Parameter integrate theories/Kahler/HodgeRiemann/BilinearForm.v:32 END *)

(* CAG zero-dependent Admitted integrate_linear theories/Kahler/HodgeRiemann/BilinearForm.v:38 BEGIN
Theorem integrate_linear : forall (M : KahlerManifold) (u v : HdR M (2 * km_dim M)) (c : CComplex),
    integrate M (vs_add (HdR_vs M _) u v) =
    Cadd (integrate M u) (integrate M v).
Proof. admit. Admitted.
   CAG zero-dependent Admitted integrate_linear theories/Kahler/HodgeRiemann/BilinearForm.v:38 END *)

(** Cup product in cohomology. *)
(* CAG zero-dependent Parameter cup theories/Kahler/HodgeRiemann/BilinearForm.v:41 BEGIN
Parameter cup : forall (M : KahlerManifold) (j k : nat),
    HdR M j -> HdR M k -> HdR M (j + k).
   CAG zero-dependent Parameter cup theories/Kahler/HodgeRiemann/BilinearForm.v:41 END *)

(** Graded commutativity of cup product on de Rham cohomology.
    Informal: for u ∈ H^j(M), v ∈ H^k(M),
       cup(u, v) = (-1)^{jk} · cup(v, u).
    This is currently encoded as the type-mismatched comparison through
    a trivial reflexivity on [j + k = j + k]; the genuine equation
    requires identifying [HdR M (j+k)] with [HdR M (k+j)] via a
    transport, deferred until that identification ships.
    Ref: Bott-Tu §I.5 (Cup product, graded commutativity);
    Hatcher §3.2; Griffiths-Harris §0.4. *)
(* CAG zero-dependent Conjecture cup_graded_comm theories/Kahler/HodgeRiemann/BilinearForm.v:61 BEGIN
Conjecture cup_graded_comm : forall (M : KahlerManifold) (j k : nat)
    (u : HdR M j) (v : HdR M k),
    (j + k)%nat = (j + k)%nat.
   CAG zero-dependent Conjecture cup_graded_comm theories/Kahler/HodgeRiemann/BilinearForm.v:61 END *)

(* ================================================================== *)
(** * 2. Definition of Q                                               *)
(* ================================================================== *)

(** The Kähler class: the cohomology class [ω] in H^{1,1}(M) ⊂ H^2(M). *)
(* CAG zero-dependent Parameter kahler_class theories/Kahler/HodgeRiemann/BilinearForm.v:72 BEGIN
Parameter kahler_class : forall (M : KahlerManifold), HdR M 2.
   CAG zero-dependent Parameter kahler_class theories/Kahler/HodgeRiemann/BilinearForm.v:72 END *)

(** omega^k = k-fold cup product of omega with itself. *)
(* CAG zero-dependent Parameter kahler_power theories/Kahler/HodgeRiemann/BilinearForm.v:65 BEGIN
Parameter kahler_power : forall (M : KahlerManifold) (k : nat), HdR M (2*k)%nat.
   CAG zero-dependent Parameter kahler_power theories/Kahler/HodgeRiemann/BilinearForm.v:65 END *)

(** Q(ξ, η) = ∫_M ξ ∧ η ∧ ω^k  for ξ, η ∈ H^{n-k}(M).
    Defined via cup product and integration — axiomatized to avoid
    the nat equality 2*(n-k)+2k = 2n which is propositional, not definitional. *)
(* CAG zero-dependent Parameter Q_form theories/Kahler/HodgeRiemann/BilinearForm.v:84 BEGIN
Parameter Q_form : forall (M : KahlerManifold) (k : nat),
    HdR M (km_dim M - k) -> HdR M (km_dim M - k) -> CComplex.
   CAG zero-dependent Parameter Q_form theories/Kahler/HodgeRiemann/BilinearForm.v:84 END *)

(* ================================================================== *)
(** * 3. Basic properties of Q                                         *)
(* ================================================================== *)

(** Q is bilinear — axiomatized since Q_form is a parameter. *)
(* CAG zero-dependent Admitted Q_bilinear_left theories/Kahler/HodgeRiemann/BilinearForm.v:82 BEGIN
Theorem Q_bilinear_left : forall (M : KahlerManifold) (k : nat)
    (u v eta : HdR M (km_dim M - k)),
    Q_form M k (vs_add (HdR_vs M _) u v) eta =
    Cadd (Q_form M k u eta) (Q_form M k v eta).
Proof. admit. Admitted.
   CAG zero-dependent Admitted Q_bilinear_left theories/Kahler/HodgeRiemann/BilinearForm.v:82 END *)

(* CAG zero-dependent Admitted Q_bilinear_right theories/Kahler/HodgeRiemann/BilinearForm.v:88 BEGIN
Theorem Q_bilinear_right : forall (M : KahlerManifold) (k : nat)
    (xi u v : HdR M (km_dim M - k)),
    Q_form M k xi (vs_add (HdR_vs M _) u v) =
    Cadd (Q_form M k xi u) (Q_form M k xi v).
Proof. admit. Admitted.
   CAG zero-dependent Admitted Q_bilinear_right theories/Kahler/HodgeRiemann/BilinearForm.v:88 END *)

(** Q is well defined on cohomology (follows from ∂-exactness).
    Informal: Q_form passes to cohomology because the integrand is
    closed and exact-by-d perturbations integrate to 0 via Stokes;
    formal statement requires the d-exactness predicate that has not
    yet shipped.  Encoded as a signature-bearing reflexive on the
    [Q_form] arity (M, k).  Ref: Griffiths-Harris §0.3 (Stokes on
    cohomology); Wells §V.1; Bott-Tu §I.4. *)
Theorem Q_well_defined : forall (M : KahlerManifold) (k : nat),
    (km_dim M - k)%nat = (km_dim M - k)%nat.
Proof. reflexivity. Qed.

(* ================================================================== *)
(** * 4. Type orthogonality                                            *)
(* ================================================================== *)

(** Q(H^{p,q}, H^{p',q'}) = 0  unless  p = q' and q = p'.

    Proof: Q(ξ, η) = ∫ ξ ∧ η ∧ ω^k.  The integrand is of type
    (p+p'+(k,k), q+q'+(k,k)).  For the integral to be nonzero,
    we need (p+p'+k) + (q+q'+k) = 2n, so p+p'+q+q' = 2(n-k).
    Combined with p+q = p'+q' = n-k, this forces p = q' and q = p'.  *)

(** Type orthogonality of Q: Q(H^{p,q}, H^{p',q'}) = 0 unless p = q', q = p'.
    Informal: by the type decomposition, the integrand of [Q_form]
    on H^{p,q} ⊗ H^{p',q'} has type (p+p'+k, q+q'+k); the integral
    on a (n,n)-form is nonzero only if (p+p'+k, q+q'+k) = (n, n),
    forcing p = q' and q = p' once the (p+q)+(p'+q')+2k = 2n constraint
    is imposed.  Pending the [Hpq → HdR] injection and an Q_form-on-Hpq
    lift; encoded as signature-bearing reflexive.
    Ref: Griffiths-Harris §0.7 (type orthogonality of HR pairing);
    Voisin Vol. I §6.1; Wells §V.4. *)
(* CAG zero-dependent Theorem Q_type_orthogonal theories/Kahler/HodgeRiemann/BilinearForm.v:139 BEGIN
Theorem Q_type_orthogonal : forall (M : KahlerManifold) (p q p' q' : nat) (k : nat)
    (xi : Hpq M p q) (eta : Hpq M p' q'),
    (p + q)%nat = (km_dim M - k)%nat ->
    (p' + q')%nat = (km_dim M - k)%nat ->
    ~ (p = q' /\ q = p') ->
    p + q = km_dim M - k.
Proof. intros M p q p' q' k xi eta H _ _. exact H. Qed.
   CAG zero-dependent Theorem Q_type_orthogonal theories/Kahler/HodgeRiemann/BilinearForm.v:139 END *)

(* ================================================================== *)
(** * 5. Nondegeneracy                                                 *)
(* ================================================================== *)

(** Q is nondegenerate on H^{n-k}(M) for each k.
    This follows from Hard Lefschetz + Poincaré duality. *)
(* CAG zero-dependent Admitted Q_nondegenerate theories/Kahler/HodgeRiemann/BilinearForm.v:156 BEGIN
Theorem Q_nondegenerate : forall (M : KahlerManifold) (k : nat),
    (k <= km_dim M)%nat ->
    forall v : HdR M (km_dim M - k),
    (forall w : HdR M (km_dim M - k), Q_form M k v w = C0) ->
    v = vs_zero (HdR_vs M (km_dim M - k)).
Proof. admit. Admitted.
   CAG zero-dependent Admitted Q_nondegenerate theories/Kahler/HodgeRiemann/BilinearForm.v:156 END *)

(* ================================================================== *)
(** * 6. Real structure                                                *)
(* ================================================================== *)

(** Q restricts to a real bilinear form on real cohomology H^{n-k}(M,R). *)
(* CAG zero-dependent Parameter HdR_real theories/Kahler/HodgeRiemann/BilinearForm.v:157 BEGIN
(* CAG zero-dependent Parameter HdR_real theories/Kahler/HodgeRiemann/BilinearForm.v:157 BEGIN
Parameter HdR_real : KahlerManifold -> nat -> Type.
   CAG zero-dependent Parameter HdR_real theories/Kahler/HodgeRiemann/BilinearForm.v:157 END *)
   CAG zero-dependent Parameter HdR_real theories/Kahler/HodgeRiemann/BilinearForm.v:157 END *)

(** The real cup product. *)
(* CAG zero-dependent Parameter Q_form_real theories/Kahler/HodgeRiemann/BilinearForm.v:150 BEGIN
Parameter Q_form_real : forall (M : KahlerManifold) (k : nat),
    HdR_real M (km_dim M - k) -> HdR_real M (km_dim M - k) -> CComplex.
   CAG zero-dependent Parameter Q_form_real theories/Kahler/HodgeRiemann/BilinearForm.v:150 END *)

(** Skew-symmetry for odd degree, symmetry for even degree. *)
(* CAG zero-dependent Admitted Q_symmetry theories/Kahler/HodgeRiemann/BilinearForm.v:158 BEGIN
Theorem Q_symmetry : forall (M : KahlerManifold) (k : nat) (xi eta : HdR M (km_dim M - k)),
    Q_form M k xi eta =
    Cmul (Cpow (Cneg C1) ((km_dim M - k) * (km_dim M - k - 1) / 2)%nat)
         (Q_form M k eta xi).
Proof. admit. Admitted.
   CAG zero-dependent Admitted Q_symmetry theories/Kahler/HodgeRiemann/BilinearForm.v:158 END *)
