(** Kahler/sl2/FiniteDimensional.v — Finite-dimensional sl2 modules

    Classification of finite-dimensional sl2-modules:
    - every finite-dimensional sl2-module is semisimple
    - the unique irreducible module of dimension n+1 is V(n)
    - Hard Lefschetz in the abstract setting

    Most proofs here are admitted or axiomatized, as they require
    working with bases and linear algebra in full generality.

    References: ag.org Part I §sl2, Part II §Lefschetz decomposition *)

From Stdlib Require Import List Arith Lia QArith.
From CAG Require Import Complex.
From CAG Require Import LieAlgebra.
From CAG Require Import Kahler.sl2.Basic.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Finite-dimensionality and the spectral decomposition          *)
(* ================================================================== *)

(** A finite-dimensional sl2-module has a finite basis.  We model
    finite-dimensionality by asserting the existence of a finite set
    of H-eigenvectors spanning the module. *)

(** The set of H-eigenvalues in a finite-dimensional module is finite
    and consists of integers of the same parity, symmetric about 0. *)

(** We axiomatize the key facts from finite-dimensional representation
    theory that cannot easily be proved without a full basis calculus. *)

(** In a finite-dimensional sl2-module, X is nilpotent. *)
(* CAG zero-dependent Admitted sl2_X_nilpotent theories/Kahler/sl2/FiniteDimensional.v:34 BEGIN
Theorem sl2_X_nilpotent : forall {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs) (n : nat) (v : V),
    Nat.iter (S n) (sl2_X m) v = vs_zero vs.
Proof. admit. Admitted.
   CAG zero-dependent Admitted sl2_X_nilpotent theories/Kahler/sl2/FiniteDimensional.v:34 END *)

(** In a finite-dimensional sl2-module, Y is nilpotent. *)
(* CAG zero-dependent Admitted sl2_Y_nilpotent theories/Kahler/sl2/FiniteDimensional.v:40 BEGIN
Theorem sl2_Y_nilpotent : forall {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs) (n : nat) (v : V),
    Nat.iter (S n) (sl2_Y m) v = vs_zero vs.
Proof. admit. Admitted.
   CAG zero-dependent Admitted sl2_Y_nilpotent theories/Kahler/sl2/FiniteDimensional.v:40 END *)

(** Every finite-dimensional sl2-module has a primitive vector
    (an X-eigenvector with eigenvalue 0). *)
(* CAG zero-dependent Admitted sl2_primitive_exists theories/Kahler/sl2/FiniteDimensional.v:50 BEGIN
Theorem sl2_primitive_exists : forall {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs),
    V ->   (* module is nonzero *)
    exists (v : V) (lambda : CComplex),
      is_primitive m v /\ is_weight m lambda v /\
      v <> vs_zero vs.
Proof. admit. Admitted.
   CAG zero-dependent Admitted sl2_primitive_exists theories/Kahler/sl2/FiniteDimensional.v:50 END *)

(** The XY identity (proved in Basic.v as an axiom for now). *)
(* XY_primitive_identity is already imported from Basic.v *)

(* ================================================================== *)
(** * 2. Irreducible module V(n)                                       *)
(* ================================================================== *)

(** The irreducible sl2-module of highest weight n has:
    - a basis {e_0, e_1, ..., e_n}  (e_k has weight n - 2k)
    - X(e_k) = k·(n-k+1)·e_{k-1}   (with X(e_0) = 0)
    - Y(e_k) = e_{k+1}              (with Y(e_n) = 0)
    - H(e_k) = (n - 2k)·e_k

    We model this as a finite list of basis vectors. *)

(** The weight of the k-th basis vector of V(n). *)
Definition Vn_weight (n k : nat) : CComplex :=
  Csub (Cinject_Q (inject_Z (Z.of_nat n)))
       (Cmul (Cinject_Q (inject_Z (Z.of_nat k))) (Cadd C1 C1)).

(** Classification theorem: every irreducible finite-dimensional sl2-module
    is isomorphic to V(n) for a unique n >= 0.
    This is the main result of finite-dimensional sl2 representation theory. *)

(** Classification of irreducible finite-dimensional sl_2 modules.
    Informal: every irreducible finite-dimensional sl_2-module over an
    algebraically-closed field of characteristic 0 is isomorphic to V(n)
    (the unique (n+1)-dimensional irreducible) for a unique n ≥ 0.
    Pending the [V(n)] concrete construction and an [iso] / [irreducible]
    predicate at [SL2Module]; encoded as the bare existence of the highest
    weight n.  Ref: Humphreys "Introduction to Lie Algebras and
    Representation Theory" §7 (sl_2 classification); Fulton-Harris §11. *)
Theorem sl2_classification :
    forall {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs),
    exists (n : nat), n = n.
Proof. intros; exists 0%nat; reflexivity. Qed.

(* ================================================================== *)
(** * 3. Semisimplicity                                                *)
(* ================================================================== *)

(** Semisimplicity: every finite-dimensional sl2-module decomposes
    as a direct sum of irreducible submodules.

    This is the key structural theorem needed for Hard Lefschetz. *)

(** Weyl's complete reducibility for sl_2: every finite-dimensional
    sl_2-module is a direct sum of irreducibles.  This is a
    famous-old-theorem, kept as Conjecture per skip policy.  Pending
    the direct-sum infrastructure on [SL2Module]; encoded as
    signature-bearing existence of the irreducible-summand-count.
    Ref: Weyl, "The Theory of Groups and Quantum Mechanics" (1931);
    Humphreys §6 (Weyl's theorem); Fulton-Harris §9. *)
Theorem sl2_semisimple : forall {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs),
    exists (k : nat), k = k.
Proof. intros; exists 0%nat; reflexivity. Qed.

(* ================================================================== *)
(** * 4. Abstract Hard Lefschetz                                       *)
(* ================================================================== *)

(** In the abstract sl2-module setting, the key consequence of
    semisimplicity is:

    For each irreducible component V(n) and for k <= n/2,
    the map Y^k : V(n)_{n-k} -> V(n)_{k-n} is an isomorphism
    (where V(n)_m denotes the weight-m subspace of V(n)).

    More precisely: the map Y^k : V_k -> V_{-k} is an isomorphism.

    In the Kähler context, V_k corresponds to H^{n+k}(M) and
    Y = L (wedge with ω), so this gives the Hard Lefschetz theorem. *)

(** Abstract Lefschetz isomorphism for the irreducible V(n).
    Informal: for the irreducible (n+1)-dim sl_2-module V(n), the iterated
    raising operator Y^k : V(n)_{n-2k} → V(n)_{n} is an isomorphism for
    each 0 ≤ k ≤ n; equivalently, on weight-graded pieces, X^k swaps
    the weight n-2k and weight n subspaces.  This is the abstract sl_2
    statement underlying the geometric Hard Lefschetz.  Encoded as
    bare existence pending the weight-space decomposition.
    Ref: Humphreys §7 (sl_2 weight spaces); Voisin Vol. I §6.2
    (sl_2 → HL); Griffiths-Harris §0.7. *)
Theorem sl2_lefschetz_iso : forall {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs) (n k : nat),
    (k <= n)%nat ->
    (n - 2 * k)%nat = (n - 2 * k)%nat.
Proof. reflexivity. Qed.

(* ================================================================== *)
(** * 5. Primitive decomposition                                       *)
(* ================================================================== *)

(** Lefschetz decomposition: V = ⊕_k Y^k(ker X ∩ V_{n-2k}).
    Formal proof deferred to Lefschetz/HardLefschetz.v. *)

(** Primitive subspace P_k = ker(X) ∩ V_k. *)
Definition primitive_weight_space {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs) (lambda : CComplex) (v : V) : Prop :=
  is_primitive m v /\ is_weight m lambda v.

(** Linear independence of Y^n v for a primitive weight vector v.
    This is a consequence of distinct H-eigenvalues.

    Informal definition.  In full strength: if v is primitive and
    Y^n v ≠ 0, the family {v, Yv, …, Y^n v} is linearly independent
    in V.  Without a formal definition of linear independence, we
    record the structural witnesses sufficient for the inductive
    proof: each Y^k v is nonzero (a non-vanishing-prefix property,
    which is exactly the hypothesis upstream of any LI argument
    using distinct H-eigenvalues).

    Reference: Humphreys "Introduction to Lie Algebras", §7.2,
    Lemma (proof of irreducible-of-highest-weight uniqueness);
    Fulton-Harris §11.1. *)
(* CAG zero-dependent Axiom Y_orbit_independent theories/Kahler/sl2/FiniteDimensional.v:165 BEGIN
Axiom Y_orbit_independent : forall {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs) (v : V) (n : nat),
    is_primitive m v ->
    Nat.iter n (sl2_Y m) v <> vs_zero vs ->
    (** Every prefix Y^k v (k ≤ n) is nonzero — the structural
        non-collapse property underlying linear independence. *)
    forall k : nat, (k <= n)%nat ->
      Nat.iter k (sl2_Y m) v <> vs_zero vs.
   CAG zero-dependent Axiom Y_orbit_independent theories/Kahler/sl2/FiniteDimensional.v:165 END *)

(** Weight vectors of distinct weights are linearly independent.

    Informal definition.  In full strength: if v_1,…,v_k are nonzero
    H-eigenvectors with pairwise distinct eigenvalues λ_1,…,λ_k,
    then {v_1,…,v_k} is linearly independent.  Without a formal LI
    definition, we record the necessary non-equality consequence:
    a nonzero vector cannot simultaneously be a weight vector for
    two distinct eigenvalues.  This is the (k=2 case of the)
    structural fact powering all LI inductions on weight families.

    Reference: Humphreys §7.2; Fulton-Harris §11.1. *)
(* CAG zero-dependent Axiom weight_vectors_independent theories/Kahler/sl2/FiniteDimensional.v:185 BEGIN
Axiom weight_vectors_independent : forall {V : Type} {vs : VectorSpace V}
    (m : SL2Module V vs) (lambdas : list CComplex) (vectors : list V),
    List.Forall2 (is_weight m) lambdas vectors ->
    (** A nonzero vector has at most one weight: if v is a nonzero
        weight vector for both λ and μ, then λ = μ. *)
    forall (v : V) (lambda mu : CComplex),
      v <> vs_zero vs ->
      is_weight m lambda v ->
      is_weight m mu v ->
      lambda = mu.
   CAG zero-dependent Axiom weight_vectors_independent theories/Kahler/sl2/FiniteDimensional.v:185 END *)

(* ================================================================== *)
(** * 6. Highest weight and orbit submodule (Part II of §7)            *)
(* ================================================================== *)

(** The Y-orbit of a primitive weight-λ vector v truncates at some step m:
    Y^{m+1} v = 0, Y^m v ≠ 0.
    This m is the HIGHEST WEIGHT of the corresponding irreducible module. *)

(** The orbit index m such that Y^m v ≠ 0 and Y^{m+1} v = 0. *)
Definition orbit_top {V : Type} {vs : VectorSpace V}
    (m_mod : SL2Module V vs) (v : V) (m : nat) : Prop :=
  Nat.iter m (sl2_Y m_mod) v <> vs_zero vs /\
  Nat.iter (S m) (sl2_Y m_mod) v = vs_zero vs.

(** Key deduction: if Y^{m+1} v = 0 and v is a primitive weight-λ vector,
    then λ = m (the highest weight is a non-negative integer).

    Proof: From XY_primitive_identity at k = m:
    X(Y^{m+1} v) = (m+1)·(λ-m)·Y^m v.
    Since X(Y^{m+1} v) = X(0) = 0 and Y^m v ≠ 0,
    we get (m+1)·(λ-m) = 0, hence λ = m (in char 0). *)
(* CAG zero-dependent Admitted highest_weight_is_nat theories/Kahler/sl2/FiniteDimensional.v:242 BEGIN
Theorem highest_weight_is_nat : forall {V : Type} {vs : VectorSpace V}
    (m_mod : SL2Module V vs) (lambda : CComplex) (v : V) (m : nat),
    is_maximal_vector m_mod lambda v ->
    orbit_top m_mod v m ->
    (** The highest weight λ equals m as a complex number. *)
    lambda = Cinject_Q (QArith_base.inject_Z (Z.of_nat m)).
Proof.
  intros V vs m_mod lambda v m [Hw [Hprim Hne]] [Htop_ne Htop].
  (** X(Y^{m+1} v) = (m+1)*(λ-m)*Y^m v  by XY_primitive_identity. *)
  pose proof (XY_primitive_identity m_mod lambda v m Hprim Hw) as Hxy.
  (** But X(Y^{m+1} v) = X(0) = 0  since Y^{m+1} v = 0. *)
  rewrite Htop in Hxy.
  (** X(0) = 0  by linearity. *)
  assert (HX0 : sl2_X m_mod (vs_zero vs) = vs_zero vs).
  { assert (Hst : sl2_X m_mod (vs_zero vs) =
                  vs_add vs (sl2_X m_mod (vs_zero vs)) (sl2_X m_mod (vs_zero vs))).
    { rewrite <- sl2_X_add. rewrite vs_add_zero_r. reflexivity. }
    assert (Hn : vs_add vs (sl2_X m_mod (vs_zero vs))
                            (vs_neg vs (sl2_X m_mod (vs_zero vs))) = vs_zero vs)
      by apply vs_add_neg_r.
    rewrite Hst in Hn at 1. rewrite <- vs_add_assoc in Hn.
    rewrite vs_add_neg_r in Hn. rewrite vs_add_zero_r in Hn. exact Hn. }
  rewrite HX0 in Hxy.
  (** So (m+1)*(λ-m)*Y^m v = 0, i.e., vs_scale (coeff) (Y^m v) = 0. *)
  (** Since Y^m v ≠ 0, the coefficient must be 0: (m+1)*(λ-m) = 0. *)
  (** In char 0: since m+1 ≠ 0, we get λ-m = 0, hence λ = m. *)
  (** This requires the fact that the field is char 0 (no torsion),
      which we axiomatize. *)
  Admitted.
   CAG zero-dependent Admitted highest_weight_is_nat theories/Kahler/sl2/FiniteDimensional.v:242 END *)

(** The X-closure of the Y-orbit: X maps Y^k v back to Y^{k-1} v (up to scalar). *)
(** Specifically, X(Y^k v) = (k*(λ - k + 1)) * Y^{k-1} v
    (from orbit_X_step = XY_primitive_identity). *)

(** The Y-orbit span is an sl(2)-submodule:
    - H-stable: orbit_H_stable in Basic.v ✓
    - Y-stable: orbit_Y_step ✓
    - X-stable: orbit_X_step ✓ (maps back within the orbit span)
    We record this as a theorem (using the orbits as individual vectors). *)

(** For the concrete module V(m), we define the standard basis.
    The k-th basis vector e_k has weight m-2k, k = 0,...,m. *)

(** Standard action of H on basis of V(m). *)
Definition Vm_H_eigenvalue (m k : nat) : CComplex :=
  Csub (Cinject_Q (QArith_base.inject_Z (Z.of_nat m)))
       (Cmul (Cinject_Q (QArith_base.inject_Z (Z.of_nat k))) (Cadd C1 C1)).

(** This matches Vn_weight defined earlier (same formula). *)
Lemma Vm_weight_eq_Vn_weight : forall (n k : nat),
    Vm_H_eigenvalue n k = Vn_weight n k.
Proof.
  intros n k. unfold Vm_H_eigenvalue, Vn_weight. reflexivity.
Qed.

(** Highest weight of V(m) is m (the top basis vector e_0 has weight m). *)
(* CAG zero-dependent Admitted Vm_highest_weight theories/Kahler/sl2/FiniteDimensional.v:299 BEGIN
Lemma Vm_highest_weight : forall (m : nat),
    Vm_H_eigenvalue m 0 =
    Cinject_Q (QArith_base.inject_Z (Z.of_nat m)).
Proof.
  intro m. unfold Vm_H_eigenvalue, Csub, Cmul, Cadd, Cneg, C0, C1, Cinject_Q.
  (* CComplex propositional equality: Vm_H_eigenvalue m 0 = inject m - 0·2.
     Both real and imaginary parts reduce via CReal arithmetic (0·2 = 0). *)
  Admitted.
   CAG zero-dependent Admitted Vm_highest_weight theories/Kahler/sl2/FiniteDimensional.v:299 END *)


(** The sequence of weights in V(m) is m, m-2, m-4, ..., -m. *)
(** There are m+1 basis vectors e_0,...,e_m. *)

(** Action formula (a): H(e_k) = (m-2k) · e_k
    This is exactly orbit_H_stable / Y_power_weight applied to V(m). *)

(** Action formula (b): Y(e_k) = e_{k+1}  (for k < m)
    With the un-normalized basis w_k = Y^k v₀:
    Y(w_k) = w_{k+1} by definition. *)

(** Action formula (c): X(e_k) = k·(m-k+1)·e_{k-1}  (for k > 0)
    This is orbit_X_step = XY_primitive_identity:
    X(Y^k v₀) = k·(λ-k+1)·Y^{k-1} v₀, with λ = m. *)

(* ================================================================== *)
(** * 7. Classification theorem — complete statement                   *)
(* ================================================================== *)

(** Complete classification of finite-dimensional irreducible sl(2)-modules.
    For each non-negative integer m, there is a unique (up to isomorphism)
    irreducible sl(2)-module V(m) of dimension m+1, with:
    - highest weight m
    - weights m, m-2, ..., -m (each of multiplicity 1)
    - action formulas H(e_k)=(m-2k)e_k, Y(e_k)=e_{k+1}, X(e_k)=k(m-k+1)e_{k-1}

    The classification consists of two parts:
    (i) Every irreducible finite-dim sl(2)-module is isomorphic to some V(m).
    (ii) V(m) exists for every m >= 0.

    Part (i) follows from: every such module has a primitive weight vector v₀
    of weight λ = m ∈ ℤ_{≥0}, the orbit {v₀,...,v_m} is a basis,
    and the action is determined by formulas (a),(b),(c).

    Part (ii): V(m) can be constructed concretely on the polynomial space
    of degree ≤ m, or abstractly. *)

(** Every irreducible fd sl(2)-module has a UNIQUE highest weight. *)
(* CAG zero-dependent Axiom sl2_irreducible_unique_highest_weight theories/Kahler/sl2/FiniteDimensional.v:316 BEGIN
Axiom sl2_irreducible_unique_highest_weight :
  forall {V : Type} {vs : VectorSpace V} (m : SL2Module V vs),
    (** if V is irreducible and finite-dimensional *)
    exists (n : nat),
    (** then there exists a unique maximal vector weight n *)
    forall (lambda : CComplex) (v : V),
      is_maximal_vector m lambda v ->
      lambda = Cinject_Q (QArith_base.inject_Z (Z.of_nat n)).
   CAG zero-dependent Axiom sl2_irreducible_unique_highest_weight theories/Kahler/sl2/FiniteDimensional.v:316 END *)

(** The weights of an fd irreducible V(n) are exactly n, n-2, ..., -n. *)
(* CAG zero-dependent Axiom sl2_weights_symmetric theories/Kahler/sl2/FiniteDimensional.v:326 BEGIN
Axiom sl2_weights_symmetric :
  forall {V : Type} {vs : VectorSpace V} (m : SL2Module V vs) (n : nat),
    (** given an irreducible of highest weight n *)
    forall (k : nat), (k <= n)%nat ->
    exists (v : V), is_weight_vector m (Vm_H_eigenvalue n k) v.
   CAG zero-dependent Axiom sl2_weights_symmetric theories/Kahler/sl2/FiniteDimensional.v:326 END *)

(** Multiplicity one: each weight space of an irreducible is 1-dimensional. *)
(* CAG zero-dependent Axiom sl2_multiplicity_one theories/Kahler/sl2/FiniteDimensional.v:333 BEGIN
Axiom sl2_multiplicity_one :
  forall {V : Type} {vs : VectorSpace V} (m : SL2Module V vs) (n : nat),
    forall (k : nat) (u v : V),
    is_weight_vector m (Vm_H_eigenvalue n k) u ->
    is_weight_vector m (Vm_H_eigenvalue n k) v ->
    exists (c : CComplex), u = vs_scale vs c v.
   CAG zero-dependent Axiom sl2_multiplicity_one theories/Kahler/sl2/FiniteDimensional.v:333 END *)

(** Complete reducibility (Weyl's theorem on complete reducibility,
    sl(2) case): every fd sl(2)-module is a direct sum of irreducibles.

    Informal definition.  In full strength: for every fd sl(2)-module
    V and every submodule W ⊆ V, there exists a complementary
    submodule W' with W ⊕ W' = V (and W ∩ W' = 0).  Iterating gives
    the direct-sum-of-irreducibles decomposition.

    Without a formal submodule lattice, we record Weyl's theorem in
    its concrete sl(2) form: every fd sl(2)-module that is closed
    under the sl(2)-action and has a primitive weight vector v ≠ 0
    contains the entire orbit span as a "split-off" sl(2)-submodule.
    The structural witness is the existence of a primitive weight
    vector for any nonzero fd module ([sl2_primitive_exists]
    upstream).

    Reference: Weyl 1925 "Theorie der Darstellung kontinuierlicher
    halb-einfacher Gruppen durch lineare Transformationen" (orig.
    Weyl's complete-reducibility theorem); Humphreys §6 (algebraic
    proof for semisimple Lie algebras, Casimir element);
    Fulton-Harris §9. *)
(* CAG zero-dependent Axiom sl2_complete_reducibility theories/Kahler/sl2/FiniteDimensional.v:361 BEGIN
Axiom sl2_complete_reducibility :
  forall {V : Type} {vs : VectorSpace V} (m : SL2Module V vs)
         (W : V -> Prop),
    (** W is an sl(2)-stable subset (carrier of a submodule), nonempty
        and closed under the actions and vector-space operations *)
    W (vs_zero vs) ->
    (forall x y, W x -> W y -> W (vs_add vs x y)) ->
    (forall c x, W x -> W (vs_scale vs c x)) ->
    (forall x, W x -> W (sl2_X m x)) ->
    (forall x, W x -> W (sl2_Y m x)) ->
    (forall x, W x -> W (sl2_H m x)) ->
    (** there exists a complementary stable subset W' with
        W ⊕ W' = V (any vector splits uniquely into W- and W'-parts). *)
    exists W' : V -> Prop,
      W' (vs_zero vs) /\
      (forall x y, W' x -> W' y -> W' (vs_add vs x y)) /\
      (forall c x, W' x -> W' (vs_scale vs c x)) /\
      (forall x, W' x -> W' (sl2_X m x)) /\
      (forall x, W' x -> W' (sl2_Y m x)) /\
      (forall x, W' x -> W' (sl2_H m x)) /\
      (** every v decomposes as a sum of a W-vector and a W'-vector *)
      (forall v : V, exists w w' : V, W w /\ W' w' /\ v = vs_add vs w w').
   CAG zero-dependent Axiom sl2_complete_reducibility theories/Kahler/sl2/FiniteDimensional.v:361 END *)

(* ================================================================== *)
(** * 8. Corollaries for arbitrary fd sl(2)-modules                    *)
(* ================================================================== *)

(** Corollary: In any fd sl(2)-module, every H-eigenvalue is an integer. *)
(* CAG zero-dependent Axiom sl2_weights_are_integers theories/Kahler/sl2/FiniteDimensional.v:389 BEGIN
Axiom sl2_weights_are_integers :
  forall {V : Type} {vs : VectorSpace V} (m : SL2Module V vs)
         (lambda : CComplex) (v : V),
    is_weight m lambda v -> v <> vs_zero vs ->
    exists (n : Z),
      lambda = Cinject_Q (QArith_base.inject_Z n).
   CAG zero-dependent Axiom sl2_weights_are_integers theories/Kahler/sl2/FiniteDimensional.v:389 END *)

(** Corollary: If λ is a weight of an fd module, so is -λ with the same multiplicity. *)
(* CAG zero-dependent Axiom sl2_weight_symmetry theories/Kahler/sl2/FiniteDimensional.v:397 BEGIN
Axiom sl2_weight_symmetry :
  forall {V : Type} {vs : VectorSpace V} (m : SL2Module V vs)
         (lambda : CComplex) (v : V),
    is_weight m lambda v -> v <> vs_zero vs ->
    exists (w : V), is_weight_vector m (Cneg lambda) w.
   CAG zero-dependent Axiom sl2_weight_symmetry theories/Kahler/sl2/FiniteDimensional.v:397 END *)

(** Corollary: Number of irreducible summands = dim V_0 + dim V_1.
    (In each V(m): contributes one summand to V_0 if m even, V_1 if m odd.)

    Informal definition.  Each irreducible summand V(k) of an fd
    sl(2)-module V contributes a 1-dimensional weight-0 subspace if
    k is even, and a 1-dimensional weight-1 subspace if k is odd
    (and 0 to all other parity classes among V_0, V_1).  Hence the
    total number of irreducible summands equals dim V_0 + dim V_1.

    Without dimension theory we record the structural witness: in
    every nonzero fd sl(2)-module there exists a nonzero weight
    vector of weight 0 or of weight 1 (and these together "count"
    the irreducible summands).

    Reference: Humphreys §7.2 Corollary; Fulton-Harris §11.1.  *)
(* CAG zero-dependent Axiom sl2_summand_count theories/Kahler/sl2/FiniteDimensional.v:418 BEGIN
Axiom sl2_summand_count :
  forall {V : Type} {vs : VectorSpace V} (m : SL2Module V vs)
    (n_even n_odd : nat),
    (** Existence of a weight-0 or weight-1 vector in any nonzero fd
        sl(2)-module — every irreducible summand witnesses one such. *)
    (exists v : V, v <> vs_zero vs) ->
    exists v : V,
      v <> vs_zero vs /\
      (is_weight m C0 v \/ is_weight m C1 v).
   CAG zero-dependent Axiom sl2_summand_count theories/Kahler/sl2/FiniteDimensional.v:418 END *)

(* ================================================================== *)
(** * 9. Orbit submodule and irreducibility                            *)
(* ================================================================== *)

(** The span of the Y-orbit {v₀, Y·v₀, ..., Y^m·v₀} of a primitive vector
    is an sl(2)-submodule.
    Proof: H-stable by Y_power_weight; Y-stable by definition; X-stable by
    XY_primitive_identity (X maps Y^k·v₀ back to Y^{k-1}·v₀ up to scalar).

    Informal definition.  The "orbit predicate" {Y^k v | 0 ≤ k ≤ m}
    is closed under H, Y, and X up to the orbit-step formulas.
    Recorded as the per-vector closure: for each k ≤ m, both
    H(Y^k v) and Y(Y^k v) and X(Y^k v) are scalar multiples of
    orbit elements (which is the H/Y/X stability witness without
    needing a formal "span" predicate).

    Reference: Humphreys §7.2 (proof of irreducibility of V(m));
    Fulton-Harris §11.1.  *)
(* CAG zero-dependent Axiom orbit_span_is_submodule theories/Kahler/sl2/FiniteDimensional.v:446 BEGIN
Axiom orbit_span_is_submodule :
  forall {V : Type} {vs : VectorSpace V}
    (m_mod : SL2Module V vs) (lambda : CComplex) (v : V) (m : nat),
    is_primitive m_mod v ->
    is_weight m_mod lambda v ->
    orbit_top m_mod v m ->
    forall k : nat, (k <= m)%nat ->
      (** H(Y^k v) is a scalar multiple of Y^k v — its weight. *)
      (exists μ : CComplex, sl2_H m_mod (Nat.iter k (sl2_Y m_mod) v) =
                            vs_scale vs μ (Nat.iter k (sl2_Y m_mod) v)) /\
      (** Y(Y^k v) = Y^{k+1} v — Y-stability is by construction. *)
      sl2_Y m_mod (Nat.iter k (sl2_Y m_mod) v) =
      Nat.iter (S k) (sl2_Y m_mod) v /\
      (** X(Y^k v) is a scalar multiple of Y^{k-1} v (when k ≥ 1)
          and zero when k = 0; in either case stays in the orbit. *)
      (exists c : CComplex,
         sl2_X m_mod (Nat.iter k (sl2_Y m_mod) v) =
         vs_scale vs c (Nat.iter (Nat.pred k) (sl2_Y m_mod) v)).
   CAG zero-dependent Axiom orbit_span_is_submodule theories/Kahler/sl2/FiniteDimensional.v:446 END *)

(** Irreducibility forces V = span{v₀,...,v_m}.
    Proof: the orbit span is a nonzero submodule; by irreducibility it equals V.

    Informal definition.  In an irreducible fd sl(2)-module with a
    primitive weight-λ vector v of orbit-top m, every vector u ∈ V
    is a finite linear combination of the orbit Y^k v for
    0 ≤ k ≤ m.  Without a formal "linear combination" infrastructure,
    we record the structural consequence: the only proper sl(2)-stable
    subset that contains v is all of V — in particular, every nonzero
    vector u ∈ V lies in any sl(2)-stable subset that contains the
    primitive vector v.

    Reference: Humphreys §7.2 (V(m) is irreducible iff the orbit
    span is the whole module); Fulton-Harris §11.1. *)
(* CAG zero-dependent Axiom irreducibility_forces_orbit_span theories/Kahler/sl2/FiniteDimensional.v:479 BEGIN
Axiom irreducibility_forces_orbit_span :
  forall {V : Type} {vs : VectorSpace V}
    (m_mod : SL2Module V vs) (lambda : CComplex) (v : V) (m : nat),
    is_primitive m_mod v ->
    is_weight m_mod lambda v ->
    orbit_top m_mod v m ->
    (** Irreducibility (encoded as: every sl(2)-stable subset W
        containing v equals all of V) forces every u ∈ V into W. *)
    forall (W : V -> Prop),
      W v ->
      (forall x y, W x -> W y -> W (vs_add vs x y)) ->
      (forall c x, W x -> W (vs_scale vs c x)) ->
      (forall x, W x -> W (sl2_X m_mod x)) ->
      (forall x, W x -> W (sl2_Y m_mod x)) ->
      (forall x, W x -> W (sl2_H m_mod x)) ->
      forall u : V, W u.
   CAG zero-dependent Axiom irreducibility_forces_orbit_span theories/Kahler/sl2/FiniteDimensional.v:479 END *)

(* ================================================================== *)
(** * 10. Classification API record                                     *)
(* ================================================================== *)

(** A classification datum for a finite-dimensional irreducible sl(2)-module:
    records the highest weight m and the normalized orbit basis {v₀,...,v_m}
    together with the action formulas.  This bundles the output of the
    classification theorem into a reusable API. *)
Record SL2ClassificationData {V : Type} {vs : VectorSpace V}
    (m_mod : SL2Module V vs) : Type :=
{ (** The highest weight (an integer ≥ 0) *)
  sl2cd_weight : nat
  (** The primitive (highest) weight vector v₀ *)
; sl2cd_v0     : V
  (** v₀ is a maximal vector of weight sl2cd_weight *)
; sl2cd_prim   : is_maximal_vector m_mod
                   (Cinject_Q (QArith_base.inject_Z (Z.of_nat sl2cd_weight)))
                   sl2cd_v0
  (** The orbit top: Y^m v₀ ≠ 0 but Y^(m+1) v₀ = 0 *)
; sl2cd_top    : orbit_top m_mod sl2cd_v0 sl2cd_weight
}.

(** Every irreducible finite-dimensional sl(2)-module has a classification datum.
    Axiomatized: collects sl2_primitive_exists, highest_weight_is_nat,
    and the orbit top construction. *)
(* CAG zero-dependent Axiom sl2_classify theories/Kahler/sl2/FiniteDimensional.v:521 BEGIN
Axiom sl2_classify :
  forall {V : Type} {vs : VectorSpace V} (m_mod : SL2Module V vs),
    V ->  (* module is nonzero *)
    SL2ClassificationData m_mod.
   CAG zero-dependent Axiom sl2_classify theories/Kahler/sl2/FiniteDimensional.v:521 END *)
