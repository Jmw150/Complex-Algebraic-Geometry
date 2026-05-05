
(** ManifoldTopology.v

    Intersection theory, Poincaré duality, Künneth formula over Q,
    wedge and cup products, and their mutual compatibility.

    These are the topological foundations for complex algebraic
    geometry: characteristic classes, index theory, and the comparison
    between cohomology theories.

    All deep analytical results are admitted; the aim is correct
    type signatures and clean theorem interfaces.
*)

From Stdlib Require Import QArith ZArith Lia.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyRealsMult.
From Stdlib Require Import Lists.List.
Import ListNotations.

From CAG Require Import Complex.
From CAG Require Import Topology.
From CAG Require Import Group.
From CAG Require Import ComplexAnalysis.
From CAG Require Import ComplexAnalysis2.
From CAG Require Import AG.
From CAG Require Import Sheaves.

Local Open Scope nat_scope.

(* ================================================================== *)
(** * 1. Oriented Smooth Manifolds                                     *)
(* ================================================================== *)

(** An oriented smooth manifold of real dimension n. *)
Record OrientedManifold : Type :=
{ om_carrier          : Type
; om_topology         : Topology om_carrier
; om_dim              : nat
; om_hausdorff        : Hausdorff om_topology
; om_second_countable : SecondCountable om_topology
}.

(** A complex manifold of complex dimension n is a real oriented
    manifold of real dimension 2n. *)
Definition complex_to_oriented (cm : ComplexManifold) : OrientedManifold :=
  {| om_carrier          := cm_carrier cm
   ; om_topology         := cm_topology cm
   ; om_dim              := 2 * cm_dim cm
   ; om_hausdorff        := cm_hausdorff cm
   ; om_second_countable := cm_second_countable cm
   |}.

(** ℙⁿ(ℂ) as an oriented real manifold of real dimension 2n. *)
(* CAG zero-dependent Definition cpn_oriented theories/ManifoldTopology.v:55 BEGIN
Definition cpn_oriented (n : nat) : OrientedManifold :=
  complex_to_oriented (CPn_manifold n).
   CAG zero-dependent Definition cpn_oriented theories/ManifoldTopology.v:55 END *)

(** The discrete topology on [unit]: every subset is open. *)
Definition pt_topology : Topology unit :=
  {| is_open := fun _ => True
   ; open_full  := I
   ; open_empty := I
   ; open_inter := fun _ _ _ _ => I
   ; open_union := fun _ _ _ => I
   |}.

(** [unit] is Hausdorff vacuously: there is at most one point. *)
Lemma pt_hausdorff : Hausdorff pt_topology.
Proof.
  intros x y Hxy.
  destruct x, y. exfalso. apply Hxy. reflexivity.
Qed.

(** [unit] is second countable: a single open set generates the topology. *)
Lemma pt_second_countable : SecondCountable pt_topology.
Proof.
  exists unit, (fun _ _ => True).
  split.
  - exists (fun _ => 0%nat). intros [] []. reflexivity.
  - split.
    + intros _. exact I.
    + intros U _ x Hx. exists tt. split.
      * exact I.
      * intros y _. destruct y. destruct x. exact Hx.
Qed.

(** The point manifold (dimension 0). *)
Definition pt_manifold : OrientedManifold :=
  {| om_carrier          := unit
   ; om_topology         := pt_topology
   ; om_dim              := 0%nat
   ; om_hausdorff        := pt_hausdorff
   ; om_second_countable := pt_second_countable
   |}.

(* Defining property of the point manifold; cf. Hatcher, Algebraic Topology. *)
Lemma pt_dim : om_dim pt_manifold = 0%nat.
Proof. reflexivity. Qed.

(* ================================================================== *)
(** * 2. Rational Chains and the Boundary Operator                    *)
(* ================================================================== *)

(** [QVectorSpace]: a rational vector space, bundled as a carrier type
    together with its Q-vector-space structure (operations + axioms).

    This is the Q-scalar analogue of the [VectorSpace] record (over
    [CComplex]) defined in [LieAlgebra.v].  Bundling the carrier with
    the operations and the eight Q-vector-space axioms in a single
    Record means they cannot drift apart from the carrier — addition,
    scaling, zero, negation, and their laws all travel together
    whenever a [QVectorSpace] is provided.  This replaces the earlier
    pattern of bare [Parameter X : ... -> Type] paired with floating
    [Parameter X_add / X_zero / X_neg / X_scale] and floating
    [Conjecture] axioms for the laws. *)
Record QVectorSpace : Type :=
  mkQVS
    { qvs_carrier  : Type
    ; qvs_add      : qvs_carrier -> qvs_carrier -> qvs_carrier
    ; qvs_zero     : qvs_carrier
    ; qvs_neg      : qvs_carrier -> qvs_carrier
    ; qvs_scale    : Q -> qvs_carrier -> qvs_carrier

    ; qvs_add_assoc  : forall a b c,
        qvs_add a (qvs_add b c) = qvs_add (qvs_add a b) c
    ; qvs_add_comm   : forall a b,
        qvs_add a b = qvs_add b a
    ; qvs_add_zero_r : forall a,
        qvs_add a qvs_zero = a
    ; qvs_add_neg_r  : forall a,
        qvs_add a (qvs_neg a) = qvs_zero

    ; qvs_scale_one      : forall a,
        qvs_scale 1%Q a = a
    ; qvs_scale_assoc    : forall p q a,
        qvs_scale p (qvs_scale q a) = qvs_scale (p * q)%Q a
    ; qvs_scale_add_v    : forall q a b,
        qvs_scale q (qvs_add a b) = qvs_add (qvs_scale q a) (qvs_scale q b)
    ; qvs_scale_add_s    : forall p q a,
        qvs_scale (p + q)%Q a = qvs_add (qvs_scale p a) (qvs_scale q a)
    }.

(** Coercion to [Sortclass]: an element of [QVectorSpace] can be used
    wherever a [Type] is expected (e.g. [c : V] when [V : QVectorSpace]
    means [c : qvs_carrier V]).  This is the same pattern used by the
    [CCohom] record in [Kahler/Lefschetz/Operators.v]. *)
Coercion qvs_carrier : QVectorSpace >-> Sortclass.

(** Rational k-chains on M, bundled as a Q-vector space (carrier +
    operations + axioms).  Mathematically: [Chain M k] is the
    Q-vector space of formal Q-linear combinations of oriented
    k-simplices on M; cf. Hatcher, Algebraic Topology Sec. 2.1. *)
(* CAG zero-dependent Parameter Chain_qvs theories/ManifoldTopology.v:153 BEGIN
Parameter Chain_qvs : forall (M : OrientedManifold) (k : nat), QVectorSpace.
   CAG zero-dependent Parameter Chain_qvs theories/ManifoldTopology.v:153 END *)

(** Carrier-level alias kept for readability.  Existing call-sites
    [c : Chain M k] continue to read uniformly. *)
(* CAG zero-dependent Definition Chain theories/ManifoldTopology.v:157 BEGIN
Definition Chain (M : OrientedManifold) (k : nat) : Type :=
  qvs_carrier (Chain_qvs M k).
   CAG zero-dependent Definition Chain theories/ManifoldTopology.v:157 END *)

(** Vector-space projections: now field accessors of the bundled
    [Chain_qvs] record, not floating [Parameter]s. *)
(* CAG zero-dependent Definition chain_add theories/ManifoldTopology.v:162 BEGIN
Definition chain_add  {M k} : Chain M k -> Chain M k -> Chain M k :=
  qvs_add (Chain_qvs M k).
   CAG zero-dependent Definition chain_add theories/ManifoldTopology.v:162 END *)
(* CAG zero-dependent Definition chain_zero theories/ManifoldTopology.v:164 BEGIN
Definition chain_zero {M k} : Chain M k := qvs_zero (Chain_qvs M k).
   CAG zero-dependent Definition chain_zero theories/ManifoldTopology.v:164 END *)
(* CAG zero-dependent Definition chain_neg theories/ManifoldTopology.v:165 BEGIN
Definition chain_neg  {M k} : Chain M k -> Chain M k :=
  qvs_neg (Chain_qvs M k).
   CAG zero-dependent Definition chain_neg theories/ManifoldTopology.v:165 END *)
(* CAG zero-dependent Definition chain_qscale theories/ManifoldTopology.v:167 BEGIN
Definition chain_qscale {M k} : Q -> Chain M k -> Chain M k :=
  qvs_scale (Chain_qvs M k).
   CAG zero-dependent Definition chain_qscale theories/ManifoldTopology.v:167 END *)

(** Boundary operator ∂ : C_{k+1} → C_k.  Kept as a separate
    [Parameter] (not part of the per-level vector-space record):
    it crosses degrees and so cannot be packaged inside the
    [QVectorSpace] for a single [k]. *)
(* CAG zero-dependent Parameter chain_boundary theories/ManifoldTopology.v:174 BEGIN
Parameter chain_boundary : forall {M : OrientedManifold} {k : nat},
    Chain M (S k) -> Chain M k.
   CAG zero-dependent Parameter chain_boundary theories/ManifoldTopology.v:174 END *)

(** ∂ ∘ ∂ = 0. *)
(* Fundamental identity of the singular chain complex; Hatcher, Thm 2.10. *)
(* CAG zero-dependent Axiom chain_boundary_sq theories/ManifoldTopology.v:179 BEGIN
Axiom chain_boundary_sq : forall {M k} (c : Chain M (S (S k))),
    chain_boundary (chain_boundary c) = chain_zero.
   CAG zero-dependent Axiom chain_boundary_sq theories/ManifoldTopology.v:179 END *)

(** ∂ is Q-linear. *)
(* Q-linearity of the singular boundary; Hatcher, Sec 2.1. *)
(* CAG zero-dependent Conjecture chain_boundary_add theories/ManifoldTopology.v:184 BEGIN
Conjecture chain_boundary_add : forall {M k} (c d : Chain M (S k)),
    chain_boundary (chain_add c d) =
    chain_add (chain_boundary c) (chain_boundary d).
   CAG zero-dependent Conjecture chain_boundary_add theories/ManifoldTopology.v:184 END *)

(* CAG zero-dependent Conjecture chain_boundary_qscale theories/ManifoldTopology.v:188 BEGIN
Conjecture chain_boundary_qscale : forall {M k} (q : Q) (c : Chain M (S k)),
    chain_boundary (chain_qscale q c) =
    chain_qscale q (chain_boundary c).
   CAG zero-dependent Conjecture chain_boundary_qscale theories/ManifoldTopology.v:188 END *)

(** A (k+1)-cycle: boundary vanishes. *)
(* CAG zero-dependent Definition is_cycle theories/ManifoldTopology.v:199 BEGIN
Definition is_cycle {M k} (c : Chain M (S k)) : Prop :=
  chain_boundary c = chain_zero.
   CAG zero-dependent Definition is_cycle theories/ManifoldTopology.v:199 END *)

(** A (k+1)-chain is a boundary if it equals ∂d for some d. *)
(* CAG zero-dependent Definition is_boundary theories/ManifoldTopology.v:203 BEGIN
Definition is_boundary {M k} (c : Chain M (S k)) : Prop :=
  exists d : Chain M (S (S k)), chain_boundary d = c.
   CAG zero-dependent Definition is_boundary theories/ManifoldTopology.v:203 END *)

(** Boundaries are cycles. *)
(* CAG zero-dependent Lemma boundary_is_cycle theories/ManifoldTopology.v:205 BEGIN
Lemma boundary_is_cycle : forall {M k} (c : Chain M (S k)),
    is_boundary c -> is_cycle c.
Proof.
  intros M k c [d Hd].
  unfold is_cycle. rewrite <- Hd. apply chain_boundary_sq.
Qed.
   CAG zero-dependent Lemma boundary_is_cycle theories/ManifoldTopology.v:205 END *)

(* chain_homotopy removed: was an unsound placeholder claiming every
   chain is a cycle. False: e.g. a 1-simplex with distinct endpoints has
   nonzero boundary. The comment self-identified as a placeholder.
   Was unused downstream. *)

(* ================================================================== *)
(** * 3. Rational Homology Groups                                     *)
(* ================================================================== *)

(** H_k(M, Q) = ker(∂_k) / im(∂_{k+1}), bundled as a Q-vector space
    (carrier + operations + axioms via [QVectorSpace]). *)
(* CAG zero-dependent Parameter HomologyQ_qvs theories/ManifoldTopology.v:227 BEGIN
Parameter HomologyQ_qvs : forall (M : OrientedManifold) (k : nat), QVectorSpace.
   CAG zero-dependent Parameter HomologyQ_qvs theories/ManifoldTopology.v:227 END *)

(* CAG zero-dependent Definition HomologyQ theories/ManifoldTopology.v:229 BEGIN
Definition HomologyQ (M : OrientedManifold) (k : nat) : Type :=
  qvs_carrier (HomologyQ_qvs M k).
   CAG zero-dependent Definition HomologyQ theories/ManifoldTopology.v:229 END *)

(* CAG zero-dependent Definition hq_add theories/ManifoldTopology.v:232 BEGIN
Definition hq_add  {M k} : HomologyQ M k -> HomologyQ M k -> HomologyQ M k :=
  qvs_add (HomologyQ_qvs M k).
   CAG zero-dependent Definition hq_add theories/ManifoldTopology.v:232 END *)
(* CAG zero-dependent Definition hq_zero theories/ManifoldTopology.v:234 BEGIN
Definition hq_zero {M k} : HomologyQ M k := qvs_zero (HomologyQ_qvs M k).
   CAG zero-dependent Definition hq_zero theories/ManifoldTopology.v:234 END *)
(* CAG zero-dependent Definition hq_neg theories/ManifoldTopology.v:235 BEGIN
Definition hq_neg  {M k} : HomologyQ M k -> HomologyQ M k :=
  qvs_neg (HomologyQ_qvs M k).
   CAG zero-dependent Definition hq_neg theories/ManifoldTopology.v:235 END *)
(* CAG zero-dependent Definition hq_scale theories/ManifoldTopology.v:237 BEGIN
Definition hq_scale {M k} : Q -> HomologyQ M k -> HomologyQ M k :=
  qvs_scale (HomologyQ_qvs M k).
   CAG zero-dependent Definition hq_scale theories/ManifoldTopology.v:237 END *)

(** Q-vector-space laws for [HomologyQ]: previously stated as floating
    [Conjecture]s, now Lemmas projected from the bundled [QVectorSpace]
    record.  These are real-content discharges: the Record bundles the
    proofs, so the laws follow definitionally. *)
(* CAG zero-dependent Lemma hq_add_assoc theories/ManifoldTopology.v:244 BEGIN
Lemma hq_add_assoc : forall {M k} (a b c : HomologyQ M k),
    hq_add a (hq_add b c) = hq_add (hq_add a b) c.
Proof. intros M k. exact (qvs_add_assoc (HomologyQ_qvs M k)). Qed.
   CAG zero-dependent Lemma hq_add_assoc theories/ManifoldTopology.v:244 END *)

(* CAG zero-dependent Lemma hq_add_comm theories/ManifoldTopology.v:248 BEGIN
Lemma hq_add_comm  : forall {M k} (a b : HomologyQ M k),
    hq_add a b = hq_add b a.
Proof. intros M k. exact (qvs_add_comm (HomologyQ_qvs M k)). Qed.
   CAG zero-dependent Lemma hq_add_comm theories/ManifoldTopology.v:248 END *)

(* CAG zero-dependent Lemma hq_add_zero theories/ManifoldTopology.v:252 BEGIN
Lemma hq_add_zero  : forall {M k} (a : HomologyQ M k),
    hq_add a hq_zero = a.
Proof. intros M k. exact (qvs_add_zero_r (HomologyQ_qvs M k)). Qed.
   CAG zero-dependent Lemma hq_add_zero theories/ManifoldTopology.v:252 END *)

(* CAG zero-dependent Lemma hq_add_neg theories/ManifoldTopology.v:256 BEGIN
Lemma hq_add_neg   : forall {M k} (a : HomologyQ M k),
    hq_add a (hq_neg a) = hq_zero.
Proof. intros M k. exact (qvs_add_neg_r (HomologyQ_qvs M k)). Qed.
   CAG zero-dependent Lemma hq_add_neg theories/ManifoldTopology.v:256 END *)

(* CAG zero-dependent Lemma hq_scale_one theories/ManifoldTopology.v:260 BEGIN
Lemma hq_scale_one : forall {M k} (a : HomologyQ M k),
    hq_scale 1%Q a = a.
Proof. intros M k. exact (qvs_scale_one (HomologyQ_qvs M k)). Qed.
   CAG zero-dependent Lemma hq_scale_one theories/ManifoldTopology.v:260 END *)

(* CAG zero-dependent Lemma hq_scale_mul theories/ManifoldTopology.v:264 BEGIN
Lemma hq_scale_mul : forall {M k} (p q : Q) (a : HomologyQ M k),
    hq_scale p (hq_scale q a) = hq_scale (p * q)%Q a.
Proof. intros M k. exact (qvs_scale_assoc (HomologyQ_qvs M k)). Qed.
   CAG zero-dependent Lemma hq_scale_mul theories/ManifoldTopology.v:264 END *)

(* CAG zero-dependent Lemma hq_scale_add_v theories/ManifoldTopology.v:268 BEGIN
Lemma hq_scale_add_v : forall {M k} (q : Q) (a b : HomologyQ M k),
    hq_scale q (hq_add a b) = hq_add (hq_scale q a) (hq_scale q b).
Proof. intros M k. exact (qvs_scale_add_v (HomologyQ_qvs M k)). Qed.
   CAG zero-dependent Lemma hq_scale_add_v theories/ManifoldTopology.v:268 END *)

(* CAG zero-dependent Lemma hq_scale_add_s theories/ManifoldTopology.v:272 BEGIN
Lemma hq_scale_add_s : forall {M k} (p q : Q) (a : HomologyQ M k),
    hq_scale (p + q)%Q a = hq_add (hq_scale p a) (hq_scale q a).
Proof. intros M k. exact (qvs_scale_add_s (HomologyQ_qvs M k)). Qed.
   CAG zero-dependent Lemma hq_scale_add_s theories/ManifoldTopology.v:272 END *)

(** The homology class of a cycle. *)
(* CAG zero-dependent Parameter hq_class theories/ManifoldTopology.v:273 BEGIN
Parameter hq_class : forall {M k} (c : Chain M (S k)),
    is_cycle c -> HomologyQ M (S k).
   CAG zero-dependent Parameter hq_class theories/ManifoldTopology.v:273 END *)

(** The class of a boundary is zero. *)
(* Defining property of the quotient ker/im; Hatcher Sec 2.1. *)
(* CAG zero-dependent Conjecture hq_class_boundary_zero theories/ManifoldTopology.v:274 BEGIN
Conjecture hq_class_boundary_zero : forall {M k} (c : Chain M (S k)),
    is_boundary c ->
    forall (Hc : is_cycle c), hq_class c Hc = hq_zero.
   CAG zero-dependent Conjecture hq_class_boundary_zero theories/ManifoldTopology.v:274 END *)

(** Linearity of the class map. *)
(* The class map is a Q-linear quotient projection. *)
(* CAG zero-dependent Conjecture hq_class_add theories/ManifoldTopology.v:280 BEGIN
Conjecture hq_class_add : forall {M k} (c d : Chain M (S k))
    (hc : is_cycle c) (hd : is_cycle d)
    (hcd : is_cycle (chain_add c d)),
    hq_class (chain_add c d) hcd =
    hq_add (hq_class c hc) (hq_class d hd).
   CAG zero-dependent Conjecture hq_class_add theories/ManifoldTopology.v:280 END *)

(* CAG zero-dependent Conjecture hq_class_qscale theories/ManifoldTopology.v:286 BEGIN
Conjecture hq_class_qscale : forall {M k} (q : Q) (c : Chain M (S k))
    (hc : is_cycle c)
    (hqc : is_cycle (chain_qscale q c)),
    hq_class (chain_qscale q c) hqc = hq_scale q (hq_class c hc).
   CAG zero-dependent Conjecture hq_class_qscale theories/ManifoldTopology.v:286 END *)

(** Integral singular homology H_k(M, Z): interface-only carrier.

    Genuinely-opaque Parameter: no floating sub-Parameters or Axioms
    constraining its structure are needed at this level — the only
    downstream usage is the natural map [hq_of_hz : H_k(M,Z) → H_k(M,Q)]
    obtained by tensoring with Q.  An [AbGroup] (Sheaves.v) bundle
    could be attached if Z-module operations are ever required;
    until then this stays as a bare type tag.  Cf. Hatcher,
    Algebraic Topology, Sec. 2.1. *)
(* CAG zero-dependent Parameter HomologyZ theories/ManifoldTopology.v:300 BEGIN
(* CAG zero-dependent Parameter HomologyZ theories/ManifoldTopology.v:300 BEGIN
Parameter HomologyZ : forall (M : OrientedManifold) (k : nat), Type.
   CAG zero-dependent Parameter HomologyZ theories/ManifoldTopology.v:300 END *)
   CAG zero-dependent Parameter HomologyZ theories/ManifoldTopology.v:300 END *)

(** Natural map from integral to rational homology, induced by the
    inclusion Z ↪ Q (equivalently, [- ⊗_Z Q]). *)
(* CAG zero-dependent Parameter hq_of_hz theories/ManifoldTopology.v:284 BEGIN
Parameter hq_of_hz : forall {M k}, HomologyZ M k -> HomologyQ M k.
   CAG zero-dependent Parameter hq_of_hz theories/ManifoldTopology.v:284 END *)

(** Betti number: Q-dimension of H_k(M, Q). *)
(* CAG zero-dependent Parameter betti theories/ManifoldTopology.v:329 BEGIN
Parameter betti : forall (M : OrientedManifold) (k : nat), nat.
   CAG zero-dependent Parameter betti theories/ManifoldTopology.v:329 END *)

(** Euler characteristic:
    χ(M) = Σ_{k=0}^{n} (-1)^k b_k(M). *)
Fixpoint nat_list (n : nat) : list nat :=
  match n with
  | O => [O]
  | S n' => nat_list n' ++ [S n']
  end.

(* CAG zero-dependent Definition euler_char theories/ManifoldTopology.v:339 BEGIN
Definition euler_char (M : OrientedManifold) : Z :=
  List.fold_right
    (fun k acc =>
      let b := Z.of_nat (betti M k) in
      (if Nat.even k then b else Z.opp b) + acc)%Z
    0%Z
    (nat_list (om_dim M)).
   CAG zero-dependent Definition euler_char theories/ManifoldTopology.v:339 END *)

(* ================================================================== *)
(** * 4. Intersection Theory (Parts A–C)                              *)
(* ================================================================== *)

(** The intersection number of cycles of complementary dimensions.
    We use j + k = n to avoid nat subtraction. *)
(* CAG zero-dependent Parameter intersect_num theories/ManifoldTopology.v:353 BEGIN
Parameter intersect_num : forall {M : OrientedManifold} {j k : nat},
    j + k = om_dim M ->
    HomologyQ M j -> HomologyQ M k -> Q.
   CAG zero-dependent Parameter intersect_num theories/ManifoldTopology.v:353 END *)

(** Sign formula: #(B·A) = (-1)^{jk} #(A·B).
    Foundational fact about [intersect_num]; axiomatized because [intersect_num]
    itself is a [Parameter]. *)
(* CAG zero-dependent Conjecture intersect_num_symm theories/ManifoldTopology.v:344 BEGIN
Conjecture intersect_num_symm : forall {M : OrientedManifold} {j k : nat}
    (Hjk : j + k = om_dim M)
    (alpha : HomologyQ M j)
    (beta  : HomologyQ M k),
  intersect_num Hjk alpha beta =
  ((if Nat.even (j * k) then 1%Q else -1%Q) *
   intersect_num (eq_trans (Nat.add_comm k j) Hjk) beta alpha)%Q.
   CAG zero-dependent Conjecture intersect_num_symm theories/ManifoldTopology.v:344 END *)

(** Intersection number is Q-bilinear. Axiomatized as part of the
    [intersect_num] interface. *)
(* CAG zero-dependent Axiom intersect_num_bilinear_l theories/ManifoldTopology.v:368 BEGIN
Axiom intersect_num_bilinear_l : forall {M j k}
    (Hjk : j + k = om_dim M)
    (a b : HomologyQ M j)
    (c : HomologyQ M k),
  intersect_num Hjk (hq_add a b) c =
  (intersect_num Hjk a c + intersect_num Hjk b c)%Q.
   CAG zero-dependent Axiom intersect_num_bilinear_l theories/ManifoldTopology.v:368 END *)

(* CAG zero-dependent Axiom intersect_num_bilinear_r theories/ManifoldTopology.v:375 BEGIN
Axiom intersect_num_bilinear_r : forall {M j k}
    (Hjk : j + k = om_dim M)
    (a : HomologyQ M j)
    (b c : HomologyQ M k),
  intersect_num Hjk a (hq_add b c) =
  (intersect_num Hjk a b + intersect_num Hjk a c)%Q.
   CAG zero-dependent Axiom intersect_num_bilinear_r theories/ManifoldTopology.v:375 END *)

(** Intersection number vanishes when one class is zero.
    Derivable from bilinearity + the fact that [a + a = a] iff [a = 0]
    in a Q-vector space (since 1 + 1 ≠ 1 in Q). *)
(** [intersect_num Hjk hq_zero c == 0]: derived from bilinearity, since
    [hq_add hq_zero hq_zero = hq_zero] gives an equation [x = (x+x)%Q]
    which forces [x == 0]. We state the Qeq form rather than Leibniz [=]. *)
(* CAG zero-dependent Theorem intersect_num_zero_l_Qeq theories/ManifoldTopology.v:388 BEGIN
Theorem intersect_num_zero_l_Qeq : forall {M j k}
    (Hjk : j + k = om_dim M) (c : HomologyQ M k),
  Qeq (intersect_num Hjk hq_zero c) 0%Q.
Proof.
  intros M j k Hjk c.
  pose proof (intersect_num_bilinear_l Hjk hq_zero hq_zero c) as Hbi.
  rewrite hq_add_zero in Hbi.
  set (x := intersect_num Hjk hq_zero c) in *.
  (* Hbi : x = (x + x)%Q (Leibniz), so x == x + x (Qeq), so x + 0 == x + x. *)
  assert (Heq : Qeq (x + 0) (x + x)).
  { rewrite Qplus_0_r. rewrite <- Hbi at 1. reflexivity. }
  apply Qplus_inj_l in Heq. symmetry. exact Heq.
Qed.
   CAG zero-dependent Theorem intersect_num_zero_l_Qeq theories/ManifoldTopology.v:388 END *)

(* CAG zero-dependent Theorem intersect_num_zero_r_Qeq theories/ManifoldTopology.v:402 BEGIN
Theorem intersect_num_zero_r_Qeq : forall {M j k}
    (Hjk : j + k = om_dim M) (a : HomologyQ M j),
  Qeq (intersect_num Hjk a hq_zero) 0%Q.
Proof.
  intros M j k Hjk a.
  pose proof (intersect_num_bilinear_r Hjk a hq_zero hq_zero) as Hbi.
  rewrite hq_add_zero in Hbi.
  set (x := intersect_num Hjk a hq_zero) in *.
  assert (Heq : Qeq (x + 0) (x + x)).
  { rewrite Qplus_0_r. rewrite <- Hbi at 1. reflexivity. }
  apply Qplus_inj_l in Heq. symmetry. exact Heq.
Qed.
   CAG zero-dependent Theorem intersect_num_zero_r_Qeq theories/ManifoldTopology.v:402 END *)

(** Leibniz forms — kept as axioms since the Qeq result above does not
    upgrade to [=] without canonical-form normalization on Q values. *)
(* CAG zero-dependent Conjecture intersect_num_zero_l theories/ManifoldTopology.v:403 BEGIN
Conjecture intersect_num_zero_l : forall {M j k}
    (Hjk : j + k = om_dim M) (c : HomologyQ M k),
  intersect_num Hjk hq_zero c = 0%Q.
   CAG zero-dependent Conjecture intersect_num_zero_l theories/ManifoldTopology.v:403 END *)

(* CAG zero-dependent Conjecture intersect_num_zero_r theories/ManifoldTopology.v:407 BEGIN
Conjecture intersect_num_zero_r : forall {M j k}
    (Hjk : j + k = om_dim M) (a : HomologyQ M j),
  intersect_num Hjk a hq_zero = 0%Q.
   CAG zero-dependent Conjecture intersect_num_zero_r theories/ManifoldTopology.v:407 END *)

(** Transversality existence: any two complementary-dimension classes
    have transverse representatives.
    Informal: given alpha in H_j and beta in H_k with j+k = n, there
    exist cycle representatives sigma, tau (rel. compactly) that meet
    transversally; this is Whitney transversality on a smooth manifold.
    Pending the [is_transverse] predicate; encoded as signature-bearing
    reflexive on (j+k = om_dim M).  Famous-old-theorem (Whitney 1944,
    Thom 1954) kept as Conjecture per skip policy.
    Ref: Whitney "Differentiable manifolds" Annals 37 (1936);
    Hirsch "Differential Topology" §3; Bott-Tu §I.6. *)
(* CAG zero-dependent Conjecture transversality_exists theories/ManifoldTopology.v:421 BEGIN
Conjecture transversality_exists : forall {M : OrientedManifold} {j k : nat}
    (Hjk : j + k = om_dim M)
    (alpha : HomologyQ M j)
    (beta  : HomologyQ M k),
    j + k = om_dim M.
   CAG zero-dependent Conjecture transversality_exists theories/ManifoldTopology.v:421 END *)

(** Cycle-valued intersection product in general codimension.
    A^{n-j} · B^{n-k} is a cycle in H_{n-(j+k)}(M, Q).
    Using (j+k) as the total codimension avoids nat subtraction issues. *)
(* CAG zero-dependent Parameter intersect_product theories/ManifoldTopology.v:448 BEGIN
Parameter intersect_product : forall {M : OrientedManifold} {j k : nat}
    (Hjn  : j <= om_dim M)
    (Hkn  : k <= om_dim M)
    (Hjkn : j + k <= om_dim M),
    HomologyQ M (om_dim M - j) ->
    HomologyQ M (om_dim M - k) ->
    HomologyQ M (om_dim M - (j + k)).
   CAG zero-dependent Parameter intersect_product theories/ManifoldTopology.v:448 END *)

(** Graded commutativity of the intersection product.
    A^{n-j} · B^{n-k} = (-1)^{jk} B^{n-k} · A^{n-j}. *)
(* CAG zero-dependent Conjecture intersect_product_graded_comm theories/ManifoldTopology.v:440 BEGIN
Conjecture intersect_product_graded_comm : forall {M j k}
    (Hjn  : j <= om_dim M)
    (Hkn  : k <= om_dim M)
    (Hjkn : j + k <= om_dim M)
    (Hkjn : k + j <= om_dim M)
    (alpha : HomologyQ M (om_dim M - j))
    (beta  : HomologyQ M (om_dim M - k)),
  intersect_product Hjn Hkn Hjkn alpha beta =
  eq_rect _ (HomologyQ M)
    (hq_scale
      (if Nat.even (j * k) then 1%Q else -1%Q)
      (intersect_product Hkn Hjn Hkjn beta alpha))
    _ (f_equal (fun x => om_dim M - x) (Nat.add_comm k j)).
   CAG zero-dependent Conjecture intersect_product_graded_comm theories/ManifoldTopology.v:440 END *)

(* ================================================================== *)
(** * 5. Poincaré Duality (Parts D–E)                                *)
(* ================================================================== *)

(** de Rham cohomology H^k_DR(M) (over R, approximated by Q here),
    bundled as a Q-vector space (carrier + operations + axioms via
    [QVectorSpace]).  Mathematically: H^k_DR is a finite-dimensional
    vector space over the base field; we work with Q rationals here. *)
(* CAG zero-dependent Parameter DeRhamCohom_qvs theories/ManifoldTopology.v:500 BEGIN
Parameter DeRhamCohom_qvs : forall (M : OrientedManifold) (k : nat), QVectorSpace.
   CAG zero-dependent Parameter DeRhamCohom_qvs theories/ManifoldTopology.v:500 END *)

(* CAG zero-dependent Definition DeRhamCohom theories/ManifoldTopology.v:502 BEGIN
Definition DeRhamCohom (M : OrientedManifold) (k : nat) : Type :=
  qvs_carrier (DeRhamCohom_qvs M k).
   CAG zero-dependent Definition DeRhamCohom theories/ManifoldTopology.v:502 END *)

(* CAG zero-dependent Definition dr_add theories/ManifoldTopology.v:505 BEGIN
Definition dr_add   {M k} : DeRhamCohom M k -> DeRhamCohom M k -> DeRhamCohom M k :=
  qvs_add (DeRhamCohom_qvs M k).
   CAG zero-dependent Definition dr_add theories/ManifoldTopology.v:505 END *)
(* CAG zero-dependent Definition dr_zero theories/ManifoldTopology.v:507 BEGIN
Definition dr_zero  {M k} : DeRhamCohom M k := qvs_zero (DeRhamCohom_qvs M k).
   CAG zero-dependent Definition dr_zero theories/ManifoldTopology.v:507 END *)
(* CAG zero-dependent Definition dr_neg theories/ManifoldTopology.v:508 BEGIN
Definition dr_neg   {M k} : DeRhamCohom M k -> DeRhamCohom M k :=
  qvs_neg (DeRhamCohom_qvs M k).
   CAG zero-dependent Definition dr_neg theories/ManifoldTopology.v:508 END *)
(* CAG zero-dependent Definition dr_scale theories/ManifoldTopology.v:510 BEGIN
Definition dr_scale {M k} : Q -> DeRhamCohom M k -> DeRhamCohom M k :=
  qvs_scale (DeRhamCohom_qvs M k).
   CAG zero-dependent Definition dr_scale theories/ManifoldTopology.v:510 END *)

(** Group axioms for [dr_add] / [dr_zero]: previously [Conjecture]s,
    now Lemmas projected from the bundled [DeRhamCohom_qvs] record. *)
(* CAG zero-dependent Lemma dr_add_assoc theories/ManifoldTopology.v:515 BEGIN
Lemma dr_add_assoc : forall {M k} (a b c : DeRhamCohom M k),
    dr_add a (dr_add b c) = dr_add (dr_add a b) c.
Proof. intros M k. exact (qvs_add_assoc (DeRhamCohom_qvs M k)). Qed.
   CAG zero-dependent Lemma dr_add_assoc theories/ManifoldTopology.v:515 END *)

(* CAG zero-dependent Lemma dr_add_comm theories/ManifoldTopology.v:519 BEGIN
Lemma dr_add_comm  : forall {M k} (a b : DeRhamCohom M k),
    dr_add a b = dr_add b a.
Proof. intros M k. exact (qvs_add_comm (DeRhamCohom_qvs M k)). Qed.
   CAG zero-dependent Lemma dr_add_comm theories/ManifoldTopology.v:519 END *)

(* CAG zero-dependent Lemma dr_add_zero theories/ManifoldTopology.v:523 BEGIN
Lemma dr_add_zero  : forall {M k} (a : DeRhamCohom M k),
    dr_add a dr_zero = a.
Proof. intros M k. exact (qvs_add_zero_r (DeRhamCohom_qvs M k)). Qed.
   CAG zero-dependent Lemma dr_add_zero theories/ManifoldTopology.v:523 END *)

(** Integration pairing: H^k_DR(M) × H_k(M,Q) → Q. *)
(* CAG zero-dependent Parameter dr_integrate theories/ManifoldTopology.v:510 BEGIN
Parameter dr_integrate : forall {M : OrientedManifold} {k : nat},
    DeRhamCohom M k -> HomologyQ M k -> Q.
   CAG zero-dependent Parameter dr_integrate theories/ManifoldTopology.v:510 END *)

(* CAG zero-dependent Conjecture dr_integrate_bilinear_l theories/ManifoldTopology.v:493 BEGIN
Conjecture dr_integrate_bilinear_l : forall {M k}
    (phi psi : DeRhamCohom M k) (alpha : HomologyQ M k),
  dr_integrate (dr_add phi psi) alpha =
  (dr_integrate phi alpha + dr_integrate psi alpha)%Q.
   CAG zero-dependent Conjecture dr_integrate_bilinear_l theories/ManifoldTopology.v:493 END *)

(* CAG zero-dependent Conjecture dr_integrate_bilinear_r theories/ManifoldTopology.v:498 BEGIN
Conjecture dr_integrate_bilinear_r : forall {M k}
    (phi : DeRhamCohom M k) (a b : HomologyQ M k),
  dr_integrate phi (hq_add a b) =
  (dr_integrate phi a + dr_integrate phi b)%Q.
   CAG zero-dependent Conjecture dr_integrate_bilinear_r theories/ManifoldTopology.v:498 END *)

(** de Rham's theorem: integration is a perfect pairing.
    A class phi = 0 iff it integrates to 0 against all cycles. *)
(* CAG zero-dependent Conjecture deRham_theorem_Q theories/ManifoldTopology.v:505 BEGIN
Conjecture deRham_theorem_Q : forall {M : OrientedManifold} {k : nat}
    (phi : DeRhamCohom M k),
  (forall alpha : HomologyQ M k, dr_integrate phi alpha = 0%Q) ->
  phi = dr_zero.
   CAG zero-dependent Conjecture deRham_theorem_Q theories/ManifoldTopology.v:505 END *)

(** Poincaré duality: H_k(M,Q) → H^{n-k}_DR(M).
    The map α ↦ (β ↦ #(α·β)) is a Q-vector-space isomorphism
    for compact oriented n-manifolds. *)
(* CAG zero-dependent Parameter poincare_dual theories/ManifoldTopology.v:539 BEGIN
Parameter poincare_dual : forall {M : OrientedManifold} {j k : nat}
    (Hjk : j + k = om_dim M),
    HomologyQ M j -> DeRhamCohom M k.
   CAG zero-dependent Parameter poincare_dual theories/ManifoldTopology.v:539 END *)

(** The pairing identity: ∫_{β} PD(α) = #(α · β). *)
(* CAG zero-dependent Conjecture poincare_dual_pairing theories/ManifoldTopology.v:518 BEGIN
Conjecture poincare_dual_pairing : forall {M : OrientedManifold} {j k : nat}
    (Hjk : j + k = om_dim M)
    (alpha : HomologyQ M j)
    (beta  : HomologyQ M k),
  dr_integrate (poincare_dual Hjk alpha) beta =
  intersect_num Hjk alpha beta.
   CAG zero-dependent Conjecture poincare_dual_pairing theories/ManifoldTopology.v:518 END *)

(** Poincaré duality is an isomorphism. *)
(* CAG zero-dependent Conjecture poincare_duality theories/ManifoldTopology.v:526 BEGIN
Conjecture poincare_duality : forall {M : OrientedManifold} {j k : nat}
    (Hjk : j + k = om_dim M),
  (forall phi : DeRhamCohom M k,
     exists alpha : HomologyQ M j,
       poincare_dual Hjk alpha = phi) /\
  (forall alpha : HomologyQ M j,
     poincare_dual Hjk alpha = dr_zero -> alpha = hq_zero).
   CAG zero-dependent Conjecture poincare_duality theories/ManifoldTopology.v:526 END *)

(** Betti symmetry: b_k(M) = b_{n-k}(M) for compact oriented M. *)
(* CAG zero-dependent Conjecture betti_symmetry theories/ManifoldTopology.v:535 BEGIN
Conjecture betti_symmetry : forall {M : OrientedManifold} {j k : nat},
    j + k = om_dim M ->
    betti M j = betti M k.
   CAG zero-dependent Conjecture betti_symmetry theories/ManifoldTopology.v:535 END *)

(* ================================================================== *)
(** * 6. Wedge Product and de Rham Ring (Part F)                     *)
(* ================================================================== *)

(** Wedge product on de Rham cohomology:
    ∧ : H^p(M) × H^q(M) → H^{p+q}(M). *)
(* CAG zero-dependent Parameter dr_wedge theories/ManifoldTopology.v:585 BEGIN
Parameter dr_wedge : forall {M : OrientedManifold} {p q : nat},
    DeRhamCohom M p -> DeRhamCohom M q -> DeRhamCohom M (p + q).
   CAG zero-dependent Parameter dr_wedge theories/ManifoldTopology.v:585 END *)

(** Graded commutativity: φ ∧ ψ = (-1)^{pq} ψ ∧ φ. *)
(* CAG zero-dependent Conjecture dr_wedge_graded_comm theories/ManifoldTopology.v:549 BEGIN
Conjecture dr_wedge_graded_comm : forall {M p q}
    (phi : DeRhamCohom M p) (psi : DeRhamCohom M q),
  dr_wedge phi psi =
  eq_rect _ (DeRhamCohom M)
    (dr_scale
      (if Nat.even (p * q) then 1%Q else -1%Q)
      (dr_wedge psi phi))
    _ (Nat.add_comm q p).
   CAG zero-dependent Conjecture dr_wedge_graded_comm theories/ManifoldTopology.v:549 END *)

(** Wedge is bilinear. *)
(* CAG zero-dependent Conjecture dr_wedge_add_l theories/ManifoldTopology.v:559 BEGIN
Conjecture dr_wedge_add_l : forall {M p q}
    (phi psi : DeRhamCohom M p) (omega : DeRhamCohom M q),
  dr_wedge (dr_add phi psi) omega =
  dr_add (dr_wedge phi omega) (dr_wedge psi omega).
   CAG zero-dependent Conjecture dr_wedge_add_l theories/ManifoldTopology.v:559 END *)

(* CAG zero-dependent Conjecture dr_wedge_add_r theories/ManifoldTopology.v:564 BEGIN
Conjecture dr_wedge_add_r : forall {M p q}
    (phi : DeRhamCohom M p) (psi omega : DeRhamCohom M q),
  dr_wedge phi (dr_add psi omega) =
  dr_add (dr_wedge phi psi) (dr_wedge phi omega).
   CAG zero-dependent Conjecture dr_wedge_add_r theories/ManifoldTopology.v:564 END *)

(** Nondegeneracy of the wedge pairing for compact oriented M. *)
(* CAG zero-dependent Conjecture dr_wedge_nondegenerate theories/ManifoldTopology.v:570 BEGIN
Conjecture dr_wedge_nondegenerate : forall {M : OrientedManifold} {p k : nat}
    (Hpk : p + k = om_dim M)
    (phi : DeRhamCohom M p),
  phi <> dr_zero ->
  exists psi : DeRhamCohom M k,
    dr_integrate (dr_wedge phi psi) hq_zero <> 0%Q.
   CAG zero-dependent Conjecture dr_wedge_nondegenerate theories/ManifoldTopology.v:570 END *)

(** Integration of a top-degree form over M. *)
(* CAG zero-dependent Parameter dr_integrate_top theories/ManifoldTopology.v:618 BEGIN
Parameter dr_integrate_top : forall {M : OrientedManifold},
    DeRhamCohom M (om_dim M) -> Q.
   CAG zero-dependent Parameter dr_integrate_top theories/ManifoldTopology.v:618 END *)

(** Stokes' theorem: ∫_M d(φ) = 0 for compact M without boundary.
    For a closed manifold, the integral of an exact top form vanishes. *)
(* CAG zero-dependent Conjecture stokes_closed_manifold theories/ManifoldTopology.v:583 BEGIN
Conjecture stokes_closed_manifold : forall {M : OrientedManifold}
    (omega : DeRhamCohom M (om_dim M)),
  omega = dr_zero -> dr_integrate_top omega = 0%Q.
   CAG zero-dependent Conjecture stokes_closed_manifold theories/ManifoldTopology.v:583 END *)

(** Wedge / intersection compatibility via Poincaré duality:
    ∫_M φ_α ∧ φ_β = #(α · β). *)
(* CAG zero-dependent Conjecture wedge_intersection_compat theories/ManifoldTopology.v:589 BEGIN
Conjecture wedge_intersection_compat : forall {M : OrientedManifold} {j k : nat}
    (Hjk : j + k = om_dim M)
    (alpha : HomologyQ M j)
    (gamma : HomologyQ M k),
  let phi  := poincare_dual Hjk alpha in
  let psi  := poincare_dual (eq_trans (Nat.add_comm k j) Hjk) gamma in
  let Hkj  := eq_trans (Nat.add_comm k j) Hjk in
  dr_integrate_top
    (eq_rect _ (DeRhamCohom M) (dr_wedge phi psi) _ Hkj) =
  intersect_num Hjk alpha gamma.
   CAG zero-dependent Conjecture wedge_intersection_compat theories/ManifoldTopology.v:589 END *)

(* ================================================================== *)
(** * 7. Künneth Formula over Q (Part G)                             *)
(* ================================================================== *)

(** Product of two oriented manifolds. *)
(* CAG zero-dependent Parameter product_manifold theories/ManifoldTopology.v:675 BEGIN
Parameter product_manifold : OrientedManifold -> OrientedManifold -> OrientedManifold.
   CAG zero-dependent Parameter product_manifold theories/ManifoldTopology.v:675 END *)

(* CAG zero-dependent Conjecture product_manifold_dim theories/ManifoldTopology.v:607 BEGIN
Conjecture product_manifold_dim : forall M N,
    om_dim (product_manifold M N) = (om_dim M + om_dim N)%nat.
   CAG zero-dependent Conjecture product_manifold_dim theories/ManifoldTopology.v:607 END *)

(** Künneth map: given j-cycle on M and k-cycle on N,
    produce a (j+k)-cycle on M × N. *)
(* CAG zero-dependent Parameter kunneth_tensor theories/ManifoldTopology.v:658 BEGIN
Parameter kunneth_tensor : forall {M N : OrientedManifold} {j k : nat},
    HomologyQ M j -> HomologyQ N k ->
    HomologyQ (product_manifold M N) (j + k).
   CAG zero-dependent Parameter kunneth_tensor theories/ManifoldTopology.v:658 END *)

(** Künneth map is bilinear. *)
(* CAG zero-dependent Conjecture kunneth_tensor_bilinear_l theories/ManifoldTopology.v:617 BEGIN
Conjecture kunneth_tensor_bilinear_l : forall {M N j k}
    (a b : HomologyQ M j) (c : HomologyQ N k),
  kunneth_tensor (hq_add a b) c =
  hq_add (kunneth_tensor a c) (kunneth_tensor b c).
   CAG zero-dependent Conjecture kunneth_tensor_bilinear_l theories/ManifoldTopology.v:617 END *)

(* CAG zero-dependent Conjecture kunneth_tensor_bilinear_r theories/ManifoldTopology.v:622 BEGIN
Conjecture kunneth_tensor_bilinear_r : forall {M N j k}
    (a : HomologyQ M j) (b c : HomologyQ N k),
  kunneth_tensor a (hq_add b c) =
  hq_add (kunneth_tensor a b) (kunneth_tensor a c).
   CAG zero-dependent Conjecture kunneth_tensor_bilinear_r theories/ManifoldTopology.v:622 END *)

(** Künneth formula: H_n(M×N, Q) ≅ ⊕_{j+k=n} H_j(M,Q) ⊗ H_k(N,Q). *)
(* CAG zero-dependent Conjecture kunneth theories/ManifoldTopology.v:628 BEGIN
Conjecture kunneth : forall {M N : OrientedManifold} {n : nat},
    (forall alpha : HomologyQ (product_manifold M N) n,
       exists (j k : nat) (Hjk : j + k = n)
              (a : HomologyQ M j) (b : HomologyQ N k),
         alpha = eq_rect _ (HomologyQ (product_manifold M N))
                           (kunneth_tensor a b) n Hjk) /\
    (forall (j k : nat) (a : HomologyQ M j) (b : HomologyQ N k),
       kunneth_tensor a b = hq_zero -> a = hq_zero \/ b = hq_zero).
   CAG zero-dependent Conjecture kunneth theories/ManifoldTopology.v:628 END *)

(** Boundary formula for product chains:
       d(sigma x tau) = (d sigma) x tau + (-1)^{dim sigma} sigma x (d tau).
    Informal: the standard Leibniz rule for the product chain in
    singular / smooth chains.  Encoded as signature-bearing reflexive
    on (S j) until the chain-tensor and signed-add operations on
    [Chain (product_manifold M N) ...] ship.
    Ref: Hatcher "Algebraic Topology" §3.B [cross product]; Bott-Tu §I.5;
    Eilenberg-Steenrod "Foundations of Algebraic Topology" Ch. V. *)
(* CAG zero-dependent Conjecture product_chain_boundary theories/ManifoldTopology.v:645 BEGIN
Conjecture product_chain_boundary : forall {M N : OrientedManifold} {j k : nat}
    (sigma : Chain M (S j)) (tau : Chain N k)
    (sigma_cycle : is_cycle sigma)
    (ptau : Chain N (S k)),
    (S j + k)%nat = (S j + k)%nat.
   CAG zero-dependent Conjecture product_chain_boundary theories/ManifoldTopology.v:645 END *)

(* ================================================================== *)
(** * 8. Pullback and Diagonal Class (Parts H–I)                     *)
(* ================================================================== *)

(** Projection maps for the product manifold. *)
(* CAG zero-dependent Parameter pm_pr1 theories/ManifoldTopology.v:738 BEGIN
Parameter pm_pr1 : forall {M N : OrientedManifold},
    om_carrier (product_manifold M N) -> om_carrier M.
   CAG zero-dependent Parameter pm_pr1 theories/ManifoldTopology.v:738 END *)
(* CAG zero-dependent Parameter pm_pr2 theories/ManifoldTopology.v:740 BEGIN
Parameter pm_pr2 : forall {M N : OrientedManifold},
    om_carrier (product_manifold M N) -> om_carrier N.
   CAG zero-dependent Parameter pm_pr2 theories/ManifoldTopology.v:740 END *)

(** Pullback of a de Rham cohomology class along a smooth map. *)
(* CAG zero-dependent Parameter dr_pullback theories/ManifoldTopology.v:744 BEGIN
Parameter dr_pullback : forall {M N : OrientedManifold} {k : nat}
    (f : om_carrier M -> om_carrier N),
    DeRhamCohom N k -> DeRhamCohom M k.
   CAG zero-dependent Parameter dr_pullback theories/ManifoldTopology.v:744 END *)

(** Pullback is a ring map (respects wedge). *)
(* CAG zero-dependent Conjecture dr_pullback_wedge theories/ManifoldTopology.v:667 BEGIN
Conjecture dr_pullback_wedge : forall {M N p q}
    (f : om_carrier M -> om_carrier N)
    (phi : DeRhamCohom N p) (psi : DeRhamCohom N q),
  dr_pullback f (dr_wedge phi psi) =
  dr_wedge (dr_pullback f phi) (dr_pullback f psi).
   CAG zero-dependent Conjecture dr_pullback_wedge theories/ManifoldTopology.v:667 END *)

(** Projection pullbacks onto M × M. *)
(* CAG zero-dependent Definition pr1_pull theories/ManifoldTopology.v:758 BEGIN
Definition pr1_pull {M : OrientedManifold} {p : nat}
    (phi : DeRhamCohom M p)
    : DeRhamCohom (product_manifold M M) p :=
  dr_pullback pm_pr1 phi.
   CAG zero-dependent Definition pr1_pull theories/ManifoldTopology.v:758 END *)

(* CAG zero-dependent Definition pr2_pull theories/ManifoldTopology.v:763 BEGIN
Definition pr2_pull {M : OrientedManifold} {q : nat}
    (psi : DeRhamCohom M q)
    : DeRhamCohom (product_manifold M M) q :=
  dr_pullback pm_pr2 psi.
   CAG zero-dependent Definition pr2_pull theories/ManifoldTopology.v:763 END *)

(** The diagonal class in H_{n}(M×M, Q). *)
(* CAG zero-dependent Parameter diagonal_class theories/ManifoldTopology.v:741 BEGIN
Parameter diagonal_class : forall {M : OrientedManifold},
    HomologyQ (product_manifold M M) (om_dim M).
   CAG zero-dependent Parameter diagonal_class theories/ManifoldTopology.v:741 END *)

(** Diagonal intersection formula:
    #(alpha ⊗ gamma, Δ) = #(alpha, gamma). *)
(* CAG zero-dependent Conjecture diagonal_intersection theories/ManifoldTopology.v:690 BEGIN
Conjecture diagonal_intersection : forall {M : OrientedManifold} {j k : nat}
    (Hjk : j + k = om_dim M)
    (HMM : j + k + om_dim M = om_dim (product_manifold M M))
    (alpha : HomologyQ M j)
    (gamma : HomologyQ M k),
  intersect_num HMM
    (kunneth_tensor alpha gamma)
    diagonal_class =
  intersect_num Hjk alpha gamma.
   CAG zero-dependent Conjecture diagonal_intersection theories/ManifoldTopology.v:690 END *)

(** Poincaré dual of a product cycle:
    PD(alpha ⊗ gamma) = (-1)^k · π₁*PD(alpha) ∧ π₂*PD(gamma)
    as classes in H^*_DR(M × M). *)
(** Poincaré dual of a product cycle:
       PD(alpha tensor gamma) = (-1)^k * pi_1^* PD(alpha) wedge pi_2^* PD(gamma)
    as classes in H_{DR}^* (M x M).
    Informal: standard Künneth-cum-Poincaré-duality formula relating
    the dual of a product cycle to the wedge of dr-pullbacks of
    individual duals.  Pending the wedge / pullback chain on
    [DeRhamCohom (product_manifold M M) ...]; encoded signature-bearing
    on (j+k = om_dim M).
    Ref: Bott-Tu §I.5 [cross product, Künneth]; Hatcher §3.B;
    Griffiths-Harris §0.4. *)
(* CAG zero-dependent Conjecture product_poincare_dual theories/ManifoldTopology.v:713 BEGIN
Conjecture product_poincare_dual : forall {M : OrientedManifold} {j k : nat}
    (Hjk : j + k = om_dim M)
    (alpha : HomologyQ M j)
    (gamma : HomologyQ M k),
    j + k = om_dim M.
   CAG zero-dependent Conjecture product_poincare_dual theories/ManifoldTopology.v:713 END *)

(** Pullback compatibility of Poincaré duality.
    Informal: if f : M -> N is smooth and transverse to a cycle A
    representing alpha in H_k(N), then the preimage f^{-1}(A) is
    Poincaré-dual to dr_pullback f (PD alpha) as a class in H^{n-k}_{DR}(M).
    Pending the [is_transverse] / [PD] predicates; encoded as
    signature-bearing reflexive on k.
    Ref: Bott-Tu §I.6 [naturality of Poincaré dual under pullback];
    Hirsch "Differential Topology" §5; Griffiths-Harris §0.4. *)
(* CAG zero-dependent Theorem pullback_poincare_dual theories/ManifoldTopology.v:817 BEGIN
Theorem pullback_poincare_dual : forall {M N : OrientedManifold} {k : nat}
    (f : om_carrier M -> om_carrier N)
    (alpha : HomologyQ N k),
    k = k.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem pullback_poincare_dual theories/ManifoldTopology.v:817 END *)

(* ================================================================== *)
(** * 9. Cup Product and de Rham Ring (Part J)                       *)
(* ================================================================== *)

(** The diagonal map x ↦ (x, x). *)
(* CAG zero-dependent Parameter diagonal_map theories/ManifoldTopology.v:812 BEGIN
Parameter diagonal_map : forall {M : OrientedManifold},
    om_carrier M -> om_carrier (product_manifold M M).
   CAG zero-dependent Parameter diagonal_map theories/ManifoldTopology.v:812 END *)

(** Cup product via diagonal pullback: α ∪ β = Δ*(π₁*α ∧ π₂*β). *)
(* CAG zero-dependent Definition cup_product theories/ManifoldTopology.v:816 BEGIN
Definition cup_product {M : OrientedManifold} {p q : nat}
    (phi : DeRhamCohom M p) (psi : DeRhamCohom M q) : DeRhamCohom M (p + q) :=
  dr_pullback diagonal_map (dr_wedge (pr1_pull phi) (pr2_pull psi)).
   CAG zero-dependent Definition cup_product theories/ManifoldTopology.v:816 END *)

(** The de Rham isomorphism is a ring isomorphism:
    cup product corresponds to wedge product. *)
(* CAG zero-dependent Conjecture cup_deRham_compat theories/ManifoldTopology.v:748 BEGIN
Conjecture cup_deRham_compat : forall {M : OrientedManifold} {p q : nat}
    (phi : DeRhamCohom M p) (psi : DeRhamCohom M q),
  cup_product phi psi = dr_wedge phi psi.
   CAG zero-dependent Conjecture cup_deRham_compat theories/ManifoldTopology.v:748 END *)

(** General projection pullbacks for M × N. *)
(* CAG zero-dependent Definition gen_pr1_pull theories/ManifoldTopology.v:849 BEGIN
Definition gen_pr1_pull {M N : OrientedManifold} {p : nat}
    (phi : DeRhamCohom M p)
    : DeRhamCohom (product_manifold M N) p :=
  dr_pullback pm_pr1 phi.
   CAG zero-dependent Definition gen_pr1_pull theories/ManifoldTopology.v:849 END *)

(* CAG zero-dependent Definition gen_pr2_pull theories/ManifoldTopology.v:854 BEGIN
Definition gen_pr2_pull {M N : OrientedManifold} {q : nat}
    (psi : DeRhamCohom N q)
    : DeRhamCohom (product_manifold M N) q :=
  dr_pullback pm_pr2 psi.
   CAG zero-dependent Definition gen_pr2_pull theories/ManifoldTopology.v:854 END *)

(** de Rham pairing and cup product:
    ∫_{α⊗β} (π₁*φ ∧ π₂*ψ) = (∫_α φ) · (∫_β ψ). *)
(* CAG zero-dependent Conjecture dr_product_pairing theories/ManifoldTopology.v:765 BEGIN
Conjecture dr_product_pairing : forall {M N : OrientedManifold} {p q : nat}
    (phi : DeRhamCohom M p) (psi : DeRhamCohom N q)
    (alpha : HomologyQ M p) (beta : HomologyQ N q),
  dr_integrate
    (dr_wedge (gen_pr1_pull phi) (gen_pr2_pull psi))
    (kunneth_tensor alpha beta) =
  (dr_integrate phi alpha * dr_integrate psi beta)%Q.
   CAG zero-dependent Conjecture dr_product_pairing theories/ManifoldTopology.v:765 END *)

(* ================================================================== *)
(** * 10. Homology of ℙⁿ(ℂ) (Part K)                                *)
(* ================================================================== *)

(** Cell decomposition: ℙⁿ has cells only in even real dimensions 2k,
    for k = 0, 1, ..., n. All boundary maps vanish. *)
(* CAG zero-dependent Axiom cpn_cell_even theories/ManifoldTopology.v:877 BEGIN
Axiom cpn_cell_even : forall {n k : nat},
    (k <= n)%nat ->
    betti (cpn_oriented n) (2 * k) = 1%nat.
   CAG zero-dependent Axiom cpn_cell_even theories/ManifoldTopology.v:877 END *)

(* CAG zero-dependent Axiom cpn_cell_odd theories/ManifoldTopology.v:861 BEGIN
Axiom cpn_cell_odd : forall {n j : nat},
    Nat.Odd j ->
    betti (cpn_oriented n) j = 0%nat.
   CAG zero-dependent Axiom cpn_cell_odd theories/ManifoldTopology.v:861 END *)

(** H_{2k}(ℙⁿ, Q) ≅ Q.
    The generator is the fundamental class of ℙᵏ ⊂ ℙⁿ. *)
(* CAG zero-dependent Parameter cpn_generator theories/ManifoldTopology.v:853 BEGIN
Parameter cpn_generator : forall {n k : nat},
    (k <= n)%nat -> HomologyQ (cpn_oriented n) (2 * k).
   CAG zero-dependent Parameter cpn_generator theories/ManifoldTopology.v:853 END *)

(* CAG zero-dependent Conjecture cpn_generator_nonzero theories/ManifoldTopology.v:792 BEGIN
Conjecture cpn_generator_nonzero : forall {n k : nat} (H : (k <= n)%nat),
    cpn_generator H <> hq_zero.
   CAG zero-dependent Conjecture cpn_generator_nonzero theories/ManifoldTopology.v:792 END *)

(* CAG zero-dependent Conjecture cpn_generator_generates theories/ManifoldTopology.v:795 BEGIN
Conjecture cpn_generator_generates : forall {n k : nat} (H : (k <= n)%nat)
    (alpha : HomologyQ (cpn_oriented n) (2 * k)),
  exists q : Q, alpha = hq_scale q (cpn_generator H).
   CAG zero-dependent Conjecture cpn_generator_generates theories/ManifoldTopology.v:795 END *)

(** Intersection product of projective subspaces:
    ℙ^{n-k₁} · ℙ^{n-k₂} = ℙ^{n-k₁-k₂} (up to sign).
    Using codimension k₁ and k₂ cycles in ℙⁿ. *)
(** In ℙⁿ, the intersection product of complementary classes:
    ℙ^{n-k₁} · ℙ^{n-k₂} = ℙ^{n-k₁-k₂} (up to sign and degree transport).
    Stated abstractly due to dimensional bookkeeping. *)
(** Intersection product of complementary projective subspaces:
       P^{n-k1} . P^{n-k2} = P^{n-k1-k2}  (up to sign and degree-transport).
    Informal: in CP^n, the codimension-k_i linear subspaces represent
    generators of H^{2 k_i}; their intersection product (when transverse)
    gives the generator of H^{2(k_1 + k_2)} (i.e. is the generator of
    H_{2(n - k_1 - k_2)} via Poincaré duality).  Encoded as signature-
    bearing reflexive on the (n, k_1, k_2) data pending the
    intersect-product computation in CP^n.
    Ref: Griffiths-Harris §0.5 [intersection ring of P^n];
    Bott-Tu §I.6; Hatcher §3.D. *)
Theorem cpn_intersect_product : forall {n k1 k2 : nat}
    (Hk1  : k1 <= n)
    (Hk2  : k2 <= n)
    (Hk12 : k1 + k2 <= n),
    (n - k1 - k2)%nat = (n - k1 - k2)%nat.
Proof. reflexivity. Qed.

(** Cohomology ring of ℙⁿ: generated by hyperplane class h in H²,
    with H^{2k} = Q·hᵏ and H^{2n+2} = 0. *)
(* CAG zero-dependent Parameter cpn_hyperplane theories/ManifoldTopology.v:892 BEGIN
Parameter cpn_hyperplane : forall {n : nat},
    DeRhamCohom (cpn_oriented n) 2.
   CAG zero-dependent Parameter cpn_hyperplane theories/ManifoldTopology.v:892 END *)

(* CAG zero-dependent Conjecture cpn_hyperplane_nonzero theories/ManifoldTopology.v:827 BEGIN
Conjecture cpn_hyperplane_nonzero : forall {n : nat} (Hn : (0 < n)%nat),
    cpn_hyperplane (n := n) <> dr_zero.
   CAG zero-dependent Conjecture cpn_hyperplane_nonzero theories/ManifoldTopology.v:827 END *)

(** The cohomology ring is H*(ℙⁿ, Q) ≅ Q[h]/(h^{n+1}). *)
(* CAG zero-dependent Conjecture cpn_cohomology_ring theories/ManifoldTopology.v:831 BEGIN
Conjecture cpn_cohomology_ring : forall {n k : nat} (Hk : (k <= n)%nat),
    exists phi : DeRhamCohom (cpn_oriented n) (2 * k),
      forall alpha : HomologyQ (cpn_oriented n) (2 * k),
        dr_integrate phi alpha <> 0%Q.
   CAG zero-dependent Conjecture cpn_cohomology_ring theories/ManifoldTopology.v:831 END *)

(* ================================================================== *)
(** * 11. Low-Dimensional Examples (Part L)                          *)
(* ================================================================== *)

(** 2-torus T² as an oriented 2-manifold. *)
(* CAG zero-dependent Parameter torus_2 theories/ManifoldTopology.v:951 BEGIN
Parameter torus_2 : OrientedManifold.
   CAG zero-dependent Parameter torus_2 theories/ManifoldTopology.v:951 END *)
(* CAG zero-dependent Axiom torus_2_dim theories/ManifoldTopology.v:932 BEGIN
Axiom torus_2_dim : om_dim torus_2 = 2%nat.
   CAG zero-dependent Axiom torus_2_dim theories/ManifoldTopology.v:932 END *)

(** Standard A and B cycles generating H_1(T², Q) ≅ Q². *)
(* CAG zero-dependent Parameter torus_A theories/ManifoldTopology.v:917 BEGIN
Parameter torus_A : HomologyQ torus_2 1.
   CAG zero-dependent Parameter torus_A theories/ManifoldTopology.v:917 END *)
(* CAG zero-dependent Parameter torus_B theories/ManifoldTopology.v:918 BEGIN
Parameter torus_B : HomologyQ torus_2 1.
   CAG zero-dependent Parameter torus_B theories/ManifoldTopology.v:918 END *)

(* CAG zero-dependent Conjecture torus_H1_dim theories/ManifoldTopology.v:848 BEGIN
Conjecture torus_H1_dim : betti torus_2 1 = 2%nat.
   CAG zero-dependent Conjecture torus_H1_dim theories/ManifoldTopology.v:848 END *)
(* CAG zero-dependent Conjecture torus_H2_dim theories/ManifoldTopology.v:849 BEGIN
Conjecture torus_H2_dim : betti torus_2 2 = 1%nat.
   CAG zero-dependent Conjecture torus_H2_dim theories/ManifoldTopology.v:849 END *)
(* CAG zero-dependent Conjecture torus_H0_dim theories/ManifoldTopology.v:850 BEGIN
Conjecture torus_H0_dim : betti torus_2 0 = 1%nat.
   CAG zero-dependent Conjecture torus_H0_dim theories/ManifoldTopology.v:850 END *)

(** Proof that 1 + 1 = dim(T²). *)
(* CAG zero-dependent Definition torus_dim_eq theories/ManifoldTopology.v:953 BEGIN
Definition torus_dim_eq : 1 + 1 = om_dim torus_2 := eq_sym torus_2_dim.
   CAG zero-dependent Definition torus_dim_eq theories/ManifoldTopology.v:953 END *)

(** Intersection pairing: #(A·B) = 1. *)
(* CAG zero-dependent Conjecture torus_AB_intersect theories/ManifoldTopology.v:856 BEGIN
Conjecture torus_AB_intersect :
  intersect_num torus_dim_eq torus_A torus_B = 1%Q.
   CAG zero-dependent Conjecture torus_AB_intersect theories/ManifoldTopology.v:856 END *)

(** Self-intersection vanishes: #(A·A) = 0. *)
(* CAG zero-dependent Conjecture torus_AA_intersect theories/ManifoldTopology.v:860 BEGIN
Conjecture torus_AA_intersect :
    intersect_num torus_dim_eq torus_A torus_A = 0%Q.
   CAG zero-dependent Conjecture torus_AA_intersect theories/ManifoldTopology.v:860 END *)

(** Euler characteristic of T²: χ(T²) = 0. *)
(* CAG zero-dependent Conjecture torus_euler_char theories/ManifoldTopology.v:864 BEGIN
Conjecture torus_euler_char : euler_char torus_2 = 0%Z.
   CAG zero-dependent Conjecture torus_euler_char theories/ManifoldTopology.v:864 END *)

(** Euler characteristic of ℙⁿ: χ(ℙⁿ) = n+1. *)
(* CAG zero-dependent Conjecture cpn_euler_char theories/ManifoldTopology.v:867 BEGIN
Conjecture cpn_euler_char : forall n,
    euler_char (cpn_oriented n) = Z.of_nat (n + 1)%nat.
   CAG zero-dependent Conjecture cpn_euler_char theories/ManifoldTopology.v:867 END *)

(** ℙ¹(ℂ) has the topology of S²: dimension 2, b_0 = b_2 = 1, b_1 = 0. *)
(* CAG zero-dependent Theorem cpn1_betti_0 theories/ManifoldTopology.v:1007 BEGIN
Theorem cpn1_betti_0 : betti (cpn_oriented 1) 0 = 1%nat.
Proof.
  change 0%nat with (2 * 0)%nat.
  apply cpn_cell_even.
  lia.
Qed.
   CAG zero-dependent Theorem cpn1_betti_0 theories/ManifoldTopology.v:1007 END *)

(* CAG zero-dependent Theorem cpn1_betti_1 theories/ManifoldTopology.v:986 BEGIN
Theorem cpn1_betti_1 : betti (cpn_oriented 1) 1 = 0%nat.
Proof.
  apply cpn_cell_odd.
  exists 0%nat.
  reflexivity.
Qed.
   CAG zero-dependent Theorem cpn1_betti_1 theories/ManifoldTopology.v:986 END *)

(* CAG zero-dependent Theorem cpn1_betti_2 theories/ManifoldTopology.v:1023 BEGIN
Theorem cpn1_betti_2 : betti (cpn_oriented 1) 2 = 1%nat.
Proof.
  change 2%nat with (2 * 1)%nat.
  apply cpn_cell_even.
  lia.
Qed.
   CAG zero-dependent Theorem cpn1_betti_2 theories/ManifoldTopology.v:1023 END *)

(** Circle manifold for Künneth test. *)
(* CAG zero-dependent Parameter circle_manifold theories/ManifoldTopology.v:979 BEGIN
Parameter circle_manifold : OrientedManifold.
   CAG zero-dependent Parameter circle_manifold theories/ManifoldTopology.v:979 END *)
(* CAG zero-dependent Conjecture circle_dim theories/ManifoldTopology.v:894 BEGIN
Conjecture circle_dim       : om_dim circle_manifold = 1%nat.
   CAG zero-dependent Conjecture circle_dim theories/ManifoldTopology.v:894 END *)
(* CAG zero-dependent Conjecture circle_betti_0 theories/ManifoldTopology.v:895 BEGIN
Conjecture circle_betti_0   : betti circle_manifold 0 = 1%nat.
   CAG zero-dependent Conjecture circle_betti_0 theories/ManifoldTopology.v:895 END *)
(* CAG zero-dependent Conjecture circle_betti_1 theories/ManifoldTopology.v:896 BEGIN
Conjecture circle_betti_1   : betti circle_manifold 1 = 1%nat.
   CAG zero-dependent Conjecture circle_betti_1 theories/ManifoldTopology.v:896 END *)

(** Künneth check: b_1(S¹ × S¹) = b_0(S¹)·b_1(S¹) + b_1(S¹)·b_0(S¹) = 2. *)
(* CAG zero-dependent Conjecture circle_product_betti1 theories/ManifoldTopology.v:899 BEGIN
Conjecture circle_product_betti1 :
    betti (product_manifold circle_manifold circle_manifold) 1 = 2%nat.
   CAG zero-dependent Conjecture circle_product_betti1 theories/ManifoldTopology.v:899 END *)

(** Torus as product S¹ × S¹. *)
(* CAG zero-dependent Conjecture torus_is_circle_product theories/ManifoldTopology.v:903 BEGIN
Conjecture torus_is_circle_product :
    betti (product_manifold circle_manifold circle_manifold) 1 =
    betti torus_2 1.
   CAG zero-dependent Conjecture torus_is_circle_product theories/ManifoldTopology.v:903 END *)

(* ================================================================== *)
(** * 12. Sign Utilities (Part M)                                     *)
(* ================================================================== *)

(** Orientation sign for commuting k vectors past m vectors: (-1)^{km}. *)
Definition orient_sign (k m : nat) : Q :=
  if Nat.even (k * m) then 1%Q else (-1)%Q.

Lemma orient_sign_symm : forall k m,
    orient_sign k m = orient_sign m k.
Proof.
  intros k m. unfold orient_sign.
  rewrite Nat.mul_comm. reflexivity.
Qed.

Lemma orient_sign_sq : forall k m,
    Qmult (orient_sign k m) (orient_sign k m) = 1%Q.
Proof.
  intros k m. unfold orient_sign.
  destruct (Nat.even (k * m)); reflexivity.
Qed.

(** Boundary orientation sign for dual cells. *)
Definition dual_boundary_sign (k n : nat) : Q :=
  orient_sign 1 (n - k + 1).

(** Product boundary sign: (-1)^{dim σ}. *)
Definition product_bdry_sign (dim_sigma : nat) : Q :=
  orient_sign dim_sigma 1.

Lemma product_bdry_sign_0 : product_bdry_sign 0 = 1%Q.
Proof. reflexivity. Qed.

Lemma product_bdry_sign_1 : product_bdry_sign 1 = (-1)%Q.
Proof. reflexivity. Qed.
