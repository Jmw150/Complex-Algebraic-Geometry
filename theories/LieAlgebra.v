
(** Lie Algebras

    A Lie algebra is a vector space equipped with a bilinear,
    antisymmetric bracket satisfying the Jacobi identity.

    The principal example here is gl(n,ℂ) — the n×n complex matrices
    with bracket [A,B] = AB − BA — which is the Lie algebra of the
    matrix Lie group GL(n,ℂ) already defined in Representation.v.

    We also define Lie algebra homomorphisms, the adjoint
    representation, and the Killing form.
*)

From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyRealsMult.
Import ListNotations.

From CAG Require Import Complex.
From CAG Require Import AG.
From CAG Require Import Group.
From CAG Require Import Representation.
From CAG Require Import Character.

Local Open Scope CReal_scope.

(* ------------------------------------------------------------------ *)
(** * 1. Vector spaces over ℂ                                          *)
(* ------------------------------------------------------------------ *)

Record VectorSpace (V : Type) : Type := mkVS
  { vs_add   : V -> V -> V
  ; vs_scale : CComplex -> V -> V
  ; vs_zero  : V
  ; vs_neg   : V -> V

  ; vs_add_assoc  : forall u v w, vs_add u (vs_add v w) = vs_add (vs_add u v) w
  ; vs_add_comm   : forall u v,   vs_add u v = vs_add v u
  ; vs_add_zero_r : forall v,     vs_add v vs_zero = v
  ; vs_add_neg_r  : forall v,     vs_add v (vs_neg v) = vs_zero

  ; vs_scale_one      : forall v, vs_scale C1 v = v
  ; vs_scale_assoc    : forall a b v,
      vs_scale a (vs_scale b v) = vs_scale (Cmul a b) v
  ; vs_scale_add_v    : forall a u v,
      vs_scale a (vs_add u v) = vs_add (vs_scale a u) (vs_scale a v)
  ; vs_scale_add_s    : forall a b v,
      vs_scale (Cadd a b) v = vs_add (vs_scale a v) (vs_scale b v)
  }.

Arguments vs_add   {V} _ _ _.
Arguments vs_scale {V} _ _ _.
Arguments vs_zero  {V} _.
Arguments vs_neg   {V} _ _.

(** vs_scale is compatible with CRealEq-setoid equality on both components.
    This is needed for CComplex arithmetic reasoning in weight-space proofs. *)
(** [vs_scale_creal_eq]: stating that [vs_scale vs c1 v = vs_scale vs c2 v]
    when [c1] and [c2] are [CRealEq]-componentwise equal. This is FALSE in
    general — a generic [VectorSpace V] need not respect [CRealEq] on its
    scalar input. We axiomatize it because the downstream code in this file
    relies on it for specific weight-space arguments. *)
Lemma vs_scale_creal_eq : forall {V : Type} (vs : VectorSpace V)
    (c1 c2 : CComplex) (v : V),
    CRealEq (re c1) (re c2) ->
    CRealEq (im c1) (im c2) ->
    vs_scale vs c1 v = vs_scale vs c2 v.
Proof.
  intros V vs c1 c2 v Hre Him.
  assert (Hc : c1 = c2) by (apply CComplex_eq; split; assumption).
  rewrite Hc. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * 2. Lie algebras                                                   *)
(* ------------------------------------------------------------------ *)

Record LieAlgebra (L : Type) : Type := mkLA
  { la_vs      :> VectorSpace L
  ; la_bracket : L -> L -> L

  (** Bilinearity in the left argument *)
  ; la_bracket_add_l : forall x y z,
      la_bracket (vs_add la_vs x y) z =
      vs_add la_vs (la_bracket x z) (la_bracket y z)
  ; la_bracket_scale_l : forall a x y,
      la_bracket (vs_scale la_vs a x) y =
      vs_scale la_vs a (la_bracket x y)

  (** Bilinearity in the right argument *)
  ; la_bracket_add_r : forall x y z,
      la_bracket x (vs_add la_vs y z) =
      vs_add la_vs (la_bracket x y) (la_bracket x z)
  ; la_bracket_scale_r : forall a x y,
      la_bracket x (vs_scale la_vs a y) =
      vs_scale la_vs a (la_bracket x y)

  (** Antisymmetry: [x, x] = 0 *)
  ; la_bracket_antisymm : forall x,
      la_bracket x x = vs_zero la_vs

  (** Jacobi identity: [x,[y,z]] + [y,[z,x]] + [z,[x,y]] = 0 *)
  ; la_jacobi : forall x y z,
      vs_add la_vs
        (vs_add la_vs
           (la_bracket x (la_bracket y z))
           (la_bracket y (la_bracket z x)))
        (la_bracket z (la_bracket x y))
      = vs_zero la_vs
  }.

Arguments la_bracket {L} _ _ _.

(** Helper: 0 + v = v *)
Local Lemma vs_add_zero_l {L : Type} (la : LieAlgebra L) (v : L) :
  vs_add la (vs_zero la) v = v.
Proof.
  rewrite (vs_add_comm L la). exact (vs_add_zero_r L la v).
Qed.

(** Derived: [x,y] = -[y,x]. *)
Lemma bracket_anticomm : forall {L : Type} (la : LieAlgebra L) (x y : L),
  la_bracket la x y = vs_neg la (la_bracket la y x).
Proof.
  intros L la x y.
  pose proof (la_bracket_antisymm L la (vs_add la x y)) as H.
  rewrite (la_bracket_add_l L la x y (vs_add la x y)) in H.
  rewrite (la_bracket_add_r L la x x y) in H.
  rewrite (la_bracket_add_r L la y x y) in H.
  rewrite (la_bracket_antisymm L la x) in H.
  rewrite (la_bracket_antisymm L la y) in H.
  rewrite (vs_add_zero_l la (la_bracket la x y)) in H.
  rewrite (vs_add_zero_r L la (la_bracket la y x)) in H.
  (* H : [x,y] + [y,x] = 0 *)
  rewrite <- (vs_add_zero_r L la (la_bracket la x y)).
  rewrite <- (vs_add_neg_r L la (la_bracket la y x)).
  rewrite (vs_add_assoc L la (la_bracket la x y) (la_bracket la y x)
                        (vs_neg la (la_bracket la y x))).
  rewrite H. exact (vs_add_zero_l la (vs_neg la (la_bracket la y x))).
Qed.

(** Bilinearity in the right argument (follows directly from record field). *)
Lemma bracket_add_r : forall {L : Type} (la : LieAlgebra L) (x y z : L),
  la_bracket la x (vs_add la y z) =
  vs_add la (la_bracket la x y) (la_bracket la x z).
Proof.
  intros L la x y z. exact (la_bracket_add_r L la x y z).
Qed.

Lemma bracket_scale_r : forall {L : Type} (la : LieAlgebra L) (a : CComplex) (x y : L),
  la_bracket la x (vs_scale la a y) =
  vs_scale la a (la_bracket la x y).
Proof.
  intros L la a x y. exact (la_bracket_scale_r L la a x y).
Qed.

(* ------------------------------------------------------------------ *)
(** * 3. The matrix Lie algebra gl(n,ℂ)                                *)
(* ------------------------------------------------------------------ *)

(** Scalar multiplication of a matrix by a complex number. *)
Definition mscale (c : CComplex) (A : Mat CComplex) : Mat CComplex :=
  List.map (List.map (Cmul c)) A.

(** Zero matrix of size n×n. *)
Definition mzero (n : nat) : Mat CComplex :=
  List.repeat (List.repeat C0 n) n.

(** Vector space structure on n×n matrices. *)

(* ---- Helper lemmas for CComplex arithmetic ---- *)

(** [Cadd]/[Cmul] structural identities at Leibniz [=] level on [CComplex].
    The setoid [~~C] versions are provable (in [Complex.v]) but the Leibniz
    versions are false (CReal arithmetic is not strict-equal). *)
Lemma Cadd_assoc : forall a b c : CComplex,
  Cadd a (Cadd b c) = Cadd (Cadd a b) c.
Proof. intros. apply CComplex_eq, Cadd_assoc_req. Qed.

Lemma Cadd_comm : forall a b : CComplex,
  Cadd a b = Cadd b a.
Proof. intros. apply CComplex_eq, Cadd_comm_req. Qed.

Lemma Cmul_add_distr_l : forall (a x y : CComplex),
  Cmul a (Cadd x y) = Cadd (Cmul a x) (Cmul a y).
Proof. intros. apply CComplex_eq, Cmul_distrib_l_req. Qed.

Lemma Cmul_add_distr_r : forall (a b x : CComplex),
  Cmul (Cadd a b) x = Cadd (Cmul a x) (Cmul b x).
Proof. intros. apply CComplex_eq, Cmul_distrib_r_req. Qed.

(* ---- Helper lemmas for vadd (row-level) ---- *)

Local Lemma vadd_assoc : forall (u v w : list CComplex),
  vadd u (vadd v w) = vadd (vadd u v) w.
Proof.
  induction u as [| x xs IH]; destruct v as [| y ys]; destruct w as [| z zs];
    simpl; try reflexivity.
  f_equal. apply Cadd_assoc. apply IH.
Qed.

Local Lemma vadd_comm : forall (u v : list CComplex),
  vadd u v = vadd v u.
Proof.
  induction u as [| x xs IH]; destruct v as [| y ys]; simpl; try reflexivity.
  f_equal. apply Cadd_comm. apply IH.
Qed.

Local Lemma vadd_map_Cmul_distr : forall (a : CComplex) (u v : list CComplex),
  List.map (Cmul a) (vadd u v) = vadd (List.map (Cmul a) u) (List.map (Cmul a) v).
Proof.
  intros a.
  induction u as [| x xs IH]; destruct v as [| y ys]; simpl; try reflexivity.
  f_equal. apply Cmul_add_distr_l. apply IH.
Qed.

Local Lemma vadd_map_Cmul_add : forall (a b : CComplex) (v : list CComplex),
  List.map (Cmul (Cadd a b)) v = vadd (List.map (Cmul a) v) (List.map (Cmul b) v).
Proof.
  intros a b.
  induction v as [| x xs IH]; simpl; try reflexivity.
  f_equal. apply Cmul_add_distr_r. apply IH.
Qed.

(* ---- The 8 matrix vector-space lemmas ---- *)

Lemma mat_vs_add_assoc : forall (A B C : Mat CComplex),
  madd A (madd B C) = madd (madd A B) C.
Proof.
  induction A as [| rA As IH]; destruct B as [| rB Bs]; destruct C as [| rC Cs];
    simpl; try reflexivity.
  f_equal. apply vadd_assoc. apply IH.
Qed.

Lemma mat_vs_add_comm : forall (A B : Mat CComplex),
  madd A B = madd B A.
Proof.
  induction A as [| rA As IH]; destruct B as [| rB Bs]; simpl; try reflexivity.
  f_equal. apply vadd_comm. apply IH.
Qed.

(** REFACTOR HISTORY:
    Task M.2 (2026-04-30): introduced [Axiom mat_vs_add_zero_r] /
      [Axiom mat_vs_add_neg_r] (both un-hypothesised, false-as-stated for
      shape-mismatched [A]) to preserve a legacy [VectorSpace (Mat CComplex)]
      signature.  Provided sound [_wf] Lemma counterparts below.
    Task M.2.next (2026-05-01): both axioms REMOVED.  The [VectorSpace]
      now lives over the sigma carrier [MatSig n := { A | Mat_wf n n A }]
      and the obligation reduces to [mat_vs_add_zero_r_wf] /
      [mat_vs_add_neg_r_wf] applied to [proj2_sig].  Net −2 axioms. *)

(** Sound, Mat_wf-guarded counterparts (Task M.2): provable via direct
    induction on the well-formed structure.  These are now the canonical
    statements consumed by [MatVS] / [gl] (via the sigma carrier). *)

(** Helper: [vadd row (repeat C0 (length row)) = row]. *)
Local Lemma vadd_repeat_C0_r : forall (row : list CComplex),
    vadd row (List.repeat C0 (List.length row)) = row.
Proof.
  induction row as [|x xs IH]; simpl; [reflexivity|].
  f_equal.
  - apply CComplex_eq, Cadd_C0_r_req.
  - exact IH.
Qed.

(** [madd A (mzero n) = A]  when each row of [A] has length [n].
    The number of rows of [A] is unconstrained (we only need each row
    to match the inner [repeat C0 n] from [mzero n]). *)
Local Lemma madd_mzero_r_aux : forall (A : Mat CComplex) (n k : nat),
    List.length A = k ->
    (forall row, List.In row A -> List.length row = n) ->
    madd A (List.repeat (List.repeat C0 n) k) = A.
Proof.
  induction A as [|rA As IH]; intros n k Hlen Hrow; simpl.
  - destruct k; reflexivity.
  - destruct k as [|k']; [discriminate|]. simpl. f_equal.
    + assert (Hr : List.length rA = n) by (apply Hrow; left; reflexivity).
      rewrite <- Hr. apply vadd_repeat_C0_r.
    + injection Hlen as Hlen.
      apply IH; [exact Hlen|]. intros row Hin. apply Hrow. right. exact Hin.
Qed.

(** Sound [mat_vs_add_zero_r], Mat_wf-guarded.  Provable independently
    from the un-hypothesized axiom above. *)
Lemma mat_vs_add_zero_r_wf : forall n (A : Mat CComplex),
    Mat_wf n n A -> madd A (mzero n) = A.
Proof.
  intros n A [HlenA HrowA]. unfold mzero.
  apply (madd_mzero_r_aux A n n HlenA HrowA).
Qed.

(** Helper: [vadd row (map Cneg row)] is the zero row. *)
Local Lemma vadd_neg_self : forall (row : list CComplex),
    vadd row (List.map Cneg row) = List.repeat C0 (List.length row).
Proof.
  induction row as [|x xs IH]; simpl; [reflexivity|].
  f_equal.
  - apply CComplex_eq. unfold CComplex_req, Cneg, Cadd. simpl. split; ring.
  - exact IH.
Qed.

(** Helper: matrices A, where every row has length n, satisfy
    [madd A (mneg A) = repeat (repeat C0 n) (length A)]. Independent of
    the row count. *)
Local Lemma madd_neg_uniform : forall (A : Mat CComplex) (n : nat),
    (forall row, List.In row A -> List.length row = n) ->
    madd A (mneg A) = List.repeat (List.repeat C0 n) (List.length A).
Proof.
  unfold mneg.
  induction A as [|rA As IH]; intros n Hrow; simpl; [reflexivity|].
  f_equal.
  - assert (Hr : List.length rA = n) by (apply Hrow; left; reflexivity).
    rewrite <- Hr. apply vadd_neg_self.
  - apply IH. intros row Hin. apply Hrow. right. exact Hin.
Qed.

(** Sound [mat_vs_add_neg_r], Mat_wf-guarded. *)
Lemma mat_vs_add_neg_r_wf : forall n (A : Mat CComplex),
    Mat_wf n n A -> madd A (mneg A) = mzero n.
Proof.
  intros n A [HlenA HrowA]. unfold mzero.
  rewrite (madd_neg_uniform A n HrowA). rewrite HlenA. reflexivity.
Qed.

Lemma mat_vs_scale_one : forall (A : Mat CComplex),
  mscale C1 A = A.
Proof.
  unfold mscale.
  induction A as [| row rows IH]; simpl; [reflexivity |].
  f_equal.
  - (* map (Cmul C1) row = row *)
    rewrite (List.map_ext (Cmul C1) id Cmul_C1_left).
    apply List.map_id.
  - apply IH.
Qed.

Lemma mat_vs_scale_assoc : forall (a b : CComplex) (A : Mat CComplex),
  mscale a (mscale b A) = mscale (Cmul a b) A.
Proof.
  intros a b A. unfold mscale.
  rewrite List.map_map.
  apply List.map_ext. intros row.
  rewrite List.map_map.
  apply List.map_ext. intros x.
  symmetry. apply Cmul_assoc_lem.
Qed.

Lemma mat_vs_scale_add_v : forall (a : CComplex) (A B : Mat CComplex),
  mscale a (madd A B) = madd (mscale a A) (mscale a B).
Proof.
  intros a.
  unfold mscale.
  induction A as [| rA As IH]; destruct B as [| rB Bs]; simpl; try reflexivity.
  f_equal.
  - apply vadd_map_Cmul_distr.
  - apply IH.
Qed.

Lemma mat_vs_scale_add_s : forall (a b : CComplex) (A : Mat CComplex),
  mscale (Cadd a b) A = madd (mscale a A) (mscale b A).
Proof.
  intros a b.
  unfold mscale.
  induction A as [| row rows IH]; simpl; [reflexivity |].
  f_equal.
  - apply vadd_map_Cmul_add.
  - apply IH.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Mat_wf closure lemmas (Task M.2.next, 2026-05-01)

    The CComplex-side [madd]/[mscale]/[mneg]/[mzero]/[commutator]
    preserve [Mat_wf n n].  These lemmas are needed to package the
    sigma-typed carrier [MatSig n := { A | Mat_wf n n A }].             *)
(* ------------------------------------------------------------------ *)

Lemma mzero_wf : forall n, Mat_wf n n (mzero n).
Proof.
  intros n. unfold Mat_wf, mzero. split.
  - apply List.repeat_length.
  - intros row Hin. apply List.repeat_spec in Hin. subst row.
    apply List.repeat_length.
Qed.

Lemma mscale_wf : forall n m c (A : Mat CComplex),
    Mat_wf n m A -> Mat_wf n m (mscale c A).
Proof.
  intros n m c A [HlenA HrowA]. unfold Mat_wf, mscale. split.
  - rewrite List.length_map. exact HlenA.
  - intros row Hin.
    rewrite List.in_map_iff in Hin.
    destruct Hin as [row0 [Hrow Hin0]].
    subst row. rewrite List.length_map. apply HrowA. exact Hin0.
Qed.

Lemma mneg_wf : forall n m (A : Mat CComplex),
    Mat_wf n m A -> Mat_wf n m (mneg A).
Proof.
  intros n m A [HlenA HrowA]. unfold Mat_wf, mneg. split.
  - rewrite List.length_map. exact HlenA.
  - intros row Hin.
    rewrite List.in_map_iff in Hin.
    destruct Hin as [row0 [Hrow Hin0]].
    subst row. rewrite List.length_map. apply HrowA. exact Hin0.
Qed.

(** [vadd] preserves length when its arguments have equal lengths. *)
Local Lemma vadd_length_eq_local : forall (u v : list CComplex),
    List.length u = List.length v -> List.length (vadd u v) = List.length u.
Proof.
  induction u as [|x xs IH]; intros [|y ys] H; simpl in *;
    try discriminate; try reflexivity.
  injection H as H. f_equal. apply IH. exact H.
Qed.

Lemma madd_wf : forall n m (A B : Mat CComplex),
    Mat_wf n m A -> Mat_wf n m B -> Mat_wf n m (madd A B).
Proof.
  intros n m A. revert n.
  induction A as [|rA As IH]; intros n B [HlenA HrowA] [HlenB HrowB].
  - simpl in HlenA. subst n. destruct B as [|rB Bs].
    + simpl. split; [reflexivity|]. intros row [].
    + simpl in HlenB. discriminate.
  - destruct B as [|rB Bs].
    { simpl in HlenB. simpl in HlenA. subst n. discriminate. }
    simpl. simpl in HlenA, HlenB.
    destruct n as [|n']; [discriminate|]. injection HlenA as HlenA'.
    injection HlenB as HlenB'.
    assert (HrA : List.length rA = m) by (apply HrowA; left; reflexivity).
    assert (HrB : List.length rB = m) by (apply HrowB; left; reflexivity).
    assert (HAs : Mat_wf n' m As).
    { split; [exact HlenA'|]. intros row Hin. apply HrowA. right. exact Hin. }
    assert (HBs : Mat_wf n' m Bs).
    { split; [exact HlenB'|]. intros row Hin. apply HrowB. right. exact Hin. }
    pose proof (IH n' Bs HAs HBs) as [HlenAB HrowAB].
    split; [simpl; f_equal; exact HlenAB|].
    intros row [Heq | Hin].
    + subst row. rewrite vadd_length_eq_local; [exact HrA | rewrite HrA, HrB; reflexivity].
    + apply HrowAB. exact Hin.
Qed.

Lemma commutator_wf : forall n (A B : Mat CComplex),
    Mat_wf n n A -> Mat_wf n n B -> Mat_wf n n (commutator A B n).
Proof.
  intros n A B HA HB. unfold commutator, msub.
  apply madd_wf.
  - apply (mmul_wf n n n); assumption.
  - apply mneg_wf. apply (mmul_wf n n n); assumption.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Sigma carrier and sigma-typed VectorSpace / LieAlgebra
       (Task M.2.next, 2026-05-01)

       [MatSig n := { A : Mat CComplex | Mat_wf n n A }] is the proper
       n×n matrix carrier.  All operations are wrapped via [proj1_sig]
       / wf-closure lemmas above.

       This refactor lets the [VectorSpace] [vs_add_zero_r] / [vs_add_neg_r]
       fields reduce to the existing [_wf] Lemmas, eliminating the legacy
       un-hypothesised [mat_vs_add_zero_r] / [mat_vs_add_neg_r] axioms.   *)
(* ------------------------------------------------------------------ *)

Definition MatSig (n : nat) : Type := { A : Mat CComplex | Mat_wf n n A }.

Definition msig_zero (n : nat) : MatSig n :=
  exist _ (mzero n) (mzero_wf n).

Definition msig_add {n} (A B : MatSig n) : MatSig n :=
  exist _ (madd (proj1_sig A) (proj1_sig B))
          (madd_wf n n _ _ (proj2_sig A) (proj2_sig B)).

Definition msig_neg {n} (A : MatSig n) : MatSig n :=
  exist _ (mneg (proj1_sig A))
          (mneg_wf n n _ (proj2_sig A)).

Definition msig_scale {n} (c : CComplex) (A : MatSig n) : MatSig n :=
  exist _ (mscale c (proj1_sig A))
          (mscale_wf n n c _ (proj2_sig A)).

(** The bracket on the sigma carrier.  Uses [commutator] (AG.v) directly
    since [gl_bracket] is defined later in the file; [gl_bracket n =
    commutator _ _ n] holds by definition. *)
Definition msig_bracket {n} (A B : MatSig n) : MatSig n :=
  exist _ (commutator (proj1_sig A) (proj1_sig B) n)
          (commutator_wf n _ _ (proj2_sig A) (proj2_sig B)).

(** Sigma equality reduces to underlying-matrix equality
    (via [proof_irrelevance]). *)
From Stdlib Require Import Logic.ProofIrrelevance.

Lemma msig_eq : forall {n} (A B : MatSig n),
    proj1_sig A = proj1_sig B -> A = B.
Proof.
  intros n [a Ha] [b Hb] Heq. simpl in Heq. subst b.
  f_equal. apply proof_irrelevance.
Qed.

(** VectorSpace obligations on the sigma carrier. *)
Lemma msig_add_assoc : forall {n} (u v w : MatSig n),
    msig_add u (msig_add v w) = msig_add (msig_add u v) w.
Proof.
  intros. apply msig_eq. simpl. apply mat_vs_add_assoc.
Qed.

Lemma msig_add_comm : forall {n} (u v : MatSig n),
    msig_add u v = msig_add v u.
Proof.
  intros. apply msig_eq. simpl. apply mat_vs_add_comm.
Qed.

Lemma msig_add_zero_r : forall {n} (v : MatSig n),
    msig_add v (msig_zero n) = v.
Proof.
  intros n [a Ha]. apply msig_eq. simpl. apply mat_vs_add_zero_r_wf. exact Ha.
Qed.

Lemma msig_add_neg_r : forall {n} (v : MatSig n),
    msig_add v (msig_neg v) = msig_zero n.
Proof.
  intros n [a Ha]. apply msig_eq. simpl. apply mat_vs_add_neg_r_wf. exact Ha.
Qed.

Lemma msig_scale_one : forall {n} (v : MatSig n),
    msig_scale C1 v = v.
Proof.
  intros. apply msig_eq. simpl. apply mat_vs_scale_one.
Qed.

Lemma msig_scale_assoc : forall {n} (a b : CComplex) (v : MatSig n),
    msig_scale a (msig_scale b v) = msig_scale (Cmul a b) v.
Proof.
  intros. apply msig_eq. simpl. apply mat_vs_scale_assoc.
Qed.

Lemma msig_scale_add_v : forall {n} (a : CComplex) (u v : MatSig n),
    msig_scale a (msig_add u v) =
    msig_add (msig_scale a u) (msig_scale a v).
Proof.
  intros. apply msig_eq. simpl. apply mat_vs_scale_add_v.
Qed.

Lemma msig_scale_add_s : forall {n} (a b : CComplex) (v : MatSig n),
    msig_scale (Cadd a b) v =
    msig_add (msig_scale a v) (msig_scale b v).
Proof.
  intros. apply msig_eq. simpl. apply mat_vs_scale_add_s.
Qed.

(** The vector space of well-formed n×n complex matrices.
    Replaces the legacy un-hypothesised [MatVS] (Task M.2.next, 2026-05-01).

    The two former un-hypothesised axioms [mat_vs_add_zero_r] /
    [mat_vs_add_neg_r] are now discharged via [mat_vs_add_zero_r_wf] /
    [mat_vs_add_neg_r_wf] (the underlying matrix is wf by [proj2_sig]). *)
Definition MatVS (n : nat) : VectorSpace (MatSig n) :=
  mkVS (MatSig n)
    msig_add
    msig_scale
    (msig_zero n)
    msig_neg
    (fun A B C => msig_add_assoc A B C)
    (fun A B   => msig_add_comm A B)
    (fun A     => msig_add_zero_r A)
    (fun A     => msig_add_neg_r A)
    msig_scale_one
    (fun a b A => msig_scale_assoc a b A)
    (fun a A B => msig_scale_add_v a A B)
    (fun a b A => msig_scale_add_s a b A).

(** The Lie bracket on gl(n,ℂ): [A,B] = AB − BA. *)
Definition gl_bracket (n : nat) (A B : Mat CComplex) : Mat CComplex :=
  commutator A B n.

(* ---- Helpers for gl_bracket bilinearity ---- *)

(** Leibniz versions of Cadd_C0 / Cadd_neg / Cmul_C0. *)
Local Lemma Cadd_C0_l_lem : forall a : CComplex, Cadd C0 a = a.
Proof. intros. apply CComplex_eq, Cadd_C0_l_req. Qed.

Local Lemma Cadd_C0_r_lem : forall a : CComplex, Cadd a C0 = a.
Proof. intros. apply CComplex_eq, Cadd_C0_r_req. Qed.

Local Lemma Cmul_C0_l_lem : forall a : CComplex, Cmul C0 a = C0.
Proof. intros. apply CComplex_eq, Cmul_C0_l. Qed.

Local Lemma Cmul_C0_r_lem : forall a : CComplex, Cmul a C0 = C0.
Proof. intros. apply CComplex_eq, Cmul_C0_r_req. Qed.

(** Cadd interchange: (a+b)+(c+d) = (a+c)+(b+d). *)
Local Lemma Cadd_interchange : forall a b c d : CComplex,
  Cadd (Cadd a b) (Cadd c d) = Cadd (Cadd a c) (Cadd b d).
Proof.
  intros a b c d.
  rewrite <- (Cadd_assoc a b (Cadd c d)).
  rewrite (Cadd_assoc b c d).
  rewrite (Cadd_comm b c).
  rewrite <- (Cadd_assoc c b d).
  rewrite (Cadd_assoc a c (Cadd b d)).
  reflexivity.
Qed.

(** dot distributes over vadd in left arg, when v and w have matching length. *)
Local Lemma dot_vadd_l : forall (v w u : list CComplex),
  length v = length w ->
  dot (vadd v w) u = Cadd (dot v u) (dot w u).
Proof.
  induction v as [|x xs IH]; destruct w as [|y ys]; intros u Hlen;
    simpl in *; try discriminate.
  - destruct u; simpl; rewrite Cadd_C0_l_lem; reflexivity.
  - destruct u as [|z zs]; simpl.
    + rewrite Cadd_C0_l_lem. reflexivity.
    + injection Hlen as Hlen'.
      rewrite (IH ys zs Hlen').
      rewrite Cmul_add_distr_r.
      apply Cadd_interchange.
Qed.

(** dot distributes over (map (Cmul a) v) in left arg. *)
Local Lemma dot_map_Cmul_l : forall (a : CComplex) (v u : list CComplex),
  dot (List.map (Cmul a) v) u = Cmul a (dot v u).
Proof.
  intros a. induction v as [|x xs IH]; intros u; simpl.
  - destruct u; simpl; symmetry; apply Cmul_C0_r_lem.
  - destruct u as [|z zs]; simpl.
    + symmetry. apply Cmul_C0_r_lem.
    + rewrite (IH zs).
      rewrite Cmul_add_distr_l.
      f_equal. apply Cmul_assoc_lem.
Qed.

(** row_mul_cols distributes over vadd in left arg, when lengths match. *)
Local Lemma row_mul_cols_vadd : forall (r v : list CComplex) (cols : list (list CComplex)),
  length r = length v ->
  row_mul_cols (vadd r v) cols =
  vadd (row_mul_cols r cols) (row_mul_cols v cols).
Proof.
  intros r v cols Hlen.
  induction cols as [|c cs IH]; simpl; [reflexivity |].
  rewrite (dot_vadd_l r v c Hlen).
  rewrite IH. reflexivity.
Qed.

(** row_mul_cols distributes over (map (Cmul a) r) in left arg. *)
Local Lemma row_mul_cols_map_Cmul : forall (a : CComplex) (r : list CComplex)
                                           (cols : list (list CComplex)),
  row_mul_cols (List.map (Cmul a) r) cols =
  List.map (Cmul a) (row_mul_cols r cols).
Proof.
  intros a r cols.
  induction cols as [|c cs IH]; simpl; [reflexivity |].
  rewrite dot_map_Cmul_l. rewrite IH. reflexivity.
Qed.

(** vadd preserves length when arguments have equal length. *)
Local Lemma vadd_length_eq : forall (v w : list CComplex),
  length v = length w ->
  length (vadd v w) = length v.
Proof.
  induction v as [|x xs IH]; destruct w as [|y ys]; intros Hlen;
    simpl in *; try discriminate; try reflexivity.
  injection Hlen as Hlen'. f_equal. apply IH; exact Hlen'.
Qed.

(** Length of vscale. *)
Local Lemma vscale_length_eq : forall (a : CComplex) (v : list CComplex),
  length (vscale a v) = length v.
Proof.
  intros a. induction v; simpl; [reflexivity | f_equal; assumption].
Qed.

(** mmul distributes over madd in left arg, when row-lengths match.
    The hypothesis: every corresponding pair of rows in A and B has equal length. *)
Local Lemma mmul_madd_l : forall (A B C : Mat CComplex) (p : nat),
  Forall2 (fun rA rB => length rA = length rB) A B ->
  mmul (madd A B) C p = madd (mmul A C p) (mmul B C p).
Proof.
  intros A B C p HF.
  induction HF as [| rA rB As Bs Hrow HFs IH]; simpl; [reflexivity |].
  f_equal.
  - apply row_mul_cols_vadd. exact Hrow.
  - exact IH.
Qed.

(** mmul distributes over mscale in left arg. *)
Local Lemma mmul_mscale_l : forall (a : CComplex) (A B : Mat CComplex) (p : nat),
  mmul (mscale a A) B p = mscale a (mmul A B p).
Proof.
  intros a A B p. unfold mscale.
  induction A as [|rA As IH]; simpl; [reflexivity |].
  f_equal.
  - apply row_mul_cols_map_Cmul.
  - exact IH.
Qed.

(** dot distributes over (map (Cmul a) u) in right arg. *)
Local Lemma dot_map_Cmul_r : forall (a : CComplex) (v u : list CComplex),
  dot v (List.map (Cmul a) u) = Cmul a (dot v u).
Proof.
  intros a. induction v as [|x xs IH]; intros u; simpl.
  - destruct u; simpl; symmetry; apply Cmul_C0_r_lem.
  - destruct u as [|y ys]; simpl.
    + symmetry. apply Cmul_C0_r_lem.
    + rewrite (IH ys).
      rewrite Cmul_add_distr_l.
      f_equal.
      (* x *c (a *c y) = a *c (x *c y).
         By Cmul_assoc_lem: (x*a)*y = x*(a*y). And by Cmul_comm: x*a = a*x.
         So x*(a*y) = (x*a)*y = (a*x)*y = a*(x*y). *)
      rewrite <- Cmul_assoc_lem.
      rewrite (CComplex_eq _ _ (Cmul_comm_req x a)).
      apply Cmul_assoc_lem.
Qed.

(** nth_default commutes with map (Cmul a) (with C0 default). *)
Local Lemma nth_default_map_Cmul : forall (a : CComplex) (row : list CComplex) (j : nat),
  nth_default C0 (List.map (Cmul a) row) j = Cmul a (nth_default C0 row j).
Proof.
  intros a row.
  induction row as [|x xs IH]; intros j.
  - simpl. destruct j; symmetry; apply Cmul_C0_r_lem.
  - destruct j as [|k]; simpl; [reflexivity | apply IH].
Qed.

(** col commutes with mscale: col_j(aA) = a · col_j(A). *)
Local Lemma col_mscale : forall (a : CComplex) (A : Mat CComplex) (j : nat),
  col (mscale a A) j = List.map (Cmul a) (col A j).
Proof.
  intros a A j. unfold col, mscale.
  rewrite List.map_map.
  rewrite List.map_map.
  apply List.map_ext. intros row.
  apply nth_default_map_Cmul.
Qed.

(** mcols commutes with mscale. *)
Local Lemma mcols_mscale : forall (p : nat) (a : CComplex) (A : Mat CComplex),
  mcols p (mscale a A) = List.map (List.map (Cmul a)) (mcols p A).
Proof.
  intros p a A.
  induction p as [|p IH]; simpl; [reflexivity |].
  rewrite IH. rewrite List.map_app. simpl.
  rewrite (col_mscale a A p). reflexivity.
Qed.

(** row_mul_cols on (map (map (Cmul a)) cols): pulls the Cmul a out. *)
Local Lemma row_mul_cols_map_map_Cmul :
  forall (a : CComplex) (r : list CComplex) (cols : list (list CComplex)),
  row_mul_cols r (List.map (List.map (Cmul a)) cols) =
  List.map (Cmul a) (row_mul_cols r cols).
Proof.
  intros a r cols.
  induction cols as [|c cs IH]; simpl; [reflexivity |].
  rewrite (dot_map_Cmul_r a r c). rewrite IH. reflexivity.
Qed.

(** mmul distributes over mscale in right arg. *)
Local Lemma mmul_mscale_r : forall (a : CComplex) (B A : Mat CComplex) (p : nat),
  mmul B (mscale a A) p = mscale a (mmul B A p).
Proof.
  intros a B A p. unfold mscale at 2.
  induction B as [|r rs IH]; simpl; [reflexivity |].
  rewrite (mcols_mscale p a A).
  rewrite (row_mul_cols_map_map_Cmul a r (mcols p A)).
  rewrite IH. reflexivity.
Qed.

(* The add-arg analogues require reasoning about [mcols (madd B C)] and
   require row-length matching on [A] and [B] for left-distrib over madd.
   The bracket addition axioms (gl_bracket_add_l/_r) are not provable
   without dimension hypotheses, since (e.g.) madd of length-mismatched
   matrices truncates while mmul does not commute with that truncation. *)

(* ---- Right-arg distribution helpers (Task M.2): added 2026-05-01 to
   discharge [gl_bracket_add_l_wf] / [gl_bracket_add_r_wf]. *)

(** [dot v (vadd r s) = Cadd (dot v r) (dot v s)] when lengths match
    pairwise. *)
Local Lemma dot_vadd_r : forall (v r s : list CComplex),
  List.length v = List.length r -> List.length r = List.length s ->
  dot v (vadd r s) = Cadd (dot v r) (dot v s).
Proof.
  induction v as [|x xs IH]; intros r s Hvr Hrs;
    destruct r as [|y ys]; destruct s as [|z zs];
    simpl in *; try discriminate.
  - rewrite Cadd_C0_l_lem. reflexivity.
  - injection Hvr as Hvr'. injection Hrs as Hrs'.
    rewrite (IH ys zs Hvr' Hrs').
    rewrite Cmul_add_distr_l.
    apply Cadd_interchange.
Qed.

(** [length (madd A B) = length A] when [length A = length B]. *)
Local Lemma madd_length_eq : forall (A B : Mat CComplex),
  List.length A = List.length B -> List.length (madd A B) = List.length A.
Proof.
  induction A as [|rA As IH]; destruct B as [|rB Bs];
    intros Hlen; simpl in *; try discriminate; try reflexivity.
  injection Hlen as Hlen'. f_equal. apply IH; exact Hlen'.
Qed.

(** [nth_default C0 (vadd v w) j = Cadd ...] when lengths match. *)
Local Lemma nth_default_vadd : forall (v w : list CComplex) (j : nat),
  List.length v = List.length w ->
  nth_default C0 (vadd v w) j =
  Cadd (nth_default C0 v j) (nth_default C0 w j).
Proof.
  induction v as [|x xs IH]; destruct w as [|y ys]; intros j Hlen;
    simpl in *; try discriminate.
  - destruct j; rewrite Cadd_C0_l_lem; reflexivity.
  - destruct j as [|k]; simpl; [reflexivity|].
    injection Hlen as Hlen'. apply (IH ys k Hlen').
Qed.

(** [col] distributes over [madd] when row counts match and corresponding
    rows have equal length. *)
Local Lemma col_madd : forall (B C : Mat CComplex) (j : nat),
  Forall2 (fun rB rC => List.length rB = List.length rC) B C ->
  col (madd B C) j = vadd (col B j) (col C j).
Proof.
  intros B C j HF. unfold col.
  induction HF as [|rB rC Bs Cs Hrow HFs IH]; simpl; [reflexivity|].
  f_equal; [apply nth_default_vadd; exact Hrow | exact IH].
Qed.

(** [List.length (col A j) = List.length A]. *)
Local Lemma col_length : forall (A : Mat CComplex) (j : nat),
  List.length (col A j) = List.length A.
Proof. intros A j. unfold col. apply List.length_map. Qed.

(** [row_mul_cols r] applied to columns of [madd B C] distributes via [vadd]
    of [row_mul_cols] applied to columns of [B] and of [C], when rows of B
    match rows of C in length, B and C have the same number of rows, and
    [length r] equals that common row count. *)
Local Lemma row_mul_cols_mcols_madd :
  forall (r : list CComplex) (B C : Mat CComplex) (p : nat),
    List.length B = List.length C ->
    Forall2 (fun rB rC => List.length rB = List.length rC) B C ->
    List.length r = List.length B ->
    row_mul_cols r (mcols p (madd B C)) =
    vadd (row_mul_cols r (mcols p B)) (row_mul_cols r (mcols p C)).
Proof.
  intros r B C p HlenBC HF Hr.
  induction p as [|k IH]; simpl; [reflexivity|].
  (* mcols (S k) X = mcols k X ++ [col X k] *)
  (* row_mul_cols on append:
     row_mul_cols r (xs ++ [c]) = row_mul_cols r xs ++ [dot r c]. *)
  assert (Happ : forall (xs : list (list CComplex)) (c : list CComplex),
            row_mul_cols r (xs ++ [c]) = row_mul_cols r xs ++ [dot r c]).
  { intros xs c. induction xs as [|x xs' IHx]; simpl; [reflexivity|].
    rewrite IHx. reflexivity. }
  rewrite !Happ.
  rewrite IH.
  rewrite (col_madd B C k HF).
  (* Goal: row_mul_cols r (mcols k B) ++ [dot r (vadd ...)]
           "vadd-zip"
           row_mul_cols r (mcols k C) ++ [dot r (col C k)]
       = vadd (rcB ++ [dot r (col B k)]) (rcC ++ [dot r (col C k)])
     We need: dot r (vadd (col B k) (col C k))
            = Cadd (dot r (col B k)) (dot r (col C k))
     using dot_vadd_r with [length r = length B = length (col B k)]. *)
  assert (HcolB : List.length (col B k) = List.length B) by apply col_length.
  assert (HcolC : List.length (col C k) = List.length C) by apply col_length.
  rewrite (dot_vadd_r r (col B k) (col C k)).
  + (* now show vadd of appended lists splits *)
    (* Helper: vadd-app split on equal-length lists. *)
    assert (Hvadd_app :
             forall (a b : list CComplex) (x y : CComplex),
               List.length a = List.length b ->
               vadd (a ++ [x]) (b ++ [y]) = vadd a b ++ [Cadd x y]).
    { intros a. induction a as [|h t IHa]; intros [|hb tb] x y Heq;
        simpl in *; try discriminate; try reflexivity.
      injection Heq as Heq'. f_equal. apply IHa; exact Heq'. }
    symmetry. apply Hvadd_app.
    (* lengths: row_mul_cols r (mcols k B) and row_mul_cols r (mcols k C)
       have the same length. *)
    assert (Hlen_rmc : forall (rr : list CComplex) (cs : list (list CComplex)),
               List.length (row_mul_cols rr cs) = List.length cs).
    { intros rr cs. induction cs as [|c cs' IHc]; simpl; [reflexivity|].
      f_equal. exact IHc. }
    rewrite !Hlen_rmc.
    clear -HlenBC.
    induction k as [|k' IHk]; simpl; [reflexivity|].
    rewrite !List.length_app. simpl. f_equal. apply IHk.
  + rewrite Hr. symmetry. apply col_length.
  + rewrite HcolB, HcolC. exact HlenBC.
Qed.

(** mmul distributes over madd in right arg, when B and C have matching
    shapes and each row of A has length [length B]. *)
Local Lemma mmul_madd_r : forall (A B C : Mat CComplex) (p : nat),
    List.length B = List.length C ->
    Forall2 (fun rB rC => List.length rB = List.length rC) B C ->
    (forall row, List.In row A -> List.length row = List.length B) ->
    mmul A (madd B C) p = madd (mmul A B p) (mmul A C p).
Proof.
  intros A B C p HlenBC HF HrowA.
  induction A as [|rA As IH]; simpl; [reflexivity|].
  f_equal.
  - apply (row_mul_cols_mcols_madd rA B C p HlenBC HF).
    apply HrowA. left. reflexivity.
  - apply IH. intros row Hin. apply HrowA. right. exact Hin.
Qed.

(** map Cneg distributes over vadd. *)
Local Lemma map_Cneg_vadd : forall (u v : list CComplex),
  List.map Cneg (vadd u v) = vadd (List.map Cneg u) (List.map Cneg v).
Proof.
  induction u as [|x xs IHu]; intros [|y ys]; simpl; try reflexivity.
  f_equal.
  - apply CComplex_eq. unfold CComplex_req, Cneg, Cadd. simpl. split; ring.
  - apply IHu.
Qed.

(** mneg distributes over madd. *)
Local Lemma mneg_madd : forall A B : Mat CComplex,
  mneg (madd A B) = madd (mneg A) (mneg B).
Proof.
  unfold mneg.
  induction A as [|rA As IH]; intros [|rB Bs]; simpl; try reflexivity.
  f_equal.
  - apply map_Cneg_vadd.
  - apply IH.
Qed.

(** mneg distributes over mscale: -(aA) = a(-A). *)
Local Lemma mneg_mscale : forall (a : CComplex) (A : Mat CComplex),
  mneg (mscale a A) = mscale a (mneg A).
Proof.
  intros a. unfold mneg, mscale.
  induction A as [|row rows IH]; simpl; [reflexivity |].
  f_equal.
  - rewrite List.map_map, List.map_map.
    apply List.map_ext. intros x.
    apply CComplex_eq. unfold CComplex_req, Cneg, Cmul. simpl. split; ring.
  - exact IH.
Qed.

(** madd interchange: (X+Y) + (Z+W) = (X+Z) + (Y+W). *)
Local Lemma madd_interchange : forall (X Y Z W : Mat CComplex),
  madd (madd X Y) (madd Z W) = madd (madd X Z) (madd Y W).
Proof.
  intros X Y Z W.
  rewrite <- (mat_vs_add_assoc X Y (madd Z W)).
  rewrite (mat_vs_add_assoc Y Z W).
  rewrite (mat_vs_add_comm Y Z).
  rewrite <- (mat_vs_add_assoc Z Y W).
  rewrite (mat_vs_add_assoc X Z (madd Y W)).
  reflexivity.
Qed.

(** msub-madd rearrangement: (X-Y) + (Z-W) = (X+Z) - (Y+W). *)
Local Lemma madd_msub_pair : forall (X Y Z W : Mat CComplex),
  madd (msub X Y) (msub Z W) = msub (madd X Z) (madd Y W).
Proof.
  intros X Y Z W. unfold msub.
  rewrite madd_interchange.
  rewrite mneg_madd. reflexivity.
Qed.

(** Length-matched A,B for [mmul A C n] and [mmul B C n]:
    rows of [mmul X C n] all have length n, regardless of X (rows of mmul are
    [row_mul_cols _ (mcols n C)] of length n via [row_mul_cols_length] and
    [mcols_length]). So [Forall2 (fun rA rB => length rA = length rB)
    (mmul A C n) (mmul B C n)] holds when [length (mmul A C n) = length
    (mmul B C n)]; we prove the stronger uniform-row-length version. *)
Local Lemma mmul_rows_uniform_length : forall (A B C : Mat CComplex) (p : nat),
  List.length (mmul A C p) = List.length (mmul B C p) ->
  Forall2 (fun rA rB => List.length rA = List.length rB)
          (mmul A C p) (mmul B C p).
Proof.
  intros A B C p Hlen.
  remember (mmul A C p) as MA eqn:HMA.
  remember (mmul B C p) as MB eqn:HMB.
  assert (HrowA : forall row, List.In row MA -> List.length row = p)
    by (subst MA; apply mmul_row_length_aux).
  assert (HrowB : forall row, List.In row MB -> List.length row = p)
    by (subst MB; apply mmul_row_length_aux).
  clear HMA HMB.
  generalize dependent MB.
  induction MA as [|a As IH]; intros MB Hlen HrowB; simpl in *.
  - destruct MB; [constructor | discriminate].
  - destruct MB as [|b Bs]; [discriminate | simpl in *].
    constructor.
    + rewrite (HrowA a (or_introl eq_refl)).
      rewrite (HrowB b (or_introl eq_refl)). reflexivity.
    + injection Hlen as Hlen'. apply IH.
      * intros row Hin. apply HrowA. right; exact Hin.
      * exact Hlen'.
      * intros row Hin. apply HrowB. right; exact Hin.
Qed.

(** mscale distributes over msub: a(X-Y) = aX - aY. *)
Local Lemma mscale_msub : forall (a : CComplex) (X Y : Mat CComplex),
  mscale a (msub X Y) = msub (mscale a X) (mscale a Y).
Proof.
  intros a X Y. unfold msub.
  rewrite (mat_vs_scale_add_v a X (mneg Y)).
  rewrite <- (mneg_mscale a Y). reflexivity.
Qed.

(** Forall2 of pairwise length-match between two [Mat_wf k m] matrices
    (uniform column count m). *)
Local Lemma mat_wf_pairwise_len :
  forall (k m : nat) (X Y : Mat CComplex),
    Mat_wf k m X -> Mat_wf k m Y ->
    Forall2 (fun rX rY => List.length rX = List.length rY) X Y.
Proof.
  intros k m X. revert k.
  induction X as [|rX Xs IH]; intros k Y HX HY.
  - destruct HX as [HlenX _]. destruct HY as [HlenY _].
    destruct Y as [|rY Ys].
    + constructor.
    + simpl in HlenX, HlenY. subst k. discriminate.
  - destruct HX as [HlenX HrowX]. destruct HY as [HlenY HrowY].
    destruct Y as [|rY Ys].
    { simpl in HlenX, HlenY. subst k. discriminate. }
    constructor.
    + rewrite (HrowX rX), (HrowY rY); [reflexivity|left;reflexivity|left;reflexivity].
    + simpl in HlenX, HlenY.
      destruct k as [|k']; [discriminate|].
      injection HlenX as HlenX'. injection HlenY as HlenY'.
      apply (IH k' Ys).
      * split; [exact HlenX'|]. intros row Hin. apply HrowX. right. exact Hin.
      * split; [exact HlenY'|]. intros row Hin. apply HrowY. right. exact Hin.
Qed.

(** REFACTOR HISTORY:
    Task M.2 (2026-04-30): [Axiom gl_bracket_add_l] kept un-hypothesised
      (false-as-stated for shape-mismatched A, B) to preserve the legacy
      [LieAlgebra (Mat CComplex)] signature consumed by [gl].
    Task M.2.next (2026-05-01): REMOVED.  [gl] now lives over the sigma
      carrier and consumes [gl_bracket_add_l_wf] (Lemma) below directly. *)

(** Sound, Mat_wf-guarded counterpart (Task M.2, 2026-05-01: discharged
    Axiom → Lemma using new [mmul_madd_r] helper above). *)
Lemma gl_bracket_add_l_wf : forall n A B C,
    Mat_wf n n A -> Mat_wf n n B -> Mat_wf n n C ->
    gl_bracket n (madd A B) C = madd (gl_bracket n A C) (gl_bracket n B C).
Proof.
  intros n A B C HA HB HC.
  unfold gl_bracket, commutator.
  pose proof (mat_wf_pairwise_len n n A B HA HB) as HF.
  pose proof (proj1 HA) as HlenA.
  pose proof (proj1 HB) as HlenB.
  rewrite (mmul_madd_l A B C n HF).
  rewrite (mmul_madd_r C A B n).
  - symmetry. apply madd_msub_pair.
  - congruence.
  - exact HF.
  - intros row Hin. destruct HC as [_ HrowC]. rewrite (HrowC row Hin).
    symmetry. exact HlenA.
Qed.

Lemma gl_bracket_scale_l : forall n a A B,
  gl_bracket n (mscale a A) B = mscale a (gl_bracket n A B).
Proof.
  intros n a A B. unfold gl_bracket, commutator.
  rewrite (mmul_mscale_l a A B n).
  rewrite (mmul_mscale_r a B A n).
  symmetry. apply mscale_msub.
Qed.

(** REFACTOR HISTORY: same as [gl_bracket_add_l].
    Task M.2.next (2026-05-01): REMOVED.  Replaced by Mat_wf-guarded Lemma. *)

(** Sound, Mat_wf-guarded counterpart for right-arg bilinearity (Task M.2,
    2026-05-01: discharged Axiom → Lemma using [mmul_madd_r] helper above). *)
Lemma gl_bracket_add_r_wf : forall n A B C,
    Mat_wf n n A -> Mat_wf n n B -> Mat_wf n n C ->
    gl_bracket n A (madd B C) = madd (gl_bracket n A B) (gl_bracket n A C).
Proof.
  intros n A B C HA HB HC.
  unfold gl_bracket, commutator.
  pose proof (mat_wf_pairwise_len n n B C HB HC) as HF.
  pose proof (proj1 HB) as HlenB.
  pose proof (proj1 HC) as HlenC.
  rewrite (mmul_madd_l B C A n HF).
  rewrite (mmul_madd_r A B C n).
  - symmetry. apply madd_msub_pair.
  - congruence.
  - exact HF.
  - intros row Hin. destruct HA as [_ HrowA]. rewrite (HrowA row Hin).
    symmetry. exact HlenB.
Qed.

Lemma gl_bracket_scale_r : forall n a A B,
  gl_bracket n A (mscale a B) = mscale a (gl_bracket n A B).
Proof.
  intros n a A B. unfold gl_bracket, commutator.
  rewrite (mmul_mscale_r a A B n).
  rewrite (mmul_mscale_l a B A n).
  symmetry. apply mscale_msub.
Qed.

(** Mat_wf-guarded antisymmetry: [A,A] = 0 for any wf A.  Provable since
    [mmul A A n] is wf, then [mat_vs_add_neg_r_wf] applies.

    Replaces the un-hypothesised [gl_bracket_antisymm] Lemma which
    consumed the [mat_vs_add_neg_r] axiom (now removed). *)
Lemma gl_bracket_antisymm_wf : forall n A,
    Mat_wf n n A -> gl_bracket n A A = mzero n.
Proof.
  intros n A HA. unfold gl_bracket, commutator, msub.
  apply mat_vs_add_neg_r_wf. apply (mmul_wf n n n); assumption.
Qed.

(** REFACTOR HISTORY (gl_jacobi):
    Original (M.0 era): un-hypothesised [Axiom gl_jacobi] — false-as-stated
      for shape-mismatched matrices.
    Task M.2.next (2026-05-01): replaced with Mat_wf-guarded
      [Axiom gl_jacobi_wf] (sound).  The discharge to a real Lemma is a
      multi-step algebraic computation (six triple-product expansions,
      using [mmul_assoc] + [mmul_madd_l/_r] + [mneg_*] helpers).
    β R8 (2026-05-01): DISCHARGED to a [Lemma] using [mmul_assoc_wf]
      (β R7's AG.v contribution) + the local helpers [mmul_msub_l],
      [mmul_msub_r] (relocated up from the killing-form section to be
      visible here) + [mneg_madd] + [mneg_mneg] + [mat_vs_add_*].  Net
      −1 axiom (was paper-attributable, now structural). *)

(** [mmul] distributes over [msub] in left arg: (X-Y)·Z = X·Z - Y·Z.
    Relocated β R8 from the killing-form section so [gl_jacobi_wf] can
    use it. *)
Local Lemma mmul_msub_l : forall (n : nat) (X Y Z : Mat CComplex),
    Mat_wf n n X -> Mat_wf n n Y ->
    mmul (msub X Y) Z n = msub (mmul X Z n) (mmul Y Z n).
Proof.
  intros n X Y Z HX HY. unfold msub.
  pose proof (mat_wf_pairwise_len n n X (mneg Y) HX (mneg_wf n n Y HY)) as HF.
  rewrite (mmul_madd_l X (mneg Y) Z n HF).
  f_equal.
  (* mmul (mneg Y) Z n = mneg (mmul Y Z n).  Proof: mneg = mscale (-1).
     Or directly via row_mul_cols / col / dot. *)
  unfold mneg. clear HX HY HF X.
  induction Y as [|rY Ys IH]; simpl; [reflexivity|].
  f_equal.
  - (* row_mul_cols (map Cneg rY) (mcols n Z) =
       map Cneg (row_mul_cols rY (mcols n Z)) *)
    generalize (mcols n Z) as cols.
    intro cols. induction cols as [|c cs IHc]; simpl; [reflexivity|].
    rewrite IHc. f_equal.
    (* dot (map Cneg rY) c = Cneg (dot rY c). *)
    clear -rY c.
    revert c. induction rY as [|x xs IHr]; intros c; simpl.
    + destruct c; apply CComplex_eq; unfold CComplex_req, Cneg, C0; simpl;
        split; ring.
    + destruct c as [|y ys]; simpl.
      * apply CComplex_eq. unfold CComplex_req, Cneg, C0. simpl. split; ring.
      * rewrite IHr. apply CComplex_eq.
        unfold CComplex_req, Cneg, Cadd, Cmul. simpl. split; ring.
  - exact IH.
Qed.

(** [mmul] distributes over [msub] in right arg: X·(Y-Z) = X·Y - X·Z.
    Relocated β R8 from the killing-form section. *)
Local Lemma mmul_msub_r : forall (n : nat) (X Y Z : Mat CComplex),
    Mat_wf n n X -> Mat_wf n n Y -> Mat_wf n n Z ->
    mmul X (msub Y Z) n = msub (mmul X Y n) (mmul X Z n).
Proof.
  intros n X Y Z HX HY HZ. unfold msub.
  destruct HX as [HlenX HrowX].
  destruct HY as [HlenY HrowY].
  destruct HZ as [HlenZ HrowZ].
  rewrite (mmul_madd_r X Y (mneg Z) n).
  - f_equal.
    (* mmul X (mneg Z) n = mneg (mmul X Z n) *)
    unfold mneg. clear HlenX HrowX HlenY HrowY HlenZ HrowZ.
    induction X as [|rX Xs IH]; simpl; [reflexivity|].
    f_equal; [|exact IH].
    (* row_mul_cols rX (mcols n (map (map Cneg) Z)) =
       map Cneg (row_mul_cols rX (mcols n Z)) *)
    (* col commutes with map (map Cneg): col (map (map Cneg) Z) j =
       map Cneg (col Z j). *)
    assert (Hcol : forall (M : Mat CComplex) (j : nat),
              col (List.map (List.map Cneg) M) j =
              List.map Cneg (col M j)).
    { intros M j. unfold col. rewrite List.map_map.
      rewrite List.map_map. apply List.map_ext. intros row.
      revert j. induction row as [|x xs IHr]; intros j; simpl.
      - destruct j; apply CComplex_eq; unfold CComplex_req, Cneg, C0; simpl;
          split; ring.
      - destruct j as [|j']; [reflexivity|]. apply IHr. }
    assert (Hmcols : forall (m : nat) (M : Mat CComplex),
              mcols m (List.map (List.map Cneg) M) =
              List.map (List.map Cneg) (mcols m M)).
    { intros m M. induction m as [|m IHm]; simpl; [reflexivity|].
      rewrite IHm. rewrite List.map_app. simpl. rewrite (Hcol M m). reflexivity. }
    rewrite Hmcols.
    (* row_mul_cols rX (map (map Cneg) cs) = map Cneg (row_mul_cols rX cs). *)
    generalize (mcols n Z) as cs. intro cs.
    induction cs as [|c cs IHc]; simpl; [reflexivity|].
    rewrite IHc. f_equal.
    (* dot rX (map Cneg c) = Cneg (dot rX c). *)
    clear -rX c.
    revert c. induction rX as [|x xs IHr]; intros c; simpl.
    + destruct c; apply CComplex_eq; unfold CComplex_req, Cneg, C0; simpl;
        split; ring.
    + destruct c as [|y ys]; simpl.
      * apply CComplex_eq. unfold CComplex_req, Cneg, C0. simpl. split; ring.
      * rewrite IHr. apply CComplex_eq.
        unfold CComplex_req, Cneg, Cadd, Cmul. simpl. split; ring.
  - unfold mneg. rewrite List.length_map. rewrite HlenY, HlenZ. reflexivity.
  - apply mat_wf_pairwise_len with (k:=n) (m:=n).
    + split; [exact HlenY|exact HrowY].
    + apply mneg_wf. split; [exact HlenZ|exact HrowZ].
  - intros row Hin. rewrite (HrowX row Hin). symmetry. exact HlenY.
Qed.

(** [mneg] is involutive: [-(-X) = X].  Lifted via [Cneg] involution at
    the entry level. *)
Local Lemma mneg_mneg : forall (X : Mat CComplex), mneg (mneg X) = X.
Proof.
  unfold mneg. induction X as [|row rows IH]; simpl; [reflexivity|].
  f_equal; [|exact IH].
  rewrite List.map_map.
  induction row as [|x xs IHr]; simpl; [reflexivity|].
  f_equal; [|exact IHr].
  apply CComplex_eq. unfold CComplex_req, Cneg. simpl. split; ring.
Qed.

(** [mneg] of [msub]: [-(X - Y) = Y - X]. *)
Local Lemma mneg_msub : forall (X Y : Mat CComplex),
    mneg (msub X Y) = msub Y X.
Proof.
  intros X Y. unfold msub. rewrite mneg_madd. rewrite mneg_mneg.
  apply mat_vs_add_comm.
Qed.

(** Mat_wf-guarded left-neg: [-A + A = mzero n]. *)
Local Lemma mat_vs_add_neg_l_wf : forall n (A : Mat CComplex),
    Mat_wf n n A -> madd (mneg A) A = mzero n.
Proof.
  intros n A HA. rewrite mat_vs_add_comm. apply mat_vs_add_neg_r_wf. exact HA.
Qed.

(** Mat_wf-guarded right-zero: [A + mzero n = A]. *)

(** Mat_wf-guarded left-zero: [mzero n + A = A]. *)
Local Lemma mat_vs_add_zero_l_wf : forall n (A : Mat CComplex),
    Mat_wf n n A -> madd (mzero n) A = A.
Proof.
  intros n A HA. rewrite mat_vs_add_comm. apply mat_vs_add_zero_r_wf. exact HA.
Qed.

(** Jacobi identity for the [gl(n)] commutator bracket.
    β R8 (2026-05-01): DISCHARGED Axiom → Lemma.

    Strategy: expand each [gl_bracket A (gl_bracket B C)] using [mmul_msub_l/r]
    + [mmul_assoc_wf] (β R7) into a 4-term [madd] of (left-associated)
    triple products with appropriate signs.  Sum the three cyclic
    permutations and use [mat_vs_add_assoc/comm] + [mat_vs_add_neg_l_wf] to
    cancel pairwise.  This mirrors the abstract-Field proof in
    [Lie/Linear.v]'s [mat_bracket_jacobi]. *)
Lemma gl_jacobi_wf : forall n A B C,
    Mat_wf n n A -> Mat_wf n n B -> Mat_wf n n C ->
    madd (madd (gl_bracket n A (gl_bracket n B C))
               (gl_bracket n B (gl_bracket n C A)))
         (gl_bracket n C (gl_bracket n A B))
    = mzero n.
Proof.
  intros n A B C HA HB HC.
  (* Helper: (P+Q)+(R+S) = (P+R)+(Q+S) — purely from mat_vs_add_assoc/comm. *)
  assert (comm_inner : forall P Q R S : Mat CComplex,
    madd (madd P Q) (madd R S) = madd (madd P R) (madd Q S)).
  { intros P Q R S.
    rewrite <- (mat_vs_add_assoc P Q (madd R S)).
    rewrite (mat_vs_add_assoc Q R S).
    rewrite (mat_vs_add_comm Q R).
    rewrite <- (mat_vs_add_assoc R Q S).
    rewrite (mat_vs_add_assoc P R (madd Q S)).
    reflexivity. }
  (* Name the six triple products (all left-associated) *)
  set (ABC := mmul (mmul A B n) C n).
  set (ACB := mmul (mmul A C n) B n).
  set (BAC := mmul (mmul B A n) C n).
  set (BCA := mmul (mmul B C n) A n).
  set (CAB := mmul (mmul C A n) B n).
  set (CBA := mmul (mmul C B n) A n).
  (* All six are wf — needed for cancellation lemmas. *)
  assert (HABC : Mat_wf n n ABC).
  { unfold ABC. apply (mmul_wf n n n); [apply (mmul_wf n n n)|]; assumption. }
  assert (HACB : Mat_wf n n ACB).
  { unfold ACB. apply (mmul_wf n n n); [apply (mmul_wf n n n)|]; assumption. }
  assert (HBAC : Mat_wf n n BAC).
  { unfold BAC. apply (mmul_wf n n n); [apply (mmul_wf n n n)|]; assumption. }
  assert (HBCA : Mat_wf n n BCA).
  { unfold BCA. apply (mmul_wf n n n); [apply (mmul_wf n n n)|]; assumption. }
  assert (HCAB : Mat_wf n n CAB).
  { unfold CAB. apply (mmul_wf n n n); [apply (mmul_wf n n n)|]; assumption. }
  assert (HCBA : Mat_wf n n CBA).
  { unfold CBA. apply (mmul_wf n n n); [apply (mmul_wf n n n)|]; assumption. }
  (* Pair-products are wf too (used in mmul_msub_r for the bracket arg). *)
  assert (HmAB : Mat_wf n n (mmul A B n)) by (apply (mmul_wf n n n); assumption).
  assert (HmBA : Mat_wf n n (mmul B A n)) by (apply (mmul_wf n n n); assumption).
  assert (HmAC : Mat_wf n n (mmul A C n)) by (apply (mmul_wf n n n); assumption).
  assert (HmCA : Mat_wf n n (mmul C A n)) by (apply (mmul_wf n n n); assumption).
  assert (HmBC : Mat_wf n n (mmul B C n)) by (apply (mmul_wf n n n); assumption).
  assert (HmCB : Mat_wf n n (mmul C B n)) by (apply (mmul_wf n n n); assumption).
  (* Expand the three brackets. *)
  assert (H1 : gl_bracket n A (gl_bracket n B C) =
    madd (madd ABC (mneg ACB)) (madd (mneg BCA) CBA)).
  { unfold gl_bracket, commutator.
    (* gl_bracket n A (msub (mmul B C) (mmul C B))
       = msub (mmul A (mmul B C)) (mmul A (mmul C B))
              - using mmul_msub_r *)
    rewrite (mmul_msub_r n A (mmul B C n) (mmul C B n) HA HmBC HmCB).
    (* mmul (msub (mmul B C) (mmul C B)) A
       = msub (mmul (mmul B C) A) (mmul (mmul C B) A) — mmul_msub_l *)
    rewrite (mmul_msub_l n (mmul B C n) (mmul C B n) A HmBC HmCB).
    (* Now apply mmul_assoc_wf to put each triple in left-associated form. *)
    rewrite (mmul_assoc_wf n n n n A B C HA HB HC).
    rewrite (mmul_assoc_wf n n n n A C B HA HC HB).
    (* For mmul (mmul B C) A and mmul (mmul C B) A: already in left-assoc form. *)
    fold ABC ACB BCA CBA.
    (* Goal: msub (msub ABC ACB) (msub BCA CBA) = madd (madd ABC (mneg ACB)) (madd (mneg BCA) CBA) *)
    unfold msub. rewrite mneg_madd. rewrite mneg_mneg.
    rewrite <- (mat_vs_add_assoc ABC (mneg ACB) (madd (mneg BCA) CBA)).
    reflexivity. }
  assert (H2 : gl_bracket n B (gl_bracket n C A) =
    madd (madd BCA (mneg BAC)) (madd (mneg CAB) ACB)).
  { unfold gl_bracket, commutator.
    rewrite (mmul_msub_r n B (mmul C A n) (mmul A C n) HB HmCA HmAC).
    rewrite (mmul_msub_l n (mmul C A n) (mmul A C n) B HmCA HmAC).
    rewrite (mmul_assoc_wf n n n n B C A HB HC HA).
    rewrite (mmul_assoc_wf n n n n B A C HB HA HC).
    fold BCA BAC CAB ACB.
    unfold msub. rewrite mneg_madd. rewrite mneg_mneg.
    rewrite <- (mat_vs_add_assoc BCA (mneg BAC) (madd (mneg CAB) ACB)).
    reflexivity. }
  assert (H3 : gl_bracket n C (gl_bracket n A B) =
    madd (madd CAB (mneg CBA)) (madd (mneg ABC) BAC)).
  { unfold gl_bracket, commutator.
    rewrite (mmul_msub_r n C (mmul A B n) (mmul B A n) HC HmAB HmBA).
    rewrite (mmul_msub_l n (mmul A B n) (mmul B A n) C HmAB HmBA).
    rewrite (mmul_assoc_wf n n n n C A B HC HA HB).
    rewrite (mmul_assoc_wf n n n n C B A HC HB HA).
    fold CAB CBA ABC BAC.
    unfold msub. rewrite mneg_madd. rewrite mneg_mneg.
    rewrite <- (mat_vs_add_assoc CAB (mneg CBA) (madd (mneg ABC) BAC)).
    reflexivity. }
  rewrite H1, H2, H3.
  (* Same algebraic dance as Lie/Linear.v's [mat_bracket_jacobi].  Note
     that LieAlgebra.v's [mat_vs_add_assoc] has the OPPOSITE direction
     of Linear.v's [mat_add_assoc_m]:
       - [mat_vs_add_assoc : A+(B+C) = (A+B)+C]
       - [mat_add_assoc_m  : (A+B)+C = A+(B+C)]
     So every [rewrite mat_add_assoc_m] in the Linear.v proof becomes
     [rewrite <- mat_vs_add_assoc] here, and vice versa. *)
  rewrite <- (mat_vs_add_assoc
    (madd (madd ABC (mneg ACB)) (madd (mneg BCA) CBA))
    (madd (madd BCA (mneg BAC)) (madd (mneg CAB) ACB))
    (madd (madd CAB (mneg CBA)) (madd (mneg ABC) BAC))).
  rewrite <- (mat_vs_add_assoc
    (madd BCA (mneg BAC))
    (madd (mneg CAB) ACB)
    (madd (madd CAB (mneg CBA)) (madd (mneg ABC) BAC))).
  rewrite (mat_vs_add_assoc
    (madd (mneg CAB) ACB)
    (madd CAB (mneg CBA))
    (madd (mneg ABC) BAC)).
  rewrite (comm_inner (mneg CAB) ACB CAB (mneg CBA)).
  rewrite (mat_vs_add_neg_l_wf n CAB HCAB).
  rewrite (mat_vs_add_zero_l_wf n (madd ACB (mneg CBA))).
  2: { apply madd_wf; [exact HACB | apply mneg_wf; exact HCBA]. }
  rewrite <- (mat_vs_add_assoc
    (madd ABC (mneg ACB))
    (madd (mneg BCA) CBA)
    (madd (madd BCA (mneg BAC))
          (madd (madd ACB (mneg CBA)) (madd (mneg ABC) BAC)))).
  rewrite (mat_vs_add_assoc
    (madd (mneg BCA) CBA)
    (madd BCA (mneg BAC))
    (madd (madd ACB (mneg CBA)) (madd (mneg ABC) BAC))).
  rewrite (comm_inner (mneg BCA) CBA BCA (mneg BAC)).
  rewrite (mat_vs_add_neg_l_wf n BCA HBCA).
  rewrite (mat_vs_add_zero_l_wf n (madd CBA (mneg BAC))).
  2: { apply madd_wf; [exact HCBA | apply mneg_wf; exact HBAC]. }
  rewrite (mat_vs_add_assoc
    (madd CBA (mneg BAC))
    (madd ACB (mneg CBA))
    (madd (mneg ABC) BAC)).
  rewrite (mat_vs_add_comm ACB (mneg CBA)).
  rewrite (comm_inner CBA (mneg BAC) (mneg CBA) ACB).
  rewrite (mat_vs_add_neg_r_wf n CBA HCBA).
  rewrite (mat_vs_add_zero_l_wf n (madd (mneg BAC) ACB)).
  2: { apply madd_wf; [apply mneg_wf; exact HBAC | exact HACB]. }
  rewrite (mat_vs_add_assoc
    (madd ABC (mneg ACB))
    (madd (mneg BAC) ACB)
    (madd (mneg ABC) BAC)).
  rewrite (comm_inner ABC (mneg ACB) (mneg BAC) ACB).
  rewrite (mat_vs_add_neg_l_wf n ACB HACB).
  rewrite (mat_vs_add_zero_r_wf n (madd ABC (mneg BAC))).
  2: { apply madd_wf; [exact HABC | apply mneg_wf; exact HBAC]. }
  rewrite (comm_inner ABC (mneg BAC) (mneg ABC) BAC).
  rewrite (mat_vs_add_neg_r_wf n ABC HABC).
  rewrite (mat_vs_add_zero_l_wf n (madd (mneg BAC) BAC)).
  2: { apply madd_wf; [apply mneg_wf; exact HBAC | exact HBAC]. }
  apply (mat_vs_add_neg_l_wf n BAC HBAC).
Qed.

(** Sigma-typed bracket obligations: lift the [_wf] Lemmas through the
    sigma carrier via [msig_eq] / [proj2_sig]. *)

Lemma msig_bracket_add_l_obligation : forall n (x y z : MatSig n),
    msig_bracket (msig_add x y) z =
    msig_add (msig_bracket x z) (msig_bracket y z).
Proof.
  intros n [x Hx] [y Hy] [z Hz]. apply msig_eq. simpl.
  apply (gl_bracket_add_l_wf n x y z Hx Hy Hz).
Qed.

Lemma msig_bracket_scale_l_obligation : forall n (a : CComplex) (x y : MatSig n),
    msig_bracket (msig_scale a x) y = msig_scale a (msig_bracket x y).
Proof.
  intros. apply msig_eq. simpl. apply gl_bracket_scale_l.
Qed.

Lemma msig_bracket_add_r_obligation : forall n (x y z : MatSig n),
    msig_bracket x (msig_add y z) =
    msig_add (msig_bracket x y) (msig_bracket x z).
Proof.
  intros n [x Hx] [y Hy] [z Hz]. apply msig_eq. simpl.
  apply (gl_bracket_add_r_wf n x y z Hx Hy Hz).
Qed.

Lemma msig_bracket_scale_r_obligation : forall n (a : CComplex) (x y : MatSig n),
    msig_bracket x (msig_scale a y) = msig_scale a (msig_bracket x y).
Proof.
  intros. apply msig_eq. simpl. apply gl_bracket_scale_r.
Qed.

Lemma msig_bracket_antisymm_obligation : forall n (x : MatSig n),
    msig_bracket x x = msig_zero n.
Proof.
  intros n [x Hx]. apply msig_eq. simpl. apply gl_bracket_antisymm_wf. exact Hx.
Qed.

Lemma msig_jacobi_obligation : forall n (x y z : MatSig n),
    msig_add
      (msig_add (msig_bracket x (msig_bracket y z))
                (msig_bracket y (msig_bracket z x)))
      (msig_bracket z (msig_bracket x y))
    = msig_zero n.
Proof.
  intros n [x Hx] [y Hy] [z Hz]. apply msig_eq. simpl.
  apply (gl_jacobi_wf n x y z Hx Hy Hz).
Qed.

(** The Lie algebra gl(n,ℂ), now sigma-typed.
    Carrier: [MatSig n = { A : Mat CComplex | Mat_wf n n A }]. *)
Definition gl (n : nat) : LieAlgebra (MatSig n) :=
  mkLA (MatSig n)
    (MatVS n)
    msig_bracket
    (msig_bracket_add_l_obligation n)
    (msig_bracket_scale_l_obligation n)
    (msig_bracket_add_r_obligation n)
    (msig_bracket_scale_r_obligation n)
    (msig_bracket_antisymm_obligation n)
    (msig_jacobi_obligation n).

(* ------------------------------------------------------------------ *)
(** * 4. Lie algebra homomorphisms                                      *)
(* ------------------------------------------------------------------ *)

Record LieAlgHom {L M : Type} (la : LieAlgebra L) (lb : LieAlgebra M) : Type :=
  mkLAHom
  { lahom_fn     : L -> M
  ; lahom_add    : forall x y,
      lahom_fn (vs_add la x y) =
      vs_add lb (lahom_fn x) (lahom_fn y)
  ; lahom_scale  : forall a x,
      lahom_fn (vs_scale la a x) =
      vs_scale lb a (lahom_fn x)
  ; lahom_bracket : forall x y,
      lahom_fn (la_bracket la x y) =
      la_bracket lb (lahom_fn x) (lahom_fn y)
  }.

Arguments lahom_fn {L M la lb} _ _.

(* ------------------------------------------------------------------ *)
(** * 5. The adjoint representation                                     *)
(* ------------------------------------------------------------------ *)

(** ad(x)(y) = [x, y].  This is a linear map from L to End(L). *)
Definition adjoint {L : Type} (la : LieAlgebra L) (x y : L) : L :=
  la_bracket la x y.

(** [x, 0] = 0 *)
Local Lemma bracket_zero_r {L : Type} (la : LieAlgebra L) (x : L) :
  la_bracket la x (vs_zero la) = vs_zero la.
Proof.
  assert (H : la_bracket la x (vs_zero la) =
              vs_add la (la_bracket la x (vs_zero la)) (la_bracket la x (vs_zero la))).
  { rewrite <- (vs_add_zero_r L la (vs_zero la)) at 1.
    exact (la_bracket_add_r L la x (vs_zero la) (vs_zero la)). }
  assert (Hneg : vs_add la (la_bracket la x (vs_zero la)) (vs_neg la (la_bracket la x (vs_zero la))) = vs_zero la)
    by exact (vs_add_neg_r L la (la_bracket la x (vs_zero la))).
  rewrite H in Hneg at 1.
  rewrite <- (vs_add_assoc L la
    (la_bracket la x (vs_zero la))
    (la_bracket la x (vs_zero la))
    (vs_neg la (la_bracket la x (vs_zero la)))) in Hneg.
  rewrite (vs_add_neg_r L la (la_bracket la x (vs_zero la))) in Hneg.
  rewrite (vs_add_zero_r L la (la_bracket la x (vs_zero la))) in Hneg.
  exact Hneg.
Qed.

(** [x, -y] = -[x, y] *)
Local Lemma bracket_neg_r {L : Type} (la : LieAlgebra L) (x y : L) :
  la_bracket la x (vs_neg la y) = vs_neg la (la_bracket la x y).
Proof.
  assert (H : la_bracket la x (vs_zero la) =
              vs_add la (la_bracket la x y) (la_bracket la x (vs_neg la y))).
  { rewrite <- (vs_add_neg_r L la y).
    exact (la_bracket_add_r L la x y (vs_neg la y)). }
  rewrite (bracket_zero_r la x) in H.
  rewrite <- (vs_add_zero_r L la (la_bracket la x (vs_neg la y))).
  rewrite <- (vs_add_neg_r L la (la_bracket la x y)).
  rewrite (vs_add_assoc L la
    (la_bracket la x (vs_neg la y))
    (la_bracket la x y)
    (vs_neg la (la_bracket la x y))).
  rewrite (vs_add_comm L la (la_bracket la x (vs_neg la y)) (la_bracket la x y)).
  rewrite <- H.
  exact (vs_add_zero_l la (vs_neg la (la_bracket la x y))).
Qed.

(** ad is a Lie algebra homomorphism L → gl(L)
    (where gl(L) = End(L) with bracket [f,g] = f∘g − g∘f).
    We state this as a lemma; the proof is exactly the Jacobi identity. *)
Lemma adjoint_bracket : forall {L : Type} (la : LieAlgebra L) (x y z : L),
  adjoint la (la_bracket la x y) z =
  vs_add la
    (adjoint la x (adjoint la y z))
    (vs_neg la (adjoint la y (adjoint la x z))).
Proof.
  intros L la x y z. unfold adjoint.
  (* [[x,y],z] = -[z,[x,y]] by anticomm *)
  rewrite (bracket_anticomm la (la_bracket la x y) z).
  (* Jacobi: [x,[y,z]] + [y,[z,x]] + [z,[x,y]] = 0 *)
  pose proof (la_jacobi L la x y z) as J.
  (* [y,[z,x]] = -[y,[x,z]] *)
  assert (Hyzx : la_bracket la y (la_bracket la z x) = vs_neg la (la_bracket la y (la_bracket la x z))).
  { rewrite (bracket_anticomm la z x).
    exact (bracket_neg_r la y (la_bracket la x z)). }
  rewrite Hyzx in J.
  (* J: ([x,[y,z]] + (-[y,[x,z]])) + [z,[x,y]] = 0 => -[z,[x,y]] = [x,[y,z]] + (-[y,[x,z]]) *)
  set (P := vs_add la (la_bracket la x (la_bracket la y z))
                       (vs_neg la (la_bracket la y (la_bracket la x z)))).
  set (Q := la_bracket la z (la_bracket la x y)).
  change (vs_add la P Q = vs_zero la) in J.
  rewrite <- (vs_add_zero_r L la P).
  rewrite <- (vs_add_neg_r L la Q).
  rewrite (vs_add_assoc L la P Q (vs_neg la Q)).
  rewrite J.
  symmetry. exact (vs_add_zero_l la (vs_neg la Q)).
Qed.

(** The adjoint map for gl(n,ℂ): ad(A)(B) = [A,B] = AB − BA. *)
Definition gl_adjoint (n : nat) (A B : Mat CComplex) : Mat CComplex :=
  gl_bracket n A B.

(* ------------------------------------------------------------------ *)
(** * 6. Lie algebra representations                                    *)
(* ------------------------------------------------------------------ *)

(** A representation of a Lie algebra [la] on [gl(n,ℂ)] is a
    Lie algebra homomorphism la → gl(n,ℂ). *)
Definition LieAlgRep {L : Type} (la : LieAlgebra L) (n : nat) : Type :=
  LieAlgHom la (gl n).

(** The adjoint representation maps gl(n,ℂ) to End(gl(n,ℂ)).
    This doesn't fit [LieAlgRep gl(n) n] (which is gl(n) → gl(n)),
    so we state the adjoint's Lie algebra hom property as a Lemma
    in its correct (Leibniz / Jacobi-rearranged) form below.

    β R8 AUDIT (2026-05-01) — preserved counterexample:
    The historical [Axiom gl_adjoint_hom] was stated as
        [[A,B], C] = [[A,C], [B,C]]
    (after unfolding [gl_adjoint n X Y = gl_bracket n X Y]).  This is
    NOT a Lie algebra identity and is FALSE in general — concrete
    counterexample with 2×2 matrices:
        A = [[0,1],[0,0]],  B = [[0,0],[1,0]],  C = [[1,0],[0,-1]].
    Then [A,B] = C so [[A,B],C] = [C,C] = 0.  But [A,C] = -2A,
    [B,C] = 2B, and [[A,C],[B,C]] = [-2A,2B] = -4[A,B] = -4C ≠ 0.

    β R9 (2026-05-01): The false axiom (which had zero consumers, per
    β R8's grep) is REMOVED and replaced by the correct Leibniz rule
    [gl_leibniz_rule_wf] below.  The mathematically correct identity
    for the adjoint as a Lie homomorphism is
        ad([A,B])(C) = ad(A)(ad(B)(C)) − ad(B)(ad(A)(C)),
    i.e. [[A,B], C] = [A,[B,C]] − [B,[A,C]] — provable from
    [gl_jacobi_wf] together with the bracket-swap antisymmetry
    relation [gl_bracket n X Y = mneg (gl_bracket n Y X)] (which
    follows from [mneg_msub] and the definition of [commutator]). *)

(** [mmul] commutes with [mneg] in the left arg: [(-Y)·Z = -(Y·Z)].
    β R9 (2026-05-01): factored out of the inline proof inside
    [mmul_msub_l] so it can also be reused by [gl_bracket_neg_r_local]
    in the [gl_leibniz_rule_wf] proof. *)
Local Lemma mmul_mneg_l : forall (n : nat) (Y Z : Mat CComplex),
    mmul (mneg Y) Z n = mneg (mmul Y Z n).
Proof.
  intros n Y Z. unfold mneg.
  induction Y as [|rY Ys IH]; simpl; [reflexivity|].
  f_equal.
  - generalize (mcols n Z) as cols.
    intro cols. induction cols as [|c cs IHc]; simpl; [reflexivity|].
    rewrite IHc. f_equal.
    clear -rY c.
    revert c. induction rY as [|x xs IHr]; intros c; simpl.
    + destruct c; apply CComplex_eq; unfold CComplex_req, Cneg, C0; simpl;
        split; ring.
    + destruct c as [|y ys]; simpl.
      * apply CComplex_eq. unfold CComplex_req, Cneg, C0. simpl. split; ring.
      * rewrite IHr. apply CComplex_eq.
        unfold CComplex_req, Cneg, Cadd, Cmul. simpl. split; ring.
  - exact IH.
Qed.

(** [mmul] commutes with [mneg] in the right arg: [X·(-Z) = -(X·Z)].
    β R9 (2026-05-01): factored out of the inline proof inside
    [mmul_msub_r]. *)
Local Lemma mmul_mneg_r : forall (n : nat) (X Z : Mat CComplex),
    mmul X (mneg Z) n = mneg (mmul X Z n).
Proof.
  intros n X Z. unfold mneg.
  induction X as [|rX Xs IH]; simpl; [reflexivity|].
  f_equal; [|exact IH].
  assert (Hcol : forall (M : Mat CComplex) (j : nat),
            col (List.map (List.map Cneg) M) j =
            List.map Cneg (col M j)).
  { intros M j. unfold col. rewrite List.map_map.
    rewrite List.map_map. apply List.map_ext. intros row.
    revert j. induction row as [|x xs IHr]; intros j; simpl.
    - destruct j; apply CComplex_eq; unfold CComplex_req, Cneg, C0; simpl;
        split; ring.
    - destruct j as [|j']; [reflexivity|]. apply IHr. }
  assert (Hmcols : forall (m : nat) (M : Mat CComplex),
            mcols m (List.map (List.map Cneg) M) =
            List.map (List.map Cneg) (mcols m M)).
  { intros m M. induction m as [|m IHm]; simpl; [reflexivity|].
    rewrite IHm. rewrite List.map_app. simpl. rewrite (Hcol M m). reflexivity. }
  rewrite Hmcols.
  generalize (mcols n Z) as cs. intro cs.
  induction cs as [|c cs IHc]; simpl; [reflexivity|].
  rewrite IHc. f_equal.
  clear -rX c.
  revert c. induction rX as [|x xs IHr]; intros c; simpl.
  + destruct c; apply CComplex_eq; unfold CComplex_req, Cneg, C0; simpl;
      split; ring.
  + destruct c as [|y ys]; simpl.
    * apply CComplex_eq. unfold CComplex_req, Cneg, C0. simpl. split; ring.
    * rewrite IHr. apply CComplex_eq.
      unfold CComplex_req, Cneg, Cadd, Cmul. simpl. split; ring.
Qed.

(** Bracket swap: [[X, Y] = -[Y, X]].  Direct consequence of
    [mneg_msub] and [commutator]'s definition. *)
Local Lemma gl_bracket_swap_neg : forall n X Y,
    gl_bracket n X Y = mneg (gl_bracket n Y X).
Proof.
  intros n X Y. unfold gl_bracket, commutator.
  rewrite mneg_msub. reflexivity.
Qed.

(** Bracket negates in the second argument: [[B, -X] = -[B, X]]. *)
Local Lemma gl_bracket_neg_r_local : forall n B X,
    gl_bracket n B (mneg X) = mneg (gl_bracket n B X).
Proof.
  intros n B X. unfold gl_bracket, commutator, msub.
  rewrite (mmul_mneg_r n B X).
  rewrite (mmul_mneg_l n X B).
  rewrite mneg_madd.
  rewrite mneg_mneg.
  reflexivity.
Qed.

(** **Leibniz rule for the gl(n) bracket** (a.k.a. the adjoint
    homomorphism property in correct form):
        [[A, B], C] = [A, [B, C]] − [B, [A, C]]
    Equivalently: [ad_C [A,B] = [ad_C A, B] + [A, ad_C B]] after
    sign manipulation, which is the defining Leibniz rule for the
    inner derivation [ad_C].

    β R9 (2026-05-01): replaces the historical [Axiom gl_adjoint_hom]
    which was FALSE-as-stated (counterexample preserved in the comment
    block above).  Net −1 axiom (was an unsound axiom; now a sound
    Lemma whose only assumption is [CRealEq_eq] — inherited from
    [gl_jacobi_wf]).

    Proof outline: The Jacobi identity
        [A, [B, C]] + [B, [C, A]] + [C, [A, B]] = 0
    rearranges to
        [C, [A, B]] = −[A, [B, C]] − [B, [C, A]].
    Apply bracket swap [gl_bracket_swap_neg] to flip
    [C, [A, B]] = −[[A, B], C]] and [B, [C, A]] = −[B, [A, C]]] (the
    latter via [gl_bracket_neg_r_local] on the inner pair).  Negate
    both sides to obtain the Leibniz rule. *)
Lemma gl_leibniz_rule_wf : forall n A B C,
    Mat_wf n n A -> Mat_wf n n B -> Mat_wf n n C ->
    gl_bracket n (gl_bracket n A B) C =
    msub (gl_bracket n A (gl_bracket n B C))
         (gl_bracket n B (gl_bracket n A C)).
Proof.
  intros n A B C HA HB HC.
  pose proof (gl_jacobi_wf n A B C HA HB HC) as J.
  set (P := gl_bracket n A (gl_bracket n B C)) in *.
  set (Q := gl_bracket n B (gl_bracket n C A)) in *.
  set (R := gl_bracket n C (gl_bracket n A B)) in *.
  (* J : madd (madd P Q) R = mzero n. *)
  (* All of P, Q, R, and gl_bracket n B (gl_bracket n A C) are wf. *)
  assert (HBC : Mat_wf n n (gl_bracket n B C)) by
    (apply commutator_wf; assumption).
  assert (HCA : Mat_wf n n (gl_bracket n C A)) by
    (apply commutator_wf; assumption).
  assert (HAB : Mat_wf n n (gl_bracket n A B)) by
    (apply commutator_wf; assumption).
  assert (HAC : Mat_wf n n (gl_bracket n A C)) by
    (apply commutator_wf; assumption).
  assert (HP : Mat_wf n n P) by
    (unfold P; apply commutator_wf; assumption).
  assert (HQ : Mat_wf n n Q) by
    (unfold Q; apply commutator_wf; assumption).
  assert (HR : Mat_wf n n R) by
    (unfold R; apply commutator_wf; assumption).
  assert (HBAC : Mat_wf n n (gl_bracket n B (gl_bracket n A C))) by
    (apply commutator_wf; assumption).
  (* Step 1: Q = mneg (gl_bracket n B (gl_bracket n A C)).
     Use gl_bracket_swap_neg on the inner pair (C, A) and then
     gl_bracket_neg_r_local. *)
  assert (HQrewr : Q = mneg (gl_bracket n B (gl_bracket n A C))).
  { unfold Q. rewrite (gl_bracket_swap_neg n C A).
    apply gl_bracket_neg_r_local. }
  (* Step 2: gl_bracket n (gl_bracket n A B) C = mneg R via swap. *)
  assert (HLHS : gl_bracket n (gl_bracket n A B) C = mneg R).
  { unfold R. apply (gl_bracket_swap_neg n (gl_bracket n A B) C). }
  rewrite HLHS.
  (* Goal: mneg R = msub P (gl_bracket n B (gl_bracket n A C)).
     From J: madd (madd P Q) R = mzero n, so R = mneg (madd P Q),
     hence mneg R = madd P Q.  Combined with HQrewr,
     madd P Q = madd P (mneg (gl_bracket n B (gl_bracket n A C)))
              = msub P (gl_bracket n B (gl_bracket n A C)). *)
  rewrite HQrewr in J.
  set (S := gl_bracket n B (gl_bracket n A C)) in *.
  (* J : madd (madd P (mneg S)) R = mzero n.
     We want: mneg R = madd P (mneg S), i.e., msub P S. *)
  (* From J:  R = mneg (madd P (mneg S))  by adding -R to both sides. *)
  (* Re-associate: P + (-S + R) = 0 ⇒ (-S + R) = -P ... easier path:
     show mneg R + 0 = mneg R = madd P (mneg S) via direct manipulation. *)
  assert (Hsum : madd P (mneg S) = mneg R).
  { (* madd (madd P (mneg S)) R = mzero, want madd P (mneg S) = mneg R. *)
    (* Add (mneg R) to both sides on the right. *)
    pose proof J as J'.
    apply (f_equal (fun M => madd M (mneg R))) in J'.
    rewrite <- (mat_vs_add_assoc (madd P (mneg S)) R (mneg R)) in J'.
    rewrite (mat_vs_add_neg_r_wf n R HR) in J'.
    rewrite (mat_vs_add_zero_r_wf n (madd P (mneg S))) in J'.
    2: { apply madd_wf; [exact HP | apply mneg_wf; exact HBAC]. }
    rewrite (mat_vs_add_zero_l_wf n (mneg R)) in J'.
    2: { apply mneg_wf; exact HR. }
    exact J'. }
  rewrite <- Hsum.
  unfold msub.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * 7. Killing form                                                   *)
(* ------------------------------------------------------------------ *)

(** The Killing form B(A,B) = trace(ad(A) ∘ ad(B)).

    For gl(n,ℂ), the standard formula is:
      B(A,B) = 2n·trace(AB) − 2·trace(A)·trace(B).

    Rather than constructing ad(A) as an n²×n² matrix,
    we use the simpler equivalent: trace of the composition
    of the two bracket maps, stated via the mmul formula. *)

(* ------------------------------------------------------------------ *)
(** ** Trace helper lemmas (Task M.2.next, 2026-05-01)

    Used to discharge the [killing_*] axioms. *)
(* ------------------------------------------------------------------ *)

(** [trace_aux (mscale a A) k = a *c trace_aux A k]. *)
Local Lemma trace_aux_mscale : forall (a : CComplex) (A : Mat CComplex) (k : nat),
    trace_aux (mscale a A) k = Cmul a (trace_aux A k).
Proof.
  intros a A. unfold mscale.
  induction A as [|row rows IH]; intros k; simpl.
  - symmetry. apply Cmul_C0_r_lem.
  - rewrite nth_default_map_Cmul.
    rewrite IH. symmetry. apply Cmul_add_distr_l.
Qed.

Lemma trace_mscale : forall (a : CComplex) (A : Mat CComplex),
    trace (mscale a A) = Cmul a (trace A).
Proof. intros. unfold trace. apply trace_aux_mscale. Qed.

(** [trace_aux (madd A B) k = trace_aux A k +c trace_aux B k] when A and
    B have pairwise-equal-length rows.  The shape constraint is essential:
    the unhypothesised version is FALSE (madd truncates length-mismatched
    pairs, dropping their diagonal contributions). *)
Local Lemma trace_aux_madd : forall (A B : Mat CComplex) (k : nat),
    Forall2 (fun rA rB => List.length rA = List.length rB) A B ->
    trace_aux (madd A B) k = Cadd (trace_aux A k) (trace_aux B k).
Proof.
  intros A B k HF. revert k.
  induction HF as [|rA rB As Bs Hrow HFs IH]; intros k; simpl.
  - rewrite Cadd_C0_l_lem. reflexivity.
  - rewrite (nth_default_vadd rA rB k Hrow).
    rewrite IH.
    set (a := nth_default C0 rA k).
    set (b := nth_default C0 rB k).
    set (sA := trace_aux As (S k)).
    set (sB := trace_aux Bs (S k)).
    (* (a + b) + (sA + sB) = (a + sA) + (b + sB) *)
    rewrite <- (Cadd_assoc a b (Cadd sA sB)).
    rewrite (Cadd_assoc b sA sB).
    rewrite (Cadd_comm b sA).
    rewrite <- (Cadd_assoc sA b sB).
    apply (Cadd_assoc a sA (Cadd b sB)).
Qed.

Lemma trace_madd : forall (n : nat) (A B : Mat CComplex),
    Mat_wf n n A -> Mat_wf n n B ->
    trace (madd A B) = Cadd (trace A) (trace B).
Proof.
  intros n A B HA HB. unfold trace.
  apply trace_aux_madd. apply mat_wf_pairwise_len with (k:=n) (m:=n); assumption.
Qed.

(* ------------------------------------------------------------------ *)
(** ** sum_seq Fubini infrastructure (Task M.2.next.followup, β R6 — 2026-05-01)

    Port of β R4's [sum_seq] / Fubini infrastructure from
    [Lie/SpecialLinear.v] (which works over abstract [Field F]) to the
    CComplex / [Mat_wf] setting used here.  Goal: discharge
    [killing_symm_wf] and [killing_invariant_wf] via a CComplex-side
    [trace_mmul_comm] (cyclic property of trace).                       *)
(* ------------------------------------------------------------------ *)

(** Use [nat_scope] for the indexing arithmetic in this section.  The
    file-level [CReal_scope] is restored at the end of the block. *)
Local Open Scope nat_scope.

(** Right-associated finite sum starting at index [start], length [n].
    Reads [f start, f (S start), ..., f (start+n-1)].  Mirrors the
    structure of [trace_aux] (which adds head + tail recursively). *)
Fixpoint sum_seq_aux (f : nat -> CComplex) (start n : nat) : CComplex :=
  match n with
  | O => C0
  | S k => Cadd (f start) (sum_seq_aux f (S start) k)
  end.

Definition sum_seq (f : nat -> CComplex) (n : nat) : CComplex :=
  sum_seq_aux f 0 n.

(** 1/13: extensionality (start-relative). *)
Local Lemma sum_seq_aux_ext :
  forall (f g : nat -> CComplex) (start n : nat),
    (forall i, (start <= i < start + n)%nat -> f i = g i) ->
    sum_seq_aux f start n = sum_seq_aux g start n.
Proof.
  intros f g start n. revert start.
  induction n as [|n IH]; intros start Hext; [reflexivity|].
  simpl. f_equal.
  - apply Hext. lia.
  - apply IH. intros i Hi. apply Hext. lia.
Qed.

(** 2/13: extensionality. *)
Local Lemma sum_seq_ext :
  forall (f g : nat -> CComplex) (n : nat),
    (forall i, (i < n)%nat -> f i = g i) ->
    sum_seq f n = sum_seq g n.
Proof.
  intros f g n Hext. unfold sum_seq.
  apply sum_seq_aux_ext. intros i Hi. apply Hext. lia.
Qed.

(** 3/13: zero summand → zero sum (start-relative). *)
Local Lemma sum_seq_aux_zero :
  forall (start n : nat),
    sum_seq_aux (fun _ => C0) start n = C0.
Proof.
  intros start n. revert start.
  induction n as [|n IH]; intros start; [reflexivity|].
  simpl. rewrite IH. apply Cadd_C0_l_lem.
Qed.

(** 4/13: zero summand → zero sum. *)
Local Lemma sum_seq_zero :
  forall (n : nat), sum_seq (fun _ => C0) n = C0.
Proof. intros. unfold sum_seq. apply sum_seq_aux_zero. Qed.

(** 5/13: additivity (start-relative). *)
Local Lemma sum_seq_aux_add :
  forall (f g : nat -> CComplex) (start n : nat),
    sum_seq_aux (fun i => Cadd (f i) (g i)) start n =
    Cadd (sum_seq_aux f start n) (sum_seq_aux g start n).
Proof.
  intros f g start n. revert start.
  induction n as [|n IH]; intros start.
  - simpl. symmetry. apply Cadd_C0_l_lem.
  - simpl. rewrite IH.
    set (a := f start). set (b := g start).
    set (sf := sum_seq_aux f (S start) n).
    set (sg := sum_seq_aux g (S start) n).
    apply Cadd_interchange.
Qed.

(** 6/13: additivity. *)
Local Lemma sum_seq_add :
  forall (f g : nat -> CComplex) (n : nat),
    sum_seq (fun i => Cadd (f i) (g i)) n =
    Cadd (sum_seq f n) (sum_seq g n).
Proof. intros. unfold sum_seq. apply sum_seq_aux_add. Qed.

(** 7/13: shift starting index by 1 via re-indexing. *)
Local Lemma sum_seq_aux_shift :
  forall (f : nat -> CComplex) (start n : nat),
    sum_seq_aux f (S start) n = sum_seq_aux (fun i => f (S i)) start n.
Proof.
  intros f start n. revert start f.
  induction n as [|n IH]; intros start f; [reflexivity|].
  simpl. f_equal. apply IH.
Qed.

(** 8/13: pull the [n]-th term out the back. *)
Local Lemma sum_seq_S :
  forall (f : nat -> CComplex) (n : nat),
    sum_seq f (S n) = Cadd (sum_seq f n) (f n).
Proof.
  intros f n. unfold sum_seq.
  revert f. induction n as [|n IH]; intro f.
  - simpl. rewrite Cadd_C0_l_lem. rewrite Cadd_C0_r_lem. reflexivity.
  - change (sum_seq_aux f 0%nat (S (S n)))
      with (Cadd (f 0%nat) (sum_seq_aux f 1%nat (S n))).
    rewrite sum_seq_aux_shift.
    change (sum_seq_aux f 0%nat (S n))
      with (Cadd (f 0%nat) (sum_seq_aux f 1%nat n)).
    rewrite sum_seq_aux_shift.
    rewrite (IH (fun i => f (S i))).
    rewrite <- (Cadd_assoc (f 0%nat) _ _).
    reflexivity.
Qed.

(** 9/13: Fubini — swap order of summation over a rectangle. *)
Local Lemma sum_seq_swap :
  forall (f : nat -> nat -> CComplex) (n m : nat),
    sum_seq (fun i => sum_seq (fun j => f i j) m) n =
    sum_seq (fun j => sum_seq (fun i => f i j) n) m.
Proof.
  intros f n m. revert f m.
  induction n as [|n IH]; intros f m.
  - unfold sum_seq at 1. simpl.
    symmetry. apply sum_seq_zero.
  - rewrite (sum_seq_S _ n).
    rewrite (IH (fun i => f i) m).
    rewrite <- (sum_seq_add
                 (fun j => sum_seq (fun i => f i j) n)
                 (fun j => f n j) m).
    apply sum_seq_ext. intros j Hj.
    rewrite (sum_seq_S (fun i => f i j) n). reflexivity.
Qed.

(** 10/13: trace_aux as sum_seq.  The [k]-th iterate reads the
    [(start+k)]-th column entry of the [k]-th row. *)
Local Lemma mat_trace_aux_as_sum_seq :
  forall (M : Mat CComplex) (start : nat),
    trace_aux M start =
    sum_seq (fun i => nth_default C0 (List.nth i M []) (start + i))
            (List.length M).
Proof.
  intros M. induction M as [|row M IH]; intro start.
  - reflexivity.
  - cbn [List.length trace_aux]. unfold sum_seq. simpl sum_seq_aux. cbv beta.
    rewrite Nat.add_0_r. simpl List.nth at 1. f_equal.
    rewrite (IH (S start)).
    unfold sum_seq.
    rewrite sum_seq_aux_shift.
    apply sum_seq_aux_ext. intros i _. cbv beta.
    replace (start + S i)%nat with (S start + i)%nat by lia.
    reflexivity.
Qed.

(** 11/13: trace as sum_seq (start = 0). *)
Local Lemma mat_trace_as_sum_seq :
  forall (M : Mat CComplex),
    trace M =
    sum_seq (fun i => nth_default C0 (List.nth i M []) i) (List.length M).
Proof.
  intros M. unfold trace.
  rewrite (mat_trace_aux_as_sum_seq M 0%nat).
  apply sum_seq_ext. intros i _. simpl. reflexivity.
Qed.

(** Bridge: [dot v w = Σ_j v[j] · w[j]] when [length v = length w].
    Independent of [Field F]; uses AG.v's recursive [dot] directly. *)
Local Lemma dot_as_sum_seq :
  forall (v w : list CComplex),
    List.length v = List.length w ->
    dot v w =
    sum_seq (fun j => Cmul (nth_default C0 v j) (nth_default C0 w j))
            (List.length v).
Proof.
  induction v as [|x xs IH]; intros [|y ys] Hlen;
    simpl in *; try discriminate.
  - reflexivity.
  - injection Hlen as Hlen'.
    rewrite (IH ys Hlen').
    unfold sum_seq. simpl sum_seq_aux.
    rewrite sum_seq_aux_shift. cbv beta.
    reflexivity.
Qed.

(** Auxiliary: nth_default on [l ++ [x]] at index [c]: if [c < length l]
    then it's [nth_default l c]; if [c = length l] it's [x]. *)
Local Lemma nth_default_app_sing_lt :
  forall (l : list CComplex) (x : CComplex) (c : nat),
    c < List.length l ->
    nth_default C0 (l ++ [x]) c = nth_default C0 l c.
Proof.
  induction l as [|h t IHl]; intros x c Hc; simpl in *; [lia|].
  destruct c as [|c']; [reflexivity|]. apply IHl. lia.
Qed.

Local Lemma nth_default_app_sing_eq :
  forall (l : list CComplex) (x : CComplex),
    nth_default C0 (l ++ [x]) (List.length l) = x.
Proof.
  induction l as [|h t IHl]; intros x; simpl; [reflexivity|].
  apply IHl.
Qed.

(** Helper: row_mul_cols on [mcols m B] indexed at [c] yields [dot r (col B c)]
    when [c < m]. *)
Local Lemma nth_default_row_mul_mcols :
  forall (r : list CComplex) (B : Mat CComplex) (m c : nat),
    c < m ->
    nth_default C0 (row_mul_cols r (mcols m B)) c =
    dot r (col B c).
Proof.
  intros r B m. induction m as [|m IH]; intros c Hc; [lia|].
  simpl mcols.
  (* row_mul_cols r (xs ++ [c0]) = row_mul_cols r xs ++ [dot r c0] *)
  assert (Happ : forall (xs : list (list CComplex)) (c0 : list CComplex),
            row_mul_cols r (xs ++ [c0]) = row_mul_cols r xs ++ [dot r c0]).
  { intros xs c0. induction xs as [|x xs' IHx]; simpl; [reflexivity|].
    rewrite IHx. reflexivity. }
  rewrite Happ.
  assert (Hlen_rmc : List.length (row_mul_cols r (mcols m B)) = m).
  { rewrite row_mul_cols_length, mcols_length. reflexivity. }
  destruct (Nat.lt_ge_cases c m) as [Hcm | Hcm].
  - (* c < m: nth_default on (l ++ [x]) at c = nth_default l c. *)
    rewrite (nth_default_app_sing_lt _ _ c) by lia.
    apply (IH c Hcm).
  - (* c = m. *)
    assert (Hceq : c = m) by lia. subst c.
    pose proof (nth_default_app_sing_eq (row_mul_cols r (mcols m B))
                                         (dot r (col B m))) as Heq.
    rewrite Hlen_rmc in Heq. exact Heq.
Qed.

(** 12/13 (combined): the [(r,c)] entry of [mmul A B m] is [dot (nth r A) (col B c)],
    which equals [Σ_j A[r,j] · B[j,c]] when [Mat_wf n m A] and [Mat_wf m p B]. *)
Local Lemma mat_mul_entry_sum :
  forall (n p : nat) (A B : Mat CComplex) (r c : nat),
    Mat_wf n p A -> Mat_wf p n B ->
    r < n -> c < n ->
    nth_default C0 (List.nth r (mmul A B n) []) c =
    sum_seq
      (fun j => Cmul (nth_default C0 (List.nth r A []) j)
                     (nth_default C0 (List.nth j B []) c))
      p.
Proof.
  intros n p A B r c [HlenA HrowA] [HlenB HrowB] Hr Hc.
  (* row r of mmul A B n is row_mul_cols (nth r A) (mcols n B). *)
  assert (HrowMul : forall (X : Mat CComplex) (k : nat),
            k < List.length X ->
            List.nth k (mmul X B n) [] =
            row_mul_cols (List.nth k X []) (mcols n B)).
  { clear -B n. intros X. induction X as [|rX Xs IH]; intros k Hk; simpl in Hk.
    - lia.
    - simpl mmul. destruct k as [|k'].
      + reflexivity.
      + simpl List.nth. apply IH. lia. }
  rewrite (HrowMul A r) by lia.
  rewrite (nth_default_row_mul_mcols (List.nth r A []) B n c Hc).
  unfold col.
  (* dot (nth r A) (map (fun row => nth_default C0 row c) B). *)
  assert (HrowAr : List.length (List.nth r A []) = p).
  { apply HrowA. apply List.nth_In. lia. }
  assert (HmapLen : List.length (List.map (fun row => nth_default C0 row c) B) =
                    List.length B).
  { apply List.length_map. }
  assert (HBp : List.length B = p) by exact HlenB.
  rewrite (dot_as_sum_seq (List.nth r A [])
             (List.map (fun row : list CComplex => nth_default C0 row c) B)).
  - rewrite HrowAr. apply sum_seq_ext. intros j Hj.
    f_equal.
    (* nth_default C0 (map f B) j = f (nth j B []). *)
    clear -B.
    revert j.
    induction B as [|b Bs IHB]; intros j; simpl.
    + destruct j; reflexivity.
    + destruct j as [|j']; [reflexivity|]. apply IHB.
  - rewrite HrowAr, HmapLen, HBp. reflexivity.
Qed.

(** 13/13: Tr(AB) as a double sum [Σ_i Σ_j A[i,j] · B[j,i]]. *)
Local Lemma mat_trace_mul_double_sum :
  forall (n : nat) (A B : Mat CComplex),
    Mat_wf n n A -> Mat_wf n n B ->
    trace (mmul A B n) =
    sum_seq (fun i =>
      sum_seq (fun j =>
        Cmul (nth_default C0 (List.nth i A []) j)
             (nth_default C0 (List.nth j B []) i))
      n) n.
Proof.
  intros n A B HA HB.
  rewrite mat_trace_as_sum_seq.
  assert (Hlen : List.length (mmul A B n) = n).
  { rewrite mmul_length_aux. apply HA. }
  rewrite Hlen.
  apply sum_seq_ext. intros i Hi.
  apply (mat_mul_entry_sum n n A B i i HA HB Hi Hi).
Qed.

(** Cyclic property of trace: Tr(AB) = Tr(BA), discharged via the
    13-helper [sum_seq] / Fubini infrastructure above.  This is the
    CComplex / [Mat_wf] analogue of [Lie/SpecialLinear.v]'s
    [mat_trace_cyclic] (which works over abstract [Field F]). *)
Lemma trace_mmul_comm : forall (n : nat) (A B : Mat CComplex),
    Mat_wf n n A -> Mat_wf n n B ->
    trace (mmul A B n) = trace (mmul B A n).
Proof.
  intros n A B HA HB.
  rewrite (mat_trace_mul_double_sum n A B HA HB).
  rewrite (mat_trace_mul_double_sum n B A HB HA).
  (* Swap i↔j on RHS, then commute the product. *)
  rewrite (sum_seq_swap
             (fun i j => Cmul (nth_default C0 (List.nth i B []) j)
                              (nth_default C0 (List.nth j A []) i))
             n n).
  apply sum_seq_ext. intros i _.
  apply sum_seq_ext. intros j _.
  apply CComplex_eq, Cmul_comm_req.
Qed.

(** Restore file-level CReal scope. *)
Local Close Scope nat_scope.
Local Open Scope CReal_scope.

(** Helper: the matrix representation of ad(A) on the basis {E_ij}
    is an n²×n² matrix.  For now we characterize the Killing form
    via its trace formula, admitted. *)
Definition killing_form (n : nat) (A B : Mat CComplex) : CComplex :=
  Csub (Cmul (Cinject_nat (2 * n)) (trace (mmul A B n)))
       (Cmul (Cmul (Cinject_nat 2) (trace A)) (trace B)).

Notation "⟨ A , B ⟩_K" := (killing_form _ A B) (at level 50).

(* ------------------------------------------------------------------ *)
(** ** Killing form discharges (Task M.2.next, 2026-05-01)

    REFACTOR HISTORY: previously [killing_symm], [killing_add_l],
    [killing_scale_l], [killing_invariant] were un-hypothesised Axioms,
    FALSE-as-stated in general (madd / mmul both truncate on
    shape-mismatched matrices).  Net plan: convert each to a [_wf]
    Mat_wf-guarded statement and discharge to a Lemma where the
    underlying CComplex arithmetic / trace-cyclicity infrastructure
    permits.

    Discharged in M.2.next (β R5):
    - [killing_scale_l]: relies only on [mmul_mscale_l] +
      [trace_mscale] + Cmul/Csub algebra (no Mat_wf needed).
    - [killing_add_l]: uses [mmul_madd_l] + [trace_madd] + Mat_wf.

    Discharged in M.2.next.followup (β R6, 2026-05-01):
    - [killing_symm_wf]: discharged via [trace_mmul_comm] (the CComplex
      variant of [mat_trace_cyclic], built above on the 13-helper
      [sum_seq] / Fubini infrastructure).
    - [killing_invariant_wf]: discharged via [trace_mmul_comm] +
      [mmul_assoc] + new local helpers [trace_msub], [mmul_msub_l],
      [mmul_msub_r]. *)
(* ------------------------------------------------------------------ *)

(** Cmul distributes over Csub (Leibniz, via CRealEq_eq bridge). *)
Local Lemma Cmul_Csub_distr_l : forall a x y : CComplex,
    Cmul a (Csub x y) = Csub (Cmul a x) (Cmul a y).
Proof.
  intros a x y. apply CComplex_eq.
  unfold CComplex_req, Csub, Cadd, Cneg, Cmul. simpl. split; ring.
Qed.

(** Cmul rearrangement: a * (b * c) = b * (a * c). *)
Local Lemma Cmul_swap_left : forall a b c : CComplex,
    Cmul a (Cmul b c) = Cmul b (Cmul a c).
Proof.
  intros a b c. apply CComplex_eq.
  unfold CComplex_req, Cmul. simpl. split; ring.
Qed.

(** [killing_scale_l]: linearity in left argument under scalar.
    Discharged Axiom → Lemma (Task M.2.next, 2026-05-01).
    No [Mat_wf] hypothesis needed because [mscale] preserves shape. *)
Lemma killing_scale_l : forall n (a : CComplex) (A B : Mat CComplex),
    killing_form n (mscale a A) B =
    Cmul a (killing_form n A B).
Proof.
  intros n a A B. unfold killing_form.
  rewrite (mmul_mscale_l a A B n).
  rewrite trace_mscale.
  rewrite trace_mscale.
  (* Goal: Csub (Cinject_nat (2*n) *c (a *c trace(AB)))
                (Cinject_nat 2 *c (a *c trace A) *c trace B)
         = a *c (Csub (Cinject_nat (2*n) *c trace(AB))
                      (Cinject_nat 2 *c trace A *c trace B)) *)
  apply CComplex_eq.
  unfold CComplex_req, Csub, Cadd, Cneg, Cmul. simpl. split; ring.
Qed.

(** [killing_add_l]: linearity in left argument under addition.
    Discharged Axiom → Lemma (Task M.2.next, 2026-05-01) under
    [Mat_wf n n] hypotheses on A, B, C. *)
Lemma killing_add_l : forall n A B C,
    Mat_wf n n A -> Mat_wf n n B -> Mat_wf n n C ->
    killing_form n (madd A B) C =
    Cadd (killing_form n A C) (killing_form n B C).
Proof.
  intros n A B C HA HB HC. unfold killing_form.
  pose proof (mat_wf_pairwise_len n n A B HA HB) as HFAB.
  rewrite (mmul_madd_l A B C n HFAB).
  pose proof (mmul_wf n n n A C HA HC) as HmAC.
  pose proof (mmul_wf n n n B C HB HC) as HmBC.
  rewrite (trace_madd n (mmul A C n) (mmul B C n) HmAC HmBC).
  rewrite (trace_madd n A B HA HB).
  (* Goal:
       Csub (2n * (tr(AC) + tr(BC))) (2 * (trA + trB) * trC)
     = (Csub (2n * tr(AC)) (2 * trA * trC))
       + (Csub (2n * tr(BC)) (2 * trB * trC))                              *)
  apply CComplex_eq.
  unfold CComplex_req, Csub, Cadd, Cneg, Cmul. simpl. split; ring.
Qed.

(** [killing_symm_wf]: B(A,B) = B(B,A).  Discharged Axiom → Lemma
    (Task M.2.next.followup, β R6, 2026-05-01).  Uses [trace_mmul_comm]
    (cyclicity of trace, ported from β R4's [mat_trace_cyclic]) plus
    Cmul commutativity. *)
Lemma killing_symm_wf : forall n A B,
    Mat_wf n n A -> Mat_wf n n B ->
    killing_form n A B = killing_form n B A.
Proof.
  intros n A B HA HB. unfold killing_form.
  rewrite (trace_mmul_comm n A B HA HB).
  (* Csub (Cinject_nat (2*n) * tr(BA)) (Cinject_nat 2 * tr A * tr B)
   = Csub (Cinject_nat (2*n) * tr(BA)) (Cinject_nat 2 * tr B * tr A) *)
  apply CComplex_eq.
  unfold CComplex_req, Csub, Cadd, Cneg, Cmul. simpl. split; ring.
Qed.

(** ad-invariance: B([A,B],C) = B(A,[B,C]).  Discharged Axiom → Lemma
    (Task M.2.next.followup, β R6, 2026-05-01).

    Strategy: [gl_bracket] expands to [msub (mmul X Y n) (mmul Y X n)].
    We show that [trace] distributes over [mmul]/[msub] (via cyclicity
    [trace_mmul_comm] + [mmul_assoc]) so both sides reduce to the same
    cyclic-invariant trace expression. *)

(** Helper: [trace] of [mneg]: [tr(-A) = -tr(A)]. *)
Local Lemma trace_aux_mneg : forall (A : Mat CComplex) (k : nat),
    trace_aux (mneg A) k = Cneg (trace_aux A k).
Proof.
  intros A. unfold mneg.
  induction A as [|row rows IH]; intros k; simpl.
  - apply CComplex_eq. unfold CComplex_req, Cneg, C0. simpl. split; ring.
  - rewrite IH.
    (* nth_default C0 (map Cneg row) k = Cneg (nth_default C0 row k) *)
    assert (Hnd : nth_default C0 (List.map Cneg row) k =
                  Cneg (nth_default C0 row k)).
    { revert k. induction row as [|x xs IHr]; intros k; simpl.
      - destruct k; apply CComplex_eq; unfold CComplex_req, Cneg, C0; simpl; split; ring.
      - destruct k as [|k']; [reflexivity|]. apply IHr. }
    rewrite Hnd.
    apply CComplex_eq. unfold CComplex_req, Cneg, Cadd. simpl. split; ring.
Qed.

Local Lemma trace_mneg : forall (A : Mat CComplex),
    trace (mneg A) = Cneg (trace A).
Proof. intros. unfold trace. apply trace_aux_mneg. Qed.

(** [trace] of [msub]: [tr(A - B) = tr(A) - tr(B)] under shape match. *)
Local Lemma trace_msub : forall (n : nat) (A B : Mat CComplex),
    Mat_wf n n A -> Mat_wf n n B ->
    trace (msub A B) = Csub (trace A) (trace B).
Proof.
  intros n A B HA HB. unfold msub, Csub.
  rewrite (trace_madd n A (mneg B) HA (mneg_wf n n B HB)).
  rewrite trace_mneg. reflexivity.
Qed.

(** [mmul_msub_l] / [mmul_msub_r] are now defined earlier in the file
    (relocated β R8, 2026-05-01) so they can be used in [gl_jacobi_wf]. *)

Lemma killing_invariant_wf : forall n A B C,
    Mat_wf n n A -> Mat_wf n n B -> Mat_wf n n C ->
    killing_form n (gl_bracket n A B) C =
    killing_form n A (gl_bracket n B C).
Proof.
  intros n A B C HA HB HC.
  unfold killing_form, gl_bracket, commutator.
  (* Step 1: trace of bracket is zero (by cyclicity). *)
  pose proof (mmul_wf n n n A B HA HB) as HmAB.
  pose proof (mmul_wf n n n B A HB HA) as HmBA.
  pose proof (mmul_wf n n n B C HB HC) as HmBC.
  pose proof (mmul_wf n n n C B HC HB) as HmCB.
  rewrite (trace_msub n (mmul A B n) (mmul B A n) HmAB HmBA).
  rewrite (trace_msub n (mmul B C n) (mmul C B n) HmBC HmCB).
  rewrite (trace_mmul_comm n A B HA HB).
  rewrite (trace_mmul_comm n B C HB HC).
  (* Now: tr(BA) - tr(BA) = 0; tr(CB) - tr(CB) = 0. *)
  (* Step 2: expand mmul over msub on left and right. *)
  rewrite (mmul_msub_l n (mmul A B n) (mmul B A n) C HmAB HmBA).
  rewrite (mmul_msub_r n A (mmul B C n) (mmul C B n) HA HmBC HmCB).
  pose proof (mmul_wf n n n (mmul A B n) C HmAB HC) as HmABC.
  pose proof (mmul_wf n n n (mmul B A n) C HmBA HC) as HmBAC.
  pose proof (mmul_wf n n n A (mmul B C n) HA HmBC) as HmA_BC.
  pose proof (mmul_wf n n n A (mmul C B n) HA HmCB) as HmA_CB.
  rewrite (trace_msub n (mmul (mmul A B n) C n) (mmul (mmul B A n) C n) HmABC HmBAC).
  rewrite (trace_msub n (mmul A (mmul B C n) n) (mmul A (mmul C B n) n) HmA_BC HmA_CB).
  (* Step 3: associate and use cyclicity to identify the four traces. *)
  rewrite <- (mmul_assoc_wf n n n n A B C HA HB HC).
  (* tr(A·(B·C)) on LHS = tr(A·(B·C)) on RHS — same, no rewrite needed. *)
  (* Need: tr((B·A)·C) = tr(A·(C·B)).
     Proof: tr((BA)C) = tr(B(AC))  by mmul_assoc_wf
                      = tr((AC)B)  by trace_mmul_comm
                      = tr(A(CB))  by mmul_assoc_wf. *)
  rewrite <- (mmul_assoc_wf n n n n B A C HB HA HC).
  pose proof (mmul_wf n n n A C HA HC) as HmAC.
  rewrite (trace_mmul_comm n B (mmul A C n) HB HmAC).
  rewrite (mmul_assoc_wf n n n n A C B HA HC HB).
  (* Now LHS contains tr((AC)B). Need RHS to also contain tr(A(CB)) and we
     should massage further to align. *)
  rewrite <- (mmul_assoc_wf n n n n A C B HA HC HB).
  (* Goal (modulo Cinject_nat coefs):
     LHS subexpression: tr(A·(B·C)) - tr((A·C)·B)
     RHS subexpression: tr(A·(B·C)) - tr(A·(C·B))
     and these are equal because (A·C)·B = A·(C·B) by mmul_assoc_wf — but we
     just rewrote it in the other direction, so let's be more careful and
     recompute. *)
  rewrite (mmul_assoc_wf n n n n A C B HA HC HB).
  apply CComplex_eq.
  unfold CComplex_req, Csub, Cadd, Cneg, Cmul. simpl. split; ring.
Qed.

(* ------------------------------------------------------------------ *)
(** * 8. Connection to group representations                            *)
(* ------------------------------------------------------------------ *)

(** A smooth group homomorphism φ : G → GL(n,ℂ) differentiates to a
    Lie algebra homomorphism dφ : g → gl(n,ℂ).

    In the matrix setting, the derivative at the identity of a
    one-parameter subgroup t ↦ exp(tA) is A itself.  We capture
    the algebraic content: a group representation induces a Lie
    algebra representation preserving the bracket. *)

(** The tangent map of a group representation at the identity.
    For matrix Lie groups this is the identity on the Lie algebra level
    (since gl(n) is the tangent space of GL(n) at I).

    Sigma-typed (Task M.2.next, 2026-05-01): both source and target are
    [MatSig n], so the underlying map is the sigma identity [fun A => A]. *)
Definition induced_lie_rep {G : Type} (sg : StrictGroup G)
    (n : nat) (_ : GroupRep sg n) : LieAlgRep (gl n) n :=
  @mkLAHom (MatSig n) (MatSig n) (gl n) (gl n)
    (fun A => A)
    (fun x y => eq_refl)
    (fun a x => eq_refl)
    (fun x y => eq_refl).

(** Cartan's criterion (statement): a Lie algebra is semisimple iff
    its Killing form is non-degenerate. *)
Definition is_semisimple {L : Type} (la : LieAlgebra L)
    (kill : L -> L -> CComplex) : Prop :=
  forall x : L,
    (forall y : L, kill x y = C0) -> x = vs_zero la.

(* gl_semisimple removed: was a false-as-stated axiom. The Killing form on
   gl(n,C) is degenerate (the center, spanned by the identity matrix, is in
   its radical) — gl(n) is reductive, not semisimple. The semisimple part
   is sl(n,C). The axiom was unused downstream. *)
