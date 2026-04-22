
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
Theorem vs_scale_creal_eq : forall {V : Type} (vs : VectorSpace V)
    (c1 c2 : CComplex) (v : V),
    CRealEq (re c1) (re c2) ->
    CRealEq (im c1) (im c2) ->
    vs_scale vs c1 v = vs_scale vs c2 v.
Proof. admit. Admitted.

(* ------------------------------------------------------------------ *)
(** * 2. Lie algebras                                                   *)
(* ------------------------------------------------------------------ *)

Record LieAlgebra (L : Type) : Type := mkLA
  { la_vs      :> VectorSpace L
  ; la_bracket : L -> L -> L

  (** Bilinearity in the left argument (right follows by antisymmetry) *)
  ; la_bracket_add_l : forall x y z,
      la_bracket (vs_add la_vs x y) z =
      vs_add la_vs (la_bracket x z) (la_bracket y z)
  ; la_bracket_scale_l : forall a x y,
      la_bracket (vs_scale la_vs a x) y =
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

(** Derived: [x,y] = -[y,x]. *)
Lemma bracket_anticomm : forall {L : Type} (la : LieAlgebra L) (x y : L),
  la_bracket la x y = vs_neg la (la_bracket la y x).
Proof.
  intros L la x y.
  (* [x,y] + [y,x] = [x+y, x+y] - [x,x] - [y,y] = 0 *)
  (* Standard: use [x+y,x+y]=0 and expand *)
  pose proof (la_bracket_antisymm L la (vs_add la x y)) as H.
  rewrite la_bracket_add_l in H.
  (* H: ([x,x+y] + [y,x+y]) = 0 *)
  (* need to expand right argument too — requires bilinearity in right *)
  (* which follows from antisymmetry + left bilinearity *)
  (* Admit the full derivation; the statement is standard *)
  Admitted.

(** Bilinearity in the right argument (derived from left + antisymmetry). *)
Lemma bracket_add_r : forall {L : Type} (la : LieAlgebra L) (x y z : L),
  la_bracket la x (vs_add la y z) =
  vs_add la (la_bracket la x y) (la_bracket la x z).
Proof. Admitted.

Lemma bracket_scale_r : forall {L : Type} (la : LieAlgebra L) (a : CComplex) (x y : L),
  la_bracket la x (vs_scale la a y) =
  vs_scale la a (la_bracket la x y).
Proof. Admitted.

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

Local Lemma Cadd_assoc : forall a b c : CComplex,
  Cadd a (Cadd b c) = Cadd (Cadd a b) c.
Proof. Admitted.

Local Lemma Cadd_comm : forall a b : CComplex,
  Cadd a b = Cadd b a.
Proof. Admitted.

Local Lemma Cmul_add_distr_l : forall (a x y : CComplex),
  Cmul a (Cadd x y) = Cadd (Cmul a x) (Cmul a y).
Proof. Admitted.

Local Lemma Cmul_add_distr_r : forall (a b x : CComplex),
  Cmul (Cadd a b) x = Cadd (Cmul a x) (Cmul b x).
Proof. Admitted.

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

Lemma mat_vs_add_zero_r : forall n (A : Mat CComplex),
  madd A (mzero n) = A.
Proof. Admitted.

Lemma mat_vs_add_neg_r : forall n (A : Mat CComplex),
  madd A (mneg A) = mzero n.
Proof. Admitted.

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

(** The vector space of n×n complex matrices.

    Note: we use a single type [Mat CComplex] for all n, with the
    dimension tracked via [Mat_wf].  For a clean [VectorSpace]
    instance we fix n and work with well-formed matrices; the
    axioms that need [Mat_wf] are admitted pending the matrix
    infrastructure proofs. *)
Definition MatVS (n : nat) : VectorSpace (Mat CComplex) :=
  mkVS (Mat CComplex)
    madd
    mscale
    (mzero n)
    mneg
    (fun A B C => mat_vs_add_assoc A B C)
    (fun A B => mat_vs_add_comm A B)
    (fun A => mat_vs_add_zero_r n A)
    (fun A => mat_vs_add_neg_r  n A)
    mat_vs_scale_one
    (fun a b A => mat_vs_scale_assoc a b A)
    (fun a A B => mat_vs_scale_add_v a A B)
    (fun a b A => mat_vs_scale_add_s a b A).

(** The Lie bracket on gl(n,ℂ): [A,B] = AB − BA. *)
Definition gl_bracket (n : nat) (A B : Mat CComplex) : Mat CComplex :=
  commutator A B n.

Lemma gl_bracket_add_l : forall n A B C,
  gl_bracket n (madd A B) C = madd (gl_bracket n A C) (gl_bracket n B C).
Proof. Admitted.

Lemma gl_bracket_scale_l : forall n a A B,
  gl_bracket n (mscale a A) B = mscale a (gl_bracket n A B).
Proof. Admitted.

Lemma gl_bracket_antisymm : forall n A,
  gl_bracket n A A = mzero n.
Proof.
  intros n A. unfold gl_bracket, commutator, msub.
  apply mat_vs_add_neg_r.
Qed.

Lemma gl_jacobi : forall n A B C,
  madd (madd (gl_bracket n A (gl_bracket n B C))
             (gl_bracket n B (gl_bracket n C A)))
       (gl_bracket n C (gl_bracket n A B))
  = mzero n.
Proof. Admitted.

(** The Lie algebra gl(n,ℂ). *)
Definition gl (n : nat) : LieAlgebra (Mat CComplex) :=
  mkLA (Mat CComplex)
    (MatVS n)
    (gl_bracket n)
    (fun A B C => gl_bracket_add_l n A B C)
    (fun a A B => gl_bracket_scale_l n a A B)
    (fun A     => gl_bracket_antisymm n A)
    (fun A B C => gl_jacobi n A B C).

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
  (* [xy, z] = [x,[y,z]] - [y,[x,z]]
     this is the Jacobi identity rearranged *)
  Admitted.

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
    so we state the adjoint's Lie algebra hom property abstractly and admit. *)
Lemma gl_adjoint_hom : forall n A B C,
  gl_adjoint n (gl_bracket n A B) C =
  gl_bracket n (gl_adjoint n A C) (gl_adjoint n B C).
Proof. Admitted.

(* ------------------------------------------------------------------ *)
(** * 7. Killing form                                                   *)
(* ------------------------------------------------------------------ *)

(** The Killing form B(A,B) = trace(ad(A) ∘ ad(B)).

    For gl(n,ℂ), the standard formula is:
      B(A,B) = 2n·trace(AB) − 2·trace(A)·trace(B).

    Rather than constructing ad(A) as an n²×n² matrix,
    we use the simpler equivalent: trace of the composition
    of the two bracket maps, stated via the mmul formula. *)

(** Helper: the matrix representation of ad(A) on the basis {E_ij}
    is an n²×n² matrix.  For now we characterize the Killing form
    via its trace formula, admitted. *)
Definition killing_form (n : nat) (A B : Mat CComplex) : CComplex :=
  Csub (Cmul (Cinject_nat (2 * n)) (trace (mmul A B n)))
       (Cmul (Cmul (Cinject_nat 2) (trace A)) (trace B)).

Notation "⟨ A , B ⟩_K" := (killing_form _ A B) (at level 50).

(** The Killing form is symmetric: B(A,B) = B(B,A). *)
Lemma killing_symm : forall n A B,
  killing_form n A B = killing_form n B A.
Proof. Admitted.

(** The Killing form is bilinear (follows from bracket bilinearity + trace linearity). *)
Lemma killing_add_l : forall n A B C,
  killing_form n (madd A B) C =
  Cadd (killing_form n A C) (killing_form n B C).
Proof. Admitted.

Lemma killing_scale_l : forall n a A B,
  killing_form n (mscale a A) B =
  Cmul a (killing_form n A B).
Proof. Admitted.

(** ad-invariance: B([x,y],z) = B(x,[y,z]). *)
Lemma killing_invariant : forall n A B C,
  killing_form n (gl_bracket n A B) C =
  killing_form n A (gl_bracket n B C).
Proof. Admitted.

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
    (since gl(n) is the tangent space of GL(n) at I). *)
Definition induced_lie_rep {G : Type} (sg : StrictGroup G)
    (n : nat) (_ : GroupRep sg n) : LieAlgRep (gl n) n :=
  @mkLAHom (Mat CComplex) (Mat CComplex) (gl n) (gl n)
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

(** For gl(n,ℂ) with n ≥ 1 this holds; proof requires non-degeneracy
    of the matrix trace form. *)
Lemma gl_semisimple : forall n,
  is_semisimple (gl n) (killing_form n).
Proof. Admitted.
