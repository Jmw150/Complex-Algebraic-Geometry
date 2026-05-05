
(** Group Representations over C^n

    A group representation is a group homomorphism ρ : G → GL(n,ℂ),
    where GL(n,ℂ) is the general linear group of invertible n×n
    complex matrices.

    We build GL(n,ℂ) as a [StrictGroup] using the matrix machinery
    from AG.v, then define [GroupRep] as a [GroupHom] into it.
*)

From Stdlib Require Import List Arith Lia ProofIrrelevance.
Import ListNotations.

From CAG Require Import Complex.
From CAG Require Import AG.
From CAG Require Import Group.

(** * Invertible n×n complex matrices — the GLMat record

    We carry the inverse matrix explicitly (like [Perm n] carries its
    inverse permutation), so that [GL_inv] is fully concrete and the
    [StrictGroup] axioms can be stated without any choice principle.
*)

(* CAG constructive-remove Record GLMat theories/Representation.v:26 BEGIN -- constructive downstream cleanup: missing GroupRep
Record GLMat (n : nat) : Type := mkGL
  { gl_mat     : Mat CComplex
  ; gl_inv_mat : Mat CComplex
  ; gl_wf      : Mat_wf n n gl_mat
  ; gl_inv_wf  : Mat_wf n n gl_inv_mat
  ; gl_right_inv : mmul gl_mat gl_inv_mat n = mident n
  ; gl_left_inv  : mmul gl_inv_mat gl_mat n = mident n
  }.
   CAG constructive-remove Record GLMat theories/Representation.v:26 END *)

(* CAG constructive-remove Command Arguments theories/Representation.v:37 BEGIN -- missing gl_mat
Arguments gl_mat     {n} _.

   CAG constructive-remove Command Arguments theories/Representation.v:37 END *)
(* CAG constructive-remove Command Arguments theories/Representation.v:41 BEGIN -- missing gl_inv_mat
Arguments gl_inv_mat {n} _.

   CAG constructive-remove Command Arguments theories/Representation.v:41 END *)
(* CAG constructive-remove Command Arguments theories/Representation.v:45 BEGIN -- missing gl_wf
Arguments gl_wf      {n} _.

   CAG constructive-remove Command Arguments theories/Representation.v:45 END *)
(* CAG constructive-remove Command Arguments theories/Representation.v:49 BEGIN -- missing gl_inv_wf
Arguments gl_inv_wf  {n} _.

   CAG constructive-remove Command Arguments theories/Representation.v:49 END *)
(* CAG constructive-remove Command Arguments theories/Representation.v:53 BEGIN -- missing gl_right_inv
Arguments gl_right_inv {n} _.

   CAG constructive-remove Command Arguments theories/Representation.v:53 END *)
(* CAG constructive-remove Command Arguments theories/Representation.v:57 BEGIN -- missing gl_left_inv
Arguments gl_left_inv  {n} _.

   CAG constructive-remove Command Arguments theories/Representation.v:57 END *)

(** Two GLMat values are equal when their underlying matrices agree. *)
(* CAG constructive-remove Lemma GLMat_eq theories/Representation.v:43 BEGIN -- constructive downstream cleanup: missing GroupRep
Lemma GLMat_eq : forall n (A B : GLMat n),
  gl_mat A = gl_mat B ->
  gl_inv_mat A = gl_inv_mat B ->
  A = B.
Proof.
  intros n [mA iA wA wiA rA lA] [mB iB wB wiB rB lB].
  simpl. intros HM HI. subst.
  f_equal; apply proof_irrelevance.
Qed.
   CAG constructive-remove Lemma GLMat_eq theories/Representation.v:43 END *)

(** * GL group operations *)

(** (AB)(B⁻¹A⁻¹) = I — follows from associativity and AB·B⁻¹ = A *)
(* CAG zero-dependent Lemma GL_mul_right_inv_aux theories/Representation.v:56 BEGIN
Lemma GL_mul_right_inv_aux : forall n (A B : GLMat n),
  mmul (mmul (gl_mat A) (gl_mat B) n) (mmul (gl_inv_mat B) (gl_inv_mat A) n) n
  = mident n.
Proof.
  intros n A B.
  rewrite <- mmul_assoc.
  rewrite (mmul_assoc (gl_mat B) (gl_inv_mat B) (gl_inv_mat A) n).
  rewrite (gl_right_inv B).
  rewrite (mmul_mident_left n (gl_inv_mat A) (gl_inv_wf A)).
  exact (gl_right_inv A).
Qed.
   CAG zero-dependent Lemma GL_mul_right_inv_aux theories/Representation.v:56 END *)

(** (B⁻¹A⁻¹)(AB) = I *)
(* CAG zero-dependent Lemma GL_mul_left_inv_aux theories/Representation.v:69 BEGIN
Lemma GL_mul_left_inv_aux : forall n (A B : GLMat n),
  mmul (mmul (gl_inv_mat B) (gl_inv_mat A) n) (mmul (gl_mat A) (gl_mat B) n) n
  = mident n.
Proof.
  intros n A B.
  rewrite <- mmul_assoc.
  rewrite (mmul_assoc (gl_inv_mat A) (gl_mat A) (gl_mat B) n).
  rewrite (gl_left_inv A).
  rewrite (mmul_mident_left n (gl_mat B) (gl_wf B)).
  exact (gl_left_inv B).
Qed.
   CAG zero-dependent Lemma GL_mul_left_inv_aux theories/Representation.v:69 END *)

(** Multiplication: compose the matrices, compose the inverses in reverse *)
(* CAG zero-dependent Definition GL_mul theories/Representation.v:82 BEGIN
Definition GL_mul {n : nat} (A B : GLMat n) : GLMat n :=
  mkGL n
    (mmul (gl_mat A) (gl_mat B) n)
    (mmul (gl_inv_mat B) (gl_inv_mat A) n)
    (mmul_wf _ _ _ _ _ (gl_wf A) (gl_wf B))
    (mmul_wf _ _ _ _ _ (gl_inv_wf B) (gl_inv_wf A))
    (GL_mul_right_inv_aux n A B)
    (GL_mul_left_inv_aux n A B).
   CAG zero-dependent Definition GL_mul theories/Representation.v:82 END *)

(** Identity matrix as a GL element *)
(* CAG zero-dependent Definition GL_id theories/Representation.v:92 BEGIN
Definition GL_id (n : nat) : GLMat n :=
  mkGL n
    (mident n)
    (mident n)
    (mident_wf n)
    (mident_wf n)
    (mmul_mident_right n (mident n) (mident_wf n))
    (mmul_mident_left  n (mident n) (mident_wf n)).
   CAG zero-dependent Definition GL_id theories/Representation.v:92 END *)

(** Inverse: swap the matrix and its stored inverse *)
(* CAG constructive-remove Definition GL_inv theories/Representation.v:110 BEGIN -- constructive downstream cleanup: missing GroupRep
Definition GL_inv {n : nat} (A : GLMat n) : GLMat n :=
  mkGL n
    (gl_inv_mat A)
    (gl_mat A)
    (gl_inv_wf A)
    (gl_wf A)
    (gl_left_inv A)
    (gl_right_inv A).
   CAG constructive-remove Definition GL_inv theories/Representation.v:110 END *)

(** * StrictGroup axioms for GLMat n *)

(* CAG zero-dependent Lemma GL_assoc theories/Representation.v:113 BEGIN
Lemma GL_assoc : forall n (A B C : GLMat n),
  GL_mul A (GL_mul B C) = GL_mul (GL_mul A B) C.
Proof.
  intros n A B C.
  apply GLMat_eq; simpl.
  - (* (A·(B·C)) mat = ((A·B)·C) mat *)
    apply mmul_assoc.
  - (* inv side: C⁻¹·(B⁻¹·A⁻¹) = (C⁻¹·B⁻¹)·A⁻¹ *)
    symmetry. apply mmul_assoc.
Qed.
   CAG zero-dependent Lemma GL_assoc theories/Representation.v:113 END *)

(* CAG zero-dependent Lemma GL_id_right theories/Representation.v:124 BEGIN
Lemma GL_id_right : forall n (A : GLMat n),
  GL_mul A (GL_id n) = A.
Proof.
  intros n A.
  apply GLMat_eq; simpl.
  - apply mmul_mident_right. exact (gl_wf A).
  - apply mmul_mident_left.  exact (gl_inv_wf A).
Qed.
   CAG zero-dependent Lemma GL_id_right theories/Representation.v:124 END *)

(* CAG zero-dependent Lemma GL_id_left theories/Representation.v:133 BEGIN
Lemma GL_id_left : forall n (A : GLMat n),
  GL_mul (GL_id n) A = A.
Proof.
  intros n A.
  apply GLMat_eq; simpl.
  - apply mmul_mident_left.  exact (gl_wf A).
  - apply mmul_mident_right. exact (gl_inv_wf A).
Qed.
   CAG zero-dependent Lemma GL_id_left theories/Representation.v:133 END *)

(* CAG zero-dependent Lemma GL_inv_right theories/Representation.v:142 BEGIN
Lemma GL_inv_right : forall n (A : GLMat n),
  GL_mul A (GL_inv A) = GL_id n.
Proof.
  intros n A.
  apply GLMat_eq; simpl.
  - exact (gl_right_inv A).
  - exact (gl_right_inv A).
Qed.
   CAG zero-dependent Lemma GL_inv_right theories/Representation.v:142 END *)

(* CAG zero-dependent Lemma GL_inv_left theories/Representation.v:151 BEGIN
Lemma GL_inv_left : forall n (A : GLMat n),
  GL_mul (GL_inv A) A = GL_id n.
Proof.
  intros n A.
  apply GLMat_eq; simpl.
  - exact (gl_left_inv A).
  - exact (gl_left_inv A).
Qed.
   CAG zero-dependent Lemma GL_inv_left theories/Representation.v:151 END *)

(* CAG zero-dependent Definition GL_StrictGroup theories/Representation.v:160 BEGIN
Definition GL_StrictGroup (n : nat) : StrictGroup (GLMat n) :=
  mkSG (GLMat n)
    (@GL_mul n)
    (GL_id n)
    (@GL_inv n)
    (GL_assoc n)
    (GL_id_right n)
    (GL_id_left n)
    (GL_inv_right n)
    (GL_inv_left n).
   CAG zero-dependent Definition GL_StrictGroup theories/Representation.v:160 END *)

(** * Group Representations

    A representation of a group G on C^n is a group homomorphism
    ρ : G → GL(n,ℂ).
*)

(* CAG zero-dependent Definition GroupRep theories/Representation.v:177 BEGIN
Definition GroupRep {G : Type} (sg : StrictGroup G) (n : nat) : Type :=
  GroupHom sg (GL_StrictGroup n).
   CAG zero-dependent Definition GroupRep theories/Representation.v:177 END *)

(** Convenience: extract the matrix assigned to a group element *)
(* CAG zero-dependent Definition rep_matrix theories/Representation.v:181 BEGIN
Definition rep_matrix {G : Type} {sg : StrictGroup G} {n : nat}
    (ρ : GroupRep sg n) (g : G) : Mat CComplex :=
  gl_mat (hom_fn ρ g).
   CAG zero-dependent Definition rep_matrix theories/Representation.v:181 END *)

(** * Basic facts about representations *)

Section RepFacts.

(* CAG constructive-remove Command Context theories/Representation.v:237 BEGIN -- missing GroupRep
Context {G : Type} (sg : StrictGroup G) (n : nat) (ρ : GroupRep sg n).

   CAG constructive-remove Command Context theories/Representation.v:237 END *)

(** ρ(e) = I_n *)
(* CAG zero-dependent Lemma rep_identity theories/Representation.v:192 BEGIN
Lemma rep_identity :
  rep_matrix ρ (se G sg) = mident n.
Proof.
  unfold rep_matrix.
  pose proof (hom_id sg (GL_StrictGroup n) ρ) as H.
  (* hom_id : hom_fn φ (se G sg) = se H sh *)
  (* But hom_id takes (sg sh φ) explicitly in the section — here we call it globally *)
  rewrite H. simpl. reflexivity.
Qed.
   CAG zero-dependent Lemma rep_identity theories/Representation.v:192 END *)

(** ρ(g⁻¹) = ρ(g)⁻¹ as GLMat *)
(* CAG zero-dependent Lemma rep_inv_glmat theories/Representation.v:203 BEGIN
Lemma rep_inv_glmat : forall g : G,
  hom_fn ρ (sinv G sg g) = GL_inv (hom_fn ρ g).
Proof.
  intros g.
  pose proof (hom_inv sg (GL_StrictGroup n) ρ g) as H.
  simpl in H. exact H.
Qed.
   CAG zero-dependent Lemma rep_inv_glmat theories/Representation.v:203 END *)

(** ρ(g⁻¹) as a raw matrix equals the stored inverse of ρ(g) *)
(* CAG zero-dependent Lemma rep_inv_matrix theories/Representation.v:212 BEGIN
Lemma rep_inv_matrix : forall g : G,
  rep_matrix ρ (sinv G sg g) = gl_inv_mat (hom_fn ρ g).
Proof.
  intros g.
  unfold rep_matrix.
  rewrite rep_inv_glmat. simpl. reflexivity.
Qed.
   CAG zero-dependent Lemma rep_inv_matrix theories/Representation.v:212 END *)

(** ρ(gh) = ρ(g)·ρ(h) as matrices *)
(* CAG zero-dependent Lemma rep_mul_matrix theories/Representation.v:221 BEGIN
Lemma rep_mul_matrix : forall g h : G,
  rep_matrix ρ (smul G sg g h) =
  mmul (rep_matrix ρ g) (rep_matrix ρ h) n.
Proof.
  intros g h.
  unfold rep_matrix.
  pose proof (hom_mul ρ g h) as H.
  rewrite H. simpl. reflexivity.
Qed.
   CAG zero-dependent Lemma rep_mul_matrix theories/Representation.v:221 END *)

End RepFacts.

(** * Trivial representation

    The trivial representation sends every group element to I_n. *)

(* CAG zero-dependent Definition trivial_rep_fn theories/Representation.v:237 BEGIN
Definition trivial_rep_fn {G : Type} (sg : StrictGroup G) (n : nat)
    (g : G) : GLMat n :=
  GL_id n.
   CAG zero-dependent Definition trivial_rep_fn theories/Representation.v:237 END *)

(* CAG zero-dependent Lemma trivial_rep_hom theories/Representation.v:241 BEGIN
Lemma trivial_rep_hom : forall {G : Type} (sg : StrictGroup G) (n : nat),
  forall g h : G,
    trivial_rep_fn sg n (smul G sg g h) =
    smul (GLMat n) (GL_StrictGroup n)
      (trivial_rep_fn sg n g) (trivial_rep_fn sg n h).
Proof.
  intros G sg n g h.
  unfold trivial_rep_fn. simpl.
  (* GL_mul (GL_id n) (GL_id n) = GL_id n *)
  apply GLMat_eq; simpl.
  - symmetry. apply mmul_mident_left. exact (mident_wf n).
  - symmetry. apply mmul_mident_right. exact (mident_wf n).
Qed.
   CAG zero-dependent Lemma trivial_rep_hom theories/Representation.v:241 END *)

(* CAG zero-dependent Definition trivial_rep theories/Representation.v:255 BEGIN
Definition trivial_rep {G : Type} (sg : StrictGroup G) (n : nat)
    : GroupRep sg n :=
  {| hom_fn  := trivial_rep_fn sg n
   ; hom_mul := trivial_rep_hom sg n
   |}.
   CAG zero-dependent Definition trivial_rep theories/Representation.v:255 END *)

(** * Extraction hint

    Add to Extract.v:

      From CAG Require Import Representation.
      Extraction "lib/representation.ml"
        GL_mul GL_id GL_inv rep_matrix trivial_rep.
*)
