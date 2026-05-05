(** * Lie/StructureConstants.v
    Structure constants of a Lie algebra relative to a basis.

    We work abstractly: a "coordinate system" for L is a function
      coord : L -> nat -> F
    together with a basis list  bs : list L  such that
      [x_i, x_j] = Σ_k a_{ij}^k · x_k
    where  a_{ij}^k := coord (laF_bracket la bs_i bs_j) k.

    We do NOT require the basis to be formally spanning or independent
    (that would need a finite-dimensional framework); instead we state
    only the consequences that follow from the Lie axioms alone. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.

(** ** Coordinate systems *)

(** A coordinate system on L is a function coord : L -> nat -> F
    that is:
    - linear in its first argument (so that it respects the vector
      space structure), and
    - zero on la_zero.

    These are the only properties we need for the structure-constant
    identities below. *)

Record CoordSystem {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) : Type := {
  cs_coord   : L -> nat -> F;
  cs_zero    : forall k, cs_coord (la_zero la) k = cr_zero fld;
  cs_neg     : forall x k,
    cs_coord (la_neg la x) k = cr_neg fld (cs_coord x k);
  cs_add     : forall x y k,
    cs_coord (la_add la x y) k =
    cr_add fld (cs_coord x k) (cs_coord y k);
  cs_scale   : forall a x k,
    cs_coord (la_scale la a x) k =
    cr_mul fld a (cs_coord x k);
}.

Arguments cs_coord {F fld L la} _ _ _.
Arguments cs_zero  {F fld L la} _.
Arguments cs_neg   {F fld L la} _.
Arguments cs_add   {F fld L la} _.
Arguments cs_scale {F fld L la} _.

(** ** Structure constants *)

(** Given a basis list bs and a coordinate system cs, the structure
    constant a_{ij}^k is the k-th coordinate of [bs_i, bs_j]. *)

Definition struct_const {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (cs : CoordSystem la)
    (bs : list L) (i j k : nat) : F :=
  cs_coord cs
    (laF_bracket la
       (List.nth i bs (la_zero la))
       (List.nth j bs (la_zero la)))
    k.

(** ** Key identities *)

(** *** Diagonal zero: a_{ii}^k = 0.

    Proof: [x_i, x_i] = 0 (alternating axiom), hence every coordinate
    of [x_i, x_i] is cr_zero. *)

Lemma struct_const_diag_zero {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (cs : CoordSystem la)
    (bs : list L) (i k : nat) :
    struct_const la cs bs i i k = cr_zero fld.
Proof.
  unfold struct_const.
  rewrite la.(laF_bracket_alt).
  apply cs.(cs_zero).
Qed.

(** *** Antisymmetry: a_{ij}^k = - a_{ji}^k.

    Proof: [x_i, x_j] = -[x_j, x_i] (laF_anticomm), so
    coord([x_i,x_j]) k = coord(-[x_j,x_i]) k = - coord([x_j,x_i]) k. *)

Lemma struct_const_antisymm {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (cs : CoordSystem la)
    (bs : list L) (i j k : nat) :
    struct_const la cs bs i j k =
    cr_neg fld (struct_const la cs bs j i k).
Proof.
  unfold struct_const.
  rewrite (laF_anticomm la).
  apply cs.(cs_neg).
Qed.

(** *** Bilinearity in i: a_{(i+i')j}^k = a_{ij}^k + a_{i'j}^k.

    More precisely: if we replace bs_i by the sum of two elements x,y,
    the structure constants add.  We state this for explicit elements
    rather than for list indices (the list indexing can be reduced to
    this by substituting). *)

Lemma struct_const_add_l {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (cs : CoordSystem la)
    (x y z : L) (k : nat) :
    cs_coord cs (laF_bracket la (la_add la x y) z) k =
    cr_add fld
      (cs_coord cs (laF_bracket la x z) k)
      (cs_coord cs (laF_bracket la y z) k).
Proof.
  rewrite la.(laF_bracket_add_l).
  apply cs.(cs_add).
Qed.

Lemma struct_const_add_r {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (cs : CoordSystem la)
    (x y z : L) (k : nat) :
    cs_coord cs (laF_bracket la x (la_add la y z)) k =
    cr_add fld
      (cs_coord cs (laF_bracket la x y) k)
      (cs_coord cs (laF_bracket la x z) k).
Proof.
  rewrite la.(laF_bracket_add_r).
  apply cs.(cs_add).
Qed.

Lemma struct_const_scale_l {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (cs : CoordSystem la)
    (a : F) (x y : L) (k : nat) :
    cs_coord cs (laF_bracket la (la_scale la a x) y) k =
    cr_mul fld a (cs_coord cs (laF_bracket la x y) k).
Proof.
  rewrite la.(laF_bracket_scale_l).
  apply cs.(cs_scale).
Qed.

Lemma struct_const_scale_r {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (cs : CoordSystem la)
    (a : F) (x y : L) (k : nat) :
    cs_coord cs (laF_bracket la x (la_scale la a y)) k =
    cr_mul fld a (cs_coord cs (laF_bracket la x y) k).
Proof.
  rewrite la.(laF_bracket_scale_r).
  apply cs.(cs_scale).
Qed.

(** *** Jacobi identity for structure constants.

    The abstract Jacobi identity says
      [x,[y,z]] + [y,[z,x]] + [z,[x,y]] = 0.
    Taking the k-th coordinate and using linearity of cs_coord:
      a_{x,[y,z]}^k + a_{y,[z,x]}^k + a_{z,[x,y]}^k = 0
    where by "a_{u,v}^k" we mean cs_coord (laF_bracket la u v) k.

    Written for arbitrary elements (not just basis elements): *)

Lemma struct_const_jacobi {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (cs : CoordSystem la)
    (x y z : L) (k : nat) :
    cr_add fld
      (cr_add fld
         (cs_coord cs (laF_bracket la x (laF_bracket la y z)) k)
         (cs_coord cs (laF_bracket la y (laF_bracket la z x)) k))
      (cs_coord cs (laF_bracket la z (laF_bracket la x y)) k)
    = cr_zero fld.
Proof.
  rewrite <- cs.(cs_add).
  rewrite <- cs.(cs_add).
  rewrite la.(laF_jacobi).
  apply cs.(cs_zero).
Qed.

(** ** Converse: existence of a Lie algebra from structure constants

    Given scalars c : nat -> nat -> nat -> F on a vector space L
    and a "linear combination" function expand : (nat -> F) -> L,
    one can define a bracket by
      [x, y] = expand (fun k => Σ_i Σ_j c i j k * coord x i * coord y j).
    Proving this is a Lie algebra requires the antisymmetry and Jacobi
    conditions on c.

    We state the abstract theorem as an axiom, pending a concrete
    finite-dimensional vector space framework. *)

(** Abstract reconstruction conjecture (pending finite-dim framework).

    Informal statement: given scalars (c_{ij}^k) ∈ F (1 ≤ i,j,k ≤ n)
    satisfying
        antisymmetry:  c_{ij}^k = -c_{ji}^k,
        diagonal zero: c_{ii}^k = 0,
        Jacobi:        Σ_l (c_{ij}^l c_{lk}^m + c_{jk}^l c_{li}^m
                            + c_{ki}^l c_{lj}^m) = 0  for all i,j,k,m,
    there exists an n-dimensional Lie algebra L over F with basis
    e_1,...,e_n such that [e_i, e_j] = Σ_k c_{ij}^k e_k.  Concretely,
    L can be taken as F^n with the bracket defined componentwise from
    the c_{ij}^k.

    The strengthened conclusion below requires the bracket of any two
    basis vectors to expand correctly via the structure constants —
    not the trivial existential `exists L la, True`.

    Reference: Humphreys, Introduction to Lie Algebras and
    Representation Theory (1972) §1; Jacobson, Lie Algebras (1962)
    Chapter 1 §2. *)
(* CAG zero-dependent Conjecture lie_algebra_from_structure_constants theories/Lie/StructureConstants.v:204 BEGIN
Conjecture lie_algebra_from_structure_constants :
  forall {F : Type} (fld : Field F) (n : nat)
    (c : nat -> nat -> nat -> F)
    (** Antisymmetry: c i j k = - c j i k *)
    (Hanti : forall i j k, c i j k = cr_neg fld (c j i k))
    (** Diagonal zero: c i i k = 0 *)
    (Hdiag : forall i k, c i i k = cr_zero fld)
    (** Jacobi: Σ_{l} (c i j l * c l k m + c j k l * c l i m + c k i l * c l j m) = 0 *)
    (HJac : forall i j k m,
      cr_add fld
        (cr_add fld
           (List.fold_left (fun acc l =>
              cr_add fld acc (cr_mul fld (c i j l) (c l k m))) (List.seq 0 n) (cr_zero fld))
           (List.fold_left (fun acc l =>
              cr_add fld acc (cr_mul fld (c j k l) (c l i m))) (List.seq 0 n) (cr_zero fld)))
        (List.fold_left (fun acc l =>
           cr_add fld acc (cr_mul fld (c k i l) (c l j m))) (List.seq 0 n) (cr_zero fld))
      = cr_zero fld),
  exists (L : Type) (la : LieAlgebraF fld L) (basis : nat -> L)
         (cs : CoordSystem la),
    (* The chosen basis has the prescribed structure constants. *)
    forall i j k : nat,
      cs_coord cs (laF_bracket la (basis i) (basis j)) k = c i j k.
   CAG zero-dependent Conjecture lie_algebra_from_structure_constants theories/Lie/StructureConstants.v:204 END *)
