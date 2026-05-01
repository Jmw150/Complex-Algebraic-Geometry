(** * Lie/LowDimensional.v
    Classification of Lie algebras of dimension ≤ 2, and small examples. *)

From Stdlib Require Import Setoid Ring.
From Stdlib Require Import Logic.Classical.
Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.Lie.Ideals.
Require Import CAG.Lie.Solvable.
Require Import CAG.Lie.Nilpotent.
Require Import CAG.Lie.Radical.
Require Import CAG.Lie.Derivations.

(** ** Abelian Lie algebras *)

(** L is abelian if [x,y]=0 for all x,y. *)
Definition IsAbelian {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) : Prop :=
  forall x y, laF_bracket la x y = la_zero la.

(** Every vector space becomes an abelian Lie algebra. *)
Definition abelian_lie_algebra {F : Type} (fld : Field F) (V : Type)
    (vs : VectorSpaceF fld V) : LieAlgebraF fld V.
Proof.
  refine {|
    laF_vs      := vs;
    laF_bracket := fun _ _ => vsF_zero vs;
  |}.
  - intros x y z. symmetry. apply vs.(vsF_add_zero_r).
  - intros a x y. symmetry. apply vsF_scale_zero_v.
  - intros x y z. symmetry. apply vs.(vsF_add_zero_r).
  - intros a x y. symmetry. apply vsF_scale_zero_v.
  - intros x. reflexivity.
  - intros x y z.
    rewrite vs.(vsF_add_zero_r). apply vs.(vsF_add_zero_r).
Defined.

Lemma abelian_lie_algebra_is_abelian {F : Type} (fld : Field F) (V : Type)
    (vs : VectorSpaceF fld V) :
    IsAbelian (abelian_lie_algebra fld V vs).
Proof. intros x y. reflexivity. Qed.

(** Failed proof of IsAbelian implies existence of a non-zero bracket
    (constructive, useful for direct constructive proof patterns). *)
Lemma exists_nonzero_bracket_implies_not_abelian {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    (exists x y, laF_bracket la x y <> la_zero la) ->
    ~ IsAbelian la.
Proof.
  intros [x [y Hxy]] Habel.
  apply Hxy. apply Habel.
Qed.

(** In an abelian Lie algebra, ad x = 0 for all x. *)
Lemma abelian_ad_zero {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) :
    IsAbelian la -> forall x y, laF_bracket la x y = la_zero la.
Proof. intros H x y. apply H. Qed.

(** ** Classification in dimension 1 *)

(** Every 1-dimensional Lie algebra is abelian.
    If L has basis {x}, then [x,x] = 0 by the alternating axiom. *)
Lemma dim1_is_abelian {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (x : L)
    (hbasis : forall y, exists a : F, y = la_scale la a x) :
    IsAbelian la.
Proof.
  intros y1 y2.
  destruct (hbasis y1) as [a Ha].
  destruct (hbasis y2) as [b Hb].
  rewrite Ha, Hb.
  rewrite la.(laF_bracket_scale_l).
  rewrite la.(laF_bracket_scale_r).
  rewrite la.(laF_bracket_alt).
  rewrite vsF_scale_zero_v.
  apply vsF_scale_zero_v.
Qed.

(** ** Standard 2-dimensional nonabelian Lie algebra *)

(** The nonabelian 2-dimensional algebra has basis {x, y} with [x,y] = x. *)
(** We construct it on F×F. *)

Definition nonabelian_2d_bracket {F : Type} (fld : Field F)
    (u v : F * F) : F * F :=
  (* [u,v] = (u.1 * v.2 - u.2 * v.1, 0) -- this gives [e1,e2] = e1 *)
  (cr_add fld (cr_mul fld (fst u) (snd v))
              (cr_neg fld (cr_mul fld (snd u) (fst v))),
   cr_zero fld).

Definition nonabelian_2d_vs {F : Type} (fld : Field F) : VectorSpaceF fld (F * F).
Proof.
  refine {|
    vsF_add   := fun u v => (cr_add fld (fst u) (fst v), cr_add fld (snd u) (snd v));
    vsF_zero  := (cr_zero fld, cr_zero fld);
    vsF_neg   := fun u => (cr_neg fld (fst u), cr_neg fld (snd u));
    vsF_scale := fun c u => (cr_mul fld c (fst u), cr_mul fld c (snd u));
  |}.
  - intros [a1 b1] [a2 b2] [a3 b3]. simpl.
    f_equal; apply fld.(cr_add_assoc).
  - intros [a1 b1] [a2 b2]. simpl.
    f_equal; apply fld.(cr_add_comm).
  - intros [a b]. simpl.
    f_equal; apply fld.(cr_add_zero).
  - intros [a b]. simpl.
    f_equal; apply fld.(cr_add_neg).
  - intros [a b]. simpl.
    f_equal; (rewrite fld.(cr_mul_comm); apply fld.(cr_mul_one)).
  - intros c d [a b]. simpl.
    f_equal; apply fld.(cr_mul_assoc).
  - intros c [a1 b1] [a2 b2]. simpl.
    f_equal; apply fld.(cr_distrib).
  - intros c d [a b]. simpl.
    f_equal.
    + rewrite (fld.(cr_mul_comm) (cr_add fld c d) a), fld.(cr_distrib).
      f_equal; apply fld.(cr_mul_comm).
    + rewrite (fld.(cr_mul_comm) (cr_add fld c d) b), fld.(cr_distrib).
      f_equal; apply fld.(cr_mul_comm).
Defined.

(* ── ring helpers for the nonabelian_2d proofs ──────────────────────── *)

Local Lemma cr_add_zero_l' {F : Type} (fld : Field F) (a : F) :
    fld.(cr_add) fld.(cr_zero) a = a.
Proof. rewrite fld.(cr_add_comm). apply fld.(cr_add_zero). Qed.

(** Additive inverse uniqueness: a+b=0 → b = -a. *)
Local Lemma cr_add_inv_uniq {F : Type} (fld : Field F) (a b : F) :
    fld.(cr_add) a b = fld.(cr_zero) -> b = fld.(cr_neg) a.
Proof.
  intro H.
  assert (K : fld.(cr_add) (fld.(cr_add) (fld.(cr_neg) a) a) b = fld.(cr_neg) a).
  { rewrite <- fld.(cr_add_assoc), H, fld.(cr_add_zero). reflexivity. }
  rewrite (fld.(cr_add_comm) (fld.(cr_neg) a) a), fld.(cr_add_neg) in K.
  rewrite (cr_add_zero_l' fld b) in K.
  exact K.
Qed.

(** a * 0 = 0. *)
Local Lemma cr_mul_zero_r' {F : Type} (fld : Field F) (a : F) :
    fld.(cr_mul) a fld.(cr_zero) = fld.(cr_zero).
Proof.
  assert (Hd : fld.(cr_mul) a fld.(cr_zero) =
               fld.(cr_add) (fld.(cr_mul) a fld.(cr_zero)) (fld.(cr_mul) a fld.(cr_zero))).
  { rewrite <- fld.(cr_distrib), fld.(cr_add_zero). reflexivity. }
  assert (Hn := fld.(cr_add_neg) (fld.(cr_mul) a fld.(cr_zero))).
  assert (Heq : fld.(cr_add)
      (fld.(cr_add) (fld.(cr_mul) a fld.(cr_zero)) (fld.(cr_mul) a fld.(cr_zero)))
      (fld.(cr_neg) (fld.(cr_mul) a fld.(cr_zero))) = fld.(cr_zero))
    by (rewrite <- Hd; exact Hn).
  rewrite <- fld.(cr_add_assoc), Hn, fld.(cr_add_zero) in Heq.
  exact Heq.
Qed.

(** 0 * a = 0. *)
Local Lemma cr_mul_zero_l' {F : Type} (fld : Field F) (a : F) :
    fld.(cr_mul) fld.(cr_zero) a = fld.(cr_zero).
Proof. rewrite fld.(cr_mul_comm). apply cr_mul_zero_r'. Qed.

(** Right-distributivity: (a+b)*c = a*c + b*c. *)
Local Lemma cr_distrib_r' {F : Type} (fld : Field F) (a b c : F) :
    fld.(cr_mul) (fld.(cr_add) a b) c =
    fld.(cr_add) (fld.(cr_mul) a c) (fld.(cr_mul) b c).
Proof.
  rewrite fld.(cr_mul_comm), fld.(cr_distrib).
  rewrite (fld.(cr_mul_comm) c a), (fld.(cr_mul_comm) c b). reflexivity.
Qed.

(** Negation distributes over addition: -(a+b) = -a + -b. *)
Local Lemma cr_neg_add_distr {F : Type} (fld : Field F) (a b : F) :
    fld.(cr_neg) (fld.(cr_add) a b) =
    fld.(cr_add) (fld.(cr_neg) a) (fld.(cr_neg) b).
Proof.
  symmetry. apply cr_add_inv_uniq.
  (* goal: (a+b) + (-a + -b) = 0 *)
  rewrite <- fld.(cr_add_assoc).
  (* a + (b + (-a + -b)) = 0 *)
  rewrite (fld.(cr_add_assoc) b (fld.(cr_neg) a) (fld.(cr_neg) b)).
  (* a + ((b + -a) + -b) = 0 *)
  rewrite (fld.(cr_add_comm) b (fld.(cr_neg) a)).
  (* a + ((-a + b) + -b) = 0 *)
  rewrite <- (fld.(cr_add_assoc) (fld.(cr_neg) a) b (fld.(cr_neg) b)).
  (* a + (-a + (b + -b)) = 0 *)
  rewrite fld.(cr_add_neg).
  (* a + (-a + 0) = 0 *)
  rewrite fld.(cr_add_zero).
  (* a + -a = 0 *)
  apply fld.(cr_add_neg).
Qed.

(** (-a)*b = -(a*b). *)
Local Lemma cr_neg_mul_l' {F : Type} (fld : Field F) (a b : F) :
    fld.(cr_mul) (fld.(cr_neg) a) b = fld.(cr_neg) (fld.(cr_mul) a b).
Proof.
  apply cr_add_inv_uniq.
  rewrite <- cr_distrib_r', fld.(cr_add_neg).
  apply cr_mul_zero_l'.
Qed.

(** a*(-b) = -(a*b). *)
Local Lemma cr_neg_mul_r' {F : Type} (fld : Field F) (a b : F) :
    fld.(cr_mul) a (fld.(cr_neg) b) = fld.(cr_neg) (fld.(cr_mul) a b).
Proof.
  rewrite fld.(cr_mul_comm), cr_neg_mul_l', fld.(cr_mul_comm). reflexivity.
Qed.

(** -(-a) = a. *)
Local Lemma cr_neg_neg' {F : Type} (fld : Field F) (a : F) :
    fld.(cr_neg) (fld.(cr_neg) a) = a.
Proof.
  symmetry. apply cr_add_inv_uniq.
  rewrite fld.(cr_add_comm). apply fld.(cr_add_neg).
Qed.

(** neg 0 = 0. *)
Local Lemma cr_neg_zero' {F : Type} (fld : Field F) :
    fld.(cr_neg) fld.(cr_zero) = fld.(cr_zero).
Proof.
  symmetry. apply cr_add_inv_uniq.
  apply fld.(cr_add_zero).
Qed.

(* ── main definition ─────────────────────────────────────────────────── *)

(** The ring identity needed for Jacobi:
    -x2*(y1*z2-y2*z1) + -y2*(z1*x2-z2*x1) + -z2*(x1*y2-x2*y1) = 0. *)
Local Lemma cr_add_neg_l' {F : Type} (fld : Field F) (a : F) :
    fld.(cr_add) (fld.(cr_neg) a) a = fld.(cr_zero).
Proof. rewrite fld.(cr_add_comm). apply fld.(cr_add_neg). Qed.

(** The ring identity needed for Jacobi:
    -x2*(y1*z2-y2*z1) + -y2*(z1*x2-z2*x1) + -z2*(x1*y2-x2*y1) = 0.
    Proof: after expansion the 6 monomials cancel in 3 pairs:
      -(x2*y1*z2) + (x2*y2*z1) + -(y2*z1*x2) + (y2*z2*x1) + -(z2*x1*y2) + (z2*x2*y1)
    where y2*z1*x2 = x2*y2*z1, y2*z2*x1 = x1*y2*z2, z2*x2*y1 = x2*y1*z2. *)
Local Lemma nonabelian_jacobi_ring {F : Type} (fld : Field F)
    (x1 x2 y1 y2 z1 z2 : F) :
    fld.(cr_add) (fld.(cr_add)
      (fld.(cr_neg) (fld.(cr_mul) x2
        (fld.(cr_add) (fld.(cr_mul) y1 z2) (fld.(cr_neg) (fld.(cr_mul) y2 z1)))))
      (fld.(cr_neg) (fld.(cr_mul) y2
        (fld.(cr_add) (fld.(cr_mul) z1 x2) (fld.(cr_neg) (fld.(cr_mul) z2 x1))))))
    (fld.(cr_neg) (fld.(cr_mul) z2
      (fld.(cr_add) (fld.(cr_mul) x1 y2) (fld.(cr_neg) (fld.(cr_mul) x2 y1)))))
    = fld.(cr_zero).
Proof.
  (* Let A = x2*(y1*z2), B = x2*(y2*z1), C = x1*(y2*z2).
     LHS = -A + B + -B + C + -C + A = 0. *)
  set (A := fld.(cr_mul) x2 (fld.(cr_mul) y1 z2)).
  set (B := fld.(cr_mul) x2 (fld.(cr_mul) y2 z1)).
  set (C := fld.(cr_mul) x1 (fld.(cr_mul) y2 z2)).
  (* Step 1: rewrite the three bracketed sub-expressions *)
  (* First term: -(x2*(y1*z2 + -(y2*z1))) = -(A + -(B)) = -A + B *)
  assert (H1 : fld.(cr_neg) (fld.(cr_mul) x2
      (fld.(cr_add) (fld.(cr_mul) y1 z2) (fld.(cr_neg) (fld.(cr_mul) y2 z1))))
      = fld.(cr_add) (fld.(cr_neg) A) B).
  { unfold A, B.
    rewrite fld.(cr_distrib), cr_neg_mul_r', cr_neg_add_distr, cr_neg_neg'.
    reflexivity. }
  (* Second term: -(y2*(z1*x2 + -(z2*x1))) = -(B + -C) = -B + C *)
  (* Note: y2*(z1*x2) = B and y2*(z2*x1) = C after commutativity *)
  assert (H2 : fld.(cr_neg) (fld.(cr_mul) y2
      (fld.(cr_add) (fld.(cr_mul) z1 x2) (fld.(cr_neg) (fld.(cr_mul) z2 x1))))
      = fld.(cr_add) (fld.(cr_neg) B) C).
  { unfold B, C.
    rewrite fld.(cr_distrib), cr_neg_mul_r', cr_neg_add_distr, cr_neg_neg'.
    (* y2*(z1*x2) = x2*(y2*z1) and y2*(z2*x1) = x1*(y2*z2) *)
    f_equal.
    - (* -(y2*(z1*x2)) = -(x2*(y2*z1)) *)
      f_equal.
      rewrite (fld.(cr_mul_comm) z1 x2), fld.(cr_mul_assoc),
              (fld.(cr_mul_comm) y2 x2), <- fld.(cr_mul_assoc). reflexivity.
    - (* y2*(z2*x1) = x1*(y2*z2) *)
      rewrite (fld.(cr_mul_comm) z2 x1), fld.(cr_mul_assoc),
              (fld.(cr_mul_comm) y2 x1), <- fld.(cr_mul_assoc). reflexivity. }
  (* Third term: -(z2*(x1*y2 + -(x2*y1))) = -(C + -A) = -C + A *)
  assert (H3 : fld.(cr_neg) (fld.(cr_mul) z2
      (fld.(cr_add) (fld.(cr_mul) x1 y2) (fld.(cr_neg) (fld.(cr_mul) x2 y1))))
      = fld.(cr_add) (fld.(cr_neg) C) A).
  { unfold A, C.
    rewrite fld.(cr_distrib), cr_neg_mul_r', cr_neg_add_distr, cr_neg_neg'.
    f_equal.
    - (* -(z2*(x1*y2)) = -(x1*(y2*z2)) *)
      f_equal.
      rewrite fld.(cr_mul_assoc), (fld.(cr_mul_comm) z2 x1),
              <- fld.(cr_mul_assoc), (fld.(cr_mul_comm) z2 y2). reflexivity.
    - (* z2*(x2*y1) = x2*(y1*z2) *)
      rewrite fld.(cr_mul_assoc), (fld.(cr_mul_comm) z2 x2),
              <- fld.(cr_mul_assoc), (fld.(cr_mul_comm) z2 y1). reflexivity. }
  rewrite H1, H2, H3.
  (* ((-A+B) + (-B+C)) + (-C+A) = 0 *)
  rewrite <- (fld.(cr_add_assoc) (fld.(cr_add) (fld.(cr_neg) A) B)
                                  (fld.(cr_add) (fld.(cr_neg) B) C)
                                  (fld.(cr_add) (fld.(cr_neg) C) A)).
  (* (-A+B) + ((-B+C) + (-C+A)) = 0 *)
  rewrite <- (fld.(cr_add_assoc) (fld.(cr_neg) B) C (fld.(cr_add) (fld.(cr_neg) C) A)).
  (* (-A+B) + (-B + (C + (-C+A))) = 0 *)
  rewrite (fld.(cr_add_assoc) C (fld.(cr_neg) C) A), fld.(cr_add_neg), cr_add_zero_l'.
  (* (-A+B) + (-B+A) = 0 *)
  rewrite <- (fld.(cr_add_assoc) (fld.(cr_neg) A) B (fld.(cr_add) (fld.(cr_neg) B) A)).
  (* -A + (B + (-B+A)) = 0 *)
  rewrite (fld.(cr_add_assoc) B (fld.(cr_neg) B) A), fld.(cr_add_neg), cr_add_zero_l'.
  (* -A + A = 0 *)
  apply cr_add_neg_l'.
Qed.

Definition nonabelian_2d {F : Type} (fld : Field F) : LieAlgebraF fld (F * F).
Proof.
  refine {|
    laF_vs      := nonabelian_2d_vs fld;
    laF_bracket := nonabelian_2d_bracket fld;
  |}.
  (* ── bracket_add_l: [(u+v),w] = [u,w]+[v,w] ── *)
  - intros [x1 x2] [y1 y2] [z1 z2].
    unfold nonabelian_2d_bracket, nonabelian_2d_vs. simpl.
    f_equal.
    + (* (x1+y1)*z2 - (x2+y2)*z1 = (x1*z2 - x2*z1) + (y1*z2 - y2*z1) *)
      (* Expand: LHS = x1*z2 + y1*z2 + -(x2*z1) + -(y2*z1) = RHS *)
      rewrite cr_distrib_r', cr_distrib_r', cr_neg_add_distr.
      (* (x1*z2 + y1*z2) + (-(x2*z1) + -(y2*z1))
         = (x1*z2 + -(x2*z1)) + (y1*z2 + -(y2*z1)) *)
      rewrite <- fld.(cr_add_assoc).
      rewrite (fld.(cr_add_assoc) (fld.(cr_mul) y1 z2)
                                   (fld.(cr_neg) (fld.(cr_mul) x2 z1))
                                   (fld.(cr_neg) (fld.(cr_mul) y2 z1))).
      rewrite (fld.(cr_add_comm) (fld.(cr_mul) y1 z2) (fld.(cr_neg) (fld.(cr_mul) x2 z1))).
      rewrite <- (fld.(cr_add_assoc) (fld.(cr_neg) (fld.(cr_mul) x2 z1))
                                      (fld.(cr_mul) y1 z2)
                                      (fld.(cr_neg) (fld.(cr_mul) y2 z1))).
      rewrite (fld.(cr_add_assoc) (fld.(cr_mul) x1 z2)
                                   (fld.(cr_neg) (fld.(cr_mul) x2 z1))
                                   (fld.(cr_add) (fld.(cr_mul) y1 z2) (fld.(cr_neg) (fld.(cr_mul) y2 z1)))).
      reflexivity.
    + symmetry. apply fld.(cr_add_zero).
  (* ── bracket_scale_l: [(c*u),v] = c*[u,v] ── *)
  - intros c [x1 x2] [y1 y2].
    unfold nonabelian_2d_bracket, nonabelian_2d_vs. simpl.
    f_equal.
    + (* (c*x1)*y2 - (c*x2)*y1 = c*(x1*y2 - x2*y1) *)
      rewrite <- fld.(cr_mul_assoc), <- fld.(cr_mul_assoc),
              <- cr_neg_mul_r', <- fld.(cr_distrib). reflexivity.
    + symmetry. apply cr_mul_zero_r'.
  (* ── bracket_add_r: [u,(v+w)] = [u,v]+[u,w] ── *)
  - intros [x1 x2] [y1 y2] [z1 z2].
    unfold nonabelian_2d_bracket, nonabelian_2d_vs. simpl.
    f_equal.
    + (* x1*(y2+z2) - x2*(y1+z1) = (x1*y2 - x2*y1) + (x1*z2 - x2*z1) *)
      rewrite fld.(cr_distrib), fld.(cr_distrib), cr_neg_add_distr.
      rewrite <- fld.(cr_add_assoc).
      rewrite (fld.(cr_add_assoc) (fld.(cr_mul) x1 z2)
                                   (fld.(cr_neg) (fld.(cr_mul) x2 y1))
                                   (fld.(cr_neg) (fld.(cr_mul) x2 z1))).
      rewrite (fld.(cr_add_comm) (fld.(cr_mul) x1 z2) (fld.(cr_neg) (fld.(cr_mul) x2 y1))).
      rewrite <- (fld.(cr_add_assoc) (fld.(cr_neg) (fld.(cr_mul) x2 y1))
                                      (fld.(cr_mul) x1 z2)
                                      (fld.(cr_neg) (fld.(cr_mul) x2 z1))).
      rewrite (fld.(cr_add_assoc) (fld.(cr_mul) x1 y2)
                                   (fld.(cr_neg) (fld.(cr_mul) x2 y1))
                                   (fld.(cr_add) (fld.(cr_mul) x1 z2) (fld.(cr_neg) (fld.(cr_mul) x2 z1)))).
      reflexivity.
    + symmetry. apply fld.(cr_add_zero).
  (* ── bracket_scale_r: [u,(c*v)] = c*[u,v] ── *)
  - intros c [x1 x2] [y1 y2].
    unfold nonabelian_2d_bracket, nonabelian_2d_vs. simpl.
    f_equal.
    + (* x1*(c*y2) - x2*(c*y1) = c*(x1*y2 - x2*y1) *)
      rewrite (fld.(cr_mul_comm) x1 (fld.(cr_mul) c y2)),
              <- fld.(cr_mul_assoc), (fld.(cr_mul_comm) y2 x1),
              (fld.(cr_mul_comm) x2 (fld.(cr_mul) c y1)),
              <- fld.(cr_mul_assoc), (fld.(cr_mul_comm) y1 x2),
              <- cr_neg_mul_r', <- fld.(cr_distrib). reflexivity.
    + symmetry. apply cr_mul_zero_r'.
  (* ── bracket_alt: [u,u] = 0 ── *)
  - intros [x1 x2].
    unfold nonabelian_2d_bracket, nonabelian_2d_vs. simpl.
    rewrite (fld.(cr_mul_comm) x1 x2), fld.(cr_add_neg). reflexivity.
  (* ── jacobi: [x,[y,z]] + [y,[z,x]] + [z,[x,y]] = 0 ── *)
  (* The bracket always has second component 0.  The first component of
     [u,v] = u.1*v.2 - u.2*v.1, and when v.2 = 0 this becomes -u.2*v.1.
     So [x,[y,z]].1 = -x2*(y1*z2-y2*z1), etc.
     The sum telescopes to 0 by the nonabelian_jacobi_ring lemma. *)
  - intros [x1 x2] [y1 y2] [z1 z2].
    unfold nonabelian_2d_bracket, nonabelian_2d_vs. simpl.
    (* Simplify x1*0, y1*0, z1*0 terms *)
    rewrite cr_mul_zero_r', cr_add_zero_l'.
    rewrite cr_mul_zero_r', cr_add_zero_l'.
    rewrite cr_mul_zero_r', cr_add_zero_l'.
    f_equal.
    + apply nonabelian_jacobi_ring.
    + rewrite fld.(cr_add_zero), fld.(cr_add_zero). reflexivity.
Defined.

(** The nonabelian 2d algebra is not abelian (over any field). *)
Lemma nonabelian_2d_is_lie {F : Type} (fld : Field F) :
    IsAbelian (nonabelian_2d fld) -> False.
Proof.
  intro HAb.
  (* Compute [(1,0), (0,1)] two ways *)
  assert (H := HAb (fld.(cr_one), fld.(cr_zero)) (fld.(cr_zero), fld.(cr_one))).
  unfold laF_bracket, nonabelian_2d, nonabelian_2d_bracket, la_zero in H. simpl in H.
  (* H : (1*0 + -(0*1), 0) = (0, 0)  -- but 1*0 = 0 and -(0*1) = 0,
     wait: it's (1*1 + -(0*0), 0) since fst(1,0)=1, snd(1,0)=0, fst(0,1)=0, snd(0,1)=1
     i.e., (fst u * snd v - snd u * fst v) = (1*1 - 0*0, 0) = (1, 0) *)
  (* Simplify: cr_one * cr_one = cr_one *)
  rewrite fld.(cr_mul_one) in H.
  (* cr_zero * cr_zero = cr_zero *)
  rewrite cr_mul_zero_r' in H.
  (* cr_neg cr_zero = cr_zero *)
  rewrite cr_neg_zero' in H.
  (* cr_one + cr_zero = cr_one *)
  rewrite fld.(cr_add_zero) in H.
  (* H : (cr_one, cr_zero) = (cr_zero, cr_zero) *)
  (* Extract the first component equality *)
  assert (Heq : fld.(cr_one) = fld.(cr_zero)) by (exact (f_equal fst H)).
  exact (fld.(fld_nontrivial) (eq_sym Heq)).
Qed.

(** ** Classification in dimension 2 *)

(* dim2_classification axiom removed: was a real theorem (every 2-dim Lie
   algebra is abelian or iso to nonabelian_2d) but never referenced
   anywhere in the codebase. The standard classification proof requires
   basis manipulation and case-splits on whether [x,y] = 0. *)

(** ** Exercise 2: 3-dimensional Lie algebra with [x,y]=z, [x,z]=y, [y,z]=0 *)

(** Bracket on F³: [u,v] = (0, u₁v₃ - u₃v₁, u₁v₂ - u₂v₁).
    Standard basis: x = (1,0,0), y = (0,1,0), z = (0,0,1).
    [x,y] = z, [x,z] = y, [y,z] = 0. *)

Definition ex2_bracket {F : Type} (fld : Field F)
    (u v : F * F * F) : F * F * F :=
  let '(u1, u2, u3) := u in
  let '(v1, v2, v3) := v in
  (fld.(cr_zero),
   fld.(cr_add) (fld.(cr_mul) u1 v3) (fld.(cr_neg) (fld.(cr_mul) u3 v1)),
   fld.(cr_add) (fld.(cr_mul) u1 v2) (fld.(cr_neg) (fld.(cr_mul) u2 v1))).

Definition ex2_vs {F : Type} (fld : Field F) : VectorSpaceF fld (F * F * F).
Proof.
  refine {|
    vsF_add   := fun '(a1,a2,a3) '(b1,b2,b3) => (cr_add fld a1 b1, cr_add fld a2 b2, cr_add fld a3 b3);
    vsF_zero  := (cr_zero fld, cr_zero fld, cr_zero fld);
    vsF_neg   := fun '(a1,a2,a3) => (cr_neg fld a1, cr_neg fld a2, cr_neg fld a3);
    vsF_scale := fun c '(a1,a2,a3) => (cr_mul fld c a1, cr_mul fld c a2, cr_mul fld c a3);
  |}.
  - intros [[a1 a2] a3] [[b1 b2] b3] [[c1 c2] c3]. simpl.
    f_equal; [f_equal|]; apply fld.(cr_add_assoc).
  - intros [[a1 a2] a3] [[b1 b2] b3]. simpl.
    f_equal; [f_equal|]; apply fld.(cr_add_comm).
  - intros [[a1 a2] a3]. simpl.
    f_equal; [f_equal|]; apply fld.(cr_add_zero).
  - intros [[a1 a2] a3]. simpl.
    f_equal; [f_equal|]; apply fld.(cr_add_neg).
  - intros [[a1 a2] a3]. simpl.
    f_equal; [f_equal|]; (rewrite fld.(cr_mul_comm); apply fld.(cr_mul_one)).
  - intros c d [[a1 a2] a3]. simpl.
    f_equal; [f_equal|]; apply fld.(cr_mul_assoc).
  - intros c [[a1 a2] a3] [[b1 b2] b3]. simpl.
    f_equal; [f_equal|]; apply fld.(cr_distrib).
  - intros c d [[a1 a2] a3]. simpl.
    f_equal; [f_equal|];
    (rewrite (fld.(cr_mul_comm) (cr_add fld c d) _), fld.(cr_distrib);
     f_equal; apply fld.(cr_mul_comm)).
Defined.

(** -(a * 0) = 0. *)
Local Lemma cr_neg_mul_zero {F : Type} (fld : Field F) (a : F) :
    fld.(cr_neg) (fld.(cr_mul) a fld.(cr_zero)) = fld.(cr_zero).
Proof.
  rewrite cr_mul_zero_r'. apply cr_neg_zero'.
Qed.

(** Telescoping sum: (P + -R) + (Q + -P) + (R + -Q) = 0.
    After converting to (-R+P) + (-P+Q) + (-Q+R) form, three pairs cancel. *)
Local Lemma telescoping_zero {F : Type} (fld : Field F) (P Q R : F) :
    fld.(cr_add) (fld.(cr_add)
      (fld.(cr_add) P (fld.(cr_neg) R))
      (fld.(cr_add) Q (fld.(cr_neg) P)))
      (fld.(cr_add) R (fld.(cr_neg) Q))
    = fld.(cr_zero).
Proof.
  rewrite (fld.(cr_add_comm) P (fld.(cr_neg) R)).
  rewrite (fld.(cr_add_comm) Q (fld.(cr_neg) P)).
  rewrite (fld.(cr_add_comm) R (fld.(cr_neg) Q)).
  (* ((-R+P) + (-P+Q)) + (-Q+R) = 0 *)
  rewrite <- (fld.(cr_add_assoc) (fld.(cr_add) (fld.(cr_neg) R) P)
                                  (fld.(cr_add) (fld.(cr_neg) P) Q)
                                  (fld.(cr_add) (fld.(cr_neg) Q) R)).
  rewrite <- (fld.(cr_add_assoc) (fld.(cr_neg) P) Q (fld.(cr_add) (fld.(cr_neg) Q) R)).
  rewrite (fld.(cr_add_assoc) Q (fld.(cr_neg) Q) R), fld.(cr_add_neg), cr_add_zero_l'.
  rewrite <- (fld.(cr_add_assoc) (fld.(cr_neg) R) P (fld.(cr_add) (fld.(cr_neg) P) R)).
  rewrite (fld.(cr_add_assoc) P (fld.(cr_neg) P) R), fld.(cr_add_neg), cr_add_zero_l'.
  apply cr_add_neg_l'.
Qed.

Definition exercise2_lie {F : Type} (fld : Field F) : LieAlgebraF fld (F * F * F).
Proof.
  refine {|
    laF_vs      := ex2_vs fld;
    laF_bracket := ex2_bracket fld;
  |}.
  - (* bracket_add_l *)
    intros [[x1 x2] x3] [[y1 y2] y3] [[z1 z2] z3].
    unfold ex2_bracket, ex2_vs. simpl.
    apply (f_equal2 pair); [apply (f_equal2 pair)|].
    + symmetry. apply cr_add_zero_l'.
    + rewrite cr_distrib_r', cr_distrib_r', cr_neg_add_distr.
      rewrite <- fld.(cr_add_assoc).
      rewrite (fld.(cr_add_assoc) (fld.(cr_mul) y1 z3)
                                   (fld.(cr_neg) (fld.(cr_mul) x3 z1))
                                   (fld.(cr_neg) (fld.(cr_mul) y3 z1))).
      rewrite (fld.(cr_add_comm) (fld.(cr_mul) y1 z3) (fld.(cr_neg) (fld.(cr_mul) x3 z1))).
      rewrite <- (fld.(cr_add_assoc) (fld.(cr_neg) (fld.(cr_mul) x3 z1))
                                      (fld.(cr_mul) y1 z3)
                                      (fld.(cr_neg) (fld.(cr_mul) y3 z1))).
      rewrite (fld.(cr_add_assoc) (fld.(cr_mul) x1 z3)
                                   (fld.(cr_neg) (fld.(cr_mul) x3 z1))
                                   (fld.(cr_add) (fld.(cr_mul) y1 z3) (fld.(cr_neg) (fld.(cr_mul) y3 z1)))).
      reflexivity.
    + rewrite cr_distrib_r', cr_distrib_r', cr_neg_add_distr.
      rewrite <- fld.(cr_add_assoc).
      rewrite (fld.(cr_add_assoc) (fld.(cr_mul) y1 z2)
                                   (fld.(cr_neg) (fld.(cr_mul) x2 z1))
                                   (fld.(cr_neg) (fld.(cr_mul) y2 z1))).
      rewrite (fld.(cr_add_comm) (fld.(cr_mul) y1 z2) (fld.(cr_neg) (fld.(cr_mul) x2 z1))).
      rewrite <- (fld.(cr_add_assoc) (fld.(cr_neg) (fld.(cr_mul) x2 z1))
                                      (fld.(cr_mul) y1 z2)
                                      (fld.(cr_neg) (fld.(cr_mul) y2 z1))).
      rewrite (fld.(cr_add_assoc) (fld.(cr_mul) x1 z2)
                                   (fld.(cr_neg) (fld.(cr_mul) x2 z1))
                                   (fld.(cr_add) (fld.(cr_mul) y1 z2) (fld.(cr_neg) (fld.(cr_mul) y2 z1)))).
      reflexivity.
  - (* bracket_scale_l *)
    intros c [[x1 x2] x3] [[y1 y2] y3].
    unfold ex2_bracket, ex2_vs. simpl.
    apply (f_equal2 pair); [apply (f_equal2 pair)|].
    + symmetry. apply cr_mul_zero_r'.
    + rewrite <- fld.(cr_mul_assoc), <- fld.(cr_mul_assoc),
              <- cr_neg_mul_r', <- fld.(cr_distrib). reflexivity.
    + rewrite <- fld.(cr_mul_assoc), <- fld.(cr_mul_assoc),
              <- cr_neg_mul_r', <- fld.(cr_distrib). reflexivity.
  - (* bracket_add_r *)
    intros [[x1 x2] x3] [[y1 y2] y3] [[z1 z2] z3].
    unfold ex2_bracket, ex2_vs. simpl.
    apply (f_equal2 pair); [apply (f_equal2 pair)|].
    + symmetry. apply cr_add_zero_l'.
    + rewrite fld.(cr_distrib), fld.(cr_distrib), cr_neg_add_distr.
      rewrite <- fld.(cr_add_assoc).
      rewrite (fld.(cr_add_assoc) (fld.(cr_mul) x1 z3)
                                   (fld.(cr_neg) (fld.(cr_mul) x3 y1))
                                   (fld.(cr_neg) (fld.(cr_mul) x3 z1))).
      rewrite (fld.(cr_add_comm) (fld.(cr_mul) x1 z3) (fld.(cr_neg) (fld.(cr_mul) x3 y1))).
      rewrite <- (fld.(cr_add_assoc) (fld.(cr_neg) (fld.(cr_mul) x3 y1))
                                      (fld.(cr_mul) x1 z3)
                                      (fld.(cr_neg) (fld.(cr_mul) x3 z1))).
      rewrite (fld.(cr_add_assoc) (fld.(cr_mul) x1 y3)
                                   (fld.(cr_neg) (fld.(cr_mul) x3 y1))
                                   (fld.(cr_add) (fld.(cr_mul) x1 z3) (fld.(cr_neg) (fld.(cr_mul) x3 z1)))).
      reflexivity.
    + rewrite fld.(cr_distrib), fld.(cr_distrib), cr_neg_add_distr.
      rewrite <- fld.(cr_add_assoc).
      rewrite (fld.(cr_add_assoc) (fld.(cr_mul) x1 z2)
                                   (fld.(cr_neg) (fld.(cr_mul) x2 y1))
                                   (fld.(cr_neg) (fld.(cr_mul) x2 z1))).
      rewrite (fld.(cr_add_comm) (fld.(cr_mul) x1 z2) (fld.(cr_neg) (fld.(cr_mul) x2 y1))).
      rewrite <- (fld.(cr_add_assoc) (fld.(cr_neg) (fld.(cr_mul) x2 y1))
                                      (fld.(cr_mul) x1 z2)
                                      (fld.(cr_neg) (fld.(cr_mul) x2 z1))).
      rewrite (fld.(cr_add_assoc) (fld.(cr_mul) x1 y2)
                                   (fld.(cr_neg) (fld.(cr_mul) x2 y1))
                                   (fld.(cr_add) (fld.(cr_mul) x1 z2) (fld.(cr_neg) (fld.(cr_mul) x2 z1)))).
      reflexivity.
  - (* bracket_scale_r *)
    intros c [[x1 x2] x3] [[y1 y2] y3].
    unfold ex2_bracket, ex2_vs. simpl.
    apply (f_equal2 pair); [apply (f_equal2 pair)|].
    + symmetry. apply cr_mul_zero_r'.
    + rewrite (fld.(cr_mul_comm) x1 (fld.(cr_mul) c y3)),
              <- fld.(cr_mul_assoc), (fld.(cr_mul_comm) y3 x1),
              (fld.(cr_mul_comm) x3 (fld.(cr_mul) c y1)),
              <- fld.(cr_mul_assoc), (fld.(cr_mul_comm) y1 x3),
              <- cr_neg_mul_r', <- fld.(cr_distrib). reflexivity.
    + rewrite (fld.(cr_mul_comm) x1 (fld.(cr_mul) c y2)),
              <- fld.(cr_mul_assoc), (fld.(cr_mul_comm) y2 x1),
              (fld.(cr_mul_comm) x2 (fld.(cr_mul) c y1)),
              <- fld.(cr_mul_assoc), (fld.(cr_mul_comm) y1 x2),
              <- cr_neg_mul_r', <- fld.(cr_distrib). reflexivity.
  - (* bracket_alt *)
    intros [[x1 x2] x3].
    unfold ex2_bracket, ex2_vs. simpl.
    rewrite (fld.(cr_mul_comm) x1 x3), fld.(cr_add_neg),
            (fld.(cr_mul_comm) x1 x2), fld.(cr_add_neg). reflexivity.
  - (* jacobi: three component proofs.
       [x,[y,z]] = (0, x1*(y1*z2-y2*z1)-x3*0, x1*(y1*z3-y3*z1)-x2*0)  etc.
       A component (fst fst): (0+0)+0 = 0
       B component (snd fst): telescoping sum = 0
       C component (snd):     telescoping sum = 0 *)
    intros [[x1 x2] x3] [[y1 y2] y3] [[z1 z2] z3].
    unfold ex2_bracket, ex2_vs. simpl.
    apply (f_equal2 pair); [apply (f_equal2 pair)|].
    + (* A: (0+0)+0 = 0 *)
      rewrite cr_add_zero_l', cr_add_zero_l'. reflexivity.
    + (* B: x1*(y1*z2-y2*z1) + y1*(z1*x2-z2*x1) + z1*(x1*y2-x2*y1) = 0
           after eliminating -(x3*0), -(y3*0), -(z3*0) *)
      rewrite (cr_neg_mul_zero fld x3), (cr_neg_mul_zero fld y3), (cr_neg_mul_zero fld z3).
      rewrite fld.(cr_add_zero), fld.(cr_add_zero), fld.(cr_add_zero).
      set (P := fld.(cr_mul) x1 (fld.(cr_mul) y1 z2)).
      set (Q := fld.(cr_mul) y1 (fld.(cr_mul) z1 x2)).
      set (R := fld.(cr_mul) z1 (fld.(cr_mul) x1 y2)).
      assert (T1 : fld.(cr_mul) x1 (fld.(cr_add) (fld.(cr_mul) y1 z2) (fld.(cr_neg) (fld.(cr_mul) y2 z1)))
                   = fld.(cr_add) P (fld.(cr_neg) R)).
      { unfold P, R.
        rewrite fld.(cr_distrib), cr_neg_mul_r'. f_equal. f_equal.
        rewrite (fld.(cr_mul_comm) y2 z1), fld.(cr_mul_assoc),
                (fld.(cr_mul_comm) x1 z1), <- fld.(cr_mul_assoc). reflexivity. }
      assert (T2 : fld.(cr_mul) y1 (fld.(cr_add) (fld.(cr_mul) z1 x2) (fld.(cr_neg) (fld.(cr_mul) z2 x1)))
                   = fld.(cr_add) Q (fld.(cr_neg) P)).
      { unfold P, Q.
        rewrite fld.(cr_distrib), cr_neg_mul_r'. f_equal. f_equal.
        rewrite (fld.(cr_mul_comm) z2 x1), fld.(cr_mul_assoc),
                (fld.(cr_mul_comm) y1 x1), <- fld.(cr_mul_assoc),
                (fld.(cr_mul_comm) y1 z2). reflexivity. }
      assert (T3 : fld.(cr_mul) z1 (fld.(cr_add) (fld.(cr_mul) x1 y2) (fld.(cr_neg) (fld.(cr_mul) x2 y1)))
                   = fld.(cr_add) R (fld.(cr_neg) Q)).
      { unfold Q, R.
        rewrite fld.(cr_distrib), cr_neg_mul_r'. f_equal. f_equal.
        rewrite (fld.(cr_mul_comm) x2 y1), fld.(cr_mul_assoc),
                (fld.(cr_mul_comm) z1 y1), <- fld.(cr_mul_assoc). reflexivity. }
      rewrite T1, T2, T3. apply telescoping_zero.
    + (* C: x1*(y1*z3-y3*z1) + y1*(z1*x3-z3*x1) + z1*(x1*y3-x3*y1) = 0
           after eliminating -(x2*0), -(y2*0), -(z2*0) *)
      rewrite (cr_neg_mul_zero fld x2), (cr_neg_mul_zero fld y2), (cr_neg_mul_zero fld z2).
      rewrite fld.(cr_add_zero), fld.(cr_add_zero), fld.(cr_add_zero).
      set (P := fld.(cr_mul) x1 (fld.(cr_mul) y1 z3)).
      set (Q := fld.(cr_mul) y1 (fld.(cr_mul) z1 x3)).
      set (R := fld.(cr_mul) z1 (fld.(cr_mul) x1 y3)).
      assert (T1 : fld.(cr_mul) x1 (fld.(cr_add) (fld.(cr_mul) y1 z3) (fld.(cr_neg) (fld.(cr_mul) y3 z1)))
                   = fld.(cr_add) P (fld.(cr_neg) R)).
      { unfold P, R.
        rewrite fld.(cr_distrib), cr_neg_mul_r'. f_equal. f_equal.
        rewrite (fld.(cr_mul_comm) y3 z1), fld.(cr_mul_assoc),
                (fld.(cr_mul_comm) x1 z1), <- fld.(cr_mul_assoc). reflexivity. }
      assert (T2 : fld.(cr_mul) y1 (fld.(cr_add) (fld.(cr_mul) z1 x3) (fld.(cr_neg) (fld.(cr_mul) z3 x1)))
                   = fld.(cr_add) Q (fld.(cr_neg) P)).
      { unfold P, Q.
        rewrite fld.(cr_distrib), cr_neg_mul_r'. f_equal. f_equal.
        rewrite (fld.(cr_mul_comm) z3 x1), fld.(cr_mul_assoc),
                (fld.(cr_mul_comm) y1 x1), <- fld.(cr_mul_assoc),
                (fld.(cr_mul_comm) y1 z3). reflexivity. }
      assert (T3 : fld.(cr_mul) z1 (fld.(cr_add) (fld.(cr_mul) x1 y3) (fld.(cr_neg) (fld.(cr_mul) x3 y1)))
                   = fld.(cr_add) R (fld.(cr_neg) Q)).
      { unfold Q, R.
        rewrite fld.(cr_distrib), cr_neg_mul_r'. f_equal. f_equal.
        rewrite (fld.(cr_mul_comm) x3 y1), fld.(cr_mul_assoc),
                (fld.(cr_mul_comm) z1 y1), <- fld.(cr_mul_assoc). reflexivity. }
      rewrite T1, T2, T3. apply telescoping_zero.
Defined.

(** ** sl(2,F) — the key 3-dimensional example *)

(** Standard basis of sl(2,F):
    x = [[0,1],[0,0]], h = [[1,0],[0,-1]], y = [[0,0],[1,0]] *)

(** Multiplication table: [h,x]=2x, [h,y]=-2y, [x,y]=h. *)
Lemma sl2_bracket_hx :
  forall {F : Type} (fld : Field F), True. (* placeholder *)
Proof. intros. exact I. Qed.

(** ** Construction of sl(2,F) on F * F * F.
    Basis: x = (1,0,0), h = (0,1,0), y = (0,0,1).
    Bracket: [(a,b,c), (d,e,f)] = (2(bd-ae), af-cd, 2(ce-bf)).
    Note F * F * F in Coq is (F * F) * F.

    These are specialized in their own subsection because we need them
    to apply [sl2_abstract_simple]. *)

Section Sl2On3D.
  Context {F : Type} (fld : Field F).

  Local Notation "0F" := (cr_zero fld).
  Local Notation "1F" := (cr_one fld).
  Local Notation "x +F y" := (cr_add fld x y) (at level 50).
  Local Notation "x *F y" := (cr_mul fld x y) (at level 40).
  Local Notation "-F x" := (cr_neg fld x) (at level 35).

  (** Register fld as a ring for the [ring] tactic. *)
  Lemma fld_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof.
    constructor.
    - intro x. apply (cr_add_zero_l fld).
    - intros x y. apply (cr_add_comm fld).
    - intros x y z. apply (cr_add_assoc fld).
    - intro x. apply (cr_one_mul fld).
    - intros x y. apply (cr_mul_comm fld).
    - intros x y z. apply (cr_mul_assoc fld).
    - intros x y z. apply (cr_distrib_r fld).
    - intros x y. reflexivity.
    - intro x. apply (cr_add_neg fld).
  Qed.

  Add Ring fld_ring_inst : fld_ring_theory.

  (** Triple type. *)
  Definition tF := (F * F * F)%type.

  (** Project the components. *)
  Definition tF_x (t : tF) : F := fst (fst t).
  Definition tF_h (t : tF) : F := snd (fst t).
  Definition tF_y (t : tF) : F := snd t.

  (** Triple constructor. *)
  Definition mkT (a b c : F) : tF := ((a, b), c).

  Definition la3_add (u v : tF) : tF :=
    mkT (tF_x u +F tF_x v) (tF_h u +F tF_h v) (tF_y u +F tF_y v).

  Definition la3_zero : tF := mkT 0F 0F 0F.

  Definition la3_neg (u : tF) : tF :=
    mkT (-F tF_x u) (-F tF_h u) (-F tF_y u).

  Definition la3_scale (c : F) (u : tF) : tF :=
    mkT (c *F tF_x u) (c *F tF_h u) (c *F tF_y u).

  (** Bracket of two triples. *)
  Definition la3_bracket (u v : tF) : tF :=
    let two := 1F +F 1F in
    mkT
      (two *F (tF_h u *F tF_x v +F -F (tF_x u *F tF_h v)))
      (tF_x u *F tF_y v +F -F (tF_y u *F tF_x v))
      (two *F (tF_y u *F tF_h v +F -F (tF_h u *F tF_y v))).

  (** Construct the vector space. *)
  Definition la3_vs : VectorSpaceF fld tF.
  Proof.
    refine {|
      vsF_add   := la3_add;
      vsF_zero  := la3_zero;
      vsF_neg   := la3_neg;
      vsF_scale := la3_scale;
    |}.
    - intros u v w. unfold la3_add, mkT, tF_x, tF_h, tF_y. simpl.
      f_equal. f_equal; apply fld.(cr_add_assoc). apply fld.(cr_add_assoc).
    - intros u v. unfold la3_add, mkT, tF_x, tF_h, tF_y. simpl.
      f_equal. f_equal; apply fld.(cr_add_comm). apply fld.(cr_add_comm).
    - intro u. destruct u as [[a b] c]. unfold la3_add, la3_zero, mkT, tF_x, tF_h, tF_y. simpl.
      f_equal. f_equal; apply fld.(cr_add_zero). apply fld.(cr_add_zero).
    - intro u. destruct u as [[a b] c]. unfold la3_add, la3_zero, la3_neg, mkT, tF_x, tF_h, tF_y. simpl.
      f_equal. f_equal; apply fld.(cr_add_neg). apply fld.(cr_add_neg).
    - intro u. destruct u as [[a b] c]. unfold la3_scale, mkT, tF_x, tF_h, tF_y. simpl.
      f_equal. f_equal; apply (cr_one_mul fld). apply (cr_one_mul fld).
    - intros a b u. destruct u as [[x1 x2] x3]. unfold la3_scale, mkT, tF_x, tF_h, tF_y. simpl.
      f_equal. f_equal; apply fld.(cr_mul_assoc). apply fld.(cr_mul_assoc).
    - intros a u v. unfold la3_scale, la3_add, mkT, tF_x, tF_h, tF_y. simpl.
      f_equal. f_equal; apply fld.(cr_distrib). apply fld.(cr_distrib).
    - intros a b u. unfold la3_scale, la3_add, mkT, tF_x, tF_h, tF_y. simpl.
      f_equal. f_equal; apply (cr_distrib_r fld). apply (cr_distrib_r fld).
  Defined.

  (** Bracket axioms. Each component requires bilinear/ring-like reasoning
      on the cr_mul/cr_add expressions. We prove only [bracket_alt] here
      because the others (Jacobi etc.) are very long without ring tactic. *)

  (** Bracket alternation: [u, u] = 0. *)
  Lemma la3_bracket_alt : forall u, la3_bracket u u = la3_zero.
  Proof.
    intros [[a b] c].
    unfold la3_bracket, la3_zero, mkT, tF_x, tF_h, tF_y. simpl.
    f_equal. f_equal.
    - (* 2 * (b*a + -(a*b)) = 0 *)
      rewrite (cr_mul_comm fld b a). rewrite (cr_add_neg fld). apply (cr_mul_zero_r fld).
    - (* a*c + -(c*a) = 0 *)
      rewrite (cr_mul_comm fld a c). apply (cr_add_neg fld).
    - (* 2 * (c*b + -(b*c)) = 0 *)
      rewrite (cr_mul_comm fld c b). rewrite (cr_add_neg fld). apply (cr_mul_zero_r fld).
  Qed.

  (** Helper for bilinearity: (x + y) + (z + w) = (x + z) + (y + w) (rearrangement). *)
  Lemma cr_add_4_swap : forall x y z w,
    cr_add fld (cr_add fld x y) (cr_add fld z w) =
    cr_add fld (cr_add fld x z) (cr_add fld y w).
  Proof.
    intros x y z w.
    rewrite (cr_add_assoc fld (cr_add fld x y) z w).
    rewrite <- (cr_add_assoc fld x y z).
    rewrite (cr_add_comm fld y z).
    rewrite (cr_add_assoc fld x z y).
    rewrite <- (cr_add_assoc fld (cr_add fld x z) y w).
    reflexivity.
  Qed.

  (** Common bilinearity step: (b+e)*g + -((a+d)*h) = (b*g + -(a*h)) + (e*g + -(d*h)). *)
  Lemma bilin_add_step : forall a b d e g h,
    cr_add fld (cr_mul fld (cr_add fld b e) g)
              (cr_neg fld (cr_mul fld (cr_add fld a d) h))
    = cr_add fld
        (cr_add fld (cr_mul fld b g) (cr_neg fld (cr_mul fld a h)))
        (cr_add fld (cr_mul fld e g) (cr_neg fld (cr_mul fld d h))).
  Proof.
    intros a b d e g h.
    rewrite (cr_distrib_r fld). (* (b+e)*g = b*g + e*g *)
    rewrite (cr_distrib_r fld). (* (a+d)*h = a*h + d*h *)
    rewrite (cr_neg_add fld). (* -(a*h + d*h) = -(a*h) + -(d*h) *)
    apply cr_add_4_swap.
  Qed.

  (** Bracket-add-l: [u + v, w] = [u, w] + [v, w]. *)
  Lemma la3_bracket_add_l : forall u v w,
    la3_bracket (la3_add u v) w = la3_add (la3_bracket u w) (la3_bracket v w).
  Proof.
    intros [[a b] c] [[d e] f] [[g h] i].
    unfold la3_add, la3_bracket, mkT, tF_x, tF_h, tF_y. simpl.
    f_equal. f_equal.
    - (* 1st: 2 * ((b+e)*g + -((a+d)*h)) = 2*(b*g + -(a*h)) + 2*(e*g + -(d*h)) *)
      rewrite (bilin_add_step a b d e g h).
      apply (cr_distrib fld).
    - (* 2nd: (a+d)*i + -((c+f)*g) = (a*i + -(c*g)) + (d*i + -(f*g)) *)
      apply (bilin_add_step c a f d i g).
    - (* 3rd: 2 * ((c+f)*h + -((b+e)*i)) = 2*(c*h + -(b*i)) + 2*(f*h + -(e*i)) *)
      rewrite (bilin_add_step b c e f h i).
      apply (cr_distrib fld).
  Qed.

  (** Common bilinearity step (right): b*(d+g) + -(a*(e+h)) = (b*d + -(a*e)) + (b*g + -(a*h)). *)
  Lemma bilin_add_step_r : forall b a d g e h,
    cr_add fld (cr_mul fld b (cr_add fld d g))
              (cr_neg fld (cr_mul fld a (cr_add fld e h)))
    = cr_add fld
        (cr_add fld (cr_mul fld b d) (cr_neg fld (cr_mul fld a e)))
        (cr_add fld (cr_mul fld b g) (cr_neg fld (cr_mul fld a h))).
  Proof.
    intros b a d g e h.
    rewrite (cr_distrib fld). (* b*(d+g) = b*d + b*g *)
    rewrite (cr_distrib fld). (* a*(e+h) = a*e + a*h *)
    rewrite (cr_neg_add fld). (* -(a*e + a*h) = -(a*e) + -(a*h) *)
    apply cr_add_4_swap.
  Qed.

  (** Bracket-add-r: [u, v + w] = [u, v] + [u, w]. *)
  Lemma la3_bracket_add_r : forall u v w,
    la3_bracket u (la3_add v w) = la3_add (la3_bracket u v) (la3_bracket u w).
  Proof.
    intros [[a b] c] [[d e] f] [[g h] i].
    unfold la3_add, la3_bracket, mkT, tF_x, tF_h, tF_y. simpl.
    f_equal. f_equal.
    - rewrite (bilin_add_step_r b a d g e h).
      apply (cr_distrib fld).
    - apply (bilin_add_step_r a c f i d g).
    - rewrite (bilin_add_step_r c b e h f i).
      apply (cr_distrib fld).
  Qed.

  (** Helper: scale a bilinear "x*y - z*w" form: (c*x)*y + -((c*z)*w) = c * (x*y + -(z*w)). *)
  Lemma bilin_scale_l_step : forall c a b d e,
    cr_add fld (cr_mul fld (cr_mul fld c a) b)
              (cr_neg fld (cr_mul fld (cr_mul fld c d) e))
    = cr_mul fld c (cr_add fld (cr_mul fld a b) (cr_neg fld (cr_mul fld d e))).
  Proof.
    intros c a b d e.
    rewrite <- (cr_mul_assoc fld c a b). (* (c*a)*b → c*(a*b) *)
    rewrite <- (cr_mul_assoc fld c d e). (* (c*d)*e → c*(d*e) *)
    rewrite <- (cr_neg_mul_r fld). (* -(c*(d*e)) → c*(-(d*e)) *)
    rewrite <- (cr_distrib fld). (* c*(a*b) + c*(-(d*e)) → c*(a*b + -(d*e)) *)
    reflexivity.
  Qed.

  (** Helper: 2 * (c * X) = c * (2 * X). *)
  Lemma two_c_swap : forall c X,
    cr_mul fld (cr_add fld (cr_one fld) (cr_one fld)) (cr_mul fld c X) =
    cr_mul fld c (cr_mul fld (cr_add fld (cr_one fld) (cr_one fld)) X).
  Proof.
    intros c X.
    rewrite (cr_mul_assoc fld). (* 2 * (c*X) → (2*c) * X *)
    rewrite (cr_mul_comm fld _ c). (* (2*c) → (c*2) *)
    rewrite <- (cr_mul_assoc fld). (* (c*2)*X → c*(2*X) *)
    reflexivity.
  Qed.

  (** Bracket-scale-l: [c * u, v] = c * [u, v]. *)
  Lemma la3_bracket_scale_l : forall c u v,
    la3_bracket (la3_scale c u) v = la3_scale c (la3_bracket u v).
  Proof.
    intros c [[a b] c'] [[d e] f].
    unfold la3_scale, la3_bracket, mkT, tF_x, tF_h, tF_y. simpl.
    f_equal. f_equal.
    - (* 1st *) rewrite (bilin_scale_l_step c b d a e). apply two_c_swap.
    - (* 2nd *) apply (bilin_scale_l_step c a f c' d).
    - (* 3rd *) rewrite (bilin_scale_l_step c c' e b f). apply two_c_swap.
  Qed.

  (** Helper: x * (c * y) form. *)
  Lemma bilin_scale_r_step : forall c a b d e,
    cr_add fld (cr_mul fld a (cr_mul fld c b))
              (cr_neg fld (cr_mul fld d (cr_mul fld c e)))
    = cr_mul fld c (cr_add fld (cr_mul fld a b) (cr_neg fld (cr_mul fld d e))).
  Proof.
    intros c a b d e.
    rewrite (cr_mul_assoc fld a c b). (* a*(c*b) → (a*c)*b *)
    rewrite (cr_mul_comm fld a c).    (* (a*c) → c*a *)
    rewrite <- (cr_mul_assoc fld c a b). (* (c*a)*b → c*(a*b) *)
    rewrite (cr_mul_assoc fld d c e).
    rewrite (cr_mul_comm fld d c).
    rewrite <- (cr_mul_assoc fld c d e).
    rewrite <- (cr_neg_mul_r fld c (cr_mul fld d e)).
    rewrite <- (cr_distrib fld).
    reflexivity.
  Qed.

  (** Bracket-scale-r: [u, c * v] = c * [u, v]. *)
  Lemma la3_bracket_scale_r : forall c u v,
    la3_bracket u (la3_scale c v) = la3_scale c (la3_bracket u v).
  Proof.
    intros c [[a b] c'] [[d e] f].
    unfold la3_scale, la3_bracket, mkT, tF_x, tF_h, tF_y. simpl.
    f_equal. f_equal.
    - rewrite (bilin_scale_r_step c b d a e). apply two_c_swap.
    - apply (bilin_scale_r_step c a f c' d).
    - rewrite (bilin_scale_r_step c c' e b f). apply two_c_swap.
  Qed.

  (** Jacobi identity: [[u,v],w] + [[v,w],u] + [[w,u],v] = 0.
      Provable by polynomial identity in the coordinates using the [ring] tactic. *)
  Lemma la3_bracket_jacobi : forall u v w,
    la3_add
      (la3_add (la3_bracket u (la3_bracket v w))
               (la3_bracket v (la3_bracket w u)))
      (la3_bracket w (la3_bracket u v))
    = la3_zero.
  Proof.
    intros [[a1 a2] a3] [[b1 b2] b3] [[c1 c2] c3].
    unfold la3_add, la3_bracket, la3_zero, mkT, tF_x, tF_h, tF_y. simpl.
    f_equal.
    - f_equal; ring.
    - ring.
  Qed.

  (** Construct the Lie algebra. *)
  Definition la3 : LieAlgebraF fld tF.
  Proof.
    refine {|
      laF_vs := la3_vs;
      laF_bracket := la3_bracket;
    |}.
    - apply la3_bracket_add_l.
    - apply la3_bracket_scale_l.
    - apply la3_bracket_add_r.
    - apply la3_bracket_scale_r.
    - apply la3_bracket_alt.
    - apply la3_bracket_jacobi.
  Defined.

  (** Standard sl(2) basis vectors. *)
  Definition la3_x : tF := mkT (cr_one fld) (cr_zero fld) (cr_zero fld).
  Definition la3_h : tF := mkT (cr_zero fld) (cr_one fld) (cr_zero fld).
  Definition la3_y : tF := mkT (cr_zero fld) (cr_zero fld) (cr_one fld).

  (** [x, y] = h. *)
  Lemma la3_bracket_xy : la3_bracket la3_x la3_y = la3_h.
  Proof.
    unfold la3_bracket, la3_x, la3_y, la3_h, mkT, tF_x, tF_h, tF_y. simpl.
    f_equal.
    - f_equal; ring.
    - ring.
  Qed.

  (** [h, x] = 2 * x. *)
  Lemma la3_bracket_hx : la3_bracket la3_h la3_x =
    la3_scale (cr_add fld (cr_one fld) (cr_one fld)) la3_x.
  Proof.
    unfold la3_bracket, la3_h, la3_x, la3_scale, mkT, tF_x, tF_h, tF_y. simpl.
    f_equal.
    - f_equal; ring.
    - ring.
  Qed.

  (** [h, y] = -(2 * y). *)
  Lemma la3_bracket_hy : la3_bracket la3_h la3_y =
    la3_neg (la3_scale (cr_add fld (cr_one fld) (cr_one fld)) la3_y).
  Proof.
    unfold la3_bracket, la3_h, la3_y, la3_neg, la3_scale, mkT, tF_x, tF_h, tF_y. simpl.
    f_equal.
    - f_equal; ring.
    - ring.
  Qed.

  (** la3 is non-abelian: [x, y] = h ≠ 0 (where x = (1,0,0), h = (0,1,0), y = (0,0,1)). *)
  Lemma la3_not_abelian :
    fld.(cr_one) <> fld.(cr_zero) ->
    ~ (forall u v : tF, la3_bracket u v = la3_zero).
  Proof.
    intros Hone Habel.
    pose proof (Habel (mkT (cr_one fld) (cr_zero fld) (cr_zero fld))
                       (mkT (cr_zero fld) (cr_zero fld) (cr_one fld))) as Hcontra.
    unfold la3_bracket, la3_zero, mkT, tF_x, tF_h, tF_y in Hcontra. simpl in Hcontra.
    (* Hcontra has: ((2*(0*0 + -(1*0)), 1*1 + -(0*0)), 2*(0*0 + -(0*1))) = ((0, 0), 0) *)
    apply Hone.
    (* From Hcontra second component: 1*1 + -(0*0) = 0. Conclude 1 = 0. *)
    assert (H2 : (cr_one fld) *F (cr_one fld) +F
                 -F ((cr_zero fld) *F (cr_zero fld)) = (cr_zero fld)).
    { injection Hcontra. intros _ H _. exact H. }
    rewrite (cr_mul_one fld) in H2.
    rewrite (cr_mul_zero_l fld) in H2.
    assert (Hnz : -F (cr_zero fld) = (cr_zero fld)).
    { rewrite <- (cr_add_zero_l fld (-F (cr_zero fld))).
      apply (cr_add_neg fld). }
    rewrite Hnz in H2.
    rewrite (cr_add_zero fld) in H2.
    exact H2.
  Qed.

  (** ad(h) action: [h, (a,b,c)] = (2a, 0, -2c). *)
  Lemma la3_ad_h_action : forall a b c,
    la3_bracket la3_h (mkT a b c) =
    mkT ((cr_one fld +F cr_one fld) *F a)
        (cr_zero fld)
        (-F ((cr_one fld +F cr_one fld) *F c)).
  Proof.
    intros a b c.
    unfold la3_bracket, la3_h, mkT, tF_x, tF_h, tF_y. simpl.
    f_equal.
    - f_equal; ring.
    - ring.
  Qed.

  (** ad(h)^2 action: [h, [h, (a,b,c)]] = (4a, 0, 4c). *)
  Lemma la3_ad_h_sq_action : forall a b c,
    la3_bracket la3_h (la3_bracket la3_h (mkT a b c)) =
    mkT (((cr_one fld +F cr_one fld) *F (cr_one fld +F cr_one fld)) *F a)
        (cr_zero fld)
        (((cr_one fld +F cr_one fld) *F (cr_one fld +F cr_one fld)) *F c).
  Proof.
    intros a b c.
    unfold la3_bracket, la3_h, mkT, tF_x, tF_h, tF_y. simpl.
    f_equal.
    - f_equal; ring.
    - ring.
  Qed.

  (** Helper: 8 = (1+1)*(1+1)*(1+1) but more useful is just (1+1)^2 = 4 in any commring. *)
  Definition la3_two : F := cr_one fld +F cr_one fld.

  (** Combination: 1/2 * (ad(h)^2 + 2*ad(h)) extracts pure x-component scaled by 4. *)
  (** Specifically: ad(h)^2 z + 2 * ad(h) z = (4a + 4a, 0, 4c + (-4c)) = (8a, 0, 0). *)
  Lemma la3_extract_x : forall a b c,
    la3_add (la3_bracket la3_h (la3_bracket la3_h (mkT a b c)))
            (la3_scale la3_two (la3_bracket la3_h (mkT a b c))) =
    mkT (la3_two *F la3_two *F a +F la3_two *F (la3_two *F a))
        (cr_zero fld)
        (cr_zero fld).
  Proof.
    intros a b c.
    unfold la3_add, la3_scale, la3_bracket, la3_h, mkT, tF_x, tF_h, tF_y, la3_two. simpl.
    f_equal.
    - f_equal; ring.
    - ring.
  Qed.

  (** Similarly: ad(h)^2 z - 2 * ad(h) z = (0, 0, 8c). *)
  Lemma la3_extract_y : forall a b c,
    la3_add (la3_bracket la3_h (la3_bracket la3_h (mkT a b c)))
            (la3_neg (la3_scale la3_two (la3_bracket la3_h (mkT a b c)))) =
    mkT (cr_zero fld)
        (cr_zero fld)
        (la3_two *F la3_two *F c +F la3_two *F (la3_two *F c)).
  Proof.
    intros a b c.
    unfold la3_add, la3_scale, la3_neg, la3_bracket, la3_h, mkT,
           tF_x, tF_h, tF_y, la3_two. simpl.
    f_equal.
    - f_equal; ring.
    - ring.
  Qed.

  (** Helper: in any field, 8 = (1+1)*(1+1)*(1+1). *)
  Definition la3_eight : F := la3_two *F la3_two *F la3_two.

  (** la3_extract_x simplified: [(h, [h, z]) + 2*[h, z]] equals (8a, 0, 0). *)
  Lemma la3_extract_x_eq : forall a b c,
    la3_add (la3_bracket la3_h (la3_bracket la3_h (mkT a b c)))
            (la3_scale la3_two (la3_bracket la3_h (mkT a b c))) =
    mkT (la3_eight *F a) (cr_zero fld) (cr_zero fld).
  Proof.
    intros a b c. rewrite la3_extract_x.
    unfold la3_eight, la3_two, mkT.
    f_equal. f_equal. ring.
  Qed.

  Lemma la3_extract_y_eq : forall a b c,
    la3_add (la3_bracket la3_h (la3_bracket la3_h (mkT a b c)))
            (la3_neg (la3_scale la3_two (la3_bracket la3_h (mkT a b c)))) =
    mkT (cr_zero fld) (cr_zero fld) (la3_eight *F c).
  Proof.
    intros a b c. rewrite la3_extract_y.
    unfold la3_eight, la3_two, mkT.
    f_equal. ring.
  Qed.

  (** From an ideal I containing z = (a, b, c), derive that (8a*x, 0, 0) ∈ I. *)
  Lemma la3_ideal_pivot_x : forall (I : tF -> Prop),
    IsIdeal la3 I -> forall a b c,
    I (mkT a b c) -> I (mkT (la3_eight *F a) (cr_zero fld) (cr_zero fld)).
  Proof.
    intros I HI a b c Hz.
    rewrite <- (la3_extract_x_eq a b c).
    apply HI.(ideal_add).
    - apply HI.(ideal_bracket_l).
      apply HI.(ideal_bracket_l).
      exact Hz.
    - apply HI.(ideal_scale).
      apply HI.(ideal_bracket_l).
      exact Hz.
  Qed.

  (** From an ideal I containing z = (a, b, c), derive that (0, 0, 8c*y) ∈ I. *)
  Lemma la3_ideal_pivot_y : forall (I : tF -> Prop),
    IsIdeal la3 I -> forall a b c,
    I (mkT a b c) -> I (mkT (cr_zero fld) (cr_zero fld) (la3_eight *F c)).
  Proof.
    intros I HI a b c Hz.
    rewrite <- (la3_extract_y_eq a b c).
    apply HI.(ideal_add).
    - apply HI.(ideal_bracket_l).
      apply HI.(ideal_bracket_l).
      exact Hz.
    - apply HI.(ideal_neg).
      apply HI.(ideal_scale).
      apply HI.(ideal_bracket_l).
      exact Hz.
  Qed.

  (** la3_x = scale (1/8a) (8a, 0, 0) when 8a ≠ 0 (so when a ≠ 0 and char ≠ 2). *)
  Lemma la3_recover_x : forall a, a <> cr_zero fld ->
    la3_eight <> cr_zero fld ->
    la3_x = la3_scale (fld_inv fld (la3_eight *F a))
                      (mkT (la3_eight *F a) (cr_zero fld) (cr_zero fld)).
  Proof.
    intros a Ha Height.
    assert (Hprod : la3_eight *F a <> cr_zero fld).
    { intro Hp. apply Ha.
      destruct (field_no_zero_div fld _ _ Hp); [contradiction|exact H]. }
    unfold la3_x, la3_scale, mkT, tF_x, tF_h, tF_y. simpl.
    assert (Hinv := fld.(fld_inv_mul) (la3_eight *F a) Hprod).
    f_equal.
    f_equal.
    - symmetry. rewrite (cr_mul_comm fld _ (la3_eight *F a)). exact Hinv.
    - symmetry. apply (cr_mul_zero_r fld).
    - symmetry. apply (cr_mul_zero_r fld).
  Qed.

  (** la3_y = scale (1/8c) (0, 0, 8c) when 8c ≠ 0. *)
  Lemma la3_recover_y : forall c, c <> cr_zero fld ->
    la3_eight <> cr_zero fld ->
    la3_y = la3_scale (fld_inv fld (la3_eight *F c))
                      (mkT (cr_zero fld) (cr_zero fld) (la3_eight *F c)).
  Proof.
    intros c Hc Height.
    assert (Hprod : la3_eight *F c <> cr_zero fld).
    { intro Hp. apply Hc.
      destruct (field_no_zero_div fld _ _ Hp); [contradiction|exact H]. }
    unfold la3_y, la3_scale, mkT, tF_x, tF_h, tF_y. simpl.
    assert (Hinv := fld.(fld_inv_mul) (la3_eight *F c) Hprod).
    f_equal.
    f_equal.
    - symmetry. apply (cr_mul_zero_r fld).
    - symmetry. apply (cr_mul_zero_r fld).
    - symmetry. rewrite (cr_mul_comm fld _ (la3_eight *F c)). exact Hinv.
  Qed.

  (** Once x ∈ I, h ∈ I (using bracket [y, x] = -h, anticomm, and ideal_neg). *)
  Lemma la3_ideal_x_implies_h : forall (I : tF -> Prop),
    IsIdeal la3 I -> I la3_x -> I la3_h.
  Proof.
    intros I HI Hx.
    (* [la3_y, la3_x] = -[la3_x, la3_y] = -h. Since x ∈ I, [la3_y, la3_x] ∈ I. *)
    pose proof (HI.(ideal_bracket_l) la3_y la3_x Hx) as H1.
    simpl in H1.
    assert (Hyx : la3_bracket la3_y la3_x = la3_neg la3_h).
    { unfold la3_bracket, la3_y, la3_x, la3_h, la3_neg, mkT, tF_x, tF_h, tF_y.
      simpl. f_equal. - f_equal; ring. - ring. }
    rewrite Hyx in H1.
    pose proof (HI.(ideal_neg) (la3_neg la3_h) H1) as H2.
    simpl in H2.
    assert (Hnn : la3_neg (la3_neg la3_h) = la3_h).
    { unfold la3_neg, la3_h, mkT, tF_x, tF_h, tF_y. simpl.
      f_equal. - f_equal; ring. - ring. }
    rewrite Hnn in H2.
    exact H2.
  Qed.

  (** Once y ∈ I, h ∈ I. *)
  Lemma la3_ideal_y_implies_h : forall (I : tF -> Prop),
    IsIdeal la3 I -> I la3_y -> I la3_h.
  Proof.
    intros I HI Hy.
    pose proof (HI.(ideal_bracket_l) la3_x la3_y Hy) as H1.
    simpl in H1.
    rewrite la3_bracket_xy in H1. exact H1.
  Qed.

  (** Once h ∈ I, given char ≠ 2, x ∈ I.
      [x, h] = -2x, ideal closure + ideal_neg gives 2x ∈ I, then scale 1/2. *)
  Lemma la3_ideal_h_implies_x : forall (I : tF -> Prop),
    IsIdeal la3 I -> la3_two <> cr_zero fld -> I la3_h -> I la3_x.
  Proof.
    intros I HI Hchar Hh.
    (* [la3_x, la3_h] = la3_neg (la3_scale 2 la3_x). *)
    pose proof (HI.(ideal_bracket_l) la3_x la3_h Hh) as H1.
    simpl in H1.
    assert (Hxh : la3_bracket la3_x la3_h = la3_neg (la3_scale la3_two la3_x)).
    { unfold la3_bracket, la3_x, la3_h, la3_neg, la3_scale, la3_two,
             mkT, tF_x, tF_h, tF_y. simpl.
      f_equal. - f_equal; ring. - ring. }
    rewrite Hxh in H1.
    pose proof (HI.(ideal_neg) (la3_neg (la3_scale la3_two la3_x)) H1) as H2.
    simpl in H2.
    assert (Hnn : la3_neg (la3_neg (la3_scale la3_two la3_x)) = la3_scale la3_two la3_x).
    { unfold la3_neg, la3_scale, la3_x, la3_two, mkT, tF_x, tF_h, tF_y. simpl.
      f_equal. - f_equal; ring. - ring. }
    rewrite Hnn in H2.
    (* Now H2 : I (la3_scale la3_two la3_x). Scale by 1/la3_two to get la3_x. *)
    pose proof (HI.(ideal_scale) (fld_inv fld la3_two) (la3_scale la3_two la3_x) H2) as H3.
    simpl in H3.
    (* Need: la3_scale (1/2) (la3_scale 2 la3_x) = la3_x. *)
    assert (Hrec : la3_scale (fld_inv fld la3_two) (la3_scale la3_two la3_x) = la3_x).
    { unfold la3_scale, la3_x, mkT, tF_x, tF_h, tF_y. simpl.
      pose proof (fld.(fld_inv_mul) la3_two Hchar) as Hinv.
      f_equal.
      - f_equal.
        + rewrite (cr_mul_one fld).
          rewrite (cr_mul_comm fld _ la3_two). exact Hinv.
        + rewrite (cr_mul_zero_r fld). apply (cr_mul_zero_r fld).
      - rewrite (cr_mul_zero_r fld). apply (cr_mul_zero_r fld). }
    rewrite Hrec in H3. exact H3.
  Qed.

  (** From z = (a,b,c) ∈ I with a ≠ 0 and la3_eight ≠ 0: la3_x ∈ I. *)
  Lemma la3_ideal_a_nonzero_implies_x : forall (I : tF -> Prop),
    IsIdeal la3 I -> la3_eight <> cr_zero fld ->
    forall a b c, a <> cr_zero fld ->
    I (mkT a b c) -> I la3_x.
  Proof.
    intros I HI Height a b c Ha Hz.
    pose proof (la3_ideal_pivot_x I HI a b c Hz) as Hpivot.
    rewrite (la3_recover_x a Ha Height).
    apply HI.(ideal_scale). exact Hpivot.
  Qed.

  (** From z = (a,b,c) ∈ I with c ≠ 0 and la3_eight ≠ 0: la3_y ∈ I. *)
  Lemma la3_ideal_c_nonzero_implies_y : forall (I : tF -> Prop),
    IsIdeal la3 I -> la3_eight <> cr_zero fld ->
    forall a b c, c <> cr_zero fld ->
    I (mkT a b c) -> I la3_y.
  Proof.
    intros I HI Height a b c Hc Hz.
    pose proof (la3_ideal_pivot_y I HI a b c Hz) as Hpivot.
    rewrite (la3_recover_y c Hc Height).
    apply HI.(ideal_scale). exact Hpivot.
  Qed.

  (** la3_eight ≠ 0 follows from la3_two ≠ 0 (char ≠ 2). *)
  Lemma la3_eight_nonzero : la3_two <> cr_zero fld -> la3_eight <> cr_zero fld.
  Proof.
    intros Htwo H8.
    unfold la3_eight in H8.
    (* H8: la3_two * la3_two * la3_two = 0 *)
    (* In a field with no zero divisors: la3_two = 0. Contradicts Htwo. *)
    apply Htwo.
    destruct (field_no_zero_div fld _ _ H8) as [Hsq | Hone].
    - destruct (field_no_zero_div fld _ _ Hsq); assumption.
    - exact Hone.
  Qed.

  (** From z = (0,b,0) ∈ I with b ≠ 0: la3_h ∈ I. *)
  Lemma la3_ideal_b_nonzero_implies_h : forall (I : tF -> Prop),
    IsIdeal la3 I -> forall b, b <> cr_zero fld ->
    I (mkT (cr_zero fld) b (cr_zero fld)) -> I la3_h.
  Proof.
    intros I HI b Hb Hz.
    pose proof (HI.(ideal_scale) (fld_inv fld b)
                  (mkT (cr_zero fld) b (cr_zero fld)) Hz) as H1.
    simpl in H1.
    assert (Hrec : la3_scale (fld_inv fld b)
                             (mkT (cr_zero fld) b (cr_zero fld)) = la3_h).
    { unfold la3_scale, la3_h, mkT, tF_x, tF_h, tF_y. simpl.
      pose proof (fld.(fld_inv_mul) b Hb) as Hinv.
      f_equal.
      - f_equal.
        + apply (cr_mul_zero_r fld).
        + rewrite (cr_mul_comm fld _ b). exact Hinv.
      - apply (cr_mul_zero_r fld). }
    rewrite Hrec in H1. exact H1.
  Qed.

  (** Helper: from x, h, y ∈ I, any element of la3 is in I. *)
  Lemma la3_ideal_basis_implies_full : forall (I : tF -> Prop),
    IsIdeal la3 I -> I la3_x -> I la3_h -> I la3_y ->
    forall z, I z.
  Proof.
    intros I HI Hx Hh Hy z.
    destruct z as [[a b] c].
    (* z = a*x + b*h + c*y *)
    assert (Heq : mkT a b c = la3_add (la3_scale a la3_x)
                              (la3_add (la3_scale b la3_h) (la3_scale c la3_y))).
    { unfold la3_add, la3_scale, la3_x, la3_h, la3_y, mkT, tF_x, tF_h, tF_y.
      simpl. f_equal. - f_equal; ring. - ring. }
    unfold mkT in Heq. rewrite Heq.
    apply HI.(ideal_add).
    - apply HI.(ideal_scale). exact Hx.
    - apply HI.(ideal_add).
      + apply HI.(ideal_scale). exact Hh.
      + apply HI.(ideal_scale). exact Hy.
  Qed.

  (** Once h ∈ I, given char ≠ 2, y ∈ I. *)
  Lemma la3_ideal_h_implies_y : forall (I : tF -> Prop),
    IsIdeal la3 I -> la3_two <> cr_zero fld -> I la3_h -> I la3_y.
  Proof.
    intros I HI Hchar Hh.
    pose proof (HI.(ideal_bracket_l) la3_y la3_h Hh) as H1.
    simpl in H1.
    (* [y, h] = -[h, y] = 2y *)
    assert (Hyh : la3_bracket la3_y la3_h = la3_scale la3_two la3_y).
    { unfold la3_bracket, la3_y, la3_h, la3_scale, la3_two,
             mkT, tF_x, tF_h, tF_y. simpl.
      f_equal. - f_equal; ring. - ring. }
    rewrite Hyh in H1.
    pose proof (HI.(ideal_scale) (fld_inv fld la3_two) (la3_scale la3_two la3_y) H1) as H3.
    simpl in H3.
    assert (Hrec : la3_scale (fld_inv fld la3_two) (la3_scale la3_two la3_y) = la3_y).
    { unfold la3_scale, la3_y, mkT, tF_x, tF_h, tF_y. simpl.
      pose proof (fld.(fld_inv_mul) la3_two Hchar) as Hinv.
      f_equal.
      - f_equal.
        + rewrite (cr_mul_zero_r fld). apply (cr_mul_zero_r fld).
        + rewrite (cr_mul_zero_r fld). apply (cr_mul_zero_r fld).
      - rewrite (cr_mul_one fld).
        rewrite (cr_mul_comm fld _ la3_two). exact Hinv. }
    rewrite Hrec in H3. exact H3.
  Qed.

  (** ** Main theorem: sl(2,F) is simple when char F ≠ 2 *)

  (** This is Humphreys §4.3 (Theorem 4.3) for the explicit triple model.
      The proof structure: take any non-zero ideal I and a witness
      [z = (a,b,c)] in I that is not zero. By case analysis on which of
      [a, b, c] is non-zero, derive one of [la3_x, la3_h, la3_y] in I,
      then use bracket relations to derive the other two, then
      [la3_ideal_basis_implies_full] to conclude I = la3. *)
  Theorem la3_simple : la3_two <> cr_zero fld -> IsSimple la3.
  Proof.
    intros Hchar.
    pose proof (la3_eight_nonzero Hchar) as Height.
    pose proof (fld.(fld_nontrivial)) as Hzo. (* cr_zero <> cr_one *)
    assert (Hone : cr_one fld <> cr_zero fld) by (intro H; apply Hzo; symmetry; exact H).
    split.
    - (* For every ideal I: trivial or full *)
      intros I HI.
      destruct (classic (forall x, I x -> x = la_zero la3)) as [Htriv | Hntriv].
      + left. exact Htriv.
      + right.
        apply not_all_ex_not in Hntriv.
        destruct Hntriv as [z Hz].
        apply imply_to_and in Hz.
        destruct Hz as [HzI Hznz].
        destruct z as [[a b] c].
        (* z = (a, b, c) is in I and ≠ 0 *)
        assert (HzNotZero : ~ (a = cr_zero fld /\ b = cr_zero fld /\ c = cr_zero fld)).
        { intros [Ha [Hb Hc]]. apply Hznz.
          unfold la_zero, la3_zero, mkT. simpl.
          rewrite Ha, Hb, Hc. reflexivity. }
        change ((a, b, c)) with (mkT a b c) in HzI.
        destruct (classic (a = cr_zero fld)) as [Ha | Hane].
        * destruct (classic (c = cr_zero fld)) as [Hc | Hcne].
          -- (* a = 0, c = 0, so b ≠ 0 *)
             assert (Hbne : b <> cr_zero fld).
             { intro Hb. apply HzNotZero. split; [|split]; assumption. }
             rewrite Ha, Hc in HzI.
             pose proof (la3_ideal_b_nonzero_implies_h I HI b Hbne HzI) as Hh.
             pose proof (la3_ideal_h_implies_x I HI Hchar Hh) as Hx.
             pose proof (la3_ideal_h_implies_y I HI Hchar Hh) as Hy.
             apply (la3_ideal_basis_implies_full I HI Hx Hh Hy).
          -- (* c ≠ 0: derive y, h, x *)
             pose proof (la3_ideal_c_nonzero_implies_y I HI Height a b c Hcne HzI) as Hy.
             pose proof (la3_ideal_y_implies_h I HI Hy) as Hh.
             pose proof (la3_ideal_h_implies_x I HI Hchar Hh) as Hx.
             apply (la3_ideal_basis_implies_full I HI Hx Hh Hy).
        * (* a ≠ 0: derive x, h, y *)
          pose proof (la3_ideal_a_nonzero_implies_x I HI Height a b c Hane HzI) as Hx.
          pose proof (la3_ideal_x_implies_h I HI Hx) as Hh.
          pose proof (la3_ideal_h_implies_y I HI Hchar Hh) as Hy.
          apply (la3_ideal_basis_implies_full I HI Hx Hh Hy).
    - (* la3 has non-trivial bracket *)
      apply la3_not_abelian. exact Hone.
  Qed.

  (** ** Corollaries of la3 simplicity *)

  (** Center of sl(2) is trivial. *)
  Corollary la3_center_trivial : la3_two <> cr_zero fld ->
    forall z, IsCenter la3 z -> z = la_zero la3.
  Proof.
    intros Hchar z Hz.
    apply (simple_center_zero la3 (la3_simple Hchar) z Hz).
  Qed.

  (** Derived algebra of sl(2) is all of sl(2). *)
  Corollary la3_derived_full : la3_two <> cr_zero fld ->
    forall z, IsDerivedAlg la3 z.
  Proof.
    intros Hchar z.
    apply (simple_derived_full la3 (la3_simple Hchar) z).
  Qed.

  (** sl(2,F) is not solvable. *)
  Corollary la3_not_solvable : la3_two <> cr_zero fld ->
    ~ IsSolvable la3.
  Proof.
    intros Hchar.
    exact (simple_not_solvable la3 (la3_simple Hchar)).
  Qed.

  (** sl(2,F) is not nilpotent (simple Lie algebras never are). *)
  Corollary la3_not_nilpotent : la3_two <> cr_zero fld ->
    ~ IsNilpotent la3.
  Proof.
    intros Hchar.
    exact (simple_not_nilpotent la3 (la3_simple Hchar)).
  Qed.

  (** sl(2,F) is semisimple. *)
  Corollary la3_semisimple : la3_two <> cr_zero fld ->
    IsSemisimple la3.
  Proof.
    intros Hchar.
    exact (simple_is_semisimple la3 (la3_simple Hchar)).
  Qed.

  (** ad : la3 → End(la3) is injective (kernel = center = 0). *)
  Corollary la3_ad_injective : la3_two <> cr_zero fld ->
    forall x : tF, (forall y, ad la3 x y = la_zero la3) -> x = la_zero la3.
  Proof.
    intros Hchar.
    exact (simple_ad_injective la3 (la3_simple Hchar)).
  Qed.

  (** la3_x is non-zero (when 1 ≠ 0). *)
  Lemma la3_x_nonzero : cr_one fld <> cr_zero fld -> la3_x <> la3_zero.
  Proof.
    intros Hone Heq.
    apply Hone.
    unfold la3_x, la3_zero, mkT in Heq.
    exact (f_equal (fun p => fst (fst p)) Heq).
  Qed.

  (** la3_h is non-zero. *)
  Lemma la3_h_nonzero : cr_one fld <> cr_zero fld -> la3_h <> la3_zero.
  Proof.
    intros Hone Heq.
    apply Hone.
    unfold la3_h, la3_zero, mkT in Heq.
    exact (f_equal (fun p => snd (fst p)) Heq).
  Qed.

  (** la3_y is non-zero. *)
  Lemma la3_y_nonzero : cr_one fld <> cr_zero fld -> la3_y <> la3_zero.
  Proof.
    intros Hone Heq.
    apply Hone.
    unfold la3_y, la3_zero, mkT in Heq.
    exact (f_equal snd Heq).
  Qed.

  (** Basis vectors are pairwise distinct (when 1 ≠ 0). *)
  Lemma la3_x_neq_h : cr_one fld <> cr_zero fld -> la3_x <> la3_h.
  Proof.
    intros Hone Heq.
    apply Hone.
    unfold la3_x, la3_h, mkT in Heq.
    exact (f_equal (fun p => fst (fst p)) Heq).
  Qed.

  Lemma la3_h_neq_y : cr_one fld <> cr_zero fld -> la3_h <> la3_y.
  Proof.
    intros Hone Heq.
    apply Hone.
    unfold la3_h, la3_y, mkT in Heq.
    exact (f_equal (fun p => snd (fst p)) Heq).
  Qed.

  Lemma la3_x_neq_y : cr_one fld <> cr_zero fld -> la3_x <> la3_y.
  Proof.
    intros Hone Heq.
    apply Hone.
    unfold la3_x, la3_y, mkT in Heq.
    exact (f_equal (fun p => fst (fst p)) Heq).
  Qed.

  (** [y, x] = -h (by anticommutativity of la3_bracket_xy). *)
  Lemma la3_bracket_yx : la3_bracket la3_y la3_x = la3_neg la3_h.
  Proof.
    unfold la3_bracket, la3_y, la3_x, la3_h, la3_neg, mkT, tF_x, tF_h, tF_y. simpl.
    f_equal. - f_equal; ring. - ring.
  Qed.

  (** [x, h] = -(2*x) (by anticommutativity of la3_bracket_hx). *)
  Lemma la3_bracket_xh : la3_bracket la3_x la3_h =
    la3_neg (la3_scale (cr_add fld (cr_one fld) (cr_one fld)) la3_x).
  Proof.
    unfold la3_bracket, la3_x, la3_h, la3_neg, la3_scale, mkT, tF_x, tF_h, tF_y. simpl.
    f_equal. - f_equal; ring. - ring.
  Qed.

  (** [y, h] = 2*y. *)
  Lemma la3_bracket_yh : la3_bracket la3_y la3_h =
    la3_scale (cr_add fld (cr_one fld) (cr_one fld)) la3_y.
  Proof.
    unfold la3_bracket, la3_y, la3_h, la3_scale, mkT, tF_x, tF_h, tF_y. simpl.
    f_equal. - f_equal; ring. - ring.
  Qed.

  (** la3_x is ad-nilpotent: (ad la3_x)^3 = 0 on all of la3. Standard
      sl(2,F) fact: x has weight +2 on h-eigenspaces, three iterations
      drive any element to zero. *)
  Theorem la3_x_ad_nilpotent : IsAdNilpotent la3 la3_x.
  Proof.
    exists 3. intros [[a b] c]. simpl.
    unfold la3_bracket, la3_x, la_zero, la3, ex2_vs, mkT, tF_x, tF_h, tF_y.
    simpl.
    apply (f_equal2 (@pair _ _)); [apply (f_equal2 (@pair _ _))|]; ring.
  Qed.

  (** la3_y is ad-nilpotent: (ad la3_y)^3 = 0 on all of la3. Symmetric
      to la3_x. *)
  Theorem la3_y_ad_nilpotent : IsAdNilpotent la3 la3_y.
  Proof.
    exists 3. intros [[a b] c]. simpl.
    unfold la3_bracket, la3_y, la_zero, la3, ex2_vs, mkT, tF_x, tF_h, tF_y.
    simpl.
    apply (f_equal2 (@pair _ _)); [apply (f_equal2 (@pair _ _))|]; ring.
  Qed.

  (** (ad h)^N applied to x gives (s, 0, 0) for some s ≠ 0. *)
  Lemma la3_iter_h_x_nonzero :
      cr_one fld <> cr_zero fld ->
      la3_two <> cr_zero fld ->
      forall N, exists s : F,
        s <> cr_zero fld /\
        Nat.iter N (laF_bracket la3 la3_h) la3_x = mkT s (cr_zero fld) (cr_zero fld).
  Proof.
    intros Hone Htwo N. induction N as [|N IH].
    - exists (cr_one fld). split; [exact Hone|reflexivity].
    - destruct IH as [s [Hs Heq]].
      replace (Nat.iter (S N) (laF_bracket la3 la3_h) la3_x)
         with (laF_bracket la3 la3_h
               (Nat.iter N (laF_bracket la3 la3_h) la3_x))
         by reflexivity.
      rewrite Heq.
      exists (la3_two *F s). split.
      + intro Hcontra.
        destruct (field_no_zero_div fld la3_two s Hcontra) as [H1 | H1];
          [exact (Htwo H1) | exact (Hs H1)].
      + unfold laF_bracket, la3, la3_bracket, la3_h, mkT, tF_x, tF_h, tF_y, la3_two.
        simpl. apply (f_equal2 (@pair _ _)); [apply (f_equal2 (@pair _ _))|]; ring.
  Qed.

  (** la3_h is NOT ad-nilpotent (when char ≠ 2): brackets with x grow as 2^N. *)
  Theorem la3_h_not_ad_nilpotent :
      cr_one fld <> cr_zero fld ->
      la3_two <> cr_zero fld ->
      ~ IsAdNilpotent la3 la3_h.
  Proof.
    intros Hone Htwo [N HN].
    specialize (HN la3_x).
    destruct (la3_iter_h_x_nonzero Hone Htwo N) as [s [Hs Heq]].
    rewrite Heq in HN.
    apply Hs.
    unfold la_zero, la3, ex2_vs, mkT in HN. simpl in HN.
    exact (f_equal (fun p => fst (fst p)) HN).
  Qed.

End Sl2On3D.

(** ** The 2D nonabelian Lie algebra is solvable

    Standard graduate-level fact: nonabelian_2d (with bracket [x,y] = x)
    has [L,L] = span(x) (1-dimensional), and [[L,L],[L,L]] = 0.
    Hence the derived series terminates at level 2. *)

(** Helper: every element of derived_series 1 has zero second coordinate. *)
Lemma nonabelian_2d_derived_1_snd_zero {F : Type} (fld : Field F) :
    forall a, derived_series (nonabelian_2d fld) 1 a -> snd a = cr_zero fld.
Proof.
  intros a Ha. simpl in Ha.
  set (U := fun z : F * F => snd z = cr_zero fld).
  assert (HU : IsIdeal (nonabelian_2d fld) U).
  { constructor; unfold U.
    - simpl. reflexivity.
    - intros x y Hx Hy. simpl. rewrite Hx, Hy. apply (cr_add_zero fld).
    - intros x Hx. simpl. rewrite Hx. apply cr_neg_zero'.
    - intros c x Hx. simpl. rewrite Hx. apply (cr_mul_zero_r fld).
    - intros x y _. simpl. reflexivity. }
  apply (Ha U HU). intros x y _ _. unfold U. simpl. reflexivity.
Qed.

(** Helper: the element (1, 0) is in the n-th lower central series term
    for every n. Hence the lower central series of nonabelian_2d never
    reaches 0 — so nonabelian_2d is not nilpotent. *)
Lemma nonabelian_2d_lower_central_x {F : Type} (fld : Field F) :
    forall n, lower_central (nonabelian_2d fld) n
                            (cr_one fld, cr_zero fld).
Proof.
  intros n. induction n as [| n IHn].
  - simpl. exact I.
  - simpl. intros U HU HB.
    (* Apply HB at x = (0, 1), y = (1, 0). y ∈ L_n by IHn. *)
    pose proof (HB (cr_zero fld, cr_one fld) (cr_one fld, cr_zero fld) I IHn) as Hxy.
    (* [x, y] = (0*0 - 1*1, 0) = (-1, 0). Then -[x, y] = (1, 0). *)
    pose proof (HU.(ideal_neg) _ Hxy) as Hneg.
    (* Show la_neg [x, y] = (1, 0). *)
    assert (Heq : la_neg (nonabelian_2d fld)
                    (laF_bracket (nonabelian_2d fld)
                       (cr_zero fld, cr_one fld) (cr_one fld, cr_zero fld))
                  = (cr_one fld, cr_zero fld)).
    { unfold la_neg, laF_bracket, nonabelian_2d, nonabelian_2d_bracket,
             nonabelian_2d_vs. simpl.
      f_equal.
      - rewrite cr_mul_zero_l', (fld.(cr_mul_one)), cr_add_zero_l'.
        apply cr_neg_neg'.
      - apply cr_neg_zero'. }
    rewrite <- Heq. exact Hneg.
Qed.

(** The 2D nonabelian Lie algebra is NOT nilpotent. *)
Theorem nonabelian_2d_not_nilpotent {F : Type} (fld : Field F) :
    ~ IsNilpotent (nonabelian_2d fld).
Proof.
  intros [n Hn].
  pose proof (Hn (cr_one fld, cr_zero fld)
              (nonabelian_2d_lower_central_x fld n)) as Hcontra.
  (* Hcontra : (1, 0) = la_zero = (0, 0). Extract first component. *)
  apply (fld.(fld_nontrivial)).
  symmetry. exact (f_equal fst Hcontra).
Qed.

(** The 2D nonabelian Lie algebra is solvable (with derived length 2). *)
Theorem nonabelian_2d_solvable {F : Type} (fld : Field F) :
    IsSolvable (nonabelian_2d fld).
Proof.
  exists 2. intros x Hx. simpl in Hx.
  apply (Hx (fun z => z = la_zero (nonabelian_2d fld))).
  - apply zero_ideal.
  - intros a b Ha Hb.
    pose proof (nonabelian_2d_derived_1_snd_zero fld a Ha) as Has.
    pose proof (nonabelian_2d_derived_1_snd_zero fld b Hb) as Hbs.
    destruct a as [a1 a2], b as [b1 b2]. simpl in Has, Hbs.
    subst a2. subst b2.
    unfold laF_bracket, nonabelian_2d, nonabelian_2d_bracket, la_zero. simpl.
    f_equal.
    rewrite (cr_mul_zero_r fld a1).
    rewrite cr_mul_zero_l'.
    rewrite cr_neg_zero'.
    apply (cr_add_zero fld).
Qed.

(** The 2D nonabelian Lie algebra is NOT simple (it's solvable). *)
Corollary nonabelian_2d_not_simple {F : Type} (fld : Field F) :
    ~ IsSimple (nonabelian_2d fld).
Proof.
  intro Hsimp.
  exact (simple_not_solvable (nonabelian_2d fld) Hsimp (nonabelian_2d_solvable fld)).
Qed.

(** nonabelian_2d is NOT perfect: the element (0, 1) is not in the
    derived algebra (since every bracket lands in {(x, 0)}). *)
Lemma nonabelian_2d_not_perfect {F : Type} (fld : Field F) :
    cr_one fld <> cr_zero fld ->
    ~ IsDerivedAlg (nonabelian_2d fld) (cr_zero fld, cr_one fld).
Proof.
  intros Hone HD.
  set (S := fun z : F * F => snd z = cr_zero fld).
  assert (HSsub : IsSubalgebra (nonabelian_2d fld) S).
  { constructor; unfold S.
    - reflexivity.
    - intros u v Hu Hv. simpl. rewrite Hu, Hv. apply (cr_add_zero fld).
    - intros u Hu. simpl. rewrite Hu. apply cr_neg_zero'.
    - intros c u Hu. simpl. rewrite Hu. apply (cr_mul_zero_r fld).
    - intros u v _ _. simpl. reflexivity. }
  assert (HSbr : forall x y, S (laF_bracket (nonabelian_2d fld) x y))
    by (intros x y; reflexivity).
  pose proof (HD S HSsub HSbr) as Hcontra.
  unfold S in Hcontra. simpl in Hcontra.
  apply Hone. exact Hcontra.
Qed.

(** ** Exercise 4: Linear realization of the 2D nonabelian algebra *)

(** The center of nonabelian_2d is trivial. *)
Lemma nonabelian_2d_center_zero {F : Type} (fld : Field F) (v : F * F) :
    IsCenter (nonabelian_2d fld) v -> v = la_zero (nonabelian_2d fld).
Proof.
  intro H.
  destruct v as [c d].
  (* Use [(1,0), (c,d)] = 0 *)
  assert (H1 := H (fld.(cr_one), fld.(cr_zero))).
  (* Use [(0,1), (c,d)] = 0 *)
  assert (H2 := H (fld.(cr_zero), fld.(cr_one))).
  unfold laF_bracket, nonabelian_2d, nonabelian_2d_bracket in H1, H2.
  unfold la_zero, nonabelian_2d. simpl in *.
  (* H1: (1*d + -(0*c), 0) = (0, 0); 1*d = d by comm+mul_one, 0*c = 0 by mul_zero_l *)
  rewrite (fld.(cr_mul_comm) (fld.(cr_one)) d), fld.(cr_mul_one),
          cr_mul_zero_l', cr_neg_zero', fld.(cr_add_zero) in H1.
  (* H1: (d, 0) = (0, 0); extract d = 0 *)
  assert (Hd : d = fld.(cr_zero)) by exact (f_equal fst H1).
  (* H2: (0*d + -(1*c), 0) = (0, 0); 0*d = 0 by mul_zero_l, 1*c = c by comm+mul_one *)
  rewrite cr_mul_zero_l', (fld.(cr_mul_comm) (fld.(cr_one)) c),
          fld.(cr_mul_one), cr_add_zero_l' in H2.
  (* H2: (-(c), 0) = (0, 0); extract -c = 0, then c = 0 *)
  assert (Hnc : fld.(cr_neg) c = fld.(cr_zero)) by exact (f_equal fst H2).
  assert (Hc : c = fld.(cr_zero)).
  { rewrite <- (cr_neg_neg' fld c). rewrite Hnc. apply cr_neg_zero'. }
  (* Conclude (c,d) = (0,0) *)
  rewrite Hc, Hd. reflexivity.
Qed.

(** The adjoint representation ad : nonabelian_2d → End(F×F) is injective.
    The kernel of ad equals the center, which is trivial. *)
Lemma nonabelian_2d_ad_injective {F : Type} (fld : Field F) (v : F * F) :
    (forall w, ad (nonabelian_2d fld) v w = la_zero (nonabelian_2d fld)) ->
    v = la_zero (nonabelian_2d fld).
Proof.
  intro Hker.
  apply nonabelian_2d_center_zero.
  apply (ad_ker_is_center (nonabelian_2d fld)).
  exact Hker.
Qed.

Section Nonabelian2dAdNilpotent.
  Context {F : Type} (fld : Field F).

  Add Ring fld_ring_n2d : (cr_ring_theory fld).

  (** Standard basis vector x = (1, 0) of the 2D nonabelian Lie algebra. *)
  Definition nonabelian_2d_x : F * F :=
    (cr_one fld, cr_zero fld).

  (** x is ad-nilpotent: bracket x squared = 0 on all v.
      [x, v] = (v_2, 0), and [x, (v_2, 0)] = (1*0 - 0*v_2, 0) = 0. *)
  Theorem nonabelian_2d_x_ad_nilpotent :
      IsAdNilpotent (nonabelian_2d fld) nonabelian_2d_x.
  Proof.
    exists 2. intros [c d]. simpl.
    unfold laF_bracket, nonabelian_2d, nonabelian_2d_bracket,
           nonabelian_2d_x, la_zero, nonabelian_2d_vs.
    simpl.
    apply (f_equal2 (@pair _ _)); ring.
  Qed.

  (** Standard basis vector y = (0, 1) of the 2D nonabelian Lie algebra. *)
  Definition nonabelian_2d_y : F * F :=
    (cr_zero fld, cr_one fld).

  (** Standard bracket relation: [x, y] = x in the 2D nonabelian Lie algebra. *)
  Lemma nonabelian_2d_bracket_xy :
      laF_bracket (nonabelian_2d fld) nonabelian_2d_x nonabelian_2d_y = nonabelian_2d_x.
  Proof.
    unfold laF_bracket, nonabelian_2d, nonabelian_2d_bracket,
           nonabelian_2d_x, nonabelian_2d_y. simpl.
    apply (f_equal2 (@pair _ _)); ring.
  Qed.

  (** nonabelian_2d basis vectors are non-zero (when 1 ≠ 0). *)
  Lemma nonabelian_2d_x_nonzero :
      cr_one fld <> cr_zero fld ->
      nonabelian_2d_x <> la_zero (nonabelian_2d fld).
  Proof.
    intros Hone Heq. apply Hone.
    unfold nonabelian_2d_x, la_zero, nonabelian_2d, nonabelian_2d_vs in Heq.
    simpl in Heq.
    exact (f_equal fst Heq).
  Qed.

  Lemma nonabelian_2d_y_nonzero :
      cr_one fld <> cr_zero fld ->
      nonabelian_2d_y <> la_zero (nonabelian_2d fld).
  Proof.
    intros Hone Heq. apply Hone.
    unfold nonabelian_2d_y, la_zero, nonabelian_2d, nonabelian_2d_vs in Heq.
    simpl in Heq.
    exact (f_equal snd Heq).
  Qed.

  Lemma nonabelian_2d_x_neq_y :
      cr_one fld <> cr_zero fld ->
      nonabelian_2d_x <> nonabelian_2d_y.
  Proof.
    intros Hone Heq. apply Hone.
    unfold nonabelian_2d_x, nonabelian_2d_y in Heq.
    exact (f_equal fst Heq).
  Qed.

  (** Nonabelian 2D Lie algebra is NOT abelian (when 1 ≠ 0). *)
  Lemma nonabelian_2d_not_abelian :
      cr_one fld <> cr_zero fld ->
      ~ IsAbelian (nonabelian_2d fld).
  Proof.
    intros Hone Habel.
    pose proof (Habel nonabelian_2d_x nonabelian_2d_y) as Hcontra.
    rewrite nonabelian_2d_bracket_xy in Hcontra.
    apply Hone.
    unfold nonabelian_2d_x, la_zero, nonabelian_2d, nonabelian_2d_vs in Hcontra.
    simpl in Hcontra.
    exact (f_equal fst Hcontra).
  Qed.

  (** Iterating ad y on x cycles between x and -x (never reaches 0). *)
  Lemma nonabelian_2d_iter_y_x_cycle :
      forall N, Nat.iter N (laF_bracket (nonabelian_2d fld) nonabelian_2d_y) nonabelian_2d_x
              = nonabelian_2d_x
              \/ Nat.iter N (laF_bracket (nonabelian_2d fld) nonabelian_2d_y) nonabelian_2d_x
              = la_neg (nonabelian_2d fld) nonabelian_2d_x.
  Proof.
    intros N. induction N as [|N IH].
    - left. reflexivity.
    - replace (Nat.iter (S N) (laF_bracket (nonabelian_2d fld) nonabelian_2d_y) nonabelian_2d_x)
         with (laF_bracket (nonabelian_2d fld) nonabelian_2d_y
               (Nat.iter N (laF_bracket (nonabelian_2d fld) nonabelian_2d_y) nonabelian_2d_x))
         by reflexivity.
      destruct IH as [Hx | Hnegx].
      + rewrite Hx. right.
        unfold laF_bracket, nonabelian_2d, nonabelian_2d_bracket,
               nonabelian_2d_x, nonabelian_2d_y, la_neg, nonabelian_2d_vs.
        simpl. apply (f_equal2 (@pair _ _)); ring.
      + rewrite Hnegx. left.
        unfold laF_bracket, nonabelian_2d, nonabelian_2d_bracket,
               nonabelian_2d_x, nonabelian_2d_y, la_neg, nonabelian_2d_vs.
        simpl. apply (f_equal2 (@pair _ _)); ring.
  Qed.

  (** y is NOT ad-nilpotent (when 1 ≠ 0): iterated bracket on x cycles
      between non-zero values. *)
  Theorem nonabelian_2d_y_not_ad_nilpotent :
      cr_one fld <> cr_zero fld ->
      ~ IsAdNilpotent (nonabelian_2d fld) nonabelian_2d_y.
  Proof.
    intros Hone [N HN].
    specialize (HN nonabelian_2d_x).
    destruct (nonabelian_2d_iter_y_x_cycle N) as [Hx | Hnegx].
    - rewrite Hx in HN.
      apply Hone.
      unfold nonabelian_2d_x, la_zero, nonabelian_2d, nonabelian_2d_vs in HN.
      simpl in HN. exact (f_equal fst HN).
    - rewrite Hnegx in HN.
      apply Hone.
      unfold nonabelian_2d_x, la_zero, la_neg, nonabelian_2d, nonabelian_2d_vs in HN.
      simpl in HN.
      assert (Hneg1 : cr_neg fld (cr_one fld) = cr_zero fld) by exact (f_equal fst HN).
      assert (Hresult : cr_one fld = cr_zero fld).
      { rewrite <- (cr_neg_neg' fld (cr_one fld)).
        rewrite Hneg1. apply cr_neg_zero'. }
      exact Hresult.
  Qed.

End Nonabelian2dAdNilpotent.

(** ** Exercise 1: F³ with the cross product *)

(** Cross product on F³:
    (u₁,u₂,u₃) × (v₁,v₂,v₃) = (u₂v₃ - u₃v₂, u₃v₁ - u₁v₃, u₁v₂ - u₂v₁).
    Standard basis: e₁=(1,0,0), e₂=(0,1,0), e₃=(0,0,1).
    [e₁,e₂]=e₃, [e₂,e₃]=e₁, [e₃,e₁]=e₂ (cyclic). *)

Definition cross_product {F : Type} (fld : Field F)
    (u v : F * F * F) : F * F * F :=
  let '((u1,u2),u3) := u in
  let '((v1,v2),v3) := v in
  ((fld.(cr_add) (fld.(cr_mul) u2 v3) (fld.(cr_neg) (fld.(cr_mul) u3 v2)),
    fld.(cr_add) (fld.(cr_mul) u3 v1) (fld.(cr_neg) (fld.(cr_mul) u1 v3))),
   fld.(cr_add) (fld.(cr_mul) u1 v2) (fld.(cr_neg) (fld.(cr_mul) u2 v1))).

(** Helper: one component of the cross product Jacobi identity.
    The 12 monomials split into 6 cancelling pairs (PQR-part and STU-part). *)
Local Lemma cross_comp_zero {F : Type} (fld : Field F)
    (a b c d e f g h i : F) :
    fld.(cr_add)
      (fld.(cr_add)
        (fld.(cr_add)
          (fld.(cr_mul) a (fld.(cr_add) (fld.(cr_mul) b c) (fld.(cr_neg) (fld.(cr_mul) d e))))
          (fld.(cr_neg) (fld.(cr_mul) f (fld.(cr_add) (fld.(cr_mul) g e) (fld.(cr_neg) (fld.(cr_mul) b h))))))
        (fld.(cr_add)
          (fld.(cr_mul) d (fld.(cr_add) (fld.(cr_mul) e a) (fld.(cr_neg) (fld.(cr_mul) c i))))
          (fld.(cr_neg) (fld.(cr_mul) g (fld.(cr_add) (fld.(cr_mul) h i) (fld.(cr_neg) (fld.(cr_mul) e f)))))))
      (fld.(cr_add)
        (fld.(cr_mul) c (fld.(cr_add) (fld.(cr_mul) i d) (fld.(cr_neg) (fld.(cr_mul) a b))))
        (fld.(cr_neg) (fld.(cr_mul) h (fld.(cr_add) (fld.(cr_mul) f b) (fld.(cr_neg) (fld.(cr_mul) i g))))))
    = fld.(cr_zero).
Proof.
  set (P := fld.(cr_mul) a (fld.(cr_mul) b c)).
  set (Q := fld.(cr_mul) a (fld.(cr_mul) d e)).
  set (R := fld.(cr_mul) c (fld.(cr_mul) i d)).
  set (S := fld.(cr_mul) f (fld.(cr_mul) g e)).
  set (T := fld.(cr_mul) f (fld.(cr_mul) b h)).
  set (U := fld.(cr_mul) g (fld.(cr_mul) h i)).
  (* H1: a*(b*c - d*e) = P - Q *)
  assert (H1 : fld.(cr_mul) a (fld.(cr_add) (fld.(cr_mul) b c) (fld.(cr_neg) (fld.(cr_mul) d e)))
             = fld.(cr_add) P (fld.(cr_neg) Q)).
  { unfold P, Q. rewrite fld.(cr_distrib), cr_neg_mul_r'. reflexivity. }
  (* H2: neg(f*(g*e - b*h)) = neg(S) + T *)
  assert (H2 : fld.(cr_neg) (fld.(cr_mul) f
                  (fld.(cr_add) (fld.(cr_mul) g e) (fld.(cr_neg) (fld.(cr_mul) b h))))
             = fld.(cr_add) (fld.(cr_neg) S) T).
  { unfold S, T.
    rewrite fld.(cr_distrib), cr_neg_mul_r', cr_neg_add_distr, cr_neg_neg'.
    reflexivity. }
  (* H3: d*(e*a - c*i) = Q - R *)
  assert (H3 : fld.(cr_mul) d (fld.(cr_add) (fld.(cr_mul) e a) (fld.(cr_neg) (fld.(cr_mul) c i)))
             = fld.(cr_add) Q (fld.(cr_neg) R)).
  { unfold Q, R. rewrite fld.(cr_distrib), cr_neg_mul_r'. f_equal.
    - rewrite (fld.(cr_mul_comm) e a), (fld.(cr_mul_assoc) d a e),
              (fld.(cr_mul_comm) d a), <- (fld.(cr_mul_assoc) a d e). reflexivity.
    - f_equal. rewrite (fld.(cr_mul_assoc) d c i), (fld.(cr_mul_comm) d c),
                        <- (fld.(cr_mul_assoc) c d i), (fld.(cr_mul_comm) d i). reflexivity. }
  (* H4: neg(g*(h*i - e*f)) = neg(U) + S *)
  assert (H4 : fld.(cr_neg) (fld.(cr_mul) g
                  (fld.(cr_add) (fld.(cr_mul) h i) (fld.(cr_neg) (fld.(cr_mul) e f))))
             = fld.(cr_add) (fld.(cr_neg) U) S).
  { unfold S, U.
    rewrite fld.(cr_distrib), cr_neg_mul_r', cr_neg_add_distr, cr_neg_neg'.
    f_equal.
    rewrite (fld.(cr_mul_comm) e f), (fld.(cr_mul_assoc) g f e),
            (fld.(cr_mul_comm) g f), <- (fld.(cr_mul_assoc) f g e). reflexivity. }
  (* H5: c*(i*d - a*b) = R - P *)
  assert (H5 : fld.(cr_mul) c (fld.(cr_add) (fld.(cr_mul) i d) (fld.(cr_neg) (fld.(cr_mul) a b)))
             = fld.(cr_add) R (fld.(cr_neg) P)).
  { unfold P, R. rewrite fld.(cr_distrib), cr_neg_mul_r'. f_equal.
    f_equal. rewrite (fld.(cr_mul_assoc) c a b), (fld.(cr_mul_comm) c a),
                     <- (fld.(cr_mul_assoc) a c b), (fld.(cr_mul_comm) c b). reflexivity. }
  (* H6: neg(h*(f*b - i*g)) = neg(T) + U *)
  assert (H6 : fld.(cr_neg) (fld.(cr_mul) h
                  (fld.(cr_add) (fld.(cr_mul) f b) (fld.(cr_neg) (fld.(cr_mul) i g))))
             = fld.(cr_add) (fld.(cr_neg) T) U).
  { unfold T, U.
    rewrite fld.(cr_distrib), cr_neg_mul_r', cr_neg_add_distr, cr_neg_neg'.
    f_equal.
    - f_equal. rewrite (fld.(cr_mul_assoc) h f b), (fld.(cr_mul_comm) h f),
                        <- (fld.(cr_mul_assoc) f h b), (fld.(cr_mul_comm) h b). reflexivity.
    - rewrite (fld.(cr_mul_assoc) h i g), (fld.(cr_mul_comm) (fld.(cr_mul) h i) g). reflexivity. }
  rewrite H1, H2, H3, H4, H5, H6.
  (* Goal: ((P-Q)+(-S+T)) + ((Q-R)+(-U+S)) + ((R-P)+(-T+U)) = 0 *)
  set (B1 := fld.(cr_add) P (fld.(cr_neg) Q)).
  set (B2 := fld.(cr_add) (fld.(cr_neg) S) T).
  set (B3 := fld.(cr_add) Q (fld.(cr_neg) R)).
  set (B4 := fld.(cr_add) (fld.(cr_neg) U) S).
  set (B5 := fld.(cr_add) R (fld.(cr_neg) P)).
  set (B6 := fld.(cr_add) (fld.(cr_neg) T) U).
  (* PQR-part: (B1+B3)+B5 = 0 *)
  assert (HA : fld.(cr_add) (fld.(cr_add) B1 B3) B5 = fld.(cr_zero)).
  { unfold B1, B3, B5.
    rewrite <- (fld.(cr_add_assoc) (fld.(cr_add) P (fld.(cr_neg) Q))
                                    (fld.(cr_add) Q (fld.(cr_neg) R))
                                    (fld.(cr_add) R (fld.(cr_neg) P))).
    rewrite <- (fld.(cr_add_assoc) Q (fld.(cr_neg) R) (fld.(cr_add) R (fld.(cr_neg) P))).
    rewrite (fld.(cr_add_assoc) (fld.(cr_neg) R) R (fld.(cr_neg) P)).
    rewrite cr_add_neg_l', cr_add_zero_l'.
    rewrite <- (fld.(cr_add_assoc) P (fld.(cr_neg) Q) (fld.(cr_add) Q (fld.(cr_neg) P))).
    rewrite (fld.(cr_add_assoc) (fld.(cr_neg) Q) Q (fld.(cr_neg) P)).
    rewrite cr_add_neg_l', cr_add_zero_l'. apply fld.(cr_add_neg). }
  (* STU-part: (B2+B4)+B6 = 0 — same structure with T,S,U *)
  assert (HB : fld.(cr_add) (fld.(cr_add) B2 B4) B6 = fld.(cr_zero)).
  { unfold B2, B4, B6.
    rewrite (fld.(cr_add_comm) (fld.(cr_neg) S) T),
            (fld.(cr_add_comm) (fld.(cr_neg) U) S),
            (fld.(cr_add_comm) (fld.(cr_neg) T) U).
    rewrite <- (fld.(cr_add_assoc) (fld.(cr_add) T (fld.(cr_neg) S))
                                    (fld.(cr_add) S (fld.(cr_neg) U))
                                    (fld.(cr_add) U (fld.(cr_neg) T))).
    rewrite <- (fld.(cr_add_assoc) S (fld.(cr_neg) U) (fld.(cr_add) U (fld.(cr_neg) T))).
    rewrite (fld.(cr_add_assoc) (fld.(cr_neg) U) U (fld.(cr_neg) T)).
    rewrite cr_add_neg_l', cr_add_zero_l'.
    rewrite <- (fld.(cr_add_assoc) T (fld.(cr_neg) S) (fld.(cr_add) S (fld.(cr_neg) T))).
    rewrite (fld.(cr_add_assoc) (fld.(cr_neg) S) S (fld.(cr_neg) T)).
    rewrite cr_add_neg_l', cr_add_zero_l'. apply fld.(cr_add_neg). }
  (* Rearrange ((B1+B2)+(B3+B4))+(B5+B6) to ((B1+B3)+B5)+((B2+B4)+B6) *)
  rewrite <- (fld.(cr_add_assoc) (fld.(cr_add) B1 B2) (fld.(cr_add) B3 B4)
                                  (fld.(cr_add) B5 B6)).
  rewrite <- (fld.(cr_add_assoc) B3 B4 (fld.(cr_add) B5 B6)).
  rewrite <- (fld.(cr_add_assoc) B1 B2
                (fld.(cr_add) B3 (fld.(cr_add) B4 (fld.(cr_add) B5 B6)))).
  rewrite (fld.(cr_add_assoc) B2 B3 (fld.(cr_add) B4 (fld.(cr_add) B5 B6))).
  rewrite (fld.(cr_add_comm) B2 B3).
  rewrite <- (fld.(cr_add_assoc) B3 B2 (fld.(cr_add) B4 (fld.(cr_add) B5 B6))).
  rewrite (fld.(cr_add_assoc) B1 B3
             (fld.(cr_add) B2 (fld.(cr_add) B4 (fld.(cr_add) B5 B6)))).
  rewrite (fld.(cr_add_assoc) B2 B4 (fld.(cr_add) B5 B6)).
  rewrite (fld.(cr_add_assoc) (fld.(cr_add) B2 B4) B5 B6).
  rewrite (fld.(cr_add_comm) (fld.(cr_add) B2 B4) B5).
  rewrite <- (fld.(cr_add_assoc) B5 (fld.(cr_add) B2 B4) B6).
  rewrite (fld.(cr_add_assoc) (fld.(cr_add) B1 B3) B5
             (fld.(cr_add) (fld.(cr_add) B2 B4) B6)).
  (* Now: ((B1+B3)+B5) + ((B2+B4)+B6) = 0 *)
  rewrite HA, HB. apply cr_add_zero_l'.
Qed.

(** F³ with the cross product is a Lie algebra. *)
Definition cross_product_lie {F : Type} (fld : Field F) : LieAlgebraF fld (F * F * F).
Proof.
  refine {|
    laF_vs      := ex2_vs fld;
    laF_bracket := cross_product fld;
  |}.
  - (* bracket_add_l: (u+v)×w = u×w + v×w *)
    intros [[x1 x2] x3] [[y1 y2] y3] [[z1 z2] z3].
    unfold cross_product, ex2_vs. simpl.
    apply (f_equal2 pair); [apply (f_equal2 pair)|].
    + (* comp1: (x2+y2)*z3 - (x3+y3)*z2 = (x2*z3-x3*z2) + (y2*z3-y3*z2) *)
      rewrite cr_distrib_r', cr_distrib_r', cr_neg_add_distr.
      rewrite <- fld.(cr_add_assoc).
      rewrite (fld.(cr_add_assoc) (fld.(cr_mul) y2 z3)
                                   (fld.(cr_neg) (fld.(cr_mul) x3 z2))
                                   (fld.(cr_neg) (fld.(cr_mul) y3 z2))).
      rewrite (fld.(cr_add_comm) (fld.(cr_mul) y2 z3)
                                  (fld.(cr_neg) (fld.(cr_mul) x3 z2))).
      rewrite <- (fld.(cr_add_assoc) (fld.(cr_neg) (fld.(cr_mul) x3 z2))
                                      (fld.(cr_mul) y2 z3)
                                      (fld.(cr_neg) (fld.(cr_mul) y3 z2))).
      rewrite (fld.(cr_add_assoc) (fld.(cr_mul) x2 z3)
                                   (fld.(cr_neg) (fld.(cr_mul) x3 z2))
                                   (fld.(cr_add) (fld.(cr_mul) y2 z3)
                                                 (fld.(cr_neg) (fld.(cr_mul) y3 z2)))).
      reflexivity.
    + (* comp2: (x3+y3)*z1 - (x1+y1)*z3 = (x3*z1-x1*z3) + (y3*z1-y1*z3) *)
      rewrite cr_distrib_r', cr_distrib_r', cr_neg_add_distr.
      rewrite <- fld.(cr_add_assoc).
      rewrite (fld.(cr_add_assoc) (fld.(cr_mul) y3 z1)
                                   (fld.(cr_neg) (fld.(cr_mul) x1 z3))
                                   (fld.(cr_neg) (fld.(cr_mul) y1 z3))).
      rewrite (fld.(cr_add_comm) (fld.(cr_mul) y3 z1)
                                  (fld.(cr_neg) (fld.(cr_mul) x1 z3))).
      rewrite <- (fld.(cr_add_assoc) (fld.(cr_neg) (fld.(cr_mul) x1 z3))
                                      (fld.(cr_mul) y3 z1)
                                      (fld.(cr_neg) (fld.(cr_mul) y1 z3))).
      rewrite (fld.(cr_add_assoc) (fld.(cr_mul) x3 z1)
                                   (fld.(cr_neg) (fld.(cr_mul) x1 z3))
                                   (fld.(cr_add) (fld.(cr_mul) y3 z1)
                                                 (fld.(cr_neg) (fld.(cr_mul) y1 z3)))).
      reflexivity.
    + (* comp3: (x1+y1)*z2 - (x2+y2)*z1 = (x1*z2-x2*z1) + (y1*z2-y2*z1) *)
      rewrite cr_distrib_r', cr_distrib_r', cr_neg_add_distr.
      rewrite <- fld.(cr_add_assoc).
      rewrite (fld.(cr_add_assoc) (fld.(cr_mul) y1 z2)
                                   (fld.(cr_neg) (fld.(cr_mul) x2 z1))
                                   (fld.(cr_neg) (fld.(cr_mul) y2 z1))).
      rewrite (fld.(cr_add_comm) (fld.(cr_mul) y1 z2)
                                  (fld.(cr_neg) (fld.(cr_mul) x2 z1))).
      rewrite <- (fld.(cr_add_assoc) (fld.(cr_neg) (fld.(cr_mul) x2 z1))
                                      (fld.(cr_mul) y1 z2)
                                      (fld.(cr_neg) (fld.(cr_mul) y2 z1))).
      rewrite (fld.(cr_add_assoc) (fld.(cr_mul) x1 z2)
                                   (fld.(cr_neg) (fld.(cr_mul) x2 z1))
                                   (fld.(cr_add) (fld.(cr_mul) y1 z2)
                                                 (fld.(cr_neg) (fld.(cr_mul) y2 z1)))).
      reflexivity.
  - (* bracket_scale_l: (c*u)×v = c*(u×v) *)
    intros c [[x1 x2] x3] [[y1 y2] y3].
    unfold cross_product, ex2_vs. simpl.
    apply (f_equal2 pair); [apply (f_equal2 pair)|].
    + rewrite <- fld.(cr_mul_assoc), <- fld.(cr_mul_assoc),
              <- cr_neg_mul_r', <- fld.(cr_distrib). reflexivity.
    + rewrite <- fld.(cr_mul_assoc), <- fld.(cr_mul_assoc),
              <- cr_neg_mul_r', <- fld.(cr_distrib). reflexivity.
    + rewrite <- fld.(cr_mul_assoc), <- fld.(cr_mul_assoc),
              <- cr_neg_mul_r', <- fld.(cr_distrib). reflexivity.
  - (* bracket_add_r: u×(v+w) = u×v + u×w *)
    intros [[x1 x2] x3] [[y1 y2] y3] [[z1 z2] z3].
    unfold cross_product, ex2_vs. simpl.
    apply (f_equal2 pair); [apply (f_equal2 pair)|].
    + rewrite fld.(cr_distrib), fld.(cr_distrib), cr_neg_add_distr.
      rewrite <- fld.(cr_add_assoc).
      rewrite (fld.(cr_add_assoc) (fld.(cr_mul) x2 z3)
                                   (fld.(cr_neg) (fld.(cr_mul) x3 y2))
                                   (fld.(cr_neg) (fld.(cr_mul) x3 z2))).
      rewrite (fld.(cr_add_comm) (fld.(cr_mul) x2 z3)
                                  (fld.(cr_neg) (fld.(cr_mul) x3 y2))).
      rewrite <- (fld.(cr_add_assoc) (fld.(cr_neg) (fld.(cr_mul) x3 y2))
                                      (fld.(cr_mul) x2 z3)
                                      (fld.(cr_neg) (fld.(cr_mul) x3 z2))).
      rewrite (fld.(cr_add_assoc) (fld.(cr_mul) x2 y3)
                                   (fld.(cr_neg) (fld.(cr_mul) x3 y2))
                                   (fld.(cr_add) (fld.(cr_mul) x2 z3)
                                                 (fld.(cr_neg) (fld.(cr_mul) x3 z2)))).
      reflexivity.
    + rewrite fld.(cr_distrib), fld.(cr_distrib), cr_neg_add_distr.
      rewrite <- fld.(cr_add_assoc).
      rewrite (fld.(cr_add_assoc) (fld.(cr_mul) x3 z1)
                                   (fld.(cr_neg) (fld.(cr_mul) x1 y3))
                                   (fld.(cr_neg) (fld.(cr_mul) x1 z3))).
      rewrite (fld.(cr_add_comm) (fld.(cr_mul) x3 z1)
                                  (fld.(cr_neg) (fld.(cr_mul) x1 y3))).
      rewrite <- (fld.(cr_add_assoc) (fld.(cr_neg) (fld.(cr_mul) x1 y3))
                                      (fld.(cr_mul) x3 z1)
                                      (fld.(cr_neg) (fld.(cr_mul) x1 z3))).
      rewrite (fld.(cr_add_assoc) (fld.(cr_mul) x3 y1)
                                   (fld.(cr_neg) (fld.(cr_mul) x1 y3))
                                   (fld.(cr_add) (fld.(cr_mul) x3 z1)
                                                 (fld.(cr_neg) (fld.(cr_mul) x1 z3)))).
      reflexivity.
    + rewrite fld.(cr_distrib), fld.(cr_distrib), cr_neg_add_distr.
      rewrite <- fld.(cr_add_assoc).
      rewrite (fld.(cr_add_assoc) (fld.(cr_mul) x1 z2)
                                   (fld.(cr_neg) (fld.(cr_mul) x2 y1))
                                   (fld.(cr_neg) (fld.(cr_mul) x2 z1))).
      rewrite (fld.(cr_add_comm) (fld.(cr_mul) x1 z2)
                                  (fld.(cr_neg) (fld.(cr_mul) x2 y1))).
      rewrite <- (fld.(cr_add_assoc) (fld.(cr_neg) (fld.(cr_mul) x2 y1))
                                      (fld.(cr_mul) x1 z2)
                                      (fld.(cr_neg) (fld.(cr_mul) x2 z1))).
      rewrite (fld.(cr_add_assoc) (fld.(cr_mul) x1 y2)
                                   (fld.(cr_neg) (fld.(cr_mul) x2 y1))
                                   (fld.(cr_add) (fld.(cr_mul) x1 z2)
                                                 (fld.(cr_neg) (fld.(cr_mul) x2 z1)))).
      reflexivity.
  - (* bracket_scale_r: u×(c*v) = c*(u×v) *)
    intros c [[x1 x2] x3] [[y1 y2] y3].
    unfold cross_product, ex2_vs. simpl.
    apply (f_equal2 pair); [apply (f_equal2 pair)|].
    + rewrite (fld.(cr_mul_comm) x2 (fld.(cr_mul) c y3)),
              <- fld.(cr_mul_assoc), (fld.(cr_mul_comm) y3 x2),
              (fld.(cr_mul_comm) x3 (fld.(cr_mul) c y2)),
              <- fld.(cr_mul_assoc), (fld.(cr_mul_comm) y2 x3),
              <- cr_neg_mul_r', <- fld.(cr_distrib). reflexivity.
    + rewrite (fld.(cr_mul_comm) x3 (fld.(cr_mul) c y1)),
              <- fld.(cr_mul_assoc), (fld.(cr_mul_comm) y1 x3),
              (fld.(cr_mul_comm) x1 (fld.(cr_mul) c y3)),
              <- fld.(cr_mul_assoc), (fld.(cr_mul_comm) y3 x1),
              <- cr_neg_mul_r', <- fld.(cr_distrib). reflexivity.
    + rewrite (fld.(cr_mul_comm) x1 (fld.(cr_mul) c y2)),
              <- fld.(cr_mul_assoc), (fld.(cr_mul_comm) y2 x1),
              (fld.(cr_mul_comm) x2 (fld.(cr_mul) c y1)),
              <- fld.(cr_mul_assoc), (fld.(cr_mul_comm) y1 x2),
              <- cr_neg_mul_r', <- fld.(cr_distrib). reflexivity.
  - (* bracket_alt: u×u = 0 *)
    intros [[x1 x2] x3].
    unfold cross_product, ex2_vs. simpl.
    apply (f_equal2 pair); [apply (f_equal2 pair)|].
    + rewrite (fld.(cr_mul_comm) x2 x3). apply fld.(cr_add_neg).
    + rewrite (fld.(cr_mul_comm) x3 x1). apply fld.(cr_add_neg).
    + rewrite (fld.(cr_mul_comm) x1 x2). apply fld.(cr_add_neg).
  - (* jacobi: [u,[v,w]] + [v,[w,u]] + [w,[u,v]] = 0 per component.
       Each component is an instance of cross_comp_zero. *)
    intros [[x1 x2] x3] [[y1 y2] y3] [[z1 z2] z3].
    unfold cross_product, ex2_vs. simpl.
    apply (f_equal2 pair); [apply (f_equal2 pair)|].
    + exact (cross_comp_zero fld x2 y1 z2 y2 z1 x3 y3 z3 x1).
    + exact (cross_comp_zero fld x3 y2 z3 y3 z2 x1 y1 z1 x2).
    + exact (cross_comp_zero fld x1 y3 z1 y1 z3 x2 y2 z2 x3).
Defined.

(** The cross-product Lie algebra is non-abelian when 1 ≠ 0:
    [e_1, e_2] = e_3 ≠ 0. *)
(** The cross-product Lie algebra has trivial center when 1 ≠ 0:
    every central element is zero. *)
Lemma cross_product_lie_center_zero {F : Type} (fld : Field F) :
    fld.(cr_one) <> fld.(cr_zero) ->
    forall v : F * F * F, IsCenter (cross_product_lie fld) v ->
    v = la_zero (cross_product_lie fld).
Proof.
  intros Hone v Hctr.
  destruct v as [[a b] c].
  (* H1 = [(1,0,0), (a,b,c)] = 0; component 3 = 1*b - 0*a = b ⇒ b = 0 *)
  pose proof (Hctr ((cr_one fld, cr_zero fld), cr_zero fld)) as H1.
  unfold laF_bracket, cross_product_lie, cross_product, ex2_vs, la_zero in H1.
  simpl in H1.
  assert (Hb : b = cr_zero fld).
  { assert (Heq : fld.(cr_add) (fld.(cr_mul) (cr_one fld) b)
                    (fld.(cr_neg) (fld.(cr_mul) (cr_zero fld) a)) = cr_zero fld)
      by exact (f_equal snd H1).
    rewrite (cr_mul_comm fld _ b), (cr_mul_one fld) in Heq.
    rewrite cr_mul_zero_l' in Heq.
    rewrite cr_neg_zero' in Heq.
    rewrite (cr_add_zero fld) in Heq.
    exact Heq. }
  (* H1 component 2 = 0*a - 1*c = -c ⇒ c = 0 *)
  assert (Hc : c = cr_zero fld).
  { assert (Heq : fld.(cr_add) (fld.(cr_mul) (cr_zero fld) a)
                    (fld.(cr_neg) (fld.(cr_mul) (cr_one fld) c)) = cr_zero fld)
      by exact (f_equal (fun p => snd (fst p)) H1).
    rewrite cr_mul_zero_l' in Heq.
    rewrite (cr_mul_comm fld _ c), (cr_mul_one fld) in Heq.
    rewrite cr_add_zero_l' in Heq.
    rewrite <- (cr_neg_neg' fld c).
    rewrite Heq. apply cr_neg_zero'. }
  (* H2 = [(0,1,0), (a,b,c)] = 0; component 3 = 0*b - 1*a = -a ⇒ a = 0 *)
  pose proof (Hctr ((cr_zero fld, cr_one fld), cr_zero fld)) as H2.
  unfold laF_bracket, cross_product_lie, cross_product, ex2_vs, la_zero in H2.
  simpl in H2.
  assert (Ha : a = cr_zero fld).
  { assert (Heq : fld.(cr_add) (fld.(cr_mul) (cr_zero fld) b)
                    (fld.(cr_neg) (fld.(cr_mul) (cr_one fld) a)) = cr_zero fld)
      by exact (f_equal snd H2).
    rewrite cr_mul_zero_l' in Heq.
    rewrite (cr_mul_comm fld _ a), (cr_mul_one fld) in Heq.
    rewrite cr_add_zero_l' in Heq.
    rewrite <- (cr_neg_neg' fld a).
    rewrite Heq. apply cr_neg_zero'. }
  rewrite Ha, Hb, Hc. reflexivity.
Qed.

(** Adjoint representation of cross_product is injective (trivial center). *)
Lemma cross_product_lie_ad_injective {F : Type} (fld : Field F) :
    fld.(cr_one) <> fld.(cr_zero) ->
    forall v : F * F * F,
      (forall w, ad (cross_product_lie fld) v w = la_zero (cross_product_lie fld)) ->
      v = la_zero (cross_product_lie fld).
Proof.
  intros Hone v Hker.
  apply (cross_product_lie_center_zero fld Hone).
  apply (ad_ker_is_center (cross_product_lie fld)).
  exact Hker.
Qed.

(** The cross-product Lie algebra is perfect: every element is in the
    derived algebra. Wrapped in a section to register the [ring] tactic. *)
Section CrossProductDerived.

  Context {F : Type} (fld : Field F).

  Local Lemma cross_ring_theory_local : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring cross_fld_ring_inst : cross_ring_theory_local.

  Lemma cross_product_lie_derived_full :
      forall z : F * F * F, IsDerivedAlg (cross_product_lie fld) z.
  Proof.
    intro z. unfold IsDerivedAlg.
    intros S HS HB.
    destruct z as [[a b] c].
    set (e1 := ((cr_one fld, cr_zero fld), cr_zero fld) : F * F * F).
    set (e2 := ((cr_zero fld, cr_one fld), cr_zero fld) : F * F * F).
    set (e3 := ((cr_zero fld, cr_zero fld), cr_one fld) : F * F * F).
    assert (He1 : S e1).
    { unfold e1.
      replace ((cr_one fld, cr_zero fld), cr_zero fld) with
        (laF_bracket (cross_product_lie fld) e2 e3); [apply HB|].
      unfold laF_bracket, cross_product_lie, cross_product, e2, e3, ex2_vs.
      simpl. f_equal. - f_equal; ring. - ring. }
    assert (He2 : S e2).
    { unfold e2.
      replace ((cr_zero fld, cr_one fld), cr_zero fld) with
        (laF_bracket (cross_product_lie fld) e3 e1); [apply HB|].
      unfold laF_bracket, cross_product_lie, cross_product, e3, e1, ex2_vs.
      simpl. f_equal. - f_equal; ring. - ring. }
    assert (He3 : S e3).
    { unfold e3.
      replace ((cr_zero fld, cr_zero fld), cr_one fld) with
        (laF_bracket (cross_product_lie fld) e1 e2); [apply HB|].
      unfold laF_bracket, cross_product_lie, cross_product, e1, e2, ex2_vs.
      simpl. f_equal. - f_equal; ring. - ring. }
    assert (Hz : (a, b, c) =
                 la_add (cross_product_lie fld)
                   (la_add (cross_product_lie fld)
                      (la_scale (cross_product_lie fld) a e1)
                      (la_scale (cross_product_lie fld) b e2))
                   (la_scale (cross_product_lie fld) c e3)).
    { unfold la_add, la_scale, cross_product_lie, e1, e2, e3, ex2_vs. simpl.
      f_equal. - f_equal; ring. - ring. }
    rewrite Hz.
    apply HS.(sub_add).
    - apply HS.(sub_add).
      + apply HS.(sub_scale). exact He1.
      + apply HS.(sub_scale). exact He2.
    - apply HS.(sub_scale). exact He3.
  Qed.

  (** Each level of the derived series of cross_product_lie is the full algebra. *)
  Lemma cross_product_lie_derived_series_full :
      forall n (z : F * F * F), derived_series (cross_product_lie fld) n z.
  Proof.
    intros n. induction n as [| n IHn]; intro z.
    - simpl. exact Logic.I.
    - simpl. intros U HU HBr.
      apply (cross_product_lie_derived_full z).
      + apply ideal_is_subalgebra. exact HU.
      + intros x y. apply HBr; apply IHn.
  Qed.

  (** The cross-product Lie algebra is NOT solvable when 1 ≠ 0. *)
  Lemma cross_product_lie_not_solvable :
      fld.(cr_one) <> fld.(cr_zero) ->
      ~ IsSolvable (cross_product_lie fld).
  Proof.
    intros Hone [n Hsolv].
    set (e1 := ((cr_one fld, cr_zero fld), cr_zero fld) : F * F * F).
    assert (He1ne : e1 <> la_zero (cross_product_lie fld)).
    { intro H. apply Hone. unfold e1, la_zero, cross_product_lie, ex2_vs in H.
      simpl in H. exact (f_equal (fun p => fst (fst p)) H). }
    apply He1ne. apply Hsolv.
    apply cross_product_lie_derived_series_full.
  Qed.

  (** Therefore cross_product_lie is NOT nilpotent (nilpotent ⟹ solvable). *)
  Lemma cross_product_lie_not_nilpotent :
      fld.(cr_one) <> fld.(cr_zero) ->
      ~ IsNilpotent (cross_product_lie fld).
  Proof.
    intros Hone Hnilp.
    apply (cross_product_lie_not_solvable Hone).
    apply nilpotent_is_solvable. exact Hnilp.
  Qed.

End CrossProductDerived.

Section CrossProductBasis.
  Context {F : Type} (fld : Field F).

  Local Lemma cross_basis_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring fld_ring_cb : cross_basis_ring_theory.

  (** Standard basis vectors of F^3 with cross product. *)
  Definition cross_e1 : F * F * F := ((cr_one fld, cr_zero fld), cr_zero fld).
  Definition cross_e2 : F * F * F := ((cr_zero fld, cr_one fld), cr_zero fld).
  Definition cross_e3 : F * F * F := ((cr_zero fld, cr_zero fld), cr_one fld).

  (** Standard cross-product bracket relations: [e1, e2] = e3, [e2, e3] = e1, [e3, e1] = e2. *)
  Lemma cross_bracket_e1_e2 :
      laF_bracket (cross_product_lie fld) cross_e1 cross_e2 = cross_e3.
  Proof.
    unfold laF_bracket, cross_product_lie, cross_product,
           cross_e1, cross_e2, cross_e3, ex2_vs. simpl.
    apply (f_equal2 (@pair _ _)); [apply (f_equal2 (@pair _ _))|]; ring.
  Qed.

  Lemma cross_bracket_e2_e3 :
      laF_bracket (cross_product_lie fld) cross_e2 cross_e3 = cross_e1.
  Proof.
    unfold laF_bracket, cross_product_lie, cross_product,
           cross_e1, cross_e2, cross_e3, ex2_vs. simpl.
    apply (f_equal2 (@pair _ _)); [apply (f_equal2 (@pair _ _))|]; ring.
  Qed.

  Lemma cross_bracket_e3_e1 :
      laF_bracket (cross_product_lie fld) cross_e3 cross_e1 = cross_e2.
  Proof.
    unfold laF_bracket, cross_product_lie, cross_product,
           cross_e1, cross_e2, cross_e3, ex2_vs. simpl.
    apply (f_equal2 (@pair _ _)); [apply (f_equal2 (@pair _ _))|]; ring.
  Qed.

  (** Standard basis vectors are non-zero (when 1 ≠ 0). *)
  Lemma cross_e1_nonzero : cr_one fld <> cr_zero fld -> cross_e1 <> la_zero (cross_product_lie fld).
  Proof.
    intros Hone Heq. apply Hone.
    unfold cross_e1, la_zero, cross_product_lie, ex2_vs in Heq. simpl in Heq.
    exact (f_equal (fun p => fst (fst p)) Heq).
  Qed.

  Lemma cross_e2_nonzero : cr_one fld <> cr_zero fld -> cross_e2 <> la_zero (cross_product_lie fld).
  Proof.
    intros Hone Heq. apply Hone.
    unfold cross_e2, la_zero, cross_product_lie, ex2_vs in Heq. simpl in Heq.
    exact (f_equal (fun p => snd (fst p)) Heq).
  Qed.

  Lemma cross_e3_nonzero : cr_one fld <> cr_zero fld -> cross_e3 <> la_zero (cross_product_lie fld).
  Proof.
    intros Hone Heq. apply Hone.
    unfold cross_e3, la_zero, cross_product_lie, ex2_vs in Heq. simpl in Heq.
    exact (f_equal snd Heq).
  Qed.

  (** Standard basis vectors are pairwise distinct (when 1 ≠ 0). *)
  Lemma cross_e1_neq_e2 : cr_one fld <> cr_zero fld -> cross_e1 <> cross_e2.
  Proof.
    intros Hone Heq. apply Hone.
    unfold cross_e1, cross_e2 in Heq.
    exact (f_equal (fun p => fst (fst p)) Heq).
  Qed.

  Lemma cross_e2_neq_e3 : cr_one fld <> cr_zero fld -> cross_e2 <> cross_e3.
  Proof.
    intros Hone Heq. apply Hone.
    unfold cross_e2, cross_e3 in Heq.
    exact (f_equal (fun p => snd (fst p)) Heq).
  Qed.

  Lemma cross_e1_neq_e3 : cr_one fld <> cr_zero fld -> cross_e1 <> cross_e3.
  Proof.
    intros Hone Heq. apply Hone.
    unfold cross_e1, cross_e3 in Heq.
    exact (f_equal (fun p => fst (fst p)) Heq).
  Qed.

  (** Iterating bracket e1 on e2 cycles through {e2, e3, -e2, -e3} of length 4. *)
  Lemma cross_iter_e1_e2_cycle :
      forall N, Nat.iter N (laF_bracket (cross_product_lie fld) cross_e1) cross_e2 = cross_e2
              \/ Nat.iter N (laF_bracket (cross_product_lie fld) cross_e1) cross_e2 = cross_e3
              \/ Nat.iter N (laF_bracket (cross_product_lie fld) cross_e1) cross_e2 =
                 la_neg (cross_product_lie fld) cross_e2
              \/ Nat.iter N (laF_bracket (cross_product_lie fld) cross_e1) cross_e2 =
                 la_neg (cross_product_lie fld) cross_e3.
  Proof.
    intros N. induction N as [|N IH].
    - left. reflexivity.
    - replace (Nat.iter (S N) (laF_bracket (cross_product_lie fld) cross_e1) cross_e2)
         with (laF_bracket (cross_product_lie fld) cross_e1
               (Nat.iter N (laF_bracket (cross_product_lie fld) cross_e1) cross_e2))
         by reflexivity.
      destruct IH as [He2 | [He3 | [Hne2 | Hne3]]].
      + (* iter N = e2 → bracket e1 e2 = e3 *)
        rewrite He2, cross_bracket_e1_e2. right; left. reflexivity.
      + (* iter N = e3 → bracket e1 e3 = -e2 *)
        rewrite He3.
        right; right; left.
        unfold laF_bracket, cross_product_lie, cross_product,
               cross_e1, cross_e2, cross_e3, la_neg, ex2_vs. simpl.
        apply (f_equal2 (@pair _ _)); [apply (f_equal2 (@pair _ _))|]; ring.
      + (* iter N = -e2 → bracket e1 (-e2) = -e3 *)
        rewrite Hne2.
        right; right; right.
        unfold laF_bracket, cross_product_lie, cross_product,
               cross_e1, cross_e2, cross_e3, la_neg, ex2_vs. simpl.
        apply (f_equal2 (@pair _ _)); [apply (f_equal2 (@pair _ _))|]; ring.
      + (* iter N = -e3 → bracket e1 (-e3) = e2 *)
        rewrite Hne3.
        left.
        unfold laF_bracket, cross_product_lie, cross_product,
               cross_e1, cross_e2, cross_e3, la_neg, ex2_vs. simpl.
        apply (f_equal2 (@pair _ _)); [apply (f_equal2 (@pair _ _))|]; ring.
  Qed.

  (** Iterating bracket e2 on e1 cycles through {e1, -e3, -e1, e3} of length 4. *)
  Lemma cross_iter_e2_e1_cycle :
      forall N, Nat.iter N (laF_bracket (cross_product_lie fld) cross_e2) cross_e1 = cross_e1
              \/ Nat.iter N (laF_bracket (cross_product_lie fld) cross_e2) cross_e1 =
                 la_neg (cross_product_lie fld) cross_e3
              \/ Nat.iter N (laF_bracket (cross_product_lie fld) cross_e2) cross_e1 =
                 la_neg (cross_product_lie fld) cross_e1
              \/ Nat.iter N (laF_bracket (cross_product_lie fld) cross_e2) cross_e1 = cross_e3.
  Proof.
    intros N. induction N as [|N IH].
    - left. reflexivity.
    - replace (Nat.iter (S N) (laF_bracket (cross_product_lie fld) cross_e2) cross_e1)
         with (laF_bracket (cross_product_lie fld) cross_e2
               (Nat.iter N (laF_bracket (cross_product_lie fld) cross_e2) cross_e1))
         by reflexivity.
      destruct IH as [He1 | [Hne3 | [Hne1 | He3]]].
      + rewrite He1. right; left.
        unfold laF_bracket, cross_product_lie, cross_product,
               cross_e1, cross_e2, cross_e3, la_neg, ex2_vs. simpl.
        apply (f_equal2 (@pair _ _)); [apply (f_equal2 (@pair _ _))|]; ring.
      + rewrite Hne3. right; right; left.
        unfold laF_bracket, cross_product_lie, cross_product,
               cross_e1, cross_e2, cross_e3, la_neg, ex2_vs. simpl.
        apply (f_equal2 (@pair _ _)); [apply (f_equal2 (@pair _ _))|]; ring.
      + rewrite Hne1. right; right; right.
        unfold laF_bracket, cross_product_lie, cross_product,
               cross_e1, cross_e2, cross_e3, la_neg, ex2_vs. simpl.
        apply (f_equal2 (@pair _ _)); [apply (f_equal2 (@pair _ _))|]; ring.
      + rewrite He3. left.
        unfold laF_bracket, cross_product_lie, cross_product,
               cross_e1, cross_e2, cross_e3, la_neg, ex2_vs. simpl.
        apply (f_equal2 (@pair _ _)); [apply (f_equal2 (@pair _ _))|]; ring.
  Qed.

  (** e2 is NOT ad-nilpotent in cross_product_lie (when 1 ≠ 0). *)
  Theorem cross_e2_not_ad_nilpotent :
      cr_one fld <> cr_zero fld ->
      ~ IsAdNilpotent (cross_product_lie fld) cross_e2.
  Proof.
    intros Hone [N HN].
    specialize (HN cross_e1).
    destruct (cross_iter_e2_e1_cycle N) as [Hv | [Hv | [Hv | Hv]]];
      rewrite Hv in HN; apply Hone.
    - unfold cross_e1, la_zero, cross_product_lie, ex2_vs in HN. simpl in HN.
      exact (f_equal (fun p => fst (fst p)) HN).
    - unfold cross_e3, la_neg, la_zero, cross_product_lie, ex2_vs in HN. simpl in HN.
      assert (Hneg1 : cr_neg fld (cr_one fld) = cr_zero fld).
      { exact (f_equal snd HN). }
      rewrite <- (cr_neg_neg' fld (cr_one fld)). rewrite Hneg1.
      apply cr_neg_zero'.
    - unfold cross_e1, la_neg, la_zero, cross_product_lie, ex2_vs in HN. simpl in HN.
      assert (Hneg1 : cr_neg fld (cr_one fld) = cr_zero fld).
      { exact (f_equal (fun p => fst (fst p)) HN). }
      rewrite <- (cr_neg_neg' fld (cr_one fld)). rewrite Hneg1.
      apply cr_neg_zero'.
    - unfold cross_e3, la_zero, cross_product_lie, ex2_vs in HN. simpl in HN.
      exact (f_equal snd HN).
  Qed.

  (** Iterating bracket e3 on e1 cycles through {e1, e2, -e1, -e2} of length 4. *)
  Lemma cross_iter_e3_e1_cycle :
      forall N, Nat.iter N (laF_bracket (cross_product_lie fld) cross_e3) cross_e1 = cross_e1
              \/ Nat.iter N (laF_bracket (cross_product_lie fld) cross_e3) cross_e1 = cross_e2
              \/ Nat.iter N (laF_bracket (cross_product_lie fld) cross_e3) cross_e1 =
                 la_neg (cross_product_lie fld) cross_e1
              \/ Nat.iter N (laF_bracket (cross_product_lie fld) cross_e3) cross_e1 =
                 la_neg (cross_product_lie fld) cross_e2.
  Proof.
    intros N. induction N as [|N IH].
    - left. reflexivity.
    - replace (Nat.iter (S N) (laF_bracket (cross_product_lie fld) cross_e3) cross_e1)
         with (laF_bracket (cross_product_lie fld) cross_e3
               (Nat.iter N (laF_bracket (cross_product_lie fld) cross_e3) cross_e1))
         by reflexivity.
      destruct IH as [He1 | [He2 | [Hne1 | Hne2]]].
      + rewrite He1. right; left.
        unfold laF_bracket, cross_product_lie, cross_product,
               cross_e1, cross_e2, cross_e3, la_neg, ex2_vs. simpl.
        apply (f_equal2 (@pair _ _)); [apply (f_equal2 (@pair _ _))|]; ring.
      + rewrite He2. right; right; left.
        unfold laF_bracket, cross_product_lie, cross_product,
               cross_e1, cross_e2, cross_e3, la_neg, ex2_vs. simpl.
        apply (f_equal2 (@pair _ _)); [apply (f_equal2 (@pair _ _))|]; ring.
      + rewrite Hne1. right; right; right.
        unfold laF_bracket, cross_product_lie, cross_product,
               cross_e1, cross_e2, cross_e3, la_neg, ex2_vs. simpl.
        apply (f_equal2 (@pair _ _)); [apply (f_equal2 (@pair _ _))|]; ring.
      + rewrite Hne2. left.
        unfold laF_bracket, cross_product_lie, cross_product,
               cross_e1, cross_e2, cross_e3, la_neg, ex2_vs. simpl.
        apply (f_equal2 (@pair _ _)); [apply (f_equal2 (@pair _ _))|]; ring.
  Qed.

  (** e3 is NOT ad-nilpotent in cross_product_lie (when 1 ≠ 0). *)
  Theorem cross_e3_not_ad_nilpotent :
      cr_one fld <> cr_zero fld ->
      ~ IsAdNilpotent (cross_product_lie fld) cross_e3.
  Proof.
    intros Hone [N HN].
    specialize (HN cross_e1).
    destruct (cross_iter_e3_e1_cycle N) as [Hv | [Hv | [Hv | Hv]]];
      rewrite Hv in HN; apply Hone.
    - unfold cross_e1, la_zero, cross_product_lie, ex2_vs in HN. simpl in HN.
      exact (f_equal (fun p => fst (fst p)) HN).
    - unfold cross_e2, la_zero, cross_product_lie, ex2_vs in HN. simpl in HN.
      exact (f_equal (fun p => snd (fst p)) HN).
    - unfold cross_e1, la_neg, la_zero, cross_product_lie, ex2_vs in HN. simpl in HN.
      assert (Hneg1 : cr_neg fld (cr_one fld) = cr_zero fld).
      { exact (f_equal (fun p => fst (fst p)) HN). }
      rewrite <- (cr_neg_neg' fld (cr_one fld)). rewrite Hneg1.
      apply cr_neg_zero'.
    - unfold cross_e2, la_neg, la_zero, cross_product_lie, ex2_vs in HN. simpl in HN.
      assert (Hneg1 : cr_neg fld (cr_one fld) = cr_zero fld).
      { exact (f_equal (fun p => snd (fst p)) HN). }
      rewrite <- (cr_neg_neg' fld (cr_one fld)). rewrite Hneg1.
      apply cr_neg_zero'.
  Qed.

  (** e1 is NOT ad-nilpotent in cross_product_lie (when 1 ≠ 0): its iterates
      on e2 cycle through 4 non-zero values forever. *)
  Theorem cross_e1_not_ad_nilpotent :
      cr_one fld <> cr_zero fld ->
      ~ IsAdNilpotent (cross_product_lie fld) cross_e1.
  Proof.
    intros Hone [N HN].
    specialize (HN cross_e2).
    destruct (cross_iter_e1_e2_cycle N) as [Hv | [Hv | [Hv | Hv]]];
      rewrite Hv in HN; apply Hone.
    - unfold cross_e2, la_zero, cross_product_lie, ex2_vs in HN. simpl in HN.
      exact (f_equal (fun p => snd (fst p)) HN).
    - unfold cross_e3, la_zero, cross_product_lie, ex2_vs in HN. simpl in HN.
      exact (f_equal snd HN).
    - unfold cross_e2, la_neg, la_zero, cross_product_lie, ex2_vs in HN. simpl in HN.
      assert (Hneg1 : cr_neg fld (cr_one fld) = cr_zero fld).
      { exact (f_equal (fun p => snd (fst p)) HN). }
      rewrite <- (cr_neg_neg' fld (cr_one fld)). rewrite Hneg1.
      apply cr_neg_zero'.
    - unfold cross_e3, la_neg, la_zero, cross_product_lie, ex2_vs in HN. simpl in HN.
      assert (Hneg1 : cr_neg fld (cr_one fld) = cr_zero fld).
      { exact (f_equal snd HN). }
      rewrite <- (cr_neg_neg' fld (cr_one fld)). rewrite Hneg1.
      apply cr_neg_zero'.
  Qed.

End CrossProductBasis.

Lemma cross_product_lie_not_abelian {F : Type} (fld : Field F) :
    fld.(cr_one) <> fld.(cr_zero) ->
    ~ (forall u v : F * F * F,
        laF_bracket (cross_product_lie fld) u v = la_zero (cross_product_lie fld)).
Proof.
  intros Hone Habel.
  pose proof (Habel ((cr_one fld, cr_zero fld), cr_zero fld)
                    ((cr_zero fld, cr_one fld), cr_zero fld)) as Hcontra.
  unfold laF_bracket, cross_product_lie, cross_product, ex2_vs, la_zero in Hcontra.
  simpl in Hcontra.
  apply Hone.
  (* Hcontra third component: 1 * 1 + -(0 * 0) = 0. *)
  assert (Heq : fld.(cr_add) (fld.(cr_mul) (cr_one fld) (cr_one fld))
                   (fld.(cr_neg) (fld.(cr_mul) (cr_zero fld) (cr_zero fld))) = cr_zero fld)
    by exact (f_equal snd Hcontra).
  rewrite (cr_mul_one fld) in Heq.
  rewrite cr_mul_zero_l' in Heq.
  rewrite cr_neg_zero' in Heq.
  rewrite (cr_add_zero fld) in Heq.
  exact Heq.
Qed.

(** ** The Heisenberg algebra h_3

    The 3-dimensional Heisenberg Lie algebra over F:
    basis {x, y, z} with [x,y] = z, [x,z] = 0, [y,z] = 0.
    Z = F·z is the center; h_3 = F·x + F·y + F·z.
    The simplest non-abelian nilpotent Lie algebra. *)

Section HeisenbergAlgebra.

  Context {F : Type} (fld : Field F).

  Local Notation "0F" := (cr_zero fld).
  Local Notation "1F" := (cr_one fld).
  Local Notation "x +F y" := (cr_add fld x y) (at level 50).
  Local Notation "x *F y" := (cr_mul fld x y) (at level 40).
  Local Notation "-F x" := (cr_neg fld x) (at level 35).

  (** Register fld for [ring] tactic. *)
  Local Lemma heis_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring heis_fld_ring_inst : heis_ring_theory.

  Definition heis_carrier := (F * F * F)%type.
  Definition heis_mkT (a b c : F) : heis_carrier := ((a, b), c).
  Definition heis_x : heis_carrier := heis_mkT 1F 0F 0F.
  Definition heis_y : heis_carrier := heis_mkT 0F 1F 0F.
  Definition heis_z : heis_carrier := heis_mkT 0F 0F 1F.

  (** Heisenberg bracket: [(a,b,c), (a',b',c')] = (0, 0, a*b' - b*a'). *)
  Definition heis_bracket (u v : heis_carrier) : heis_carrier :=
    let '((a, b), _) := u in
    let '((a', b'), _) := v in
    heis_mkT 0F 0F (a *F b' +F -F (b *F a')).

  Local Ltac heis_bracket_solver :=
    unfold heis_bracket, heis_mkT, ex2_vs; simpl;
    repeat (f_equal; try ring); try ring.

  Definition heis : LieAlgebraF fld heis_carrier.
  Proof.
    refine {|
      laF_vs := ex2_vs fld;
      laF_bracket := heis_bracket;
    |}.
    - intros [[a b] cz] [[a' b'] cz'] [[a'' b''] cz''].
      heis_bracket_solver.
    - intros c [[a b] cz] [[a' b'] cz'].
      heis_bracket_solver.
    - intros [[a b] cz] [[a' b'] cz'] [[a'' b''] cz''].
      heis_bracket_solver.
    - intros c [[a b] cz] [[a' b'] cz'].
      heis_bracket_solver.
    - intros [[a b] cz].
      heis_bracket_solver.
    - intros [[a b] cz] [[a' b'] cz'] [[a'' b''] cz''].
      heis_bracket_solver.
  Defined.

  (** Heisenberg is non-abelian (when 1 ≠ 0): [x, y] = z ≠ 0. *)
  Lemma heis_not_abelian : 1F <> 0F ->
    ~ (forall u v : heis_carrier, heis_bracket u v = la_zero heis).
  Proof.
    intros Hone Habel.
    pose proof (Habel heis_x heis_y) as Hcontra.
    unfold heis_bracket, heis_x, heis_y, heis_mkT, la_zero, heis, ex2_vs in Hcontra.
    simpl in Hcontra.
    apply Hone.
    assert (H1 : 1F *F 1F +F -F (0F *F 0F) = 0F).
    { exact (f_equal snd Hcontra). }
    rewrite (cr_mul_one fld) in H1.
    rewrite cr_mul_zero_l' in H1.
    assert (Hnz : -F 0F = 0F) by apply cr_neg_zero'.
    rewrite Hnz, (cr_add_zero fld) in H1.
    exact H1.
  Qed.

  (** Heisenberg's bracket lands in F·z (the center).
      Hence [heis, heis] ⊆ F·z, and [heis, F·z] = 0, so heis is nilpotent. *)
  Lemma heis_bracket_in_z : forall u v,
    exists c, heis_bracket u v = heis_mkT 0F 0F c.
  Proof.
    intros [[a b] cz] [[a' b'] cz'].
    unfold heis_bracket, heis_mkT.
    exists (a *F b' +F -F (b *F a')). reflexivity.
  Qed.

  (** Bracket of a F·z element (left) with anything is 0. *)
  Lemma heis_bracket_z_zero_l : forall c v,
    heis_bracket (heis_mkT 0F 0F c) v = la_zero heis.
  Proof.
    intros c [[a' b'] cz'].
    unfold heis_bracket, heis_mkT, la_zero, heis, ex2_vs. simpl.
    repeat (f_equal; try ring).
  Qed.

  (** Bracket of anything with a F·z element (right) is 0. *)
  Lemma heis_bracket_z_zero_r : forall c v,
    heis_bracket v (heis_mkT 0F 0F c) = la_zero heis.
  Proof.
    intros c [[a b] cz].
    unfold heis_bracket, heis_mkT, la_zero, heis, ex2_vs. simpl.
    repeat (f_equal; try ring).
  Qed.

  (** Heisenberg is nilpotent (lower_central at level 2 is 0). *)
  Theorem heis_nilpotent : IsNilpotent heis.
  Proof.
    exists 2. intros x Hx.
    (* Need: x = la_zero heis. Use the universal property of bracket_span. *)
    apply (Hx (fun z => z = la_zero heis)).
    - apply zero_ideal.
    - intros a b _ Hb.
      (* Hb : lower_central heis 1 b. Need: heis_bracket a b = 0. *)
      (* lower_central 1 = bracket_span (full) (full). So b is in the span of brackets,
         meaning b ∈ F·z (since all brackets land in F·z). Then [a, b] = 0. *)
      simpl in Hb.
      (* Apply Hb to U = {z | exists c, z = heis_mkT 0F 0F c} *)
      assert (Hbz : exists c, b = heis_mkT 0F 0F c).
      { apply (Hb (fun z => exists c, z = heis_mkT 0F 0F c)).
        - constructor.
          + exists 0F. reflexivity.
          + intros u v [cu Hu] [cv Hv]. exists (cu +F cv).
            rewrite Hu, Hv. unfold heis_mkT, ex2_vs, vsF_add. simpl.
            repeat (f_equal; try ring).
          + intros u [cu Hu]. exists (-F cu).
            rewrite Hu. unfold heis_mkT, ex2_vs, vsF_neg. simpl.
            repeat (f_equal; try ring).
          + intros c u [cu Hu]. exists (c *F cu).
            rewrite Hu. unfold heis_mkT, ex2_vs, vsF_scale. simpl.
            repeat (f_equal; try ring).
          + intros u v [cv Hv].
            (* [u, v] is in F·z because v can be anything but [u, v] always ∈ F·z. *)
            apply heis_bracket_in_z.
        - intros u v _ _. apply heis_bracket_in_z. }
      destruct Hbz as [c Hc]. rewrite Hc.
      apply heis_bracket_z_zero_r.
  Qed.

  (** Heisenberg is solvable (corollary: nilpotent ⟹ solvable). *)
  Corollary heis_solvable : IsSolvable heis.
  Proof. apply nilpotent_is_solvable. apply heis_nilpotent. Qed.

  (** Heisenberg is not simple (since it's solvable). *)
  Corollary heis_not_simple : 1F <> 0F -> ~ IsSimple heis.
  Proof.
    intros _.
    intro Hsimp.
    exact (simple_not_solvable heis Hsimp heis_solvable).
  Qed.

  (** Heisenberg's center is non-trivial: contains z = (0, 0, 1).
      Direct: [u, z] = (0, 0, u_1·1 - u_2·0) = (0, 0, u_1) — wait actually
      bracket is heis_bracket(u, v) = (0, 0, u_1*v_2 - u_2*v_1). For
      v = z = (0, 0, 1), we have v_1 = 0, v_2 = 0, so [u, z] = (0, 0, 0). *)
  Lemma heis_z_central : forall u, heis_bracket u heis_z = la_zero heis.
  Proof. intro u. apply heis_bracket_z_zero_r. Qed.

  (** From left side: [z, v] = 0. *)
  Lemma heis_z_central_l : forall v, heis_bracket heis_z v = la_zero heis.
  Proof.
    intro v. unfold heis_z. apply heis_bracket_z_zero_l.
  Qed.

  (** Heisenberg's z is in the center. *)
  Lemma heis_z_in_center : IsCenter heis heis_z.
  Proof. intro u. apply heis_z_central. Qed.

  (** Heisenberg's center is non-trivial when 1 ≠ 0. *)
  Lemma heis_center_nontrivial : 1F <> 0F ->
    exists z, IsCenter heis z /\ z <> la_zero heis.
  Proof.
    intros Hone.
    exists heis_z. split.
    - apply heis_z_in_center.
    - intro Heq.
      apply Hone.
      unfold heis_z, heis_mkT, la_zero, heis, ex2_vs in Heq.
      simpl in Heq.
      exact (f_equal snd Heq).
  Qed.

  (** Standard Heisenberg bracket: [x, y] = z. *)
  Lemma heis_bracket_xy : heis_bracket heis_x heis_y = heis_z.
  Proof.
    unfold heis_bracket, heis_x, heis_y, heis_z, heis_mkT. simpl.
    repeat (f_equal; try ring).
  Qed.

  (** [y, x] = -z. *)
  Lemma heis_bracket_yx : heis_bracket heis_y heis_x = la_neg heis heis_z.
  Proof.
    unfold heis_bracket, heis_y, heis_x, heis_z, heis_mkT, la_neg, heis, ex2_vs.
    simpl.
    repeat (f_equal; try ring).
  Qed.

  (** Every element of Heisenberg is ad-nilpotent (corollary: heis is
      nilpotent, so by Engel's forward direction every element ad-nilpotent). *)
  Corollary heis_all_ad_nilpotent : forall u, IsAdNilpotent heis u.
  Proof.
    apply nilpotent_all_ad_nilpotent. apply heis_nilpotent.
  Qed.

  (** Heisenberg basis vectors are non-zero (when 1 ≠ 0). *)
  Lemma heis_x_nonzero : 1F <> 0F -> heis_x <> la_zero heis.
  Proof.
    intros Hone Heq.
    apply Hone.
    unfold heis_x, heis_mkT, la_zero, heis, ex2_vs in Heq. simpl in Heq.
    exact (f_equal (fun p => fst (fst p)) Heq).
  Qed.

  Lemma heis_y_nonzero : 1F <> 0F -> heis_y <> la_zero heis.
  Proof.
    intros Hone Heq.
    apply Hone.
    unfold heis_y, heis_mkT, la_zero, heis, ex2_vs in Heq. simpl in Heq.
    exact (f_equal (fun p => snd (fst p)) Heq).
  Qed.

  Lemma heis_z_nonzero : 1F <> 0F -> heis_z <> la_zero heis.
  Proof.
    intros Hone Heq.
    apply Hone.
    unfold heis_z, heis_mkT, la_zero, heis, ex2_vs in Heq. simpl in Heq.
    exact (f_equal snd Heq).
  Qed.

  (** Heisenberg basis vectors are pairwise distinct (when 1 ≠ 0). *)
  Lemma heis_x_neq_y : 1F <> 0F -> heis_x <> heis_y.
  Proof.
    intros Hone Heq.
    apply Hone.
    unfold heis_x, heis_y, heis_mkT in Heq.
    exact (f_equal (fun p => fst (fst p)) Heq).
  Qed.

  Lemma heis_y_neq_z : 1F <> 0F -> heis_y <> heis_z.
  Proof.
    intros Hone Heq.
    apply Hone.
    unfold heis_y, heis_z, heis_mkT in Heq.
    exact (f_equal (fun p => snd (fst p)) Heq).
  Qed.

  Lemma heis_x_neq_z : 1F <> 0F -> heis_x <> heis_z.
  Proof.
    intros Hone Heq.
    apply Hone.
    unfold heis_x, heis_z, heis_mkT in Heq.
    exact (f_equal (fun p => fst (fst p)) Heq).
  Qed.

  (** Every F·z element is central in heis. *)
  Lemma heis_F_z_in_center : forall c : F, IsCenter heis (heis_mkT 0F 0F c).
  Proof.
    intros c u. apply heis_bracket_z_zero_r.
  Qed.

  (** A central element of heis must lie in F·z (first two components zero).
      Proof: [x, u] = (0, 0, b) = 0 forces b = 0. [y, u] = (0, 0, -a) = 0 forces a = 0. *)
  Lemma heis_central_in_F_z : forall u, IsCenter heis u ->
    exists c : F, u = heis_mkT 0F 0F c.
  Proof.
    intros [[a b] cz] Hcen.
    pose proof (Hcen heis_x) as Hbx.
    pose proof (Hcen heis_y) as Hby.
    change (laF_bracket heis heis_x ((a, b), cz)) with
      (heis_bracket heis_x ((a, b), cz)) in Hbx.
    change (laF_bracket heis heis_y ((a, b), cz)) with
      (heis_bracket heis_y ((a, b), cz)) in Hby.
    unfold heis_bracket, heis_x, heis_y, heis_mkT, la_zero, heis, ex2_vs in Hbx, Hby.
    simpl in Hbx, Hby.
    (* Hbx says snd_third_component = 0 of bracket [x, u]. *)
    (* The third component of bracket x u = 1*b - 0*a = b. *)
    (* The third component of bracket y u = 0*b - 1*a = -a. *)
    assert (Hb : b = 0F).
    { pose proof (f_equal snd Hbx) as Hbsnd.
      simpl in Hbsnd.
      (* Hbsnd : 1*b + (-(0*a)) = 0 *)
      assert (Hbeq : b = 1F *F b +F -F (0F *F a)).
      { rewrite (cr_one_mul fld). rewrite (cr_mul_zero_l fld).
        rewrite cr_neg_zero'. rewrite (cr_add_zero fld). reflexivity. }
      rewrite Hbeq. exact Hbsnd. }
    assert (Ha : a = 0F).
    { pose proof (f_equal snd Hby) as Hasnd.
      simpl in Hasnd.
      (* Hasnd : 0*b + (-(1*a)) = 0 *)
      assert (Haeq : -F a = 0F *F b +F -F (1F *F a)).
      { rewrite (cr_one_mul fld). rewrite (cr_mul_zero_l fld).
        rewrite (cr_add_comm fld). rewrite (cr_add_zero fld). reflexivity. }
      assert (Hneg : -F a = 0F).
      { rewrite Haeq. exact Hasnd. }
      rewrite <- (cr_neg_neg' fld a). rewrite Hneg. apply cr_neg_zero'. }
    exists cz. unfold heis_mkT. rewrite Ha, Hb. reflexivity.
  Qed.


  (** heis_x is NOT central: [y, x] = -z ≠ 0. *)
  Lemma heis_x_not_central : 1F <> 0F -> ~ IsCenter heis heis_x.
  Proof.
    intros Hone Hcen.
    pose proof (Hcen heis_y) as Hcontra.
    change (laF_bracket heis heis_y heis_x) with (heis_bracket heis_y heis_x) in Hcontra.
    rewrite heis_bracket_yx in Hcontra.
    apply Hone.
    unfold heis_z, heis_mkT, la_zero, la_neg, heis, ex2_vs in Hcontra.
    simpl in Hcontra.
    assert (Hneg1 : -F 1F = 0F) by exact (f_equal snd Hcontra).
    rewrite <- (cr_neg_neg' fld 1F). rewrite Hneg1.
    apply cr_neg_zero'.
  Qed.

  (** heis_y is NOT central: [x, y] = z ≠ 0. *)
  Lemma heis_y_not_central : 1F <> 0F -> ~ IsCenter heis heis_y.
  Proof.
    intros Hone Hcen.
    pose proof (Hcen heis_x) as Hcontra.
    change (laF_bracket heis heis_x heis_y) with (heis_bracket heis_x heis_y) in Hcontra.
    rewrite heis_bracket_xy in Hcontra.
    apply Hone.
    unfold heis_z, heis_mkT, la_zero, heis, ex2_vs in Hcontra.
    simpl in Hcontra.
    exact (f_equal snd Hcontra).
  Qed.

End HeisenbergAlgebra.
