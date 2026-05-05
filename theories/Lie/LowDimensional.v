(** * Lie/LowDimensional.v
    Classification of Lie algebras of dimension ≤ 2, and small examples. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.Lie.Ideals.
Require Import CAG.Lie.Derivations.
From Stdlib Require Import Ring.

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

(** Every 2-dimensional Lie algebra over F is either abelian or isomorphic
    to the nonabelian 2-dimensional algebra. *)
(* CAG zero-dependent Admitted dim2_classification theories/Lie/LowDimensional.v:411 BEGIN
Theorem dim2_classification {F : Type} (fld : Field F) {L : Type}
    (la : LieAlgebraF fld L)
    (hbasis : exists x y : L,
      x <> y /\
      (forall z, exists a b : F, z = la_add la (la_scale la a x) (la_scale la b y))) :
    IsAbelian la \/
    exists (φ : LieIsom la (nonabelian_2d fld)), True.
Proof. Admitted.
   CAG zero-dependent Admitted dim2_classification theories/Lie/LowDimensional.v:411 END *)

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

Definition mkT {A : Type} (x h y : A) : A * A * A := (x, h, y).

Definition tF_x {F : Type} (u : F * F * F) : F := fst (fst u).
Definition tF_h {F : Type} (u : F * F * F) : F := snd (fst u).
Definition tF_y {F : Type} (u : F * F * F) : F := snd u.

Definition la3_add {F : Type} (fld : Field F)
    (u v : F * F * F) : F * F * F :=
  mkT (cr_add fld (tF_x u) (tF_x v))
      (cr_add fld (tF_h u) (tF_h v))
      (cr_add fld (tF_y u) (tF_y v)).

Definition la3_scale {F : Type} (fld : Field F)
    (c : F) (u : F * F * F) : F * F * F :=
  mkT (cr_mul fld c (tF_x u))
      (cr_mul fld c (tF_h u))
      (cr_mul fld c (tF_y u)).

Definition la3_x {F : Type} (fld : Field F) : F * F * F :=
  mkT (cr_one fld) (cr_zero fld) (cr_zero fld).

Definition la3_h {F : Type} (fld : Field F) : F * F * F :=
  mkT (cr_zero fld) (cr_one fld) (cr_zero fld).

Definition la3_y {F : Type} (fld : Field F) : F * F * F :=
  mkT (cr_zero fld) (cr_zero fld) (cr_one fld).

Lemma la3_x_nonzero {F : Type} (fld : Field F) :
    cr_one fld <> cr_zero fld ->
    la3_x fld <> vsF_zero (ex2_vs fld).
Proof.
  intros Hone H.
  unfold la3_x, mkT, ex2_vs in H. cbn in H.
  apply Hone. exact (f_equal (fun p => fst (fst p)) H).
Qed.

Lemma la3_h_nonzero {F : Type} (fld : Field F) :
    cr_one fld <> cr_zero fld ->
    la3_h fld <> vsF_zero (ex2_vs fld).
Proof.
  intros Hone H.
  unfold la3_h, mkT, ex2_vs in H. cbn in H.
  apply Hone. exact (f_equal (fun p => snd (fst p)) H).
Qed.

Lemma la3_y_nonzero {F : Type} (fld : Field F) :
    cr_one fld <> cr_zero fld ->
    la3_y fld <> vsF_zero (ex2_vs fld).
Proof.
  intros Hone H.
  unfold la3_y, mkT, ex2_vs in H. cbn in H.
  apply Hone. exact (f_equal snd H).
Qed.

Definition la3_bracket {F : Type} (fld : Field F)
    (u v : F * F * F) : F * F * F :=
  let two := cr_add fld (cr_one fld) (cr_one fld) in
  mkT
    (cr_mul fld two
      (cr_add fld
        (cr_mul fld (tF_h u) (tF_x v))
        (cr_neg fld (cr_mul fld (tF_x u) (tF_h v)))))
    (cr_add fld
      (cr_mul fld (tF_x u) (tF_y v))
      (cr_neg fld (cr_mul fld (tF_y u) (tF_x v))))
    (cr_mul fld two
      (cr_add fld
        (cr_mul fld (tF_y u) (tF_h v))
        (cr_neg fld (cr_mul fld (tF_h u) (tF_y v))))).

Section La3LieAlgebra.
  Context {F : Type} (fld : Field F).

  Local Lemma la3_ring_theory : ring_theory (cr_zero fld) (cr_one fld)
    (cr_add fld) (cr_mul fld) (cr_sub fld) (cr_neg fld) eq.
  Proof. apply cr_ring_theory. Qed.

  Add Ring la3_ring : la3_ring_theory.

Definition la3 : LieAlgebraF fld (F * F * F).
Proof.
  refine {|
    laF_vs := ex2_vs fld;
    laF_bracket := la3_bracket fld;
  |}.
  - intros [[x1 xh] xy] [[y1 yh] yy] [[z1 zh] zy].
    unfold la3_bracket, ex2_vs, mkT, tF_x, tF_h, tF_y. cbn.
    apply (f_equal2 pair); [apply (f_equal2 pair)|]; ring.
  - intros a [[x1 xh] xy] [[y1 yh] yy].
    unfold la3_bracket, ex2_vs, mkT, tF_x, tF_h, tF_y. cbn.
    apply (f_equal2 pair); [apply (f_equal2 pair)|]; ring.
  - intros [[x1 xh] xy] [[y1 yh] yy] [[z1 zh] zy].
    unfold la3_bracket, ex2_vs, mkT, tF_x, tF_h, tF_y. cbn.
    apply (f_equal2 pair); [apply (f_equal2 pair)|]; ring.
  - intros a [[x1 xh] xy] [[y1 yh] yy].
    unfold la3_bracket, ex2_vs, mkT, tF_x, tF_h, tF_y. cbn.
    apply (f_equal2 pair); [apply (f_equal2 pair)|]; ring.
  - intros [[x1 xh] xy].
    unfold la3_bracket, ex2_vs, mkT, tF_x, tF_h, tF_y. cbn.
    apply (f_equal2 pair); [apply (f_equal2 pair)|]; ring.
  - intros [[x1 xh] xy] [[y1 yh] yy] [[z1 zh] zy].
    unfold la3_bracket, ex2_vs, mkT, tF_x, tF_h, tF_y. cbn.
    apply (f_equal2 pair); [apply (f_equal2 pair)|]; ring.
Defined.

End La3LieAlgebra.

(** Multiplication table for the sl(2,F) abstract presentation:
    [h,x] = 2x, [h,y] = -2y, [x,y] = h.

    This is the *abstract* sl(2) bracket relation (cf. SpecialLinear.v
    for the matrix realization). Stated as a Conjecture: any 3-dimensional
    Lie algebra with basis (x,h,y) satisfying these relations is
    isomorphic to sl(2,F). Reference: Humphreys §2.1. *)
(* CAG zero-dependent Conjecture sl2_bracket_hx theories/Lie/LowDimensional.v:773 BEGIN
Conjecture sl2_bracket_hx :
  forall {F : Type} (fld : Field F),
    exists (la : LieAlgebraF fld (F * F * F)) (x h y : F * F * F),
      laF_bracket la h x = vsF_scale (laF_vs la)
                             (fld.(cr_add) fld.(cr_one) fld.(cr_one)) x /\
      laF_bracket la x y = h.
   CAG zero-dependent Conjecture sl2_bracket_hx theories/Lie/LowDimensional.v:773 END *)


(** sl(2,F) is simple when char F ≠ 2. *)
(* CAG zero-dependent Axiom sl2_simple theories/Lie/LowDimensional.v:668 BEGIN
Axiom sl2_simple :
  forall {F : Type} (fld : Field F),
    cr_add fld (cr_one fld) (cr_one fld) <> cr_zero fld ->
    exists la : LieAlgebraF fld (F * F * F), IsSimple la.
   CAG zero-dependent Axiom sl2_simple theories/Lie/LowDimensional.v:668 END *)

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
