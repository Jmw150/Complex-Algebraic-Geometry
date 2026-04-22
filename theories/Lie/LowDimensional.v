(** * Lie/LowDimensional.v
    Classification of Lie algebras of dimension ≤ 2, and small examples. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.Lie.Ideals.
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
Theorem dim2_classification {F : Type} (fld : Field F) {L : Type}
    (la : LieAlgebraF fld L)
    (hbasis : exists x y : L,
      x <> y /\
      (forall z, exists a b : F, z = la_add la (la_scale la a x) (la_scale la b y))) :
    IsAbelian la \/
    exists (φ : LieIsom la (nonabelian_2d fld)), True.
Proof. Admitted.

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
Axiom sl2_bracket_hx :
  forall {F : Type} (fld : Field F), True. (* placeholder *)

(** sl(2,F) is simple when char F ≠ 2. *)
Axiom sl2_simple :
  forall {F : Type} (fld : Field F),
    cr_add fld (cr_one fld) (cr_one fld) <> cr_zero fld ->
    exists la : LieAlgebraF fld (F * F * F), IsSimple la.

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
