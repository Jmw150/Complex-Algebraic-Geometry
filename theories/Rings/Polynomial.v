(** * Polynomial.v — Polynomial ring R[x] over a base ring R

    Represents polynomials as lists of coefficients, lowest-degree first.
    Example: [a0; a1; a2] = a0 + a1 x + a2 x^2.

    Provides:
      - Operations: padd, pmul, pneg, pzero, pone, pscale, peval
      - Additive laws: padd is associative, commutative, has pzero as identity
      - Multiplicative laws: distributivity, pone is identity
      - Negation: padd p (pneg p) yields a list of zeros (not [] in general,
                  due to the redundant list representation)
      - Formal derivative D : Polynomial R -> Polynomial R
      - D_add (additivity) on the nose
      - D_mul_pequiv (Leibniz rule) — proven theorem under setoid equivalence
        (the Leibniz form fails due to trailing-zero asymmetries)

    Representation note: the list representation is redundant ([a; 0] and
    [a] denote the same polynomial). The additive structure (padd) is
    engineered so that all *positively-stated* additive laws hold exactly:
        padd_assoc, padd_comm, padd_zero_r, padd_zero_l.
    The negation law [padd p (pneg p) = pzero] does NOT hold on the nose
    (LHS is a list of zeros of length [length p]); we provide
    [padd_neg_zerolist] which says padd p (pneg p) is a "zero list".
    A future refinement can quotient by the trailing-zero relation to
    produce a true [Ring (Polynomial R)] instance. *)

From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Setoid Morphisms.
Import ListNotations.
Require Import CAG.Rings.Ring.

(* ================================================================== *)
(** ** Carrier and basic operations *)
(* ================================================================== *)

Definition Polynomial (R : Type) : Type := list R.

Definition pzero {R : Type} : Polynomial R := nil.

Section PolyOps.
  Context {R : Type} (r : Ring R).

  Definition pone : Polynomial R := cons (rone R r) nil.

  (** Coefficient-wise addition. *)
  Fixpoint padd (p q : Polynomial R) : Polynomial R :=
    match p, q with
    | nil, _ => q
    | _, nil => p
    | cons a p', cons b q' => cons (radd R r a b) (padd p' q')
    end.

  Fixpoint pneg (p : Polynomial R) : Polynomial R :=
    match p with
    | nil => nil
    | cons a p' => cons (rneg R r a) (pneg p')
    end.

  Fixpoint pscale (c : R) (p : Polynomial R) : Polynomial R :=
    match p with
    | nil => nil
    | cons a p' => cons (rmul R r c a) (pscale c p')
    end.

  (** Multiplication: convolution. We special-case nil on either side to
      avoid producing trailing zeros from (a)*(0). *)
  Fixpoint pmul (p q : Polynomial R) : Polynomial R :=
    match p with
    | nil => nil
    | cons a p' =>
        match q with
        | nil => nil
        | _ => padd (pscale a q) (cons (rzero R r) (pmul p' q))
        end
    end.

  Fixpoint peval (p : Polynomial R) (x : R) : R :=
    match p with
    | nil => rzero R r
    | cons a p' => radd R r a (rmul R r x (peval p' x))
    end.

End PolyOps.

(* ================================================================== *)
(** ** Additive ring laws *)
(* ================================================================== *)

Section PolyAdd.
  Context {R : Type} (r : Ring R).

  Lemma padd_nil_l : forall p, padd r nil p = p.
  Proof. intro p; destruct p; reflexivity. Qed.

  Lemma padd_nil_r : forall p, padd r p nil = p.
  Proof. intro p; destruct p; reflexivity. Qed.

  Lemma padd_comm : forall p q, padd r p q = padd r q p.
  Proof.
    induction p as [|a p IH]; intros q.
    - rewrite padd_nil_l, padd_nil_r; reflexivity.
    - destruct q as [|b q]; [reflexivity|].
      simpl. rewrite (radd_comm R r a b), (IH q); reflexivity.
  Qed.

  Lemma padd_assoc : forall p q s,
      padd r p (padd r q s) = padd r (padd r p q) s.
  Proof.
    induction p as [|a p IH]; intros q s.
    - rewrite !padd_nil_l; reflexivity.
    - destruct q as [|b q].
      + rewrite padd_nil_r, padd_nil_l; reflexivity.
      + destruct s as [|c s].
        * rewrite !padd_nil_r; reflexivity.
        * simpl. rewrite (radd_assoc R r a b c), (IH q s); reflexivity.
  Qed.

  Lemma padd_zero_r : forall p, padd r p pzero = p.
  Proof. apply padd_nil_r. Qed.

  Lemma padd_zero_l : forall p, padd r pzero p = p.
  Proof. apply padd_nil_l. Qed.

  (** "Zero list of length n". *)
  Fixpoint zlist (n : nat) : Polynomial R :=
    match n with
    | O => nil
    | S k => cons (rzero R r) (zlist k)
    end.

  (** padd p (pneg p) is a zero list of length [length p], NOT [pzero]
      in general (the list representation has trailing zeros). *)
  Lemma padd_neg_zlist : forall p, padd r p (pneg r p) = zlist (length p).
  Proof.
    induction p as [|a p IH]; [reflexivity|].
    simpl. rewrite (radd_neg_r R r a), IH; reflexivity.
  Qed.

End PolyAdd.

(* ================================================================== *)
(** ** Properties of pscale and pneg *)
(* ================================================================== *)

Section PolyScale.
  Context {R : Type} (r : Ring R).

  Lemma pscale_padd : forall c p q,
      pscale r c (padd r p q) = padd r (pscale r c p) (pscale r c q).
  Proof.
    intros c. induction p as [|a p IH]; intros q.
    - rewrite !padd_nil_l; reflexivity.
    - destruct q as [|b q].
      + rewrite !padd_nil_r; reflexivity.
      + simpl. rewrite (rmul_distrib_l R r c a b), (IH q); reflexivity.
  Qed.

  Lemma pscale_radd : forall a b p,
      pscale r (radd R r a b) p = padd r (pscale r a p) (pscale r b p).
  Proof.
    intros a b. induction p as [|c p IH]; [reflexivity|].
    simpl. rewrite (rmul_distrib_r R r a b c), IH; reflexivity.
  Qed.

  Lemma pscale_one_l : forall p, pscale r (rone R r) p = p.
  Proof.
    induction p as [|a p IH]; [reflexivity|].
    simpl. rewrite (rmul_one_l R r a), IH; reflexivity.
  Qed.

  Lemma pneg_padd : forall p q,
      pneg r (padd r p q) = padd r (pneg r p) (pneg r q).
  Proof.
    induction p as [|a p IH]; intros q.
    - rewrite !padd_nil_l; reflexivity.
    - destruct q as [|b q].
      + rewrite !padd_nil_r; reflexivity.
      + simpl. f_equal; [|apply IH].
        (* Show -(a+b) = -a + -b via inverse uniqueness. *)
        assert (Hinv : forall u v : R,
                   radd R r u v = rzero R r -> v = rneg R r u).
        { intros u v Huv.
          transitivity (radd R r (rzero R r) v).
          { symmetry; apply (radd_zero_l r). }
          rewrite <- (radd_neg_l r u), <- (radd_assoc R r), Huv.
          apply (radd_zero_r R r). }
        symmetry. apply Hinv.
        (* Goal: (a + b) + (-a + -b) = 0 *)
        (* Rewrite as a + (b + (-a + -b)). *)
        rewrite <- (radd_assoc R r a b (radd R r (rneg R r a) (rneg R r b))).
        (* Goal: a + (b + (-a + -b)) = 0
           Rewrite b + (-a + -b) = (b + -a) + -b. *)
        rewrite (radd_assoc R r b (rneg R r a) (rneg R r b)).
        (* Now: a + ((b + -a) + -b) = 0
           Swap b + -a to -a + b. *)
        rewrite (radd_comm R r b (rneg R r a)).
        (* Now: a + ((-a + b) + -b) = 0
           Re-associate: (-a + b) + -b = -a + (b + -b) *)
        rewrite <- (radd_assoc R r (rneg R r a) b (rneg R r b)).
        rewrite (radd_neg_r R r b).
        rewrite (radd_zero_r R r (rneg R r a)).
        apply (radd_neg_r R r a).
  Qed.

End PolyScale.

(* ================================================================== *)
(** ** Multiplicative properties *)
(* ================================================================== *)

Section PolyMul.
  Context {R : Type} (r : Ring R).

  Lemma pmul_nil_l : forall q, pmul r nil q = nil.
  Proof. reflexivity. Qed.

  Lemma pmul_nil_r : forall p, pmul r p nil = nil.
  Proof. intro p. destruct p; reflexivity. Qed.

  (** pone is a left identity. *)
  Lemma pmul_one_l : forall p, pmul r (pone r) p = p.
  Proof.
    intro p. unfold pone. destruct p as [|a p]; [reflexivity|].
    simpl. rewrite (rmul_one_l R r a).
    rewrite (pscale_one_l r p).
    simpl. rewrite (radd_zero_r R r a), padd_nil_r; reflexivity.
  Qed.

  (** pone is a right identity (Leibniz). *)
  Lemma pmul_one_r : forall p, pmul r p (pone r) = p.
  Proof.
    induction p as [|a p IH]; [reflexivity|].
    unfold pone.
    (* pmul (a::p) [1] = padd (cons (a*1) nil) (cons 0 (pmul p [1])). *)
    change (pmul r (cons a p) (cons (rone R r) nil))
      with (padd r (cons (rmul R r a (rone R r)) nil)
                   (cons (rzero R r) (pmul r p (cons (rone R r) nil)))).
    fold (pone r). rewrite IH.
    rewrite (rmul_one_r R r a).
    (* Goal: padd (cons a nil) (cons 0 p) = cons a p. *)
    change (padd r (cons a nil) (cons (rzero R r) p))
      with (cons (radd R r a (rzero R r)) (padd r nil p)).
    rewrite (radd_zero_r R r a).
    rewrite padd_nil_l. reflexivity.
  Qed.

  (** Helper: padd of two cons-zero lists is cons-zero of padd. *)
  Lemma cons_zero_padd : forall p q,
      padd r (cons (rzero R r) p) (cons (rzero R r) q)
    = cons (rzero R r) (padd r p q).
  Proof.
    intros p q. simpl. rewrite (radd_zero_r R r); reflexivity.
  Qed.

  (** Distributivity of pmul over padd on the right. *)
  Lemma pmul_padd_r : forall p q s,
      pmul r p (padd r q s) = padd r (pmul r p q) (pmul r p s).
  Proof.
    induction p as [|a p IH]; intros q s; [reflexivity|].
    destruct q as [|qa q'].
    { rewrite (padd_nil_l r s).
      change (pmul r (cons a p) s = padd r (pmul r (cons a p) nil) (pmul r (cons a p) s)).
      rewrite (pmul_nil_r (cons a p)), padd_nil_l; reflexivity. }
    destruct s as [|sa s'].
    { rewrite (padd_nil_r r).
      change (pmul r (cons a p) (cons qa q')
            = padd r (pmul r (cons a p) (cons qa q')) (pmul r (cons a p) nil)).
      rewrite (pmul_nil_r (cons a p)), padd_nil_r; reflexivity. }
    (* Unfold the LHS pmul: it doesn't simplify cleanly because q is not
       syntactically a cons (it's [padd r (qa::q') (sa::s')]). We rewrite
       explicitly using the unfolded form. *)
    assert (Hlhs : pmul r (cons a p) (padd r (cons qa q') (cons sa s'))
                 = padd r (pscale r a (padd r (cons qa q') (cons sa s')))
                          (cons (rzero R r) (pmul r p (padd r (cons qa q') (cons sa s'))))).
    { simpl padd. reflexivity. }
    rewrite Hlhs.
    rewrite (pscale_padd r a (cons qa q') (cons sa s')).
    rewrite (IH (cons qa q') (cons sa s')).
    assert (Hrhs1 : pmul r (cons a p) (cons qa q')
                  = padd r (pscale r a (cons qa q'))
                           (cons (rzero R r) (pmul r p (cons qa q')))).
    { reflexivity. }
    assert (Hrhs2 : pmul r (cons a p) (cons sa s')
                  = padd r (pscale r a (cons sa s'))
                           (cons (rzero R r) (pmul r p (cons sa s')))).
    { reflexivity. }
    rewrite Hrhs1, Hrhs2.
    rewrite <- (cons_zero_padd (pmul r p (cons qa q')) (pmul r p (cons sa s'))).
    set (A := pscale r a (cons qa q')).
    set (B := pscale r a (cons sa s')).
    set (C := cons (rzero R r) (pmul r p (cons qa q'))).
    set (D := cons (rzero R r) (pmul r p (cons sa s'))).
    rewrite <- (padd_assoc r A B (padd r C D)).
    rewrite (padd_assoc r B C D).
    rewrite (padd_comm r B C).
    rewrite <- (padd_assoc r C B D).
    rewrite (padd_assoc r A C (padd r B D)).
    reflexivity.
  Qed.

  (** Distributivity on the left. *)
  Lemma pmul_padd_l : forall p q s,
      pmul r (padd r p q) s = padd r (pmul r p s) (pmul r q s).
  Proof.
    induction p as [|a p IH]; intros q s.
    - simpl. destruct (pmul r q s); reflexivity.
    - destruct q as [|b q].
      + simpl padd. destruct s as [|sh st]; [reflexivity|]. simpl. reflexivity.
      + destruct s as [|sa s'].
        { rewrite !pmul_nil_r. simpl. reflexivity. }
        (* Reduce outer padd then unfold pmul. *)
        simpl padd at 1.
        change (pmul r (cons (radd R r a b) (padd r p q)) (cons sa s'))
          with (padd r (pscale r (radd R r a b) (cons sa s'))
                       (cons (rzero R r) (pmul r (padd r p q) (cons sa s')))).
        rewrite (pscale_radd r a b (cons sa s')).
        rewrite (IH q (cons sa s')).
        rewrite <- (cons_zero_padd (pmul r p (cons sa s'))
                                    (pmul r q (cons sa s'))).
        set (A := pscale r a (cons sa s')).
        set (B := pscale r b (cons sa s')).
        set (C := cons (rzero R r) (pmul r p (cons sa s'))).
        set (D := cons (rzero R r) (pmul r q (cons sa s'))).
        rewrite <- (padd_assoc r A B (padd r C D)).
        rewrite (padd_assoc r B C D).
        rewrite (padd_comm r B C).
        rewrite <- (padd_assoc r C B D).
        rewrite (padd_assoc r A C (padd r B D)).
        reflexivity.
  Qed.

End PolyMul.

(* ================================================================== *)
(** ** Formal derivative *)
(* ================================================================== *)

Section PolyDeriv.
  Context {R : Type} (r : Ring R).

  (** Iterated addition: ntimes n a = a + a + ... + a (n copies). *)
  Fixpoint ntimes (n : nat) (a : R) : R :=
    match n with
    | O => rzero R r
    | S k => radd R r a (ntimes k a)
    end.

  (** Multiply each element of [p] by its position-from-base [idx, idx+1, ...]. *)
  Fixpoint mult_by_index_from (idx : nat) (p : Polynomial R) : Polynomial R :=
    match p with
    | nil => nil
    | cons a p' => cons (ntimes idx a) (mult_by_index_from (S idx) p')
    end.

  (** Derivative: drop a0, then multiply ai by i. *)
  Definition D (p : Polynomial R) : Polynomial R :=
    match p with
    | nil => nil
    | cons _ p' => mult_by_index_from 1 p'
    end.

  (** ** Properties of ntimes *)

  Lemma ntimes_zero : forall n, ntimes n (rzero R r) = rzero R r.
  Proof.
    induction n as [|n IH]; [reflexivity|].
    simpl. rewrite IH. apply (radd_zero_r R r).
  Qed.

  Lemma ntimes_add : forall n a b,
      ntimes n (radd R r a b) = radd R r (ntimes n a) (ntimes n b).
  Proof.
    induction n as [|n IH]; intros a b.
    - simpl. symmetry. apply (radd_zero_r R r).
    - simpl. rewrite (IH a b).
      rewrite <- (radd_assoc R r a b (radd R r (ntimes n a) (ntimes n b))).
      rewrite (radd_assoc R r b (ntimes n a) (ntimes n b)).
      rewrite (radd_comm R r b (ntimes n a)).
      rewrite <- (radd_assoc R r (ntimes n a) b (ntimes n b)).
      rewrite (radd_assoc R r a (ntimes n a) (radd R r b (ntimes n b))).
      reflexivity.
  Qed.

  (** ** D_add: derivative is additive. *)

  Lemma mult_by_index_from_add : forall idx p q,
      mult_by_index_from idx (padd r p q)
    = padd r (mult_by_index_from idx p) (mult_by_index_from idx q).
  Proof.
    intros idx p q. revert idx q.
    induction p as [|a p IH]; intros idx q.
    - simpl mult_by_index_from at 2. simpl padd at 2.
      destruct q as [|b q]; reflexivity.
    - destruct q as [|b q].
      + simpl padd.
        simpl mult_by_index_from.
        destruct (mult_by_index_from (S idx) p); reflexivity.
      + simpl. rewrite (ntimes_add idx a b), (IH (S idx) q); reflexivity.
  Qed.

  Lemma D_add : forall p q, D (padd r p q) = padd r (D p) (D q).
  Proof.
    intros p q. unfold D.
    destruct p as [|a p]; destruct q as [|b q].
    - reflexivity.
    - simpl padd. destruct (mult_by_index_from 1 q); reflexivity.
    - simpl padd. destruct (mult_by_index_from 1 p); reflexivity.
    - simpl padd at 1.
      apply mult_by_index_from_add.
  Qed.

End PolyDeriv.

(* ================================================================== *)
(** ** Leibniz rule for D *)
(* ================================================================== *)

Section LeibnizRule.
  Context {R : Type} (r : Ring R).

  (** Increasing the start index by 1 in mult_by_index_from adds [p] once. *)
  Lemma mift_shift : forall idx p,
      mult_by_index_from r (S idx) p = padd r p (mult_by_index_from r idx p).
  Proof.
    intros idx p. revert idx.
    induction p as [|a p IH]; intro idx; [reflexivity|].
    simpl. f_equal. apply IH.
  Qed.

  (** [ntimes] interacts with multiplication. *)
  Lemma ntimes_rmul_l : forall n c a,
      ntimes r n (rmul R r c a) = rmul R r c (ntimes r n a).
  Proof.
    intros n c a. induction n as [|n IH]; simpl.
    - symmetry. apply rmul_zero_r.
    - rewrite IH. symmetry. apply rmul_distrib_l.
  Qed.

  (** mult_by_index_from commutes with pscale on the left. *)
  Lemma mift_pscale : forall idx c p,
      mult_by_index_from r idx (pscale r c p)
      = pscale r c (mult_by_index_from r idx p).
  Proof.
    intros idx c p. revert idx.
    induction p as [|a p IH]; intro idx; [reflexivity|].
    simpl. f_equal.
    - apply ntimes_rmul_l.
    - apply IH.
  Qed.

  (** D commutes with pscale on the left. *)
  Lemma D_scale : forall c p, D r (pscale r c p) = pscale r c (D r p).
  Proof.
    intros c p. unfold D. destruct p as [|a p]; [reflexivity|]. apply mift_pscale.
  Qed.

  (** Iterated [pscale] uses ring multiplication. *)
  Lemma pscale_pscale : forall x y p,
      pscale r (rmul R r x y) p = pscale r x (pscale r y p).
  Proof.
    intros x y p. induction p as [|a p IH]; [reflexivity|].
    simpl. rewrite IH. f_equal. symmetry. apply (rmul_assoc R r).
  Qed.

  (** [pscale] of a cons-zero list. *)
  Lemma pscale_cons_zero : forall c p,
      pscale r c (cons (rzero R r) p) = cons (rzero R r) (pscale r c p).
  Proof. intros c p. simpl. f_equal. apply rmul_zero_r. Qed.

  (** [pmul] interacts with [pscale] on the left. *)
  Lemma pmul_pscale_l : forall c p q,
      pmul r (pscale r c p) q = pscale r c (pmul r p q).
  Proof.
    intros c p q. revert q.
    induction p as [|a p IH]; intro q; [reflexivity|].
    destruct q as [|b q]; [reflexivity|].
    (* Manually unfold both sides one step. *)
    transitivity (padd r (pscale r (rmul R r c a) (cons b q))
                          (cons (rzero R r) (pmul r (pscale r c p) (cons b q)))).
    { reflexivity. }
    rewrite (IH (cons b q)).
    transitivity (pscale r c (padd r (pscale r a (cons b q))
                                      (cons (rzero R r) (pmul r p (cons b q))))).
    2: { reflexivity. }
    rewrite pscale_padd. f_equal.
    - apply pscale_pscale.
    - symmetry. apply pscale_cons_zero.
  Qed.

  (** Express [mult_by_index_from 1 s] in terms of [D] for non-nil [s]. *)
  Lemma mift1_cons : forall a s,
      mult_by_index_from r 1 (cons a s)
      = padd r (cons a s) (cons (rzero R r) (D r (cons a s))).
  Proof.
    intros a s.
    (* LHS reduces to ((1)*a) :: mift 2 s = (a + 0) :: mift 2 s. *)
    cbn [mult_by_index_from ntimes].
    rewrite (radd_zero_r R r).
    (* Now: a :: mift 2 s. We rewrite mift 2 s = padd s (mift 1 s). *)
    rewrite mift_shift.
    (* RHS: padd (a::s) (0 :: D(a::s)). D(a::s) = mift 1 s. *)
    cbn [D padd].
    rewrite (radd_zero_r R r). reflexivity.
  Qed.

  (** mift 1 of a non-nil polynomial expressed via D. *)
  Lemma mift1_via_D : forall s,
      match s with
      | nil => True
      | _ => mult_by_index_from r 1 s = padd r s (cons (rzero R r) (D r s))
      end.
  Proof.
    intro s. destruct s as [|a s']; [exact I|]. apply mift1_cons.
  Qed.

End LeibnizRule.

(** The Leibniz rule [D(p*q) = D p * q + p * D q] is FALSE as a Leibniz
    equality in our list-rep due to trailing-zero asymmetries; see
    [D_mul_pequiv] below for the (proven) setoid-equivalence form, which
    holds in any commutative ring. *)

(* ================================================================== *)
(** ** Evaluation homomorphism (universal direction)

    Over a general (non-commutative) ring, [peval] is additive but does
    NOT preserve multiplication or scaling without further hypotheses on
    [x] (e.g. [x] commuting with all coefficients). We therefore prove
    only the additive part here. The multiplicative part is given below
    in a separate section assuming a [CommutativeRing]. *)
(* ================================================================== *)

Section PolyEval.
  Context {R : Type} (r : Ring R).

  Lemma peval_pzero : forall x, peval r pzero x = rzero R r.
  Proof. reflexivity. Qed.

  Lemma peval_pone : forall x, peval r (pone r) x = rone R r.
  Proof.
    intro x. unfold pone, peval.
    rewrite (rmul_zero_r r x).
    apply (radd_zero_r R r).
  Qed.

  Lemma peval_padd : forall p q x,
      peval r (padd r p q) x = radd R r (peval r p x) (peval r q x).
  Proof.
    induction p as [|a p IH]; intros q x.
    - rewrite (padd_nil_l r q). simpl.
      symmetry. apply (radd_zero_l r).
    - destruct q as [|b q].
      + rewrite (padd_nil_r r). simpl.
        symmetry. apply (radd_zero_r R r).
      + simpl. rewrite (IH q x).
        rewrite (rmul_distrib_l R r x (peval r p x) (peval r q x)).
        (* Goal: (a+b) + (x*P + x*Q) = (a + x*P) + (b + x*Q). *)
        set (P := rmul R r x (peval r p x)).
        set (Q := rmul R r x (peval r q x)).
        rewrite <- (radd_assoc R r a b (radd R r P Q)).
        rewrite (radd_assoc R r b P Q).
        rewrite (radd_comm R r b P).
        rewrite <- (radd_assoc R r P b Q).
        rewrite (radd_assoc R r a P (radd R r b Q)).
        reflexivity.
  Qed.

  Lemma peval_pneg : forall p x,
      peval r (pneg r p) x = rneg R r (peval r p x).
  Proof.
    induction p as [|a p IH]; intro x.
    - simpl. symmetry.
      (* -0 = 0 follows from 0 + (-0) = 0 and 0 + (-0) = -0. *)
      assert (H0 : radd R r (rzero R r) (rneg R r (rzero R r)) = rzero R r)
        by apply (radd_neg_r R r).
      rewrite (radd_zero_l r) in H0. exact H0.
    - simpl. rewrite (IH x).
      (* Goal: -a + x*(-P) = -(a + x*P). *)
      (* Show by additive uniqueness: (a + x*P) + (-a + x*(-P)) = 0. *)
      assert (Hinv : forall u v : R,
                 radd R r u v = rzero R r -> v = rneg R r u).
      { intros u v Huv.
        transitivity (radd R r (rzero R r) v).
        { symmetry; apply (radd_zero_l r). }
        rewrite <- (radd_neg_l r u), <- (radd_assoc R r), Huv.
        apply (radd_zero_r R r). }
      apply Hinv.
      (* Goal: (a + x*P) + (-a + x*(-P)) = 0. *)
      set (P := peval r p x).
      (* Prove x*(-P) = -(x*P) first. *)
      assert (HxP : rmul R r x (rneg R r P) = rneg R r (rmul R r x P)).
      { apply Hinv.
        rewrite <- (rmul_distrib_l R r x P (rneg R r P)).
        rewrite (radd_neg_r R r P).
        apply (rmul_zero_r r). }
      rewrite HxP.
      (* Goal: (a + xP) + (-a + -(xP)) = 0. *)
      rewrite <- (radd_assoc R r a (rmul R r x P)
                              (radd R r (rneg R r a) (rneg R r (rmul R r x P)))).
      rewrite (radd_assoc R r (rmul R r x P) (rneg R r a) (rneg R r (rmul R r x P))).
      rewrite (radd_comm R r (rmul R r x P) (rneg R r a)).
      rewrite <- (radd_assoc R r (rneg R r a) (rmul R r x P) (rneg R r (rmul R r x P))).
      rewrite (radd_neg_r R r (rmul R r x P)).
      rewrite (radd_zero_r R r (rneg R r a)).
      apply (radd_neg_r R r a).
  Qed.

End PolyEval.

(* ================================================================== *)
(** ** Helpers about [mult_by_index_from] and [peval] (any ring) *)
(* ================================================================== *)

Section PevalMiftHelpers.
  Context {R : Type} (r : Ring R).

  (** Shifting the index in [mult_by_index_from] adds [p] to peval. *)
  Lemma peval_mift_shift : forall idx p x,
      peval r (mult_by_index_from r (S idx) p) x =
      radd R r (peval r p x) (peval r (mult_by_index_from r idx p) x).
  Proof.
    intros idx p x.
    rewrite (mift_shift r idx p).
    apply (peval_padd r).
  Qed.

  (** [ntimes 1] is the identity (for any element). *)
  Lemma ntimes_one : forall a, ntimes r 1 a = a.
  Proof. intro a. simpl. apply (radd_zero_r R r). Qed.

  (** [peval (mift 0 p) x = x * peval (D p) x]. *)
  Lemma peval_mift_zero : forall p x,
      peval r (mult_by_index_from r 0 p) x =
      rmul R r x (peval r (D r p) x).
  Proof.
    induction p as [|a p IH]; intro x.
    - simpl. symmetry. apply (rmul_zero_r r).
    - simpl mult_by_index_from. simpl peval. simpl D.
      simpl ntimes. rewrite (radd_zero_l r).
      reflexivity.
  Qed.

  (** [peval (D (cons a p)) x = peval p x + x * peval (D p) x] (independent of a!). *)
  Lemma peval_D_cons : forall a p x,
      peval r (D r (cons a p)) x =
      radd R r (peval r p x) (rmul R r x (peval r (D r p) x)).
  Proof.
    intros a p x.
    change (D r (cons a p)) with (mult_by_index_from r 1 p).
    rewrite (peval_mift_shift 0 p x).
    rewrite peval_mift_zero.
    reflexivity.
  Qed.

  (** Specialization: a = 0. *)
  Lemma peval_D_cons_zero : forall p x,
      peval r (D r (cons (rzero R r) p)) x =
      radd R r (peval r p x) (rmul R r x (peval r (D r p) x)).
  Proof. intros. apply peval_D_cons. Qed.

End PevalMiftHelpers.

(* ================================================================== *)
(** ** Multiplicative evaluation in a commutative ring *)
(* ================================================================== *)

Section PolyEvalCom.
  Context {R : Type} (cr : CommutativeRing R).

  Notation r := (cring R cr).

  (** In a commutative ring, evaluation commutes with scaling. *)
  Lemma peval_pscale_com : forall c p x,
      peval r (pscale r c p) x = rmul R r c (peval r p x).
  Proof.
    intros c p x. induction p as [|a p IH].
    - simpl. symmetry. apply (rmul_zero_r r).
    - simpl. rewrite IH.
      rewrite (rmul_distrib_l R r c a (rmul R r x (peval r p x))).
      f_equal.
      (* Goal: x * (c * peval p x) = c * (x * peval p x). *)
      rewrite (rmul_assoc R r x c (peval r p x)).
      rewrite (rmul_comm R cr x c).
      rewrite <- (rmul_assoc R r c x (peval r p x)).
      reflexivity.
  Qed.

  Lemma peval_pmul_com : forall p q x,
      peval r (pmul r p q) x
    = rmul R r (peval r p x) (peval r q x).
  Proof.
    induction p as [|a p IH]; intros q x.
    - simpl. symmetry. apply (rmul_zero_l r).
    - destruct q as [|b q].
      + rewrite (pmul_nil_r r). simpl. symmetry. apply (rmul_zero_r r).
      + (* pmul (a::p) (b::q) = padd (pscale a (b::q)) (0 :: pmul p (b::q)). *)
        change (pmul r (cons a p) (cons b q))
          with (padd r (pscale r a (cons b q))
                       (cons (rzero R r) (pmul r p (cons b q)))).
        rewrite (peval_padd r).
        rewrite (peval_pscale_com a (cons b q) x).
        (* peval (0 :: pmul p (b::q)) x = 0 + x*peval(pmul p (b::q)) x. *)
        change (peval r (cons (rzero R r) (pmul r p (cons b q))) x)
          with (radd R r (rzero R r)
                         (rmul R r x (peval r (pmul r p (cons b q)) x))).
        rewrite (radd_zero_l r).
        rewrite (IH (cons b q) x).
        (* Now LHS = a*peval(b::q) + x*(peval p * peval(b::q)).
           RHS = (a + x*peval p)*peval(b::q)
               = a*peval(b::q) + (x*peval p)*peval(b::q). *)
        rewrite (rmul_assoc R r x (peval r p x) (peval r (cons b q) x)).
        rewrite <- (rmul_distrib_r R r a (rmul R r x (peval r p x))
                                  (peval r (cons b q) x)).
        reflexivity.
  Qed.

  (** [pmul] is commutative under evaluation in a commutative ring. *)
  Theorem peval_pmul_comm : forall p q x,
      peval r (pmul r p q) x = peval r (pmul r q p) x.
  Proof.
    intros p q x.
    rewrite (peval_pmul_com p q x), (peval_pmul_com q p x).
    apply (rmul_comm R cr).
  Qed.

  (** Polynomial multiplication is associative under evaluation. *)
  Theorem peval_pmul_assoc : forall p q s x,
      peval r (pmul r (pmul r p q) s) x = peval r (pmul r p (pmul r q s)) x.
  Proof.
    intros p q s x.
    rewrite (peval_pmul_com (pmul r p q) s x).
    rewrite (peval_pmul_com p q x).
    rewrite (peval_pmul_com p (pmul r q s) x).
    rewrite (peval_pmul_com q s x).
    symmetry. apply (rmul_assoc R r).
  Qed.

End PolyEvalCom.

(* ================================================================== *)
(** ** Divided differences and the Factor Theorem

    In a commutative ring, the evaluation map at any point exhibits a
    divided-difference structure:

        p(x) - p(a) = (x - a) * q(x)

    where [q] is computed structurally from [p] and [a]. As a corollary,
    if [p(a) = 0] then [p(x) = (x - a) * q(x)]. *)
(* ================================================================== *)

Section FactorTheorem.
  Context {R : Type} (cr : CommutativeRing R).

  Notation r := (cring R cr).

  (** [divided_diff_q a p] is the polynomial [q] such that
      [p(x) - p(a) = (x - a) * q(x)]. By induction on the list
      representation. *)
  Fixpoint divided_diff_q (a : R) (p : Polynomial R) : Polynomial R :=
    match p with
    | nil => nil
    | cons _ p' => cons (peval r p' a) (divided_diff_q a p')
    end.

  (** The defining equation: in a commutative ring,
      [p(x) = p(a) + (x - a) * q(x)] where [q = divided_diff_q a p]. *)
  Theorem divided_diff_eq : forall p a x,
      peval r p x =
      radd R r (peval r p a)
               (rmul R r (radd R r x (rneg R r a))
                         (peval r (divided_diff_q a p) x)).
  Proof.
    induction p as [|c p IH]; intros a x.
    - simpl. rewrite (rmul_zero_r r). symmetry. apply (radd_zero_r R r).
    - (* Unfold peval on both sides by one step. *)
      simpl peval. simpl divided_diff_q. simpl peval.
      (* Replace peval p x by p(a) + (x-a) * q(x). *)
      rewrite (IH a x).
      (* Set abbreviations after IH-rewrite. *)
      set (P := peval r p a).
      set (Q := peval r (divided_diff_q a p) x).
      set (XmA := radd R r x (rneg R r a)).
      (* Goal: c + x*(P + (x-a)*Q) = (c + a*P) + (x-a)*(P + x*Q). *)
      rewrite (rmul_distrib_l R r x P (rmul R r XmA Q)).
      rewrite (rmul_distrib_l R r XmA P (rmul R r x Q)).
      (* Goal: c + (x*P + x*((x-a)*Q)) = (c + a*P) + ((x-a)*P + (x-a)*(x*Q)). *)
      (* Show x*((x-a)*Q) = (x-a)*(x*Q). *)
      assert (Hcom : rmul R r x (rmul R r XmA Q) = rmul R r XmA (rmul R r x Q)).
      { rewrite (rmul_assoc R r x XmA Q).
        rewrite (rmul_comm R cr x XmA).
        rewrite <- (rmul_assoc R r XmA x Q). reflexivity. }
      rewrite Hcom.
      (* Goal: c + (x*P + (x-a)*(x*Q)) = (c + a*P) + ((x-a)*P + (x-a)*(x*Q)). *)
      (* Both sides are 4-term sums. Re-associate to compare. *)
      rewrite <- (radd_assoc R r c (rmul R r a P)
                  (radd R r (rmul R r XmA P) (rmul R r XmA (rmul R r x Q)))).
      f_equal.
      (* Goal: x*P + (x-a)*(x*Q) = a*P + ((x-a)*P + (x-a)*(x*Q)). *)
      rewrite (radd_assoc R r (rmul R r a P)
                          (rmul R r XmA P)
                          (rmul R r XmA (rmul R r x Q))).
      (* Goal: x*P + (x-a)*(x*Q) = (a*P + (x-a)*P) + (x-a)*(x*Q). *)
      f_equal.
      (* Goal: x*P = a*P + (x-a)*P. *)
      rewrite <- (rmul_distrib_r R r a XmA P).
      f_equal.
      (* Goal: x = a + (x - a). *)
      unfold XmA.
      rewrite (radd_assoc R r a x (rneg R r a)).
      rewrite (radd_comm R r a x).
      rewrite <- (radd_assoc R r x a (rneg R r a)).
      rewrite (radd_neg_r R r a).
      symmetry. apply (radd_zero_r R r).
  Qed.

  (** Corollary: if [a] is a root of [p], the evaluation factors. *)
  Theorem factor_theorem : forall p a x,
      peval r p a = rzero R r ->
      peval r p x =
        rmul R r (radd R r x (rneg R r a))
                 (peval r (divided_diff_q a p) x).
  Proof.
    intros p a x Ha.
    rewrite (divided_diff_eq p a x), Ha.
    apply (radd_zero_l r).
  Qed.

  (** Special case: a polynomial vanishing at 0 has 0 as a constant
      coefficient — i.e., its representation begins with rzero (modulo
      list-rep redundancy). The cleanest form: [peval p rzero] is the
      head coefficient (or rzero for the empty list). *)
  Lemma peval_at_zero : forall p,
      peval r p (rzero R r) =
      match p with nil => rzero R r | cons a _ => a end.
  Proof.
    intro p. destruct p as [|a p']; [reflexivity|].
    simpl. rewrite (rmul_zero_l r). apply (radd_zero_r R r).
  Qed.

  (** Connecting divided differences to the formal derivative:
      evaluating the divided-difference quotient at the root [a] gives
      the same value as evaluating the formal derivative at [a]. *)
  Theorem divided_diff_at_root : forall p a,
      peval r (divided_diff_q a p) a = peval r (D r p) a.
  Proof.
    induction p as [|c p IH]; intro a; [reflexivity|].
    simpl divided_diff_q. simpl peval.
    rewrite IH.
    (* Goal: peval p a + a * peval (D p) a = peval (D (c::p)) a. *)
    symmetry. apply (peval_D_cons r c p a).
  Qed.

End FactorTheorem.

(* ================================================================== *)
(** ** Special polynomials: constants, X, X − a *)
(* ================================================================== *)

Section SpecialPolynomials.
  Context {R : Type} (r : Ring R).

  (** Constant polynomial [c]. *)
  Definition pconst (c : R) : Polynomial R := cons c nil.

  (** The indeterminate X = 0 + 1·X. *)
  Definition pX : Polynomial R := cons (rzero R r) (cons (rone R r) nil).

  (** Linear polynomial X − a. *)
  Definition pX_sub (a : R) : Polynomial R :=
    cons (rneg R r a) (cons (rone R r) nil).

  Lemma peval_pconst : forall c x, peval r (pconst c) x = c.
  Proof.
    intros c x. unfold pconst. simpl.
    rewrite (rmul_zero_r r). apply (radd_zero_r R r).
  Qed.

  Lemma peval_pX : forall x, peval r pX x = x.
  Proof.
    intro x. unfold pX. simpl.
    rewrite (rmul_zero_r r), (radd_zero_r R r), (rmul_one_r R r).
    apply (radd_zero_l r).
  Qed.

  Lemma peval_pX_sub : forall a x,
      peval r (pX_sub a) x = radd R r x (rneg R r a).
  Proof.
    intros a x. unfold pX_sub. simpl.
    rewrite (rmul_zero_r r), (radd_zero_r R r), (rmul_one_r R r).
    apply (radd_comm R r).
  Qed.

  (** [a] is a root of [pX_sub a] (i.e., the polynomial X − a vanishes at a). *)
  Lemma peval_pX_sub_at_root : forall a,
      peval r (pX_sub a) a = rzero R r.
  Proof.
    intro a. rewrite peval_pX_sub. apply (radd_neg_r R r).
  Qed.

End SpecialPolynomials.

(* ================================================================== *)
(** ** Polynomial composition

    [pcomp p q] is the polynomial obtained by substituting [q] for the
    variable in [p].  Over a commutative ring,
        peval (pcomp p q) x = peval p (peval q x). *)
(* ================================================================== *)

Section PolyComp.
  Context {R : Type} (cr : CommutativeRing R).

  Notation r := (cring R cr).

  Fixpoint pcomp (p q : Polynomial R) : Polynomial R :=
    match p with
    | nil => nil
    | cons a p' => padd r (cons a nil) (pmul r q (pcomp p' q))
    end.

  (** Constant-polynomial peval. *)
  Local Lemma peval_const : forall (a x : R),
      peval r (cons a nil) x = a.
  Proof.
    intros a x. simpl. rewrite (rmul_zero_r r). apply (radd_zero_r R r).
  Qed.

  Theorem peval_pcomp : forall p q x,
      peval r (pcomp p q) x = peval r p (peval r q x).
  Proof.
    induction p as [|a p IH]; intros q x; [reflexivity|].
    cbn [pcomp].
    rewrite (peval_padd r (cons a nil) (pmul r q (pcomp p q)) x).
    rewrite peval_const.
    rewrite (peval_pmul_com cr q (pcomp p q) x).
    rewrite (IH q x).
    reflexivity.
  Qed.

  (** [pcomp p pX] equals [p] under evaluation. *)
  Lemma peval_pcomp_pX : forall p x,
      peval r (pcomp p (cons (rzero R r) (cons (rone R r) nil))) x
    = peval r p x.
  Proof.
    intros p x. rewrite (peval_pcomp p _ x).
    f_equal. simpl.
    rewrite (rmul_zero_r r), (radd_zero_r R r), (rmul_one_r R r).
    apply (radd_zero_l r).
  Qed.

  (** Composition is associative under evaluation. *)
  Theorem peval_pcomp_assoc : forall p q s x,
      peval r (pcomp (pcomp p q) s) x = peval r (pcomp p (pcomp q s)) x.
  Proof.
    intros p q s x.
    rewrite (peval_pcomp (pcomp p q) s x).
    rewrite (peval_pcomp p q (peval r s x)).
    rewrite (peval_pcomp p (pcomp q s) x).
    rewrite (peval_pcomp q s x).
    reflexivity.
  Qed.

End PolyComp.

(* ================================================================== *)
(** ** Polynomial powers and integer multiples *)
(* ================================================================== *)

Section PolyPow.
  Context {R : Type} (cr : CommutativeRing R).

  Notation r := (cring R cr).

  (** Repeated polynomial multiplication: p^n. *)
  Fixpoint ppow (p : Polynomial R) (n : nat) : Polynomial R :=
    match n with
    | O => cons (rone R r) nil
    | S k => pmul r p (ppow p k)
    end.

  Lemma peval_ppow : forall p n x,
      peval r (ppow p n) x = ring_pow r (peval r p x) n.
  Proof.
    intros p n x. induction n as [|n IH].
    - simpl ppow. simpl ring_pow.
      simpl peval.
      rewrite (rmul_zero_r r). apply (radd_zero_r R r).
    - simpl. rewrite (peval_pmul_com cr p (ppow p n) x).
      rewrite IH. reflexivity.
  Qed.

  (** Powers of [pX] evaluate to powers of the variable. *)
  Lemma peval_ppow_pX : forall n x,
      peval r (ppow (pX r) n) x = ring_pow r x n.
  Proof.
    intros n x. rewrite peval_ppow. rewrite (peval_pX r x). reflexivity.
  Qed.

  (** [ppow p (n+m)] evaluates to product of separate powers. *)
  Lemma peval_ppow_add : forall p n m x,
      peval r (ppow p (n + m)) x =
      rmul R r (peval r (ppow p n) x) (peval r (ppow p m) x).
  Proof.
    intros p n m x.
    rewrite !peval_ppow. apply ring_pow_add.
  Qed.

  (** [pone^n = pone] (Leibniz). *)
  Lemma ppow_pone : forall n, ppow (pone r) n = pone r.
  Proof.
    induction n as [|n IH]; [reflexivity|].
    simpl ppow. rewrite IH. apply pmul_one_l.
  Qed.

  (** [pzero^(S n) = pzero] (Leibniz). *)
  Lemma ppow_pzero_succ : forall n, ppow pzero (S n) = pzero.
  Proof. intros. reflexivity. Qed.

End PolyPow.

(* ================================================================== *)
(** ** Peval-equivalence: polynomials are equivalent if they evaluate
       to the same value at every point.

    This is a coarser equivalence than Leibniz equality on the list
    representation; it ignores trailing zeros and is the natural
    setoid for working with the polynomial ring. *)
(* ================================================================== *)

Section PolyPequiv.
  Context {R : Type} (r : Ring R).

  Definition pequiv (p q : Polynomial R) : Prop :=
    forall x, peval r p x = peval r q x.

  Lemma pequiv_refl : forall p, pequiv p p.
  Proof. intros p x. reflexivity. Qed.

  Lemma pequiv_sym : forall p q, pequiv p q -> pequiv q p.
  Proof. intros p q H x. symmetry. apply H. Qed.

  Lemma pequiv_trans : forall p q s,
      pequiv p q -> pequiv q s -> pequiv p s.
  Proof. intros p q s H1 H2 x. rewrite H1. apply H2. Qed.

  #[global] Instance pequiv_Equivalence : Equivalence pequiv.
  Proof.
    split.
    - intros p; apply pequiv_refl.
    - intros p q; apply pequiv_sym.
    - intros p q s; apply pequiv_trans.
  Qed.

  (** padd respects pequiv. *)
  #[global] Instance padd_Proper :
    Proper (pequiv ==> pequiv ==> pequiv) (padd r).
  Proof.
    intros p1 p2 Hp q1 q2 Hq x.
    rewrite !(peval_padd r).
    rewrite (Hp x), (Hq x). reflexivity.
  Qed.

  (** pneg respects pequiv. *)
  #[global] Instance pneg_Proper :
    Proper (pequiv ==> pequiv) (pneg r).
  Proof.
    intros p1 p2 Hp x.
    rewrite !(peval_pneg r).
    rewrite (Hp x). reflexivity.
  Qed.

  (** Additive inverse holds under pequiv (it does NOT hold in Leibniz
      due to trailing zeros, but does hold semantically). *)
  Lemma padd_neg_pequiv : forall p, pequiv (padd r p (pneg r p)) pzero.
  Proof.
    intros p x.
    rewrite (peval_padd r p (pneg r p) x).
    rewrite (peval_pneg r p x).
    apply (radd_neg_r R r).
  Qed.

  (** Symmetric: pneg p + p = 0. *)
  Lemma padd_neg_l_pequiv : forall p, pequiv (padd r (pneg r p) p) pzero.
  Proof.
    intros p x.
    rewrite (peval_padd r (pneg r p) p x).
    rewrite (peval_pneg r p x).
    apply (radd_neg_l r).
  Qed.

  (** padd is associative under pequiv (it's also Leibniz, but stated
      here for convenient setoid use). *)
  Lemma padd_pequiv_assoc : forall p q s,
      pequiv (padd r p (padd r q s)) (padd r (padd r p q) s).
  Proof. intros p q s. rewrite (padd_assoc r p q s). reflexivity. Qed.

  Lemma padd_pequiv_comm : forall p q,
      pequiv (padd r p q) (padd r q p).
  Proof. intros p q. rewrite (padd_comm r p q). reflexivity. Qed.

  Lemma padd_pequiv_zero_l : forall p, pequiv (padd r pzero p) p.
  Proof. intros p. rewrite (padd_zero_l r p). reflexivity. Qed.

  Lemma padd_pequiv_zero_r : forall p, pequiv (padd r p pzero) p.
  Proof. intros p. rewrite (padd_zero_r r p). reflexivity. Qed.

  (** [pneg (pneg p) ≈ p] under pequiv. *)
  Lemma pneg_pneg_pequiv : forall p, pequiv (pneg r (pneg r p)) p.
  Proof.
    intros p x.
    rewrite (peval_pneg r). rewrite (peval_pneg r).
    apply (rneg_neg r).
  Qed.

  (** [pneg pzero ≈ pzero] under pequiv. *)
  Lemma pneg_pzero_pequiv : pequiv (pneg r pzero) pzero.
  Proof. intro x. reflexivity. Qed.

  (** Scaling by zero gives the zero polynomial under pequiv (NOT Leibniz —
      [pscale rzero p] is the zero list of length [length p]). *)
  Lemma pscale_zero_pequiv : forall p, pequiv (pscale r (rzero R r) p) pzero.
  Proof.
    intros p x. simpl peval at 2.
    induction p as [|a p IH]; [reflexivity|].
    simpl pscale. simpl peval.
    rewrite (rmul_zero_l r a).
    rewrite IH. (* peval (pscale 0 p) x = 0 *)
    rewrite (rmul_zero_r r x).
    apply (radd_zero_r R r).
  Qed.

  (** Polynomial additive cancellation. *)
  Lemma padd_pequiv_cancel_l : forall p q s,
      pequiv (padd r p q) (padd r p s) -> pequiv q s.
  Proof.
    intros p q s H x.
    pose proof (H x) as Hx.
    rewrite !(peval_padd r) in Hx.
    apply (radd_cancel_l r (peval r p x)). exact Hx.
  Qed.

End PolyPequiv.

Section PolyPequivCom.
  Context {R : Type} (cr : CommutativeRing R).

  Notation r := (cring R cr).

  (** pmul respects pequiv (in commutative ring). *)
  #[global] Instance pmul_Proper :
    Proper (pequiv r ==> pequiv r ==> pequiv r) (pmul r).
  Proof.
    intros p1 p2 Hp q1 q2 Hq x.
    rewrite !(peval_pmul_com cr).
    rewrite (Hp x), (Hq x). reflexivity.
  Qed.

  (** pscale respects pequiv. *)
  #[global] Instance pscale_Proper :
    Proper (eq ==> pequiv r ==> pequiv r) (pscale r).
  Proof.
    intros c1 c2 Hc p1 p2 Hp x. subst c2.
    rewrite !(peval_pscale_com cr).
    rewrite (Hp x). reflexivity.
  Qed.

  (** Polynomial ring laws hold up to pequiv. *)
  Lemma pmul_pequiv_comm : forall p q, pequiv r (pmul r p q) (pmul r q p).
  Proof. intros p q x. apply (peval_pmul_comm cr p q x). Qed.

  Lemma pmul_pequiv_assoc : forall p q s,
      pequiv r (pmul r (pmul r p q) s) (pmul r p (pmul r q s)).
  Proof. intros p q s x. apply (peval_pmul_assoc cr p q s x). Qed.

  (** Helper for D_mul_pequiv: evaluation reduction. *)
  Local Lemma four_term_radd_perm : forall (a1 a2 a3 a4 : R),
      radd R r (radd R r a1 a2) (radd R r a3 a4) =
      radd R r a3 (radd R r a1 (radd R r a2 a4)).
  Proof.
    intros a1 a2 a3 a4.
    rewrite <- (radd_assoc R r).
    rewrite (radd_assoc R r a2 a3 a4).
    rewrite (radd_comm R r a2 a3).
    rewrite <- (radd_assoc R r a3 a2 a4).
    rewrite (radd_assoc R r a1 a3 _).
    rewrite (radd_comm R r a1 a3).
    rewrite <- (radd_assoc R r a3 a1 _).
    reflexivity.
  Qed.

  (** Leibniz rule (product rule) under pequiv.
      The Leibniz form is FALSE in our list-rep due to trailing-zero
      asymmetries; under [pequiv] it holds in any commutative ring. *)
  Theorem D_mul_pequiv : forall p q,
      pequiv r (D r (pmul r p q))
              (padd r (pmul r (D r p) q) (pmul r p (D r q))).
  Proof.
    induction p as [|a p IH]; intros q x.
    - (* p = nil *)
      change (pmul r nil q) with (@nil R).
      change (D r (@nil R)) with (@nil R).
      rewrite (peval_padd r).
      rewrite (peval_pmul_com cr nil q x).
      rewrite (peval_pmul_com cr nil (D r q) x).
      change (peval r nil x) with (rzero R r).
      rewrite (rmul_zero_l r), (rmul_zero_l r), (radd_zero_r R r). reflexivity.
    - destruct q as [|b q'].
      + (* q = nil — both LHS and RHS are 0 after reduction. *)
        rewrite (pmul_nil_r r).
        change (D r nil) with (@nil R).
        rewrite (pmul_nil_r r).
        rewrite (peval_padd r).
        change (peval r nil x) with (rzero R r).
        rewrite (radd_zero_l r). reflexivity.
      + (* p = cons a p, q = cons b q' *)
        change (pmul r (cons a p) (cons b q'))
          with (padd r (pscale r a (cons b q'))
                       (cons (rzero R r) (pmul r p (cons b q')))).
        rewrite (D_add r), (D_scale r).
        rewrite (peval_padd r).
        rewrite (peval_pscale_com cr a (D r (cons b q')) x).
        rewrite (peval_D_cons r (rzero R r) (pmul r p (cons b q')) x).
        rewrite (peval_pmul_com cr p (cons b q') x).
        rewrite (IH (cons b q') x).
        rewrite (peval_padd r).
        rewrite (peval_pmul_com cr (D r p) (cons b q') x).
        rewrite (peval_pmul_com cr p (D r (cons b q')) x).
        (* RHS *)
        rewrite (peval_padd r).
        rewrite (peval_pmul_com cr (D r (cons a p)) (cons b q') x).
        rewrite (peval_pmul_com cr (cons a p) (D r (cons b q')) x).
        rewrite (peval_D_cons r a p x).
        change (peval r (cons a p) x)
          with (radd R r a (rmul R r x (peval r p x))).
        set (Pp := peval r p x).
        set (Pq := peval r (cons b q') x).
        set (PDp := peval r (D r p) x).
        set (PDq := peval r (D r (cons b q')) x).
        (* LHS = a*PDq + (Pp*Pq + x*(PDp*Pq + Pp*PDq)).
           RHS = (Pp + x*PDp)*Pq + (a + x*Pp)*PDq. *)
        rewrite (rmul_distrib_l R r x (rmul R r PDp Pq) (rmul R r Pp PDq)).
        rewrite (rmul_distrib_r R r Pp (rmul R r x PDp) Pq).
        rewrite (rmul_distrib_r R r a (rmul R r x Pp) PDq).
        (* LHS = a*PDq + (Pp*Pq + (x*(PDp*Pq) + x*(Pp*PDq))).
           After [rmul_assoc x PDp Pq] and [rmul_assoc x Pp PDq]:
           LHS = a*PDq + (Pp*Pq + ((x*PDp)*Pq + (x*Pp)*PDq)).
           RHS = (Pp*Pq + (x*PDp)*Pq) + (a*PDq + (x*Pp)*PDq).
           By [four_term_radd_perm a1 a2 a3 a4]:
              (a1+a2) + (a3+a4) = a3 + (a1 + (a2 + a4))
           with a1 = Pp*Pq, a2 = (x*PDp)*Pq, a3 = a*PDq, a4 = (x*Pp)*PDq.
           So RHS = LHS via symmetry. *)
        rewrite (rmul_assoc R r x PDp Pq).
        rewrite (rmul_assoc R r x Pp PDq).
        symmetry.
        apply (four_term_radd_perm
                 (rmul R r Pp Pq)
                 (rmul R r (rmul R r x PDp) Pq)
                 (rmul R r a PDq)
                 (rmul R r (rmul R r x Pp) PDq)).
  Qed.

  (** [pcomp] respects [pequiv] in both arguments. *)
  #[global] Instance pcomp_Proper :
    Proper (pequiv r ==> pequiv r ==> pequiv r) (pcomp cr).
  Proof.
    intros p1 p2 Hp q1 q2 Hq x.
    rewrite !(peval_pcomp _ _ _ x).
    rewrite (Hq x).
    apply Hp.
  Qed.

  (** [ppow] respects [pequiv] in the polynomial argument. *)
  #[global] Instance ppow_Proper :
    Proper (pequiv r ==> eq ==> pequiv r) (ppow cr).
  Proof.
    intros p1 p2 Hp n1 n2 Hn x. subst n2.
    rewrite !peval_ppow. rewrite (Hp x). reflexivity.
  Qed.

  (** Setoid form of [ppow_add]: [ppow p (n+m) ≈ ppow p n * ppow p m]. *)
  Lemma ppow_pequiv_add : forall p n m,
      pequiv r (ppow cr p (n + m))
              (pmul r (ppow cr p n) (ppow cr p m)).
  Proof.
    intros p n m x.
    rewrite (peval_ppow_add cr p n m x).
    rewrite (peval_pmul_com cr (ppow cr p n) (ppow cr p m) x).
    reflexivity.
  Qed.

  (** [(p * q)^n ≈ p^n * q^n] under pequiv. *)
  Lemma ppow_pequiv_pmul_distrib : forall p q n,
      pequiv r (ppow cr (pmul r p q) n)
              (pmul r (ppow cr p n) (ppow cr q n)).
  Proof.
    intros p q n x.
    rewrite peval_ppow.
    rewrite (peval_pmul_com cr p q x).
    rewrite ring_pow_mul_distrib.
    rewrite (peval_pmul_com cr (ppow cr p n) (ppow cr q n) x).
    rewrite !peval_ppow. reflexivity.
  Qed.

  (** [D pX ≈ pone]: derivative of the indeterminate is 1. *)
  Lemma D_pX_pequiv : pequiv r (D r (pX r)) (pone r).
  Proof.
    intro x. unfold pX, pone.
    change (D r (cons (rzero R r) (cons (rone R r) nil)))
      with (mult_by_index_from r 1 (cons (rone R r) nil)).
    cbn [mult_by_index_from ntimes peval].
    repeat (rewrite (rmul_zero_r r) || rewrite (radd_zero_r R r)).
    reflexivity.
  Qed.

  (** [D (pconst c) ≈ pzero]: derivative of a constant is 0. *)
  Lemma D_pconst_pequiv : forall c, pequiv r (D r (pconst c)) pzero.
  Proof.
    intros c x. unfold pconst.
    change (D r (cons c nil)) with (@nil R).
    reflexivity.
  Qed.

  (** Natural number cast: rnat n = ntimes n (rone R r). *)
  Definition rnat (n : nat) : R := ntimes r n (rone R r).

  (** [rmul (rnat n) a = ntimes n a]: the embedded natural acts as repeated addition. *)
  Lemma rmul_rnat : forall n a,
      rmul R r (rnat n) a = ntimes r n a.
  Proof.
    induction n as [|n IH]; intro a.
    - unfold rnat. simpl. apply (rmul_zero_l r).
    - unfold rnat. simpl ntimes.
      rewrite (rmul_distrib_r R r (rone R r) (ntimes r n (rone R r)) a).
      rewrite (rmul_one_l R r). f_equal.
      apply IH.
  Qed.

  (** [pmul (X − a) q] vanishes at a (converse direction of factor theorem). *)
  Theorem peval_pmul_pX_sub_at_root : forall a q,
      peval r (pmul r (pX_sub r a) q) a = rzero R r.
  Proof.
    intros a q.
    rewrite (peval_pmul_com cr (pX_sub r a) q a).
    rewrite (peval_pX_sub_at_root r a).
    apply (rmul_zero_l r).
  Qed.

  (** Peval-level power rule:
      [peval (D (p^(n+1))) x = (n+1) * (peval (p^n) x * peval (D p) x)]
      where the [(n+1) *] is [ntimes (n+1)] in the ring [R]. *)
  Theorem peval_D_ppow_succ : forall p n x,
      peval r (D r (ppow cr p (S n))) x =
      ntimes r (S n) (rmul R r (peval r (ppow cr p n) x)
                              (peval r (D r p) x)).
  Proof.
    intros p n x.
    induction n as [|n IH].
    - (* n = 0: peval (D (ppow p 1)) x ≈ peval (D p) x. *)
      change (ppow cr p 1) with (pmul r p (cons (rone R r) nil)).
      rewrite (D_mul_pequiv p (cons (rone R r) nil) x).
      rewrite (peval_padd r).
      rewrite (peval_pmul_com cr (D r p) (cons (rone R r) nil) x).
      rewrite (peval_pmul_com cr p (D r (cons (rone R r) nil)) x).
      change (D r (cons (rone R r) nil)) with (@nil R).
      change (peval r (@nil R) x) with (rzero R r).
      change (peval r (cons (rone R r) nil) x)
        with (radd R r (rone R r) (rmul R r x (rzero R r))).
      simpl ring_pow.
      simpl ntimes.
      change (ppow cr p 0) with (cons (rone R r) (@nil R)).
      change (peval r (cons (rone R r) nil) x)
        with (radd R r (rone R r) (rmul R r x (rzero R r))).
      repeat (rewrite (rmul_zero_r r) || rewrite (radd_zero_r R r) ||
              rewrite (rmul_one_r R r) || rewrite (rmul_one_l R r)).
      reflexivity.
    - (* n = S k *)
      change (ppow cr p (S (S n))) with (pmul r p (ppow cr p (S n))).
      rewrite (D_mul_pequiv p (ppow cr p (S n)) x).
      rewrite (peval_padd r).
      rewrite (peval_pmul_com cr (D r p) (ppow cr p (S n)) x).
      rewrite (peval_pmul_com cr p (D r (ppow cr p (S n))) x).
      rewrite IH.
      (* LHS = PDp * peval (ppow p (S n)) x
              + Pp * ntimes (S n) (peval (ppow p n) x * PDp). *)
      rewrite <- (ntimes_rmul_l r (S n) (peval r p x)
                              (rmul R r (peval r (ppow cr p n) x) (peval r (D r p) x))).
      (* Now: PDp * peval (ppow p (S n)) x
              + ntimes (S n) (peval p x * (peval (ppow p n) x * PDp)). *)
      rewrite (rmul_assoc R r (peval r p x)
                              (peval r (ppow cr p n) x)
                              (peval r (D r p) x)).
      change (peval r p x) with (peval r p x).
      (* peval p x * peval (ppow p n) x = peval (pmul p (ppow p n)) x = peval (ppow p (S n)) x. *)
      rewrite <- (peval_pmul_com cr p (ppow cr p n) x).
      change (pmul r p (ppow cr p n)) with (ppow cr p (S n)).
      (* Now: PDp * peval (ppow p (S n)) x
              + ntimes (S n) (peval (ppow p (S n)) x * PDp). *)
      rewrite (rmul_comm R cr (peval r (D r p) x) (peval r (ppow cr p (S n)) x)).
      simpl ntimes.
      reflexivity.
  Qed.

  (** Polynomial-level power rule under pequiv:
      [D (p^(n+1)) ≈ rnat(n+1) * p^n * D p]. *)
  Theorem D_ppow_pequiv : forall p n,
      pequiv r (D r (ppow cr p (S n)))
              (pmul r (pscale r (rnat (S n)) (ppow cr p n)) (D r p)).
  Proof.
    intros p n x.
    rewrite (peval_D_ppow_succ p n x).
    rewrite (peval_pmul_com cr).
    rewrite (peval_pscale_com cr).
    rewrite <- (rmul_rnat (S n)
                  (rmul R r (peval r (ppow cr p n) x) (peval r (D r p) x))).
    apply (rmul_assoc R r).
  Qed.

  (** Concrete: [D (X^(n+1)) ≈ rnat(n+1) * X^n]. *)
  Theorem D_ppow_pX_pequiv : forall n,
      pequiv r (D r (ppow cr (pX r) (S n)))
              (pscale r (rnat (S n)) (ppow cr (pX r) n)).
  Proof.
    intros n x.
    rewrite (D_ppow_pequiv (pX r) n x).
    rewrite (peval_pmul_com cr).
    rewrite (peval_pscale_com cr).
    rewrite (D_pX_pequiv x).
    change (peval r (pone r) x)
      with (radd R r (rone R r) (rmul R r x (rzero R r))).
    rewrite (rmul_zero_r r).
    rewrite (radd_zero_r R r).
    rewrite (rmul_one_r R r).
    reflexivity.
  Qed.

  (** Power rule for square: [D (p^2) ≈ (p + p) * D p]. *)
  Theorem D_psquare_pequiv : forall p,
      pequiv r (D r (pmul r p p)) (pmul r (padd r p p) (D r p)).
  Proof.
    intros p x.
    rewrite (D_mul_pequiv p p x).
    rewrite (peval_padd r).
    rewrite (peval_pmul_com cr (padd r p p) (D r p) x).
    rewrite (peval_padd r p p x).
    rewrite (peval_pmul_com cr (D r p) p x).
    rewrite (peval_pmul_com cr p (D r p) x).
    rewrite (rmul_distrib_r R r (peval r p x) (peval r p x) (peval r (D r p) x)).
    rewrite (rmul_comm R cr (peval r (D r p) x) (peval r p x)).
    reflexivity.
  Qed.

  (** Scaling commutes with multiplication under pequiv. *)
  Lemma pscale_pmul_pequiv_l : forall c p q,
      pequiv r (pmul r (pscale r c p) q) (pscale r c (pmul r p q)).
  Proof.
    intros c p q x.
    rewrite (peval_pmul_com cr).
    rewrite (peval_pscale_com cr).
    rewrite (peval_pscale_com cr).
    rewrite (peval_pmul_com cr).
    symmetry. apply (rmul_assoc R r).
  Qed.

  Lemma pscale_pmul_pequiv_r : forall c p q,
      pequiv r (pmul r p (pscale r c q)) (pscale r c (pmul r p q)).
  Proof.
    intros c p q x.
    rewrite (peval_pmul_com cr).
    rewrite (peval_pscale_com cr).
    rewrite (peval_pscale_com cr).
    rewrite (peval_pmul_com cr).
    (* Goal: peval p x * (c * peval q x) = c * (peval p x * peval q x). *)
    rewrite (rmul_assoc R r (peval r p x) c (peval r q x)).
    rewrite (rmul_comm R cr (peval r p x) c).
    rewrite <- (rmul_assoc R r c (peval r p x) (peval r q x)).
    reflexivity.
  Qed.

  (** Chain rule for the formal derivative under [pequiv].
      [D (p ∘ q) ≈ (D p ∘ q) · D q]. *)
  Theorem D_pcomp_pequiv : forall p q,
      pequiv r (D r (pcomp cr p q))
              (pmul r (pcomp cr (D r p) q) (D r q)).
  Proof.
    induction p as [|a p IH]; intros q x.
    - change (pcomp cr nil q) with (@nil R).
      change (D r (@nil R)) with (@nil R).
      change (pmul r nil (D r q)) with (@nil R).
      reflexivity.
    - change (pcomp cr (cons a p) q) with
        (padd r (cons a nil) (pmul r q (pcomp cr p q))).
      rewrite (D_add r).
      change (D r (cons a nil)) with (@nil R).
      rewrite (padd_nil_l r).
      (* LHS = peval (D (pmul q (pcomp p q))) x; apply D_mul_pequiv. *)
      rewrite (D_mul_pequiv q (pcomp cr p q) x).
      rewrite (peval_padd r).
      rewrite (peval_pmul_com cr (D r q) (pcomp cr p q) x).
      rewrite (peval_pcomp cr p q x).
      rewrite (peval_pmul_com cr q (D r (pcomp cr p q)) x).
      rewrite (IH q x).
      rewrite (peval_pmul_com cr (pcomp cr (D r p) q) (D r q) x).
      rewrite (peval_pcomp cr (D r p) q x).
      (* Now LHS = peval (D q) x * peval p (peval q x)
                   + peval q x * (peval (D p) (peval q x) * peval (D q) x).
         RHS = peval (D (cons a p)) (peval q x) * peval (D q) x. *)
      rewrite (peval_pmul_com cr (pcomp cr (D r (cons a p)) q) (D r q) x).
      rewrite (peval_pcomp cr (D r (cons a p)) q x).
      rewrite (peval_D_cons r a p (peval r q x)).
      (* RHS = (peval p y + y * peval (D p) y) * peval (D q) x where y = peval q x. *)
      rewrite (rmul_distrib_r R r
                (peval r p (peval r q x))
                (rmul R r (peval r q x) (peval r (D r p) (peval r q x)))
                (peval r (D r q) x)).
      rewrite (rmul_comm R cr (peval r (D r q) x)
                              (peval r p (peval r q x))).
      f_equal.
      apply (rmul_assoc R r).
  Qed.

  (** Square of difference: [(p - q)^2 ≈ p*p - (p*q + p*q) + q*q]. *)
  Theorem pmul_pneg_pneg_pequiv : forall p q,
      pequiv r (pmul r (padd r p (pneg r q)) (padd r p (pneg r q)))
              (padd r (pmul r p p)
                      (padd r (pneg r (padd r (pmul r p q) (pmul r p q)))
                              (pmul r q q))).
  Proof.
    intros p q x.
    rewrite (peval_pmul_com cr).
    rewrite !(peval_padd r).
    rewrite !(peval_pneg r).
    rewrite !(peval_padd r).
    rewrite !(peval_pmul_com cr).
    set (Pp := peval r p x).
    set (Pq := peval r q x).
    rewrite (rmul_distrib_l R r (radd R r Pp (rneg R r Pq)) Pp (rneg R r Pq)).
    rewrite (rmul_distrib_r R r Pp (rneg R r Pq) Pp).
    rewrite (rmul_distrib_r R r Pp (rneg R r Pq) (rneg R r Pq)).
    rewrite (rmul_neg_l_full r Pq Pp).
    rewrite (rmul_neg_r_full r Pp Pq).
    rewrite (rmul_neg_l_full r Pq (rneg R r Pq)).
    rewrite (rmul_neg_r_full r Pq Pq).
    rewrite (rneg_neg r).
    rewrite (rmul_comm R cr Pq Pp).
    (* LHS: (Pp*Pp + -(Pp*Pq)) + (-(Pp*Pq) + Pq*Pq).
       RHS: Pp*Pp + (-(Pp*Pq + Pp*Pq) + Pq*Pq).  *)
    rewrite (rneg_add r (rmul R r Pp Pq) (rmul R r Pp Pq)).
    rewrite <- (radd_assoc R r (rmul R r Pp Pp)
                              (rneg R r (rmul R r Pp Pq))
                              (radd R r (rneg R r (rmul R r Pp Pq))
                                          (rmul R r Pq Pq))).
    rewrite (radd_assoc R r (rneg R r (rmul R r Pp Pq))
                            (rneg R r (rmul R r Pp Pq))
                            (rmul R r Pq Pq)).
    reflexivity.
  Qed.

  (** Difference of squares: [(p + q)*(p - q) ≈ p*p - q*q] under pequiv. *)
  Theorem pmul_padd_pneg_pequiv : forall p q,
      pequiv r (pmul r (padd r p q) (padd r p (pneg r q)))
              (padd r (pmul r p p) (pneg r (pmul r q q))).
  Proof.
    intros p q x.
    rewrite (peval_pmul_com cr).
    rewrite !(peval_padd r).
    rewrite !(peval_pneg r).
    rewrite (peval_pmul_com cr p p x).
    rewrite (peval_pmul_com cr q q x).
    set (Pp := peval r p x).
    set (Pq := peval r q x).
    (* Goal: (Pp + Pq) * (Pp + -Pq) = Pp*Pp + -(Pq*Pq). *)
    rewrite (rmul_distrib_l R r (radd R r Pp Pq) Pp (rneg R r Pq)).
    rewrite (rmul_distrib_r R r Pp Pq Pp).
    rewrite (rmul_distrib_r R r Pp Pq (rneg R r Pq)).
    rewrite (rmul_neg_r_full r).
    rewrite (rmul_neg_r_full r).
    rewrite (rmul_comm R cr Pq Pp).
    (* Goal: (Pp*Pp + Pp*Pq) + (-(Pp*Pq) + -(Pq*Pq)) = Pp*Pp + -(Pq*Pq). *)
    rewrite <- (radd_assoc R r (rmul R r Pp Pp) (rmul R r Pp Pq)
                              (radd R r (rneg R r (rmul R r Pp Pq))
                                          (rneg R r (rmul R r Pq Pq)))).
    rewrite (radd_assoc R r (rmul R r Pp Pq)
                            (rneg R r (rmul R r Pp Pq))
                            (rneg R r (rmul R r Pq Pq))).
    rewrite (radd_neg_r R r).
    rewrite (radd_zero_l r).
    reflexivity.
  Qed.

  (** Binomial-square: [(p + q)^2 ≈ p*p + (p*q + p*q) + q*q] under pequiv. *)
  Theorem pmul_padd_padd_pequiv : forall p q,
      pequiv r (pmul r (padd r p q) (padd r p q))
              (padd r (pmul r p p)
                      (padd r (padd r (pmul r p q) (pmul r p q))
                              (pmul r q q))).
  Proof.
    intros p q x.
    rewrite (peval_pmul_com cr).
    rewrite !(peval_padd r).
    rewrite !(peval_pmul_com cr).
    (* Goal: (Pp+Pq)*(Pp+Pq) = Pp*Pp + ((Pp*Pq + Pp*Pq) + Pq*Pq). *)
    rewrite (rmul_distrib_l R r (radd R r (peval r p x) (peval r q x))
                                (peval r p x) (peval r q x)).
    rewrite !(rmul_distrib_r R r (peval r p x) (peval r q x)).
    (* (Pp*Pp + Pq*Pp) + (Pp*Pq + Pq*Pq) = Pp*Pp + (Pp*Pq + Pp*Pq) + Pq*Pq. *)
    rewrite (rmul_comm R cr (peval r q x) (peval r p x)).
    rewrite <- (radd_assoc R r (rmul R r (peval r p x) (peval r p x))
                              (rmul R r (peval r p x) (peval r q x))
                              (radd R r (rmul R r (peval r p x) (peval r q x))
                                          (rmul R r (peval r q x) (peval r q x)))).
    rewrite (radd_assoc R r (rmul R r (peval r p x) (peval r q x))
                            (rmul R r (peval r p x) (peval r q x))
                            (rmul R r (peval r q x) (peval r q x))).
    reflexivity.
  Qed.

End PolyPequivCom.

(* ================================================================== *)
(** ** Polynomial degree (length-based, not minimal-form) *)
(* ================================================================== *)

(** [pdeg p] = length p − 1 for nonempty p, with pdeg [] = 0 by convention.
    This is "list-degree" (counts trailing zeros), not the minimal-form
    degree. Useful as an upper bound. *)
Definition pdeg_list {R : Type} (p : Polynomial R) : nat :=
  match p with
  | nil => 0
  | _ :: q => List.length q
  end.

Lemma pdeg_list_pzero {R : Type} : pdeg_list (@pzero R) = 0%nat.
Proof. reflexivity. Qed.

Lemma pdeg_list_pone {R : Type} (r : Ring R) :
  pdeg_list (pone r) = 0%nat.
Proof. reflexivity. Qed.

Lemma pdeg_list_pX {R : Type} (r : Ring R) :
  pdeg_list (pX r) = 1%nat.
Proof. reflexivity. Qed.

Lemma pscale_length {R : Type} (r : Ring R) (c : R) (p : Polynomial R) :
  List.length (pscale r c p) = List.length p.
Proof.
  induction p as [|x p IH]; [reflexivity|].
  simpl. f_equal. exact IH.
Qed.

Lemma pneg_length {R : Type} (r : Ring R) (p : Polynomial R) :
  List.length (pneg r p) = List.length p.
Proof.
  induction p as [|x p IH]; [reflexivity|].
  simpl. f_equal. exact IH.
Qed.

Lemma pdeg_list_pscale {R : Type} (r : Ring R) (c : R) (p : Polynomial R) :
  pdeg_list (pscale r c p) = pdeg_list p.
Proof.
  destruct p as [|x p']; [reflexivity|].
  simpl. apply pscale_length.
Qed.

Lemma pdeg_list_pneg {R : Type} (r : Ring R) (p : Polynomial R) :
  pdeg_list (pneg r p) = pdeg_list p.
Proof.
  destruct p as [|x p']; [reflexivity|].
  simpl. apply pneg_length.
Qed.

(** Leading coefficient (length-based, coincides with classical degree
    only when the last entry is nonzero). *)
Definition plead {R : Type} (r : Ring R) (p : Polynomial R) : R :=
  List.last p (rzero R r).

Lemma plead_pzero {R : Type} (r : Ring R) :
  plead r pzero = rzero R r.
Proof. reflexivity. Qed.

Lemma plead_pone {R : Type} (r : Ring R) :
  plead r (pone r) = rone R r.
Proof. reflexivity. Qed.

Lemma plead_pX {R : Type} (r : Ring R) :
  plead r (pX r) = rone R r.
Proof. reflexivity. Qed.

(** All-zero list predicate. *)
Definition all_zero {R : Type} (r : Ring R) (p : Polynomial R) : Prop :=
  forall x, List.In x p -> x = rzero R r.

Lemma all_zero_nil {R : Type} (r : Ring R) :
  all_zero r nil.
Proof. intros x H. inversion H. Qed.

Lemma all_zero_cons {R : Type} (r : Ring R) (a : R) (p : Polynomial R) :
  a = rzero R r -> all_zero r p -> all_zero r (cons a p).
Proof.
  intros Ha Hp x [H | H].
  - subst x. exact Ha.
  - apply Hp. exact H.
Qed.

(** all-zero polynomial peval to zero. *)
Lemma peval_all_zero {R : Type} (r : Ring R) (p : Polynomial R) :
  all_zero r p -> forall x, peval r p x = rzero R r.
Proof.
  intros Hp x. induction p as [|a p IH].
  - reflexivity.
  - simpl.
    rewrite (Hp a (or_introl eq_refl)).
    rewrite IH; [|intros y Hy; apply Hp; right; exact Hy].
    rewrite (rmul_zero_r r). rewrite (radd_zero_l r). reflexivity.
Qed.

(** A polynomial is monic if its leading coefficient is 1. *)
Definition is_monic {R : Type} (r : Ring R) (p : Polynomial R) : Prop :=
  plead r p = rone R r.

Lemma pX_is_monic {R : Type} (r : Ring R) :
  is_monic r (pX r).
Proof. unfold is_monic, plead, pX, last. reflexivity. Qed.

Lemma pX_sub_is_monic {R : Type} (r : Ring R) (a : R) :
  is_monic r (pX_sub r a).
Proof. unfold is_monic, plead, pX_sub, last. reflexivity. Qed.

(** A polynomial peval at point x is the leading coefficient when the
    polynomial has length 1 (constant). *)
Lemma peval_singleton {R : Type} (r : Ring R) (a : R) (x : R) :
  peval r (cons a nil) x = a.
Proof.
  simpl. rewrite (rmul_zero_r r). apply (radd_zero_r R r).
Qed.

(** peval is bilinear in the polynomial (additive in p). *)
Lemma peval_padd_eq {R : Type} (r : Ring R) (p q : Polynomial R) (x : R) :
  peval r (padd r p q) x = radd R r (peval r p x) (peval r q x).
Proof. apply peval_padd. Qed.

(** A polynomial composed with a constant evaluates to a constant. *)
Lemma peval_pcomp_pconst {R : Type} (cr : CommutativeRing R)
    (p : Polynomial R) (c : R) (x : R) :
  peval (cring R cr) (pcomp cr p (pconst c)) x = peval (cring R cr) p c.
Proof.
  rewrite (peval_pcomp cr).
  rewrite (peval_pconst (cring R cr) c x).
  reflexivity.
Qed.

(** Polynomial composition with the indeterminate: pcomp p X = p (peval-equal). *)
Lemma peval_pcomp_pX_id {R : Type} (cr : CommutativeRing R)
    (p : Polynomial R) (x : R) :
  peval (cring R cr) (pcomp cr p (pX (cring R cr))) x = peval (cring R cr) p x.
Proof. apply peval_pcomp_pX. Qed.

(** Polynomial composition pcomp pone q = pone (peval-equal). *)
Lemma peval_pcomp_pone_l {R : Type} (cr : CommutativeRing R)
    (q : Polynomial R) (x : R) :
  peval (cring R cr) (pcomp cr (pone (cring R cr)) q) x = rone R (cring R cr).
Proof.
  rewrite (peval_pcomp cr).
  apply (peval_pone (cring R cr)).
Qed.

(** peval is a homomorphism: peval (p + q) = peval p + peval q (Leibniz). *)
Lemma peval_padd_hom {R : Type} (r : Ring R) (p q : Polynomial R) (x : R) :
  peval r (padd r p q) x = radd R r (peval r p x) (peval r q x).
Proof. apply peval_padd. Qed.

(** Composition distributes over addition (peval-equivalent). *)
Lemma peval_pcomp_padd {R : Type} (cr : CommutativeRing R)
    (p1 p2 q : Polynomial R) (x : R) :
  peval (cring R cr) (pcomp cr (padd (cring R cr) p1 p2) q) x =
  radd R (cring R cr) (peval (cring R cr) (pcomp cr p1 q) x)
                      (peval (cring R cr) (pcomp cr p2 q) x).
Proof.
  rewrite (peval_pcomp cr).
  rewrite (peval_padd (cring R cr) p1 p2).
  rewrite !(peval_pcomp cr).
  reflexivity.
Qed.

(** Composition with constant factor scales: pcomp (pscale c p) q at x = c * peval (pcomp p q) x *)
Lemma peval_pcomp_pscale {R : Type} (cr : CommutativeRing R)
    (c : R) (p q : Polynomial R) (x : R) :
  peval (cring R cr) (pcomp cr (pscale (cring R cr) c p) q) x =
  rmul R (cring R cr) c (peval (cring R cr) (pcomp cr p q) x).
Proof.
  rewrite (peval_pcomp cr).
  rewrite (peval_pscale_com cr).
  rewrite (peval_pcomp cr).
  reflexivity.
Qed.
