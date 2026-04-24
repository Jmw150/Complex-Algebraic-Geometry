(** * Ideals.v — Ideals and related constructions *)

From CAG Require Import Rings.Ring.
From Stdlib Require Import Arith Lia List.
Import ListNotations.

(* ================================================================== *)
(** ** Ideal predicates *)
(* ================================================================== *)

Section Ideals.
  Context {R : Type} (r : Ring R).

  (** Additive subgroup predicate *)
  Definition is_add_subgroup (I : R -> Prop) : Prop :=
    I (rzero R r) /\
    (forall a b, I a -> I b -> I (radd R r a b)) /\
    (forall a,   I a -> I (rneg R r a)).

  (** Left ideal: additive subgroup + closed under left ring multiplication *)
  Definition is_left_ideal (I : R -> Prop) : Prop :=
    is_add_subgroup I /\
    forall x a, I a -> I (rmul R r x a).

  (** Right ideal: additive subgroup + closed under right ring multiplication *)
  Definition is_right_ideal (I : R -> Prop) : Prop :=
    is_add_subgroup I /\
    forall a x, I a -> I (rmul R r a x).

  (** Two-sided ideal: both left and right *)
  Definition is_ideal (I : R -> Prop) : Prop :=
    is_left_ideal I /\ is_right_ideal I.

  (** Sum of ideals: I + J = { a + b | a ∈ I, b ∈ J } *)
  Definition ideal_sum (I J : R -> Prop) : R -> Prop :=
    fun x => exists a b, I a /\ J b /\ x = radd R r a b.

  (** Product of ideals: IJ = finite sums of products a*b, a∈I, b∈J *)
  Definition ideal_product (I J : R -> Prop) : R -> Prop :=
    fun x =>
      exists l : list (R * R),
        (forall ab, In ab l -> I (fst ab) /\ J (snd ab)) /\
        x = fold_left
              (fun acc ab => radd R r acc (rmul R r (fst ab) (snd ab)))
              l
              (rzero R r).

End Ideals.

Arguments is_left_ideal  {R} r I.
Arguments is_right_ideal {R} r I.
Arguments is_ideal        {R} r I.
Arguments ideal_sum       {R} r I J.
Arguments ideal_product   {R} r I J.

(* ================================================================== *)
(** ** Kernel and image of a ring hom *)
(* ================================================================== *)

Section KernelImage.
  Context {R S : Type} (r : Ring R) (s : Ring S).
  Context (rh : RingHom r s).

  (** Kernel: ker φ = { x : R | φ(x) = 0 } *)
  Definition kernel_ideal : R -> Prop :=
    fun x => rhom_fn rh x = rzero S s.

  (** Image: im φ = { y : S | ∃ x, φ(x) = y } *)
  Definition image_subring : S -> Prop :=
    fun y => exists x : R, rhom_fn rh x = y.

  (** Kernel is an ideal *)
  Lemma kernel_is_ideal : is_ideal r kernel_ideal.
  Proof.
    unfold is_ideal, is_left_ideal, is_right_ideal, is_add_subgroup, kernel_ideal.
    split; split; try split; try split.
    - (* 0 ∈ ker *)
      apply rhom_zero.
    - (* closed under add *)
      intros a b Ha Hb.
      rewrite rhom_add, Ha, Hb.
      apply radd_zero_r.
    - (* closed under neg *)
      intros a Ha.
      rewrite rhom_neg, Ha.
      assert (H0 : radd S s (rzero S s) (rneg S s (rzero S s)) = rzero S s)
        by apply radd_neg_r.
      rewrite (radd_zero_l s) in H0. exact H0.
    - (* left multiply *)
      intros x a Ha.
      rewrite rhom_mul, Ha.
      apply rmul_zero_r.
    - (* 0 ∈ ker (for right ideal subgroup) *)
      apply rhom_zero.
    - intros a b Ha Hb.
      rewrite rhom_add, Ha, Hb.
      apply radd_zero_r.
    - intros a Ha.
      rewrite rhom_neg, Ha.
      assert (H0 : radd S s (rzero S s) (rneg S s (rzero S s)) = rzero S s)
        by apply radd_neg_r.
      rewrite (radd_zero_l s) in H0. exact H0.
    - (* right multiply *)
      intros a x Ha.
      rewrite rhom_mul, Ha.
      apply rmul_zero_l.
  Qed.

  (** Image is a subring *)
  Lemma image_is_subring : is_subring s image_subring.
  Proof.
    unfold is_subring, image_subring.
    split; [| split; [| split; [| split]]].
    - exists (rzero R r). apply rhom_zero.
    - exists (rone R r). apply rhom_one.
    - intros a b [x Hx] [y Hy].
      exists (radd R r x y).
      rewrite rhom_add, Hx, Hy. reflexivity.
    - intros a b [x Hx] [y Hy].
      exists (rmul R r x y).
      rewrite rhom_mul, Hx, Hy. reflexivity.
    - intros a [x Hx].
      exists (rneg R r x).
      rewrite rhom_neg, Hx. reflexivity.
  Qed.

End KernelImage.

(* ================================================================== *)
(** ** Ideal sum and product are ideals *)
(* ================================================================== *)

Section IdealOps.
  Context {R : Type} (r : Ring R).

  (** Helper: additive inverse distributes over addition *)
  Lemma rneg_add_ideal (a b : R) :
      rneg R r (radd R r a b) = radd R r (rneg R r a) (rneg R r b).
  Proof.
    assert (Hsum : radd R r (radd R r (rneg R r a) (rneg R r b)) (radd R r a b) = rzero R r).
    { rewrite <- (radd_assoc R r (rneg R r a) (rneg R r b) (radd R r a b)).
      rewrite (radd_assoc R r (rneg R r b) a b).
      rewrite (radd_comm R r (rneg R r b) a).
      rewrite <- (radd_assoc R r a (rneg R r b) b).
      rewrite (radd_neg_l r b).
      rewrite (radd_zero_r R r a).
      apply (radd_neg_l r). }
    assert (step : radd R r
                     (radd R r (radd R r (rneg R r a) (rneg R r b)) (radd R r a b))
                     (rneg R r (radd R r a b)) = rneg R r (radd R r a b)).
    { rewrite Hsum. apply (radd_zero_l r). }
    rewrite <- radd_assoc in step.
    rewrite (radd_neg_r R r (radd R r a b)) in step.
    rewrite radd_zero_r in step.
    exact (eq_sym step).
  Qed.

  (** Helper: (a+b) + (c+d) = (a+c) + (b+d) *)
  Lemma radd_swap4 (a b c d : R) :
      radd R r (radd R r a b) (radd R r c d) =
      radd R r (radd R r a c) (radd R r b d).
  Proof.
    rewrite <- (radd_assoc R r a b (radd R r c d)).
    rewrite (radd_assoc R r b c d).
    rewrite (radd_comm R r b c).
    rewrite <- (radd_assoc R r c b d).
    rewrite (radd_assoc R r a c (radd R r b d)).
    reflexivity.
  Qed.

  Lemma ideal_sum_is_ideal (I J : R -> Prop)
      (HI : is_ideal r I) (HJ : is_ideal r J) :
      is_ideal r (ideal_sum r I J).
  Proof.
    unfold is_ideal, is_left_ideal, is_right_ideal, is_add_subgroup, ideal_sum.
    destruct HI as [[HI_sg HIleft] [_ HIright]].
    destruct HI_sg as [HI0 [HIadd HIneg]].
    destruct HJ as [[HJ_sg HJleft] [_ HJright]].
    destruct HJ_sg as [HJ0 [HJadd HJneg]].
    split; split; try split; try split.
    - (* 0 ∈ I+J *)
      exists (rzero R r), (rzero R r).
      split; [exact HI0 | split; [exact HJ0 |]].
      symmetry. apply radd_zero_r.
    - (* closed under add *)
      intros x y [a [b [Ha [Hb Hx]]]] [c [d [Hc [Hd Hy]]]].
      exists (radd R r a c), (radd R r b d).
      split; [apply HIadd; assumption |
      split; [apply HJadd; assumption |]].
      subst x y. apply radd_swap4.
    - (* closed under neg *)
      intros x [a [b [Ha [Hb Hx]]]].
      exists (rneg R r a), (rneg R r b).
      split; [apply HIneg; assumption |
      split; [apply HJneg; assumption |]].
      subst x. apply rneg_add_ideal.
    - (* left absorption: x*(a+b) = x*a + x*b *)
      intros x y [a [b [Ha [Hb Hy]]]].
      exists (rmul R r x a), (rmul R r x b).
      split; [apply HIleft; assumption |
      split; [apply HJleft; assumption |]].
      subst y. apply rmul_distrib_l.
    - (* 0 ∈ I+J for right ideal subgroup *)
      exists (rzero R r), (rzero R r).
      split; [exact HI0 | split; [exact HJ0 |]].
      symmetry. apply radd_zero_r.
    - intros x y [a [b [Ha [Hb Hx]]]] [c [d [Hc [Hd Hy]]]].
      exists (radd R r a c), (radd R r b d).
      split; [apply HIadd; assumption |
      split; [apply HJadd; assumption |]].
      subst x y. apply radd_swap4.
    - intros x [a [b [Ha [Hb Hx]]]].
      exists (rneg R r a), (rneg R r b).
      split; [apply HIneg; assumption |
      split; [apply HJneg; assumption |]].
      subst x. apply rneg_add_ideal.
    - (* right absorption: (a+b)*x = a*x + b*x *)
      intros y x [a [b [Ha [Hb Hy]]]].
      exists (rmul R r a x), (rmul R r b x).
      split; [apply HIright; assumption |
      split; [apply HJright; assumption |]].
      subst y. apply rmul_distrib_r.
  Qed.

  Lemma ideal_product_is_ideal (I J : R -> Prop)
      (HI : is_ideal r I) (HJ : is_ideal r J) :
      is_ideal r (ideal_product r I J).
  Proof.
    unfold is_ideal, is_left_ideal, is_right_ideal, is_add_subgroup, ideal_product.
    destruct HI as [[HI_sg HIleft] [_ HIright]].
    destruct HI_sg as [HI0 [HIadd HIneg]].
    destruct HJ as [[HJ_sg HJleft] [_ HJright]].
    destruct HJ_sg as [HJ0 [HJadd HJneg]].
    (* shift: fold_left f l acc = acc + fold_left f l 0 *)
    assert (fold_shift : forall (l : list (R * R)) (acc : R),
        fold_left (fun a ab => radd R r a (rmul R r (fst ab) (snd ab))) l acc =
        radd R r acc (fold_left (fun a ab => radd R r a (rmul R r (fst ab) (snd ab))) l (rzero R r))).
    { intros l. induction l as [| x xs IH].
      - intro acc. simpl. symmetry. apply radd_zero_r.
      - intro acc. simpl.
        rewrite IH.
        rewrite (IH (radd R r (rzero R r) (rmul R r (fst x) (snd x)))).
        rewrite (radd_zero_l r). symmetry. apply radd_assoc. }
    (* shift for the negated-fst fold *)
    assert (fold_shift_neg : forall (l : list (R * R)) (acc : R),
        fold_left (fun a ab => radd R r a (rmul R r (rneg R r (fst ab)) (snd ab))) l acc =
        radd R r acc (fold_left (fun a ab => radd R r a (rmul R r (rneg R r (fst ab)) (snd ab)))
                       l (rzero R r))).
    { intros l. induction l as [| x xs IH].
      - intro acc. simpl. symmetry. apply radd_zero_r.
      - intro acc. simpl.
        rewrite IH.
        rewrite (IH (radd R r (rzero R r) (rmul R r (rneg R r (fst x)) (snd x)))).
        rewrite (radd_zero_l r). symmetry. apply radd_assoc. }
    (* rneg (rzero) = rzero *)
    assert (rneg_zero : rneg R r (rzero R r) = rzero R r).
    { assert (H : radd R r (rzero R r) (rneg R r (rzero R r)) = rzero R r) by apply radd_neg_r.
      rewrite (radd_zero_l r) in H. exact H. }
    (* (-a)*b = -(a*b) *)
    assert (rneg_mul_l_loc : forall a b, rmul R r (rneg R r a) b = rneg R r (rmul R r a b)).
    { intros a b.
      assert (H : radd R r (rmul R r (rneg R r a) b) (rmul R r a b) = rzero R r).
      { rewrite <- (rmul_distrib_r R r (rneg R r a) a b).
        rewrite (radd_neg_l r a). apply rmul_zero_l. }
      assert (step : radd R r (radd R r (rmul R r (rneg R r a) b) (rmul R r a b))
                       (rneg R r (rmul R r a b)) = rneg R r (rmul R r a b)).
      { rewrite H. apply (radd_zero_l r). }
      rewrite <- radd_assoc in step. rewrite (radd_neg_r R r (rmul R r a b)) in step.
      rewrite radd_zero_r in step. exact step. }
    (* fold of negated-fst list = neg of fold *)
    assert (fold_neg : forall l : list (R * R),
        fold_left (fun a ab => radd R r a (rmul R r (rneg R r (fst ab)) (snd ab)))
          l (rzero R r) =
        rneg R r (fold_left (fun a ab => radd R r a (rmul R r (fst ab) (snd ab))) l (rzero R r))).
    { intro l. induction l as [| x xs IH].
      - simpl. exact (eq_sym rneg_zero).
      - simpl. rewrite !(radd_zero_l r).
        rewrite (fold_shift_neg xs (rmul R r (rneg R r (fst x)) (snd x))).
        rewrite rneg_mul_l_loc, IH, <- rneg_add_ideal.
        f_equal. symmetry. apply fold_shift. }
    (* one-step unfold of the fold *)
    assert (fold_step : forall (l : list (R * R)) (p : R * R),
        fold_left (fun a ab => radd R r a (rmul R r (fst ab) (snd ab))) (p :: l) (rzero R r) =
        radd R r (rmul R r (fst p) (snd p))
          (fold_left (fun a ab => radd R r a (rmul R r (fst ab) (snd ab))) l (rzero R r))).
    { intros l p. simpl. rewrite (radd_zero_l r). apply fold_shift. }
    (* helper: map with negated fst gives same fold as fold_neg *)
    assert (fold_map_neg : forall l : list (R * R),
        fold_left (fun a ab => radd R r a (rmul R r (fst ab) (snd ab)))
          (map (fun ab => (rneg R r (fst ab), snd ab)) l) (rzero R r) =
        rneg R r (fold_left (fun a ab => radd R r a (rmul R r (fst ab) (snd ab))) l (rzero R r))).
    { intro l. induction l as [| p ps IH]; simpl.
      - exact (eq_sym rneg_zero).
      - rewrite !(radd_zero_l r).
        rewrite (fold_shift (map (fun ab => (rneg R r (fst ab), snd ab)) ps) (rmul R r (rneg R r (fst p)) (snd p))).
        rewrite IH, rneg_mul_l_loc, <- rneg_add_ideal.
        f_equal. symmetry. apply fold_shift. }
    split; split; try split; try split.
    - (* 0 ∈ IJ *)
      exists []. split. intros ab []. simpl. reflexivity.
    - (* closed under add *)
      intros x y [l1 [Hl1 Hx]] [l2 [Hl2 Hy]]. subst x y.
      exists (l1 ++ l2). split.
      + intros ab Hab. rewrite in_app_iff in Hab.
        destruct Hab as [H|H]. exact (Hl1 ab H). exact (Hl2 ab H).
      + rewrite fold_left_app. symmetry. apply fold_shift.
    - (* closed under neg *)
      intros x [l [Hl Hx]]. subst x.
      exists (map (fun ab => (rneg R r (fst ab), snd ab)) l). split.
      + intros ab Hab. apply in_map_iff in Hab.
        destruct Hab as [ab' [Hfun Hin]]. subst ab. simpl.
        destruct (Hl ab' Hin) as [HI' HJ'].
        split. apply HIneg. exact HI'. exact HJ'.
      + symmetry. exact (fold_map_neg l).
    - (* left absorption: c * (IJ element) ∈ IJ *)
      intros c x [l [Hl Hx]]. subst x.
      exists (map (fun ab => (rmul R r c (fst ab), snd ab)) l). split.
      + intros ab Hab. apply in_map_iff in Hab.
        destruct Hab as [ab' [Hfun Hin]]. subst ab. simpl.
        destruct (Hl ab' Hin) as [HI' HJ'].
        split. apply HIleft. exact HI'. exact HJ'.
      + assert (Hfold_mul_l : forall l',
            fold_left (fun a ab => radd R r a (rmul R r (fst ab) (snd ab)))
              (map (fun ab => (rmul R r c (fst ab), snd ab)) l') (rzero R r) =
            rmul R r c (fold_left (fun a ab => radd R r a (rmul R r (fst ab) (snd ab))) l' (rzero R r))).
        { intro l'. induction l' as [| p ps IH]; simpl.
          - symmetry. apply rmul_zero_r.
          - rewrite !(radd_zero_l r).
            rewrite (fold_shift (map (fun ab => (rmul R r c (fst ab), snd ab)) ps)
                       (rmul R r (rmul R r c (fst p)) (snd p))).
            rewrite IH.
            rewrite <- (rmul_assoc R r c (fst p) (snd p)).
            rewrite <- rmul_distrib_l.
            f_equal. symmetry. apply fold_shift. }
        symmetry. exact (Hfold_mul_l l).
    - (* 0 ∈ IJ (right ideal subgroup) *)
      exists []. split. intros ab []. simpl. reflexivity.
    - (* closed under add (right) *)
      intros x y [l1 [Hl1 Hx]] [l2 [Hl2 Hy]]. subst x y.
      exists (l1 ++ l2). split.
      + intros ab Hab. rewrite in_app_iff in Hab.
        destruct Hab as [H|H]. exact (Hl1 ab H). exact (Hl2 ab H).
      + rewrite fold_left_app. symmetry. apply fold_shift.
    - (* closed under neg (right) *)
      intros x [l [Hl Hx]]. subst x.
      exists (map (fun ab => (rneg R r (fst ab), snd ab)) l). split.
      + intros ab Hab. apply in_map_iff in Hab.
        destruct Hab as [ab' [Hfun Hin]]. subst ab. simpl.
        destruct (Hl ab' Hin) as [HI' HJ'].
        split. apply HIneg. exact HI'. exact HJ'.
      + symmetry. exact (fold_map_neg l).
    - (* right absorption: (IJ element) * c ∈ IJ *)
      intros x c [l [Hl Hx]]. subst x.
      exists (map (fun ab => (fst ab, rmul R r (snd ab) c)) l). split.
      + intros ab Hab. apply in_map_iff in Hab.
        destruct Hab as [ab' [Hfun Hin]]. subst ab. simpl.
        destruct (Hl ab' Hin) as [HI' HJ'].
        split. exact HI'. apply HJright. exact HJ'.
      + assert (Hfold_mul_r : forall l',
            fold_left (fun a ab => radd R r a (rmul R r (fst ab) (snd ab)))
              (map (fun ab => (fst ab, rmul R r (snd ab) c)) l') (rzero R r) =
            rmul R r (fold_left (fun a ab => radd R r a (rmul R r (fst ab) (snd ab))) l' (rzero R r)) c).
        { intro l'. induction l' as [| p ps IH]; simpl.
          - symmetry. apply rmul_zero_l.
          - rewrite !(radd_zero_l r).
            rewrite (fold_shift (map (fun ab => (fst ab, rmul R r (snd ab) c)) ps)
                       (rmul R r (fst p) (rmul R r (snd p) c))).
            rewrite IH.
            rewrite (rmul_assoc R r (fst p) (snd p) c).
            rewrite <- rmul_distrib_r.
            f_equal. symmetry. apply fold_shift. }
        symmetry. exact (Hfold_mul_r l).
  Qed.

  (** IJ ⊆ I ∩ J *)
  Lemma ideal_product_subset_intersection (I J : R -> Prop)
      (HI : is_ideal r I) (HJ : is_ideal r J) :
      forall x, ideal_product r I J x -> I x /\ J x.
  Proof.
    intros x [l [Hl Hx]].
    subst x.
    destruct HI as [[HI_sg HIleft] [HI_sg' HIright]].
    destruct HI_sg as [HI0 [HIadd _]].
    destruct HJ as [[HJ_sg HJleft] [HJ_sg' HJright]].
    destruct HJ_sg as [HJ0 [HJadd _]].
    (* By induction on l, the fold result is in I and J *)
    assert (Hfold : forall (l' : list (R * R)) acc,
        I acc -> J acc ->
        (forall ab, In ab l' -> I (fst ab) /\ J (snd ab)) ->
        I (fold_left (fun a ab => radd R r a (rmul R r (fst ab) (snd ab))) l' acc) /\
        J (fold_left (fun a ab => radd R r a (rmul R r (fst ab) (snd ab))) l' acc)).
    { intros l'. induction l' as [| h t IHt].
      - intros acc HaccI HaccJ _. simpl. exact (conj HaccI HaccJ).
      - intros acc HaccI HaccJ Hmemb. simpl.
        apply IHt.
        + apply HIadd. exact HaccI.
          apply HIright. exact (proj1 (Hmemb h (in_eq h t))).
        + apply HJadd. exact HaccJ.
          apply HJleft. exact (proj2 (Hmemb h (in_eq h t))).
        + intros ab Hab. apply Hmemb. right. exact Hab. }
    apply Hfold.
    - exact HI0.
    - exact HJ0.
    - exact Hl.
  Qed.

End IdealOps.
