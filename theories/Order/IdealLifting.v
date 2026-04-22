(** * Order/IdealLifting.v
    Ideal lifting of finite-join-preserving maps,
    and Corollary 1.5.19. *)

Require Import CAG.Order.Poset.
Require Import CAG.Order.Lattice.
Require Import CAG.Order.DCPO.
Require Import CAG.Order.Compact.
Require Import CAG.Order.Ideal.
Require Import CAG.Order.Adjunction.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Logic.Classical.
From Stdlib Require Import Lists.List.

Open Scope order_scope.

(** ** Finite-join-preserving map *)

Record FinJoinMap (J K : JoinSemilattice) : Type := {
  fjm_map  :> J.(carrier) -> K.(carrier);
  fjm_mono : forall x y, x ≤[J] y -> fjm_map x ≤[K] fjm_map y;
  fjm_bot  : fjm_map ⊥{J} = ⊥{K};
  fjm_join : forall x y, fjm_map (x ∨{J} y) = fjm_map x ∨{K} fjm_map y;
}.

Arguments fjm_map  {J K}.
Arguments fjm_mono {J K}.
Arguments fjm_bot  {J K}.
Arguments fjm_join {J K}.

(** ** Ideal lifting: extend f : J -> A to f̄ : IdCompl J -> A *)

(** Given f : J -> A where J is a JSL and A is an algebraic complete lattice,
    define f̄(I) = ⊔ {f(x) | x ∈ I}. *)

Definition ideal_lift_fn (J : JoinSemilattice) (A : CompleteLattice)
    (f : J.(carrier) -> A.(carrier))
    (I : { I' : J.(carrier) -> Prop | IsIdeal J I' }) :
    A.(carrier) :=
  ⊔{A} (fun y => exists x, proj1_sig I x /\ y = f x).

(** f̄ is monotone *)
Lemma ideal_lift_mono (J : JoinSemilattice) (A : CompleteLattice)
    (f : J.(carrier) -> A.(carrier))
    (I1 I2 : { I' : J.(carrier) -> Prop | IsIdeal J I' }) :
    I1 ≤[IdCompl J] I2 ->
    ideal_lift_fn J A f I1 ≤[A] ideal_lift_fn J A f I2.
Proof.
  intros H12. unfold ideal_lift_fn.
  apply A.(cl_sup_lub). intros y [x [Hx Hy]].
  apply A.(cl_sup_ub). exists x. split.
  - apply H12. exact Hx.
  - exact Hy.
Qed.

(** f̄ preserves directed joins *)
Lemma ideal_lift_cont (J : JoinSemilattice) (A : CompleteLattice)
    (f : J.(carrier) -> A.(carrier)) :
    PreservesDirectedJoins (IdealCompl_CompleteLattice J) A
      (@Build_MonotoneMap (IdealCompl_CompleteLattice J) A
         (ideal_lift_fn J A f)
         (ideal_lift_mono J A f)).
Proof.
  intros D hD.
  apply A.(le_antisym).
  - (* ideal_lift_fn J A f (⊔{L} D) ≤ ⊔{A} {ideal_lift_fn J A f I | I ∈ D} *)
    unfold ideal_lift_fn at 1.
    apply A.(cl_sup_lub).
    intros y [x [Hx Hy]].
    cbn in Hx. unfold ideal_generated in Hx.
    destruct Hx as [xs [Hxs Hxle]].
    destruct (directed_covers_finite_list J D hD xs Hxs) as [Iz [HIz Hiz]].
    apply A.(le_trans) with (ideal_lift_fn J A f Iz).
    + subst y. unfold ideal_lift_fn.
      apply A.(cl_sup_ub). exists x. split.
      * apply (ideal_down J _ (proj2_sig Iz) (finite_join J xs) x).
        -- exact (ideal_finite_join_closed_pre J _ (proj2_sig Iz) xs Hiz).
        -- exact Hxle.
      * reflexivity.
    + apply A.(cl_sup_ub). exists Iz. split. exact HIz. reflexivity.
  - (* ⊔{A} {ideal_lift_fn J A f I | I ∈ D} ≤ ideal_lift_fn J A f (⊔{L} D) *)
    apply A.(cl_sup_lub).
    intros y [I [HI Hy]].
    subst y. unfold ideal_lift_fn.
    apply A.(cl_sup_lub).
    intros z [x [Hx Hz]].
    apply A.(cl_sup_ub). exists x. split.
    + cbn. unfold ideal_generated.
      exists (x :: nil). split.
      * intros w Hw. simpl in Hw. destruct Hw as [<- | []].
        exists I. split. exact HI. exact Hx.
      * simpl. apply J.(jsl_join_ub1).
    + exact Hz.
Qed.

(** f̄ maps bottom ideal to bottom *)
Lemma ideal_lift_preserves_bot (J : JoinSemilattice) (A : CompleteLattice)
    (f : J.(carrier) -> A.(carrier))
    (hf_bot : f ⊥{J} = cl_bot A) :
    ideal_lift_fn J A f (cl_bot (IdealCompl_CompleteLattice J)) = cl_bot A.
Proof.
  unfold ideal_lift_fn, cl_bot.
  apply A.(le_antisym).
  - (* ⊔{f x | x ∈ ⊥↓} ≤ cl_bot A *)
    apply A.(cl_sup_lub).
    intros y [x [Hx Hy]].
    (* Hx : proj1_sig (cl_bot (IdealCompl_CompleteLattice J)) x *)
    cbn in Hx. unfold ideal_generated in Hx.
    destruct Hx as [xs [Hxs Hxle]].
    destruct xs as [| h t].
    + (* xs = []: x ≤ ⊥{J} so x = ⊥{J} *)
      simpl in Hxle.
      assert (Heqx : x = ⊥{J}).
      { apply J.(le_antisym). exact Hxle. apply J.(jsl_bot_le). }
      subst x. subst y. rewrite hf_bot. apply A.(le_refl).
    + (* xs nonempty: contradiction with Hxs *)
      exfalso.
      destruct (Hxs h (or_introl eq_refl)) as [I [HI _]]. exact HI.
  - (* cl_bot A ≤ ⊔{f x | x ∈ ⊥↓} *)
    apply cl_bot_le.
Qed.

(** f̄ is the unique join-preserving extension of f *)
Lemma ideal_lift_universal (J : JoinSemilattice) (A : AlgCompleteLattice)
    (f : FinJoinMap J (cl_to_jsl A))
    (g : { I : J.(carrier) -> Prop | IsIdeal J I } -> A.(carrier))
    (hg_mono : forall I1 I2, I1 ≤[IdCompl J] I2 -> g I1 ≤[A] g I2)
    (hg_all_joins : PreservesAllJoins (IdealCompl_CompleteLattice J) A
        (@Build_MonotoneMap (IdealCompl_CompleteLattice J) A g hg_mono))
    (hg_ext : forall x, g (x ↓i{J}) = f x) :
    forall I, g I = ideal_lift_fn J A f I.
Proof.
  intro I.
  (* The family of principal sub-ideals of I *)
  set (principals := fun I' : { I' : J.(carrier) -> Prop | IsIdeal J I'} =>
            exists x, proj1_sig I x /\ I' = (x ↓i{J})).
  (* Every ideal equals the sup of its principal sub-ideals *)
  assert (HsupP : cl_sup (IdealCompl_CompleteLattice J) principals = I).
  { apply (le_antisym (IdealCompletion J)).
    - (* sup principals ≤ I *)
      intros z Hz. cbn in Hz. unfold ideal_generated in Hz.
      destruct Hz as [xs [Hxs Hzle]].
      apply (ideal_down J _ (proj2_sig I) (finite_join J xs) z).
      + apply (ideal_finite_join_closed_pre J _ (proj2_sig I) xs).
        intros xi Hxi.
        destruct (Hxs xi Hxi) as [I' [HPI' HIxi]].
        unfold principals in HPI'.
        destruct HPI' as [x [Hx HI'eq]]. subst I'.
        exact (ideal_down J _ (proj2_sig I) x xi Hx HIxi).
      + exact Hzle.
    - (* I ≤ sup principals *)
      intros y Hy. cbn. unfold ideal_generated.
      exists (y :: nil). split.
      + intros w Hw. simpl in Hw. destruct Hw as [<- | []].
        exists (y ↓i{J}). split.
        * unfold principals. exists y. split. exact Hy. reflexivity.
        * cbn. apply J.(le_refl).
      + simpl. apply J.(jsl_join_ub1).
  }
  (* g I = ⊔{A} {g I' | principals I'} by hg_all_joins *)
  assert (HgI : g I = ⊔{A} (fun y => exists I', principals I' /\ y = g I')).
  { rewrite <- HsupP. apply (hg_all_joins principals). }
  rewrite HgI. unfold ideal_lift_fn.
  apply A.(le_antisym).
  - (* ⊔{g I' | principals I'} ≤ ⊔{f x | x ∈ I} *)
    apply A.(cl_sup_lub).
    intros y [I' [HPI' ->]].
    unfold principals in HPI'.
    destruct HPI' as [x [Hx ->]].
    rewrite hg_ext.
    apply A.(cl_sup_ub). exists x. split. exact Hx. reflexivity.
  - (* ⊔{f x | x ∈ I} ≤ ⊔{g I' | principals I'} *)
    apply A.(cl_sup_lub).
    intros y [x [Hx ->]].
    apply A.(cl_sup_ub).
    exists (x ↓i{J}). split.
    + unfold principals. exists x. split. exact Hx. reflexivity.
    + rewrite hg_ext. reflexivity.
Qed.

(** ** Ideal lifting between JSLs *)

(** If f : J -> K preserves finite joins,
    define f̄ : IdCompl J -> IdCompl K by
    f̄(I) = ideal generated by {f(x) | x ∈ I}. *)

Definition ideal_lift_jsl (J K : JoinSemilattice)
    (f : FinJoinMap J K)
    (I : { I' : J.(carrier) -> Prop | IsIdeal J I' }) :
    { I' : K.(carrier) -> Prop | IsIdeal K I' }.
Proof.
  exists (fun y => exists x, proj1_sig I x /\ y ≤[K] f x).
  constructor.
  - exists ⊥{J}. split.
    + apply (ideal_bot _ _ (proj2_sig I)).
    + rewrite (fjm_bot f). apply K.(le_refl).
  - intros a b [x [Hx Ha]] [y [Hy Hb]].
    exists (x ∨{J} y). split.
    + apply (ideal_join _ _ (proj2_sig I)); assumption.
    + rewrite (fjm_join f).
      apply K.(jsl_join_lub).
      * apply K.(le_trans) with (fjm_map f x). exact Ha. apply K.(jsl_join_ub1).
      * apply K.(le_trans) with (fjm_map f y). exact Hb. apply K.(jsl_join_ub2).
  - intros a b [x [Hx Ha]] Hle.
    exists x. split. exact Hx.
    apply K.(le_trans) with a; assumption.
Defined.

Lemma ideal_lift_jsl_mono (J K : JoinSemilattice) (f : FinJoinMap J K) :
    forall I1 I2 : { I' : J.(carrier) -> Prop | IsIdeal J I' },
      I1 ≤[IdCompl J] I2 ->
      ideal_lift_jsl J K f I1 ≤[IdCompl K] ideal_lift_jsl J K f I2.
Proof.
  intros I1 I2 H12 z [x [Hx Hz]].
  cbn. exists x. split.
  - apply H12. exact Hx.
  - exact Hz.
Qed.

(** Helper: finite join of f-images equals f of finite join *)
Lemma fjm_preserves_finite_join (J K : JoinSemilattice) (f : FinJoinMap J K)
    (xs : list J.(carrier)) :
    fjm_map f (finite_join J xs) = finite_join K (List.map (fjm_map f) xs).
Proof.
  induction xs as [| x xs' IH].
  - simpl. exact (fjm_bot f).
  - simpl. rewrite (fjm_join f). rewrite IH. reflexivity.
Qed.

(** f̄ preserves all joins *)
Lemma ideal_lift_jsl_all_joins (J K : JoinSemilattice) (f : FinJoinMap J K) :
    PreservesAllJoins (IdealCompl_CompleteLattice J) (IdealCompl_CompleteLattice K)
      (@Build_MonotoneMap (IdealCompl_CompleteLattice J) (IdealCompl_CompleteLattice K)
         (ideal_lift_jsl J K f)
         (ideal_lift_jsl_mono J K f)).
Proof.
  intro S.
  apply (le_antisym (IdealCompletion K)).
  - (* ideal_lift_jsl J K f (⊔ S) ≤ ⊔ {ideal_lift_jsl J K f I | I ∈ S} *)
    intros y Hy.
    cbn in Hy. destruct Hy as [x [Hx Hyx]].
    cbn in Hx. unfold ideal_generated in Hx.
    destruct Hx as [xs [Hxs Hxle]].
    cbn. unfold ideal_generated.
    exists (List.map (fjm_map f) xs). split.
    + intros w Hw.
      apply List.in_map_iff in Hw.
      destruct Hw as [xi [<- Hxi]].
      destruct (Hxs xi Hxi) as [I [HI HIxi]].
      exists (ideal_lift_jsl J K f I). split.
      * exists I. split. exact HI. reflexivity.
      * cbn. exists xi. split. exact HIxi. apply K.(le_refl).
    + apply K.(le_trans) with (fjm_map f x).
      * exact Hyx.
      * apply K.(le_trans) with (fjm_map f (finite_join J xs)).
        -- apply (fjm_mono f). exact Hxle.
        -- rewrite fjm_preserves_finite_join. apply K.(le_refl).
  - (* ⊔ {ideal_lift_jsl J K f I | I ∈ S} ≤ ideal_lift_jsl J K f (⊔ S) *)
    intros y Hy.
    cbn in Hy. unfold ideal_generated in Hy.
    destruct Hy as [ys [Hys Hyle]].
    (* A = ideal_lift_jsl J K f (cl_sup J S) is an ideal containing each yi *)
    set (A := ideal_lift_jsl J K f (cl_sup (IdealCompl_CompleteLattice J) S)).
    apply (ideal_down K _ (proj2_sig A) (finite_join K ys) y).
    + apply (ideal_finite_join_closed_pre K _ (proj2_sig A) ys).
      intros yi Hyi.
      destruct (Hys yi Hyi) as [J' [[I [HI ->]] HJ'yi]].
      cbn in HJ'yi. destruct HJ'yi as [xi [HIxi Hyixi]].
      (* yi ∈ A: need xi ∈ ideal_generated J union_S *)
      cbn. exists xi. split.
      * cbn. unfold ideal_generated.
        exists (xi :: nil). split.
        -- intros w Hw. simpl in Hw. destruct Hw as [<- | []].
           exists I. split. exact HI. exact HIxi.
        -- simpl. apply J.(jsl_join_ub1).
      * exact Hyixi.
    + exact Hyle.
Qed.

(** f̄ preserves compact elements *)
Lemma ideal_lift_jsl_compact (J K : JoinSemilattice) (f : FinJoinMap J K)
    (e : { I : J.(carrier) -> Prop | IsIdeal J I })
    (he : IsCompact (cl_to_dcpo (IdealCompl_CompleteLattice J)) e) :
    IsCompact (cl_to_dcpo (IdealCompl_CompleteLattice K)) (ideal_lift_jsl J K f e).
Proof.
  (* e compact => e = x↓ for some x *)
  destruct (compact_ideal_is_principal J e he) as [x Hx].
  (* ideal_lift_jsl f (x↓) = (f x)↓ *)
  assert (Heq : ideal_lift_jsl J K f e = ((fjm_map f x) ↓i{K})).
  { apply (le_antisym (IdealCompletion K)).
    - intros y [z [Hz Hyz]].
      cbn. apply K.(le_trans) with (fjm_map f z).
      + exact Hyz.
      + apply (fjm_mono f). rewrite Hx in Hz. cbn in Hz. exact Hz.
    - intros y Hy. cbn in Hy.
      cbn. exists x. split.
      + rewrite Hx. cbn. apply J.(le_refl).
      + exact Hy.
  }
  rewrite Heq.
  exact (principal_ideal_compact K (fjm_map f x)).

Qed.

(** ** Corollary 1.5.19

    If X, Y are algebraic complete lattices and f : X -> Y preserves all
    joins and compact elements, then there is a commuting square:

       X° → Y°        (f restricted to compact elements)
       ↓     ↓         (ideal completions)
       X  →  Y        (f itself)

    via the isomorphism X ≅ IdCompl(X°). *)

(** The compact elements of an algebraic CL form a JSL. *)
Definition compact_jsl (L : AlgCompleteLattice) : JoinSemilattice.
Proof.
  refine {|
    jsl_poset  := SubPoset L (IsCompact (cl_to_dcpo L));
    jsl_bot    := exist _ (cl_bot L) (compact_bot L);
    jsl_join   := fun e1 e2 =>
      exist _ (cl_join L (proj1_sig e1) (proj1_sig e2))
             (compact_join L _ _ (proj2_sig e1) (proj2_sig e2));
    jsl_bot_le := _;
    jsl_join_ub1 := _;
    jsl_join_ub2 := _;
    jsl_join_lub := _;
  |}.
  - intros [x hx]. cbn. apply cl_bot_le.
  - intros [x hx] [y hy]. cbn. apply cl_join_ub1.
  - intros [x hx] [y hy]. cbn. apply cl_join_ub2.
  - intros [x hx] [y hy] [z hz] H1 H2. cbn in *.
    apply cl_join_lub; assumption.
Defined.

(** theta : IdCompl(X°) -> X by I ↦ sup I *)
Definition theta (L : AlgCompleteLattice) :
    { I : (compact_jsl L).(carrier) -> Prop | IsIdeal (compact_jsl L) I } ->
    L.(carrier) :=
  fun I => ⊔{L} (fun x => exists e : (compact_jsl L).(carrier),
                              proj1_sig I e /\ x = proj1_sig e).

(** theta^{-1} : X -> IdCompl(X°) by x ↦ {e compact | e ≤ x} *)
Definition theta_inv (L : AlgCompleteLattice) :
    L.(carrier) ->
    { I : (compact_jsl L).(carrier) -> Prop | IsIdeal (compact_jsl L) I }.
Proof.
  intros x.
  exists (fun e => proj1_sig e ≤[L] x).
  constructor.
  - cbn. apply cl_bot_le.
  - intros [e1 he1] [e2 he2] H1 H2. cbn in *.
    apply cl_join_lub; assumption.
  - intros [e1 he1] [e2 he2] H1 H2. cbn in *.
    apply L.(le_trans) with (proj1_sig (exist _ e1 he1)); assumption.
Defined.

(** theta is an isomorphism *)
Theorem theta_iso (L : AlgCompleteLattice) :
    forall I, theta_inv L (theta L I) = I /\ forall x, theta L (theta_inv L x) = x.
Proof.
  intro I. split.
  - (* theta_inv L (theta L I) = I *)
    apply (le_antisym (IdealCompletion (compact_jsl L))).
    + (* theta_inv L (theta L I) ≤ I:
         for each e compact with proj1_sig e ≤ theta L I, e ∈ I *)
      intros e He.
      cbn in He. unfold theta in He.
      set (S := fun y : L.(carrier) =>
            exists e' : (compact_jsl L).(carrier), proj1_sig I e' /\ y = proj1_sig e').
      assert (hSD : IsDirected L S).
      { constructor.
        - unfold S. exists (proj1_sig (⊥{compact_jsl L})).
          exists ⊥{compact_jsl L}. split.
          + exact (ideal_bot _ _ (proj2_sig I)).
          + reflexivity.
        - intros y1 y2 Hy1 Hy2.
          unfold S in Hy1, Hy2.
          destruct Hy1 as [e1 [He1 ->]].
          destruct Hy2 as [e2 [He2 ->]].
          exists (proj1_sig (e1 ∨{compact_jsl L} e2)). split.
          + unfold S. exists (e1 ∨{compact_jsl L} e2). split.
            * exact (ideal_join _ _ (proj2_sig I) _ _ He1 He2).
            * reflexivity.
          + split. apply cl_join_ub1. apply cl_join_ub2.
      }
      destruct ((proj2_sig e) S hSD He) as [d [Hd Hed]].
      unfold S in Hd. destruct Hd as [e' [He' ->]].
      exact (ideal_down (compact_jsl L) _ (proj2_sig I) e' e He' Hed).
    + (* I ≤ theta_inv L (theta L I):
         for each e ∈ I, proj1_sig e ≤ theta L I *)
      intros e He.
      cbn. unfold theta.
      apply L.(cl_sup_ub).
      exists e. split. exact He. reflexivity.
  - (* theta L (theta_inv L x) = x *)
    intro x. apply L.(le_antisym).
    + (* ⊔{L} {proj1_sig e | e compact, e ≤ x} ≤ x *)
      apply L.(cl_sup_lub).
      intros y [e [He ->]].
      exact He.
    + (* x ≤ ⊔{L} {proj1_sig e | e compact, e ≤ x} *)
      apply L.(le_trans) with
        (⊔{L} (fun e => IsCompact (cl_to_dcpo L) e /\ e ≤[L] x)).
      * rewrite <- (acl_eq_compact_sup L x). apply L.(le_refl).
      * apply L.(cl_sup_lub).
        intros y [hy hyx].
        apply L.(cl_sup_ub).
        exists (exist _ y hy). split. exact hyx. reflexivity.
Qed.
