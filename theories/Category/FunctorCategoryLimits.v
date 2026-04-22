(** * Category/FunctorCategoryLimits.v
    Pointwise limits in functor categories.
    If C has limits of shape J, then [I, C] has limits of shape J
    computed pointwise (Example 2.11.11(2)). *)

Require Import CAG.Category.Core.
Require Import CAG.Category.Functor.
Require Import CAG.Category.Limits.
Require Import CAG.Category.PreservesLimits.

Set Universe Polymorphism.
Open Scope cat_scope.

(* ------------------------------------------------------------------ *)
(** ** Evaluation functor  Ev_E : [I, C] -> C                          *)
(*                                                                      *)
(*   Ev_E(F) := F(E),   Ev_E(α) := α_E                                 *)
(* ------------------------------------------------------------------ *)

Definition EvalFunctor {I C : Category} (E : I.(Ob)) :
    Functor (FunctorCat I C) C.
Proof.
  apply (Build_Functor (FunctorCat I C) C
    (fun F => F ## E)
    (fun F G α => α.(component) E)).
  - intros F. reflexivity.
  - intros F G H β α. reflexivity.
Defined.

(* ------------------------------------------------------------------ *)
(** ** Pointwise limits in [I, C]                                       *)
(*                                                                      *)
(*   Given D : J -> [I, C], the pointwise limit lim_j D_j               *)
(*   sends each i : I to the limit of the diagram                       *)
(*   D(-)(i) : J -> C                                                   *)
(*   (i.e., the j-th functor D_j evaluated at i).                       *)
(*                                                                      *)
(*   The limit functor I -> C is defined by choosing,                   *)
(*   for each i, a limit of the pointwise diagram.                       *)
(* ------------------------------------------------------------------ *)

(** Pointwise diagram at i: evaluates each D_j at i. *)
Definition pointwise_diagram {I J C : Category}
    (D : Functor J (FunctorCat I C)) (i : I.(Ob)) :
    Functor J C.
Proof.
  apply (Build_Functor J C
    (fun j => (D ## j) ## i)
    (fun j1 j2 u => (D #> u).(component) i)).
  - intros j. cbn.
    assert (H := D.(fmap_id) j). cbn in H.
    exact (f_equal (fun α => α.(component) i) H).
  - intros j1 j2 j3 u v. cbn.
    assert (H := D.(fmap_comp) u v). cbn in H.
    exact (f_equal (fun α => α.(component) i) H).
Defined.

(** If C has limits of shape J, then [I,C] has limits of shape J,
    computed pointwise. *)
Theorem functor_category_limits {I J C : Category}
    (hlim : HasLimitsOfShape J C) :
    HasLimitsOfShape J (FunctorCat I C).
Proof.
  intros D.
  (* For each i : I, take the limit of the pointwise diagram *)
  pose (Lc := fun i => projT1 (hlim (pointwise_diagram D i))).
  pose (LH := fun i => projT2 (hlim (pointwise_diagram D i))).
  (* cone_comm for the morphism-induced cone *)
  assert (fc_comm : forall (i i' : I.(Ob)) (f : I⟦i, i'⟧)
      {j1 j2 : J.(Ob)} (u : J⟦j1, j2⟧),
      (pointwise_diagram D i') #> u ∘ ((D ## j1) #> f ∘ cone_map (Lc i) j1)
      = (D ## j2) #> f ∘ cone_map (Lc i) j2).
  { intros i i' f j1 j2 u. cbn.
    rewrite C.(comp_assoc).
    assert (Hnat := (D #> u).(naturality) f). cbn in Hnat.
    rewrite <- Hnat, <- C.(comp_assoc).
    assert (Hcc := (Lc i).(cone_comm) u). cbn in Hcc.
    rewrite Hcc. reflexivity. }
  (* For f : I⟦i,i'⟧, a cone over pointwise D i' with vertex cone_vertex (Lc i) *)
  pose (fmap_cone := fun (i i' : I.(Ob)) (f : I⟦i, i'⟧) =>
    Build_Cone J C (pointwise_diagram D i')
      (cone_vertex (Lc i))
      (fun j => (D ## j) #> f ∘ cone_map (Lc i) j)
      (fun j1 j2 u => fc_comm i i' f j1 j2 u)).
  (* Functoriality: identity *)
  assert (L_id : forall i,
      lim_med (LH i) (fmap_cone i i (I.(id) i)) = C.(id) (cone_vertex (Lc i))).
  { intro i. symmetry.
    apply ((LH i).(lim_med_uniq) (fmap_cone i i (I.(id) i))).
    intro j. cbn.
    rewrite C.(id_right), (D ## j).(fmap_id). symmetry. apply C.(id_left). }
  (* Functoriality: composition *)
  assert (L_comp : forall {i i' i'' : I.(Ob)} (f : I⟦i', i''⟧) (g : I⟦i, i'⟧),
      lim_med (LH i'') (fmap_cone i i'' (f ∘ g)) =
      lim_med (LH i'') (fmap_cone i' i'' f) ∘ lim_med (LH i') (fmap_cone i i' g)).
  { intros i i' i'' f g. symmetry.
    apply ((LH i'').(lim_med_uniq) (fmap_cone i i'' (f ∘ g))).
    intro j.
    exact (eq_trans (C.(comp_assoc) _ _ _)
          (eq_trans (f_equal (fun x => x ∘ lim_med (LH i') (fmap_cone i i' g))
                             ((LH i'').(lim_med_comm) (fmap_cone i' i'' f) j))
          (eq_trans (eq_sym (C.(comp_assoc) _ _ _))
          (eq_trans (f_equal (fun x => (D ## j) #> f ∘ x)
                             ((LH i').(lim_med_comm) (fmap_cone i i' g) j))
          (eq_trans (C.(comp_assoc) _ _ _)
          (f_equal (fun x => x ∘ cone_map (Lc i) j)
                   (eq_sym ((D ## j).(fmap_comp) f g)))))))). }
  (* The limit functor L : I -> C *)
  pose (L := Build_Functor I C
    (fun i => cone_vertex (Lc i))
    (fun i i' f => lim_med (LH i') (fmap_cone i i' f))
    L_id
    L_comp).
  (* Naturality of cone maps j: L ⟹ D ## j *)
  assert (cm_nat : forall (j : J.(Ob)) {i i' : I.(Ob)} (f : I⟦i, i'⟧),
      (D ## j) #> f ∘ cone_map (Lc i) j =
      cone_map (Lc i') j ∘ lim_med (LH i') (fmap_cone i i' f)).
  { intros j i i' f. symmetry.
    exact ((LH i').(lim_med_comm) (fmap_cone i i' f) j). }
  (* Cone maps mk_cone_map j : L ⟹ D ## j *)
  pose (mk_cone_map := fun (j : J.(Ob)) =>
    Build_NatTrans I C L (D ## j)
      (fun i => cone_map (Lc i) j)
      (fun i i' f => cm_nat j i i' f)).
  (* cone_comm for the limit cone in FunctorCat *)
  assert (lc_comm : forall {j1 j2 : J.(Ob)} (u : J⟦j1, j2⟧),
      D #> u ∘ mk_cone_map j1 = mk_cone_map j2).
  { intros j1 j2 u. apply nattrans_eq. intro i. cbn.
    assert (Hcc := (Lc i).(cone_comm) u). cbn in Hcc. exact Hcc. }
  (* K_i: for K : Cone D and i : I, the pointwise cone at i *)
  pose (K_i := fun (K : Cone D) (i : I.(Ob)) =>
    Build_Cone J C (pointwise_diagram D i)
      ((cone_vertex K) ## i)
      (fun j => (K.(cone_map) j).(component) i)
      (fun j1 j2 u => f_equal (fun α => α.(component) i) (K.(cone_comm) u))).
  (* Naturality of the mediating morphisms *)
  assert (mu_nat : forall (K : Cone D) {i i' : I.(Ob)} (f : I⟦i, i'⟧),
      lim_med (LH i') (fmap_cone i i' f) ∘ lim_med (LH i) (K_i K i) =
      lim_med (LH i') (K_i K i') ∘ (cone_vertex K) #> f).
  { intros K i i' f.
    assert (kpp_comm : forall {j1 j2 : J.(Ob)} (u : J⟦j1, j2⟧),
        (pointwise_diagram D i') #> u ∘
          ((D ## j1) #> f ∘ (K.(cone_map) j1).(component) i)
        = (D ## j2) #> f ∘ (K.(cone_map) j2).(component) i).
    { intros j1 j2 u. cbn.
      rewrite C.(comp_assoc).
      assert (Hnat := (D #> u).(naturality) f). cbn in Hnat.
      rewrite <- Hnat, <- C.(comp_assoc).
      apply f_equal.
      exact (f_equal (fun α => α.(component) i) (K.(cone_comm) u)). }
    pose (K'' := Build_Cone J C (pointwise_diagram D i')
      ((cone_vertex K) ## i)
      (fun j => (D ## j) #> f ∘ (K.(cone_map) j).(component) i)
      (fun j1 j2 u => kpp_comm j1 j2 u)).
    transitivity (lim_med (LH i') K'').
    - apply ((LH i').(lim_med_uniq) K''). intro j.
      exact (eq_trans (C.(comp_assoc) _ _ _)
            (eq_trans (f_equal (fun x => x ∘ lim_med (LH i) (K_i K i))
                               ((LH i').(lim_med_comm) (fmap_cone i i' f) j))
            (eq_trans (eq_sym (C.(comp_assoc) _ _ _))
            (f_equal (fun x => (D ## j) #> f ∘ x)
                     ((LH i).(lim_med_comm) (K_i K i) j))))).
    - symmetry. apply ((LH i').(lim_med_uniq) K''). intro j.
      exact (eq_trans (C.(comp_assoc) _ _ _)
            (eq_trans (f_equal (fun x => x ∘ (cone_vertex K) #> f)
                               ((LH i').(lim_med_comm) (K_i K i') j))
            (eq_sym ((K.(cone_map) j).(naturality) f)))). }
  (* Build and return the limit *)
  apply (existT _ (Build_Cone J (FunctorCat I C) D L mk_cone_map lc_comm)).
  unshelve econstructor.
  - (* lim_med: mediating NatTrans for any cone K over D *)
    exact (fun K => Build_NatTrans I C (cone_vertex K) L
      (fun i => lim_med (LH i) (K_i K i))
      (fun i i' f => mu_nat K i i' f)).
  - (* lim_med_comm *)
    intros K j. apply nattrans_eq. intro i. cbn.
    exact ((LH i).(lim_med_comm) (K_i K i) j).
  - (* lim_med_uniq *)
    intros K v Hv. apply nattrans_eq. intro i. cbn.
    apply ((LH i).(lim_med_uniq) (K_i K i)).
    intro j. exact (f_equal (fun α => α.(component) i) (Hv j)).
Defined.

(** Corollary: Evaluation functor preserves limits. *)
Theorem eval_preserves_limits {I J C : Category}
    (hlim : HasLimitsOfShape J C) (E : I.(Ob)) :
    PreservesLimitsOfShape J (EvalFunctor E) (C := FunctorCat I C).
Proof.
  intros D L HL.
  pose (LcE := projT1 (hlim (pointwise_diagram D E))).
  pose (LHE := projT2 (hlim (pointwise_diagram D E))).
  (* Get the pointwise limit functor from functor_category_limits *)
  pose (LF := projT1 (functor_category_limits hlim D)).
  pose (HLF := projT2 (functor_category_limits hlim D)).
  (* cone_fmap (EvalFunctor E) LF has vertex LcE.cv and maps cone_map LcE j
     (definitionally, since functor_category_limits is Defined).
     Build IsLimit directly from LHE. *)
  assert (HLF_E : IsLimit (cone_fmap (EvalFunctor E) LF)).
  { refine (@Build_IsLimit J C (FunctorComp (EvalFunctor E) D)
        (cone_fmap (EvalFunctor E) LF)
        (fun K => lim_med LHE K)
        _ _).
    - intros K j. cbn. exact (LHE.(lim_med_comm) K j).
    - intros K v Hv. apply (LHE.(lim_med_uniq) K).
      intro j. exact (Hv j). }
  (* The two mediating NatTrans linking L and LF *)
  set (φ := HL.(lim_med) LF).    (* NatTrans (cone_vertex LF) (cone_vertex L) *)
  set (ψ := HLF.(lim_med) L).    (* NatTrans (cone_vertex L) (cone_vertex LF) *)
  (* φ ∘N ψ = NatId (cone_vertex L) *)
  assert (φψ_eq_id : φ ∘N ψ = NatId (cone_vertex L)).
  { transitivity (HL.(lim_med) L).
    - apply (HL.(lim_med_uniq) L). intro j.
      apply nattrans_eq. intro i. cbn.
      exact (eq_trans (C.(comp_assoc) _ _ _)
            (eq_trans (f_equal (fun x => x ∘ ψ.(component) i)
                               (f_equal (fun α => α.(component) i)
                                        (HL.(lim_med_comm) LF j)))
            (f_equal (fun α => α.(component) i) (HLF.(lim_med_comm) L j)))).
    - symmetry. apply (HL.(lim_med_uniq) L). intro j.
      apply nattrans_eq. intro i. cbn.
      exact (C.(id_right) _). }
  (* Extract the identity at component E *)
  assert (φψ_id_E : φ.(component) E ∘ ψ.(component) E =
      C.(id) ((cone_vertex L) ## E)).
  { exact (f_equal (fun α => α.(component) E) φψ_eq_id). }
  (* φ commutes with cone maps at E:
     (cone_map L j).component E ∘ φ.component E = cone_map LcE j *)
  assert (φ_comm_E : forall j,
      (cone_map L j).(component) E ∘ φ.(component) E = cone_map LcE j).
  { intro j.
    assert (H := f_equal (fun α => α.(component) E)
                    (HL.(lim_med_comm) LF j)).
    cbn in H. exact H. }
  (* ψ commutes with cone maps at E:
     cone_map LcE j ∘ ψ.component E = (cone_map L j).component E *)
  assert (ψ_comm_E : forall j,
      cone_map LcE j ∘ ψ.(component) E = (cone_map L j).(component) E).
  { intro j.
    assert (H := f_equal (fun α => α.(component) E)
                    (HLF.(lim_med_comm) L j)).
    cbn in H. exact H. }
  (* Build IsLimit for cone_fmap (EvalFunctor E) L *)
  refine (@Build_IsLimit J C (FunctorComp (EvalFunctor E) D)
      (cone_fmap (EvalFunctor E) L)
      (fun K => φ.(component) E ∘ lim_med LHE K)
      _ _).
  - (* lim_med_comm *)
    intros K j. cbn.
    rewrite C.(comp_assoc), φ_comm_E.
    exact (LHE.(lim_med_comm) K j).
  - (* lim_med_uniq *)
    intros K v Hv.
    (* Show ψ.component E ∘ v = lim_med LHE K *)
    assert (ψv_eq : ψ.(component) E ∘ v = lim_med LHE K).
    { apply (LHE.(lim_med_uniq) K). intro j.
      rewrite C.(comp_assoc), ψ_comm_E. exact (Hv j). }
    (* Conclude v = φ.cE ∘ lim_med LHE K using φ ∘ ψ = id *)
    symmetry. transitivity (φ.(component) E ∘ (ψ.(component) E ∘ v)).
    + rewrite ψv_eq. reflexivity.
    + rewrite C.(comp_assoc), φψ_id_E. apply C.(id_left).
Qed.

