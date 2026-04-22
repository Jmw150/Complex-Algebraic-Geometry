(** * Category/UnderLimits.v
    Lemma 2.11.14: if G preserves limits of shape I and S has them,
    then (A ↓ G) has limits of shape I, preserved by the forgetful functor. *)

Require Import CAG.Category.Core.
Require Import CAG.Category.Functor.
Require Import CAG.Category.Limits.
Require Import CAG.Category.PreservesLimits.
Require Import CAG.Category.Comma.
From Stdlib Require Import Logic.ProofIrrelevance.

Set Universe Polymorphism.
Open Scope cat_scope.

(* ------------------------------------------------------------------ *)
(** ** Lemma 2.11.14                                                    *)
(*                                                                      *)
(*   Suppose G : S -> C,  S has limits of shape I,                      *)
(*   and G preserves limits of shape I.                                 *)
(*   Then (A ↓ G) has limits of shape I,                                *)
(*   and the forgetful functor U : (A ↓ G) -> S preserves them.         *)
(*                                                                      *)
(*   Proof sketch:                                                       *)
(*   Given D : I -> (A ↓ G), the underlying diagram UD : I -> S         *)
(*   has a limit L in S.  Since G preserves the limit,                  *)
(*   G(lim UD) with maps G(L.cone_map i) is a limit of G∘UD in C.       *)
(*   The object data of D gives cone maps h_i : A -> G(D_i(ob)).        *)
(*   These form a cone over G∘UD with vertex A.                         *)
(*   The universal property of G(lim UD) gives unique k : A -> G(lim L).*)
(*   This makes (lim UD, k) an object of (A ↓ G),                       *)
(*   and the limit cone in (A ↓ G) has that vertex.                     *)
(* ------------------------------------------------------------------ *)

Theorem under_category_limits {C S : Category}
    (A : C.(Ob)) (G : Functor S C)
    (I : Category)
    (hlim : HasLimitsOfShape I S)
    (hpres : PreservesLimitsOfShape I G) :
    HasLimitsOfShape I (A ↓ G).
Proof.
  intros D.
  (* Underlying S-diagram *)
  set (UD := FunctorComp (UnderForget A G) D).
  (* Limit of UD in S *)
  destruct (hlim UD) as [Lcone HL].
  (* G preserves this limit *)
  set (HGL := hpres UD Lcone HL).
  (* Cone over G∘UD with vertex A; cone_map i = D(i).under_map *)
  (* Note: outside Section UnderCategory, record projections like under_map
     need explicit A G arguments via @projection _ _ A G.               *)
  set (KA := Build_Cone I C (FunctorComp G UD)
    A
    (fun i => @under_map _ _ A G (D ## i))
    (fun i j u => @under_comm _ _ A G _ _ (D #> u))).
  (* Universal morphism k : A -> G(lim UD) *)
  set (k := HGL.(lim_med) KA).
  (* Limit vertex in A↓G *)
  set (lim_vert := {| under_ob := Lcone.(cone_vertex);
                      under_map := k |} : UnderOb A G).
  (* Helper: extract an S-cone from an A↓G-cone *)
  set (extract := fun (K : Cone D) =>
    Build_Cone I S UD
      (@under_ob _ _ A G K.(cone_vertex))
      (fun i => @under_hom _ _ A G _ _ (K.(cone_map) i))
      (fun i j u => f_equal (@under_hom _ _ A G _ _) (K.(cone_comm) u))).
  (* Build the under_comm proof for lim_med (opaque, just a proof) *)
  assert (mk_med_comm : forall K : Cone D,
      G #> (HL.(lim_med) (extract K)) ∘ under_map A G (cone_vertex K) = HGL.(lim_med) KA).
  { intro K.
    apply (HGL.(lim_med_uniq) KA). intro i.
    change (cone_map (cone_fmap G Lcone) i) with (G #> (cone_map Lcone i)).
    transitivity (G #> (cone_map Lcone i ∘ HL.(lim_med) (extract K)) ∘
                  under_map A G (cone_vertex K)).
    { rewrite C.(comp_assoc). f_equal.
      exact (eq_sym (G.(fmap_comp) (cone_map Lcone i) (HL.(lim_med) (extract K)))). }
    { rewrite (HL.(lim_med_comm) (extract K) i). cbn.
      exact (@under_comm _ _ A G _ _ (K.(cone_map) i)). } }
  (* mk_med is transparent (pose) so cbn can reduce under_hom (mk_med K) *)
  pose (mk_med := fun K : Cone D =>
    @Build_UnderHom C S A G (cone_vertex K) lim_vert
      (HL.(lim_med) (extract K)) (mk_med_comm K)).
  (* Build cone_comm and commit the cone *)
  assert (lim_cone_comm : forall (i j : I.(Ob)) (u : I⟦i,j⟧),
    (D #> u) ∘ @Build_UnderHom C S A G lim_vert (D ## i) (cone_map Lcone i) (HGL.(lim_med_comm) KA i) =
    @Build_UnderHom C S A G lim_vert (D ## j) (cone_map Lcone j) (HGL.(lim_med_comm) KA j)).
  { intros i j u. apply under_hom_eq. exact (Lcone.(cone_comm) u). }
  apply (existT (fun c : Cone D => IsLimit c)
    (@Build_Cone I (A ↓ G) D lim_vert
      (fun i => @Build_UnderHom C S A G lim_vert (D ## i)
                  (cone_map Lcone i) (HGL.(lim_med_comm) KA i))
      lim_cone_comm)).
  (* IsLimit; use econstructor so K gets type Cone D (not Cone ?D) *)
  unshelve econstructor.
  - (* lim_med *)
    exact mk_med.
  - (* lim_med_comm *)
    intros K i. apply under_hom_eq. cbn.
    exact (HL.(lim_med_comm) (extract K) i).
  - (* lim_med_uniq *)
    intros K v Hv. apply under_hom_eq. cbn.
    apply (HL.(lim_med_uniq) (extract K)).
    intro i. exact (f_equal (@under_hom _ _ A G _ _) (Hv i)).
Qed.

Theorem under_forget_preserves_limits {C S : Category}
    (A : C.(Ob)) (G : Functor S C)
    (I : Category)
    (hlim : HasLimitsOfShape I S)
    (hpres : PreservesLimitsOfShape I G) :
    PreservesLimitsOfShape I (UnderForget A G).
Proof.
  intros D Lcone HL.
  set (UD := FunctorComp (UnderForget A G) D).
  destruct (hlim UD) as [Slimit SHL].
  set (HGL := hpres UD Slimit SHL).
  set (KA := Build_Cone I C (FunctorComp G UD) A
    (fun i => @under_map _ _ A G (D ## i))
    (fun i j u => @under_comm _ _ A G _ _ (D #> u))).
  set (k := HGL.(lim_med) KA).
  set (slimit_vert := {| under_ob := Slimit.(cone_vertex); under_map := k |} : UnderOb A G).
  assert (slift_comm : forall (i j : I.(Ob)) (u : I⟦i, j⟧),
    (D #> u) ∘ @Build_UnderHom C S A G slimit_vert (D ## i)
        (Slimit.(cone_map) i) (HGL.(lim_med_comm) KA i) =
    @Build_UnderHom C S A G slimit_vert (D ## j)
        (Slimit.(cone_map) j) (HGL.(lim_med_comm) KA j)).
  { intros i j u. apply under_hom_eq. exact (Slimit.(cone_comm) u). }
  set (Lcone_lift := @Build_Cone I (A ↓ G) D slimit_vert
    (fun i => @Build_UnderHom C S A G slimit_vert (D ## i)
                (Slimit.(cone_map) i) (HGL.(lim_med_comm) KA i))
    slift_comm).
  set (φ := HL.(lim_med) Lcone_lift).
  set (ψ := SHL.(lim_med) (cone_fmap (UnderForget A G) Lcone)).
  (* under_hom φ ∘ ψ = id *)
  assert (φψ_id : @under_hom _ _ A G _ _ φ ∘ ψ = S.(id) _).
  { assert (ψ_comm : G #> ψ ∘ @under_map _ _ A G (cone_vertex Lcone) = k).
    { unfold k. apply (HGL.(lim_med_uniq) KA). intro i.
      change (cone_map (cone_fmap G Slimit) i) with (G #> (cone_map Slimit i)).
      assert (Hcomm : cone_map Slimit i ∘ ψ =
                      @under_hom _ _ A G _ _ (Lcone.(cone_map) i)).
      { exact (SHL.(lim_med_comm) (cone_fmap (UnderForget A G) Lcone) i). }
      rewrite C.(comp_assoc).
      transitivity (G #> (cone_map Slimit i ∘ ψ) ∘ @under_map _ _ A G (cone_vertex Lcone)).
      { f_equal. exact (eq_sym (G.(fmap_comp) (cone_map Slimit i) ψ)). }
      rewrite Hcomm.
      exact (@under_comm _ _ A G _ _ (Lcone.(cone_map) i)). }
    pose (lift_ψ := @Build_UnderHom C S A G (cone_vertex Lcone) slimit_vert ψ ψ_comm).
    assert (φ_lψ_comm : forall i,
        Lcone.(cone_map) i ∘ (φ ∘ lift_ψ) = Lcone.(cone_map) i).
    { intro i.
      assert (Hc : Lcone.(cone_map) i ∘ φ = Lcone_lift.(cone_map) i).
      { exact (HL.(lim_med_comm) Lcone_lift i). }
      transitivity (Lcone_lift.(cone_map) i ∘ lift_ψ).
      { transitivity ((Lcone.(cone_map) i ∘ φ) ∘ lift_ψ).
        { exact ((A ↓ G).(comp_assoc) _ _ _). }
        rewrite Hc. reflexivity. }
      { apply under_hom_eq. cbn.
        exact (SHL.(lim_med_comm) (cone_fmap (UnderForget A G) Lcone) i). } }
    assert (id_comm : forall i,
        Lcone.(cone_map) i ∘ (A ↓ G).(id) (cone_vertex Lcone) = Lcone.(cone_map) i).
    { intro i. apply (A ↓ G).(id_right). }
    assert (Heq : φ ∘ lift_ψ = (A ↓ G).(id) (cone_vertex Lcone)).
    { apply eq_trans with (HL.(lim_med) Lcone).
      - apply HL.(lim_med_uniq). exact φ_lψ_comm.
      - exact (eq_sym (HL.(lim_med_uniq) Lcone ((A ↓ G).(id) _) id_comm)). }
    assert (H := f_equal (@under_hom _ _ A G _ _) Heq). cbn in H. exact H. }
  unshelve econstructor.
  - exact (fun K => @under_hom _ _ A G _ _ φ ∘ SHL.(lim_med) K).
  - (* lim_med_comm *)
    intros K i.
    change (cone_map (cone_fmap (UnderForget A G) Lcone) i) with
      (@under_hom _ _ A G _ _ (Lcone.(cone_map) i)).
    assert (Hφcomm : @under_hom _ _ A G _ _ (Lcone.(cone_map) i) ∘
                     @under_hom _ _ A G _ _ φ = Slimit.(cone_map) i).
    { assert (H := f_equal (@under_hom _ _ A G _ _) (HL.(lim_med_comm) Lcone_lift i)).
      cbn in H. exact H. }
    transitivity ((@under_hom _ _ A G _ _ (Lcone.(cone_map) i) ∘ @under_hom _ _ A G _ _ φ) ∘ SHL.(lim_med) K).
    { exact (S.(comp_assoc) _ _ _). }
    rewrite Hφcomm. exact (SHL.(lim_med_comm) K i).
  - (* lim_med_uniq *)
    intros K v Hv. cbn.
    assert (ψv : ψ ∘ v = SHL.(lim_med) K).
    { apply SHL.(lim_med_uniq). intro i.
      assert (Hψcomm : Slimit.(cone_map) i ∘ ψ =
                       @under_hom _ _ A G _ _ (Lcone.(cone_map) i)).
      { exact (SHL.(lim_med_comm) (cone_fmap (UnderForget A G) Lcone) i). }
      transitivity ((Slimit.(cone_map) i ∘ ψ) ∘ v).
      { exact (S.(comp_assoc) _ _ _). }
      rewrite Hψcomm. exact (Hv i). }
    symmetry.
    exact (eq_trans
      (f_equal (fun x => @under_hom _ _ A G _ _ φ ∘ x) (eq_sym ψv))
      (eq_trans (S.(comp_assoc) _ _ _)
        (eq_trans (f_equal (fun x => x ∘ v) φψ_id)
          (S.(id_left) v)))).
Qed.
