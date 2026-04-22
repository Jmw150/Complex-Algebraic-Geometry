(** * Category/AdjunctionLimits.v
    Right adjoints preserve limits; left adjoints preserve colimits.
    Theorem 2.11.13. *)

Require Import CAG.Category.Core.
Require Import CAG.Category.Functor.
Require Import CAG.Category.Limits.
Require Import CAG.Category.Adjunction.
Require Import CAG.Category.PreservesLimits.

Set Universe Polymorphism.
Open Scope cat_scope.

(* ------------------------------------------------------------------ *)
(** ** Helper: transpose a cone over G∘Dg to a cone over Dg            *)
(*                                                                      *)
(*   Given adj : F ⊣ G and a cone K over G∘Dg in C,                    *)
(*   produce a cone over Dg in D by transposing each component          *)
(*   K.cone_map i : W -> G(Dg i)  to  F W -> Dg i  via adj_lr.         *)
(* ------------------------------------------------------------------ *)

Definition cone_adj_lr {C D : Category}
    {F : Functor C D} {G : Functor D C} (adj : F ⊣ G)
    {I : Category} {Dg : Functor I D}
    (K : Cone (FunctorComp G Dg)) : Cone Dg.
Proof.
  refine {|
    cone_vertex := F ## K.(cone_vertex);
    cone_map    := fun i => adj_lr adj (K.(cone_map) i);
  |}.
  intros i j u.
  unfold adj_lr. cbn.
  (* Goal: Dg#>u ∘ (ε_{Dg i} ∘ F(K.cone_map i)) = ε_{Dg j} ∘ F(K.cone_map j) *)
  rewrite D.(comp_assoc).
  (* (Dg#>u ∘ ε_{Dg i}) ∘ F(K.cone_map i) = ε_{Dg j} ∘ F(K.cone_map j) *)
  assert (Hnat := (adj.(adj_counit)).(naturality) (Dg #> u)).
  cbn in Hnat.
  (* Hnat: Dg#>u ∘ ε_{Dg i} = ε_{Dg j} ∘ F(G(Dg#>u)) *)
  rewrite Hnat.
  rewrite <- D.(comp_assoc).
  rewrite <- F.(fmap_comp).
  (* K.cone_comm for FunctorComp G Dg: G(Dg#>u) ∘ K.cone_map i = K.cone_map j *)
  assert (Hcc := K.(cone_comm) u). cbn in Hcc.
  rewrite Hcc.
  reflexivity.
Defined.

(* ------------------------------------------------------------------ *)
(** ** Theorem 2.11.13: Right adjoints preserve limits                  *)
(*                                                                      *)
(*   If F ⊣ G  then G preserves all limits that exist in D.            *)
(*                                                                      *)
(*   Proof sketch:                                                       *)
(*   Given limit cone L over Dg : I -> D,                               *)
(*   and a cone K over G∘Dg with vertex W in C,                         *)
(*   transpose K to a cone (cone_adj_lr adj K) over Dg in D,            *)
(*   apply the universal property of L to get ū : F W -> lim Dg,        *)
(*   transpose back to u : W -> G(lim Dg).                              *)
(* ------------------------------------------------------------------ *)

Theorem right_adjoint_preserves_limits {C D : Category}
    {F : Functor C D} {G : Functor D C} (adj : F ⊣ G)
    (I : Category) : PreservesLimitsOfShape I G.
Proof.
  intros Dg L HL.
  refine (@Build_IsLimit I C (FunctorComp G Dg) (cone_fmap G L)
    (fun K => adj_rl adj (HL.(lim_med) (cone_adj_lr adj K)))
    _ _).
  - (* (cone_fmap G L).cone_map i ∘ (adj_rl adj ū) = K.cone_map i  *)
    intros K i.
    (* Split at the lim_med_comm step before any cbn expands cone_adj_lr adj K *)
    set (K' := cone_adj_lr adj K).
    transitivity (G #> (K'.(cone_map) i) ∘ adj.(adj_unit).(component) K.(cone_vertex)).
    + (* Use lim_med_comm without expanding cone_adj_lr adj K *)
      change (G #> (L.(cone_map) i) ∘
              (G #> (HL.(lim_med) K') ∘ adj.(adj_unit).(component) K.(cone_vertex))
              = G #> (K'.(cone_map) i) ∘ adj.(adj_unit).(component) K.(cone_vertex)).
      rewrite C.(comp_assoc), <- G.(fmap_comp).
      rewrite (HL.(lim_med_comm) K' i).
      reflexivity.
    + (* G #> K'.cm i ∘ η_W = K.cm i  where K' = cone_adj_lr adj K *)
      subst K'. unfold cone_adj_lr, adj_lr. cbn.
      rewrite G.(fmap_comp), <- C.(comp_assoc).
      assert (Hnat := adj.(adj_unit).(naturality) (K.(cone_map) i)).
      (* note: K.cone_map i is a morphism in C, applied correctly *)
      cbn in Hnat. rewrite Hnat.
      rewrite C.(comp_assoc).
      assert (Htri := adj.(adj_triangle_right) (Dg ## i)).
      cbn in Htri. rewrite Htri.
      apply C.(id_left).
  - (* v = adj_rl adj ū  iff  adj_lr adj v = ū  (by bijection) *)
    intros K v Hv.
    (* cone_vertex (cone_fmap G L) = G ## L.cv definitionally *)
    change (C⟦K.(cone_vertex), G ## L.(cone_vertex)⟧) in v.
    etransitivity.
    + symmetry. exact (adj_rl_lr adj v).
    + apply (f_equal (adj_rl adj)).
      apply (HL.(lim_med_uniq) (cone_adj_lr adj K) (adj_lr adj v)).
      intros i.
      unfold adj_lr. cbn.
      rewrite D.(comp_assoc).
      assert (Hnat_ε := adj.(adj_counit).(naturality) (L.(cone_map) i)).
      cbn in Hnat_ε. rewrite Hnat_ε.
      rewrite <- D.(comp_assoc), <- F.(fmap_comp).
      specialize (Hv i). unfold cone_fmap in Hv. cbn in Hv.
      rewrite Hv.
      unfold cone_adj_lr, adj_lr. cbn. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Helper: transpose a cocone over F∘Dg to a cocone over Dg        *)
(*                                                                      *)
(*   Given adj : F ⊣ G and a cocone K over F∘Dg in D,                  *)
(*   produce a cocone over Dg in C by transposing each component        *)
(*   K.cocone_map i : F(Dg i) -> W  to  Dg i -> G W  via adj_rl.      *)
(* ------------------------------------------------------------------ *)

Definition cocone_adj_rl {C D : Category}
    {F : Functor C D} {G : Functor D C} (adj : F ⊣ G)
    {I : Category} {Dg : Functor I C}
    (K : Cocone (FunctorComp F Dg)) : Cocone Dg.
Proof.
  refine {|
    cocone_vertex := G ## K.(cocone_vertex);
    cocone_map    := fun i => adj_rl adj (K.(cocone_map) i);
  |}.
  intros i j u.
  unfold adj_rl. cbn.
  (* Goal: (G #> K.cm j ∘ η_{Dg j}) ∘ Dg#>u = G #> K.cm i ∘ η_{Dg i} *)
  rewrite <- C.(comp_assoc).
  assert (Hnat := (adj.(adj_unit)).(naturality) (Dg #> u)).
  cbn in Hnat.
  (* Hnat: G(F(Dg#>u)) ∘ η_{Dg i} = η_{Dg j} ∘ Dg#>u *)
  rewrite <- Hnat.
  rewrite C.(comp_assoc).
  rewrite <- G.(fmap_comp).
  assert (Hcc := K.(cocone_comm) u). cbn in Hcc.
  rewrite Hcc.
  reflexivity.
Defined.

(* ------------------------------------------------------------------ *)
(** ** Corollary: Left adjoints preserve colimits                       *)
(* ------------------------------------------------------------------ *)

Theorem left_adjoint_preserves_colimits {C D : Category}
    {F : Functor C D} {G : Functor D C} (adj : F ⊣ G)
    (I : Category) : PreservesColimitsOfShape I F.
Proof.
  intros Dg L HL.
  refine (@Build_IsColimit I D (FunctorComp F Dg) (cocone_fmap F L)
    (fun K => adj_lr adj (HL.(colim_med) (cocone_adj_rl adj K)))
    _ _).
  - (* colim_med_comm: adj_lr adj (...) ∘ F(L.cm i) = K.cm i *)
    intros K i.
    set (K' := cocone_adj_rl adj K).
    transitivity (adj.(adj_counit).(component) K.(cocone_vertex) ∘ F #> (K'.(cocone_map) i)).
    + change (adj_lr adj (HL.(colim_med) K') ∘ F #> (L.(cocone_map) i)
              = adj.(adj_counit).(component) K.(cocone_vertex) ∘ F #> (K'.(cocone_map) i)).
      unfold adj_lr. cbn.
      transitivity (adj.(adj_counit).(component) K.(cocone_vertex) ∘
                    F #> (HL.(colim_med) K' ∘ L.(cocone_map) i)).
      { rewrite <- D.(comp_assoc). f_equal.
        exact (eq_sym (F.(fmap_comp) (HL.(colim_med) K') (L.(cocone_map) i))). }
      { f_equal. f_equal. exact (HL.(colim_med_comm) K' i). }
    + subst K'. unfold cocone_adj_rl, adj_rl. cbn.
      rewrite F.(fmap_comp), D.(comp_assoc).
      assert (Hnat := adj.(adj_counit).(naturality) (K.(cocone_map) i)).
      cbn in Hnat. rewrite <- Hnat.
      rewrite <- D.(comp_assoc).
      assert (Htri := adj.(adj_triangle_left) (Dg ## i)).
      cbn in Htri. rewrite Htri.
      apply D.(id_right).
  - (* colim_med_uniq *)
    intros K u Hu.
    change (D⟦F ## L.(cocone_vertex), K.(cocone_vertex)⟧) in u.
    etransitivity.
    + symmetry. exact (adj_lr_rl adj u).
    + apply (f_equal (adj_lr adj)).
      apply (HL.(colim_med_uniq) (cocone_adj_rl adj K) (adj_rl adj u)).
      intros i.
      unfold adj_rl. cbn.
      rewrite <- C.(comp_assoc).
      assert (Hnat_η := adj.(adj_unit).(naturality) (L.(cocone_map) i)).
      cbn in Hnat_η. rewrite <- Hnat_η.
      rewrite C.(comp_assoc).
      rewrite <- G.(fmap_comp).
      specialize (Hu i). unfold cocone_fmap in Hu. cbn in Hu.
      rewrite Hu.
      unfold cocone_adj_rl, adj_rl. cbn. reflexivity.
Qed.
