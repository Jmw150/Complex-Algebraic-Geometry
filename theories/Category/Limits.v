(** * Category/Limits.v
    Cones, cocones, limits, colimits, completeness, uniqueness,
    and application of functors to cones. *)

Require Import CAG.Category.Core.
Require Import CAG.Category.Functor.

Set Universe Polymorphism.
Open Scope cat_scope.

(* ------------------------------------------------------------------ *)
(** ** Cones                                                            *)
(* ------------------------------------------------------------------ *)

Record Cone {I C : Category} (D : Functor I C) : Type := {
  cone_vertex : C.(Ob);
  cone_map    : forall i : I.(Ob), C⟦cone_vertex, D ## i⟧;
  cone_comm   : forall {i j : I.(Ob)} (u : I⟦i, j⟧),
    D #> u ∘ cone_map i = cone_map j;
}.

Arguments cone_vertex {I C D} c.
Arguments cone_map    {I C D} c i.
Arguments cone_comm   {I C D} c {i j} u.

(* ------------------------------------------------------------------ *)
(** ** Cocones                                                          *)
(* ------------------------------------------------------------------ *)

Record Cocone {I C : Category} (D : Functor I C) : Type := {
  cocone_vertex : C.(Ob);
  cocone_map    : forall i : I.(Ob), C⟦D ## i, cocone_vertex⟧;
  cocone_comm   : forall {i j : I.(Ob)} (u : I⟦i, j⟧),
    cocone_map j ∘ D #> u = cocone_map i;
}.

Arguments cocone_vertex {I C D} c.
Arguments cocone_map    {I C D} c i.
Arguments cocone_comm   {I C D} c {i j} u.

(* ------------------------------------------------------------------ *)
(** ** Limits                                                           *)
(* ------------------------------------------------------------------ *)

Record IsLimit {I C : Category} {D : Functor I C} (L : Cone D) : Type := {
  lim_med      : forall (K : Cone D), C⟦K.(cone_vertex), L.(cone_vertex)⟧;
  lim_med_comm : forall (K : Cone D) (i : I.(Ob)),
    L.(cone_map) i ∘ lim_med K = K.(cone_map) i;
  lim_med_uniq : forall (K : Cone D) (u : C⟦K.(cone_vertex), L.(cone_vertex)⟧),
    (forall i : I.(Ob), L.(cone_map) i ∘ u = K.(cone_map) i) ->
    u = lim_med K;
}.

Arguments lim_med      {I C D L} h K : rename.
Arguments lim_med_comm {I C D L} h K i : rename.
Arguments lim_med_uniq {I C D L} h K u : rename.

(* ------------------------------------------------------------------ *)
(** ** Colimits                                                         *)
(* ------------------------------------------------------------------ *)

Record IsColimit {I C : Category} {D : Functor I C} (L : Cocone D) : Type := {
  colim_med      : forall (K : Cocone D), C⟦L.(cocone_vertex), K.(cocone_vertex)⟧;
  colim_med_comm : forall (K : Cocone D) (i : I.(Ob)),
    colim_med K ∘ L.(cocone_map) i = K.(cocone_map) i;
  colim_med_uniq : forall (K : Cocone D) (u : C⟦L.(cocone_vertex), K.(cocone_vertex)⟧),
    (forall i : I.(Ob), u ∘ L.(cocone_map) i = K.(cocone_map) i) ->
    u = colim_med K;
}.

Arguments colim_med      {I C D L} h K : rename.
Arguments colim_med_comm {I C D L} h K i : rename.
Arguments colim_med_uniq {I C D L} h K u : rename.

(* ------------------------------------------------------------------ *)
(** ** Uniqueness of limits and colimits                                *)
(* ------------------------------------------------------------------ *)

Lemma limit_unique {I C : Category} {D : Functor I C}
    {L L' : Cone D} (HL : IsLimit L) (HL' : IsLimit L') :
    L.(cone_vertex) ≅[C] L'.(cone_vertex).
Proof.
  refine {|
    iso_fwd := lim_med HL' L;
    iso_bwd := lim_med HL  L';
  |}.
  - (* bwd ∘ fwd = id_{cone_vertex L} *)
    transitivity (lim_med HL L).
    + apply lim_med_uniq. intros i.
      rewrite C.(comp_assoc).
      rewrite lim_med_comm.
      apply lim_med_comm.
    + symmetry. apply lim_med_uniq. intro i. apply C.(id_right).
  - (* fwd ∘ bwd = id_{cone_vertex L'} *)
    transitivity (lim_med HL' L').
    + apply lim_med_uniq. intros i.
      rewrite C.(comp_assoc).
      rewrite lim_med_comm.
      apply lim_med_comm.
    + symmetry. apply lim_med_uniq. intro i. apply C.(id_right).
Qed.

Lemma colimit_unique {I C : Category} {D : Functor I C}
    {L L' : Cocone D} (HL : IsColimit L) (HL' : IsColimit L') :
    L.(cocone_vertex) ≅[C] L'.(cocone_vertex).
Proof.
  refine {|
    iso_fwd := colim_med HL  L';
    iso_bwd := colim_med HL' L;
  |}.
  - (* bwd ∘ fwd = id_{cocone_vertex L} *)
    transitivity (colim_med HL L).
    + apply colim_med_uniq. intro i.
      rewrite <- C.(comp_assoc).
      rewrite colim_med_comm.
      apply colim_med_comm.
    + symmetry. apply colim_med_uniq. intro i. apply C.(id_left).
  - (* fwd ∘ bwd = id_{cocone_vertex L'} *)
    transitivity (colim_med HL' L').
    + apply colim_med_uniq. intro i.
      rewrite <- C.(comp_assoc).
      rewrite colim_med_comm.
      apply colim_med_comm.
    + symmetry. apply colim_med_uniq. intro i. apply C.(id_left).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Category has limits / colimits of shape I                        *)
(* ------------------------------------------------------------------ *)

Definition HasLimitsOfShape (I C : Category) : Type :=
  forall (D : Functor I C), { L : Cone D & IsLimit L }.

Definition HasColimitsOfShape (I C : Category) : Type :=
  forall (D : Functor I C), { L : Cocone D & IsColimit L }.

(** A complete category has all small limits.  We parametrize over the
    index category rather than fixing a universe. *)
Definition Complete (C : Category) : Type :=
  forall (I : Category), HasLimitsOfShape I C.

Definition Cocomplete (C : Category) : Type :=
  forall (I : Category), HasColimitsOfShape I C.

(* ------------------------------------------------------------------ *)
(** ** Applying a functor to a cone / cocone                            *)
(* ------------------------------------------------------------------ *)

Definition cone_fmap {I C D : Category} (F : Functor C D)
    {Dg : Functor I C} (K : Cone Dg) : Cone (FunctorComp F Dg).
Proof.
  apply (Build_Cone I D (FunctorComp F Dg)
    (F ## K.(cone_vertex))
    (fun i => F #> (K.(cone_map) i))).
  intros i j u. cbn.
  rewrite <- F.(fmap_comp).
  rewrite K.(cone_comm).
  reflexivity.
Defined.

Definition cocone_fmap {I C D : Category} (F : Functor C D)
    {Dg : Functor I C} (K : Cocone Dg) : Cocone (FunctorComp F Dg).
Proof.
  apply (Build_Cocone I D (FunctorComp F Dg)
    (F ## K.(cocone_vertex))
    (fun i => F #> (K.(cocone_map) i))).
  intros i j u. cbn.
  rewrite <- F.(fmap_comp).
  rewrite K.(cocone_comm).
  reflexivity.
Defined.
