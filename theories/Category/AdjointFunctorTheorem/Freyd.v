(** * Category/AdjointFunctorTheorem/Freyd.v
    Freyd's adjoint functor theorem (Theorem 2.11.16):
    G has a left adjoint iff it preserves all small limits and satisfies
    the solution set condition. *)

Require Import CAG.Category.Core.
Require Import CAG.Category.Functor.
Require Import CAG.Category.Limits.
Require Import CAG.Category.Adjunction.
Require Import CAG.Category.PreservesLimits.
Require Import CAG.Category.Comma.
Require Import CAG.Category.UnderLimits.
Require Import CAG.Category.InitialObjectCriteria.
Require Import CAG.Category.AdjunctionLimits.

Set Universe Polymorphism.
Open Scope cat_scope.

(* ------------------------------------------------------------------ *)
(** ** Solution set condition                                           *)
(*                                                                      *)
(*   G : S -> C satisfies the solution set condition at A ∈ C if        *)
(*   there is a set {f_x : A -> G B_x} such that every g : A -> G C     *)
(*   factors as  g = G(h_x) ∘ f_x  for some x and some h_x : B_x -> C. *)
(* ------------------------------------------------------------------ *)

Record SolutionSet {C S : Category} (G : Functor S C) (A : C.(Ob)) : Type := {
  ss_index  : Type;
  ss_obj    : ss_index -> S.(Ob);
  ss_map    : forall x : ss_index, C⟦A, G ## (ss_obj x)⟧;
  ss_factor : forall (B : S.(Ob)) (g : C⟦A, G ## B⟧),
    exists (x : ss_index) (h : S⟦ss_obj x, B⟧),
      g = G #> h ∘ ss_map x;
}.

Arguments ss_index  {C S G A} s.
Arguments ss_obj    {C S G A} s x.
Arguments ss_map    {C S G A} s x.
Arguments ss_factor {C S G A} s B g.

(** G satisfies the solution set condition globally. *)
Definition HasSolutionSet {C S : Category} (G : Functor S C) : Type :=
  forall A : C.(Ob), SolutionSet G A.

(* ------------------------------------------------------------------ *)
(** ** Freyd's adjoint functor theorem                                  *)
(*                                                                      *)
(*   Theorem 2.11.16: Let G : S -> C where S is locally small           *)
(*   and complete. Then G has a left adjoint iff:                        *)
(*   (1) G preserves all small limits, and                              *)
(*   (2) G satisfies the solution set condition.                         *)
(*                                                                      *)
(*   Proof of (1)+(2) => left adjoint:                                  *)
(*   For each A, by (2) the under-category (A ↓ G) has a covering       *)
(*   family (the solution set).                                          *)
(*   By UnderLimits.under_category_limits (using completeness of S       *)
(*   and preservation by G), (A ↓ G) is complete.                       *)
(*   By InitialObjectCriteria.covering_family_gives_initial,             *)
(*   (A ↓ G) has an initial object — the unit η_A : A -> G(F A).        *)
(*   Varying over A gives the adjunction.                                *)
(* ------------------------------------------------------------------ *)

(** Forward direction: left adjoint exists => G preserves limits. *)
Theorem freyd_forward {C S : Category}
    {F : Functor C S} {G : Functor S C} (adj : F ⊣ G)
    (I : Category) :
    PreservesLimitsOfShape I G.
Proof.
  exact (right_adjoint_preserves_limits adj I).
Qed.

(** Forward direction: left adjoint exists => solution set condition. *)
Theorem freyd_solution_set {C S : Category}
    {F : Functor C S} {G : Functor S C} (adj : F ⊣ G) :
    HasSolutionSet G.
Proof.
  (* For each A, the singleton {η_A : A -> G(FA)} is a solution set:
     every g : A -> G(B) factors as G(adj_lr adj g) ∘ η_A by the
     co-transpose calculation. *)
  intros A.
  apply (Build_SolutionSet _ _ _ _ unit (fun _ => F ## A) (fun _ => adj.(adj_unit).(component) A)).
  intros B g.
  exists tt. exists (adj_lr adj g).
  symmetry. apply adj_rl_lr.
Qed.

(** Main backward direction: preservation + solution set => left adjoint. *)
Theorem freyd_adjoint_functor_theorem {C S : Category}
    (G : Functor S C)
    (hcomp : Complete S)
    (hpres : forall I, PreservesLimitsOfShape I G)
    (hss   : HasSolutionSet G) :
    { F : Functor C S & F ⊣ G }.
Proof.
  Admitted.
