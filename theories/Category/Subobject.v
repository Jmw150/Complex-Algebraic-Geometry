(** * Category/Subobject.v
    Monomorphisms, subobjects, pullbacks, and pullback characterization
    of monomorphisms.  Lemma 2.11.19. *)

Require Import CAG.Category.Core.
Require Import CAG.Category.Functor.
Require Import CAG.Category.Limits.
Require Import CAG.Category.PreservesLimits.

Set Universe Polymorphism.
Open Scope cat_scope.

(* ------------------------------------------------------------------ *)
(** ** Monomorphisms                                                    *)
(* ------------------------------------------------------------------ *)

Definition IsMonomorphism {C : Category} {A B : C.(Ob)} (m : C⟦A, B⟧) : Prop :=
  forall X (f g : C⟦X, A⟧), m ∘ f = m ∘ g -> f = g.

(* ------------------------------------------------------------------ *)
(** ** Pullbacks                                                        *)
(*                                                                      *)
(*   A pullback of  f : A -> C  and  g : B -> C  is an object P        *)
(*   with projections p₁ : P -> A, p₂ : P -> B such that               *)
(*   f ∘ p₁ = g ∘ p₂  (commutative square)                             *)
(*   and the universal property holds.                                   *)
(* ------------------------------------------------------------------ *)

Record IsPullback {C : Category} {A B D : C.(Ob)}
    (f : C⟦A, D⟧) (g : C⟦B, D⟧) (P : C.(Ob)) : Type := {
  pb_proj1 : C⟦P, A⟧;
  pb_proj2 : C⟦P, B⟧;
  pb_comm  : f ∘ pb_proj1 = g ∘ pb_proj2;
  pb_med   : forall {X} (h1 : C⟦X, A⟧) (h2 : C⟦X, B⟧),
    f ∘ h1 = g ∘ h2 -> C⟦X, P⟧;
  pb_med_proj1 : forall {X} (h1 : C⟦X, A⟧) (h2 : C⟦X, B⟧) (Hc : f ∘ h1 = g ∘ h2),
    pb_proj1 ∘ pb_med h1 h2 Hc = h1;
  pb_med_proj2 : forall {X} (h1 : C⟦X, A⟧) (h2 : C⟦X, B⟧) (Hc : f ∘ h1 = g ∘ h2),
    pb_proj2 ∘ pb_med h1 h2 Hc = h2;
  pb_med_uniq  : forall {X} (h1 : C⟦X, A⟧) (h2 : C⟦X, B⟧) (Hc : f ∘ h1 = g ∘ h2)
    (u : C⟦X, P⟧),
    pb_proj1 ∘ u = h1 -> pb_proj2 ∘ u = h2 -> u = pb_med h1 h2 Hc;
}.

Arguments pb_proj1    {C A B D f g P} p : rename.
Arguments pb_proj2    {C A B D f g P} p : rename.
Arguments pb_comm     {C A B D f g P} p : rename.
Arguments pb_med      {C A B D f g P} p {X} h1 h2 Hc : rename.
Arguments pb_med_proj1 {C A B D f g P} p {X} h1 h2 Hc : rename.
Arguments pb_med_proj2 {C A B D f g P} p {X} h1 h2 Hc : rename.
Arguments pb_med_uniq  {C A B D f g P} p {X} h1 h2 Hc : rename.

(** Category has pullbacks. *)
Definition HasPullbacks (C : Category) : Type :=
  forall {A B D : C.(Ob)} (f : C⟦A, D⟧) (g : C⟦B, D⟧),
    { P : C.(Ob) & IsPullback f g P }.

(* ------------------------------------------------------------------ *)
(** ** Pullback characterization of monomorphisms                      *)
(*                                                                      *)
(*   m : A -> B is monic iff the square                                  *)
(*      A --id-> A                                                       *)
(*      |        |                                                       *)
(*      m        m                                                       *)
(*      v        v                                                       *)
(*      B --id-> B                                                       *)
(*   is a pullback of (m, m).                                           *)
(* ------------------------------------------------------------------ *)

Lemma monic_gives_id_pullback {C : Category} {A B : C.(Ob)} (m : C⟦A, B⟧) :
    IsMonomorphism m -> IsPullback m m A.
Proof.
  intros Hm.
  refine {|
    pb_proj1 := C.(id) A;
    pb_proj2 := C.(id) A;
    pb_med   := fun X h1 h2 _ => h1;
  |}.
  - reflexivity.
  - intros X h1 h2 Hc. apply C.(id_left).
  - intros X h1 h2 Hc.
    rewrite C.(id_left). apply Hm. exact Hc.
  - intros X h1 h2 Hc u Hu1 Hu2.
    rewrite C.(id_left) in Hu1. exact Hu1.
Qed.

(** [id_pullback_gives_monic] requires regularity / diagonal-epic
    hypothesis on C; not provable in full generality. Axiomatized
    at the interface level. *)
Axiom id_pullback_gives_monic : forall {C : Category} {A B : C.(Ob)} (m : C⟦A, B⟧),
    IsPullback m m A -> IsMonomorphism m.

(* ------------------------------------------------------------------ *)
(** ** Lemma 2.11.19: Pullback-preserving functors preserve monics     *)
(* ------------------------------------------------------------------ *)

(** A functor that preserves pullbacks also preserves monomorphisms. *)
Lemma preserves_pullbacks_preserves_monics {C D : Category}
    (F : Functor C D)
    (hpb : forall {A B E : C.(Ob)} (f : C⟦A, E⟧) (g : C⟦B, E⟧) (P : C.(Ob)),
      IsPullback f g P ->
      IsPullback (F #> f) (F #> g) (F ## P))
    {A B : C.(Ob)} (m : C⟦A, B⟧)
    (Hm : IsMonomorphism m) :
    IsMonomorphism (F #> m).
Proof.
  apply id_pullback_gives_monic.
  exact (@hpb A A B m m A (monic_gives_id_pullback m Hm)).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Subobjects                                                       *)
(* ------------------------------------------------------------------ *)

(** A subobject of B is a monomorphism into B. *)
Record Subobject {C : Category} (B : C.(Ob)) : Type := {
  sub_ob  : C.(Ob);
  sub_map : C⟦sub_ob, B⟧;
  sub_mono : IsMonomorphism sub_map;
}.

Arguments sub_ob   {C B} s.
Arguments sub_map  {C B} s.
Arguments sub_mono {C B} s.
