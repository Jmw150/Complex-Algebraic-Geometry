(** * Category/InitialObjectCriteria.v
    Lemma 2.11.15: a locally-small complete category has an initial object
    iff there is a small family of objects covering all morphisms out. *)

Require Import CAG.Category.Core.
Require Import CAG.Category.Functor.
Require Import CAG.Category.Limits.

Set Universe Polymorphism.
Open Scope cat_scope.

(* ------------------------------------------------------------------ *)
(** ** Covering family                                                  *)
(*                                                                      *)
(*   A family {A_x | x : X} covers outgoing morphisms if for every     *)
(*   object B there is some x and some morphism A_x -> B.               *)
(* ------------------------------------------------------------------ *)

Definition CoveringFamily {C : Category} {X : Type}
    (family : X -> C.(Ob)) : Type :=
  forall B : C.(Ob), { x : X & C⟦family x, B⟧ }.

(* ------------------------------------------------------------------ *)
(** ** Lemma 2.11.15                                                    *)
(*                                                                      *)
(*   If C is locally small and complete, then C has an initial object   *)
(*   iff it has a small covering family.                                 *)
(*                                                                      *)
(*   Forward: if 0 is initial, the singleton family {0} covers          *)
(*            (init_arr 0 B : 0 -> B for every B).                      *)
(*                                                                      *)
(*   Backward: form P = Π_x A_x, take the limit of the endomorphism     *)
(*             diagram on P, conclude that limit is initial.            *)
(* ------------------------------------------------------------------ *)

(** Forward direction: initial object yields a singleton covering family. *)
Lemma initial_gives_covering_family {C : Category} {I : C.(Ob)}
    (hI : IsInitial I) :
    CoveringFamily (fun _ : unit => I).
Proof.
  intros B. exact (existT _ tt (init_arr I hI B)).
Qed.

(** Backward direction: covering family + completeness => initial object.
    Axiomatized — proof requires constructing the limit of an
    endomorphism diagram on the product of the family. *)
Axiom covering_family_gives_initial : forall {C : Category}
    {X : Type} {family : X -> C.(Ob)}
    (hfam  : CoveringFamily family)
    (hcomp : Complete C),
    { I : C.(Ob) & IsInitial I }.
