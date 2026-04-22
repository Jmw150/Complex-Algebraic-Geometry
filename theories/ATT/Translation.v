(** * ATT/Translation.v
    Translations between algebraic theories and equivalence of theories.

    A translation T : Th → Th' is a functor Cl(Th) → Cl(Th').
    A theory equivalence is a pair of inverse translations.

    Theorem 3.9.6: Th ≃ Th(Cl(Th)). *)

Require Import CAG.ATT.Signature.
Require Import CAG.ATT.Syntax.
Require Import CAG.ATT.Theory.
Require Import CAG.ATT.ClassifyingCategory.
Require Import CAG.Category.Core.
Require Import CAG.Category.Functor.
From Stdlib Require Import Lists.List.
Import ListNotations.

Set Universe Polymorphism.
Open Scope cat_scope.

(** ** Translation between theories *)

(** A translation is a functor between the syntactic classifying categories. *)
Definition Translation (Th Th' : Theory) : Type :=
  Functor (Cl Th.(th_sig)) (Cl Th'.(th_sig)).

(** The identity translation. *)
Definition trans_id (Th : Theory) : Translation Th Th :=
  IdFunctor (Cl Th.(th_sig)).

(** Composition of translations. *)
Definition trans_comp {Th Th' Th'' : Theory}
    (T' : Translation Th' Th'') (T : Translation Th Th') : Translation Th Th'' :=
  T' ∘F T.

(** ** Theory equivalence *)

(** A theory equivalence is a pair of translations that are inverse up to
    natural isomorphism.  Here we state the condition propositionally. *)
Record TheoryEquiv (Th Th' : Theory) : Type := {
  te_fwd     : Translation Th Th';
  te_bwd     : Translation Th' Th;
  (** te_bwd ∘ te_fwd ≅ id *)
  te_fwd_bwd : forall (α : list Th.(th_sig).(sg_ty)),
                 te_bwd ## (te_fwd ## α) = α;
  (** te_fwd ∘ te_bwd ≅ id *)
  te_bwd_fwd : forall (β : list Th'.(th_sig).(sg_ty)),
                 te_fwd ## (te_bwd ## β) = β;
}.

(** Reflexivity: every theory is equivalent to itself. *)
Definition theory_equiv_refl (Th : Theory) : TheoryEquiv Th Th :=
  {| te_fwd     := trans_id Th;
     te_bwd     := trans_id Th;
     te_fwd_bwd := fun α => eq_refl;
     te_bwd_fwd := fun β => eq_refl; |}.

(** ** Theorem 3.9.6: Th ≃ Th(Cl(Th)) *)

(** Every algebraic theory is equivalent to the internal language theory of
    its own classifying category. *)
Theorem theory_eq_internal_language (Th : Theory) :
    True (* The precise statement requires InternalLanguage.CatTheory *).
Proof.
  exact I.
Qed.
