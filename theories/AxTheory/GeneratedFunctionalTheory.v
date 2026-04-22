(** * AxTheory/GeneratedFunctionalTheory.v
    The Ax-theory generated from an algebraic theory.

    Given an algebraic theory Th, we generate an Ax-theory Th' with:
    - the same underlying signature Sg = Th.sig
    - axioms that include both:
      (a) the lifted algebraic axioms (equations at ground types)
      (b) the structural beta/eta equations (which are already built into AxThEq)

    The main content:
    - Definition of the generated Ax-theory Th' from an algebraic Th
    - The functor I : Cl(Th) → Cl(Th')
    - The conservativity statement:
        if Th' ⊢ Γ ⊢ M = N : γ  (ground types, algebraic context)
        then  Th ⊢ Γ ⊢ M = N : γ

    This file prepares the setup for the gluing proof. *)

Require Import CAG.ATT.Signature.
Require Import CAG.ATT.Syntax.
Require Import CAG.ATT.Theory.
Require Import CAG.ATT.ClassifyingCategory.
Require Import CAG.AxTheory.Syntax.
Require Import CAG.AxTheory.Theory.
Require Import CAG.AxTheory.ClassifyingCategory.
Require Import CAG.AxTheory.RelativeFreeCCC.
Require Import CAG.Category.Core.
Require Import CAG.Category.Functor.
From Stdlib Require Import Lists.List.
Import ListNotations.

Set Universe Polymorphism.
Open Scope cat_scope.

(** ** Lifting algebraic axioms to Ax-axioms

    An algebraic axiom a : TheoryAxiom Sg has a context (list of ground sorts),
    an LHS and RHS (algebraic terms), and a common sort.
    We lift it to an AxAxiom by embedding everything into the Ax world. *)

(** Lift an algebraic term to an Ax-term (using only ax_var and ax_app_fn). *)
Fixpoint lift_alg_term {Sg : Signature} (t : Term Sg) : AxTerm Sg :=
  match t with
  | t_var n       => ax_var n
  | t_app f args  => ax_app_fn f (List.map lift_alg_term args)
  end.

(** Lifting preserves types. *)
Lemma lift_alg_term_typed (Sg : Signature)
    (Γ : list Sg.(sg_ty))
    (t : Term Sg) (τ : Sg.(sg_ty))
    (Ht : HasType Sg Γ t τ) :
    AxHasType Sg (List.map ax_ground Γ) (lift_alg_term t) (ax_ground τ).
Proof.
  revert t τ Ht.
  fix IH 3.
  intros t τ Ht.
  destruct Ht as [n τ Hn | f args Hargs].
  - (* ht_var: ax_var n is well-typed at ax_ground τ *)
    apply ax_ht_var.
    rewrite List.nth_error_map, Hn. reflexivity.
  - (* ht_app: recurse over the argument list *)
    simpl. apply ax_ht_fn.
    induction Hargs as [| a τ' args' dom' Ha Hrest IHargs].
    + constructor.
    + constructor.
      * exact (IH a τ' Ha).
      * exact IHargs.
Qed.

(** Lift an algebraic axiom to an Ax-axiom. *)
Definition lift_alg_axiom {Sg : Signature} (a : TheoryAxiom Sg) : AxAxiom Sg :=
  {| axax_ctx       := List.map ax_ground a.(ax_ctx);
     axax_lhs       := lift_alg_term a.(ax_lhs);
     axax_rhs       := lift_alg_term a.(ax_rhs);
     axax_sort      := ax_ground a.(ax_sort);
     axax_lhs_typed := lift_alg_term_typed Sg a.(ax_ctx) a.(ax_lhs) a.(ax_sort) a.(ax_lhs_typed);
     axax_rhs_typed := lift_alg_term_typed Sg a.(ax_ctx) a.(ax_rhs) a.(ax_sort) a.(ax_rhs_typed); |}.

(** ** Generated Ax-theory *)

Definition GeneratedAxTheory (Th : Theory) : AxTheory := {|
  ax_sig := Th.(th_sig);
  ax_ax  := List.map lift_alg_axiom Th.(th_ax);
|}.

(** ** The functor I : Cl(Th) → AxCl(Sg)

    This is exactly the functor I_functor from RelativeFreeCCC.v,
    instantiated to the algebraic classifying category. *)

Definition I_alg_functor (Th : Theory) :
    Functor (Cl Th.(th_sig)) (AxCl Th.(th_sig)) :=
  I_functor Th.(th_sig).

(** ** Ground-type conservativity

    If two algebraic terms M, N are provably equal in the generated
    Ax-theory Th' at ground types and algebraic context, then they
    are already provably equal in the algebraic theory Th. *)

Theorem ground_type_conservativity (Th : Theory)
    (Γ : list Th.(th_sig).(sg_ty))
    (t1 t2 : Term Th.(th_sig))
    (τ : Th.(th_sig).(sg_ty))
    (Ht1 : HasType Th.(th_sig) Γ t1 τ)
    (Ht2 : HasType Th.(th_sig) Γ t2 τ)
    (Heq : AxThEq Th.(th_sig) (List.map lift_alg_axiom Th.(th_ax))
                  (List.map ax_ground Γ)
                  (lift_alg_term t1)
                  (lift_alg_term t2)
                  (ax_ground τ)) :
    ThEq Th.(th_sig) Th.(th_ax) Γ t1 t2 τ.
Proof.
  (* This is the main conservativity result — proved via gluing in GluingSetup.v *)
  Admitted.
