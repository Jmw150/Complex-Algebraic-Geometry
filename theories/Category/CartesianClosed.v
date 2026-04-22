(** * Category/CartesianClosed.v
    Cartesian closed categories (CCC): categories with finite products
    and exponential objects.

    An exponential (function-type) B^A comes with:
    - eval : B^A × A → B
    - curry (transpose): for any f : C × A → B, a unique
        Λ(f) : C → B^A  with  eval ∘ (Λ(f) × id_A) = f. *)

Require Import CAG.Category.Core.
Require Import CAG.Category.Products.
Require Import CAG.Category.Functor.

Set Universe Polymorphism.
Open Scope cat_scope.

(** ** Exponential object *)

(** [IsExponential bp A B E] asserts that E is the exponential B^A,
    where bp is a binary product structure for C.  We parametrize over
    bp so that the same exponential can be used with different product
    witnesses. *)

Record IsExponential {C : Category} (hp : HasBinaryProducts C)
    (A B E : C.(Ob)) : Type := {
  (** Evaluation morphism  eval : E × A → B *)
  exp_eval  : C⟦ E ×{hp} A, B ⟧;

  (** Currying / transposition:
      for any C and f : C × A → B, produce Λ(f) : C → E *)
  exp_curry : forall {X : C.(Ob)}, C⟦ X ×{hp} A, B ⟧ -> C⟦ X, E ⟧;

  (** Beta reduction: eval ∘ (Λ(f) × id_A) = f *)
  exp_beta  : forall {X : C.(Ob)} (f : C⟦ X ×{hp} A, B ⟧),
                exp_eval ∘ prod_map (hp.(prod_bp) X A) (hp.(prod_bp) E A)
                                    (exp_curry f) (C.(id) A) = f;

  (** Eta / uniqueness: Λ(eval ∘ (g × id_A)) = g *)
  exp_eta   : forall {X : C.(Ob)} (g : C⟦ X, E ⟧),
                exp_curry (exp_eval ∘ prod_map (hp.(prod_bp) X A)
                                               (hp.(prod_bp) E A)
                                               g (C.(id) A)) = g;
}.

Arguments exp_eval  {C hp A B E}.
Arguments exp_curry {C hp A B E} _ {X}.
Arguments exp_beta  {C hp A B E} _ {X}.
Arguments exp_eta   {C hp A B E} _ {X}.

(** ** Category with exponentials *)

Record HasExponentials (C : Category) (hp : HasBinaryProducts C) : Type := {
  exp_obj : C.(Ob) -> C.(Ob) -> C.(Ob);  (* exp_obj A B = B^A *)
  exp_is  : forall A B, IsExponential hp A B (exp_obj A B);
}.

Arguments exp_obj {C hp} h A B.
Arguments exp_is  {C hp} h A B.

(** ** Cartesian closed category *)

Record IsCartesianClosed (C : Category) : Type := {
  ccc_fp   : HasFiniteProducts C;
  ccc_exp  : HasExponentials C (@fp_binary C ccc_fp);
}.

Arguments ccc_fp  {C}.
Arguments ccc_exp {C}.

(** Convenient accessor: the binary product structure from a CCC. *)
Definition ccc_bp {C : Category} (ccc : IsCartesianClosed C) : HasBinaryProducts C :=
  @fp_binary C ccc.(ccc_fp).

(** Notation: A ⇒ B for B^A in a CCC. *)
Notation "A ⇒{ ccc } B" := (exp_obj ccc.(ccc_exp) A B)
  (at level 55, right associativity) : cat_scope.

(** ** CCC functor *)

(** A functor between CCCs that preserves finite products and exponentials. *)

Record CCCFunctor {C D : Category} (cC : IsCartesianClosed C)
    (cD : IsCartesianClosed D) : Type := {
  ccc_funct      :> Functor C D;

  (** Preserves terminal object *)
  ccc_pres_term  : ccc_funct ## (projT1 (@fp_terminal C cC.(ccc_fp))) =
                   projT1 (@fp_terminal D cD.(ccc_fp));

  (** Preserves binary products (up to equality of objects) *)
  ccc_pres_prod  : forall A B,
                     ccc_funct ## (A ×{@fp_binary C cC.(ccc_fp)} B) =
                     ccc_funct ## A ×{@fp_binary D cD.(ccc_fp)} ccc_funct ## B;

  (** Preserves exponentials (up to equality of objects) *)
  ccc_pres_exp   : forall A B,
                     ccc_funct ## (A ⇒{cC} B) =
                     ccc_funct ## A ⇒{cD} ccc_funct ## B;
}.

Arguments ccc_funct     {C D cC cD}.
Arguments ccc_pres_term {C D cC cD}.
Arguments ccc_pres_prod {C D cC cD}.
Arguments ccc_pres_exp  {C D cC cD}.

(** ** Key identities for CCCs *)

(** Currying is natural: curry distributes over composition. *)
Lemma exp_curry_comp {C : Category} (hp : HasBinaryProducts C)
    {A B E X Y : C.(Ob)} (ex : IsExponential hp A B E)
    (f : C⟦ X ×{hp} A, B ⟧) (g : C⟦ Y, X ⟧) :
    ex.(exp_curry) (f ∘ prod_map (hp.(prod_bp) Y A) (hp.(prod_bp) X A)
                                  g (C.(id) A)) =
    ex.(exp_curry) f ∘ g.
Proof.
  (* Establish: exp_eval ∘ prod_map (exp_curry f ∘ g) id = f ∘ prod_map g id *)
  assert (Hstep :
    exp_eval ex ∘ prod_map (hp.(prod_bp) Y A) (hp.(prod_bp) E A)
                           (exp_curry ex f ∘ g) (C.(id) A) =
    f ∘ prod_map (hp.(prod_bp) Y A) (hp.(prod_bp) X A) g (C.(id) A)).
  { (* RHS of this goal via comp_assoc and prod_map_comp *)
    transitivity ((exp_eval ex ∘ prod_map (hp.(prod_bp) X A) (hp.(prod_bp) E A)
                                          (exp_curry ex f) (C.(id) A))
                  ∘ prod_map (hp.(prod_bp) Y A) (hp.(prod_bp) X A) g (C.(id) A)).
    - (* show LHS = (eval ∘ prod_map (exp_curry f) id) ∘ prod_map g id
         by unfolding RHS: (A ∘ B) ∘ C = A ∘ (B ∘ C) then using prod_map_comp *)
      rewrite <- C.(comp_assoc).
      rewrite prod_map_comp.
      rewrite C.(id_left).
      reflexivity.
    - rewrite exp_beta. reflexivity. }
  rewrite <- Hstep.
  apply exp_eta.
Qed.

(** The exponential functor: (- ⇒ B) is contravariant in the first argument,
    (A ⇒ -) is covariant in the second.
    We record the covariant post-composition action. *)

Definition exp_map_cod {C : Category} (hp : HasBinaryProducts C)
    {A B B' E E' : C.(Ob)}
    (ex  : IsExponential hp A B  E)
    (ex' : IsExponential hp A B' E')
    (f : C⟦ B, B' ⟧) : C⟦ E, E' ⟧ :=
  ex'.(exp_curry) (f ∘ ex.(exp_eval)).

(** ** Closed structure: the internal hom *)

(** For a fixed CCC C with chosen exponentials, we have:
    Hom(X × A, B) ≅ Hom(X, B^A). *)

Definition curry_iso_fwd {C : Category} (hp : HasBinaryProducts C)
    {A B E X : C.(Ob)} (ex : IsExponential hp A B E)
    (f : C⟦ X ×{hp} A, B ⟧) : C⟦ X, E ⟧ :=
  ex.(exp_curry) f.

Definition curry_iso_bwd {C : Category} (hp : HasBinaryProducts C)
    {A B E X : C.(Ob)} (ex : IsExponential hp A B E)
    (g : C⟦ X, E ⟧) : C⟦ X ×{hp} A, B ⟧ :=
  ex.(exp_eval) ∘ prod_map (hp.(prod_bp) X A)
                            (hp.(prod_bp) E A)
                            g (C.(id) A).

Lemma curry_iso_bwd_fwd {C : Category} (hp : HasBinaryProducts C)
    {A B E X : C.(Ob)} (ex : IsExponential hp A B E)
    (f : C⟦ X ×{hp} A, B ⟧) :
    curry_iso_bwd hp ex (curry_iso_fwd hp ex f) = f.
Proof.
  unfold curry_iso_bwd, curry_iso_fwd.
  apply ex.(exp_beta).
Qed.

Lemma curry_iso_fwd_bwd {C : Category} (hp : HasBinaryProducts C)
    {A B E X : C.(Ob)} (ex : IsExponential hp A B E)
    (g : C⟦ X, E ⟧) :
    curry_iso_fwd hp ex (curry_iso_bwd hp ex g) = g.
Proof.
  unfold curry_iso_bwd, curry_iso_fwd.
  apply ex.(exp_eta).
Qed.
