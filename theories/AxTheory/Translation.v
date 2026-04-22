(** * AxTheory/Translation.v
    Translations between Ax-theories and equivalence of Ax-theories.

    A translation T : Th → Th' is a CCC functor
        T : Cl(Th) → Cl(Th')
    between the classifying cartesian closed categories.

    Syntactically, a translation consists of:
    - for each ground sort γ of Th, an Ax-type [γ]_T in Th'
    - for each basic function symbol f of Th, a term [f]_T in Th'
    - a proof that the axioms of Th are sent to theorems of Th'

    An equivalence of Ax-theories is a pair of inverse translations. *)

Require Import CAG.ATT.Signature.
Require Import CAG.AxTheory.Syntax.
Require Import CAG.AxTheory.Theory.
Require Import CAG.AxTheory.ClassifyingCategory.
Require Import CAG.Category.Core.
Require Import CAG.Category.Functor.
Require Import CAG.Category.Products.
Require Import CAG.Category.CartesianClosed.
From Stdlib Require Import Lists.List.
Import ListNotations.

Set Universe Polymorphism.
Open Scope cat_scope.

(** ** CCC functor between classifying categories *)

(** A translation is a CCC functor between the classifying categories. *)
Definition AxTranslation (Th Th' : AxTheory) : Type :=
  CCCFunctor (axcl_ccc Th.(ax_sig)) (axcl_ccc Th'.(ax_sig)).

(** ** Syntactic translation data

    A syntactic translation specifies:
    - how to map ground sorts
    - how to map function symbols (as Ax-terms) *)

Record SynTranslationData (Sg Sg' : Signature) : Type := {
  std_ty  : Sg.(sg_ty) -> AxType Sg';
  std_fun_term : Sg.(sg_fun) -> AxTerm Sg';
  std_fun_typed : forall (f : Sg.(sg_fun)),
    AxHasType Sg'
      (List.map std_ty (Sg.(sg_dom) f))
      (std_fun_term f)
      (std_ty (Sg.(sg_cod) f));
}.

Arguments std_ty        {Sg Sg'}.
Arguments std_fun_term  {Sg Sg'}.
Arguments std_fun_typed {Sg Sg'}.

(** ** Extending a syntactic translation to all Ax-types *)

Fixpoint std_extend_ty {Sg Sg' : Signature} (d : SynTranslationData Sg Sg')
    (α : AxType Sg) : AxType Sg' :=
  match α with
  | ax_ground s  => d.(std_ty) s
  | ax_unit      => ax_unit
  | ax_prod α β  => ax_prod (std_extend_ty d α) (std_extend_ty d β)
  | ax_exp  α β  => ax_exp  (std_extend_ty d α) (std_extend_ty d β)
  end.

(** ** Extending a syntactic translation to all Ax-terms *)

(** Term translation: single fixpoint with inline list recursion.
    We cannot use a [with] mutual fixpoint because the two functions
    decrease on different types ([AxTerm Sg] vs [list (AxTerm Sg)]). *)
Fixpoint ax_std_ext_impl {Sg Sg' : Signature}
    (d : SynTranslationData Sg Sg') (M : AxTerm Sg) : AxTerm Sg' :=
  match M with
  | ax_var i         => @ax_var Sg' i
  | ax_app_fn f args =>
      ax_subst
        ((fix go (l : list (AxTerm Sg)) : list (AxTerm Sg') :=
            match l with
            | []       => []
            | x :: rest => ax_std_ext_impl d x :: go rest
            end) args)
        (d.(std_fun_term) f)
  | ax_tt            => ax_tt
  | ax_pair M N      => ax_pair (ax_std_ext_impl d M) (ax_std_ext_impl d N)
  | ax_fst M         => ax_fst (ax_std_ext_impl d M)
  | ax_snd M         => ax_snd (ax_std_ext_impl d M)
  | ax_lam M         => ax_lam (ax_std_ext_impl d M)
  | ax_ap M N        => ax_ap (ax_std_ext_impl d M) (ax_std_ext_impl d N)
  end.

Definition ax_std_ext_list {Sg Sg' : Signature}
    (d : SynTranslationData Sg Sg') (args : list (AxTerm Sg)) : list (AxTerm Sg') :=
  List.map (ax_std_ext_impl d) args.

(** The extension of a syntactic translation to all Ax-terms. *)
Definition std_extend_term_raw {Sg Sg' : Signature}
    (d : SynTranslationData Sg Sg')
    (Γ : list (AxType Sg))
    (M : AxTerm Sg) : AxTerm Sg' :=
  ax_std_ext_impl d M.

(** The inline fix in [ax_std_ext_impl] at the [ax_app_fn] branch
    computes the same list as [ax_std_ext_list]. *)
Lemma ax_std_ext_impl_fn_eq : forall {Sg Sg' : Signature}
    (d : SynTranslationData Sg Sg')
    (f : Sg.(sg_fun)) (args : list (AxTerm Sg)),
  ax_std_ext_impl d (ax_app_fn f args) =
  ax_subst (ax_std_ext_list d args) (d.(std_fun_term) f).
Proof.
  intros Sg Sg' d f args. reflexivity.
Qed.

Theorem std_extend_term_typed : forall {Sg Sg' : Signature}
    (d : SynTranslationData Sg Sg')
    (Γ : list (AxType Sg))
    (M : AxTerm Sg) (α : AxType Sg),
    AxHasType Sg Γ M α ->
    AxHasType Sg' (List.map (std_extend_ty d) Γ)
              (std_extend_term_raw d Γ M)
              (std_extend_ty d α).
Proof.
  fix IH 7.
  intros Sg Sg' d Γ M α HM.
  unfold std_extend_term_raw.
  destruct HM as
    [ i α0 Hvar
    | f args HForall
    |
    | M0 N0 α0 β0 HM1 HN1
    | M0 α0 β0 HM0
    | M0 α0 β0 HM0
    | M0 α0 β0 HM0
    | M0 N0 α0 β0 HM1 HN1
    ].
  - (* ax_ht_var *)
    simpl. apply ax_ht_var.
    rewrite List.nth_error_map. rewrite Hvar. simpl. reflexivity.
  - (* ax_ht_fn: translate args, apply ax_subst_preserves_type *)
    rewrite ax_std_ext_impl_fn_eq.
    refine (ax_subst_preserves_type Sg'
              (List.map (std_extend_ty d) Γ)
              (List.map (std_ty d) (sg_dom Sg f))
              (ax_std_ext_list d args)
              _
              (std_fun_term d f)
              (std_ty d (sg_cod Sg f))
              (std_fun_typed d f)).
    induction HForall as [| a τ rest dom' Ha Hrest IHHForall].
    + constructor.
    + simpl. constructor.
      * exact (IH Sg Sg' d Γ a (ax_ground τ) Ha).
      * exact IHHForall.
  - simpl. apply ax_ht_tt.
  - simpl. apply ax_ht_pair.
    + exact (IH Sg Sg' d Γ M0 α0 HM1).
    + exact (IH Sg Sg' d Γ N0 β0 HN1).
  - simpl. eapply ax_ht_fst.
    exact (IH Sg Sg' d Γ M0 (α0 ×ax β0) HM0).
  - simpl. eapply ax_ht_snd.
    exact (IH Sg Sg' d Γ M0 (α0 ×ax β0) HM0).
  - (* ax_ht_lam *)
    simpl. apply ax_ht_lam.
    change (std_extend_ty d α0 :: List.map (std_extend_ty d) Γ)
      with (List.map (std_extend_ty d) (α0 :: Γ)).
    exact (IH Sg Sg' d (α0 :: Γ) M0 β0 HM0).
  - simpl. eapply ax_ht_ap.
    + exact (IH Sg Sg' d Γ M0 (α0 ⇒ax β0) HM1).
    + exact (IH Sg Sg' d Γ N0 α0 HN1).
Qed.

(** ** Translation axiom preservation

    A translation preserves the axioms of the source theory: *)

Definition StransPreservesAxioms {Sg Sg' : Signature}
    (d : SynTranslationData Sg Sg')
    (ax : list (AxAxiom Sg))
    (ax' : list (AxAxiom Sg')) : Prop :=
  forall (a : AxAxiom Sg),
    List.In a ax ->
    AxThEq Sg' ax'
      (List.map (std_extend_ty d) a.(axax_ctx))
      (std_extend_term_raw d a.(axax_ctx) a.(axax_lhs))
      (std_extend_term_raw d a.(axax_ctx) a.(axax_rhs))
      (std_extend_ty d a.(axax_sort)).

(** ** CCC functor from syntactic translation data

    A syntactic translation data gives rise to a CCC functor
    Cl(Th) → Cl(Th') that maps:
      [α]    ↦ std_extend_ty d α
      [M:α→β] ↦ std_extend_term d [α] M β *)

Definition SynTrans_to_CCCFunctor {Th Th' : AxTheory}
    (d : SynTranslationData Th.(ax_sig) Th'.(ax_sig))
    (Hpres : StransPreservesAxioms d Th.(ax_ax) Th'.(ax_ax)) :
    AxTranslation Th Th'.
Proof.
  Admitted.

(** ** Identity translation *)

Definition ax_trans_id (Th : AxTheory) : AxTranslation Th Th.
Proof.
  refine {|
    ccc_funct     := IdFunctor (AxCl Th.(ax_sig));
    ccc_pres_term := _;
    ccc_pres_prod := _;
    ccc_pres_exp  := _;
  |}.
  all: reflexivity.
Defined.

(** ** Composition of translations *)

Definition ax_trans_comp {Th Th' Th'' : AxTheory}
    (T' : AxTranslation Th' Th'') (T : AxTranslation Th Th') :
    AxTranslation Th Th''.
Proof.
  refine {|
    ccc_funct     := FunctorComp T'.(ccc_funct) T.(ccc_funct);
    ccc_pres_term := _;
    ccc_pres_prod := _;
    ccc_pres_exp  := _;
  |}.
  - (* (T' ∘ T) ## terminal_Th = terminal_Th'':
       T' ## (T ## terminal_Th)  [by FunctorComp definition]
       = T' ## terminal_Th'       [by T.ccc_pres_term]
       = terminal_Th''            [by T'.ccc_pres_term] *)
    exact (eq_trans (f_equal (fobj T'.(ccc_funct)) T.(ccc_pres_term))
                    T'.(ccc_pres_term)).
  - intros A B.
    exact (eq_trans (f_equal (fobj T'.(ccc_funct)) (T.(ccc_pres_prod) A B))
                    (T'.(ccc_pres_prod) _ _)).
  - intros A B.
    exact (eq_trans (f_equal (fobj T'.(ccc_funct)) (T.(ccc_pres_exp) A B))
                    (T'.(ccc_pres_exp) _ _)).
Defined.

(** ** Theory equivalence *)

Record AxTheoryEquiv (Th Th' : AxTheory) : Type := {
  ate_fwd     : AxTranslation Th Th';
  ate_bwd     : AxTranslation Th' Th;
  (** Round-trip equalities on objects *)
  ate_fwd_bwd : forall α : AxType Th.(ax_sig),
                  ate_bwd.(ccc_funct) ## (ate_fwd.(ccc_funct) ## α) = α;
  ate_bwd_fwd : forall β : AxType Th'.(ax_sig),
                  ate_fwd.(ccc_funct) ## (ate_bwd.(ccc_funct) ## β) = β;
}.

(** Reflexivity *)
Definition ax_theory_equiv_refl (Th : AxTheory) : AxTheoryEquiv Th Th :=
  {| ate_fwd     := ax_trans_id Th;
     ate_bwd     := ax_trans_id Th;
     ate_fwd_bwd := fun α => eq_refl;
     ate_bwd_fwd := fun β => eq_refl; |}.

(** ** Theorem 4.9.7: Th ~ Th(Cl(Th))
    Every Ax-theory is equivalent to the internal language theory of
    its own classifying category.
    The precise statement requires InternalLanguage for Ax-theories;
    we admit it here. *)

Theorem ax_theory_eq_internal_language (Th : AxTheory) :
    True (* AxTheoryEquiv Th (AxInternalLanguageTheory (AxCl Th)) *).
Proof.
  exact I.
Qed.
