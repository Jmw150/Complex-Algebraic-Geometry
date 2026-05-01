(** * AxTheory/ClassifyingCategory.v
    The classifying category Cl(Th) of an Ax-theory Th.

    Objects: Ax-types  AxType Sg.

    Morphisms α → β: equivalence class (under provable AxThEq w.r.t.
    the empty axiom set) of an Ax-term M with AxHasType Sg [α] M β.

    The resulting category is cartesian closed:
    - terminal object: ax_unit
    - binary product: ax_prod α β
    - exponential: ax_exp α β

    NOTE.  Earlier versions of this file built the syntactic category
    on raw representatives and axiomatised the β/η laws as
    Leibniz-equalities (which are FALSE on raw representatives — they
    only hold modulo AxThEq).  Round γ-A diagnosed substitution
    congruence ([ax_subst_cong]) as the key lemma needed for the
    quotient construction, and Task A.0 added it to Syntax.v.  This
    file now quotients morphisms by AxThEq and discharges the
    product β/η laws as real lemmas via [ax_subst_cong] + the
    AxThEq β/η constructors.

    The quotient is constructed in the standard way, mirroring
    [theories/Rings/Quotients.v]: a morphism is the
    [AxThEq]-equivalence class of a representative, represented as a
    sigma over predicates, with [functional_extensionality] +
    [propositional_extensionality] used to identify equivalent
    classes.

    Task A.1b discharged the two exponential rules ([axcl_exp_beta],
    [axcl_exp_eta]) on top of A.1's quotient framework: each is a
    multi-step AxThEq derivation chaining [axeq_beta_lam] /
    [axeq_eta_lam] / [axeq_beta_fst] / [axeq_beta_snd] /
    [axeq_eta_prod] congruence steps with [ax_subst_cong] +
    [ax_subst_comp] bookkeeping.  The only rule still axiomatised is
    [axcl_terminal_unique], which requires [axeq_eta_unit] (not in
    current Syntax.v) — discharging it requires editing Syntax.v,
    which is out of scope.  With the quotient infrastructure in place,
    adding [axeq_eta_unit] to AxThEq would make the discharge a
    one-liner. *)

Require Import CAG.ATT.Signature.
Require Import CAG.AxTheory.Syntax.
Require Import CAG.AxTheory.Theory.
Require Import CAG.Category.Core.
Require Import CAG.Category.Products.
Require Import CAG.Category.CartesianClosed.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.PropExtensionality.
Import ListNotations.

Set Universe Polymorphism.
Open Scope cat_scope.

(* ================================================================== *)
(** ** Representative morphisms: typed terms in singleton context *)
(* ================================================================== *)

(** A representative morphism α → β is a term M with
    AxHasType Sg [α] M β.  The kept name [AxClMor] is the
    representative type (so downstream files can still refer to it);
    the actual category morphism is the quotient [AxClMor_q] introduced
    below. *)

Record AxClMor (Sg : Signature) (α β : AxType Sg) : Type := {
  axcl_term  : AxTerm Sg;
  axcl_typed : AxHasType Sg [α] axcl_term β;
}.

Arguments axcl_term  {Sg α β}.
Arguments axcl_typed {Sg α β}.

Lemma axcl_ext (Sg : Signature) (α β : AxType Sg) (f g : AxClMor Sg α β) :
    f.(axcl_term) = g.(axcl_term) -> f = g.
Proof.
  intro H. destruct f, g. simpl in H. subst.
  f_equal. apply proof_irrelevance.
Qed.

(** Identity-on-representatives: variable 0 in singleton context. *)
Definition axcl_id_rep (Sg : Signature) (α : AxType Sg) : AxClMor Sg α α :=
  {| axcl_term  := ax_var 0;
     axcl_typed := ax_ht_var Sg [α] 0 α eq_refl; |}.

(** Composition-on-representatives: substitute. *)
Lemma axcl_comp_rep_typed (Sg : Signature) (α β γ : AxType Sg)
    (f : AxClMor Sg α β) (g : AxClMor Sg β γ) :
    AxHasType Sg [α] (ax_subst [f.(axcl_term)] g.(axcl_term)) γ.
Proof.
  apply ax_subst_preserves_type with [β].
  - constructor. exact f.(axcl_typed). constructor.
  - exact g.(axcl_typed).
Qed.

Definition axcl_comp_rep (Sg : Signature) (α β γ : AxType Sg)
    (g : AxClMor Sg β γ) (f : AxClMor Sg α β) : AxClMor Sg α γ :=
  {| axcl_term  := ax_subst [f.(axcl_term)] g.(axcl_term);
     axcl_typed := axcl_comp_rep_typed Sg α β γ f g; |}.

(* ================================================================== *)
(** ** AxThEq-equivalence on representatives + class predicates *)
(* ================================================================== *)

(** Provable equality on representatives, w.r.t. the empty axiom set
    (the structural β/η rules of [AxThEq] suffice for the
    classifying category itself; theory-specific axioms come in on
    top via [Theory.v]). *)
Definition AxClMor_eq (Sg : Signature) (α β : AxType Sg)
    (m m' : AxClMor Sg α β) : Prop :=
  AxThEq Sg [] [α] m.(axcl_term) m'.(axcl_term) β.

Lemma AxClMor_eq_refl (Sg : Signature) (α β : AxType Sg) (m : AxClMor Sg α β) :
    AxClMor_eq Sg α β m m.
Proof.
  unfold AxClMor_eq. apply axeq_refl. exact m.(axcl_typed).
Qed.

Lemma AxClMor_eq_sym (Sg : Signature) (α β : AxType Sg) (m m' : AxClMor Sg α β) :
    AxClMor_eq Sg α β m m' -> AxClMor_eq Sg α β m' m.
Proof. unfold AxClMor_eq. intros. apply axeq_sym. exact H. Qed.

Lemma AxClMor_eq_trans (Sg : Signature) (α β : AxType Sg)
    (m1 m2 m3 : AxClMor Sg α β) :
    AxClMor_eq Sg α β m1 m2 -> AxClMor_eq Sg α β m2 m3 ->
    AxClMor_eq Sg α β m1 m3.
Proof.
  unfold AxClMor_eq. intros H1 H2.
  exact (axeq_trans Sg [] [α] _ _ _ β H1 H2).
Qed.

(** The equivalence class of a representative as a predicate. *)
Definition AxThEq_class_of {Sg : Signature} {α β : AxType Sg}
    (m : AxClMor Sg α β) : AxClMor Sg α β -> Prop :=
  fun m' => AxClMor_eq Sg α β m m'.

(** Quotient morphisms: predicates that are representable as some class. *)
Definition AxClMor_q (Sg : Signature) (α β : AxType Sg) : Type :=
  { S : AxClMor Sg α β -> Prop | exists m, S = AxThEq_class_of m }.

(** Constructing a quotient morphism from a representative. *)
Definition mk_q {Sg : Signature} {α β : AxType Sg}
    (m : AxClMor Sg α β) : AxClMor_q Sg α β :=
  exist _ (AxThEq_class_of m) (ex_intro _ m eq_refl).

Lemma class_of_eq_iff (Sg : Signature) (α β : AxType Sg)
    (m m' : AxClMor Sg α β) :
    AxThEq_class_of m = AxThEq_class_of m' <-> AxClMor_eq Sg α β m m'.
Proof.
  unfold AxThEq_class_of. split.
  - intro Heq.
    assert (Hself : (fun m'0 : AxClMor Sg α β => AxClMor_eq Sg α β m' m'0) m').
    { apply AxClMor_eq_refl. }
    rewrite <- Heq in Hself.
    exact Hself.
  - intro Hmm'.
    apply functional_extensionality. intro x.
    apply propositional_extensionality. split.
    + intro Hmx. apply (AxClMor_eq_trans Sg α β m' m x).
      * apply AxClMor_eq_sym. exact Hmm'.
      * exact Hmx.
    + intro Hm'x. apply (AxClMor_eq_trans Sg α β m m' x); assumption.
Qed.

Lemma mk_q_eq_iff (Sg : Signature) (α β : AxType Sg)
    (m m' : AxClMor Sg α β) :
    mk_q m = mk_q m' <-> AxClMor_eq Sg α β m m'.
Proof.
  split.
  - intro Heq.
    assert (Hpred : AxThEq_class_of m = AxThEq_class_of m').
    { apply (f_equal (@proj1_sig _ _)) in Heq. exact Heq. }
    apply class_of_eq_iff. exact Hpred.
  - intro Hmm'.
    assert (Hpred : AxThEq_class_of m = AxThEq_class_of m').
    { apply class_of_eq_iff. exact Hmm'. }
    unfold mk_q.
    apply eq_sig_uncurried. simpl.
    exists Hpred. apply proof_irrelevance.
Qed.

Lemma mk_q_surj (Sg : Signature) (α β : AxType Sg) (q : AxClMor_q Sg α β) :
    exists m : AxClMor Sg α β, mk_q m = q.
Proof.
  destruct q as [S [m Hm]]. exists m.
  unfold mk_q.
  apply eq_sig_uncurried. simpl.
  exists (eq_sym Hm). apply proof_irrelevance.
Qed.

Lemma AxClMor_q_eq (Sg : Signature) (α β : AxType Sg)
    (q1 q2 : AxClMor_q Sg α β) :
    proj1_sig q1 = proj1_sig q2 -> q1 = q2.
Proof.
  intro H. destruct q1 as [S1 H1], q2 as [S2 H2]. simpl in H.
  apply eq_sig_uncurried. simpl. exists H. apply proof_irrelevance.
Qed.

(* ================================================================== *)
(** ** Operations on the quotient *)
(* ================================================================== *)

Definition axcl_id (Sg : Signature) (α : AxType Sg) : AxClMor_q Sg α α :=
  mk_q (axcl_id_rep Sg α).

(** Composition is well-defined modulo AxThEq via [ax_subst_cong]. *)
Lemma axcl_comp_well_defined (Sg : Signature) (α β γ : AxType Sg)
    (g1 g2 : AxClMor Sg β γ) (f1 f2 : AxClMor Sg α β) :
    AxClMor_eq Sg β γ g1 g2 ->
    AxClMor_eq Sg α β f1 f2 ->
    AxClMor_eq Sg α γ
      (axcl_comp_rep Sg α β γ g1 f1)
      (axcl_comp_rep Sg α β γ g2 f2).
Proof.
  unfold AxClMor_eq, axcl_comp_rep. simpl. intros Hg Hf.
  apply (ax_subst_cong Sg [] [α] [β]
                       [f1.(axcl_term)] [f2.(axcl_term)]
                       g1.(axcl_term) g2.(axcl_term) γ).
  - constructor. exact f1.(axcl_typed). constructor.
  - constructor. exact f2.(axcl_typed). constructor.
  - intros i α_i s s' Hai Hsi Hsi'.
    destruct i as [|i].
    + simpl in Hai. injection Hai as <-.
      simpl in Hsi. injection Hsi as <-.
      simpl in Hsi'. injection Hsi' as <-.
      exact Hf.
    + simpl in Hai. destruct i; discriminate Hai.
  - exact Hg.
Qed.

(** Composition on quotient morphisms: build the predicate
    [exists representatives g0, f0 in the input classes whose
    representative-level composition is in this class]. *)
Definition axcl_comp (Sg : Signature) (α β γ : AxType Sg)
    (g : AxClMor_q Sg β γ) (f : AxClMor_q Sg α β) : AxClMor_q Sg α γ.
Proof.
  refine (exist _
            (fun h => exists g0 f0,
                proj1_sig g g0 /\ proj1_sig f f0 /\
                AxClMor_eq Sg α γ (axcl_comp_rep Sg α β γ g0 f0) h)
            _).
  destruct g as [Sg' [g0 Hg]]; destruct f as [Sf [f0 Hf]]; simpl.
  exists (axcl_comp_rep Sg α β γ g0 f0).
  apply functional_extensionality. intro x.
  apply propositional_extensionality. split.
  - intros [g1 [f1 [Hg1 [Hf1 Hcomp]]]].
    rewrite Hg in Hg1. rewrite Hf in Hf1.
    unfold AxThEq_class_of in Hg1, Hf1.
    apply (AxClMor_eq_trans Sg α γ
              (axcl_comp_rep Sg α β γ g0 f0)
              (axcl_comp_rep Sg α β γ g1 f1) x).
    + apply axcl_comp_well_defined; assumption.
    + exact Hcomp.
  - intro Hx.
    exists g0, f0.
    rewrite Hg, Hf. unfold AxThEq_class_of.
    repeat split.
    + apply AxClMor_eq_refl.
    + apply AxClMor_eq_refl.
    + exact Hx.
Defined.

(** Computational lemma for composition. *)
Lemma axcl_comp_mk (Sg : Signature) (α β γ : AxType Sg)
    (g : AxClMor Sg β γ) (f : AxClMor Sg α β) :
    axcl_comp Sg α β γ (mk_q g) (mk_q f) =
    mk_q (axcl_comp_rep Sg α β γ g f).
Proof.
  apply AxClMor_q_eq. simpl.
  apply functional_extensionality. intro x.
  apply propositional_extensionality. split.
  - intros [g0 [f0 [Hg0 [Hf0 Hcomp]]]].
    unfold AxThEq_class_of in Hg0, Hf0.
    apply (AxClMor_eq_trans Sg α γ
             (axcl_comp_rep Sg α β γ g f)
             (axcl_comp_rep Sg α β γ g0 f0) x).
    + apply axcl_comp_well_defined; assumption.
    + exact Hcomp.
  - intro Hx.
    exists g, f. unfold AxThEq_class_of. repeat split.
    + apply AxClMor_eq_refl.
    + apply AxClMor_eq_refl.
    + exact Hx.
Qed.

(* ================================================================== *)
(** ** Category laws *)
(* ================================================================== *)

Lemma axcl_id_left (Sg : Signature) (α β : AxType Sg) (f : AxClMor_q Sg α β) :
    axcl_comp Sg α β β (axcl_id Sg β) f = f.
Proof.
  destruct (mk_q_surj Sg α β f) as [f0 Hf]. subst f.
  unfold axcl_id. rewrite axcl_comp_mk.
  apply mk_q_eq_iff.
  unfold AxClMor_eq, axcl_comp_rep, axcl_id_rep. simpl.
  (* ax_subst [f0.term] (ax_var 0) reduces by computation to f0.term. *)
  apply axeq_refl. exact f0.(axcl_typed).
Qed.

Lemma axcl_id_right (Sg : Signature) (α β : AxType Sg) (f : AxClMor_q Sg α β) :
    axcl_comp Sg α α β f (axcl_id Sg α) = f.
Proof.
  destruct (mk_q_surj Sg α β f) as [f0 Hf]. subst f.
  unfold axcl_id. rewrite axcl_comp_mk.
  apply mk_q_eq_iff.
  unfold AxClMor_eq.
  unfold axcl_comp_rep, axcl_id_rep.
  cbn [axcl_term].
  (* Goal: AxThEq Sg [] [α]
            (ax_subst [ax_var 0] f0.term) f0.term β.
     [ax_var 0] is exactly ax_id_sub Sg 1 = ax_id_sub Sg (length [α]). *)
  change (cons (ax_var 0) nil) with (ax_id_sub Sg (length (cons α nil))).
  rewrite (ax_subst_id Sg (cons α nil) f0.(axcl_term) β f0.(axcl_typed)).
  apply axeq_refl. exact f0.(axcl_typed).
Qed.

Lemma axcl_comp_assoc (Sg : Signature) (α β γ δ : AxType Sg)
    (f : AxClMor_q Sg α β) (g : AxClMor_q Sg β γ) (h : AxClMor_q Sg γ δ) :
    axcl_comp Sg α γ δ h (axcl_comp Sg α β γ g f) =
    axcl_comp Sg α β δ (axcl_comp Sg β γ δ h g) f.
Proof.
  destruct (mk_q_surj Sg α β f) as [f0 Hf]. subst f.
  destruct (mk_q_surj Sg β γ g) as [g0 Hg]. subst g.
  destruct (mk_q_surj Sg γ δ h) as [h0 Hh]. subst h.
  rewrite !axcl_comp_mk.
  apply mk_q_eq_iff.
  unfold AxClMor_eq, axcl_comp_rep. simpl.
  (* LHS: ax_subst [ax_subst [f0.term] g0.term] h0.term
     RHS: ax_subst [f0.term] (ax_subst [g0.term] h0.term)
     ax_subst_comp normalises RHS to LHS. *)
  rewrite (ax_subst_comp Sg [γ] [f0.(axcl_term)] [g0.(axcl_term)]
            h0.(axcl_term) δ eq_refl h0.(axcl_typed)).
  cbn [List.map].
  apply axeq_refl.
  (* Goal: AxHasType Sg [α]
            (ax_subst [ax_subst [f0.term] g0.term] h0.term) δ.
     This is well-typed: ax_subst [g0.term] h0.term : γ ⇒
       ax_subst [.] over [γ] context with proper typing of [f0.term]
       gives a term of type δ. *)
  set (gf := ax_subst (cons (axcl_term f0) nil) (axcl_term g0)).
  apply (ax_subst_preserves_type Sg (cons α nil) (cons γ nil)
           (cons gf nil)).
  - constructor.
    + unfold gf.
      apply (ax_subst_preserves_type Sg (cons α nil) (cons β nil)
               (cons (axcl_term f0) nil)).
      * constructor. exact f0.(axcl_typed). constructor.
      * exact g0.(axcl_typed).
    + constructor.
  - exact h0.(axcl_typed).
Qed.

(* ================================================================== *)
(** ** The classifying category *)
(* ================================================================== *)

Definition AxCl (Sg : Signature) : Category := {|
  Ob   := AxType Sg;
  Hom  := AxClMor_q Sg;
  id   := axcl_id Sg;
  comp := fun α β γ g f => axcl_comp Sg α β γ g f;
  comp_assoc := fun α β γ δ h g f => axcl_comp_assoc Sg α β γ δ f g h;
  id_left  := fun α β f => axcl_id_left  Sg α β f;
  id_right := fun α β f => axcl_id_right Sg α β f;
|}.

(* ================================================================== *)
(** ** Terminal object: ax_unit *)
(* ================================================================== *)

Definition axcl_to_unit_rep (Sg : Signature) (α : AxType Sg) :
    AxClMor Sg α ax_unit :=
  {| axcl_term := ax_tt; axcl_typed := ax_ht_tt Sg [α] |}.

Definition axcl_to_unit (Sg : Signature) (α : AxType Sg) :
    AxCl Sg ⟦ α, ax_unit ⟧ :=
  mk_q (axcl_to_unit_rep Sg α).

(** Terminal-uniqueness in the quotient: DISCHARGED.
    Uses [axeq_eta_unit] (added to AxThEq in Syntax.v as part of
    Task A.1, paralleling [axeq_eta_prod] for binary products).
    With unit-η in hand, the discharge is the expected one-liner:
    after surjecting onto a representative [f0], the goal reduces
    to [f0.term ~~ ax_tt] in [AxThEq], which is precisely
    [axeq_eta_unit] applied to [f0.term]'s typing. *)
Lemma axcl_terminal_unique : forall (Sg : Signature) (α : AxType Sg)
    (f : AxCl Sg ⟦ α, ax_unit ⟧),
    f = axcl_to_unit Sg α.
Proof.
  intros Sg α f.
  destruct (mk_q_surj Sg α ax_unit f) as [f0 Hf]. subst f.
  unfold axcl_to_unit.
  apply mk_q_eq_iff.
  unfold AxClMor_eq, axcl_to_unit_rep. simpl.
  apply axeq_eta_unit. exact f0.(axcl_typed).
Qed.

Definition axcl_is_terminal (Sg : Signature) : @IsTerminal (AxCl Sg) ax_unit.
Proof.
  apply Build_IsTerminal with (term_arr := axcl_to_unit Sg).
  intros α f. exact (axcl_terminal_unique Sg α f).
Defined.

(* ================================================================== *)
(** ** Binary product: ax_prod — β/η laws DISCHARGED *)
(* ================================================================== *)

Definition axcl_proj1_rep (Sg : Signature) (α β : AxType Sg) :
    AxClMor Sg (α ×ax β) α :=
  {| axcl_term  := ax_fst (ax_var 0);
     axcl_typed := ax_ht_fst Sg [α ×ax β] (ax_var 0) α β
                     (ax_ht_var Sg [α ×ax β] 0 (α ×ax β) eq_refl); |}.

Definition axcl_proj1 (Sg : Signature) (α β : AxType Sg) :
    AxCl Sg ⟦ α ×ax β, α ⟧ :=
  mk_q (axcl_proj1_rep Sg α β).

Definition axcl_proj2_rep (Sg : Signature) (α β : AxType Sg) :
    AxClMor Sg (α ×ax β) β :=
  {| axcl_term  := ax_snd (ax_var 0);
     axcl_typed := ax_ht_snd Sg [α ×ax β] (ax_var 0) α β
                     (ax_ht_var Sg [α ×ax β] 0 (α ×ax β) eq_refl); |}.

Definition axcl_proj2 (Sg : Signature) (α β : AxType Sg) :
    AxCl Sg ⟦ α ×ax β, β ⟧ :=
  mk_q (axcl_proj2_rep Sg α β).

Lemma axcl_pair_rep_typed (Sg : Signature) (γ α β : AxType Sg)
    (f : AxClMor Sg γ α) (g : AxClMor Sg γ β) :
    AxHasType Sg [γ] (ax_pair f.(axcl_term) g.(axcl_term)) (α ×ax β).
Proof.
  apply ax_ht_pair.
  - exact f.(axcl_typed).
  - exact g.(axcl_typed).
Qed.

Definition axcl_pair_rep (Sg : Signature) (γ α β : AxType Sg)
    (f : AxClMor Sg γ α) (g : AxClMor Sg γ β) : AxClMor Sg γ (α ×ax β) :=
  {| axcl_term  := ax_pair f.(axcl_term) g.(axcl_term);
     axcl_typed := axcl_pair_rep_typed Sg γ α β f g; |}.

Lemma axcl_pair_well_defined (Sg : Signature) (γ α β : AxType Sg)
    (f1 f2 : AxClMor Sg γ α) (g1 g2 : AxClMor Sg γ β) :
    AxClMor_eq Sg γ α f1 f2 ->
    AxClMor_eq Sg γ β g1 g2 ->
    AxClMor_eq Sg γ (α ×ax β)
      (axcl_pair_rep Sg γ α β f1 g1)
      (axcl_pair_rep Sg γ α β f2 g2).
Proof.
  unfold AxClMor_eq, axcl_pair_rep. simpl. intros Hf Hg.
  apply axeq_pair; assumption.
Qed.

Definition axcl_pair (Sg : Signature) (γ α β : AxType Sg)
    (f : AxCl Sg ⟦ γ, α ⟧) (g : AxCl Sg ⟦ γ, β ⟧) :
    AxCl Sg ⟦ γ, α ×ax β ⟧.
Proof.
  refine (exist _
            (fun h => exists f0 g0,
                proj1_sig f f0 /\ proj1_sig g g0 /\
                AxClMor_eq Sg γ (α ×ax β) (axcl_pair_rep Sg γ α β f0 g0) h)
            _).
  destruct f as [Sf [f0 Hf]]; destruct g as [Sg' [g0 Hg]]; simpl.
  exists (axcl_pair_rep Sg γ α β f0 g0).
  apply functional_extensionality. intro x.
  apply propositional_extensionality. split.
  - intros [f1 [g1 [Hf1 [Hg1 Hp]]]].
    rewrite Hf in Hf1. rewrite Hg in Hg1.
    unfold AxThEq_class_of in Hf1, Hg1.
    apply (AxClMor_eq_trans Sg γ (α ×ax β)
             (axcl_pair_rep Sg γ α β f0 g0)
             (axcl_pair_rep Sg γ α β f1 g1) x).
    + apply axcl_pair_well_defined; assumption.
    + exact Hp.
  - intro Hx.
    exists f0, g0. rewrite Hf, Hg. unfold AxThEq_class_of.
    repeat split.
    + apply AxClMor_eq_refl.
    + apply AxClMor_eq_refl.
    + exact Hx.
Defined.

Lemma axcl_pair_mk (Sg : Signature) (γ α β : AxType Sg)
    (f : AxClMor Sg γ α) (g : AxClMor Sg γ β) :
    axcl_pair Sg γ α β (mk_q f) (mk_q g) =
    mk_q (axcl_pair_rep Sg γ α β f g).
Proof.
  apply AxClMor_q_eq. simpl.
  apply functional_extensionality. intro x.
  apply propositional_extensionality. split.
  - intros [f0 [g0 [Hf0 [Hg0 Hp]]]].
    unfold AxThEq_class_of in Hf0, Hg0.
    apply (AxClMor_eq_trans Sg γ (α ×ax β)
             (axcl_pair_rep Sg γ α β f g)
             (axcl_pair_rep Sg γ α β f0 g0) x).
    + apply axcl_pair_well_defined; assumption.
    + exact Hp.
  - intro Hx.
    exists f, g. unfold AxThEq_class_of. repeat split.
    + apply AxClMor_eq_refl.
    + apply AxClMor_eq_refl.
    + exact Hx.
Qed.

(** Beta rule 1 for products: DISCHARGED. *)
Lemma axcl_bp_beta1 (Sg : Signature) (γ α β : AxType Sg)
    (f : AxCl Sg ⟦ γ, α ⟧) (g : AxCl Sg ⟦ γ, β ⟧) :
    axcl_comp Sg γ (α ×ax β) α (axcl_proj1 Sg α β) (axcl_pair Sg γ α β f g) = f.
Proof.
  destruct (mk_q_surj Sg γ α f) as [f0 Hf]. subst f.
  destruct (mk_q_surj Sg γ β g) as [g0 Hg]. subst g.
  unfold axcl_proj1.
  rewrite axcl_pair_mk.
  rewrite axcl_comp_mk.
  apply mk_q_eq_iff.
  unfold AxClMor_eq, axcl_comp_rep, axcl_proj1_rep, axcl_pair_rep. simpl.
  apply axeq_beta_fst with (β := β).
  - exact f0.(axcl_typed).
  - exact g0.(axcl_typed).
Qed.

(** Beta rule 2 for products: DISCHARGED. *)
Lemma axcl_bp_beta2 (Sg : Signature) (γ α β : AxType Sg)
    (f : AxCl Sg ⟦ γ, α ⟧) (g : AxCl Sg ⟦ γ, β ⟧) :
    axcl_comp Sg γ (α ×ax β) β (axcl_proj2 Sg α β) (axcl_pair Sg γ α β f g) = g.
Proof.
  destruct (mk_q_surj Sg γ α f) as [f0 Hf]. subst f.
  destruct (mk_q_surj Sg γ β g) as [g0 Hg]. subst g.
  unfold axcl_proj2.
  rewrite axcl_pair_mk.
  rewrite axcl_comp_mk.
  apply mk_q_eq_iff.
  unfold AxClMor_eq, axcl_comp_rep, axcl_proj2_rep, axcl_pair_rep. simpl.
  apply axeq_beta_snd with (α := α).
  - exact f0.(axcl_typed).
  - exact g0.(axcl_typed).
Qed.

(** Eta / uniqueness for products: DISCHARGED. *)
Lemma axcl_bp_uniq (Sg : Signature) (γ α β : AxType Sg)
    (h : AxCl Sg ⟦ γ, α ×ax β ⟧) :
    h = axcl_pair Sg γ α β
          (axcl_comp Sg γ (α ×ax β) α (axcl_proj1 Sg α β) h)
          (axcl_comp Sg γ (α ×ax β) β (axcl_proj2 Sg α β) h).
Proof.
  destruct (mk_q_surj Sg γ (α ×ax β) h) as [h0 Hh]. subst h.
  unfold axcl_proj1, axcl_proj2.
  rewrite !axcl_comp_mk.
  rewrite axcl_pair_mk.
  apply mk_q_eq_iff.
  unfold AxClMor_eq, axcl_comp_rep, axcl_proj1_rep, axcl_proj2_rep,
         axcl_pair_rep. simpl.
  apply axeq_sym.
  apply axeq_eta_prod. exact h0.(axcl_typed).
Qed.

Definition axcl_binary_product (Sg : Signature) (α β : AxType Sg) :
    @IsBinaryProduct (AxCl Sg) α β (α ×ax β).
Proof.
  apply Build_IsBinaryProduct with
    (bp_proj1 := axcl_proj1 Sg α β)
    (bp_proj2 := axcl_proj2 Sg α β)
    (bp_pair  := fun γ f g => axcl_pair Sg γ α β f g).
  - intros γ f g. exact (axcl_bp_beta1 Sg γ α β f g).
  - intros γ f g. exact (axcl_bp_beta2 Sg γ α β f g).
  - intros γ h.   exact (axcl_bp_uniq  Sg γ α β h).
Defined.

(* ================================================================== *)
(** ** Exponential object: ax_exp α β  (= β^α) *)
(* ================================================================== *)

Lemma axcl_eval_rep_typed (Sg : Signature) (α β : AxType Sg) :
    AxHasType Sg [(α ⇒ax β) ×ax α]
      (ax_ap (ax_fst (ax_var 0)) (ax_snd (ax_var 0))) β.
Proof.
  apply ax_ht_ap with α.
  - apply (ax_ht_fst Sg [(α ⇒ax β) ×ax α] (ax_var 0) (α ⇒ax β) α).
    apply ax_ht_var. reflexivity.
  - apply (ax_ht_snd Sg [(α ⇒ax β) ×ax α] (ax_var 0) (α ⇒ax β) α).
    apply ax_ht_var. reflexivity.
Qed.

Definition axcl_eval_rep (Sg : Signature) (α β : AxType Sg) :
    AxClMor Sg ((α ⇒ax β) ×ax α) β :=
  {| axcl_term  := ax_ap (ax_fst (ax_var 0)) (ax_snd (ax_var 0));
     axcl_typed := axcl_eval_rep_typed Sg α β; |}.

Definition axcl_eval (Sg : Signature) (α β : AxType Sg) :
    AxCl Sg ⟦ (α ⇒ax β) ×ax α, β ⟧ :=
  mk_q (axcl_eval_rep Sg α β).

Theorem axcl_curry_rep : forall (Sg : Signature) (γ α β : AxType Sg)
    (f : AxClMor Sg (γ ×ax α) β),
    AxClMor Sg γ (α ⇒ax β).
Proof.
  intros Sg γ α β f.
  refine {| axcl_term  := ax_lam (ax_subst [ax_pair (ax_var 1) (ax_var 0)] f.(axcl_term));
            axcl_typed := _ |}.
  apply ax_ht_lam.
  refine (ax_subst_preserves_type Sg [α; γ] [γ ×ax α]
            [ax_pair (ax_var 1) (ax_var 0)] _ f.(axcl_term) β f.(axcl_typed)).
  constructor.
  - apply ax_ht_pair.
    + apply ax_ht_var. reflexivity.
    + apply ax_ht_var. reflexivity.
  - constructor.
Defined.

Lemma axcl_curry_well_defined (Sg : Signature) (γ α β : AxType Sg)
    (f1 f2 : AxClMor Sg (γ ×ax α) β) :
    AxClMor_eq Sg (γ ×ax α) β f1 f2 ->
    AxClMor_eq Sg γ (α ⇒ax β) (axcl_curry_rep Sg γ α β f1) (axcl_curry_rep Sg γ α β f2).
Proof.
  unfold AxClMor_eq, axcl_curry_rep. simpl. intro Hf.
  apply axeq_lam.
  apply (ax_subst_cong Sg [] [α; γ] [γ ×ax α]
                       [ax_pair (ax_var 1) (ax_var 0)]
                       [ax_pair (ax_var 1) (ax_var 0)]
                       f1.(axcl_term) f2.(axcl_term) β).
  - constructor.
    + apply ax_ht_pair.
      * apply ax_ht_var. reflexivity.
      * apply ax_ht_var. reflexivity.
    + constructor.
  - constructor.
    + apply ax_ht_pair.
      * apply ax_ht_var. reflexivity.
      * apply ax_ht_var. reflexivity.
    + constructor.
  - intros i α_i s s' Hai Hsi Hsi'.
    destruct i as [|i].
    + simpl in Hai, Hsi, Hsi'.
      injection Hai as <-. injection Hsi as <-. injection Hsi' as <-.
      apply axeq_refl.
      apply ax_ht_pair; apply ax_ht_var; reflexivity.
    + destruct i; simpl in *; discriminate.
  - exact Hf.
Qed.

Definition axcl_curry (Sg : Signature) (γ α β : AxType Sg)
    (f : AxCl Sg ⟦ γ ×ax α, β ⟧) : AxCl Sg ⟦ γ, α ⇒ax β ⟧.
Proof.
  refine (exist _
            (fun h => exists f0,
                proj1_sig f f0 /\
                AxClMor_eq Sg γ (α ⇒ax β) (axcl_curry_rep Sg γ α β f0) h)
            _).
  destruct f as [Sf [f0 Hf]]; simpl.
  exists (axcl_curry_rep Sg γ α β f0).
  apply functional_extensionality. intro x.
  apply propositional_extensionality. split.
  - intros [f1 [Hf1 Hc]].
    rewrite Hf in Hf1. unfold AxThEq_class_of in Hf1.
    apply (AxClMor_eq_trans Sg γ (α ⇒ax β)
             (axcl_curry_rep Sg γ α β f0)
             (axcl_curry_rep Sg γ α β f1) x).
    + apply axcl_curry_well_defined. exact Hf1.
    + exact Hc.
  - intro Hx. exists f0. rewrite Hf. unfold AxThEq_class_of.
    split.
    + apply AxClMor_eq_refl.
    + exact Hx.
Defined.

Lemma axcl_curry_mk (Sg : Signature) (γ α β : AxType Sg)
    (f : AxClMor Sg (γ ×ax α) β) :
    axcl_curry Sg γ α β (mk_q f) = mk_q (axcl_curry_rep Sg γ α β f).
Proof.
  apply AxClMor_q_eq. simpl.
  apply functional_extensionality. intro x.
  apply propositional_extensionality. split.
  - intros [f0 [Hf0 Hc]].
    unfold AxThEq_class_of in Hf0.
    apply (AxClMor_eq_trans Sg γ (α ⇒ax β)
             (axcl_curry_rep Sg γ α β f)
             (axcl_curry_rep Sg γ α β f0) x).
    + apply axcl_curry_well_defined. exact Hf0.
    + exact Hc.
  - intro Hx. exists f. unfold AxThEq_class_of.
    split.
    + apply AxClMor_eq_refl.
    + exact Hx.
Qed.

(** Exponential β/η.  DISCHARGED in Task A.1b on top of the quotient
    framework: each follows from a multi-step AxThEq derivation
    composed of [axeq_beta_lam] / [axeq_eta_lam] / [axeq_beta_fst] /
    [axeq_beta_snd] / [axeq_eta_prod] congruence steps and
    [ax_subst_cong] + [ax_subst_comp] bookkeeping.  The quotient
    framework reduces the goal to a single AxThEq derivation between
    representatives, which we then walk through term-by-term. *)

(** Helper: typing of [ax_subst [ax_fst (ax_var 0)] K] for a
    representative-level [γ]-context term [K] of type [α ⇒ax β]. *)
Lemma ax_subst_proj1_typed (Sg : Signature) (γ α β : AxType Sg) (K : AxTerm Sg) :
    AxHasType Sg [γ] K (α ⇒ax β) ->
    AxHasType Sg [γ ×ax α] (ax_subst [ax_fst (ax_var 0)] K) (α ⇒ax β).
Proof.
  intro HK.
  apply (ax_subst_preserves_type Sg [γ ×ax α] [γ] [ax_fst (ax_var 0)]).
  - constructor.
    + apply (ax_ht_fst Sg [γ ×ax α] (ax_var 0) γ α).
      apply ax_ht_var. reflexivity.
    + constructor.
  - exact HK.
Qed.

(** Computational normalisation of [ax_subst [ax_fst (ax_var 0)] (axcl_curry_rep f0).term].
    The substitution pushes under the [ax_lam] and merges with the inner pair-substitution
    via [ax_subst_comp], yielding a single substitution. *)
Lemma axcl_curry_proj1_subst (Sg : Signature) (γ α β : AxType Sg)
    (f0 : AxClMor Sg (γ ×ax α) β) :
    ax_subst [ax_fst (ax_var 0)] (axcl_curry_rep Sg γ α β f0).(axcl_term) =
    ax_lam (ax_subst [ax_var 0; ax_fst (ax_var 1)]
                     (ax_subst [ax_pair (ax_var 1) (ax_var 0)] f0.(axcl_term))).
Proof.
  unfold axcl_curry_rep. simpl.
  reflexivity.
Qed.

(** Inner subst-comp simplification: under the [ax_lam], the two stacked
    substitutions collapse into one with body
    [ax_pair (ax_fst (ax_var 1)) (ax_var 0)]. *)
Lemma axcl_curry_proj1_normalize (Sg : Signature) (γ α β : AxType Sg)
    (f0 : AxClMor Sg (γ ×ax α) β) :
    ax_subst [ax_var 0; ax_fst (ax_var 1)]
             (ax_subst [ax_pair (ax_var 1) (ax_var 0)] f0.(axcl_term)) =
    ax_subst [ax_pair (ax_fst (ax_var 1)) (ax_var 0)] f0.(axcl_term).
Proof.
  (* Note: f0.term is typed in [γ ×ax α] (length 1).  But sub2 here is
     [ax_pair (ax_var 1) (ax_var 0)] (length 1), substituting into a term
     typed in [γ ×ax α].  However, the term we're substituting INTO is
     ax_subst [ax_pair (ax_var 1) (ax_var 0)] f0.term = body of curry's lambda,
     typed in [α; γ].  So we need ax_subst_comp with Γ = [γ ×ax α].
     Wait — re-examining: in ax_subst sub1 (ax_subst sub2 M),
     ax_subst_comp says ax_subst sub1 (ax_subst sub2 M) = ax_subst (map (subst sub1) sub2) M
     where sub2 substitutes into M's typing context.  M = f0.term : β in [γ ×ax α],
     length 1.  sub2 = [ax_pair (ax_var 1) (ax_var 0)] of length 1.  Good. *)
  rewrite (ax_subst_comp Sg [γ ×ax α]
             [ax_var 0; ax_fst (ax_var 1)]
             [ax_pair (ax_var 1) (ax_var 0)]
             f0.(axcl_term) β eq_refl f0.(axcl_typed)).
  simpl. reflexivity.
Qed.

Lemma axcl_exp_beta : forall (Sg : Signature) (γ α β : AxType Sg)
    (f : AxCl Sg ⟦ γ ×ax α, β ⟧),
    axcl_comp Sg (γ ×ax α) ((α ⇒ax β) ×ax α) β
      (axcl_eval Sg α β)
      (axcl_pair Sg (γ ×ax α) (α ⇒ax β) α
        (axcl_curry Sg γ α β f ∘ axcl_proj1 Sg γ α)
        (axcl_proj2 Sg γ α)) = f.
Proof.
  intros Sg γ α β f.
  destruct (mk_q_surj Sg (γ ×ax α) β f) as [f0 Hf]. subst f.
  rewrite axcl_curry_mk.
  unfold axcl_proj1, axcl_proj2, axcl_eval.
  change (@comp (AxCl Sg) ?A ?B ?C) with (axcl_comp Sg A B C).
  rewrite axcl_comp_mk.
  rewrite axcl_pair_mk.
  rewrite axcl_comp_mk.
  apply mk_q_eq_iff.
  unfold AxClMor_eq, axcl_comp_rep, axcl_pair_rep, axcl_proj1_rep,
         axcl_proj2_rep, axcl_eval_rep. simpl.
  set (Cterm := (axcl_curry_rep Sg γ α β f0).(axcl_term)).
  set (P := ax_subst [ax_fst (ax_var 0)] Cterm).
  assert (HP : AxHasType Sg [γ ×ax α] P (α ⇒ax β)).
  { unfold P. apply ax_subst_proj1_typed.
    exact (axcl_curry_rep Sg γ α β f0).(axcl_typed). }
  assert (Hsnd : AxHasType Sg [γ ×ax α] (ax_snd (ax_var 0)) α).
  { apply (ax_ht_snd Sg [γ ×ax α] (ax_var 0) γ α).
    apply ax_ht_var. reflexivity. }
  (* Step 1: beta_fst/beta_snd reduce ax_fst/ax_snd of pair P x. *)
  apply (axeq_trans Sg [] [γ ×ax α]
           (ax_ap (ax_fst (ax_pair P (ax_snd (ax_var 0))))
                  (ax_snd (ax_pair P (ax_snd (ax_var 0)))))
           (ax_ap P (ax_snd (ax_var 0)))
           f0.(axcl_term) β).
  { apply axeq_ap with (α := α).
    - apply (axeq_beta_fst Sg [] [γ ×ax α] P (ax_snd (ax_var 0))
              (α ⇒ax β) α HP Hsnd).
    - apply (axeq_beta_snd Sg [] [γ ×ax α] P (ax_snd (ax_var 0))
              (α ⇒ax β) α HP Hsnd). }
  (* Step 2: P = ax_lam (ax_subst [...] (ax_subst [...] f0.term)) by definitional
     unfolding of ax_subst on ax_lam.  Then the inner double-subst collapses to
     ax_subst [ax_pair (ax_fst (ax_var 1)) (ax_var 0)] f0.term via ax_subst_comp. *)
  unfold P, Cterm.
  rewrite axcl_curry_proj1_subst.
  rewrite (axcl_curry_proj1_normalize Sg γ α β f0).
  (* Goal:
       AxThEq Sg [] [γ ×ax α]
         (ax_ap (ax_lam (ax_subst [ax_pair (ax_fst (ax_var 1)) (ax_var 0)] f0.term))
                (ax_snd (ax_var 0)))
         f0.term β. *)
  set (S2 := [ax_pair (ax_fst (ax_var 1)) (ax_var 0)] : list (AxTerm Sg)).
  assert (HS2 : List.Forall2 (AxHasType Sg [α; γ ×ax α]) S2 [γ ×ax α]).
  { unfold S2. constructor.
    - apply ax_ht_pair.
      + apply (ax_ht_fst Sg [α; γ ×ax α] (ax_var 1) γ α).
        apply ax_ht_var. reflexivity.
      + apply ax_ht_var. reflexivity.
    - constructor. }
  assert (HQbody : AxHasType Sg [α; γ ×ax α] (ax_subst S2 f0.(axcl_term)) β).
  { apply (ax_subst_preserves_type Sg [α; γ ×ax α] [γ ×ax α] S2 HS2).
    exact f0.(axcl_typed). }
  (* Step 3: beta_lam *)
  apply (axeq_trans Sg [] [γ ×ax α]
           (ax_ap (ax_lam (ax_subst S2 f0.(axcl_term))) (ax_snd (ax_var 0)))
           (ax_subst (ax_snd (ax_var 0) :: ax_id_sub Sg 1)
                     (ax_subst S2 f0.(axcl_term)))
           f0.(axcl_term) β).
  { apply axeq_beta_lam with (α := α).
    - exact HQbody.
    - exact Hsnd. }
  (* Step 4: ax_subst_comp collapses the two stacked substitutions. *)
  rewrite (ax_subst_comp Sg [γ ×ax α]
             (ax_snd (ax_var 0) :: ax_id_sub Sg 1) S2 f0.(axcl_term) β eq_refl
             f0.(axcl_typed)).
  cbn [List.map ax_subst List.nth_error].
  (* Goal: AxThEq Sg [] [γ ×ax α]
       (ax_subst [ax_pair (ax_fst (ax_var 0)) (ax_snd (ax_var 0))] f0.term)
       f0.term β. *)
  apply (axeq_trans Sg [] [γ ×ax α]
           (ax_subst [ax_pair (ax_fst (ax_var 0)) (ax_snd (ax_var 0))] f0.(axcl_term))
           (ax_subst [ax_var 0] f0.(axcl_term))
           f0.(axcl_term) β).
  { (* Step 5: ax_subst_cong with axeq_eta_prod on the substitution element. *)
    apply (ax_subst_cong Sg [] [γ ×ax α] [γ ×ax α]
             [ax_pair (ax_fst (ax_var 0)) (ax_snd (ax_var 0))]
             [ax_var 0]
             f0.(axcl_term) f0.(axcl_term) β).
    - constructor.
      + apply ax_ht_pair.
        * apply (ax_ht_fst Sg [γ ×ax α] (ax_var 0) γ α).
          apply ax_ht_var. reflexivity.
        * apply (ax_ht_snd Sg [γ ×ax α] (ax_var 0) γ α).
          apply ax_ht_var. reflexivity.
      + constructor.
    - constructor.
      + apply ax_ht_var. reflexivity.
      + constructor.
    - intros i α_i s s' Hai Hsi Hsi'.
      destruct i as [|i].
      + simpl in Hai, Hsi, Hsi'.
        injection Hai as <-. injection Hsi as <-. injection Hsi' as <-.
        apply (axeq_eta_prod Sg [] [γ ×ax α] (ax_var 0) γ α).
        apply ax_ht_var. reflexivity.
      + destruct i; simpl in *; discriminate.
    - apply axeq_refl. exact f0.(axcl_typed). }
  (* Step 6: ax_subst [ax_var 0] f0.term = f0.term via ax_subst_id. *)
  change (cons (ax_var 0) nil)
    with (ax_id_sub Sg (length (cons (γ ×ax α) (@nil (AxType Sg))))).
  rewrite (ax_subst_id Sg [γ ×ax α] f0.(axcl_term) β f0.(axcl_typed)).
  apply axeq_refl. exact f0.(axcl_typed).
Qed.

Lemma axcl_exp_eta : forall (Sg : Signature) (γ α β : AxType Sg)
    (g : AxCl Sg ⟦ γ, α ⇒ax β ⟧),
    axcl_curry Sg γ α β
      (axcl_comp Sg (γ ×ax α) ((α ⇒ax β) ×ax α) β
        (axcl_eval Sg α β)
        (axcl_pair Sg (γ ×ax α) (α ⇒ax β) α
          (g ∘ axcl_proj1 Sg γ α)
          (axcl_proj2 Sg γ α))) = g.
Proof.
  intros Sg γ α β g.
  destruct (mk_q_surj Sg γ (α ⇒ax β) g) as [g0 Hg]. subst g.
  unfold axcl_proj1, axcl_proj2, axcl_eval.
  change (@comp (AxCl Sg) ?A ?B ?C) with (axcl_comp Sg A B C).
  rewrite axcl_comp_mk.
  rewrite axcl_pair_mk.
  rewrite axcl_comp_mk.
  rewrite axcl_curry_mk.
  apply mk_q_eq_iff.
  unfold AxClMor_eq, axcl_curry_rep, axcl_comp_rep, axcl_pair_rep,
         axcl_proj1_rep, axcl_proj2_rep, axcl_eval_rep. simpl.
  (* Goal: AxThEq Sg [] [γ]
       (ax_lam (ax_subst [ax_pair (ax_var 1) (ax_var 0)]
                 (ax_ap (ax_fst (ax_pair (ax_subst [ax_fst (ax_var 0)] g0.term)
                                          (ax_snd (ax_var 0))))
                        (ax_snd (ax_pair (ax_subst [ax_fst (ax_var 0)] g0.term)
                                          (ax_snd (ax_var 0)))))))
       g0.term
       (α ⇒ax β). *)
  set (S' := ax_subst [ax_fst (ax_var 0)] g0.(axcl_term)).
  assert (HS' : AxHasType Sg [γ ×ax α] S' (α ⇒ax β)).
  { unfold S'.
    apply (ax_subst_preserves_type Sg [γ ×ax α] [γ] [ax_fst (ax_var 0)]).
    - constructor.
      + apply (ax_ht_fst Sg [γ ×ax α] (ax_var 0) γ α).
        apply ax_ht_var. reflexivity.
      + constructor.
    - exact g0.(axcl_typed). }
  assert (Hsnd : AxHasType Sg [γ ×ax α] (ax_snd (ax_var 0)) α).
  { apply (ax_ht_snd Sg [γ ×ax α] (ax_var 0) γ α).
    apply ax_ht_var. reflexivity. }
  (* The inner ax_subst [ax_pair (ax_var 1) (ax_var 0)] R distributes through
     ax_ap, ax_fst, ax_snd, ax_pair, var.  We use lemma-form rewriting via cbn. *)
  cbn [ax_subst].
  change (List.nth_error [ax_pair (ax_var 1) (ax_var 0)] 0)
    with (Some (ax_pair (@ax_var Sg 1) (@ax_var Sg 0))).
  cbv beta iota.
  (* Goal now (with sharing of subterms):
       AxThEq Sg [] [γ]
         (ax_lam
           (ax_ap
             (ax_fst (ax_pair (ax_subst [ax_pair (ax_var 1) (ax_var 0)] S')
                              (ax_snd (ax_pair (ax_var 1) (ax_var 0)))))
             (ax_snd (ax_pair (ax_subst [ax_pair (ax_var 1) (ax_var 0)] S')
                              (ax_snd (ax_pair (ax_var 1) (ax_var 0)))))))
         g0.term
         (α ⇒ax β). *)
  (* Let T = ax_subst [ax_pair (ax_var 1) (ax_var 0)] S'.
     By ax_subst_comp, T = ax_subst [ax_fst (ax_pair (ax_var 1) (ax_var 0))] g0.term. *)
  set (T := ax_subst [ax_pair (@ax_var Sg 1) (@ax_var Sg 0)] S').
  (* Type of T: in context [α; γ], T : α ⇒ax β. *)
  assert (HT : AxHasType Sg [α; γ] T (α ⇒ax β)).
  { unfold T.
    apply (ax_subst_preserves_type Sg [α; γ] [γ ×ax α] [ax_pair (ax_var 1) (ax_var 0)]).
    - constructor.
      + apply ax_ht_pair; apply ax_ht_var; reflexivity.
      + constructor.
    - exact HS'. }
  assert (HsndPair : AxHasType Sg [α; γ]
            (ax_snd (ax_pair (@ax_var Sg 1) (@ax_var Sg 0))) α).
  { apply (ax_ht_snd Sg [α; γ] (ax_pair (ax_var 1) (ax_var 0)) γ α).
    apply ax_ht_pair; apply ax_ht_var; reflexivity. }
  (* Step 1 (under the lambda): reduce
       ax_ap (ax_fst (ax_pair T (ax_snd (pair v1 v0))))
             (ax_snd (ax_pair T (ax_snd (pair v1 v0))))
     to ax_ap T (ax_snd (ax_pair (ax_var 1) (ax_var 0)))
     via beta_fst/beta_snd. *)
  apply (axeq_trans Sg [] [γ]
           (ax_lam (ax_ap
              (ax_fst (ax_pair T (ax_snd (ax_pair (ax_var 1) (ax_var 0)))))
              (ax_snd (ax_pair T (ax_snd (ax_pair (ax_var 1) (ax_var 0)))))))
           (ax_lam (ax_ap T (ax_snd (ax_pair (@ax_var Sg 1) (@ax_var Sg 0)))))
           g0.(axcl_term) (α ⇒ax β)).
  { apply axeq_lam.
    apply axeq_ap with (α := α).
    - apply (axeq_beta_fst Sg [] [α; γ] T
              (ax_snd (ax_pair (ax_var 1) (ax_var 0)))
              (α ⇒ax β) α HT HsndPair).
    - apply (axeq_beta_snd Sg [] [α; γ] T
              (ax_snd (ax_pair (ax_var 1) (ax_var 0)))
              (α ⇒ax β) α HT HsndPair). }
  (* Step 2 (under lambda): reduce ax_snd (ax_pair (ax_var 1) (ax_var 0)) to ax_var 0
     via beta_snd. *)
  assert (Hv0 : AxHasType Sg [α; γ] (@ax_var Sg 0) α).
  { apply ax_ht_var. reflexivity. }
  assert (Hv1 : AxHasType Sg [α; γ] (@ax_var Sg 1) γ).
  { apply ax_ht_var. reflexivity. }
  apply (axeq_trans Sg [] [γ]
           (ax_lam (ax_ap T (ax_snd (ax_pair (@ax_var Sg 1) (@ax_var Sg 0)))))
           (ax_lam (ax_ap T (@ax_var Sg 0)))
           g0.(axcl_term) (α ⇒ax β)).
  { apply axeq_lam.
    apply axeq_ap with (α := α).
    - apply axeq_refl. exact HT.
    - apply (axeq_beta_snd Sg [] [α; γ] (ax_var 1) (ax_var 0) γ α Hv1 Hv0). }
  (* Step 3: rewrite T = ax_subst [ax_fst (ax_pair (ax_var 1) (ax_var 0))] g0.term
     via ax_subst_comp.  Then reduce ax_fst (ax_pair (ax_var 1) (ax_var 0)) to ax_var 1
     via ax_subst_cong + axeq_beta_fst. *)
  unfold T, S'.
  rewrite (ax_subst_comp Sg [γ]
             [ax_pair (@ax_var Sg 1) (@ax_var Sg 0)]
             [ax_fst (@ax_var Sg 0)]
             g0.(axcl_term) (α ⇒ax β) eq_refl g0.(axcl_typed)).
  cbn [List.map ax_subst List.nth_error].
  (* Goal: AxThEq Sg [] [γ]
       (ax_lam (ax_ap
          (ax_subst [ax_fst (ax_pair (ax_var 1) (ax_var 0))] g0.term)
          (ax_var 0)))
       g0.term (α ⇒ax β). *)
  apply (axeq_trans Sg [] [γ]
           (ax_lam (ax_ap
              (ax_subst [ax_fst (ax_pair (@ax_var Sg 1) (@ax_var Sg 0))] g0.(axcl_term))
              (@ax_var Sg 0)))
           (ax_lam (ax_ap (ax_subst [@ax_var Sg 1] g0.(axcl_term)) (@ax_var Sg 0)))
           g0.(axcl_term) (α ⇒ax β)).
  { apply axeq_lam.
    apply axeq_ap with (α := α).
    - apply (ax_subst_cong Sg [] [α; γ] [γ]
               [ax_fst (ax_pair (ax_var 1) (ax_var 0))]
               [ax_var 1]
               g0.(axcl_term) g0.(axcl_term) (α ⇒ax β)).
      + constructor.
        * apply (ax_ht_fst Sg [α; γ] (ax_pair (ax_var 1) (ax_var 0)) γ α).
          apply ax_ht_pair; apply ax_ht_var; reflexivity.
        * constructor.
      + constructor.
        * apply ax_ht_var. reflexivity.
        * constructor.
      + intros i α_i s s' Hai Hsi Hsi'.
        destruct i as [|i].
        * simpl in Hai, Hsi, Hsi'.
          injection Hai as <-. injection Hsi as <-. injection Hsi' as <-.
          apply (axeq_beta_fst Sg [] [α; γ] (ax_var 1) (ax_var 0) γ α Hv1 Hv0).
        * destruct i; simpl in *; discriminate.
      + apply axeq_refl. exact g0.(axcl_typed).
    - apply axeq_refl. exact Hv0. }
  (* Step 4: axeq_eta_lam.  For Γ = [γ], length Γ = 1, ax_id_sub Sg 1 = [ax_var 0].
     map (λt. ax_subst [ax_var 1] t) [ax_var 0] = [ax_subst [ax_var 1] (ax_var 0)] = [ax_var 1].
     So axeq_eta_lam says
       ax_lam (ax_ap (ax_subst [ax_var 1] g0.term) (ax_var 0)) ~ g0.term. *)
  pose proof (axeq_eta_lam Sg [] [γ] g0.(axcl_term) α β g0.(axcl_typed)) as Heta.
  cbn [List.map ax_id_sub List.seq ax_subst List.length List.nth_error] in Heta.
  exact Heta.
Qed.

(* ================================================================== *)
(** ** Finite products in AxCl *)
(* ================================================================== *)

Definition axcl_has_binary_products (Sg : Signature) : HasBinaryProducts (AxCl Sg).
Proof.
  apply Build_HasBinaryProducts with (prod_obj := fun α β : AxType Sg => α ×ax β).
  exact (axcl_binary_product Sg).
Defined.

Definition axcl_finite_products (Sg : Signature) : HasFiniteProducts (AxCl Sg).
Proof.
  refine {|
    fp_terminal := existT (fun T => @IsTerminal (AxCl Sg) T) ax_unit (axcl_is_terminal Sg);
    fp_binary   := axcl_has_binary_products Sg;
  |}.
Defined.

(* ================================================================== *)
(** ** AxCl is cartesian closed *)
(* ================================================================== *)

Definition axcl_exp_obj_fn (Sg : Signature) (α β : AxType Sg) : AxType Sg :=
  α ⇒ax β.

Definition axcl_is_exp (Sg : Signature) (α β : AxType Sg) :
    IsExponential (axcl_has_binary_products Sg) α β (α ⇒ax β).
Proof.
  apply Build_IsExponential with
    (exp_eval  := axcl_eval Sg α β)
    (exp_curry := fun X f => axcl_curry Sg X α β f).
  - intros X f.
    unfold prod_map.
    cbn [prod_bp bp_pair bp_proj1 bp_proj2].
    rewrite (AxCl Sg).(id_left).
    exact (axcl_exp_beta Sg X α β f).
  - intros X g.
    unfold prod_map.
    cbn [prod_bp bp_pair bp_proj1 bp_proj2].
    rewrite (AxCl Sg).(id_left).
    exact (axcl_exp_eta Sg X α β g).
Defined.

Definition axcl_has_exponentials (Sg : Signature) :
    HasExponentials (AxCl Sg) (axcl_has_binary_products Sg).
Proof.
  apply Build_HasExponentials with (exp_obj := axcl_exp_obj_fn Sg).
  exact (axcl_is_exp Sg).
Defined.

Definition axcl_ccc (Sg : Signature) : IsCartesianClosed (AxCl Sg).
Proof.
  exact {|
    ccc_fp  := axcl_finite_products Sg;
    ccc_exp := axcl_has_exponentials Sg;
  |}.
Defined.
