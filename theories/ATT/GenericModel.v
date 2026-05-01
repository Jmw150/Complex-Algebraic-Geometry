(** * ATT/GenericModel.v
    The generic model G of a theory Th in its classifying category Cl(Sg).

    The generic model is defined by:
      [α]_G  :=  [α]   (the one-element list, object of Cl(Sg))
      [f]_G  :=  the morphism (dom f → cod f) given by [x₁:α₁,...,xₙ:αₙ | f(x₁,...,xₙ)]

    This is a model of Sg (the signature) in Cl(Sg) with finite products.
    It satisfies all axioms of Th because the morphism equality in the quotient
    Cl(Th) identifies provably equal term tuples.

    Proposition: for any proved equation Th ⊢ Γ ⊢ t = t' : τ, the interpretations
    [Γ ⊢ t]_G and [Γ ⊢ t']_G coincide in Cl(Th). *)

Require Import CAG.ATT.Signature.
Require Import CAG.ATT.Syntax.
Require Import CAG.ATT.Theory.
Require Import CAG.ATT.Model.
Require Import CAG.ATT.ClassifyingCategory.
Require Import CAG.Category.Core.
Require Import CAG.Category.Products.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Logic.ProofIrrelevance.
Import ListNotations.

Set Universe Polymorphism.
Open Scope cat_scope.

(** ** The generic model on Cl(Sg) *)

(** The sort α is sent to the singleton list [α]. *)
Definition G_ty (Sg : Signature) (α : Sg.(sg_ty)) : (Cl Sg).(Ob) := [α].

(** A function symbol f with domain [α₁,...,αₙ] and codomain β is sent to
    the morphism [α₁,...,αₙ] → [β] given by the term f(x₀,...,x_{n-1})
    in the canonical context [α₁,...,αₙ]. *)

Definition G_fun_term (Sg : Signature) (f : Sg.(sg_fun)) : Term Sg :=
  t_app f (List.map t_var (List.seq 0 (length (Sg.(sg_dom) f)))).

Lemma G_fun_term_typed (Sg : Signature) (f : Sg.(sg_fun)) :
    HasType Sg (Sg.(sg_dom) f) (G_fun_term Sg f) (Sg.(sg_cod) f).
Proof.
  unfold G_fun_term.
  apply ht_app.
  (* Need: Forall2 (HasType Sg (sg_dom f)) (map t_var (seq 0 n)) (sg_dom f) *)
  apply id_vars_typed_ok.
Qed.

(** Helper: fp_prod of singleton lists is the original list. *)
Lemma fp_prod_singleton_list (Sg : Signature) (xs : list Sg.(sg_ty)) :
    fp_prod (cl_finite_products Sg) (List.map (fun α => [α]) xs) = xs.
Proof.
  induction xs as [| α xs IH].
  - reflexivity.
  - destruct xs as [| β xs'].
    + reflexivity.
    + (* simpl would unfold map to [β]::map f xs', breaking rewrite IH.
         Instead use change to expose the IH subterm directly. *)
      change ([α] ++ fp_prod (cl_finite_products Sg)
                              (List.map (fun a => [a]) (β :: xs')) = α :: β :: xs').
      rewrite IH. reflexivity.
Qed.

(** The morphism [dom f → cod f] representing f in Cl(Sg). *)
Definition G_fun (Sg : Signature) (f : Sg.(sg_fun)) :
    Cl Sg ⟦ Sg.(sg_dom) f, [Sg.(sg_cod) f] ⟧ :=
  {| clmor_terms := [G_fun_term Sg f];
     clmor_typed := Forall2_cons _ _ (G_fun_term_typed Sg f) (Forall2_nil _) |}.

(** ** The generic model record *)

(** We state the generic model as a [Model] of the signature (ignoring axioms
    for now — axiom satisfaction follows in the quotient Cl(Th)).  *)

(** mod_fun for the generic model: defined separately so the rewrite is in
    a goal with a concrete type. *)
Definition GenericModel_mod_fun (Sg : Signature) (f : Sg.(sg_fun)) :
    Cl Sg ⟦ fp_prod (cl_finite_products Sg)
                    (List.map (fun α => [α]) (Sg.(sg_dom) f)),
             [Sg.(sg_cod) f] ⟧.
Proof.
  rewrite fp_prod_singleton_list.
  exact (G_fun Sg f).
Defined.

Definition GenericModel (Sg : Signature) :
    Model {| th_sig := Sg; th_ax := [] |}
          (Cl Sg)
          (cl_finite_products Sg).
Proof.
  refine (@Build_Model
    {| th_sig := Sg; th_ax := [] |}
    (Cl Sg)
    (cl_finite_products Sg)
    (@Build_ModelData
       {| th_sig := Sg; th_ax := [] |}
       (Cl Sg)
       (cl_finite_products Sg)
       (fun α : Sg.(sg_ty) => [α])
       (GenericModel_mod_fun Sg))
    _).
  (* mod_ax: vacuous since the axiom list is empty. *)
  intros a Hin. simpl in Hin. destruct Hin.
Defined.

(** ** Interpretation lemma (Proposition 1.1)

    For any proved equation Γ ⊢ t = t' : τ in Th,
    the interpretations [t]_G and [t']_G are equal as morphisms in Cl(Th).

    Proof idea:
    By induction on the derivation of ThEq, checking each rule.
    The key case is axiom application: if Th ⊢ ax : s = s' and sub instantiates
    the axiom variables, then [sub(s)]_G = [sub(s')]_G by the quotient equality
    in Cl(Th). *)

Theorem interpretation_lemma (Sg : Signature) (ax : list (TheoryAxiom Sg))
    (Γ : list Sg.(sg_ty)) (t t' : Term Sg) (τ : Sg.(sg_ty))
    (Ht  : HasType Sg Γ t  τ)
    (Ht' : HasType Sg Γ t' τ) :
    ThEq Sg ax Γ t t' τ ->
    ClMor_theq {| th_sig := Sg; th_ax := ax |}
      Γ [τ]
      {| clmor_terms := [t];
         clmor_typed := Forall2_cons _ _ Ht (Forall2_nil _) |}
      {| clmor_terms := [t'];
         clmor_typed := Forall2_cons _ _ Ht' (Forall2_nil _) |}.
Proof.
  intro Heq.
  unfold ClMor_theq. simpl.
  intros i t1 t2 τ0 H1 H2 H3.
  destruct i as [| i'].
  - simpl in H1, H2, H3.
    injection H1 as <-. injection H2 as <-. injection H3 as <-.
    exact Heq.
  - assert (Hnil : List.nth_error [t] (S i') = None).
    { apply List.nth_error_None. simpl. lia. }
    rewrite Hnil in H1. discriminate H1.
Qed.

(* ================================================================== *)
(** ** L.3 — The generic model on the QUOTIENT [ClTh Th]               *)
(*                                                                     *)
(*  We now build [GenericModelTh : Model Th (ClTh Th)] using the        *)
(*  finite-products-on-quotient structure built in                     *)
(*  [ClassifyingCategory.v].  This is the model required by the        *)
(*  completeness proof.                                                *)
(* ================================================================== *)

(** Helper: [fp_prod] of singleton lists in the quotient category, as
    an iterated [α ++ β], collapses to the original list.  Proof is
    structurally identical to [fp_prod_singleton_list] for [Cl Sg]. *)
Lemma fp_prod_singleton_list_th (Th : Theory)
    (xs : list Th.(th_sig).(sg_ty)) :
    fp_prod (clth_finite_products Th)
            (List.map (fun α => [α]) xs) = xs.
Proof.
  induction xs as [| α xs IH].
  - reflexivity.
  - destruct xs as [| β xs'].
    + reflexivity.
    + change ([α] ++ fp_prod (clth_finite_products Th)
                              (List.map (fun a => [a]) (β :: xs')) = α :: β :: xs').
      rewrite IH. reflexivity.
Qed.

(** [md_fun] for the Th-version of the generic model: the morphism
    representing function symbol [f] is the quotient class of the
    singleton-term ClMor [G_fun Sg f]. *)
Definition GenericModelTh_mod_fun (Th : Theory) (f : Th.(th_sig).(sg_fun)) :
    ClTh Th ⟦ fp_prod (clth_finite_products Th)
                       (List.map (fun α : Th.(th_sig).(sg_ty) => [α])
                                 (Th.(th_sig).(sg_dom) f)),
              [Th.(th_sig).(sg_cod) f] ⟧.
Proof.
  rewrite fp_prod_singleton_list_th.
  exact (clth_mk_q (G_fun Th.(th_sig) f)).
Defined.

(** [ModelData] for the Th-version of the generic model. *)
Definition GenericModelTh_data (Th : Theory) :
    ModelData Th (ClTh Th) (clth_finite_products Th) :=
  {| md_ty  := fun α : Th.(th_sig).(sg_ty) =>
                 (cons α nil : (ClTh Th).(Ob));
     md_fun := GenericModelTh_mod_fun Th |}.

(* ================================================================== *)
(** ** Term-to-quotient-morphism lifting                               *)
(*                                                                     *)
(*  [term_to_clmor] sends a typed term [Γ ⊢ t : τ] to the singleton    *)
(*  ClMor in [ClTh Th] from Γ to [τ].                                  *)
(* ================================================================== *)

Definition term_to_clmor (Th : Theory)
    (Γ : list Th.(th_sig).(sg_ty)) (τ : Th.(th_sig).(sg_ty))
    (t : Term Th.(th_sig)) (Ht : HasType Th.(th_sig) Γ t τ) :
    ClMor Th.(th_sig) Γ [τ] :=
  {| clmor_terms := [t];
     clmor_typed := Forall2_cons _ _ Ht (Forall2_nil _) |}.

(** A term-to-quotient-morphism, as a single ClMor_q. *)
Definition term_to_clmor_q (Th : Theory)
    (Γ : list Th.(th_sig).(sg_ty)) (τ : Th.(th_sig).(sg_ty))
    (t : Term Th.(th_sig)) (Ht : HasType Th.(th_sig) Γ t τ) :
    ClTh Th ⟦ Γ, [τ] ⟧ :=
  clth_mk_q (term_to_clmor Th Γ τ t Ht).

(** Transport a [ClMor_q]-typed morphism from domain Γ to the
    domain [fp_prod (clth_finite_products Th) (map (fun α => [α]) Γ)]
    by [eq_rect] along [fp_prod_singleton_list_th]. *)
Definition transport_clmor_dom (Th : Theory)
    (Γ : list Th.(th_sig).(sg_ty)) (τ : Th.(th_sig).(sg_ty))
    (m : ClTh Th ⟦ Γ, [τ] ⟧) :
    ClTh Th ⟦ fp_prod (clth_finite_products Th)
                       (List.map (fun α : Th.(th_sig).(sg_ty) => [α]) Γ),
              [τ] ⟧ :=
  eq_rect_r (fun X => ClTh Th ⟦ X, [τ] ⟧) m
            (fp_prod_singleton_list_th Th Γ).

(* ================================================================== *)
(** ** L.3 residual — Interpretation lemma scaffolding                 *)
(*                                                                     *)
(*  Below is a SCAFFOLD for the interpretation lemma:                  *)
(*    interp_term_data GenericModelTh_data Γ t τ Ht                    *)
(*      = transport_clmor_dom Th Γ τ (term_to_clmor_q Th Γ τ t Ht).    *)
(*                                                                     *)
(*  The variable case can be discharged via [interp_term_data_var] +   *)
(*  an induction on Γ characterising [context_proj] of                 *)
(*  [clth_finite_products Th] applied to a singleton-mapped list.      *)
(*                                                                     *)
(*  The application case folds [interp_term_data_app_explicit] +       *)
(*  composition reduction via [clth_comp_mk] / [clth_pair_mk].         *)
(*                                                                     *)
(*  γ R6 NOTE: The full proof needs ~150-300 lines of careful          *)
(*  dependent-rewrite work bridging [eq_rect] over                     *)
(*  [fp_prod_singleton_list_th] with [context_proj_clth].  The         *)
(*  scaffolding here records the precise statement (so a future        *)
(*  round can drop in the proof) but does not discharge the proof —    *)
(*  per project policy "clean PARTIAL > broken WIP".                   *)
(*                                                                     *)
(*  α R6 PROGRESS (Strategy (b)): The canonical-form lemma              *)
(*  [transport_clmor_dom_canonical] makes the [eq_rect_r] commute        *)
(*  with the quotient projection [clth_mk_q].  Combined with             *)
(*  [context_proj_singleton_terms] (which characterises [context_proj]   *)
(*  on a singleton-mapped list as a [clth_mk_q] of a specific            *)
(*  iterated-projection morphism whose underlying [clmor_terms] is      *)
(*  [[t_var n]]), the var case of the interpretation lemma reduces      *)
(*  to a single-component [ClMor_theq]-refl.  See below.                *)
(* ================================================================== *)

(* ================================================================== *)
(** ** Strategy (b): canonical form for [transport_clmor_dom]          *)
(* ================================================================== *)

(** Helper: length of [fp_prod] of a singleton-mapped list. *)
Lemma length_fp_prod_singleton_list_th (Th : Theory)
    (xs : list Th.(th_sig).(sg_ty)) :
    length (fp_prod (clth_finite_products Th)
                    (List.map (fun α : Th.(th_sig).(sg_ty) => [α]) xs))
    = length xs.
Proof.
  rewrite (fp_prod_singleton_list_th Th xs). reflexivity.
Qed.

(** [eq_rect] over a domain-equality of [ClMor_q] commutes with the
    quotient projection [clth_mk_q].  Type-level rewrite. *)
Lemma eq_rect_clth_mk_q (Th : Theory) (τ : Th.(th_sig).(sg_ty))
    (X Y : list Th.(th_sig).(sg_ty)) (e : X = Y)
    (m : ClMor Th.(th_sig) X [τ]) :
    eq_rect X (fun Z => ClTh Th ⟦ Z, [τ] ⟧) (clth_mk_q m) Y e =
    clth_mk_q (eq_rect X (fun Z => ClMor Th.(th_sig) Z [τ]) m Y e).
Proof.
  destruct e. simpl. reflexivity.
Qed.

(** [eq_rect] over a CODOMAIN-equality of [ClMor_q] commutes with [clth_mk_q]. *)
Lemma eq_rect_clth_mk_q_cod (Th : Theory) (γ : list Th.(th_sig).(sg_ty))
    (X Y : (ClTh Th).(Ob)) (e : X = Y)
    (m : ClMor Th.(th_sig) γ X) :
    eq_rect X (fun Z : (ClTh Th).(Ob) => ClTh Th ⟦ γ, Z ⟧) (clth_mk_q m) Y e =
    clth_mk_q (eq_rect X (fun Z : (ClTh Th).(Ob) => ClMor Th.(th_sig) γ Z) m Y e).
Proof.
  destruct e. simpl. reflexivity.
Qed.

(** Strategy (b) canonical form: [transport_clmor_dom] of a quotient
    projection equals the quotient projection of the [eq_rect_r] of
    the underlying representative.  This pushes the dependent transport
    "inside" the quotient. *)
Lemma transport_clmor_dom_canonical (Th : Theory)
    (Γ : list Th.(th_sig).(sg_ty)) (τ : Th.(th_sig).(sg_ty))
    (m : ClMor Th.(th_sig) Γ [τ]) :
    transport_clmor_dom Th Γ τ (clth_mk_q m) =
    clth_mk_q
      (eq_rect_r (fun X => ClMor Th.(th_sig) X [τ]) m
                 (fp_prod_singleton_list_th Th Γ)).
Proof.
  unfold transport_clmor_dom, eq_rect_r.
  apply eq_rect_clth_mk_q.
Qed.

(** [eq_rect] at [ClMor] preserves [clmor_terms]: the dependent
    transport on the index list affects only the typing-proof field. *)
Lemma cl_mor_eq_rect_terms (Sg : Signature) (β : list Sg.(sg_ty))
    (X Y : list Sg.(sg_ty)) (e : X = Y) (m : ClMor Sg X β) :
    (eq_rect X (fun Z => ClMor Sg Z β) m Y e).(clmor_terms) =
    m.(clmor_terms).
Proof.
  destruct e. reflexivity.
Qed.

(** Composition reduces over [clth_mk_q] (re-export of [clth_comp_mk]
    through a more explicit name for downstream proofs). *)
Lemma clth_comp_mk_simpl (Th : Theory) (α β γ : list Th.(th_sig).(sg_ty))
    (g : ClMor Th.(th_sig) β γ) (f : ClMor Th.(th_sig) α β) :
    clth_comp Th α β γ (clth_mk_q g) (clth_mk_q f) =
    clth_mk_q (cl_comp Th.(th_sig) α β γ g f).
Proof.
  apply (clth_comp_mk Th).
Qed.

(* ================================================================== *)
(** ** [context_proj] for a singleton-mapped list                       *)
(* ================================================================== *)

(** When [Γ : list Sg.(sg_ty)] and [objs := List.map (fun α => [α]) Γ],
    the iterated projection [context_proj (clth_finite_products Th) n
    [τ] Hn_map] is the quotient projection [clth_mk_q m] of an
    explicit "iterated-cl_proj" morphism [m] whose underlying
    [clmor_terms] is [[t_var n]].  Existential form: we don't name
    [m] explicitly; we just witness its underlying terms list is
    [[t_var n]], which is sufficient for the var case below. *)
Lemma context_proj_singleton_terms (Th : Theory) :
    forall (Γ : list Th.(th_sig).(sg_ty)) (n : nat) (τ : Th.(th_sig).(sg_ty))
           (Hn : List.nth_error Γ n = Some τ)
           (Hn_map : List.nth_error
                       (List.map (fun α : Th.(th_sig).(sg_ty) => [α]) Γ) n
                     = Some [τ]),
    exists m : ClMor Th.(th_sig)
                 (fp_prod (clth_finite_products Th)
                          (List.map (fun α : Th.(th_sig).(sg_ty) => [α]) Γ))
                 [τ],
      context_proj (clth_finite_products Th) n [τ] Hn_map = clth_mk_q m
      /\ m.(clmor_terms) = [t_var n].
Proof.
  intro Γ.
  induction Γ as [|α Γ' IH]; intros n τ Hn Hn_map.
  - destruct n; discriminate Hn.
  - destruct n as [|n].
    + (* n = 0 *)
      simpl in Hn. injection Hn as Heq. subst α.
      destruct Γ' as [|β Γ''].
      * (* Γ = [τ], objs = [[τ]] singleton *)
        simpl in Hn_map.
        eexists (cl_id Th.(th_sig) [τ]). split.
        -- assert (Hn_map_eq : Hn_map = eq_refl) by apply proof_irrelevance.
           rewrite Hn_map_eq. cbn. reflexivity.
        -- simpl. unfold cl_id. simpl. unfold id_sub. simpl. reflexivity.
      * (* Γ = τ::β::Γ'', objs = [τ]::[β]::map (fun α => [α]) Γ'' *)
        simpl in Hn_map.
        assert (Hn_map_eq : Hn_map = eq_refl) by apply proof_irrelevance.
        rewrite Hn_map_eq. cbn -[fp_prod].
        eexists (cl_proj1 Th.(th_sig) [τ]
                   (fp_prod (clth_finite_products Th)
                            (List.map (fun α : Th.(th_sig).(sg_ty) => [α])
                                      (β :: Γ'')))). split.
        -- reflexivity.
        -- simpl. unfold cl_proj1. simpl. unfold id_sub. simpl. reflexivity.
    + (* n = S n' *)
      destruct Γ' as [|β Γ''].
      * destruct n; discriminate Hn.
      * (* Γ = α :: β :: Γ'' *)
        simpl in Hn.
        assert (Hn_map' : List.nth_error
                            (List.map (fun α : Th.(th_sig).(sg_ty) => [α])
                                      (β :: Γ'')) n = Some [τ]).
        { simpl in Hn_map. simpl. exact Hn_map. }
        destruct (IH n τ Hn Hn_map') as [m' [Hm'_eq Hm'_terms]].
        assert (Heq : context_proj (clth_finite_products Th) (S n) [τ] Hn_map
                      = context_proj (clth_finite_products Th) n [τ] Hn_map'
                          ∘ bp_proj2 (prod_bp (@fp_binary _ (clth_finite_products Th))
                                       [α]
                                       (fp_prod (clth_finite_products Th)
                                          (List.map (fun α : Th.(th_sig).(sg_ty) => [α])
                                                    (β :: Γ''))))).
        { rewrite (proof_irrelevance _ Hn_map'
                     (Hn_map : List.nth_error
                        (List.map (fun α : Th.(th_sig).(sg_ty) => [α])
                                  (β :: Γ'')) n = Some [τ])).
          simpl. reflexivity. }
        rewrite Heq.
        rewrite Hm'_eq.
        exists (cl_comp Th.(th_sig) _ _ _ m'
                  (cl_proj2 Th.(th_sig) [α]
                    (fp_prod (clth_finite_products Th)
                       (List.map (fun α : Th.(th_sig).(sg_ty) => [α])
                                 (β :: Γ''))))).
        split.
        -- assert (Hbp : bp_proj2
                          (prod_bp (@fp_binary _ (clth_finite_products Th)) [α]
                             (fp_prod (clth_finite_products Th)
                                (List.map (fun α : Th.(th_sig).(sg_ty) => [α])
                                          (β :: Γ''))))
                        = clth_mk_q
                            (cl_proj2 Th.(th_sig) [α]
                               (fp_prod (clth_finite_products Th)
                                  (List.map (fun α : Th.(th_sig).(sg_ty) => [α])
                                            (β :: Γ''))))).
           { reflexivity. }
           rewrite Hbp.
           apply (clth_comp_mk Th).
        -- simpl. simpl in Hm'_terms.
           rewrite Hm'_terms.
           cbn.
           assert (Hlen_β : n < S (length Γ'')).
           { enough (n < length (β :: Γ'')) as Hl by (simpl in Hl; exact Hl).
             rewrite <- List.nth_error_Some. rewrite Hn. discriminate. }
           cbn -[fp_prod].
           rewrite List.nth_error_map.
           rewrite List.nth_error_seq.
           assert (Heq_len :
              length (match List.map (fun α0 : Th.(th_sig).(sg_ty) => [α0]) Γ'' with
                      | [] => [β]
                      | _ :: _ =>
                          β :: fp_prod (clth_finite_products Th)
                                       (List.map (fun α0 : Th.(th_sig).(sg_ty) => [α0]) Γ'')
                      end)
              = S (length Γ'')).
           { destruct Γ'' as [|γ Γ'''].
             - simpl. reflexivity.
             - cbn -[fp_prod]. f_equal.
               change ([γ] :: List.map (fun α0 : Th.(th_sig).(sg_ty) => [α0]) Γ''')
                 with (List.map (fun α0 : Th.(th_sig).(sg_ty) => [α0]) (γ :: Γ''')).
               apply length_fp_prod_singleton_list_th. }
           rewrite Heq_len.
           assert (Hlt : PeanoNat.Nat.ltb n (S (length Γ'')) = true).
           { apply PeanoNat.Nat.ltb_lt. exact Hlen_β. }
           rewrite Hlt. simpl. reflexivity.
Qed.

(* ================================================================== *)
(** ** Var case of the interpretation lemma                            *)
(* ================================================================== *)

(** The variable case of the interpretation lemma:
    interpretation in [GenericModelTh_data Th] of a variable equals
    the transport of the singleton-term ClMor [t_var n].  This is the
    base case for the term-level interpretation lemma. *)
Lemma interp_var_eq_transport (Th : Theory)
    (Γ : list Th.(th_sig).(sg_ty)) (n : nat) (τ : Th.(th_sig).(sg_ty))
    (Ht : HasType Th.(th_sig) Γ (t_var n) τ) :
    interp_term_data (GenericModelTh_data Th) Γ (t_var n) τ Ht =
    transport_clmor_dom Th Γ τ
      (term_to_clmor_q Th Γ τ (t_var n) Ht).
Proof.
  pose proof (ht_var_nth_err Ht) as Hn.
  assert (Hn_map : List.nth_error
                     (List.map (md_ty (GenericModelTh_data Th)) Γ) n
                   = Some (md_ty (GenericModelTh_data Th) τ)).
  { rewrite List.nth_error_map. rewrite Hn. reflexivity. }
  rewrite (interp_term_data_var (GenericModelTh_data Th) Γ n τ Ht Hn_map).
  unfold term_to_clmor_q, term_to_clmor.
  rewrite transport_clmor_dom_canonical.
  destruct (context_proj_singleton_terms Th Γ n τ Hn Hn_map) as
    [m_proj [Hm_proj_eq Hm_proj_terms]].
  simpl. simpl in Hm_proj_eq. rewrite Hm_proj_eq.
  apply clth_mk_q_eq_iff.
  unfold ClMor_theq.
  intros i t1 t2 τ0 H1 H2 H3.
  destruct i as [|i'].
  - rewrite Hm_proj_terms in H1. cbn in H1. injection H1 as Ht1eq.
    let X := match type of H2 with
             | List.nth_error (clmor_terms ?X) 0 = Some _ => X
             end in
    let H := fresh in
    assert (H : clmor_terms X = [t_var n]) by
      (unfold eq_rect_r; apply cl_mor_eq_rect_terms);
    rewrite H in H2.
    cbn in H2. injection H2 as Ht2eq.
    simpl in H3. injection H3 as Hτ0eq.
    subst t1 t2 τ0.
    apply theq_refl.
    apply ht_var.
    rewrite (fp_prod_singleton_list_th Th Γ). exact Hn.
  - simpl in H3. destruct i'; discriminate H3.
Qed.

(* ================================================================== *)
(** ** App case — lemmas towards the interpretation lemma             *)
(* ================================================================== *)

(** [fp_tuple] in [clth_finite_products] over a list of singleton-typed
    objects (i.e. [List.map (fun α => [α]) xs]) reduces canonically to
    [clth_mk_q] of a [ClMor] whose [clmor_terms] is the concatenation
    of the per-component representatives.

    This is the "binary [clth_pair] iterated" form, with each leaf
    being [clth_mk_q m_i] for some [m_i : ClMor _ γ [xs[i]]] given by
    the continuation [k].

    The key ingredients are [clth_pair_mk] (which says
    [clth_pair (clth_mk_q f) (clth_mk_q g) = clth_mk_q (cl_pair f g)])
    plus the definitional unfolding of [fp_tuple] in the binary
    finite-products structure. *)

(** Helper: each [bp_pair] in [clth_finite_products] is [clth_pair]. *)
Lemma clth_bp_pair_unfold (Th : Theory) (γ α β : list Th.(th_sig).(sg_ty))
    (f : ClTh Th ⟦ γ, α ⟧) (g : ClTh Th ⟦ γ, β ⟧) :
    bp_pair (prod_bp (@fp_binary _ (clth_finite_products Th)) α β) f g
    = clth_pair Th γ α β f g.
Proof. reflexivity. Qed.

(** [fp_tuple] in [clth_finite_products] for a non-empty list reduces
    to [clth_pair] of the first component and the recursive tuple. *)
Lemma fp_tuple_clth_cons2 (Th : Theory) (γ : list Th.(th_sig).(sg_ty))
    (A : list Th.(th_sig).(sg_ty)) (B : list Th.(th_sig).(sg_ty))
    (Bs : list (list Th.(th_sig).(sg_ty)))
    (fs : forall i (X : (ClTh Th).(Ob)),
            List.nth_error (A :: B :: Bs) i = Some X -> ClTh Th ⟦ γ, X ⟧) :
    fp_tuple (clth_finite_products Th) (A :: B :: Bs) fs =
    clth_pair Th γ A (fp_prod (clth_finite_products Th) (B :: Bs))
      (fs 0 A eq_refl)
      (fp_tuple (clth_finite_products Th) (B :: Bs)
                (fun i X H => fs (S i) X H)).
Proof. reflexivity. Qed.

(** When the continuation [fs] factors through [clth_mk_q]:
    [fp_tuple] of singleton-mapped types reduces to [clth_mk_q] of a
    concatenation.

    Statement: given a continuation [fs] that returns
    [clth_mk_q (singleton-term clmor)] at each index, and the underlying
    representatives have concrete representative-terms [u_i],
    [fp_tuple] returns [clth_mk_q M] where [M.(clmor_terms) =
    concat (map (fun u => [u]) [u_0; ...; u_{n-1}]) = [u_0; ...]].

    Proof by induction on [xs]; uses [clth_pair_mk] at each step. *)
Lemma fp_tuple_singleton_canonical (Th : Theory)
    (γ : (ClTh Th).(Ob)) (xs : list Th.(th_sig).(sg_ty))
    (us : list (Term Th.(th_sig)))
    (Hus : Forall2 (HasType Th.(th_sig) γ) us xs)
    (fs : forall i (X : (ClTh Th).(Ob)),
            List.nth_error (List.map (fun α : Th.(th_sig).(sg_ty) => [α]) xs) i
            = Some X -> ClTh Th ⟦ γ, X ⟧)
    (Hfs : forall i (τi : Th.(th_sig).(sg_ty)) (ui : Term Th.(th_sig))
                  (Hxs : List.nth_error xs i = Some τi)
                  (Hus' : List.nth_error us i = Some ui)
                  (HX : List.nth_error
                          (List.map (fun α : Th.(th_sig).(sg_ty) => [α]) xs) i
                        = Some [τi])
                  (Hi : HasType Th.(th_sig) γ ui τi),
            fs i [τi] HX
            = clth_mk_q (term_to_clmor Th γ τi ui Hi)) :
    fp_tuple (clth_finite_products Th)
             (List.map (fun α : Th.(th_sig).(sg_ty) => [α]) xs) fs
    = eq_rect_r (fun X => ClTh Th ⟦ γ, X ⟧)
                (clth_mk_q {| clmor_terms := us; clmor_typed := Hus |})
                (fp_prod_singleton_list_th Th xs).
Proof.
  revert us Hus fs Hfs.
  induction xs as [|α xs IH]; intros us Hus fs Hfs.
  - (* xs = [] : us must be [] *)
    inversion Hus as [|]; subst.
    cbn [List.map fp_tuple].
    unfold eq_rect_r. simpl.
    (* fp_prod_singleton_list_th Th [] = eq_refl by reflexivity *)
    assert (Heq : fp_prod_singleton_list_th Th
                    (@nil Th.(th_sig).(sg_ty)) = eq_refl).
    { apply proof_irrelevance. }
    rewrite Heq. cbn.
    apply clth_mk_q_eq_iff.
    unfold ClMor_theq. intros i t1 t2 τ H1 H2 H3.
    destruct i; cbn in H3; discriminate.
  - (* xs = α :: xs (after re-binding by induction) *)
    (* Hus : Forall2 _ us (α :: xs).  Invert to get us = x :: us0, then
       case on whether xs = [] or xs = β :: xs1. *)
    inversion Hus as [|x y us0 xs0 Hxy Hrest Eqx Eqy].
    subst.
    destruct xs as [|β xs1].
    + (* xs = []: total is [α], us = [x] *)
      inversion Hrest. subst us0.
      assert (Hα : List.nth_error [α] 0 = Some α) by reflexivity.
      assert (Hx : List.nth_error [x] 0 = Some x) by reflexivity.
      (* Show that the LHS reduces to fs 0 [α] eq_refl *)
      change (fs 0 [α] eq_refl
              = eq_rect_r (fun X => ClTh Th ⟦ γ, X ⟧)
                          (clth_mk_q {| clmor_terms := [x]; clmor_typed := Hus |})
                          (fp_prod_singleton_list_th Th [α])).
      pose proof (Hfs 0 α x Hα Hx eq_refl Hxy) as Hfs0.
      rewrite Hfs0.
      unfold eq_rect_r.
      assert (Heq : fp_prod_singleton_list_th Th [α] = eq_refl)
        by apply proof_irrelevance.
      rewrite Heq. cbn.
      apply f_equal. apply clmor_ext. simpl. reflexivity.
    + (* xs = β :: xs1: total is α :: β :: xs1 *)
      inversion Hrest as [|x' y' us1 xs1' Hxy' Hrest' Eq1 Eq2].
      subst.
      (* us0 = x' :: us1, with Hrest : Forall2 _ (x' :: us1) (β :: xs1) *)
      assert (Hα : List.nth_error (α :: β :: xs1) 0 = Some α) by reflexivity.
      assert (Hx : List.nth_error (x :: x' :: us1) 0 = Some x) by reflexivity.
      pose proof (Hfs 0 α x Hα Hx eq_refl Hxy) as Hfs0.
      change (List.map (fun α : Th.(th_sig).(sg_ty) => [α]) (α :: β :: xs1))
        with ([α] :: List.map (fun α : Th.(th_sig).(sg_ty) => [α]) (β :: xs1)).
      change (fp_tuple (clth_finite_products Th)
                ([α] :: List.map (fun α : Th.(th_sig).(sg_ty) => [α]) (β :: xs1)) fs)
        with (clth_pair Th γ [α]
                (fp_prod (clth_finite_products Th)
                   (List.map (fun α : Th.(th_sig).(sg_ty) => [α]) (β :: xs1)))
                (fs 0 [α] eq_refl)
                (fp_tuple (clth_finite_products Th)
                   (List.map (fun α : Th.(th_sig).(sg_ty) => [α]) (β :: xs1))
                   (fun i X H => fs (S i) X H))).
      rewrite Hfs0.
      (* Replace the inner fp_tuple call by the IH's RHS *)
      set (fs_shift := fun i X (H : List.nth_error
                                      (List.map (fun α : Th.(th_sig).(sg_ty) => [α])
                                                (β :: xs1)) i = Some X) =>
                         fs (S i) X H).
      change (fun i X H => fs (S i) X H) with fs_shift.
      pose proof (IH (x' :: us1) Hrest fs_shift
                     (fun i τi ui Hxs' Hus_eq HX' Hi =>
                        Hfs (S i) τi ui Hxs' Hus_eq HX' Hi)) as IH_inst.
      rewrite IH_inst.
      (* LHS: clth_pair (clth_mk_q ..) (eq_rect_r .. (clth_mk_q ..))
         RHS: eq_rect_r .. (clth_mk_q ..) at the outer level *)
      unfold eq_rect_r.
      rewrite (eq_rect_clth_mk_q_cod Th γ _ _
                 (eq_sym (fp_prod_singleton_list_th Th (β :: xs1)))
                 {| clmor_terms := x' :: us1; clmor_typed := Hrest |}).
      rewrite clth_pair_mk.
      change ([α] :: List.map (fun α0 : Th.(th_sig).(sg_ty) => [α0]) (β :: xs1))
        with (List.map (fun α0 : Th.(th_sig).(sg_ty) => [α0]) (α :: β :: xs1)).
      rewrite (eq_rect_clth_mk_q_cod Th γ _ _
                 (eq_sym (fp_prod_singleton_list_th Th (α :: β :: xs1)))
                 {| clmor_terms := x :: x' :: us1; clmor_typed := Hus |}).
      apply f_equal.
      apply clmor_ext.
      cbn [clmor_terms cl_pair].
      (* The eq_rect on a ClMor only affects the typing index, not the terms. *)
      assert (Hterms_eq : forall (γ' X Y : list Th.(th_sig).(sg_ty)) (e : X = Y)
                                 (m : ClMor Th.(th_sig) γ' X),
              (eq_rect X (fun Z => ClMor Th.(th_sig) γ' Z) m Y e).(clmor_terms)
              = m.(clmor_terms)).
      { intros γ' X Y e m. destruct e. reflexivity. }
      rewrite Hterms_eq. cbn.
      rewrite Hterms_eq. cbn.
      reflexivity.
Qed.

(* ================================================================== *)
(** ** Interpretation lemma (full)                                     *)
(* ================================================================== *)

(** Helper: composition of a transport (along a domain equality) of one
    [clth_mk_q] with another [clth_mk_q] reduces by [clth_comp_mk]
    after pushing the transport inside. *)
Lemma clth_comp_eq_rect_l_mk_q (Th : Theory)
    (γ α α' β : list Th.(th_sig).(sg_ty)) (e : α = α')
    (g : ClMor Th.(th_sig) α' β)
    (f : ClMor Th.(th_sig) γ α) :
    clth_comp Th γ α β
      (eq_rect α' (fun Z : (ClTh Th).(Ob) => ClTh Th ⟦ Z, β ⟧)
                  (clth_mk_q g) α (eq_sym e))
      (clth_mk_q f)
    = clth_mk_q (cl_comp Th.(th_sig) γ α β
                   (eq_rect α' (fun Z : (ClTh Th).(Ob) =>
                                  ClMor Th.(th_sig) Z β) g α (eq_sym e))
                   f).
Proof.
  destruct e. simpl.
  apply (clth_comp_mk Th).
Qed.

(** The full interpretation lemma:
    [interp_term_data (GenericModelTh_data Th) Γ t τ Ht =
     transport_clmor_dom Th Γ τ (term_to_clmor_q Th Γ τ t Ht)]. *)
Lemma interp_term_eq_transport (Th : Theory)
    (Γ : list Th.(th_sig).(sg_ty)) (t : Term Th.(th_sig))
    (τ : Th.(th_sig).(sg_ty))
    (Ht : HasType Th.(th_sig) Γ t τ) :
    interp_term_data (GenericModelTh_data Th) Γ t τ Ht =
    transport_clmor_dom Th Γ τ
      (term_to_clmor_q Th Γ τ t Ht).
Proof.
  revert Γ τ Ht.
  induction t as [t IH]
    using (well_founded_induction (@att_term_lt_wf Th.(th_sig))).
  intros Γ τ Ht.
  destruct t as [n | f args].
  - (* var case *) apply interp_var_eq_transport.
  - (* app case *)
    pose proof (ht_app_cod_eq Ht) as Hcod. subst τ.
    rewrite (interp_term_data_app_explicit (GenericModelTh_data Th) Γ f args Ht).
    set (Hargs := ht_app_args_f2 Ht) in *.
    (* LHS: md_fun (GenericModelTh_data Th) f ∘ fp_tuple _ _ (app_cont ...) *)
    (* Compute md_fun first; leave md_ty applications to be unified later. *)
    cbn [md_fun GenericModelTh_data].
    unfold GenericModelTh_mod_fun.
    (* Replace md_ty (GenericModelTh_data Th) with the explicit lambda. *)
    change (md_ty (GenericModelTh_data Th))
      with (fun α : Th.(th_sig).(sg_ty) => @cons Th.(th_sig).(sg_ty) α nil).
    (* Transport Hargs to be typed in fp_prod (clth_fp Th) (map ... Γ),
       which definitionally equals Γ for the trivial cases, but generally
       requires fp_prod_singleton_list_th. *)
    set (Γ' := fp_prod (clth_finite_products Th)
                       (List.map (fun α : Th.(th_sig).(sg_ty) => [α]) Γ)).
    assert (HΓΓ' : Γ' = Γ).
    { unfold Γ'. apply fp_prod_singleton_list_th. }
    pose (Hargs' := eq_rect_r
                      (fun X : list Th.(th_sig).(sg_ty) =>
                         Forall2 (HasType Th.(th_sig) X) args
                                 (Th.(th_sig).(sg_dom) f))
                      Hargs HΓΓ' : Forall2 (HasType Th.(th_sig) Γ') args
                                            (Th.(th_sig).(sg_dom) f)).
    (* Prove the Hfs hypothesis for fp_tuple_singleton_canonical first *)
    assert (Hfs_disch : forall (i : nat) (τi : Th.(th_sig).(sg_ty))
                              (ui : Term Th.(th_sig))
                              (Hxs : List.nth_error (Th.(th_sig).(sg_dom) f) i = Some τi)
                              (Hus_eq : List.nth_error args i = Some ui)
                              (HX : List.nth_error
                                      (List.map (fun α : Th.(th_sig).(sg_ty) => [α])
                                                (Th.(th_sig).(sg_dom) f)) i =
                                    Some [τi])
                              (Hi : HasType Th.(th_sig) Γ' ui τi),
                       app_cont (GenericModelTh_data Th) Γ f args Hargs i [τi] HX
                       = clth_mk_q (term_to_clmor Th Γ' τi ui Hi)).
    { intros i τi ui Hxs Hus_eq HX Hi.
      assert (Harg_typ : HasType Th.(th_sig) Γ ui τi).
      { exact (forall2_nth_hastype Hargs i ui τi Hus_eq Hxs). }
      rewrite (app_cont_some (GenericModelTh_data Th) Γ f args Hargs i [τi] HX
                 τi Hxs eq_refl ui Hus_eq Harg_typ).
      assert (HIH : interp_term_data (GenericModelTh_data Th) Γ ui τi Harg_typ =
                    transport_clmor_dom Th Γ τi (term_to_clmor_q Th Γ τi ui Harg_typ)).
      { apply (IH ui).
        apply (att_args_size_lt f args ui i Hus_eq). }
      rewrite HIH.
      unfold term_to_clmor_q, term_to_clmor.
      rewrite transport_clmor_dom_canonical.
      simpl.
      apply f_equal.
      apply clmor_ext.
      simpl. unfold eq_rect_r.
      assert (Hterms_eq : forall (β X Y : list Th.(th_sig).(sg_ty)) (e : X = Y)
                                 (m : ClMor Th.(th_sig) X β),
              (eq_rect X (fun Z : (ClTh Th).(Ob) => ClMor Th.(th_sig) Z β) m Y e).(clmor_terms)
              = m.(clmor_terms)).
      { intros β X Y e m. destruct e. reflexivity. }
      rewrite Hterms_eq. simpl. reflexivity. }
    pose proof (fp_tuple_singleton_canonical Th Γ'
                 (Th.(th_sig).(sg_dom) f) args Hargs'
                 (app_cont (GenericModelTh_data Th) Γ f args Hargs)
                 Hfs_disch)
      as Hfpt.
    (* Apply Hfpt by transitivity: both LHS-of-Hfpt and the fp_tuple in the
       goal should be definitionally equal. *)
    set (LHS_fpt := fp_tuple (clth_finite_products Th)
                      (List.map (fun α : Th.(th_sig).(sg_ty) =>
                                   (@cons _ α nil : (ClTh Th).(Ob)))
                                (Th.(th_sig).(sg_dom) f))
                      (app_cont (GenericModelTh_data Th) Γ f args Hargs)).
    change (fp_tuple (clth_finite_products Th)
              (List.map (fun α : Th.(th_sig).(sg_ty) => [α])
                        (Th.(th_sig).(sg_dom) f))
              (app_cont (GenericModelTh_data Th) Γ f args Hargs))
      with LHS_fpt in Hfpt.
    change (fp_tuple (clth_finite_products Th)
              (List.map (fun α : Th.(th_sig).(sg_ty) => [α])
                        (Th.(th_sig).(sg_dom) f))
              (app_cont (GenericModelTh_data Th) Γ f args Hargs))
      with LHS_fpt.
    rewrite Hfpt.
    (* main proof: composition reduces *)
    (* LHS: (eq_rect_r (clth_mk_q (G_fun _ f))) ∘ (eq_rect_r (clth_mk_q ⟨args⟩)).
       Both transports are along fp_prod_singleton_list_th Th (sg_dom f). *)
    cbn [comp ClassifyingThCat].
    unfold eq_rect_r.
    (* Push the eq_rect inside the clth_mk_q on the second arg of clth_comp. *)
    rewrite (eq_rect_clth_mk_q_cod Th Γ' _ _
               (eq_sym (fp_prod_singleton_list_th Th (Th.(th_sig).(sg_dom) f)))
               {| clmor_terms := args; clmor_typed := Hargs' |}).
    rewrite clth_comp_eq_rect_l_mk_q.
    unfold term_to_clmor_q.
    rewrite (transport_clmor_dom_canonical Th Γ
               (Th.(th_sig).(sg_cod) f)
               (term_to_clmor Th Γ (Th.(th_sig).(sg_cod) f) (t_app f args) Ht)).
    apply f_equal.
    apply clmor_ext.
    assert (Hterms_eq_dom : forall (β : list Th.(th_sig).(sg_ty))
                                   (X Y : (ClTh Th).(Ob)) (e : X = Y)
                                   (m : ClMor Th.(th_sig) X β),
            (eq_rect X (fun Z : (ClTh Th).(Ob) =>
                          ClMor Th.(th_sig) Z β) m Y e).(clmor_terms)
            = m.(clmor_terms)).
    { intros β X Y e m. destruct e. reflexivity. }
    assert (Hterms_eq_cod : forall (γ' : list Th.(th_sig).(sg_ty))
                                   (X Y : (ClTh Th).(Ob)) (e : X = Y)
                                   (m : ClMor Th.(th_sig) γ' X),
            (eq_rect X (fun Z : (ClTh Th).(Ob) =>
                          ClMor Th.(th_sig) γ' Z) m Y e).(clmor_terms)
            = m.(clmor_terms)).
    { intros γ' X Y e m. destruct e. reflexivity. }
    (* Generalize: prove the LHS and RHS clmor_terms are both [t_app f args]. *)
    transitivity (@cons (Term Th.(th_sig)) (t_app f args) (@nil _)).
    2: { (* RHS = [t_app f args] *)
      unfold eq_rect_r.
      symmetry.
      etransitivity.
      { apply (Hterms_eq_dom [Th.(th_sig).(sg_cod) f] _ _
                 (eq_sym (fp_prod_singleton_list_th Th Γ))
                 (term_to_clmor Th Γ (Th.(th_sig).(sg_cod) f) (t_app f args) Ht)). }
      reflexivity. }
    (* LHS = [t_app f args] *)
    cbn [clmor_terms cl_comp].
    pose proof (Hterms_eq_dom [Th.(th_sig).(sg_cod) f]
                  (Th.(th_sig).(sg_dom) f) _
                  (eq_sym (fp_prod_singleton_list_th Th (Th.(th_sig).(sg_dom) f)))
                  (G_fun Th.(th_sig) f)) as HG_terms.
    pose proof (Hterms_eq_cod Γ' (Th.(th_sig).(sg_dom) f) _
                  (eq_sym (fp_prod_singleton_list_th Th (Th.(th_sig).(sg_dom) f)))
                  {| clmor_terms := args; clmor_typed := Hargs' |}) as Hargs_terms.
    cbn [clmor_terms G_fun] in HG_terms.
    cbn [clmor_terms] in Hargs_terms.
    (* The goal has subst_list (terms_with_eq_rect) (terms_with_eq_rect).
       Use etransitivity with explicit intermediate. *)
    transitivity (subst_list Th.(th_sig) args [G_fun_term Th.(th_sig) f]).
    { f_equal.
      - exact Hargs_terms.
      - exact HG_terms. }
    (* Goal: subst_list args [G_fun_term f] = [t_app f args] *)
    unfold G_fun_term, subst_list.
    cbn [List.map].
    f_equal.
    cbn [subst_term].
    f_equal.
    assert (Hlen : length args = length (Th.(th_sig).(sg_dom) f)).
    { exact (Forall2_length Hargs). }
    rewrite <- Hlen.
    change (List.map (subst_term Th.(th_sig) args)
                     (List.map t_var (List.seq 0 (length args))) = args).
    fold (id_sub Th.(th_sig) (length args)).
    change (subst_list Th.(th_sig) args (id_sub Th.(th_sig) (length args)) = args).
    apply subst_var_list.
Qed.

(* ================================================================== *)
(** ** Step 4: GenericModelTh — full Model record                      *)
(* ================================================================== *)

(** [GenericModelTh] is the full [Model Th (ClTh Th) (clth_finite_products Th)]
    obtained from [GenericModelTh_data] together with the [mod_ax] obligation
    discharged via the interpretation lemma + [theq_ax]. *)
Definition GenericModelTh (Th : Theory) :
    Model Th (ClTh Th) (clth_finite_products Th).
Proof.
  refine (@Build_Model Th (ClTh Th) (clth_finite_products Th)
            (GenericModelTh_data Th) _).
  (* mod_ax obligation: forall (a : TheoryAxiom Th.(th_sig)) (Hin : In a Th.(th_ax)),
     interp_term_data (GenericModelTh_data Th) a.(ax_ctx)
       a.(ax_lhs) a.(ax_sort) a.(ax_lhs_typed)
     = interp_term_data (GenericModelTh_data Th) a.(ax_ctx)
       a.(ax_rhs) a.(ax_sort) a.(ax_rhs_typed). *)
  intros a Hin.
  rewrite (interp_term_eq_transport Th a.(ax_ctx) a.(ax_lhs)
             a.(ax_sort) a.(ax_lhs_typed)).
  rewrite (interp_term_eq_transport Th a.(ax_ctx) a.(ax_rhs)
             a.(ax_sort) a.(ax_rhs_typed)).
  unfold transport_clmor_dom.
  unfold term_to_clmor_q, term_to_clmor.
  (* Both sides are eq_rect_r of clth_mk_q.  Suffices: the clmors are theq-eq. *)
  assert (Hclmor_eq :
    clth_mk_q {| clmor_terms := [a.(ax_lhs)];
                 clmor_typed := Forall2_cons _ _ a.(ax_lhs_typed)
                                              (Forall2_nil _) |}
    = clth_mk_q {| clmor_terms := [a.(ax_rhs)];
                   clmor_typed := Forall2_cons _ _ a.(ax_rhs_typed)
                                                (Forall2_nil _) |}).
  { apply clth_mk_q_eq_iff.
    unfold ClMor_theq.
  intros i t1 t2 τ H1 H2 Hβ.
  destruct i as [|i'].
  - cbn in H1, H2, Hβ.
    injection H1 as <-. injection H2 as <-. injection Hβ as <-.
    (* Goal: ThEq Th.(th_sig) Th.(th_ax) a.(ax_ctx) a.(ax_lhs) a.(ax_rhs) a.(ax_sort) *)
    (* Use theq_ax with sub := id_sub _ (length a.(ax_ctx)) *)
    pose proof (theq_ax Th.(th_sig) Th.(th_ax) a.(ax_ctx) a
                  (id_sub Th.(th_sig) (length a.(ax_ctx))) Hin
                  (id_vars_typed_ok Th.(th_sig) a.(ax_ctx))) as Hax.
    rewrite (subst_id_term Th.(th_sig) (length a.(ax_ctx)) a.(ax_lhs)) in Hax.
    rewrite (subst_id_term Th.(th_sig) (length a.(ax_ctx)) a.(ax_rhs)) in Hax.
    exact Hax.
  - simpl in Hβ. destruct i'; discriminate Hβ. }
  rewrite Hclmor_eq.
  reflexivity.
Defined.
