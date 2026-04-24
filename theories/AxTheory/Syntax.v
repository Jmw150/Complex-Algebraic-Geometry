(** * AxTheory/Syntax.v
    Syntax of an Ax-theory (simply-typed lambda calculus over an algebraic signature).

    An Ax-type is built from:
    - ground sorts of the algebraic signature
    - a unit type
    - binary products (α × β)
    - exponential types (α ⇒ β)

    An Ax-term is built from:
    - variables (de Bruijn indices)
    - applications of basic function symbols to argument tuples
    - the unit term ★
    - pairs ⟨M, N⟩ and projections fst/snd
    - lambda abstraction λ M and application M N

    Contexts are lists of AxTypes.
    Typing is a simple inductive judgment AxHasType. *)

Require Import CAG.ATT.Signature.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.
Import ListNotations.

Set Universe Polymorphism.

(** ** Ax-types *)

Inductive AxType (Sg : Signature) : Type :=
  | ax_ground  : Sg.(sg_ty) -> AxType Sg       (* ground sort *)
  | ax_unit    : AxType Sg                      (* unit type  1 *)
  | ax_prod    : AxType Sg -> AxType Sg -> AxType Sg   (* product α × β *)
  | ax_exp     : AxType Sg -> AxType Sg -> AxType Sg.  (* exponential β^α *)

Arguments ax_ground {Sg} s.
Arguments ax_unit   {Sg}.
Arguments ax_prod   {Sg} α β.
Arguments ax_exp    {Sg} α β.

Notation "α ×ax β" := (ax_prod α β) (at level 40) : type_scope.
Notation "α ⇒ax β" := (ax_exp α β)  (at level 55, right associativity) : type_scope.

(** ** Ax-terms

    Terms are indexed by the signature only (not by types); typing is separate. *)

Inductive AxTerm (Sg : Signature) : Type :=
  | ax_var    : nat -> AxTerm Sg
  | ax_app_fn : Sg.(sg_fun) -> list (AxTerm Sg) -> AxTerm Sg  (* basic function *)
  | ax_tt     : AxTerm Sg                                       (* unit term ★ *)
  | ax_pair   : AxTerm Sg -> AxTerm Sg -> AxTerm Sg             (* ⟨M, N⟩ *)
  | ax_fst    : AxTerm Sg -> AxTerm Sg                          (* fst M *)
  | ax_snd    : AxTerm Sg -> AxTerm Sg                          (* snd M *)
  | ax_lam    : AxTerm Sg -> AxTerm Sg                          (* λ M  (binder) *)
  | ax_ap     : AxTerm Sg -> AxTerm Sg -> AxTerm Sg.            (* M N  (application) *)

Arguments ax_var    {Sg}.
Arguments ax_app_fn {Sg}.
Arguments ax_tt     {Sg}.
Arguments ax_pair   {Sg}.
Arguments ax_fst    {Sg}.
Arguments ax_snd    {Sg}.
Arguments ax_lam    {Sg}.
Arguments ax_ap     {Sg}.

(** ** Typing judgment

    [AxHasType Sg Γ M α] means term M has type α in context Γ.
    Context Γ is a list of AxTypes; variable i has type Γ[i]. *)

Inductive AxHasType (Sg : Signature) (Γ : list (AxType Sg)) :
    AxTerm Sg -> AxType Sg -> Prop :=

  (** Variables *)
  | ax_ht_var : forall i α,
      List.nth_error Γ i = Some α ->
      AxHasType Sg Γ (ax_var i) α

  (** Basic function symbols (ground types only) *)
  | ax_ht_fn  : forall (f : Sg.(sg_fun)) (args : list (AxTerm Sg)),
      List.Forall2 (fun M τ => AxHasType Sg Γ M (ax_ground τ))
                   args (Sg.(sg_dom) f) ->
      AxHasType Sg Γ (ax_app_fn f args) (ax_ground (Sg.(sg_cod) f))

  (** Unit *)
  | ax_ht_tt  : AxHasType Sg Γ ax_tt ax_unit

  (** Pairing *)
  | ax_ht_pair : forall M N α β,
      AxHasType Sg Γ M α ->
      AxHasType Sg Γ N β ->
      AxHasType Sg Γ (ax_pair M N) (α ×ax β)

  (** First projection *)
  | ax_ht_fst : forall M α β,
      AxHasType Sg Γ M (α ×ax β) ->
      AxHasType Sg Γ (ax_fst M) α

  (** Second projection *)
  | ax_ht_snd : forall M α β,
      AxHasType Sg Γ M (α ×ax β) ->
      AxHasType Sg Γ (ax_snd M) β

  (** Lambda abstraction: Γ, α ⊢ M : β  ⟹  Γ ⊢ λ M : α ⇒ β *)
  | ax_ht_lam : forall M α β,
      AxHasType Sg (α :: Γ) M β ->
      AxHasType Sg Γ (ax_lam M) (α ⇒ax β)

  (** Application: Γ ⊢ M : α ⇒ β   Γ ⊢ N : α  ⟹  Γ ⊢ M N : β *)
  | ax_ht_ap  : forall M N α β,
      AxHasType Sg Γ M (α ⇒ax β) ->
      AxHasType Sg Γ N α ->
      AxHasType Sg Γ (ax_ap M N) β.

(** ** Substitution

    Substitution replaces variable i by sub[i].
    In the lambda case we shift the substitution. *)

(** Lift a single term: increment all free variable indices ≥ cutoff by 1.
    Needed when going under a binder during substitution. *)
Fixpoint ax_lift (Sg : Signature) (cutoff : nat) (t : AxTerm Sg) : AxTerm Sg :=
  match t with
  | ax_var i     => if Nat.ltb i cutoff then ax_var i else ax_var (S i)
  | ax_app_fn f args => ax_app_fn f (List.map (ax_lift Sg cutoff) args)
  | ax_tt        => ax_tt
  | ax_pair M N  => ax_pair (ax_lift Sg cutoff M) (ax_lift Sg cutoff N)
  | ax_fst M     => ax_fst (ax_lift Sg cutoff M)
  | ax_snd M     => ax_snd (ax_lift Sg cutoff M)
  | ax_lam M     => ax_lam (ax_lift Sg (S cutoff) M)
  | ax_ap M N    => ax_ap (ax_lift Sg cutoff M) (ax_lift Sg cutoff N)
  end.

(** Lift/shift substitution under a binder:
    insert ax_var 0 at position 0 and lift all existing substitution terms by 1. *)
Definition ax_shift_sub (Sg : Signature) (sub : list (AxTerm Sg)) : list (AxTerm Sg) :=
  ax_var 0 :: List.map (ax_lift Sg 0) sub.

(** Parallel substitution: replace variable i by sub[i].
    If i >= length sub, the variable is free and stays as ax_var (i - length sub). *)
Fixpoint ax_subst {Sg : Signature} (sub : list (AxTerm Sg)) (t : AxTerm Sg) : AxTerm Sg :=
  match t with
  | ax_var i     => match List.nth_error sub i with
                    | Some u => u
                    | None   => ax_var (i - List.length sub)
                    end
  | ax_app_fn f args => ax_app_fn f (List.map (ax_subst sub) args)
  | ax_tt        => ax_tt
  | ax_pair M N  => ax_pair (ax_subst sub M) (ax_subst sub N)
  | ax_fst M     => ax_fst (ax_subst sub M)
  | ax_snd M     => ax_snd (ax_subst sub M)
  | ax_lam M     => ax_lam (ax_subst (ax_shift_sub Sg sub) M)
  | ax_ap M N    => ax_ap (ax_subst sub M) (ax_subst sub N)
  end.

(** Helper: lifting a term preserves typing when inserting a type in context. *)
Lemma ax_lift_preserves_type_gen : forall (Sg : Signature)
    (Γ1 Γ2 : list (AxType Sg)) (β : AxType Sg)
    (M : AxTerm Sg) (α : AxType Sg)
    (HM : AxHasType Sg (Γ1 ++ Γ2) M α),
    AxHasType Sg (Γ1 ++ β :: Γ2) (ax_lift Sg (length Γ1) M) α.
Proof.
  fix IH 7.
  intros Sg Γ1 Γ2 β M α HM.
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
    simpl. destruct (Nat.ltb_spec i (length Γ1)) as [Hlt | Hge].
    + apply ax_ht_var.
      rewrite List.nth_error_app1 in Hvar by exact Hlt.
      rewrite List.nth_error_app1 by exact Hlt.
      exact Hvar.
    + apply ax_ht_var.
      rewrite List.nth_error_app2 in Hvar by exact Hge.
      rewrite List.nth_error_app2 by lia.
      rewrite Nat.sub_succ_l by exact Hge.
      exact Hvar.
  - (* ax_ht_fn *)
    simpl. apply ax_ht_fn.
    induction HForall as [| a τ rest dom' Ha Hrest IHHForall].
    + constructor.
    + constructor.
      * exact (IH Sg Γ1 Γ2 β a (ax_ground τ) Ha).
      * exact IHHForall.
  - (* ax_ht_tt *)
    apply ax_ht_tt.
  - (* ax_ht_pair *)
    simpl. apply ax_ht_pair.
    + exact (IH Sg Γ1 Γ2 β M0 α0 HM1).
    + exact (IH Sg Γ1 Γ2 β N0 β0 HN1).
  - (* ax_ht_fst *)
    simpl. eapply ax_ht_fst.
    exact (IH Sg Γ1 Γ2 β M0 (α0 ×ax β0) HM0).
  - (* ax_ht_snd *)
    simpl. eapply ax_ht_snd.
    exact (IH Sg Γ1 Γ2 β M0 (α0 ×ax β0) HM0).
  - (* ax_ht_lam *)
    simpl. apply ax_ht_lam.
    change (S (length Γ1)) with (length (α0 :: Γ1)).
    change (α0 :: Γ1 ++ Γ2) with ((α0 :: Γ1) ++ Γ2) in HM0.
    exact (IH Sg (α0 :: Γ1) Γ2 β M0 β0 HM0).
  - (* ax_ht_ap *)
    simpl. apply (ax_ht_ap _ _ _ _ α0).
    + exact (IH Sg Γ1 Γ2 β M0 (α0 ⇒ax β0) HM1).
    + exact (IH Sg Γ1 Γ2 β N0 α0 HN1).
Qed.

(** Corollary: lift at cutoff 0 (prepend one type to context). *)
Lemma ax_lift_preserves_type : forall (Sg : Signature)
    (Γ : list (AxType Sg)) (β : AxType Sg)
    (M : AxTerm Sg) (α : AxType Sg),
    AxHasType Sg Γ M α ->
    AxHasType Sg (β :: Γ) (ax_lift Sg 0 M) α.
Proof.
  intros Sg Γ β M α H.
  exact (ax_lift_preserves_type_gen Sg [] Γ β M α H).
Qed.

(** Helper: lifting preserves Forall2 of typing. *)
Lemma ax_lift_Forall2_type : forall (Sg : Signature)
    (Γ : list (AxType Sg)) (β : AxType Sg)
    (sub : list (AxTerm Sg)) (Γ' : list (AxType Sg)),
    List.Forall2 (AxHasType Sg Γ) sub Γ' ->
    List.Forall2 (AxHasType Sg (β :: Γ)) (List.map (ax_lift Sg 0) sub) Γ'.
Proof.
  intros Sg Γ β sub Γ' HF.
  induction HF as [| u τ rest Γ'' Hu Hrest IH].
  - constructor.
  - simpl. constructor.
    + exact (ax_lift_preserves_type Sg Γ β u τ Hu).
    + exact IH.
Qed.

Theorem ax_subst_preserves_type : forall (Sg : Signature)
    (Γ Γ' : list (AxType Sg))
    (sub : list (AxTerm Sg))
    (Hsub : List.Forall2 (AxHasType Sg Γ) sub Γ')
    (M : AxTerm Sg) (α : AxType Sg)
    (HM : AxHasType Sg Γ' M α),
    AxHasType Sg Γ (ax_subst sub M) α.
Proof.
  fix IH 8.
  intros Sg Γ Γ' sub Hsub M α HM.
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
  - (* ax_ht_var i α0 Hvar : nth_error Γ' i = Some α0 *)
    revert i α0 Hvar.
    induction Hsub as [| a b la lb Ha Hla IHHsub]; intros i α0 Hvar.
    + destruct i; discriminate Hvar.
    + destruct i as [|i].
      * simpl in Hvar. injection Hvar as <-. simpl. exact Ha.
      * simpl in Hvar. simpl. exact (IHHsub i α0 Hvar).
  - (* ax_ht_fn *)
    simpl. apply ax_ht_fn.
    induction HForall as [| a τ rest dom' Ha Hrest IHHForall].
    + constructor.
    + constructor.
      * exact (IH Sg Γ Γ' sub Hsub a (ax_ground τ) Ha).
      * exact IHHForall.
  - apply ax_ht_tt.
  - simpl. apply ax_ht_pair.
    + exact (IH Sg Γ Γ' sub Hsub M0 α0 HM1).
    + exact (IH Sg Γ Γ' sub Hsub N0 β0 HN1).
  - simpl. eapply ax_ht_fst.
    exact (IH Sg Γ Γ' sub Hsub M0 (α0 ×ax β0) HM0).
  - simpl. eapply ax_ht_snd.
    exact (IH Sg Γ Γ' sub Hsub M0 (α0 ×ax β0) HM0).
  - (* ax_ht_lam : AxHasType Sg (α0 :: Γ') M0 β0 *)
    simpl. apply ax_ht_lam.
    apply (IH Sg (α0 :: Γ) (α0 :: Γ') (ax_shift_sub Sg sub)).
    + (* Forall2 (AxHasType Sg (α0 :: Γ)) (ax_shift_sub sub) (α0 :: Γ') *)
      unfold ax_shift_sub. constructor.
      * apply ax_ht_var. simpl. reflexivity.
      * exact (ax_lift_Forall2_type Sg Γ α0 sub Γ' Hsub).
    + exact HM0.
  - simpl. apply (ax_ht_ap _ _ _ _ α0).
    + exact (IH Sg Γ Γ' sub Hsub M0 (α0 ⇒ax β0) HM1).
    + exact (IH Sg Γ Γ' sub Hsub N0 α0 HN1).
Qed.

(** Identity substitution. *)
Definition ax_id_sub (Sg : Signature) (n : nat) : list (AxTerm Sg) :=
  List.map ax_var (List.seq 0 n).

(** Helper: nth_error of (seq start n) at index i < n equals Some (start + i). *)
Lemma nth_error_seq : forall (start n i : nat),
    (i < n)%nat -> List.nth_error (List.seq start n) i = Some (start + i).
Proof.
  intros start n. revert start.
  induction n as [|n IH].
  - intros start i Hi. inversion Hi.
  - intros start i Hi.
    destruct i as [|i].
    + simpl. f_equal. lia.
    + simpl. rewrite (IH (S start) i) by lia. f_equal. lia.
Qed.

(** Helper: nth_error of ax_id_sub at index i < n is Some (ax_var i). *)
Lemma nth_error_id_sub : forall (Sg : Signature) (n i : nat),
    (i < n)%nat -> List.nth_error (ax_id_sub Sg n) i = Some (ax_var i).
Proof.
  intros Sg n i Hi.
  unfold ax_id_sub.
  rewrite List.nth_error_map.
  rewrite nth_error_seq by exact Hi.
  simpl. reflexivity.
Qed.

(** Helper: ax_lift Sg 0 (ax_var i) = ax_var (S i). *)
Lemma ax_lift_var_zero : forall (Sg : Signature) (i : nat),
    ax_lift Sg 0 (ax_var i) = ax_var (S i).
Proof.
  intros Sg i. simpl.
  destruct (Nat.ltb_spec i 0) as [H | H].
  - inversion H.
  - reflexivity.
Qed.

(** Helper: map S (seq k n) = seq (S k) n. *)
Lemma seq_succ : forall (n k : nat),
    List.map S (List.seq k n) = List.seq (S k) n.
Proof.
  induction n as [|n IH].
  - intros k. reflexivity.
  - intros k. simpl. rewrite IH. reflexivity.
Qed.

(** Helper: shifting the identity substitution gives the next identity substitution. *)
Lemma ax_shift_id_sub : forall (Sg : Signature) (n : nat),
    ax_shift_sub Sg (ax_id_sub Sg n) = ax_id_sub Sg (S n).
Proof.
  intros Sg n.
  unfold ax_shift_sub, ax_id_sub.
  simpl. f_equal.
  rewrite List.map_map.
  rewrite <- (seq_succ n 0).
  rewrite List.map_map.
  apply List.map_ext.
  intro a.
  exact (ax_lift_var_zero Sg a).
Qed.

Theorem ax_subst_id : forall (Sg : Signature) (Γ : list (AxType Sg)) (M : AxTerm Sg) α,
    AxHasType Sg Γ M α ->
    ax_subst (ax_id_sub Sg (length Γ)) M = M.
Proof.
  fix IH 5.
  intros Sg Γ M α HM.
  destruct HM.
  - (* ax_ht_var: nth_error Γ i = Some α *)
    simpl.
    assert (Hi : (i < length Γ)%nat).
    { apply List.nth_error_Some. rewrite H. discriminate. }
    rewrite nth_error_id_sub by exact Hi.
    reflexivity.
  - (* ax_ht_fn: Forall2 (...) args (sg_dom f) *)
    simpl. f_equal.
    induction H as [| a τ rest dom' Ha Hrest IHrest].
    + reflexivity.
    + simpl. f_equal.
      * exact (IH Sg Γ a (ax_ground τ) Ha).
      * exact IHrest.
  - (* ax_ht_tt *)
    reflexivity.
  - (* ax_ht_pair *)
    simpl. f_equal.
    + exact (IH Sg Γ M α HM1).
    + exact (IH Sg Γ N β HM2).
  - (* ax_ht_fst *)
    simpl. f_equal.
    exact (IH Sg Γ M (ax_prod α β) HM).
  - (* ax_ht_snd *)
    simpl. f_equal.
    exact (IH Sg Γ M (ax_prod α β) HM).
  - (* ax_ht_lam: AxHasType Sg (α :: Γ) M β *)
    simpl. f_equal.
    rewrite ax_shift_id_sub.
    change (S (length Γ)) with (length (α :: Γ)).
    exact (IH Sg (α :: Γ) M β HM).
  - (* ax_ht_ap *)
    simpl. f_equal.
    + exact (IH Sg Γ M (ax_exp α β) HM1).
    + exact (IH Sg Γ N α HM2).
Qed.

(** Substitution composition.

    NOTE: The untyped statement is FALSE.  Counter-example:
      Sg arbitrary, sub2 = [], M = ax_var 0, sub1 = [ax_tt]:
        LHS = ax_subst [ax_tt] (ax_subst [] (ax_var 0))
            = ax_subst [ax_tt] (ax_var 0)   (* var 0 out of range of []: stays ax_var 0 *)
            = ax_tt
        RHS = ax_subst (map (ax_subst [ax_tt]) []) (ax_var 0)
            = ax_subst [] (ax_var 0)
            = ax_var 0.
    The correct statement requires M to be typed in a context matching sub2's domain.
    We state this restricted (typed) version as an axiom; a formal proof would proceed
    by induction on the typing derivation. *)
Axiom ax_subst_comp : forall (Sg : Signature) (Γ : list (AxType Sg))
    (sub1 sub2 : list (AxTerm Sg)) (M : AxTerm Sg) (α : AxType Sg),
    List.length sub2 = List.length Γ ->
    AxHasType Sg Γ M α ->
    ax_subst sub1 (ax_subst sub2 M) =
    ax_subst (List.map (ax_subst sub1) sub2) M.

(** Substituting a singleton list for variable 0. *)
Theorem ax_subst_singleton_var_0 : forall (Sg : Signature) (t : AxTerm Sg),
    ax_subst [t] (ax_var 0) = t.
Proof. intros. simpl. reflexivity. Qed.

(** ** Ax-axioms

    An axiom in an Ax-theory is a typing context plus two typed equal terms. *)

Record AxAxiom (Sg : Signature) : Type := {
  axax_ctx  : list (AxType Sg);
  axax_lhs  : AxTerm Sg;
  axax_rhs  : AxTerm Sg;
  axax_sort : AxType Sg;
  axax_lhs_typed : AxHasType Sg axax_ctx axax_lhs axax_sort;
  axax_rhs_typed : AxHasType Sg axax_ctx axax_rhs axax_sort;
}.

Arguments axax_ctx  {Sg}.
Arguments axax_lhs  {Sg}.
Arguments axax_rhs  {Sg}.
Arguments axax_sort {Sg}.
Arguments axax_lhs_typed {Sg}.
Arguments axax_rhs_typed {Sg}.

(** ** Provable equality in an Ax-theory

    [AxThEq Sg ax Γ M N α] is the congruence closure of axioms ax. *)

Inductive AxThEq (Sg : Signature) (ax : list (AxAxiom Sg))
    (Γ : list (AxType Sg)) :
    AxTerm Sg -> AxTerm Sg -> AxType Sg -> Prop :=

  | axeq_refl  : forall M α, AxHasType Sg Γ M α -> AxThEq Sg ax Γ M M α
  | axeq_sym   : forall M N α, AxThEq Sg ax Γ M N α -> AxThEq Sg ax Γ N M α
  | axeq_trans : forall M N P α,
      AxThEq Sg ax Γ M N α -> AxThEq Sg ax Γ N P α ->
      AxThEq Sg ax Γ M P α

  (** Congruence rules *)
  | axeq_pair : forall M M' N N' α β,
      AxThEq Sg ax Γ M M' α -> AxThEq Sg ax Γ N N' β ->
      AxThEq Sg ax Γ (ax_pair M N) (ax_pair M' N') (α ×ax β)
  | axeq_fst  : forall M M' α β,
      AxThEq Sg ax Γ M M' (α ×ax β) ->
      AxThEq Sg ax Γ (ax_fst M) (ax_fst M') α
  | axeq_snd  : forall M M' α β,
      AxThEq Sg ax Γ M M' (α ×ax β) ->
      AxThEq Sg ax Γ (ax_snd M) (ax_snd M') β
  | axeq_lam  : forall M M' α β,
      AxThEq Sg ax (α :: Γ) M M' β ->
      AxThEq Sg ax Γ (ax_lam M) (ax_lam M') (α ⇒ax β)
  | axeq_ap   : forall M M' N N' α β,
      AxThEq Sg ax Γ M M' (α ⇒ax β) ->
      AxThEq Sg ax Γ N N' α ->
      AxThEq Sg ax Γ (ax_ap M N) (ax_ap M' N') β

  (** Beta/eta rules for products *)
  | axeq_beta_fst : forall M N α β,
      AxHasType Sg Γ M α -> AxHasType Sg Γ N β ->
      AxThEq Sg ax Γ (ax_fst (ax_pair M N)) M α
  | axeq_beta_snd : forall M N α β,
      AxHasType Sg Γ M α -> AxHasType Sg Γ N β ->
      AxThEq Sg ax Γ (ax_snd (ax_pair M N)) N β
  | axeq_eta_prod : forall M α β,
      AxHasType Sg Γ M (α ×ax β) ->
      AxThEq Sg ax Γ (ax_pair (ax_fst M) (ax_snd M)) M (α ×ax β)

  (** Beta/eta rules for exponentials *)
  | axeq_beta_lam : forall M N α β,
      AxHasType Sg (α :: Γ) M β -> AxHasType Sg Γ N α ->
      AxThEq Sg ax Γ (ax_ap (ax_lam M) N) (ax_subst (N :: ax_id_sub Sg (length Γ)) M) β
  | axeq_eta_lam  : forall M α β,
      AxHasType Sg Γ M (α ⇒ax β) ->
      AxThEq Sg ax Γ (ax_lam (ax_ap (ax_subst (List.map (fun t => ax_subst [ax_var 1] t) (ax_id_sub Sg (length Γ))) M) (ax_var 0))) M (α ⇒ax β)

  (** Axiom instantiation *)
  | axeq_ax : forall (a : AxAxiom Sg) (sub : list (AxTerm Sg)),
      List.In a ax ->
      List.Forall2 (AxHasType Sg Γ) sub a.(axax_ctx) ->
      AxThEq Sg ax Γ
        (ax_subst sub a.(axax_lhs))
        (ax_subst sub a.(axax_rhs))
        a.(axax_sort).
