(** * Sheaves/PreSheaf.v
    Concrete presheaf and sheaf constructions.

    Provides a real, non-degenerate model of the "sheaf of A-valued
    functions" over an arbitrary topological space.

    For an abelian group A, sections over U are functions
        { x : X | U x } -> A
    with restriction induced by the inclusion of subtypes. Pointwise
    addition gives the abelian-group structure on each section type;
    sheaf locality and gluing are proved by choosing, for each x in
    the union, a cover element containing x and reading off its value
    there. The dependent equality between section types under a change
    of "open" predicate is handled via [eq_rect].

    This is not the locally-constant constant sheaf (those sections
    are constrained), but it IS the so-called "Godement / flasque sheaf
    of A-valued functions", which is a genuine sheaf on every space.
    It serves as a concrete witness for [Sheaves.const_sheaf] used
    purely as an existence target. *)

From Stdlib Require Import List.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.IndefiniteDescription.
From Stdlib Require Import Logic.ProofIrrelevance.
Import ListNotations.

From CAG Require Import Topology.
From CAG Require Import Sheaves.

Local Notation In := List.In.

(* ================================================================== *)
(** * The presheaf of A-valued functions                                *)
(* ================================================================== *)

Section FunctionPresheaf.

  Context {X : Type} (TX : Topology X).
  Context {A : Type} (GA : AbGroup A).

  (** Section over U: a function from points of U into A. *)
  Definition fn_sec (U : set X) (HU : is_open TX U) : Type :=
    { x : X | U x } -> A.

  (** Pointwise abelian-group structure on sections. *)
  Definition fn_group (U : set X) (HU : is_open TX U)
      : AbGroup (fn_sec U HU).
  Proof.
    refine {|
      ag_add  := fun f g => fun p => ag_add GA (f p) (g p);
      ag_zero := fun _ => ag_zero GA;
      ag_neg  := fun f => fun p => ag_neg GA (f p)
    |}.
    - intros f g h. extensionality p. apply (ag_assoc _ GA).
    - intros f g.   extensionality p. apply (ag_comm  _ GA).
    - intros f.     extensionality p. apply (ag_zero_r _ GA).
    - intros f.     extensionality p. apply (ag_neg_r  _ GA).
  Defined.

  (** Restriction along U ⊆ V: precompose with the inclusion of
      subtypes. *)
  Definition fn_res (U V : set X) (HU : is_open TX U) (HV : is_open TX V)
      (hUV : forall x, U x -> V x) (s : fn_sec V HV) : fn_sec U HU :=
    fun p => match p with exist _ x hx => s (exist _ x (hUV x hx)) end.

  (** Functoriality: identity restriction is identity. *)
  Lemma fn_res_id : forall (U : set X) (HU : is_open TX U) (s : fn_sec U HU),
      fn_res U U HU HU (fun x h => h) s = s.
  Proof.
    intros U HU s. extensionality p. destruct p as [x hx]. reflexivity.
  Qed.

  (** Functoriality: composition. *)
  Lemma fn_res_comp : forall (U V W : set X)
        (HU : is_open TX U) (HV : is_open TX V) (HW : is_open TX W)
        (hUV : forall x, U x -> V x) (hVW : forall x, V x -> W x)
        (s : fn_sec W HW),
      fn_res U V HU HV hUV (fn_res V W HV HW hVW s) =
      fn_res U W HU HW (fun x h => hVW x (hUV x h)) s.
  Proof.
    intros U V W HU HV HW hUV hVW s.
    extensionality p. destruct p as [x hx]. reflexivity.
  Qed.

  (** The presheaf of A-valued functions. *)
  Definition fn_presheaf : Presheaf X TX :=
    {| psf_sec      := fn_sec
     ; psf_group    := fn_group
     ; psf_res      := fn_res
     ; psf_res_id   := fn_res_id
     ; psf_res_comp := fn_res_comp
    |}.

End FunctionPresheaf.

(* ================================================================== *)
(** * The function presheaf is a sheaf                                  *)
(* ================================================================== *)

Section FunctionSheaf.

  Context {X : Type} (TX : Topology X).
  Context {A : Type} (GA : AbGroup A).

  (** Locality: if a section restricts to zero on every cover element,
      then it is the zero section. We use functional extensionality plus
      the cover-membership to read off the value at each point. *)
  Lemma fn_sheaf_local :
    forall (U : set X) (HU : is_open TX U)
           (s : psf_sec (fn_presheaf TX GA) U HU)
           (cover : list (set X))
           (cover_open : forall V, In V cover -> is_open TX V)
           (cover_sub  : forall V, In V cover -> forall x, V x -> U x)
           (cover_all  : forall x, U x -> exists V, In V cover /\ V x),
    (forall V (HV : is_open TX V) (hVU : forall x, V x -> U x),
       In V cover ->
       psf_res (fn_presheaf TX GA) V U HV HU hVU s =
       ag_zero (psf_group (fn_presheaf TX GA) V HV)) ->
    s = ag_zero (psf_group (fn_presheaf TX GA) U HU).
  Proof.
    intros U HU s cover cover_open cover_sub cover_all Hzero.
    extensionality p. destruct p as [x Hx].
    (* Pick a cover element containing x. *)
    destruct (cover_all x Hx) as [V [HVcov HVx]].
    pose (HV := cover_open V HVcov).
    pose (hVU := cover_sub V HVcov).
    specialize (Hzero V HV hVU HVcov).
    (* Hzero says: fn_res s = const zero (as functions {y|V y} -> A) *)
    apply (f_equal (fun (f : fn_sec TX V HV) => f (exist _ x HVx))) in Hzero.
    cbn in Hzero.
    (* Hzero refers to s at (x, hVU x HVx); we need it at (x, Hx). Use proof
       irrelevance on U x. *)
    replace (hVU x HVx) with Hx in Hzero by apply proof_irrelevance.
    exact Hzero.
  Qed.

  (** Gluing: compatible local sections glue. We define the global
      section by, at each point, choosing a cover element containing
      the point and reading off the local section there.  Compatibility
      on overlaps guarantees independence of the choice. *)
  Lemma fn_sheaf_glue :
    forall (U : set X) (HU : is_open TX U)
           (cover : list (set X))
           (cover_open : forall V, In V cover -> is_open TX V)
           (cover_sub  : forall V, In V cover -> forall x, V x -> U x)
           (cover_all  : forall x, U x -> exists V, In V cover /\ V x)
           (secs : forall V, In V cover ->
                  forall (HV : is_open TX V),
                  psf_sec (fn_presheaf TX GA) V HV),
      (forall V W (HVin : In V cover) (HWin : In W cover)
           (HV : is_open TX V) (HW : is_open TX W)
           (HVW : is_open TX (fun x => V x /\ W x)),
         psf_res (fn_presheaf TX GA) (fun x => V x /\ W x) V
           HVW HV (fun x h => proj1 h) (secs V HVin HV) =
         psf_res (fn_presheaf TX GA) (fun x => V x /\ W x) W
           HVW HW (fun x h => proj2 h) (secs W HWin HW)) ->
      exists (s : psf_sec (fn_presheaf TX GA) U HU),
        forall V (HVin : In V cover) (HV : is_open TX V)
               (hVU : forall x, V x -> U x),
          psf_res (fn_presheaf TX GA) V U HV HU hVU s = secs V HVin HV.
  Proof.
    intros U HU cover cover_open cover_sub cover_all secs Hcompat.
    (* Define the global section using indefinite description to
       extract a chosen cover element at each point. *)
    set (P := fun (p : { x : X | U x }) (V : set X) =>
                In V cover /\ V (proj1_sig p)).
    assert (existsP : forall p : { x : X | U x }, exists V, P p V).
    { intros [x Hx]. unfold P; cbn.
      destruct (cover_all x Hx) as [V [HV HxV]]. exists V; split; assumption. }
    pose (choose := fun p =>
        constructive_indefinite_description (P p) (existsP p)).
    refine (ex_intro _ (fun p =>
      let V  := proj1_sig (choose p) in
      let HV_in := proj1 (proj2_sig (choose p)) in
      let HxV   := proj2 (proj2_sig (choose p)) in
      secs V HV_in (cover_open V HV_in)
           (exist _ (proj1_sig p) HxV)) _).
    intros V HVin HV hVU.
    (* Show fn_res s = secs V HVin HV pointwise. *)
    extensionality q. destruct q as [x Hx].
    cbn.
    (* Let W be the chosen cover element at the point (x, hVU x Hx). *)
    set (q' := exist (fun x => U x) x (hVU x Hx) : { y : X | U y }).
    destruct (choose q') as [W [HWin HxW]] eqn:Eq. cbn.
    cbn in HxW. (* HxW : W x *)
    (* The compatibility on overlap V ∩ W lets us replace
       secs W (x, HxW) with secs V (x, Hx). *)
    pose (HW := cover_open W HWin).
    assert (HVW : is_open TX (fun y => V y /\ W y)).
    { exact (open_inter X TX V W HV HW). }
    specialize (Hcompat V W HVin HWin HV HW HVW).
    apply (f_equal (fun (f : fn_sec TX (fun y => V y /\ W y) HVW) =>
              f (exist _ x (conj Hx HxW)))) in Hcompat.
    cbn in Hcompat.
    (* Hcompat : secs V HVin HV (exist V x Hx) = secs W HWin HW (exist W x HxW)
       Goal:    secs W HWin (cover_open W HWin) (exist W x HxW)
              = secs V HVin HV (exist V x Hx)                                *)
    symmetry.
    unfold HW in Hcompat.
    (* All the differing arguments are propositional, so fold the
       projections by proof_irrelevance. *)
    rewrite (proof_irrelevance _ (proj1 (conj HWin HxW)) HWin).
    rewrite (proof_irrelevance _ (proj2 (conj HWin HxW)) HxW).
    rewrite (proof_irrelevance _ (proj1 (conj Hx HxW)) Hx) in Hcompat.
    rewrite (proof_irrelevance _ (proj2 (conj Hx HxW)) HxW) in Hcompat.
    exact Hcompat.
  Qed.

  (** The function presheaf is a sheaf. *)
  Definition fn_sheaf : Sheaf X TX :=
    {| shf_ps    := fn_presheaf TX GA
     ; shf_local := fn_sheaf_local
     ; shf_glue  := fn_sheaf_glue
    |}.

End FunctionSheaf.

(* ================================================================== *)
(** * Concrete instances                                                *)
(* ================================================================== *)

(** The constant integer sheaf as a [Sheaf X TX]: a real witness, not
    a degenerate placeholder, for the hitherto-axiomatized
    [Sheaves.const_sheaf TX Z Z_group]. Sections over U are arbitrary
    Z-valued functions on U; this contains the locally-constant
    Z-sheaf as a sub-sheaf. *)
Definition Z_function_sheaf {X : Type} (TX : Topology X) : Sheaf X TX :=
  fn_sheaf TX Z_group.
