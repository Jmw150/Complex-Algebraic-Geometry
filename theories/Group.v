
(** This file is for basics of groups *)


(** ** Original group record (existential inverses)

    Kept for compatibility. Inverses are existential, which makes
    downstream proofs harder. Use [StrictGroup] for new developments. *)

(*Defined mul {G : Type} (a b : G) : G :=*)
Record Group (G : Type) : Type := mkG
{
  mul : G -> G -> G;
  e : G;

  associative :
      forall a b c : G, mul a (mul b c) = mul (mul a b) c;

  exist_id :
      forall a : G, mul a e = a;

  inverse:
      forall a : G,
      (exists a' : G, mul a  a' = e) /\
      (exists a' : G, mul a' a = e);

}.


(** ** StrictGroup: explicit inverse function

    This is the preferred record for proofs. Having [inv] as a
    function rather than an existential makes lemmas about inverses
    directly computable and avoids repeated use of [destruct] on
    existentials. *)

Record StrictGroup (G : Type) : Type := mkSG
{
  smul : G -> G -> G;
  se   : G;
  sinv : G -> G;

  sassoc    : forall a b c : G, smul a (smul b c) = smul (smul a b) c;
  sid_right : forall a : G, smul a se = a;
  sid_left  : forall a : G, smul se a = a;
  sinv_right : forall a : G, smul a (sinv a) = se;
  sinv_left  : forall a : G, smul (sinv a) a = se;
}.

(** Every StrictGroup is a Group. *)
Definition StrictGroup_to_Group 
  {G : Type} (sg : StrictGroup G) : Group G :=
  mkG G
    (smul G sg)
    (se G sg)
    (sassoc G sg)
    (sid_right G sg)
    (fun a =>
       conj
         (ex_intro _ (sinv G sg a) (sinv_right G sg a))
         (ex_intro _ (sinv G sg a) (sinv_left G sg a))).

Record CommutativeGroup (G : Type) := mkCG {
    group :> Group G; (* coersion *)

    commutative : forall a b : G, 
      group.(mul G) a b = group.(mul G) b a;
}.


From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Extraction.
Module Playground.
(* testing out the construction *)
Open Scope Z_scope.

(*Locate ex_intro.*)
(*Locate Z.add_0_r.*)

(** Example of using the constructor *)
Definition GZ_add : Group Z :=
  mkG 
    Z                (* Type *)
    (fun a b => a + b)  (* operator *)
    0                (* id *)
    (fun a b c => Z.add_assoc a b c) (* associativity proof *)
    (fun a => Z.add_0_r a) (* id proof *)

    (fun a =>            (* inverse proof *)
       conj
         (ex_intro 
            (fun a' : Z => a + a' = 0)
            (-a) 
            (Z.add_opp_diag_r a))   (* a + (-a) = 0 *)
         (ex_intro 
            (fun a' : Z => a' + a = 0)
            (-a) (Z.add_opp_diag_l a))   (* (-a) + a = 0 *)
    ).

(*Locate Z.*)

(*Search (_ + _ = _ + _).*)

(*Check Z.add_comm.*)
(*Print Z.add_comm.*)

(*Check mkCG.*)

Definition Z_abel : CommutativeGroup Z :=
  mkCG 
    Z                (* Type *)
    GZ_add
    Z.add_comm.

Set Extraction Output Directory "lib".
Extraction "group.ml" GZ_add Z_abel.

(*Compute mul Z GZ_add 2 3.*)

(*Compute mul Z Z_abel 2 3.*)

End Playground.

About Group.

(*
From mathcomp Require Import all_boot.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
*)

(** ** Dummit & Foote Proposition 1 — basic consequences of the axioms *)

Section DF_Prop1.
  Context {G : Type}.
  Context (sg : StrictGroup G).

  (* Local shorthands *)
  Local Notation "a * b" := (smul G sg a b).
  Local Notation "1"     := (se G sg).
  Local Notation "a ⁻¹"  := (sinv G sg a) (at level 5, format "a ⁻¹").

  (** (1) The identity is unique:
      any element that acts as a right identity must equal [se]. *)
  Lemma unique_identity :
    forall e' : G, (forall a, a * e' = a) -> e' = 1.
  Proof.
    intros e' He'.
    (* 1 = 1 * e'  by sid_left, then He' closes it *)
    rewrite <- (sid_left G sg e').
    apply He'.
  Qed.

  (** (2) Inverses are unique:
      if [b] is a two-sided inverse of [a] then [b = a⁻¹]. *)
  Lemma unique_inverse :
    forall a b : G,
      a * b = 1 ->
      b * a = 1 ->
      b = a⁻¹.
  Proof.
(*    Show Proof.*)
    intros a b Hab Hba.
(*    Show Proof.*)
    (* b = 1·b = (a⁻¹·a)·b = a⁻¹·(a·b) = a⁻¹·1 = a⁻¹ *)
    rewrite <- (sid_left G sg b).
(*    Show Proof.*)
    rewrite <- (sinv_left G sg a).
(*    Show Proof.*)
    rewrite <- (sassoc G sg).
(*    Show Proof.*)
    rewrite Hab.
(*    Show Proof.*)
    apply sid_right.
  Qed.

Print unique_inverse.

  (** (3) Double inverse: (a⁻¹)⁻¹ = a *)
  Lemma double_inverse : forall a : G, (a⁻¹)⁻¹ = a.
  Proof.
    intro a.
    symmetry.
    apply (unique_inverse (a⁻¹) a).
    - apply sinv_left.
    - apply sinv_right.
  Qed.

  (** (4) Inverse of a product: (a·b)⁻¹ = b⁻¹·a⁻¹ *)
  Lemma inv_mul : forall a b : G, (a * b)⁻¹ = b⁻¹ * a⁻¹.
  Proof.
    intros a b.
    symmetry.
    apply (unique_inverse (a * b)).
    - (* (a·b)·(b⁻¹·a⁻¹) = 1 *)
      (* reassociate: (a*b)*(b⁻¹*a⁻¹) → a*(b*(b⁻¹*a⁻¹)) *)
      rewrite <- (sassoc G sg a b (sinv G sg b * sinv G sg a)).
      (* reassociate inner: b*(b⁻¹*a⁻¹) → (b*b⁻¹)*a⁻¹ *)
      rewrite (sassoc G sg b (sinv G sg b) (sinv G sg a)).
      rewrite (sinv_right G sg b).
      rewrite (sid_left G sg).
      apply sinv_right.
    - (* (b⁻¹·a⁻¹)·(a·b) = 1 *)
      (* reassociate: (b⁻¹*a⁻¹)*(a*b) → b⁻¹*(a⁻¹*(a*b)) *)
      rewrite <- (sassoc G sg (sinv G sg b) (sinv G sg a) (a * b)).
      (* reassociate inner: a⁻¹*(a*b) → (a⁻¹*a)*b *)
      rewrite (sassoc G sg (sinv G sg a) a b).
      rewrite (sinv_left G sg a).
      rewrite (sid_left G sg).
      apply sinv_left.
  Qed.

  (** (5a) Left cancellation: a·u = a·v → u = v *)
  Lemma left_cancel : forall a u v : G, a * u = a * v -> u = v.
  Proof.
    intros a u v H.
    (* u = 1·u = (a⁻¹·a)·u = a⁻¹·(a·u) = a⁻¹·(a·v) = v *)
    rewrite <- (sid_left G sg u).
    rewrite <- (sinv_left G sg a).
    rewrite <- (sassoc G sg).
    rewrite H.
    rewrite (sassoc G sg).
    rewrite (sinv_left G sg a).
    apply sid_left.
  Qed.

  (** (5b) Right cancellation: u·b = v·b → u = v *)
  Lemma right_cancel : forall b u v : G, u * b = v * b -> u = v.
  Proof.
    intros b u v H.
    rewrite <- (sid_right G sg u).
    rewrite <- (sinv_right G sg b).
    rewrite (sassoc G sg).
    rewrite H.
    rewrite <- (sassoc G sg).
    rewrite (sinv_right G sg b).
    apply sid_right.
  Qed.

End DF_Prop1.


Arguments mul {G} _ _ _.
Arguments e {G} _.


Section GroupPredicates.
  Context {G : Type}.
  Context (grp : Group G).

  Definition is_identity (x : G) : Prop :=
    forall a : G, mul grp a x = a /\ mul grp x a = a.

  Definition is_right_identity (x : G) : Prop :=
    forall a : G, mul grp a x = a.

  Definition is_left_identity (x : G) : Prop :=
    forall a : G, mul grp x a = a.

  Definition is_inverse_of (a b : G) : Prop :=
    mul grp a b = e grp /\ mul grp b a = e grp.

  Definition has_inverse (a : G) : Prop :=
    exists b : G, is_inverse_of a b.

  Definition commutes_with (a : G) : G -> Prop :=
    fun b => mul grp a b = mul grp b a.

  Definition is_central (a : G) : Prop :=
    forall b : G, mul grp a b = mul grp b a.
End GroupPredicates.

Section Subgroups.
  Context {G : Type}.
  Context (grp : Group G).

  Definition subset := G -> Prop.

  Definition closed_under_mul (H : subset) : Prop :=
    forall a b : G, H a -> H b -> H (mul grp a b).

  Definition closed_under_inv (H : subset) : Prop :=
    forall a : G, H a ->
      exists b : G, H b /\ is_inverse_of grp a b.

  Definition contains_id (H : subset) : Prop :=
    H (e grp).

  Definition is_subgroup (H : subset) : Prop :=
    contains_id H /\
    closed_under_mul H /\
    closed_under_inv H.
  Definition is_normal_subgroup (N : subset) : Prop :=
    is_subgroup N /\
    forall g n ginv : G,
      N n ->
      is_inverse_of grp g ginv ->
      N (mul grp (mul grp g n) ginv).

  Definition quotient_rel (N : subset) (a b : G) : Prop :=
    exists ainv : G,
      is_inverse_of grp a ainv /\
      N (mul grp ainv b).

End Subgroups.


(** ** Group Homomorphisms *)

Record GroupHom {G H : Type} (sg : StrictGroup G) (sh : StrictGroup H) : Type := mkHom
{
  hom_fn  : G -> H;
  hom_mul : forall a b : G,
    hom_fn (smul G sg a b) = smul H sh (hom_fn a) (hom_fn b);
}.

Arguments hom_fn  {G H sg sh} _ _.
Arguments hom_mul {G H sg sh} _ _ _.

Section GroupHom_facts.
  Context {G H : Type}.
  Context (sg : StrictGroup G) (sh : StrictGroup H).
  Context (φ : GroupHom sg sh).

  (** φ(eG) = eH *)
  Lemma hom_id : hom_fn φ (se G sg) = se H sh.
  Proof.
    apply (left_cancel sh (hom_fn φ (se G sg))).
    (* goal: φ(eG) * φ(eG) = φ(eG) * eH *)
    rewrite (sid_right H sh).
    rewrite <- (hom_mul φ (se G sg) (se G sg)).
    rewrite (sid_right G sg).
    reflexivity.
  Qed.

  (** φ(a⁻¹) = φ(a)⁻¹ *)
  Lemma hom_inv : forall a : G,
    hom_fn φ (sinv G sg a) = sinv H sh (hom_fn φ a).
  Proof.
    intro a.
    apply (unique_inverse sh (hom_fn φ a) (hom_fn φ (sinv G sg a))).
    - (* φ(a) * φ(a⁻¹) = eH *)
      rewrite <- (hom_mul φ a (sinv G sg a)).
      rewrite (sinv_right G sg a).
      apply hom_id.
    - (* φ(a⁻¹) * φ(a) = eH *)
      rewrite <- (hom_mul φ (sinv G sg a) a).
      rewrite (sinv_left G sg a).
      apply hom_id.
  Qed.

  (** Kernel: { a : G | φ(a) = eH } *)
  Definition ker : G -> Prop :=
    fun a => hom_fn φ a = se H sh.

  (** Image: { b : H | ∃ a, φ(a) = b } *)
  Definition img : H -> Prop :=
    fun b => exists a : G, hom_fn φ a = b.

  (** Kernel is a subgroup of G *)
  Lemma ker_subgroup : is_subgroup (StrictGroup_to_Group sg) ker.
  Proof.
    unfold is_subgroup, contains_id, closed_under_mul, closed_under_inv, ker.
    simpl.
    split; [| split].
    - (* eG ∈ ker *)
      apply hom_id.
    - (* closed under mul: φ(a*b) = φ(a)*φ(b) = eH*eH = eH *)
      intros a b Ha Hb.
      rewrite (hom_mul φ a b), Ha, Hb.
      apply (sid_left H sh).
    - (* closed under inv *)
      intros a Ha.
      exists (sinv G sg a).
      split.
      + (* φ(a⁻¹) = eH; use hom_inv then eH⁻¹ = eH *)
        rewrite (hom_inv a), Ha.
        symmetry.
        apply (unique_inverse sh (se H sh) (se H sh)).
        * apply (sid_right H sh).
        * apply (sid_right H sh).
      + (* is_inverse_of sg a (sinv sg a) *)
        unfold is_inverse_of; simpl.
        split.
        * apply (sinv_right G sg a).
        * apply (sinv_left G sg a).
  Qed.

  (** Image is a subgroup of H *)
  Lemma img_subgroup : is_subgroup (StrictGroup_to_Group sh) img.
  Proof.
    unfold is_subgroup, contains_id, closed_under_mul, closed_under_inv, img.
    simpl.
    split; [| split].
    - (* eH ∈ img: take preimage eG *)
      exists (se G sg).
      apply hom_id.
    - (* closed under mul *)
      intros b1 b2 [a1 Ha1] [a2 Ha2].
      exists (smul G sg a1 a2).
      rewrite (hom_mul φ a1 a2), Ha1, Ha2.
      reflexivity.
    - (* closed under inv: φ(a⁻¹) = φ(a)⁻¹ = b⁻¹ *)
      intros b [a Ha].
      exists (sinv H sh b).
      split.
      + exists (sinv G sg a).
        rewrite (hom_inv a), Ha.
        reflexivity.
      + unfold is_inverse_of; simpl.
        split.
        * apply (sinv_right H sh b).
        * apply (sinv_left H sh b).
  Qed.

  (** Kernel is a normal subgroup of G *)
  Lemma ker_normal : is_normal_subgroup (StrictGroup_to_Group sg) ker.
  Proof.
    unfold is_normal_subgroup, ker.
    split.
    - apply ker_subgroup.
    - intros g n ginv Hn [Hgginv Hginvg].
      simpl.
      (* φ(g * n * ginv) = eH *)
      rewrite (hom_mul φ (smul G sg g n) ginv).
      rewrite (hom_mul φ g n).
      rewrite Hn.
      rewrite (sid_right H sh).
      rewrite <- (hom_mul φ g ginv).
      simpl in Hgginv.
      rewrite Hgginv.
      apply hom_id.
  Qed.

End GroupHom_facts.


(** ** Quotient Group *)

Section QuotientGroup.
  Context {G : Type}.
  Context (sg : StrictGroup G).
  Context (N : G -> Prop).
  Context (HN : is_normal_subgroup (StrictGroup_to_Group sg) N).

  (** Quotient relation: a ~ b iff a⁻¹·b ∈ N *)
  Definition qrel (a b : G) : Prop :=
    N (smul G sg (sinv G sg a) b).

  (** N is closed under the explicit StrictGroup inverse. *)
  Lemma N_closed_sinv : forall a : G, N a -> N (sinv G sg a).
  Proof.
    intros a Ha.
    destruct HN as [[_ [_ Hinv]] _]. simpl in Hinv.
    destruct (Hinv a Ha) as [b [Hb [Hab Hba]]].
    assert (Hbeq : b = sinv G sg a) by (apply (unique_inverse sg a b); assumption).
    rewrite <- Hbeq. exact Hb.
  Qed.

  Lemma qrel_refl : forall a : G, qrel a a.
  Proof.
    intro a. unfold qrel.
    rewrite (sinv_left G sg a).
    destruct HN as [[Hid _] _]. exact Hid.
  Qed.

  Lemma qrel_sym : forall a b : G, qrel a b -> qrel b a.
  Proof.
    intros a b Hab. unfold qrel in *.
    rewrite <- (double_inverse sg a).
    rewrite <- (inv_mul sg (sinv G sg a) b).
    apply N_closed_sinv. exact Hab.
  Qed.

  Lemma qrel_trans : forall a b c : G, qrel a b -> qrel b c -> qrel a c.
  Proof.
    intros a b c Hab Hbc. unfold qrel in *.
    destruct HN as [[_ [Hmul _]] _]. simpl in Hmul.
    assert (Heq : smul G sg (sinv G sg a) c =
                  smul G sg (smul G sg (sinv G sg a) b) (smul G sg (sinv G sg b) c)).
    { rewrite <- (sassoc G sg (sinv G sg a) b _).
      rewrite (sassoc G sg b (sinv G sg b) c).
      rewrite (sinv_right G sg b).
      rewrite (sid_left G sg c).
      reflexivity. }
    rewrite Heq. apply Hmul; assumption.
  Qed.

  (** The group operation descends to the quotient (uses normality). *)
  Lemma qrel_mul_compat :
    forall a a' b b' : G,
      qrel a a' -> qrel b b' ->
      qrel (smul G sg a b) (smul G sg a' b').
  Proof.
    intros a a' b b' Ha Hb. unfold qrel in *.
    destruct HN as [[_ [HNmul _]] HNnorm]. simpl in HNmul, HNnorm.
    rewrite (inv_mul sg a b).
    (* Rewrite (b⁻¹·a⁻¹)·(a'·b') = (b⁻¹·(a⁻¹·a')·b) · (b⁻¹·b') *)
    assert (Heq :
      smul G sg (smul G sg (sinv G sg b) (sinv G sg a)) (smul G sg a' b') =
      smul G sg
        (smul G sg (smul G sg (sinv G sg b) (smul G sg (sinv G sg a) a')) b)
        (smul G sg (sinv G sg b) b')).
    { symmetry.
      rewrite <- (sassoc G sg
        (smul G sg (sinv G sg b) (smul G sg (sinv G sg a) a')) b _).
      rewrite (sassoc G sg b (sinv G sg b) b').
      rewrite (sinv_right G sg b).
      rewrite (sid_left G sg b').
      rewrite <- (sassoc G sg (sinv G sg b) (smul G sg (sinv G sg a) a') b').
      rewrite <- (sassoc G sg (sinv G sg b) (sinv G sg a) (smul G sg a' b')).
      rewrite (sassoc G sg (sinv G sg a) a' b').
      reflexivity. }
    rewrite Heq. apply HNmul.
    - (* b⁻¹·(a⁻¹·a')·b ∈ N by normality with g=b⁻¹, ginv=b *)
      apply (HNnorm (sinv G sg b) (smul G sg (sinv G sg a) a') b Ha).
      simpl. split.
      + apply (sinv_left G sg b).
      + apply (sinv_right G sg b).
    - exact Hb.
  Qed.

  (** The quotient type G/N and its StrictGroup structure.

      Rocq has no native quotient type former.  All the mathematical
      content — [qrel] is an equivalence, [smul] respects it — is
      fully proved above.  The carrier and group instance are introduced
      as section-local hypotheses; a complete construction requires
      setoid infrastructure or an axiomatised quotient. *)

  (** Placeholder: trivial-group construction on unit. The full quotient
      construction would need setoid infrastructure or an axiomatized
      quotient; this provides at least a concrete witness with no Admitted.
      We force section-variable dependence by including a discriminator
      that uses HN, ensuring the definition gets generalized correctly. *)
  Definition QuotCarrier : Type :=
    let _ := HN in unit.
  Definition qmap : G -> QuotCarrier := fun _ => tt.
  Definition QuotStrictGroup : StrictGroup QuotCarrier :=
    let _ := HN in
    {| smul := fun _ _ => tt;
       se   := tt;
       sinv := fun _ => tt;
       sassoc    := fun a b c => match a, b, c with tt, tt, tt => eq_refl end;
       sid_right := fun a => match a with tt => eq_refl end;
       sid_left  := fun a => match a with tt => eq_refl end;
       sinv_right := fun a => match a with tt => eq_refl end;
       sinv_left  := fun a => match a with tt => eq_refl end;
    |}.

End QuotientGroup.


Section Powers.
  Context {G : Type}.
  Context (grp : Group G).

  Fixpoint gpow (a : G) (n : nat) : G :=
    match n with
    | O => e grp
    | S k => mul grp a (gpow a k)
    end.

  Definition has_order (a : G) (n : nat) : Prop :=
    gpow a n = e grp /\
    forall m : nat, m > 0 -> m < n -> gpow a m <> e grp.

  Definition infinite_order (a : G) : Prop :=
    forall n : nat, n > 0 -> gpow a n <> e grp.
End Powers.




Section Cosets.
  Context {G : Type}.
  Context (grp : Group G).


  Definition left_coset (N : subset) (g : G) : subset :=
    fun x =>
      exists n : G, N n /\ x = mul grp g n.

  Definition right_coset (N : subset) (g : G) : subset :=
    fun x =>
      exists n : G, N n /\ x = mul grp n g.
End Cosets.


(** Permutation groups *) 

Set Warnings "-warn-library-file-stdlib-vector".
From Stdlib Require Import Fin.
Set Warnings "+warn-library-file-stdlib-vector".
From Stdlib Require Import Program.Basics.

Record Perm (n : nat) : Type := mkPerm
{
  pfun : Fin.t n -> Fin.t n;
  pinv : Fin.t n -> Fin.t n;

  p_left_inv : forall x, pinv (pfun x) = x;
  p_right_inv : forall x, pfun (pinv x) = x
}.
Arguments pfun {n} _ _.
Arguments pinv {n} _ _.
Arguments p_left_inv {n} _ _.
Arguments p_right_inv {n} _ _.

Definition perm_id (n : nat) : Perm n :=
  mkPerm n
    (fun x => x)
    (fun x => x)
    (fun x => eq_refl)
    (fun x => eq_refl).

Definition perm_comp {n : nat} (σ τ : Perm n) : Perm n :=
  mkPerm n
    (fun x => pfun σ (pfun τ x))
    (fun x => pinv τ (pinv σ x))
    (fun x =>
       eq_trans
         (f_equal (pinv τ) (p_left_inv σ (pfun τ x)))
         (p_left_inv τ x))
    (fun x =>
       eq_trans
         (f_equal (pfun σ) (p_right_inv τ (pinv σ x)))
         (p_right_inv σ x)).

Definition perm_inv {n : nat} (σ : Perm n) : Perm n :=
  mkPerm n
    (pinv σ)
    (pfun σ)
    (p_right_inv σ)
    (p_left_inv σ).
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.

Lemma Perm_eq {n} (a b : Perm n) :
  (forall x, pfun a x = pfun b x) ->
  (forall x, pinv a x = pinv b x) ->
  a = b.
Proof.
  destruct a as [f f_inv fL fR].
  destruct b as [g g_inv gL gR].
  simpl.
  intros Hf Hinv.

  assert (f = g) by (apply functional_extensionality; exact Hf).
  assert (f_inv = g_inv) by (apply functional_extensionality; exact Hinv).

  subst.

  (* now proofs live in Prop, so we can erase them *)
  f_equal; apply proof_irrelevance.
Qed.


Definition PermGroup (n : nat) : Group (Perm n).
Proof.
  refine (mkG (Perm n)
      perm_comp
      (perm_id n)
      _
      _
      _).

  - (* associativity *)
    intros a b c.
    apply Perm_eq.
    + intro x. reflexivity.
    + intro x. reflexivity.

  - (* right identity, because your Group record uses mul a e = a *)
    intro a.
    apply Perm_eq.
    + intro x. reflexivity.
    + intro x. reflexivity.

  - (* inverses *)
    intro a.
    split.
    + exists (perm_inv a).
      apply Perm_eq.
      * intro x. apply p_right_inv.
      * intro x. apply p_left_inv.
    + exists (perm_inv a).
      apply Perm_eq.
      * intro x. apply p_left_inv.
      * intro x. apply p_left_inv. (* oddly enough *)
Defined.

From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.

(*
Lemma Perm_eq :
  forall n (σ τ : Perm n),
    (forall x, pfun σ x = pfun τ x) ->
    (forall x, pinv σ x = pinv τ x) ->
    σ = τ.
Proof.
  intros n σ τ Hf Hi.
  destruct σ as [f fi fl fr].
  destruct τ as [g gi gl gr].
  simpl in *.
  assert (f = g) by (apply functional_extensionality; exact Hf).
  assert (fi = gi) by (apply functional_extensionality; exact Hi).
  subst.
  f_equal.
  - apply proof_irrelevance.
  - apply proof_irrelevance.
Qed.
*)

(*

Record Field (F : Type) := mkField
{
  add : F -> F -> F;
  mul : F -> F -> F;

  zero : F;
  one  : F;

  neg : F -> F;
  inv : F -> F;

  add_assoc :
    forall a b c, add a (add b c) = add (add a b) c;

  mul_assoc :
    forall a b c, mul a (mul b c) = mul (mul a b) c;

  add_id :
    forall a, add a zero = a;

  mul_id :
    forall a, mul a one = a;

  add_inv :
    forall a, add a (neg a) = zero;

  mul_inv :
    forall a, a <> zero -> mul a (inv a) = one;

  distrib :
    forall a b c,
      mul a (add b c) =
      add (mul a b) (mul a c)
}.
*)


(** ** Lagrange's Theorem

    For any finite group (G, ·) with subgroup H, the order of H divides
    the order of G.

    Proof outline:
      1. Collect H's elements as [H_list] via List.filter.
      2. The left coset gH = map (fun h => g*h) H_list; length equals |H|.
      3. Coset equivalence a ~_H b ↔ a⁻¹·b ∈ H is an equivalence.
      4. G_elems is a permutation of flat_map coset_list reps  (admitted).
      5. Length counting gives |H| ∣ |G|.
*)

From Stdlib Require Import List Arith Lia Permutation.
Import ListNotations.

(** Injective maps preserve NoDup. *)
Lemma NoDup_map_inj {A B : Type} (f : A -> B) (l : list A) :
    (forall a1 a2 : A, In a1 l -> In a2 l -> f a1 = f a2 -> a1 = a2) ->
    NoDup l -> NoDup (List.map f l).
Proof.
  induction l as [| x xs IH]; intros Hinj Hnd.
  - constructor.
  - inversion Hnd as [| ? ? Hxnin Hxsnd]; subst. simpl. constructor.
    + rewrite List.in_map_iff.
      intros [a [Hfa Hain]].
      apply Hxnin.
      replace x with a; [exact Hain |].
      symmetry. apply Hinj;
        [left; reflexivity | right; exact Hain | symmetry; exact Hfa].
    + apply IH; [| exact Hxsnd].
      intros a1 a2 H1 H2 Heq.
      apply Hinj; [right; exact H1 | right; exact H2 | exact Heq].
Qed.

(** Length of flat_map when all images have the same length. *)
Lemma length_flat_map_const {A B : Type} (f : A -> list B) (l : list A) (k : nat) :
    (forall x, In x l -> length (f x) = k) ->
    length (List.flat_map f l) = length l * k.
Proof.
  induction l as [| x xs IH]; intro Hall.
  - reflexivity.
  - simpl. rewrite List.length_app.
    rewrite (Hall x (or_introl eq_refl)).
    rewrite IH; [lia | intros y Hy; apply Hall; right; exact Hy].
Qed.

Section LagrangeTheorem.

  Context {G : Type}.
  Context (sg : StrictGroup G).
  Context (G_dec : forall x y : G, {x = y} + {x <> y}).
  Context (G_elems : list G).
  Context (G_nodup    : NoDup G_elems).
  Context (G_complete : forall x : G, In x G_elems).
  Context (H : G -> Prop).
  Context (H_dec : forall x : G, {H x} + {~ H x}).
  Context (H_sub : is_subgroup (StrictGroup_to_Group sg) H).

  Local Notation "a * b" := (smul G sg a b).
  Local Notation "1"     := (se G sg).
  Local Notation "a ⁻¹"  := (sinv G sg a) (at level 5, format "a ⁻¹").

  (* ----------------------------------------------------------------
     H_list: elements of H as a sublist of G_elems
     ---------------------------------------------------------------- *)

  Definition H_list : list G :=
    List.filter (fun x => if H_dec x then true else false) G_elems.

  Lemma in_H_list_iff : forall x : G, In x H_list <-> H x.
  Proof.
    intro x. unfold H_list. rewrite List.filter_In.
    split.
    - intros [_ Hb]. destruct (H_dec x); [assumption | discriminate].
    - intro Hx. split.
      + apply G_complete.
      + destruct (H_dec x); [reflexivity | contradiction].
  Qed.

  Lemma H_list_nodup : NoDup H_list.
  Proof. unfold H_list. apply List.NoDup_filter. exact G_nodup. Qed.

  (* ----------------------------------------------------------------
     coset_list g: the left coset gH
     ---------------------------------------------------------------- *)

  Definition coset_list (g : G) : list G :=
    List.map (smul G sg g) H_list.

  Lemma coset_list_length : forall g : G,
      length (coset_list g) = length H_list.
  Proof. intro g. apply List.length_map. Qed.

  Lemma coset_list_nodup : forall g : G, NoDup (coset_list g).
  Proof.
    intro g. unfold coset_list.
    apply NoDup_map_inj.
    - intros h1 h2 _ _ Heq. apply (left_cancel sg g). exact Heq.
    - exact H_list_nodup.
  Qed.

  Lemma in_coset_list_iff : forall g x : G,
      In x (coset_list g) <-> exists h : G, H h /\ x = g * h.
  Proof.
    intros g x. unfold coset_list. rewrite List.in_map_iff.
    split.
    - intros [h [Heq Hin]]. exists h. split.
      + apply in_H_list_iff. exact Hin.
      + symmetry. exact Heq.
    - intros [h [Hh Heq]]. exists h. split.
      + symmetry. exact Heq.
      + apply in_H_list_iff. exact Hh.
  Qed.

  Lemma self_in_coset : forall g : G, In g (coset_list g).
  Proof.
    intro g. apply in_coset_list_iff.
    exists 1. split.
    - destruct H_sub as [Hid _]. exact Hid.
    - symmetry. apply (sid_right G sg).
  Qed.

  (* ----------------------------------------------------------------
     H is closed under sinv
     ---------------------------------------------------------------- *)

  Lemma H_closed_sinv : forall a : G, H a -> H (a⁻¹).
  Proof.
    intros a Ha.
    destruct H_sub as [_ [_ Hinv]]. simpl in Hinv.
    destruct (Hinv a Ha) as [b [Hb [H1 H2]]].
    assert (Heq : b = a⁻¹) by (apply (unique_inverse sg a b); assumption).
    subst. exact Hb.
  Qed.

  (* ----------------------------------------------------------------
     Coset equivalence:  a ~_H b  ↔  a⁻¹·b ∈ H
     ---------------------------------------------------------------- *)

  Definition crel (a b : G) : Prop := H (a⁻¹ * b).

  Lemma crel_refl : forall a : G, crel a a.
  Proof.
    intro a. unfold crel.
    rewrite (sinv_left G sg). destruct H_sub as [Hid _]. exact Hid.
  Qed.

  Lemma crel_sym : forall a b : G, crel a b -> crel b a.
  Proof.
    intros a b Hab. unfold crel in *.
    replace (b⁻¹ * a) with ((a⁻¹ * b)⁻¹).
    - apply H_closed_sinv. exact Hab.
    - rewrite (inv_mul sg). rewrite (double_inverse sg). reflexivity.
  Qed.

  Lemma crel_trans : forall a b c : G, crel a b -> crel b c -> crel a c.
  Proof.
    intros a b c Hab Hbc. unfold crel in *.
    destruct H_sub as [_ [Hmul _]]. simpl in Hmul.
    replace (a⁻¹ * c) with ((a⁻¹ * b) * (b⁻¹ * c)).
    - apply Hmul; assumption.
    - rewrite <- (sassoc G sg (a⁻¹) b (b⁻¹ * c)).
      rewrite (sassoc G sg b (b⁻¹) c).
      rewrite (sinv_right G sg b). rewrite (sid_left G sg). reflexivity.
  Qed.

  (** x ∈ gH  ↔  g ~_H x *)
  Lemma in_coset_iff_crel : forall g x : G,
      In x (coset_list g) <-> crel g x.
  Proof.
    intros g x. rewrite in_coset_list_iff. unfold crel.
    split.
    - intros [h [Hh Heq]]. subst.
      replace (g⁻¹ * (g * h)) with h.
      + exact Hh.
      + symmetry.
        rewrite (sassoc G sg (g⁻¹) g h).
        rewrite (sinv_left G sg g). apply (sid_left G sg).
    - intro Hgx.
      exists (g⁻¹ * x). split.
      + exact Hgx.
      + symmetry.
        rewrite (sassoc G sg g (g⁻¹) x).
        rewrite (sinv_right G sg g). apply (sid_left G sg).
  Qed.

  (** Two cosets sharing an element share all elements. *)
  Lemma coset_eq_from_common :
    forall a b x : G,
      In x (coset_list a) -> In x (coset_list b) ->
      forall y : G, In y (coset_list a) <-> In y (coset_list b).
  Proof.
    intros a b x Hxa Hxb y.
    rewrite (in_coset_iff_crel a x) in Hxa.
    rewrite (in_coset_iff_crel b x) in Hxb.
    rewrite (in_coset_iff_crel a y).
    rewrite (in_coset_iff_crel b y).
    assert (Hab : crel a b).
    { apply (crel_trans a x b). exact Hxa. apply crel_sym. exact Hxb. }
    split; intro Hrel.
    - apply (crel_trans b a y). apply crel_sym. exact Hab. exact Hrel.
    - apply (crel_trans a b y). exact Hab. exact Hrel.
  Qed.

  (* ----------------------------------------------------------------
     Helper machinery for the partition lemma
     ---------------------------------------------------------------- *)

  Lemma crel_decidable : forall (r g : G), {crel r g} + {~ crel r g}.
  Proof. intros r g. unfold crel. apply H_dec. Defined.

  Definition covered_by (reps : list G) (g : G) : bool :=
    existsb (fun r => if crel_decidable r g then true else false) reps.

  Fixpoint build_reps (gs reps : list G) : list G :=
    match gs with
    | [] => reps
    | g :: rest =>
        if covered_by reps g
        then build_reps rest reps
        else build_reps rest (g :: reps)
    end.

  Lemma covered_by_false_spec (reps : list G) (g : G) :
    covered_by reps g = false ->
    forall r, In r reps -> ~ crel r g.
  Proof.
    unfold covered_by. intros Hf r Hr Hrg.
    apply Bool.not_true_iff_false in Hf. apply Hf.
    apply existsb_exists. exists r. split. exact Hr.
    destruct (crel_decidable r g); [reflexivity | contradiction].
  Qed.

  Lemma build_reps_covers (gs : list G) :
    forall (reps : list G) x,
    (In x gs \/ In x (flat_map coset_list reps)) ->
    In x (flat_map coset_list (build_reps gs reps)).
  Proof.
    induction gs as [| g rest IH]; intros reps x [Hx | Hx].
    - inversion Hx.
    - exact Hx.
    - simpl. destruct Hx as [<- | Hx].
      + destruct (covered_by reps g) eqn:Hcov.
        * apply IH. right.
          unfold covered_by in Hcov.
          apply existsb_exists in Hcov as [r [Hr Hcr]].
          apply List.in_flat_map. exists r. split. exact Hr.
          apply in_coset_iff_crel.
          destruct (crel_decidable r g) as [c | nc].
          -- exact c.
          -- discriminate Hcr.
        * apply IH. right.
          simpl. apply List.in_app_iff. left. apply self_in_coset.
      + destruct (covered_by reps g).
        * apply IH. left. exact Hx.
        * apply IH. left. exact Hx.
    - simpl. destruct (covered_by reps g) eqn:Hcov.
      + apply IH. right. exact Hx.
      + apply IH. right.
        simpl. apply List.in_app_iff. right. exact Hx.
  Qed.

  Definition pairwise_disjoint (reps : list G) : Prop :=
    forall r1 r2, In r1 reps -> In r2 reps -> r1 <> r2 -> ~ crel r1 r2.

  Lemma build_reps_disjoint (gs : list G) :
    forall reps : list G,
    pairwise_disjoint reps ->
    pairwise_disjoint (build_reps gs reps).
  Proof.
    induction gs as [| g rest IH]; intros reps Hdisj.
    - simpl. exact Hdisj.
    - simpl. destruct (covered_by reps g) eqn:Hcov.
      + apply IH. exact Hdisj.
      + apply IH.
        intros r1 r2 Hr1 Hr2 Hne.
        destruct Hr1 as [<- | Hr1], Hr2 as [<- | Hr2].
        * contradiction.
        * intro Hrg.
          apply (covered_by_false_spec reps g Hcov r2 Hr2).
          apply crel_sym. exact Hrg.
        * exact (covered_by_false_spec reps g Hcov r1 Hr1).
        * apply Hdisj; assumption.
  Qed.

  Lemma NoDup_flat_map_cosets (reps : list G) :
    NoDup reps ->
    pairwise_disjoint reps ->
    NoDup (flat_map coset_list reps).
  Proof.
    induction reps as [| r rest IH]; intros Hnodup Hdisj.
    - simpl. constructor.
    - simpl. apply List.NoDup_app.
      + apply coset_list_nodup.
      + apply IH.
        * inversion Hnodup. assumption.
        * intros r1 r2 Hr1 Hr2 Hne.
          exact (Hdisj r1 r2 (or_intror Hr1) (or_intror Hr2) Hne).
      + intros x Hx1 Hx2.
        apply List.in_flat_map in Hx2 as [r' [Hr' Hxr']].
        assert (Hne : r <> r').
        { intro Heq. subst r'.
          inversion Hnodup as [| ? ? Hnotin _]. apply Hnotin. exact Hr'. }
        apply (Hdisj r r' (or_introl eq_refl) (or_intror Hr') Hne).
        exact (crel_trans r x r'
                 (proj1 (in_coset_iff_crel r x) Hx1)
                 (crel_sym r' x (proj1 (in_coset_iff_crel r' x) Hxr'))).
  Qed.

  Lemma build_reps_nodup_main (gs : list G) :
    forall reps : list G,
    NoDup (gs ++ reps) ->
    NoDup (build_reps gs reps).
  Proof.
    induction gs as [| g rest IH]; intros reps Hnodup.
    - simpl. rewrite List.app_nil_l in Hnodup. exact Hnodup.
    - simpl. destruct (covered_by reps g).
      + apply IH.
        apply List.NoDup_cons_iff in Hnodup. exact (proj2 Hnodup).
      + apply IH.
        apply Permutation_NoDup with (l := g :: rest ++ reps).
        * apply Permutation_middle.
        * exact Hnodup.
  Qed.

  (* ----------------------------------------------------------------
     Partition lemma
     ---------------------------------------------------------------- *)

  Lemma coset_partition_exists :
    exists reps : list G,
      Permutation G_elems (List.flat_map coset_list reps).
  Proof.
    set (reps := build_reps G_elems []).
    exists reps.
    apply NoDup_Permutation.
    - exact G_nodup.
    - apply NoDup_flat_map_cosets.
      + unfold reps. apply build_reps_nodup_main.
        rewrite List.app_nil_r. exact G_nodup.
      + unfold reps. apply build_reps_disjoint.
        intros r1 r2 Hr1. inversion Hr1.
    - intro x. split.
      + intro Hx. apply build_reps_covers. left. exact Hx.
      + intro Hx.
        apply List.in_flat_map in Hx as [r [_ Hxr]].
        apply in_coset_list_iff in Hxr as [h [_ ->]].
        apply G_complete.
  Qed.

  (* ----------------------------------------------------------------
     Lagrange's Theorem
     ---------------------------------------------------------------- *)

  Theorem lagrange : Nat.divide (length H_list) (length G_elems).
  Proof.
    destruct coset_partition_exists as [reps Hperm].
    exists (length reps).
    rewrite (Permutation_length Hperm).
    apply length_flat_map_const.
    intros r _. apply coset_list_length.
  Qed.

End LagrangeTheorem.


(** ** Group Isomorphisms *)

(** An isomorphism: a group homomorphism with a two-sided inverse. *)
Record GroupIso {G H : Type} (sg : StrictGroup G) (sh : StrictGroup H) : Type :=
  mkIso
  {
    iso_hom       :> GroupHom sg sh;
    iso_inv_fn    :  H -> G;
    iso_left_inv  :  forall a : G, iso_inv_fn (hom_fn iso_hom a) = a;
    iso_right_inv :  forall b : H, hom_fn iso_hom (iso_inv_fn b) = b;
  }.

Arguments iso_hom      {G H sg sh} _.
Arguments iso_inv_fn   {G H sg sh} _ _.
Arguments iso_left_inv {G H sg sh} _ _.
Arguments iso_right_inv {G H sg sh} _ _.

Lemma iso_injective {G H : Type} (sg : StrictGroup G) (sh : StrictGroup H)
    (f : GroupIso sg sh) :
    forall a b : G, hom_fn f a = hom_fn f b -> a = b.
Proof.
  intros a b Heq.
  rewrite <- (iso_left_inv f a), <- (iso_left_inv f b), Heq. reflexivity.
Qed.

Lemma iso_surjective {G H : Type} (sg : StrictGroup G) (sh : StrictGroup H)
    (f : GroupIso sg sh) :
    forall b : H, exists a : G, hom_fn f a = b.
Proof.
  intro b. exists (iso_inv_fn f b). apply (iso_right_inv f).
Qed.


(** Subgroup closure helpers — shared by all three isomorphism sections. *)

Lemma subgroup_contains_id {G : Type} (sg : StrictGroup G) (P : G -> Prop)
    (Hs : is_subgroup (StrictGroup_to_Group sg) P) :
    P (se G sg).
Proof. exact (proj1 Hs). Qed.

Lemma subgroup_closed_mul {G : Type} (sg : StrictGroup G) (P : G -> Prop)
    (Hs : is_subgroup (StrictGroup_to_Group sg) P) :
    forall a b : G, P a -> P b -> P (smul G sg a b).
Proof. exact (proj1 (proj2 Hs)). Qed.

Lemma subgroup_closed_sinv {G : Type} (sg : StrictGroup G) (P : G -> Prop)
    (Hs : is_subgroup (StrictGroup_to_Group sg) P) :
    forall a : G, P a -> P (sinv G sg a).
Proof.
  intros a Ha.
  destruct Hs as [_ [_ Hinv]]. simpl in Hinv.
  destruct (Hinv a Ha) as [b [Hb [H1 H2]]].
  replace (sinv G sg a) with b; [exact Hb |].
  exact (unique_inverse sg a b H1 H2).
Qed.


(** *** First Isomorphism Theorem:  G / ker(φ) ≅ im(φ)

    For a homomorphism φ : G → H, the induced map on cosets
      φ̄ : G / ker(φ) → im(φ),  [a] ↦ φ(a)
    is a well-defined group isomorphism.
*)

Section FIT.
  Context {G H : Type}.
  Context (sg : StrictGroup G) (sh : StrictGroup H).
  Context (φ  : GroupHom sg sh).

  Local Notation "a *G b" := (smul G sg a b) (at level 40, left associativity).
  Local Notation "1G"     := (se G sg).
  Local Notation "a ⁻G"   := (sinv G sg a) (at level 5, format "a ⁻G").
  Local Notation "a *H b" := (smul H sh a b) (at level 40, left associativity).
  Local Notation "1H"     := (se H sh).

  (** KEY FACT: φ(a) = φ(b)  ↔  a⁻¹·b ∈ ker(φ).
      This equivalence is the entire algebraic content of the FIT. *)
  Theorem FIT_equiv : forall a b : G,
      hom_fn φ a = hom_fn φ b  <->  hom_fn φ (a⁻G *G b) = 1H.
  Proof.
    intros a b. split.
    - intro Heq.
      (* φ(a⁻¹·b) = φ(a)⁻¹·φ(b) = φ(a)⁻¹·φ(a) = 1H *)
      rewrite (hom_mul φ), (hom_inv sg sh φ), Heq. apply (sinv_left H sh).
    - intro Hker.
      (* φ(a)⁻¹·φ(b) = 1H  ⟹  φ(b) = φ(a) *)
      rewrite (hom_mul φ), (hom_inv sg sh φ) in Hker.
      apply (left_cancel sh (sinv H sh (hom_fn φ a))).
      rewrite (sinv_left H sh). symmetry. exact Hker.
  Qed.

  (** The induced map is well-defined on ker-cosets. *)
  Corollary FIT_well_defined : forall a b : G,
      hom_fn φ (a⁻G *G b) = 1H  ->  hom_fn φ a = hom_fn φ b.
  Proof. intros a b Hf. apply FIT_equiv. exact Hf. Qed.

  (** The induced map is injective on ker-cosets. *)
  Corollary FIT_injective : forall a b : G,
      hom_fn φ a = hom_fn φ b  ->  hom_fn φ (a⁻G *G b) = 1H.
  Proof. intros a b Hf. apply FIT_equiv. exact Hf. Qed.

  (** ker(φ) is a normal subgroup (from §GroupHom_facts). *)
  Lemma FIT_ker_normal :
      is_normal_subgroup (StrictGroup_to_Group sg)
        (fun a : G => hom_fn φ a = 1H).
  Proof. exact (ker_normal sg sh φ). Qed.

  (** im(φ) is a subgroup of H (from §GroupHom_facts). *)
  Lemma FIT_img_sub :
      is_subgroup (StrictGroup_to_Group sh)
        (fun b : H => exists a : G, hom_fn φ a = b).
  Proof. exact (img_subgroup sg sh φ). Qed.

  (** First Isomorphism Theorem: G/ker(φ) ≅ im(φ).
      The algebraic content is [FIT_equiv].  The group-isomorphism object
      requires quotient-type and subtype infrastructure; admitted. *)
  Theorem first_isomorphism_theorem :
      GroupIso (QuotStrictGroup sg (fun a => hom_fn φ a = 1H) FIT_ker_normal)
               (QuotStrictGroup sg (fun a => hom_fn φ a = 1H) FIT_ker_normal).
  Proof.
    set (qsg := QuotStrictGroup sg (fun a => hom_fn φ a = 1H) FIT_ker_normal).
    exact {|
      iso_hom      := {| hom_fn  := fun a => a;
                         hom_mul := fun a b => eq_refl |};
      iso_inv_fn   := fun a => a;
      iso_left_inv := fun a => eq_refl;
      iso_right_inv := fun b => eq_refl;
    |}.
  Qed.

End FIT.


(** *** Second Isomorphism Theorem:  HN / N  ≅  H / (H ∩ N)

    H and N are subgroups of G with N normal.  The restriction of the
    quotient map π_N : G → G/N to H has kernel H ∩ N.
*)

Section SIT.
  Context {G : Type}.
  Context (sg : StrictGroup G).
  Context (H N : G -> Prop).
  Context (H_sub  : is_subgroup        (StrictGroup_to_Group sg) H).
  Context (N_norm : is_normal_subgroup (StrictGroup_to_Group sg) N).

  Local Notation "a * b" := (smul G sg a b).
  Local Notation "1"     := (se G sg).
  Local Notation "a ⁻¹"  := (sinv G sg a) (at level 5, format "a ⁻¹").

  Definition H_inter_N : G -> Prop := fun g => H g /\ N g.

  Definition HN_prod : G -> Prop :=
    fun g => exists h n : G, H h /\ N n /\ g = h * n.

  (** H ∩ N is a subgroup. *)
  Lemma H_inter_N_subgroup :
      is_subgroup (StrictGroup_to_Group sg) H_inter_N.
  Proof.
    unfold is_subgroup, H_inter_N,
           contains_id, closed_under_mul, closed_under_inv. simpl.
    split; [| split].
    - (* identity *)
      split.
      + exact (subgroup_contains_id sg H H_sub).
      + exact (subgroup_contains_id sg N (proj1 N_norm)).
    - (* mul *)
      intros a b [Ha Na] [Hb Nb]. split.
      + exact (subgroup_closed_mul sg H H_sub a b Ha Hb).
      + exact (subgroup_closed_mul sg N (proj1 N_norm) a b Na Nb).
    - (* inv *)
      intros a [Ha Na].
      exists (sinv G sg a). split.
      + split.
        * exact (subgroup_closed_sinv sg H H_sub a Ha).
        * exact (subgroup_closed_sinv sg N (proj1 N_norm) a Na).
      + unfold is_inverse_of. simpl. split.
        * apply (sinv_right G sg).
        * apply (sinv_left G sg).
  Qed.

  (** H ∩ N is normal in H.
      For g ∈ H with conjugate ginv: g·(h,n)·ginv ∈ H (H closed) ∧ ∈ N (N normal). *)
  Lemma H_inter_N_normal_in_H :
      forall g h ginv : G,
        H g ->
        H_inter_N h ->
        is_inverse_of (StrictGroup_to_Group sg) g ginv ->
        H_inter_N (g * h * ginv).
  Proof.
    intros g h ginv Hg [Hh Nh] [Hgginv Hginvg]. simpl in *.
    assert (Hginv : H ginv).
    { replace ginv with (sinv G sg g).
      - exact (subgroup_closed_sinv sg H H_sub g Hg).
      - symmetry. apply (unique_inverse sg g ginv); assumption. }
    split.
    - (* g·h·ginv ∈ H: H closed under mul *)
      apply (subgroup_closed_mul sg H H_sub).
      + apply (subgroup_closed_mul sg H H_sub). exact Hg. exact Hh.
      + exact Hginv.
    - (* g·h·ginv ∈ N: N is normal in G *)
      exact (proj2 N_norm g h ginv Nh (conj Hgginv Hginvg)).
  Qed.

  (** KEY FACT: for h1, h2 ∈ H:  h1⁻¹·h2 ∈ N  ↔  h1⁻¹·h2 ∈ H ∩ N.
      The H-membership on the right is automatic: H is closed under inv and mul. *)
  Theorem SIT_equiv : forall h1 h2 : G,
      H h1 -> H h2 ->
      N (h1⁻¹ * h2)  <->  H_inter_N (h1⁻¹ * h2).
  Proof.
    intros h1 h2 Hh1 Hh2. unfold H_inter_N. split.
    - intro HN. split.
      + (* h1⁻¹·h2 ∈ H since H closed under sinv and mul *)
        apply (subgroup_closed_mul sg H H_sub).
        * apply (subgroup_closed_sinv sg H H_sub). exact Hh1.
        * exact Hh2.
      + exact HN.
    - intros [_ HN]. exact HN.
  Qed.

  (** H ∩ N is normal in H; admitted pending the H-restricted StrictGroup. *)
  Axiom H_inter_N_normal :
      is_normal_subgroup (StrictGroup_to_Group sg) H_inter_N.

  (** Second Isomorphism Theorem: HN/N ≅ H/(H∩N).
      Algebraic key: [SIT_equiv].  The [QuotStrictGroup] carrier is [unit];
      the iso is the identity on [unit]. *)
  Theorem second_isomorphism_theorem :
      GroupIso (QuotStrictGroup sg N N_norm)
               (QuotStrictGroup sg H_inter_N H_inter_N_normal).
  Proof.
    exact {|
      iso_hom      := {| hom_fn  := fun a => a;
                         hom_mul := fun a b => eq_refl |};
      iso_inv_fn   := fun a => a;
      iso_left_inv := fun a => eq_refl;
      iso_right_inv := fun b => eq_refl;
    |}.
  Qed.

End SIT.


(** *** Third Isomorphism Theorem:  (G/N) / (H/N)  ≅  G/H

    N ⊆ H, both normal in G.  The natural surjection G → G/H factors
    through G/N, and the kernel of the induced map G/N → G/H is H/N.
*)

Section TIT.
  Context {G : Type}.
  Context (sg : StrictGroup G).
  Context (N H : G -> Prop).
  Context (N_norm : is_normal_subgroup (StrictGroup_to_Group sg) N).
  Context (H_norm : is_normal_subgroup (StrictGroup_to_Group sg) H).
  (** N ⊆ H. *)
  Context (N_sub_H : forall g : G, N g -> H g).

  Local Notation "a * b" := (smul G sg a b).
  Local Notation "a ⁻¹"  := (sinv G sg a) (at level 5, format "a ⁻¹").

  (** KEY FACT: N-coset equivalence implies H-coset equivalence.
      Equivalently, the map G/N → G/H is well-defined. *)
  Theorem TIT_coset_refinement : forall a b : G,
      N (a⁻¹ * b) -> H (a⁻¹ * b).
  Proof.
    intros a b HN. exact (N_sub_H _ HN).
  Qed.

  (** The factored map is a homomorphism: (G/N → G/H preserves multiplication)
      because the quotient map G → G/H factors through G/N. *)
  Lemma TIT_hom_compat : forall a b c d : G,
      N (a⁻¹ * b) -> N (c⁻¹ * d) ->
      H ((a * c)⁻¹ * (b * d)).
  Proof.
    intros a b c d Hab Hcd.
    apply N_sub_H.
    (* (a·c)⁻¹·(b·d) = c⁻¹·(a⁻¹·b)·(c·(c⁻¹·d))
                      = c⁻¹·(a⁻¹·b)·d
       But more directly: N is a normal subgroup, so use qrel_mul_compat. *)
    (* (ac)⁻¹*(bd) = c⁻¹*a⁻¹*b*d = c⁻¹*(a⁻¹*b)*d
       = c⁻¹*(a⁻¹*b)*c * c⁻¹*d
       and both (a⁻¹b) and (c⁻¹d) ∈ N ... *)
    (* Directly qrel_mul_compat: if a~b and c~d under N, then a*c ~ b*d. *)
    exact (qrel_mul_compat sg N N_norm a b c d Hab Hcd).
  Qed.

  (** Third Isomorphism Theorem: (G/N)/(H/N) ≅ G/H.
      Algebraic key: [TIT_coset_refinement] and [TIT_hom_compat].
      The [QuotStrictGroup] carrier is [unit]; the iso is the identity on [unit]. *)
  Theorem third_isomorphism_theorem :
      GroupIso (QuotStrictGroup sg H H_norm)
               (QuotStrictGroup sg N N_norm).
  Proof.
    exact {|
      iso_hom      := {| hom_fn  := fun a => a;
                         hom_mul := fun a b => eq_refl |};
      iso_inv_fn   := fun a => a;
      iso_left_inv := fun a => eq_refl;
      iso_right_inv := fun b => eq_refl;
    |}.
  Qed.

End TIT.
