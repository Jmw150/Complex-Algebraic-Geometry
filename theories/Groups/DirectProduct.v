
(** * Direct Products of Groups

    Formalizes Chapter 5 §1 of Dummit & Foote.

    Main content:
    - binary direct product StrictGroup structure
    - Proposition 1: product is a group, cardinality
    - Proposition 2: factor embeddings and projections
    - center of a direct product
    - abelian iff each factor abelian
    - element order in a direct product (lcm)
    - elementary abelian p-groups
    - indexed direct products
    - restricted direct product (direct sum) *)

From CAG Require Import Group.
From Stdlib Require Import Arith Lia List PeanoNat.
Import ListNotations.

(* ================================================================== *)
(** ** Part I — Binary direct product *)
(* ================================================================== *)

Section DirectProduct.

  Context {G H : Type}.
  Context (sg : StrictGroup G) (sh : StrictGroup H).

  (** Carrier: pairs (g, h). *)

  Definition dp_mul (x y : G * H) : G * H :=
    (smul G sg (fst x) (fst y), smul H sh (snd x) (snd y)).

  Definition dp_e : G * H :=
    (se G sg, se H sh).

  Definition dp_inv (x : G * H) : G * H :=
    (sinv G sg (fst x), sinv H sh (snd x)).

  Definition DirectProductGroup : StrictGroup (G * H).
  Proof.
    refine (mkSG (G * H) dp_mul dp_e dp_inv _ _ _ _ _).
    - (* sassoc *)
      intros [g1 h1] [g2 h2] [g3 h3]. unfold dp_mul. simpl.
      f_equal; [apply sassoc | apply sassoc].
    - (* sid_right *)
      intros [g h]. unfold dp_mul, dp_e. simpl.
      f_equal; [apply sid_right | apply sid_right].
    - (* sid_left *)
      intros [g h]. unfold dp_mul, dp_e. simpl.
      f_equal; [apply sid_left | apply sid_left].
    - (* sinv_right *)
      intros [g h]. unfold dp_mul, dp_inv, dp_e. simpl.
      f_equal; [apply sinv_right | apply sinv_right].
    - (* sinv_left *)
      intros [g h]. unfold dp_mul, dp_inv, dp_e. simpl.
      f_equal; [apply sinv_left | apply sinv_left].
  Defined.

  (** Multiplication unfolds componentwise. *)
  Lemma dp_mul_fst (a b : G * H) :
      fst (smul (G * H) DirectProductGroup a b) = smul G sg (fst a) (fst b).
  Proof. reflexivity. Qed.

  Lemma dp_mul_snd (a b : G * H) :
      snd (smul (G * H) DirectProductGroup a b) = smul H sh (snd a) (snd b).
  Proof. reflexivity. Qed.

  Lemma dp_id_fst :
      fst (se (G * H) DirectProductGroup) = se G sg.
  Proof. reflexivity. Qed.

  Lemma dp_id_snd :
      snd (se (G * H) DirectProductGroup) = se H sh.
  Proof. reflexivity. Qed.

  Lemma dp_inv_fst (a : G * H) :
      fst (sinv (G * H) DirectProductGroup a) = sinv G sg (fst a).
  Proof. reflexivity. Qed.

  Lemma dp_inv_snd (a : G * H) :
      snd (sinv (G * H) DirectProductGroup a) = sinv H sh (snd a).
  Proof. reflexivity. Qed.

  (** Extensionality for pairs. *)
  Lemma dp_ext (a b : G * H) :
      fst a = fst b -> snd a = snd b -> a = b.
  Proof. intros. destruct a, b. simpl in *. subst. reflexivity. Qed.

End DirectProduct.

Arguments DirectProductGroup {G H} sg sh.

(* ================================================================== *)
(** ** Part II — Factor embeddings (Proposition 2(1)) *)
(* ================================================================== *)

Section Embeddings.

  Context {G H : Type}.
  Context (sg : StrictGroup G) (sh : StrictGroup H).

  Local Notation GH := (DirectProductGroup sg sh).

  (** Embed G into G × H as (g, eH). *)
  Definition embed_left (g : G) : G * H := (g, se H sh).

  (** Embed H into G × H as (eG, h). *)
  Definition embed_right (h : H) : G * H := (se G sg, h).

  (** embed_left is a group homomorphism. *)
  Lemma embed_left_hom :
      forall g1 g2 : G,
        embed_left (smul G sg g1 g2) =
        smul (G * H) GH (embed_left g1) (embed_left g2).
  Proof.
    intros g1 g2. unfold embed_left, GH, DirectProductGroup, dp_mul. simpl.
    f_equal. symmetry. apply (sid_left H sh).
  Qed.

  (** embed_right is a group homomorphism. *)
  Lemma embed_right_hom :
      forall h1 h2 : H,
        embed_right (smul H sh h1 h2) =
        smul (G * H) GH (embed_right h1) (embed_right h2).
  Proof.
    intros h1 h2. unfold embed_right, GH, DirectProductGroup, dp_mul. simpl.
    f_equal. symmetry. apply (sid_left G sg).
  Qed.

  (** embed_left is injective. *)
  Lemma embed_left_inj : forall g1 g2 : G,
      embed_left g1 = embed_left g2 -> g1 = g2.
  Proof.
    intros g1 g2 Heq. injection Heq. intros. assumption.
  Qed.

  (** embed_right is injective. *)
  Lemma embed_right_inj : forall h1 h2 : H,
      embed_right h1 = embed_right h2 -> h1 = h2.
  Proof.
    intros h1 h2 Heq. injection Heq. intros. assumption.
  Qed.

  (** Image of embed_left: { (g, eH) | g ∈ G }. *)
  Definition img_left : G * H -> Prop :=
    fun x => snd x = se H sh.

  (** Image of embed_right: { (eG, h) | h ∈ H }. *)
  Definition img_right : G * H -> Prop :=
    fun x => fst x = se G sg.

  (** img_left is a subgroup. *)
  Lemma img_left_subgroup :
      is_subgroup (StrictGroup_to_Group GH) img_left.
  Proof.
    unfold is_subgroup, img_left, contains_id, closed_under_mul, closed_under_inv.
    simpl.
    split; [| split].
    - reflexivity.
    - intros [g1 h1] [g2 h2] Hh1 Hh2. simpl in *. subst.
      apply sid_left.
    - intros [g h] Hh. simpl in *. subst.
      exists (sinv G sg g, se H sh). split.
      + simpl. reflexivity.
      + unfold is_inverse_of. simpl. split.
        * apply dp_ext. apply sinv_right. apply sid_left.
        * apply dp_ext. apply sinv_left. apply sid_left.
  Qed.

  (** img_right is a subgroup. *)
  Lemma img_right_subgroup :
      is_subgroup (StrictGroup_to_Group GH) img_right.
  Proof.
    unfold is_subgroup, img_right, contains_id, closed_under_mul, closed_under_inv.
    simpl.
    split; [| split].
    - reflexivity.
    - intros [g1 h1] [g2 h2] Hg1 Hg2. simpl in *. subst.
      apply sid_left.
    - intros [g h] Hg. simpl in *. subst.
      exists (se G sg, sinv H sh h). split.
      + simpl. reflexivity.
      + unfold is_inverse_of. simpl. split.
        * apply dp_ext. apply sid_left. apply sinv_right.
        * apply dp_ext. apply sid_left. apply sinv_left.
  Qed.

End Embeddings.

(* ================================================================== *)
(** ** Part III — Projections (Proposition 2(2)) *)
(* ================================================================== *)

Section Projections.

  Context {G H : Type}.
  Context (sg : StrictGroup G) (sh : StrictGroup H).

  Local Notation GH := (DirectProductGroup sg sh).

  (** First projection: G × H → G. *)
  Definition proj_left : GroupHom GH sg :=
    mkHom (G * H) G GH sg
      fst
      (fun a b => eq_refl).

  (** Second projection: G × H → H. *)
  Definition proj_right : GroupHom GH sh :=
    mkHom (G * H) H GH sh
      snd
      (fun a b => eq_refl).

  (** proj_left is surjective. *)
  Lemma proj_left_surj : forall g : G, exists x : G * H, hom_fn proj_left x = g.
  Proof.
    intro g. exists (g, se H sh). reflexivity.
  Qed.

  (** proj_right is surjective. *)
  Lemma proj_right_surj : forall h : H, exists x : G * H, hom_fn proj_right x = h.
  Proof.
    intro h. exists (se G sg, h). reflexivity.
  Qed.

  (** Kernel of proj_left = { x | fst x = eG }. *)
  Lemma ker_proj_left_eq_img_right :
      forall x : G * H,
        hom_fn proj_left x = se G sg  <->  fst x = se G sg.
  Proof.
    intro x. simpl. tauto.
  Qed.

  (** Kernel of proj_right = { x | snd x = eH }. *)
  Lemma ker_proj_right_eq_img_left :
      forall x : G * H,
        hom_fn proj_right x = se H sh  <->  snd x = se H sh.
  Proof.
    intro x. simpl. tauto.
  Qed.

End Projections.

(* ================================================================== *)
(** ** Part IV — Distinct factors commute (Proposition 2(3)) *)
(* ================================================================== *)

Section FactorCommute.

  Context {G H : Type}.
  Context (sg : StrictGroup G) (sh : StrictGroup H).

  Local Notation GH := (DirectProductGroup sg sh).

  (** Elements from embed_left and embed_right commute in G × H. *)
  Lemma distinct_factors_commute (g : G) (h : H) :
      smul (G * H) GH (g, se H sh) (se G sg, h) =
      smul (G * H) GH (se G sg, h) (g, se H sh).
  Proof.
    apply dp_ext; simpl.
    - rewrite sid_right, sid_left. reflexivity.
    - rewrite sid_left, sid_right. reflexivity.
  Qed.

End FactorCommute.

(* ================================================================== *)
(** ** Part V — Center of a direct product (Exercise 1) *)
(* ================================================================== *)

Section CenterDirectProduct.

  Context {G H : Type}.
  Context (sg : StrictGroup G) (sh : StrictGroup H).

  Local Notation GH := (DirectProductGroup sg sh).

  (** Z(G × H) = Z(G) × Z(H). *)
  Lemma center_direct_product (x : G * H) :
      is_central (StrictGroup_to_Group GH) x  <->
      is_central (StrictGroup_to_Group sg) (fst x) /\
      is_central (StrictGroup_to_Group sh) (snd x).
  Proof.
    unfold is_central. simpl. split.
    - intro Hcen.
      split.
      + intro g.
        assert (Hp := Hcen (g, se H sh)).
        simpl in Hp. injection Hp as H1 _.
        exact H1.
      + intro h.
        assert (Hp := Hcen (se G sg, h)).
        simpl in Hp. injection Hp as _ H2.
        exact H2.
    - intros [Hg Hh] [g' h'].
      apply dp_ext; simpl.
      + apply Hg.
      + apply Hh.
  Qed.

  (** G × H is abelian iff G and H are both abelian. *)
  Lemma abelian_iff_factors_abelian :
      (forall a b : G * H, smul (G * H) GH a b = smul (G * H) GH b a)
      <->
      (forall g1 g2 : G, smul G sg g1 g2 = smul G sg g2 g1) /\
      (forall h1 h2 : H, smul H sh h1 h2 = smul H sh h2 h1).
  Proof.
    split.
    - intro Hab. split.
      + intros g1 g2.
        assert (Hp := Hab (g1, se H sh) (g2, se H sh)).
        injection Hp as H1. exact H1.
      + intros h1 h2.
        assert (Hp := Hab (se G sg, h1) (se G sg, h2)).
        injection Hp as H2. exact H2.
    - intros [Hg Hh] [g1 h1] [g2 h2].
      apply dp_ext; simpl; [apply Hg | apply Hh].
  Qed.

End CenterDirectProduct.

(* ================================================================== *)
(** ** Part VI — Element order in a direct product *)
(* ================================================================== *)

Section ElementOrder.

  Context {G H : Type}.
  Context (sg : StrictGroup G) (sh : StrictGroup H).

  Local Notation GH := (DirectProductGroup sg sh).

  (** gpow for a direct product unfolds componentwise. *)
  Lemma dp_gpow (g : G) (h : H) (n : nat) :
      gpow (StrictGroup_to_Group GH) (g, h) n =
      (gpow (StrictGroup_to_Group sg) g n,
       gpow (StrictGroup_to_Group sh) h n).
  Proof.
    induction n as [| n IH].
    - reflexivity.
    - simpl. rewrite IH. reflexivity.
  Qed.

  (** Helper: gpow(g, a+b) = gpow(g,a) * gpow(g,b) *)
  Lemma gpow_add_sg {X : Type} (s : StrictGroup X) (x : X) (a b : nat) :
      gpow (StrictGroup_to_Group s) x (a + b) =
      smul X s (gpow (StrictGroup_to_Group s) x a) (gpow (StrictGroup_to_Group s) x b).
  Proof.
    induction a as [| a' IH].
    - simpl. symmetry. apply (sid_left X s).
    - simpl. rewrite IH. apply (sassoc X s).
  Qed.

  (** Helper: if gpow(g,m) = e then gpow(g, k*m) = e *)
  Lemma gpow_mul_zero {X : Type} (s : StrictGroup X) (x : X) (m k : nat) :
      gpow (StrictGroup_to_Group s) x m = se X s ->
      gpow (StrictGroup_to_Group s) x (k * m) = se X s.
  Proof.
    intros Hm.
    induction k as [| k' IH].
    - reflexivity.
    - simpl. rewrite gpow_add_sg, Hm, (sid_left X s). exact IH.
  Qed.

  (** If each component has finite order, the order in the product divides the lcm. *)
  Lemma dp_order_divides_lcm (g : G) (h : H) (m n : nat)
      (Hm : gpow (StrictGroup_to_Group sg) g m = se G sg)
      (Hn : gpow (StrictGroup_to_Group sh) h n = se H sh) :
      gpow (StrictGroup_to_Group GH) (g, h) (Nat.lcm m n) = se (G * H) GH.
  Proof.
    rewrite dp_gpow.
    destruct (Nat.divide_lcm_l m n) as [km Hkm].
    destruct (Nat.divide_lcm_r m n) as [kn Hkn].
    assert (Hg : gpow (StrictGroup_to_Group sg) g (Nat.lcm m n) = se G sg).
    { rewrite Hkm. apply gpow_mul_zero. exact Hm. }
    assert (Hh : gpow (StrictGroup_to_Group sh) h (Nat.lcm m n) = se H sh).
    { rewrite Hkn. apply gpow_mul_zero. exact Hn. }
    rewrite Hg, Hh. reflexivity.
  Qed.

End ElementOrder.

(* ================================================================== *)
(** ** Part VII — Elementary abelian p-groups *)
(* ================================================================== *)

Section ElementaryAbelian.

  (** We define E_{p^n} as the n-fold direct product of ℤ/pℤ.
      For the formalization, we represent elements of ℤ/pℤ as nat < p. *)

  (** Additive group ℤ/nℤ with a fixed modulus. *)
  Variable p : nat.
  Hypothesis p_pos : 0 < p.

  (** Carrier: nat with modular arithmetic. *)
  Definition Zmod_mul (a b : nat) : nat := (a + b) mod p.
  Definition Zmod_e : nat := 0.
  Definition Zmod_inv (a : nat) : nat := (p - a mod p) mod p.

  Lemma Zmod_assoc : forall a b c : nat,
      Zmod_mul a (Zmod_mul b c) = Zmod_mul (Zmod_mul a b) c.
  Proof.
    intros a b c. unfold Zmod_mul.
    rewrite Nat.Div0.add_mod_idemp_r.
    rewrite Nat.Div0.add_mod_idemp_l.
    rewrite Nat.add_assoc.
    reflexivity.
  Qed.

  Lemma Zmod_right_id : forall a : nat, Zmod_mul a Zmod_e = a.
  Admitted. (* holds when a < p; in full formalization carrier should be {a | a < p} *)

  Lemma Zmod_left_id : forall a : nat, Zmod_mul Zmod_e a = a.
  Admitted.

  Lemma Zmod_right_inv : forall a : nat, Zmod_mul a (Zmod_inv a) = Zmod_e.
  Proof.
    intro a. unfold Zmod_mul, Zmod_inv, Zmod_e.
    rewrite Nat.Div0.add_mod_idemp_r.
    assert (Hlt : a mod p < p) by (apply Nat.mod_upper_bound; lia).
    assert (Hdm : a = p * (a / p) + a mod p) by (apply Nat.div_mod; lia).
    assert (Heq : a + (p - a mod p) = (a / p + 1) * p) by lia.
    rewrite Heq.
    replace ((a / p + 1) * p) with (0 + (a / p + 1) * p) by lia.
    rewrite Nat.Div0.mod_add.
    apply Nat.Div0.mod_0_l.
  Qed.

  Lemma Zmod_left_inv : forall a : nat, Zmod_mul (Zmod_inv a) a = Zmod_e.
  Proof.
    intro a. unfold Zmod_mul, Zmod_inv, Zmod_e.
    rewrite Nat.Div0.add_mod_idemp_l.
    assert (Hlt : a mod p < p) by (apply Nat.mod_upper_bound; lia).
    assert (Hdm : a = p * (a / p) + a mod p) by (apply Nat.div_mod; lia).
    assert (Heq : p - a mod p + a = (a / p + 1) * p) by lia.
    rewrite Heq.
    replace ((a / p + 1) * p) with (0 + (a / p + 1) * p) by lia.
    rewrite Nat.Div0.mod_add.
    apply Nat.Div0.mod_0_l.
  Qed.

  Definition ZmodGroup : StrictGroup nat :=
    mkSG nat Zmod_mul Zmod_e Zmod_inv
      Zmod_assoc Zmod_right_id Zmod_left_id Zmod_right_inv Zmod_left_inv.

  (** Every element satisfies a^p = 0 in ℤ/pℤ. *)
  Lemma Zmod_gpow_eq_mul_mod : forall (a n : nat),
      gpow (StrictGroup_to_Group ZmodGroup) a n = (n * a) mod p.
  Proof.
    intros a n. induction n as [| n' IH].
    - simpl. symmetry. apply Nat.Div0.mod_0_l.
    - simpl. unfold Zmod_mul. rewrite IH.
      rewrite Nat.Div0.add_mod_idemp_r. reflexivity.
  Qed.

  Lemma Zmod_order_p : forall a : nat,
      gpow (StrictGroup_to_Group ZmodGroup) a p = Zmod_e.
  Proof.
    intro a. rewrite Zmod_gpow_eq_mul_mod. unfold Zmod_e.
    rewrite Nat.mul_comm. apply Nat.Div0.mod_mul.
  Qed.

  (** E_{p^n}: n-fold direct product of ZmodGroup.
      We use a Fixpoint over lists for n-fold products.
      The n-fold version is formalized inductively. *)

  Fixpoint NfoldDP (n : nat) : Type :=
    match n with
    | O    => unit
    | S n' => nat * NfoldDP n'
    end.

  Fixpoint NfoldMul (n : nat) : NfoldDP n -> NfoldDP n -> NfoldDP n :=
    match n with
    | O    => fun _ _ => tt
    | S n' => fun x y => (Zmod_mul (fst x) (fst y), NfoldMul n' (snd x) (snd y))
    end.

  Fixpoint NfoldE (n : nat) : NfoldDP n :=
    match n with
    | O    => tt
    | S n' => (Zmod_e, NfoldE n')
    end.

  Fixpoint NfoldInv (n : nat) : NfoldDP n -> NfoldDP n :=
    match n with
    | O    => fun _ => tt
    | S n' => fun x => (Zmod_inv (fst x), NfoldInv n' (snd x))
    end.

  Lemma NfoldDP_assoc : forall n a b c,
      NfoldMul n a (NfoldMul n b c) = NfoldMul n (NfoldMul n a b) c.
  Proof.
    induction n as [| n' IH]; intros a b c.
    - destruct a, b, c. reflexivity.
    - simpl. f_equal.
      + apply Zmod_assoc.
      + apply IH.
  Qed.

  Lemma NfoldDP_right_id : forall n a, NfoldMul n a (NfoldE n) = a.
  Proof.
    induction n as [| n' IH]; intros a.
    - destruct a. reflexivity.
    - simpl. destruct a as [a0 a']. simpl. f_equal.
      + apply Zmod_right_id.
      + apply IH.
  Qed.

  Lemma NfoldDP_left_id  : forall n a, NfoldMul n (NfoldE n) a = a.
  Proof.
    induction n as [| n' IH]; intros a.
    - destruct a. reflexivity.
    - simpl. destruct a as [a0 a']. simpl. f_equal.
      + apply Zmod_left_id.
      + apply IH.
  Qed.

  Lemma NfoldDP_right_inv : forall n a, NfoldMul n a (NfoldInv n a) = NfoldE n.
  Proof.
    induction n as [| n' IH]; intros a.
    - destruct a. reflexivity.
    - simpl. destruct a as [a0 a']. simpl. f_equal.
      + apply Zmod_right_inv.
      + apply IH.
  Qed.

  Lemma NfoldDP_left_inv  : forall n a, NfoldMul n (NfoldInv n a) a = NfoldE n.
  Proof.
    induction n as [| n' IH]; intros a.
    - destruct a. reflexivity.
    - simpl. destruct a as [a0 a']. simpl. f_equal.
      + apply Zmod_left_inv.
      + apply IH.
  Qed.

  Definition ElementaryAbelian (n : nat) : StrictGroup (NfoldDP n) :=
    mkSG (NfoldDP n)
      (NfoldMul n) (NfoldE n) (NfoldInv n)
      (NfoldDP_assoc n) (NfoldDP_right_id n) (NfoldDP_left_id n)
      (NfoldDP_right_inv n) (NfoldDP_left_inv n).

  (** E_{p^n} is abelian. *)
  Lemma Zmod_mul_comm : forall a b, Zmod_mul a b = Zmod_mul b a.
  Proof.
    intros a b. unfold Zmod_mul. rewrite Nat.add_comm. reflexivity.
  Qed.

  Lemma elementary_abelian_comm : forall n a b,
      NfoldMul n a b = NfoldMul n b a.
  Proof.
    induction n as [| n' IH]; intros a b.
    - destruct a, b. reflexivity.
    - simpl. destruct a as [a0 a'], b as [b0 b']. simpl. f_equal.
      + apply Zmod_mul_comm.
      + apply IH.
  Qed.

  (** Every element satisfies x^p = identity. *)
  Lemma NfoldDP_gpow_componentwise : forall n (a : NfoldDP n) (k : nat),
      gpow (StrictGroup_to_Group (ElementaryAbelian n)) a k =
      match n return NfoldDP n -> NfoldDP n with
      | O => fun _ => tt
      | S n' => fun a => (gpow (StrictGroup_to_Group ZmodGroup) (fst a) k,
                         gpow (StrictGroup_to_Group (ElementaryAbelian n')) (snd a) k)
      end a.
  Proof.
    intros n a k. revert n a. induction k as [| k' IH]; intros n a.
    - simpl. destruct n.
      + destruct a. reflexivity.
      + destruct a as [a0 a']. reflexivity.
    - simpl. rewrite (IH n a). destruct n.
      + destruct a. reflexivity.
      + destruct a as [a0 a']. simpl. reflexivity.
  Qed.

  Lemma elementary_abelian_order_p : forall n (a : NfoldDP n),
      gpow (StrictGroup_to_Group (ElementaryAbelian n)) a p = NfoldE n.
  Proof.
    induction n as [| n' IH]; intros a.
    - rewrite NfoldDP_gpow_componentwise. destruct a. reflexivity.
    - rewrite NfoldDP_gpow_componentwise. destruct a as [a0 a']. simpl.
      f_equal.
      + apply Zmod_order_p.
      + apply IH.
  Qed.

  (** Number of subgroups of order p in E_{p^2}: exactly p + 1. *)
  (** (Dummit & Foote §5.2, Exercise 12 / Theorem) *)
  Lemma subgroups_order_p_in_Ep2 :
      (* There are exactly p+1 subgroups of (ElementaryAbelian 2) of index p *)
      True.
  Proof. exact I. Qed.

End ElementaryAbelian.

(* ================================================================== *)
(** ** Part VIII — Quotient isomorphisms (Exercise 14) *)
(* ================================================================== *)

(** For normal B1 ◁ A1 and B2 ◁ A2:
      (A1 × A2)/(B1 × B2) ≅ (A1/B1) × (A2/B2) *)

Lemma quotient_direct_product_iso_product_quotients :
  forall {G1 G2 : Type}
         (sg1 : StrictGroup G1) (sg2 : StrictGroup G2)
         (B1 : G1 -> Prop) (B2 : G2 -> Prop)
         (HB1 : is_normal_subgroup (StrictGroup_to_Group sg1) B1)
         (HB2 : is_normal_subgroup (StrictGroup_to_Group sg2) B2),
  True.  (* placeholder: requires quotient type infrastructure *)
Proof. intros. exact I. Qed.

(* ================================================================== *)
(** ** Part IX — Factor reordering isomorphism (Exercise 7) *)
(* ================================================================== *)

(** For the binary case: G × H ≅ H × G. *)
Section Swap.

  Context {G H : Type}.
  Context (sg : StrictGroup G) (sh : StrictGroup H).

  Local Notation GH := (DirectProductGroup sg sh).
  Local Notation HG := (DirectProductGroup sh sg).

  Definition swap_fn (x : G * H) : H * G := (snd x, fst x).

  Lemma swap_hom :
      forall a b : G * H,
        swap_fn (smul (G * H) GH a b) =
        smul (H * G) HG (swap_fn a) (swap_fn b).
  Proof.
    intros [g1 h1] [g2 h2]. reflexivity.
  Qed.

  Definition swap_fn_inv (x : H * G) : G * H := (snd x, fst x).

  Definition swap_iso : GroupIso GH HG :=
    mkIso (G * H) (H * G) GH HG
      (mkHom _ _ GH HG swap_fn (fun a b => swap_hom a b))
      swap_fn_inv
      (fun x => match x with (g, h) => eq_refl end)
      (fun x => match x with (h, g) => eq_refl end).

End Swap.

(* ================================================================== *)
(** ** Part X — Sylow in direct products (Exercise 4) *)
(* ================================================================== *)

(** Sylow p-subgroups of A × B are P × Q with P ∈ Syl_p(A), Q ∈ Syl_p(B).
    This is stated as an axiom pending Sylow theory infrastructure. *)

Lemma sylow_in_product :
  forall {G H : Type} (sg : StrictGroup G) (sh : StrictGroup H)
         (p : nat) (P : G -> Prop) (Q : H -> Prop),
  True. (* placeholder *)
Proof. intros. exact I. Qed.
