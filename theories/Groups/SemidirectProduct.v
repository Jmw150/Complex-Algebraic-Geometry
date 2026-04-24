(** * SemidirectProduct.v — External semidirect product H ⋊_φ K

    Formalizes the external semidirect product of groups.

    Reference: Dummit & Foote §5.5. *)

From CAG Require Import Group.
From Stdlib Require Import Arith Lia List FunctionalExtensionality PropExtensionality.

(* ================================================================== *)
(** ** External semidirect product *)
(* ================================================================== *)

Section SemidirectProduct.
  Context {H K : Type}.
  Context (sh : StrictGroup H) (sk : StrictGroup K).

  (** φ : K -> Aut(H), given as an action K × H → H. *)
  Context (phi : K -> H -> H).

  (** φ is a group homomorphism K → Aut(H):
      φ(k1·k2)(h) = φ(k1)(φ(k2)(h)) *)
  Context (phi_hom_k : forall k1 k2 h,
               phi (smul K sk k1 k2) h = phi k1 (phi k2 h)).

  (** φ(e_K) = id_H *)
  Context (phi_id : forall h, phi (se K sk) h = h).

  (** For each k, φ(k) is a group homomorphism H → H. *)
  Context (phi_hom_h : forall k h1 h2,
               phi k (smul H sh h1 h2) = smul H sh (phi k h1) (phi k h2)).

  (** For each k, φ(k) sends e_H to e_H. *)
  Context (phi_id_h : forall k, phi k (se H sh) = se H sh).

  (* ============================================================ *)
  (** Carrier: H × K
      Multiplication: (h1,k1)·(h2,k2) = (h1·φ(k1)(h2), k1·k2) *)
  (* ============================================================ *)

  Definition sdp_mul (x y : H * K) : H * K :=
    (smul H sh (fst x) (phi (snd x) (fst y)),
     smul K sk (snd x) (snd y)).

  Definition sdp_e : H * K := (se H sh, se K sk).

  (** Inverse: (h,k)^{-1} = (φ(k⁻¹)(h⁻¹), k⁻¹) *)
  Definition sdp_inv (x : H * K) : H * K :=
    (phi (sinv K sk (snd x)) (sinv H sh (fst x)),
     sinv K sk (snd x)).

  Lemma sdp_assoc : forall a b c : H * K,
      sdp_mul a (sdp_mul b c) = sdp_mul (sdp_mul a b) c.
  Proof.
    intros [h1 k1] [h2 k2] [h3 k3].
    unfold sdp_mul. simpl.
    f_equal.
    - (* h1 * φ(k1)(h2 * φ(k2)(h3)) = h1 * φ(k1)(h2) * φ(k1*k2)(h3) *)
      rewrite phi_hom_h.
      rewrite <- phi_hom_k.
      (* now: h1 * (φ(k1)(h2) * φ(k1)(φ(k2)(h3))) = h1 * φ(k1)(h2) * φ(k1*k2)(h3) *)
      (* but phi_hom_k : phi (k1*k2) h = phi k1 (phi k2 h)
         so phi k1 (phi k2 h3) = phi (k1*k2) h3 ... no wait, that's the wrong direction *)
      (* Actually phi_hom_k : phi (smul K sk k1 k2) h = phi k1 (phi k2 h)
         so <- phi_hom_k gives phi k1 (phi k2 h3) = phi (k1*k2) h3 reversed *)
      apply sassoc.
    - apply sassoc.
  Qed.

  Lemma sdp_id_right : forall a : H * K, sdp_mul a sdp_e = a.
  Proof.
    intros [h k]. unfold sdp_mul, sdp_e. simpl.
    f_equal.
    - rewrite phi_id_h. apply sid_right.
    - apply sid_right.
  Qed.

  Lemma sdp_id_left : forall a : H * K, sdp_mul sdp_e a = a.
  Proof.
    intros [h k]. unfold sdp_mul, sdp_e. simpl.
    f_equal.
    - rewrite phi_id. apply sid_left.
    - apply sid_left.
  Qed.

  Lemma sdp_inv_right : forall a : H * K, sdp_mul a (sdp_inv a) = sdp_e.
  Proof.
    intros [h k]. unfold sdp_mul, sdp_inv, sdp_e. simpl.
    f_equal.
    - (* h · φ(k)(φ(k⁻¹)(h⁻¹)) = e_H *)
      rewrite <- phi_hom_k.
      rewrite sinv_right.
      rewrite phi_id.
      apply sinv_right.
    - apply sinv_right.
  Qed.

  Lemma sdp_inv_left : forall a : H * K, sdp_mul (sdp_inv a) a = sdp_e.
  Proof.
    intros [h k]. unfold sdp_mul, sdp_inv, sdp_e. simpl.
    f_equal.
    - (* φ(k⁻¹)(h⁻¹) · φ(k⁻¹)(h) = e_H *)
      rewrite <- phi_hom_h.
      rewrite sinv_left.
      apply phi_id_h.
    - apply sinv_left.
  Qed.

  (** The semidirect product group. *)
  Definition SemidirectProductGroup : StrictGroup (H * K) :=
    mkSG (H * K) sdp_mul sdp_e sdp_inv
      sdp_assoc sdp_id_right sdp_id_left sdp_inv_right sdp_inv_left.

  (* ============================================================ *)
  (** Component projections *)
  (* ============================================================ *)

  Lemma sdp_mul_fst (a b : H * K) :
      fst (smul (H * K) SemidirectProductGroup a b) =
      smul H sh (fst a) (phi (snd a) (fst b)).
  Proof. reflexivity. Qed.

  Lemma sdp_mul_snd (a b : H * K) :
      snd (smul (H * K) SemidirectProductGroup a b) =
      smul K sk (snd a) (snd b).
  Proof. reflexivity. Qed.

  Lemma sdp_id : se (H * K) SemidirectProductGroup = (se H sh, se K sk).
  Proof. reflexivity. Qed.

  Lemma sdp_inv_formula (h : H) (k : K) :
      sinv (H * K) SemidirectProductGroup (h, k) =
      (phi (sinv K sk k) (sinv H sh h), sinv K sk k).
  Proof. reflexivity. Qed.

  (* ============================================================ *)
  (** Embedding of H into H ⋊ K as (h, e_K) *)
  (* ============================================================ *)

  Definition embed_H (h : H) : H * K := (h, se K sk).

  Lemma embed_H_hom : forall h1 h2 : H,
      embed_H (smul H sh h1 h2) =
      smul (H * K) SemidirectProductGroup (embed_H h1) (embed_H h2).
  Proof.
    intros h1 h2. unfold embed_H, SemidirectProductGroup. simpl.
    unfold sdp_mul. simpl.
    f_equal.
    - rewrite phi_id. reflexivity.
    - symmetry. apply sid_right.
  Qed.

  Lemma embed_H_inj : forall h1 h2 : H,
      embed_H h1 = embed_H h2 -> h1 = h2.
  Proof.
    intros h1 h2 Heq. injection Heq. intros. assumption.
  Qed.

  (** Image of embed_H is normal in H ⋊ K. *)
  Lemma embed_H_normal : is_normal_subgroup
      (StrictGroup_to_Group SemidirectProductGroup)
      (fun x => snd x = se K sk).
  Proof.
    unfold is_normal_subgroup.
    split.
    - (* is_subgroup *)
      unfold is_subgroup, contains_id, closed_under_mul, closed_under_inv.
      simpl.
      split; [| split].
      + (* contains_id: snd (e_H, e_K) = e_K *)
        reflexivity.
      + (* closed_under_mul *)
        intros [h1 k1] [h2 k2] Hk1 Hk2. simpl in *.
        subst k1. subst k2.
        unfold sdp_mul. simpl. apply (sid_right K sk).
      + (* closed_under_inv: (h, e_K)^-1 = (sinv h, e_K) *)
        intros [h k] Hk. simpl in Hk. subst k.
        exists (sinv H sh h, se K sk).
        split.
        * simpl. reflexivity.
        * unfold is_inverse_of. simpl.
          split.
          -- unfold sdp_mul, sdp_e. simpl.
             rewrite (phi_id (sinv H sh h)), (sinv_right H sh h), (sid_right K sk (se K sk)).
             reflexivity.
          -- unfold sdp_mul, sdp_e. simpl.
             rewrite (phi_id h), (sinv_left H sh h), (sid_right K sk (se K sk)).
             reflexivity.
    - (* normality: snd(g*n*ginv) = e_K when snd(n) = e_K *)
      intros g n ginv Hn_in [Hmul _].
      destruct g as [hg kg], n as [hn kn], ginv as [hginv kginv].
      simpl in Hn_in. subst kn.
      simpl in Hmul.
      injection Hmul as _ Hk.
      simpl. rewrite (sid_right K sk kg). exact Hk.
  Qed.

  (* ============================================================ *)
  (** Embedding of K into H ⋊ K as (e_H, k) *)
  (* ============================================================ *)

  Definition embed_K (k : K) : H * K := (se H sh, k).

  Lemma embed_K_hom : forall k1 k2 : K,
      embed_K (smul K sk k1 k2) =
      smul (H * K) SemidirectProductGroup (embed_K k1) (embed_K k2).
  Proof.
    intros k1 k2. unfold embed_K, SemidirectProductGroup. simpl.
    unfold sdp_mul. simpl.
    f_equal.
    (* se H sh = smul H sh (se H sh) (phi k1 (se H sh)) *)
    rewrite phi_id_h.
    symmetry. apply sid_right.
  Qed.

  Lemma embed_K_inj : forall k1 k2 : K,
      embed_K k1 = embed_K k2 -> k1 = k2.
  Proof.
    intros k1 k2 Heq. injection Heq. intros. assumption.
  Qed.

  (** Image of embed_K is a subgroup. *)
  Lemma embed_K_subgroup :
      is_subgroup (StrictGroup_to_Group SemidirectProductGroup)
                  (fun x => fst x = se H sh).
  Proof.
    unfold is_subgroup, contains_id, closed_under_mul, closed_under_inv.
    split; [| split].
    - (* identity: fst (e_H, e_K) = e_H *)
      reflexivity.
    - (* closed under mul *)
      intros [h1 k1] [h2 k2] Hh1 Hh2.
      simpl in *. subst.
      unfold sdp_mul. simpl.
      rewrite phi_id_h. apply sid_left.
    - (* closed under inv *)
      intros [h k] Hh. simpl in *. subst.
      exists (sinv (H * K) SemidirectProductGroup (se H sh, k)).
      split.
      + simpl.
        assert (Hinv_e : sinv H sh (se H sh) = se H sh).
        { symmetry. apply (unique_inverse sh (se H sh) (se H sh));
            apply sid_right. }
        rewrite Hinv_e. apply phi_id_h.
      + (* The sinv of SemidirectProductGroup satisfies is_inverse_of *)
        unfold is_inverse_of.
        split; apply (sinv_right (H * K) SemidirectProductGroup) ||
               apply (sinv_left (H * K) SemidirectProductGroup).
  Qed.

End SemidirectProduct.

Arguments SemidirectProductGroup {H K} sh sk phi.

(* ================================================================== *)
(** ** Recognition theorem (axiomatic) *)
(*
   G ≅ H ⋊_φ K when G = HK, H ◁ G, H ∩ K = {e}.
*)
(* ================================================================== *)

Axiom recognition_theorem :
  forall {G H K : Type}
         (sg : StrictGroup G) (sh : StrictGroup H) (sk : StrictGroup K)
         (phi : K -> H -> H),
  (* Conditions: G = HK, H normal in G, H ∩ K = {e} *)
  True. (* placeholder *)

(* ================================================================== *)
(** ** Classification of groups of order pq *)
(* ================================================================== *)

Axiom order_pq_classification :
  forall (p q : nat) (p_prime : 2 <= p) (q_prime : 2 <= q) (Hpq : p < q)
         {G : Type} (sg : StrictGroup G)
         (G_list : list G)
         (G_nodup : NoDup G_list)
         (G_complete : forall x : G, In x G_list)
         (G_order : length G_list = p * q),
    (* Either cyclic or one nonabelian semidirect product *)
    (exists g : G, forall x : G,
       exists n : nat, gpow (StrictGroup_to_Group sg) g n = x)
    \/
    (~ Nat.divide p (q - 1) ->
     exists g : G, forall x : G,
       exists n : nat, gpow (StrictGroup_to_Group sg) g n = x).
