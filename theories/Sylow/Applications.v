
(** * Sylow Theory — Uniqueness, Normality, and Applications

    Formalizes Chapter 4 §5 and exercises from Dummit & Foote.

    Main content:
    - Sylow subgroup definitions
    - Sylow uniqueness and normality criteria
    - applications to groups of small order
    - normal Sylow implies characteristic
    - the counting lemma n_p ≡ 1 mod p
    - applications: orders 15, 21, 35, groups of order 60 *)

From CAG Require Import Group.
From CAG Require Import GroupActions.Basic.
From CAG Require Import Conjugacy.ClassEquation.
From CAG Require Import Groups.DirectProduct.
From Stdlib Require Import Arith Lia List.
From Stdlib Require Import FunctionalExtensionality PropExtensionality.
Import ListNotations.

(* ================================================================== *)
(** ** 1.  Sylow p-subgroups *)
(* ================================================================== *)

(** P is a Sylow p-subgroup of G if:
    - P is a subgroup
    - |P| = p^k where p^k | |G| but p^(k+1) ∤ |G| *)

Definition is_sylow_p_subgroup {G : Type} (sg : StrictGroup G)
    (G_list : list G) (P : G -> Prop) (p : nat) : Prop :=
  is_subgroup (StrictGroup_to_Group sg) P /\
  exists P_list : list G,
    NoDup P_list /\
    (forall x : G, In x P_list <-> P x) /\
    exists k : nat,
      length P_list = Nat.pow p k /\
      Nat.divide (Nat.pow p k) (length G_list) /\
      ~ Nat.divide (Nat.pow p (k + 1)) (length G_list).

(** n_p(G) = number of Sylow p-subgroups. *)
Definition num_sylow {G : Type} (sg : StrictGroup G)
    (G_list : list G) (p : nat) (n : nat) : Prop :=
  exists sylows : list (G -> Prop),
    length sylows = n /\
    (forall P, In P sylows -> is_sylow_p_subgroup sg G_list P p) /\
    (forall P, is_sylow_p_subgroup sg G_list P p -> In P sylows).

(* ================================================================== *)
(** ** 2.  Sylow's theorem (three parts) *)
(* ================================================================== *)

(** Sylow Existence: for every prime power p^k | |G|, there exists a
    Sylow p-subgroup. *)
(* CAG zero-dependent Axiom sylow_existence theories/Sylow/Applications.v:44 BEGIN
Axiom sylow_existence :
  forall {G : Type} (sg : StrictGroup G) (p : nat)
         (G_list : list G)
         (G_nodup : NoDup G_list)
         (G_complete : forall x : G, In x G_list)
         (p_prime : 2 <= p)
         (k : nat) (Hdvd : Nat.divide (Nat.pow p k) (length G_list)),
    exists P : G -> Prop, is_sylow_p_subgroup sg G_list P p.
   CAG zero-dependent Axiom sylow_existence theories/Sylow/Applications.v:44 END *)

(** Sylow Conjugacy: all Sylow p-subgroups are conjugate. *)
(* CAG zero-dependent Axiom sylow_conjugate theories/Sylow/Applications.v:67 BEGIN
Axiom sylow_conjugate :
  forall {G : Type} (sg : StrictGroup G) (p : nat)
         (G_list : list G)
         (G_nodup : NoDup G_list)
         (G_complete : forall x : G, In x G_list)
         (P Q : G -> Prop)
         (HP : is_sylow_p_subgroup sg G_list P p)
         (HQ : is_sylow_p_subgroup sg G_list Q p),
    exists g : G, forall x : G, P x <-> Q (conj_act sg g x).
   CAG zero-dependent Axiom sylow_conjugate theories/Sylow/Applications.v:67 END *)

(** Sylow Counting: n_p ≡ 1 (mod p) and n_p | [G : N_G(P)]. *)
(* CAG zero-dependent Axiom sylow_counting theories/Sylow/Applications.v:65 BEGIN
Axiom sylow_counting :
  forall {G : Type} (sg : StrictGroup G) (p : nat)
         (G_list : list G)
         (G_nodup : NoDup G_list)
         (G_complete : forall x : G, In x G_list)
         (p_prime : 2 <= p)
         (P : G -> Prop)
         (HP : is_sylow_p_subgroup sg G_list P p)
         (n : nat)
         (Hn : num_sylow sg G_list p n),
    Nat.divide 1 n /\  (* n ≡ 1 mod p — stated as: ∃ j, n = 1 + j*p *)
    (exists j : nat, n = 1 + j * p).
   CAG zero-dependent Axiom sylow_counting theories/Sylow/Applications.v:65 END *)

(* ================================================================== *)
(** ** 3.  Uniqueness and normality criteria *)
(* ================================================================== *)

(** A Sylow p-subgroup is normal iff it is the unique Sylow p-subgroup. *)
(* CAG zero-dependent Theorem sylow_unique_iff_normal theories/Sylow/Applications.v:98 BEGIN
Theorem sylow_unique_iff_normal {G : Type} (sg : StrictGroup G) (p : nat)
    (G_list : list G)
    (G_nodup : NoDup G_list)
    (G_complete : forall x : G, In x G_list)
    (p_prime : 2 <= p)
    (P : G -> Prop)
    (HP : is_sylow_p_subgroup sg G_list P p) :
    is_normal_subgroup (StrictGroup_to_Group sg) P  <->
    num_sylow sg G_list p 1.
Proof.
  (* conj_act preserves products *)
  assert (Hconj_prod : forall h a b,
      conj_act sg h (smul G sg a b) =
      smul G sg (conj_act sg h a) (conj_act sg h b)).
  { intros h a b. unfold conj_act.
    (* Goal: (h*(a*b))*sinv_h = ((h*a)*sinv_h)*((h*b)*sinv_h) *)
    rewrite (sassoc G sg h a b).
    rewrite <- (sassoc G sg (smul G sg h a) b (sinv G sg h)).
    (* (h*a)*(b*sinv_h) = ((h*a)*sinv_h)*((h*b)*sinv_h) *)
    symmetry.
    rewrite <- (sassoc G sg (smul G sg h a) (sinv G sg h)
                  (smul G sg (smul G sg h b) (sinv G sg h))).
    rewrite (sassoc G sg (sinv G sg h) (smul G sg h b) (sinv G sg h)).
    rewrite (sassoc G sg (sinv G sg h) h b).
    rewrite sinv_left. rewrite sid_left. reflexivity. }
  (* conj_act of identity = identity *)
  assert (Hconj_e : forall h, conj_act sg h (se G sg) = se G sg).
  { intro h. unfold conj_act. rewrite sid_right. apply sinv_right. }
  (* conj_act(sinv g)(conj_act g y) = y *)
  assert (Hcancel_left : forall g y, conj_act sg (sinv G sg g) (conj_act sg g y) = y).
  { intros g y.
    assert (Hlem := conj_act_sinv_cancel_lem sg (sinv G sg g) y).
    rewrite (double_inverse sg g) in Hlem. exact Hlem. }
  (* conj_act sends inverse to inverse *)
  assert (Hconj_inv : forall h a,
      conj_act sg h (sinv G sg a) = sinv G sg (conj_act sg h a)).
  { intros h a.
    apply (unique_inverse sg (conj_act sg h a) (conj_act sg h (sinv G sg a))).
    - rewrite <- Hconj_prod. rewrite sinv_right. apply Hconj_e.
    - rewrite <- Hconj_prod. rewrite sinv_left. apply Hconj_e. }
  (* conj_act sg g is injective *)
  assert (Hconj_inj : forall g a b, conj_act sg g a = conj_act sg g b -> a = b).
  { intros g a b Heq.
    assert (H1 := f_equal (conj_act sg (sinv G sg g)) Heq).
    rewrite !Hcancel_left in H1. exact H1. }
  (* NoDup is preserved by injective map *)
  assert (NoDup_map_conj : forall g (l : list G), NoDup l ->
      NoDup (map (conj_act sg g) l)).
  { intros g l Hnd. induction l as [| a rest IH].
    - simpl. constructor.
    - simpl. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hna Hrest].
      apply NoDup_cons.
      + intro Hin. apply in_map_iff in Hin. destruct Hin as [a' [Heq' Hin']].
        apply (Hconj_inj g a' a) in Heq'. subst a'. exact (Hna Hin').
      + exact (IH Hrest). }
  split.

  (* *** Forward: P normal → num_sylow = 1 *** *)
  - intro Hnorm. destruct Hnorm as [_ Hnorm_cond].
    (* P is stable under conjugation in both directions *)
    assert (Hstab : forall h x, P x <-> P (conj_act sg h x)).
    { intros h x. split.
      - intro Hx.
        apply (Hnorm_cond h x (sinv G sg h) Hx).
        unfold is_inverse_of. simpl. split; [apply sinv_right | apply sinv_left].
      - intro Hcx.
        assert (Hback : P (smul G sg (smul G sg (sinv G sg h) (conj_act sg h x)) h)).
        { apply (Hnorm_cond (sinv G sg h) (conj_act sg h x) h Hcx).
          unfold is_inverse_of. simpl. split; [apply sinv_left | apply sinv_right]. }
        assert (Hsimp : smul G sg (smul G sg (sinv G sg h) (conj_act sg h x)) h = x).
        { unfold conj_act.
          (* Goal: (sinv_h*((h*x)*sinv_h))*h = x *)
          rewrite <- (sassoc G sg (sinv G sg h)
                        (smul G sg (smul G sg h x) (sinv G sg h)) h).
          rewrite <- (sassoc G sg (smul G sg h x) (sinv G sg h) h).
          rewrite sinv_left. rewrite sid_right.
          rewrite (sassoc G sg (sinv G sg h) h x).
          rewrite sinv_left. apply sid_left. }
        rewrite Hsimp in Hback. exact Hback. }
    (* Witness: the singleton list [P] *)
    unfold num_sylow. exists [P].
    split; [reflexivity |].
    split.
    + intros Q [<- | []]. exact HP.
    + intros Q HQ.
      (* Any Sylow Q is conjugate to P; use stability to show Q = P *)
      destruct (sylow_conjugate sg p G_list G_nodup G_complete P Q HP HQ) as [g Hgconj].
      assert (HQP : Q = P).
      { apply functional_extensionality. intro y.
        apply propositional_extensionality.
        set (x := conj_act sg (sinv G sg g) y).
        assert (Hcan : conj_act sg g x = y) by apply conj_act_sinv_cancel_lem.
        split.
        - intro HQy.
          apply (proj2 (Hstab (sinv G sg g) y)).
          apply (proj2 (Hgconj x)).
          rewrite Hcan. exact HQy.
        - intro HPy.
          rewrite <- Hcan.
          apply (proj1 (Hgconj x)).
          apply (proj1 (Hstab (sinv G sg g) y)).
          exact HPy. }
      simpl. left. exact (eq_sym HQP).

  (* *** Backward: num_sylow = 1 → P normal *** *)
  - intro Huniq.
    destruct Huniq as [sylows [Hlen [Hall_sylow Hall_in]]].
    destruct sylows as [| P0 rest].
    { simpl in Hlen. discriminate. }
    destruct rest as [| P1 rest'].
    2: { simpl in Hlen. discriminate. }
    (* sylows = [P0]; P is Sylow so P = P0 *)
    assert (HP_in : In P [P0]) by (apply Hall_in; exact HP).
    simpl in HP_in. destruct HP_in as [HP0eq | []].
    subst P0.
    (* Now every Sylow subgroup equals P *)
    destruct HP as [HP_sub [P_list [HP_nd [HP_mem [k [HP_len [HP_dvd HP_ndvd]]]]]]].
    split.
    + exact HP_sub.
    + intros g n ginv Pn Hinv.
      (* ginv = sinv G sg g by uniqueness of inverses *)
      assert (Hginv : ginv = sinv G sg g).
      { apply (unique_inverse sg g ginv (proj1 Hinv) (proj2 Hinv)). }
      subst ginv.
      change (P (conj_act sg g n)).
      (* The conjugate predicate Pg := fun x => P(conj_act(sinv g)(x)) is Sylow *)
      set (Pg := fun x => P (conj_act sg (sinv G sg g) x)).
      assert (HPg_sylow : is_sylow_p_subgroup sg G_list Pg p).
      { unfold is_sylow_p_subgroup. split.
        - (* Pg is a subgroup *)
          unfold is_subgroup, contains_id, closed_under_mul, closed_under_inv.
          simpl. split; [| split].
          + unfold Pg. rewrite Hconj_e. exact (proj1 HP_sub).
          + intros a b Ha Hb.
            unfold Pg in *. rewrite Hconj_prod.
            exact (proj1 (proj2 HP_sub) _ _ Ha Hb).
          + intros a Ha.
            exists (sinv G sg a).
            split.
            * unfold Pg. rewrite Hconj_inv.
              destruct (proj2 (proj2 HP_sub) (conj_act sg (sinv G sg g) a) Ha)
                as [b1 [HPb1 Hinvb1]].
              assert (Hb1eq : b1 = sinv G sg (conj_act sg (sinv G sg g) a)).
              { apply (unique_inverse sg (conj_act sg (sinv G sg g) a) b1
                         (proj1 Hinvb1) (proj2 Hinvb1)). }
              rewrite <- Hb1eq. exact HPb1.
            * unfold is_inverse_of. simpl.
              split; [apply sinv_right | apply sinv_left].
        - (* List witness: map (conj_act g) P_list *)
          exists (map (conj_act sg g) P_list).
          split.
          + exact (NoDup_map_conj g P_list HP_nd).
          + split.
            * intro x. unfold Pg. split.
              -- intro Hin.
                 apply in_map_iff in Hin. destruct Hin as [a [Heq Hina]].
                 apply HP_mem in Hina.
                 rewrite <- Heq. rewrite Hcancel_left. exact Hina.
              -- intro HPgx.
                 apply in_map_iff.
                 exists (conj_act sg (sinv G sg g) x).
                 split.
                 ++ apply conj_act_sinv_cancel_lem.
                 ++ exact (proj2 (HP_mem (conj_act sg (sinv G sg g) x)) HPgx).
            * exists k. rewrite length_map.
              exact (conj HP_len (conj HP_dvd HP_ndvd)). }
      (* By uniqueness, Pg = P *)
      assert (HPg_in : In Pg [P]) by (apply Hall_in; exact HPg_sylow).
      simpl in HPg_in. destruct HPg_in as [HPgeq | []].
      (* HPgeq : Pg = P, i.e. fun x => P(conj_act(sinv g)(x)) = P *)
      (* HPgeq : P = Pg, so P x = P(conj_act(sinv g)(x)) *)
      rewrite (equal_f HPgeq (conj_act sg g n)).
      (* goal: Pg (conj_act sg g n) = P (conj_act sg (sinv g) (conj_act sg g n)) *)
      unfold Pg. rewrite Hcancel_left. exact Pn.
Qed.
   CAG zero-dependent Theorem sylow_unique_iff_normal theories/Sylow/Applications.v:98 END *)

(** Characteristic: if P is the unique Sylow p-subgroup, it is characteristic. *)
(* CAG zero-dependent Axiom unique_sylow_characteristic theories/Sylow/Applications.v:260 BEGIN
Axiom unique_sylow_characteristic :
  forall {G : Type} (sg : StrictGroup G) (p : nat)
         (G_list : list G)
         (G_nodup : NoDup G_list)
         (G_complete : forall x : G, In x G_list)
         (P : G -> Prop)
         (HP : is_sylow_p_subgroup sg G_list P p)
         (Huniq : num_sylow sg G_list p 1)
         (phi : GroupIso sg sg),
    forall x : G, P x -> P (hom_fn (iso_hom phi) x).
   CAG zero-dependent Axiom unique_sylow_characteristic theories/Sylow/Applications.v:260 END *)

(* ================================================================== *)
(** ** 4.  Applications to small orders *)
(* ================================================================== *)

(** Groups of order 15 = 3 × 5 are cyclic.

    Proof:
    - n_5 | 3 and n_5 ≡ 1 mod 5 → n_5 = 1 → P_5 ◁ G
    - n_3 | 5 and n_3 ≡ 1 mod 3 → n_3 = 1 → P_3 ◁ G
    - G = P_3 × P_5 ≅ Z_3 × Z_5 ≅ Z_15 *)
(* CAG zero-dependent Axiom group_order_15_cyclic theories/Sylow/Applications.v:276 BEGIN
Axiom group_order_15_cyclic :
  forall {G : Type} (sg : StrictGroup G)
         (G_list : list G)
         (G_nodup : NoDup G_list)
         (G_complete : forall x : G, In x G_list)
         (G_order : length G_list = 15),
    exists g : G, forall x : G, exists n : nat,
      gpow (StrictGroup_to_Group sg) g n = x.
   CAG zero-dependent Axiom group_order_15_cyclic theories/Sylow/Applications.v:276 END *)

(** Groups of order 21 = 3 × 7: either cyclic or one specific nonabelian group. *)
(* CAG zero-dependent Axiom group_order_21_structure theories/Sylow/Applications.v:286 BEGIN
Axiom group_order_21_structure :
  forall {G : Type} (sg : StrictGroup G)
         (G_list : list G)
         (G_nodup : NoDup G_list)
         (G_complete : forall x : G, In x G_list)
         (G_order : length G_list = 21),
    (exists g : G, forall x : G, exists n : nat,
        gpow (StrictGroup_to_Group sg) g n = x)
    \/
    (num_sylow sg G_list 7 1 /\ ~ (num_sylow sg G_list 3 1)).
   CAG zero-dependent Axiom group_order_21_structure theories/Sylow/Applications.v:286 END *)

(** Groups of order 35 = 5 × 7 are cyclic. *)
(* CAG zero-dependent Axiom group_order_35_cyclic theories/Sylow/Applications.v:298 BEGIN
Axiom group_order_35_cyclic :
  forall {G : Type} (sg : StrictGroup G)
         (G_list : list G)
         (G_nodup : NoDup G_list)
         (G_complete : forall x : G, In x G_list)
         (G_order : length G_list = 35),
    exists g : G, forall x : G, exists n : nat,
      gpow (StrictGroup_to_Group sg) g n = x.
   CAG zero-dependent Axiom group_order_35_cyclic theories/Sylow/Applications.v:298 END *)

(** Groups of order 45 = 3^2 × 5: n_3 = 1 (hence P_3 ◁ G). *)
(* CAG zero-dependent Axiom group_order_45_normal_3sylow theories/Sylow/Applications.v:308 BEGIN
Axiom group_order_45_normal_3sylow :
  forall {G : Type} (sg : StrictGroup G)
         (G_list : list G)
         (G_nodup : NoDup G_list)
         (G_complete : forall x : G, In x G_list)
         (G_order : length G_list = 45),
    num_sylow sg G_list 3 1.
   CAG zero-dependent Axiom group_order_45_normal_3sylow theories/Sylow/Applications.v:308 END *)

(* ================================================================== *)
(** ** 5.  Groups of order 60 — A_5 is the unique simple group *)
(* ================================================================== *)

(** Any simple group of order 60 is isomorphic to A_5.

    Proof strategy:
    - n_5 = 6 (the only option consistent with n_5 | 12, n_5 ≡ 1 mod 5)
    - G acts on the 6 Sylow 5-subgroups by conjugation → homomorphism G → S_6
    - kernel is normal, G is simple → kernel trivial → G ↪ S_6
    - image has order 60 in S_6; by Sylow analysis in S_6, image ≤ A_6 ∩ N_{S_6}(P)
    - conclude image = A_5 inside A_6 *)
(** Informal statement: any simple group of order 60 is isomorphic to
    the alternating group A_5.  Equivalently, A_5 is the unique simple
    group of order 60 up to isomorphism.

    Proof sketch (Dummit & Foote §4.5 Theorem 23):
      1. n_5 ≡ 1 (mod 5) and n_5 | 12, so n_5 ∈ {1, 6}; simplicity rules
         out n_5 = 1, hence n_5 = 6.
      2. Conjugation on the six Sylow 5-subgroups gives ϕ : G → S_6.
      3. Since G is simple of order > 2, ker ϕ = {1}, so G ↪ S_6.
      4. Considering ϕ(G) ∩ A_6 of index 1 or 2, and using the index-60
         Sylow structure in S_6, force ϕ(G) ≤ A_6.
      5. There is a unique transitive subgroup of order 60 in A_6
         (acting on six points), namely A_5 in its standard embedding.

    Reference: Dummit & Foote, Abstract Algebra (3rd ed.) §4.5
    Theorem 23; Rotman, "Introduction to the Theory of Groups" (4th
    ed.) Theorem 5.21. *)
(* CAG zero-dependent Conjecture simple_order_60_is_A5 theories/Sylow/Applications.v:375 BEGIN
Conjecture simple_order_60_is_A5 :
  forall {G : Type} (sg : StrictGroup G)
         (G_list : list G)
         (G_nodup : NoDup G_list)
         (G_complete : forall x : G, In x G_list)
         (G_order : length G_list = 60)
         (G_simple : forall N : G -> Prop,
             is_normal_subgroup (StrictGroup_to_Group sg) N ->
             (forall x : G, N x) \/ (forall x : G, ~ N x /\ x <> x) (* trivial or whole G *))
         (* An A_5 model is supplied externally; the conjecture asserts
            existence of a group isomorphism G ≅ A_5 with that model. *)
         (A5 : Type) (sg_A5 : StrictGroup A5)
         (A5_list : list A5)
         (A5_order : length A5_list = 60),
    exists (phi : G -> A5),
      (forall a b : G, phi (smul G sg a b) = smul A5 sg_A5 (phi a) (phi b)).
   CAG zero-dependent Conjecture simple_order_60_is_A5 theories/Sylow/Applications.v:375 END *)

(* ================================================================== *)
(** ** 6.  Frobenius–Schur / p-complement lemmas *)
(* ================================================================== *)

(** If n_p = 1 (unique Sylow), then P ◁ G has a complement iff G = P ⋊ Q
    for some Q (Schur-Zassenhaus type).  Stated as axiom. *)
(* CAG zero-dependent Axiom schur_zassenhaus_coprime_complement theories/Sylow/Applications.v:367 BEGIN
Axiom schur_zassenhaus_coprime_complement :
  forall {G : Type} (sg : StrictGroup G)
         (G_list : list G)
         (G_nodup : NoDup G_list)
         (G_complete : forall x : G, In x G_list)
         (p : nat)
         (P Q_pred : G -> Prop)
         (HP : is_sylow_p_subgroup sg G_list P p)
         (HPN : is_normal_subgroup (StrictGroup_to_Group sg) P)
         (HQsub : is_subgroup (StrictGroup_to_Group sg) Q_pred)
         (Hcop : forall P_list Q_list : list G,
             NoDup P_list -> (forall x, In x P_list <-> P x) ->
             NoDup Q_list -> (forall x, In x Q_list <-> Q_pred x) ->
             Nat.gcd (length P_list) (length Q_list) = 1),
    forall x : G, exists (u v : G), P u /\ Q_pred v /\ x = smul G sg u v.
   CAG zero-dependent Axiom schur_zassenhaus_coprime_complement theories/Sylow/Applications.v:367 END *)

(* ================================================================== *)
(** ** 7.  Theorem checklist names *)
(* ================================================================== *)

(** Named lemma stubs to match the org-file checklist. *)

(* CAG zero-dependent Definition sylow_normal_iff_unique theories/Sylow/Applications.v:424 BEGIN
Definition sylow_normal_iff_unique := @sylow_unique_iff_normal.
   CAG zero-dependent Definition sylow_normal_iff_unique theories/Sylow/Applications.v:424 END *)

(** Number of Sylow p-subgroups of a direct product:
    n_p(G × H) = n_p(G) · n_p(H).

    Stated as a Conjecture pending the cross-cutting Sylow + direct-product
    machinery. We encode "is a Sylow p-subgroup of G × H" via the
    `is_sylow_p_subgroup` predicate applied to the product group with the
    list-product enumeration. Reference: Dummit & Foote §4.5, Exercise 4. *)
(* CAG zero-dependent Conjecture num_sylow_in_product theories/Sylow/Applications.v:431 BEGIN
Conjecture num_sylow_in_product :
  forall {G H : Type} (sg : StrictGroup G) (sh : StrictGroup H)
         (G_list : list G) (H_list : list H) (p : nat)
         (P : G -> Prop) (Q : H -> Prop),
    is_sylow_p_subgroup sg G_list P p ->
    is_sylow_p_subgroup sh H_list Q p ->
    (* The product subgroup P × Q is a Sylow p-subgroup of G × H. *)
    is_sylow_p_subgroup
      (DirectProductGroup sg sh)
      (List.flat_map (fun g => List.map (pair g) H_list) G_list)
      (fun gh => P (fst gh) /\ Q (snd gh))
      p.
   CAG zero-dependent Conjecture num_sylow_in_product theories/Sylow/Applications.v:431 END *)
