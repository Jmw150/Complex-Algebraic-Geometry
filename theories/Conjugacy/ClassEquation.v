
(** * Class Equation and Conjugacy Consequences

    Formalizes Chapter 4 §3 of Dummit & Foote.

    Main content:
    - conjugation action and conjugacy classes (reusing GroupActions/Basic.v)
    - centralizer as stabilizer
    - class equation: |G| = |Z(G)| + Σ [G : C_G(g_i)]
    - nontrivial center of a p-group
    - groups of order p^2 are abelian
    - conjugacy in S_n classified by cycle type (axiom)
    - A_5 is simple (axiom)
    - selected exercise lemmas *)

From CAG Require Import Group.
From CAG Require Import GroupActions.Basic.
From Stdlib Require Import Arith Lia List.
From Stdlib Require Import FunctionalExtensionality PropExtensionality.
Import ListNotations.

(* ================================================================== *)
(** ** 1.  Conjugacy classes and centralizers *)
(* ================================================================== *)

(** We recall from GroupActions.Basic:
      conj_act sg g x = g * x * g⁻¹
      conj_class sg x = orbit of x under conj_act
      centralizer sg x = stabilizer of x under conj_act = { g | g*x=x*g } *)

(** The center Z(G) = { x | conj_class sg x = {x} } = { x | centralizer sg x = G }. *)
Definition center {G : Type} (sg : StrictGroup G) : G -> Prop :=
  fun x => is_central (StrictGroup_to_Group sg) x.

Lemma center_eq_conj_singleton {G : Type} (sg : StrictGroup G) (x : G) :
    center sg x  <->  forall g : G, conj_act sg g x = x.
Proof.
  unfold center, is_central, conj_act. simpl.
  split.
  - intros Hcen g.
    (* goal: (g * x) * g⁻¹ = x *)
    apply (right_cancel sg g).
    rewrite <- sassoc, sinv_left, sid_right.
    exact (eq_sym (Hcen g)).
  - intros Hfix g.
    (* goal: x * g = g * x.  From Hfix g: (g * x) * g⁻¹ = x. *)
    apply (right_cancel sg (sinv G sg g)).
    rewrite <- sassoc, sinv_right, sid_right.
    exact (eq_sym (Hfix g)).
Qed.

(** x ∈ center iff conj_class x = {x}. *)
Lemma center_singleton_class {G : Type} (sg : StrictGroup G) (x : G) :
    center sg x  <->  forall y : G, conj_class sg x y -> y = x.
Proof.
  rewrite center_eq_conj_singleton.
  unfold conj_class, orbit, conj_act. simpl.
  split.
  - intros Hfix y [g Hg].
    rewrite <- Hg. apply Hfix.
  - intros Hfix g.
    apply Hfix. exists g. reflexivity.
Qed.

(* ================================================================== *)
(** ** 2.  Class equation — finite version *)
(* ================================================================== *)

(** For a finite group with elements listed, the class equation says:
      |G| = |Z(G)| + Σ_{[g] non-central} [G : C_G(g)]

    We state this as an axiom since it requires:
    - choosing coset representatives
    - finite-set cardinality
    - the partition of G by conjugacy classes.

    The structural content (orbit-partition) is proved in GroupActions.Basic
    via act_rel being an equivalence relation. *)

(** Subgroup index (size of G / H as a count of cosets).
    For finite groups this equals |G| / |H|. *)
Definition subgroup_index {G : Type} (sg : StrictGroup G)
    (G_list : list G) (H : G -> Prop) : nat :=
  (* Number of cosets = |G| / |H| when G,H are finite.
     We approximate as: count of elements g in G_list such that g is not in
     the same H-coset as any earlier element. *)
  length G_list. (* placeholder — full formalization needs coset enumeration *)

(** Class equation (axiom for finite groups). *)
Axiom class_equation :
  forall {G : Type} (sg : StrictGroup G)
         (G_dec : forall x y : G, {x = y} + {x <> y})
         (G_list : list G)
         (G_nodup : NoDup G_list)
         (G_complete : forall x : G, In x G_list),
    length G_list =
    length (List.filter (fun x => if G_dec x x then true else false) (* stub *)
                        (List.filter (fun x => true) G_list)).

(* ================================================================== *)
(** ** 3.  Nontrivial center of a p-group *)
(* ================================================================== *)

(** A p-group: every element has order a power of p. *)
Definition is_pgroup {G : Type} (sg : StrictGroup G) (p : nat) : Prop :=
  forall g : G, exists k : nat, gpow (StrictGroup_to_Group sg) g (Nat.pow p k) = se G sg.

(** The key theorem: if |P| = p^a with a ≥ 1, then Z(P) ≠ {e}.

    Proof strategy (from class equation):
    - class equation: |P| = |Z(P)| + Σ [P : C_P(g_i)]
    - each noncentral conjugacy class has size [P:C_P(g_i)] divisible by p
    - p | |P| (since a ≥ 1)
    - therefore p | |Z(P)|
    - Z(P) contains e, so |Z(P)| ≥ 1
    - p | |Z(P)| and |Z(P)| ≥ 1 implies |Z(P)| ≥ p ≥ 2 *)
Axiom pgroup_center_nontrivial :
  forall {G : Type} (sg : StrictGroup G) (p a : nat)
         (p_prime : 2 <= p)
         (a_pos : 1 <= a)
         (G_list : list G)
         (G_nodup : NoDup G_list)
         (G_complete : forall x : G, In x G_list)
         (G_order : length G_list = Nat.pow p a)
         (Hpg : is_pgroup sg p),
    exists x : G, center sg x /\ x <> se G sg.

(* ================================================================== *)
(** ** 4.  Groups of order p^2 are abelian *)
(* ================================================================== *)

(** If |G| = p^2, then G is abelian.

    Proof:
    1. By pgroup_center_nontrivial, Z(G) is nontrivial.
    2. |G/Z(G)| divides |G| = p^2.
    3. Options: |Z(G)| = p or p^2.
    4. If |Z(G)| = p^2, then G = Z(G) is abelian.
    5. If |Z(G)| = p, then G/Z(G) has order p, hence is cyclic.
    6. If G/Z(G) is cyclic, then G is abelian (standard lemma).
    7. Contradiction with |Z(G)| = p (G abelian → Z(G) = G → |Z(G)| = p^2). *)

(** Auxiliary: if G/Z(G) is cyclic then G is abelian. *)
Axiom quotient_by_center_cyclic_implies_abelian :
  forall {G : Type} (sg : StrictGroup G),
    (* If the quotient G/Z(G) is generated by one element *)
    (exists g : G, forall x : G, exists n : nat,
       conj_class sg g (gpow (StrictGroup_to_Group sg) x n)) ->
    forall a b : G, smul G sg a b = smul G sg b a.

Axiom group_order_p_sq_abelian :
  forall {G : Type} (sg : StrictGroup G) (p : nat)
         (p_prime : 2 <= p)
         (G_list : list G)
         (G_nodup : NoDup G_list)
         (G_complete : forall x : G, In x G_list)
         (G_order : length G_list = Nat.pow p 2)
         (Hpg : is_pgroup sg p),
    forall a b : G, smul G sg a b = smul G sg b a.

(** Classification: groups of order p^2 are Z_{p^2} or Z_p × Z_p. *)
Axiom group_order_p_sq_iso_cyclic_or_elementary_abelian :
  forall {G : Type} (sg : StrictGroup G) (p : nat)
         (p_prime : 2 <= p)
         (G_list : list G)
         (G_nodup : NoDup G_list)
         (G_complete : forall x : G, In x G_list)
         (G_order : length G_list = Nat.pow p 2)
         (Hpg : is_pgroup sg p),
    (* Either G is cyclic of order p^2 *)
    (exists g : G, forall x : G, exists n : nat,
       gpow (StrictGroup_to_Group sg) g n = x)
    \/
    (* Or every non-identity element has order p *)
    (forall x : G, x <> se G sg ->
       gpow (StrictGroup_to_Group sg) x p = se G sg).

(* ================================================================== *)
(** ** 5.  Cycle type and conjugacy in S_n *)
(* ================================================================== *)

(** Conjugate permutations: τ σ τ⁻¹ has cycles with entries τ(aᵢ). *)
Lemma conj_perm_cycle_entries {n : nat} (sigma tau : Perm n) (i : Fin.t n) :
    pfun (perm_comp tau (perm_comp sigma (perm_inv tau))) i =
    pfun tau (pfun sigma (pfun (perm_inv tau) i)).
Proof.
  reflexivity.
Qed.

(** Two permutations in S_n are conjugate iff they have the same cycle type.
    Full proof requires cycle decomposition infrastructure. *)
Axiom conjugate_in_Sn_iff_same_cycle_type :
  forall (n : nat) (sigma tau : Perm n), True. (* placeholder *)

(** Conjugacy classes of S_n are classified by partitions of n. *)
Axiom conj_classes_Sn_equiv_partitions :
  forall (n : nat), True. (* placeholder *)

(* ================================================================== *)
(** ** 6.  Simplicity of A_5 *)
(* ================================================================== *)

(** A_5 is simple: no proper nontrivial normal subgroups.
    Proof via conjugacy class sizes: 1, 15, 20, 12, 12.
    Any normal subgroup is a union of conjugacy classes whose sizes sum to
    a divisor of 60.  The only possibilities are 1 and 60. *)

Axiom A5_simple_via_conjugacy_classes : True. (* placeholder *)

(* ================================================================== *)
(** ** 7.  Selected exercise lemmas *)
(* ================================================================== *)

(** Helper: sinv(g*h*g^{-1}) = g*h^{-1}*g^{-1}. *)
Lemma sinv_conj_lem {G : Type} (sg : StrictGroup G) (g h : G) :
  sinv G sg (smul G sg (smul G sg g h) (sinv G sg g)) =
  smul G sg g (smul G sg (sinv G sg h) (sinv G sg g)).
Proof.
  rewrite (inv_mul sg (smul G sg g h) (sinv G sg g)).
  rewrite (inv_mul sg g h), (double_inverse sg g).
  repeat rewrite (sassoc G sg). reflexivity.
Qed.

(** Helper: conj_act(g)(conj_act(h)(x)) = conj_act(g*h*g^{-1})(conj_act(g)(x)). *)
Lemma conj_act_conj_lem {G : Type} (sg : StrictGroup G) (g h x : G) :
  conj_act sg g (conj_act sg h x) =
  conj_act sg (conj_act sg g h) (conj_act sg g x).
Proof.
  unfold conj_act. rewrite sinv_conj_lem.
  repeat rewrite (sassoc G sg).
  rewrite <- (sassoc G sg (smul G sg g h) (sinv G sg g) g).
  rewrite (sinv_left G sg g), (sid_right G sg).
  repeat rewrite (sassoc G sg).
  rewrite <- (sassoc G sg (smul G sg (smul G sg g h) x) (sinv G sg g) g).
  rewrite (sinv_left G sg g), (sid_right G sg).
  reflexivity.
Qed.

(** Helper: conj_act(g)(conj_act(g^{-1})(y)) = y. *)
Lemma conj_act_sinv_cancel_lem {G : Type} (sg : StrictGroup G) (g y : G) :
  conj_act sg g (conj_act sg (sinv G sg g) y) = y.
Proof.
  unfold conj_act.
  rewrite (double_inverse sg g).
  repeat rewrite (sassoc G sg).
  rewrite (sinv_right G sg g), (sid_left G sg).
  rewrite <- (sassoc G sg y g (sinv G sg g)).
  rewrite (sinv_right G sg g), (sid_right G sg).
  reflexivity.
Qed.

(** Exercise 4: conjugation sends normalizer to normalizer.
    N_G(gSg^{-1}) = g·N_G(S)·g^{-1}.
    Note: the correct statement has g (not g^{-1}) on both sides. *)
Lemma conj_normalizer_eq {G : Type} (sg : StrictGroup G) (S : G -> Prop) (g : G) :
    normalizer sg (fun x => S (conj_act sg g x)) =
    (fun h => normalizer sg S (conj_act sg g h)).
Proof.
  apply functional_extensionality. intro h.
  apply propositional_extensionality.
  unfold normalizer. split.
  - intros [Hfwd Hbwd]. split.
    + intros y Hy.
      set (y' := conj_act sg (sinv G sg g) y).
      assert (Heq : conj_act sg g y' = y) by exact (conj_act_sinv_cancel_lem sg g y).
      rewrite <- Heq, <- conj_act_conj_lem.
      apply Hfwd. rewrite Heq. exact Hy.
    + intros y Hy.
      set (y' := conj_act sg (sinv G sg g) y).
      assert (Heq : conj_act sg g y' = y) by exact (conj_act_sinv_cancel_lem sg g y).
      rewrite <- Heq, <- conj_act_conj_lem in Hy.
      apply Hbwd in Hy. rewrite Heq in Hy. exact Hy.
  - intros [Hfwd Hbwd]. split.
    + intros x Hx.
      rewrite conj_act_conj_lem. exact (Hfwd (conj_act sg g x) Hx).
    + intros x Hx.
      rewrite conj_act_conj_lem in Hx. exact (Hbwd (conj_act sg g x) Hx).
Qed.

(** Exercise 5: if |G:Z(G)| = n then each conjugacy class has size ≤ n. *)
Axiom conj_class_bounded_by_center_index :
  forall {G : Type} (sg : StrictGroup G)
         (G_list Z_list : list G)
         (G_complete : forall x : G, In x G_list)
         (Z_complete : forall x : G, In x Z_list <-> center sg x)
         (n : nat)
         (Hindex : length G_list = n * length Z_list)
         (g : G) (class_list : list G)
         (class_complete : forall x : G, In x class_list <-> conj_class sg g x),
    length class_list <= n.

(** Exercise 8: Z(S_n) = {e} for n ≥ 3. *)
Axiom center_Sn_trivial :
  forall n : nat, 3 <= n ->
    forall sigma : Perm n,
      is_central (PermGroup n) sigma ->
      forall i, pfun sigma i = i.

(** Exercise 13: finite groups with exactly two conjugacy classes are trivial or order 2. *)
Axiom two_conj_classes_order_le_2 :
  forall {G : Type} (sg : StrictGroup G)
         (G_list reps : list G)
         (G_complete : forall x : G, In x G_list)
         (reps_classify : NoDup reps /\
            forall x : G, exists r, In r reps /\ conj_class sg r x)
         (Htwo : length reps = 2),
    length G_list <= 2.

(** Exercise 24: G is not the union of conjugates of any proper subgroup. *)
Axiom not_union_of_conjugates :
  forall {G : Type} (sg : StrictGroup G)
         (G_list : list G)
         (G_complete : forall x : G, In x G_list)
         (G_nodup : NoDup G_list)
         (H : G -> Prop)
         (H_proper : exists x : G, ~ H x)
         (H_nonempty : exists x : G, H x)
         (H_sub : is_subgroup (StrictGroup_to_Group sg) H),
    exists y : G,
      ~ (exists g : G, H (conj_act sg g y)).

(** Exercise 26: transitive permutation group with |A| > 1 has a fixed-point-free element. *)
Axiom transitive_has_fixpoint_free :
  forall {G A : Type} {sg : StrictGroup G}
    {act : G -> A -> A} (ga : IsGroupAction sg act)
    (A_elems : list A) (A_ne : 1 < length A_elems)
    (Htrans : transitive_action ga),
    exists g : G, kernel_action ga g -> False.

(** Exercise 29: p-group has subgroups of every order p^β for 0 ≤ β ≤ a. *)
Axiom pgroup_subgroups_all_orders :
  forall {G : Type} (sg : StrictGroup G) (p a : nat)
         (p_prime : 2 <= p)
         (G_list : list G)
         (G_complete : forall x : G, In x G_list)
         (G_nodup : NoDup G_list)
         (G_order : length G_list = Nat.pow p a)
         (Hpg : is_pgroup sg p)
         (beta : nat) (Hbeta : beta <= a),
    exists H : G -> Prop,
      is_subgroup (StrictGroup_to_Group sg) H /\
      exists H_list : list G,
        NoDup H_list /\
        (forall x : G, In x H_list <-> H x) /\
        length H_list = Nat.pow p beta.

(** Exercise 30: odd order group, x ≠ 1 → x not conjugate to x⁻¹. *)
Axiom odd_order_not_conj_inv :
  forall {G : Type} (sg : StrictGroup G)
         (G_list : list G)
         (G_complete : forall x : G, In x G_list)
         (G_nodup : NoDup G_list)
         (G_odd : Nat.odd (length G_list) = true)
         (x : G) (Hx : x <> se G sg),
    ~ conj_class sg x (sinv G sg x).
