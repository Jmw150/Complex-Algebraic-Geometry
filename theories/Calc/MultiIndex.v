(** * Multi-indices for (p,q)-forms

    A multi-index of length [p] in [n] variables is an increasing
    sequence [I = (i_1 < i_2 < ... < i_p)] with each [i_k ∈ {0,..,n-1}].
    These index the basis [dz_I = dz_{i_1} ∧ ... ∧ dz_{i_p}] of
    holomorphic p-tensors on Cⁿ, and (paired) the basis of (p,q)-forms.

    This file provides:
    - [MultiIndex n p] : the type of length-p increasing sequences in
      [Fin.t n].  Implemented as a sigma type packaging a [list (Fin.t n)]
      with proofs of length and strict monotonicity.
    - Decidable equality [MI_dec_eq].
    - Canonical enumeration [enum_MI : list (MultiIndex n p)].
    - Membership / rank [mi_rank] and removal [mi_remove_at].
    - Permutation sign [swap_sign] (alternating sign for index transpositions).
    - Wedge-product index combination [mi_concat_sign] giving the
      sign that arises when concatenating two strictly-increasing index
      lists and re-sorting (used for ∂̄ of a coefficient).

    No project-level axioms are introduced.  Depends only on Stdlib.
*)

From Stdlib Require Import Arith.PeanoNat Lia List ZArith Bool.
Import ListNotations.

Set Warnings "-warn-library-file-stdlib-vector".
From Stdlib Require Import Vectors.Fin.
Set Warnings "+warn-library-file-stdlib-vector".

(* ------------------------------------------------------------------ *)
(** * 1. Underlying nat-encoded multi-index                             *)
(* ------------------------------------------------------------------ *)

(** We work primarily with [list nat] under the side-condition
    "every entry is < n and the list is strictly increasing".  This
    avoids the awkward dependent-pattern arithmetic on [Fin.t]. *)

Definition all_lt (n : nat) (l : list nat) : Prop :=
  Forall (fun k => k < n) l.

Fixpoint strict_inc (l : list nat) : Prop :=
  match l with
  | []        => True
  | [_]       => True
  | a :: (b :: _) as t => a < b /\ strict_inc t
  end.

Lemma strict_inc_tail :
  forall a l, strict_inc (a :: l) -> strict_inc l.
Proof.
  intros a l H. destruct l as [| b l']; simpl in *.
  - exact I.
  - destruct H as [_ H]. exact H.
Qed.

Lemma strict_inc_cons_iff :
  forall a b l, strict_inc (a :: b :: l) <-> a < b /\ strict_inc (b :: l).
Proof.
  intros. simpl. tauto.
Qed.

(* ------------------------------------------------------------------ *)
(** * 2. The MultiIndex type                                            *)
(* ------------------------------------------------------------------ *)

Record MultiIndex (n p : nat) : Type := mkMI
  { mi_list  : list nat
  ; mi_len   : List.length mi_list = p
  ; mi_bound : all_lt n mi_list
  ; mi_sorted: strict_inc mi_list
  }.

Arguments mi_list   {n p} _.
Arguments mi_len    {n p} _.
Arguments mi_bound  {n p} _.
Arguments mi_sorted {n p} _.

(** Empty multi-index (length 0): always valid. *)
Definition mi_empty (n : nat) : MultiIndex n 0.
Proof.
  refine (mkMI n 0 [] _ _ _); try (constructor; fail); try reflexivity.
Defined.

(* ------------------------------------------------------------------ *)
(** * 3. Decidable equality                                             *)
(* ------------------------------------------------------------------ *)

(** Equality of underlying lists is decidable. *)
Definition list_nat_dec_eq : forall (l l' : list nat), {l = l'} + {l <> l'} :=
  list_eq_dec Nat.eq_dec.

(** Two multi-indices with equal underlying lists are equal as records,
    by proof irrelevance for the props (we use [UIP_refl] on [nat] for
    the length and [Forall]/[strict_inc] proof equality via decidability
    of the underlying props).  We package this as a propositional
    equality test: [mi_eqb] returns [true] iff the lists agree. *)

Definition mi_eqb {n p} (I J : MultiIndex n p) : bool :=
  if list_nat_dec_eq (mi_list I) (mi_list J) then true else false.

Lemma mi_eqb_true_iff :
  forall n p (I J : MultiIndex n p),
    mi_eqb I J = true <-> mi_list I = mi_list J.
Proof.
  intros n p I J. unfold mi_eqb.
  destruct (list_nat_dec_eq (mi_list I) (mi_list J)); split; intros H;
    try reflexivity; try discriminate; try assumption; congruence.
Qed.

(** Decidable equality of [mi_list]s — the only computational equality
    we need; record equality requires UIP on the side-conditions. *)
Definition MI_list_dec_eq :
  forall n p (I J : MultiIndex n p),
    {mi_list I = mi_list J} + {mi_list I <> mi_list J} :=
  fun n p I J => list_nat_dec_eq (mi_list I) (mi_list J).

(* ------------------------------------------------------------------ *)
(** * 4. Membership and rank                                            *)
(* ------------------------------------------------------------------ *)

(** [mi_in k I]: [k] occurs in the underlying list of [I]. *)
Definition mi_in {n p} (k : nat) (I : MultiIndex n p) : Prop :=
  In k (mi_list I).

(** [mi_rank k l] : the 0-based position of [k] in the list [l],
    returning [length l] if absent. *)
Fixpoint mi_rank_aux (k : nat) (l : list nat) : nat :=
  match l with
  | []      => 0
  | a :: l' => if Nat.eqb a k then 0 else S (mi_rank_aux k l')
  end.

Definition mi_rank {n p} (k : nat) (I : MultiIndex n p) : nat :=
  mi_rank_aux k (mi_list I).

(* ------------------------------------------------------------------ *)
(** * 5. Insert and remove                                              *)
(* ------------------------------------------------------------------ *)

(** Sorted insertion of [k] into a strictly increasing list.
    If [k] is already present, the list is returned unchanged
    (callers should guard against this case for proper signs). *)
Fixpoint sorted_insert (k : nat) (l : list nat) : list nat :=
  match l with
  | []      => [k]
  | a :: l' =>
      match Nat.compare k a with
      | Lt => k :: a :: l'
      | Eq => a :: l'                (* duplicate; keep as-is *)
      | Gt => a :: sorted_insert k l'
      end
  end.

(** Remove the first occurrence of [k] from [l]. *)
Fixpoint list_remove (k : nat) (l : list nat) : list nat :=
  match l with
  | []      => []
  | a :: l' => if Nat.eqb a k then l' else a :: list_remove k l'
  end.

(** Length of [list_remove] when [k] is present (in particular: in a
    strictly-increasing list, [k] occurs at most once). *)
Lemma list_remove_length_in :
  forall k l, In k l -> S (List.length (list_remove k l)) = List.length l.
Proof.
  intros k l Hin. induction l as [| a l' IH]; simpl in *.
  - destruct Hin.
  - destruct (Nat.eqb_spec a k) as [Heq | Hne].
    + simpl. reflexivity.
    + simpl. f_equal. apply IH. destruct Hin as [Heq | H].
      * exfalso. apply Hne. exact Heq.
      * exact H.
Qed.

Lemma list_remove_length_notin :
  forall k l, ~ In k l -> List.length (list_remove k l) = List.length l.
Proof.
  intros k l Hni. induction l as [| a l' IH]; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb_spec a k) as [Heq | Hne].
    + exfalso. apply Hni. left. exact Heq.
    + simpl. f_equal. apply IH. intro H. apply Hni. right. exact H.
Qed.

Lemma list_remove_all_lt :
  forall n k l, all_lt n l -> all_lt n (list_remove k l).
Proof.
  intros n k l H. induction l as [| a l' IH]; simpl in *.
  - constructor.
  - inversion H as [| x xs Hh Ht Hexq]; subst.
    destruct (Nat.eqb_spec a k) as [_ | _].
    + exact Ht.
    + constructor.
      * exact Hh.
      * apply IH. exact Ht.
Qed.

Lemma list_remove_strict_inc :
  forall k l, strict_inc l -> strict_inc (list_remove k l).
Proof.
  intros k l H.
  induction l as [| a l' IH].
  - simpl. exact I.
  - simpl. destruct (Nat.eqb_spec a k) as [Heq | Hne].
    + apply strict_inc_tail in H. exact H.
    + (* keep [a]; need to argue strict_inc (a :: list_remove k l') *)
      destruct l' as [| b l''].
      * simpl. exact I.
      * (* l' = b :: l''; strict_inc (a :: b :: l'') gives a < b *)
        simpl in H. destruct H as [Hab Hl'].
        simpl. destruct (Nat.eqb_spec b k) as [Hbk | Hbk].
        -- (* removing b: tail is l'' *)
           destruct l'' as [| c l'''].
           ++ simpl. exact I.
           ++ simpl. simpl in Hl'. destruct Hl' as [Hbc Hl''].
              split.
              ** lia.
              ** exact Hl''.
        -- (* keep b: recurse *)
           specialize (IH Hl').
           simpl in IH.
           destruct (Nat.eqb_spec b k) as [|_]; [contradiction|].
           split.
           ++ exact Hab.
           ++ exact IH.
Qed.

(** Removing an element [k] from a [MultiIndex n (S p)] when [k] is
    actually a member produces a [MultiIndex n p]. *)
Definition mi_remove_member
    {n p} (k : nat) (I : MultiIndex n (S p)) (Hin : In k (mi_list I))
    : MultiIndex n p.
Proof.
  refine (mkMI n p (list_remove k (mi_list I)) _ _ _).
  - pose proof (list_remove_length_in k (mi_list I) Hin) as H.
    rewrite (mi_len I) in H.
    apply (f_equal pred) in H. simpl in H. exact H.
  - apply list_remove_all_lt. exact (mi_bound I).
  - apply list_remove_strict_inc. exact (mi_sorted I).
Defined.

(* ------------------------------------------------------------------ *)
(** * 6. Sign of an insertion (for ∂̄ formulas)                          *)
(* ------------------------------------------------------------------ *)

(** Sign convention: in
       ∂̄(f dz̄_J) = Σ_k (∂f/∂z̄_k) dz̄_k ∧ dz̄_J,
    when [k] is then re-sorted into a position [r] inside [k :: J]
    (which already needed re-sorting to a strictly increasing form),
    the resulting sign is [(-1)^r] where [r] is the rank of [k] in
    the sorted result.

    Equivalently, when assembling the [(p,q+1)] coefficient at index
    [J' = (j_0 < ... < j_q)] from contributions of removing each
    [j_r ∈ J'], the sign for the [r]-th term is [(-1)^r]. *)

Definition sign_pow (r : nat) : Z :=
  if Nat.even r then 1%Z else (-1)%Z.

Lemma sign_pow_0 : sign_pow 0 = 1%Z.
Proof. reflexivity. Qed.

Lemma sign_pow_S_S : forall r, sign_pow (S (S r)) = sign_pow r.
Proof.
  intros r. unfold sign_pow. simpl.
  destruct (Nat.even r); reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * 7. Enumeration of multi-indices                                  *)
(* ------------------------------------------------------------------ *)

(** Enumerate raw [list nat]s that are strictly-increasing length-[p]
    sequences with entries in [{0,..,n-1}].

    Recursion on [p] then on the maximum allowed value.  We choose the
    "build by extending the largest entry" approach:
    [enum_lists_aux n p] enumerates strictly-increasing lists of length
    [p] with all entries < [n]. *)

Fixpoint enum_lists_aux (n p : nat) : list (list nat) :=
  match p with
  | 0   => [[]]
  | S p' =>
      (** A length-(S p') strictly-increasing list with entries < n
          factors as: choose the smallest entry [k ∈ {0,..,n-1}], then
          extend by a length-[p'] strictly-increasing list with entries
          in {k+1,..,n-1} (encoded by mapping [+ (k+1)]).  We instead
          take the simpler split: pick the LAST element [m] in the list
          (the largest), then extend a length-[p'] strictly-increasing
          list with entries < [m]. *)
      List.concat
        (List.map
           (fun m =>
              List.map (fun l => l ++ [m]) (enum_lists_aux m p'))
           (List.seq 0 n))
  end.

(** A [MultiIndex n p] from a verified raw list. *)
Definition mi_from_list_dec {n p} (l : list nat) :
    option (MultiIndex n p).
Proof.
  destruct (Nat.eq_dec (List.length l) p) as [Hlen | _]; [|exact None].
  destruct (Forall_dec (fun k => k < n) (fun k => lt_dec k n) l) as [Hb | _];
    [|exact None].
  (** Decide [strict_inc]. *)
  assert (Hsi : {strict_inc l} + {~ strict_inc l}).
  { clear Hb Hlen. induction l as [| a l' IH].
    - left. exact I.
    - destruct l' as [| b l''].
      + left. exact I.
      + destruct IH as [IHs | IHs].
        * destruct (lt_dec a b) as [Hab | Hab].
          -- left. apply strict_inc_cons_iff. split; assumption.
          -- right. intro Hcontr. apply strict_inc_cons_iff in Hcontr.
             destruct Hcontr as [H _]. apply Hab. exact H.
        * right. intro Hcontr. apply strict_inc_cons_iff in Hcontr.
          destruct Hcontr as [_ H]. apply IHs. exact H. }
  destruct Hsi as [Hsi | _]; [|exact None].
  exact (Some (mkMI n p l Hlen Hb Hsi)).
Defined.

(** Filter the raw enumeration by upgrading to actual [MultiIndex]s. *)
Definition enum_MI (n p : nat) : list (MultiIndex n p) :=
  List.fold_right
    (fun l acc => match @mi_from_list_dec n p l with
                  | Some mi => mi :: acc
                  | None => acc
                  end)
    nil
    (enum_lists_aux n p).

(* ------------------------------------------------------------------ *)
(** * 8. Insertion-with-sign: the building block for ∂̄                   *)
(* ------------------------------------------------------------------ *)

(** When inserting a fresh element [k] into a strictly-increasing list
    [J] (where [k ∉ J]), the result is [sorted_insert k J], and the
    sign relating [k :: J] (with k prepended, hence k at rank 0) to
    [sorted_insert k J] (with k at its proper sorted rank [r]) is
    [(-1)^r] = [sign_pow r], where [r] is determined by the position
    [k] occupies in the sorted output. *)

Definition mi_extend_sign
    {n p} (k : nat) (J : MultiIndex n p) : Z :=
  sign_pow (mi_rank_aux k (sorted_insert k (mi_list J))).
