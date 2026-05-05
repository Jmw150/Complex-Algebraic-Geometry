(** * HallFreeGroup/StallingsFolding.v

    Stallings folding: given a finite labeled graph (e.g., a petal
    graph for a finitely generated subgroup), iteratively identify
    pairs of edges sharing source AND label until the graph is folded.

    Termination: each fold strictly decreases the number of vertices.
    Correctness: the folded graph represents the same subgroup of F_r
    (same set of words readable as paths from basepoint to basepoint). *)

From CAG Require Import FreeGroup.
From CAG Require Import HallFreeGroup.LabeledGraph.
From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.

(* ================================================================== *)
(** * 1. Detecting fold opportunities                                   *)
(* ================================================================== *)

(** A "fold pair" is a pair of edges with the same source and label
    but different targets — these need to be identified by the fold
    operation. *)

Section FoldPairs.
  Context {r : nat}.

  Definition is_fold_pair (e1 e2 : Edge r) : bool :=
    if Nat.eqb e1.(e_src) e2.(e_src) then
      if letter_eq_dec e1.(e_lbl) e2.(e_lbl) then
        if Nat.eqb e1.(e_tgt) e2.(e_tgt) then false  (* same edge *)
        else true
      else false
    else false.

  (** Find the first pair of edges in the graph that need to be folded.
      Returns [Some (i, j)] where i, j are list indices, or [None] if
      the graph is already folded. *)
  Fixpoint find_fold_pair_aux (edges : list (Edge r))
      (other_edges : list (Edge r))
      : option (Edge r * Edge r) :=
    match edges with
    | [] => None
    | e :: rest =>
        let candidates := filter (fun e' => is_fold_pair e e') other_edges in
        match candidates with
        | c :: _ => Some (e, c)
        | [] =>
            (* Try with rest of edges, removing e from other_edges. *)
            find_fold_pair_aux rest (filter
              (fun e' => negb (
                Nat.eqb e'.(e_src) e.(e_src) &&
                (if letter_eq_dec e'.(e_lbl) e.(e_lbl) then true else false) &&
                Nat.eqb e'.(e_tgt) e.(e_tgt)))
              other_edges)
        end
    end.

  Definition find_fold_pair (G : LGraph r) : option (Edge r * Edge r) :=
    find_fold_pair_aux G.(lg_edges) G.(lg_edges).

End FoldPairs.

(* ================================================================== *)
(** * 2. Performing a fold                                              *)
(* ================================================================== *)

(** Identify two vertices: replace every occurrence of [v1] with [v2]
    in the graph, and remove [v1] from the vertex list. *)

Section IdentifyVertex.
  Context {r : nat}.

  Definition replace_vertex (v1 v2 : Vertex) (v : Vertex) : Vertex :=
    if Nat.eqb v v1 then v2 else v.

  Definition replace_in_edge (v1 v2 : Vertex) (e : Edge r) : Edge r :=
    mkEdge (replace_vertex v1 v2 e.(e_src))
           e.(e_lbl)
           (replace_vertex v1 v2 e.(e_tgt)).

  Definition identify_vertices (v1 v2 : Vertex) (G : LGraph r) : LGraph r :=
    let new_verts := filter (fun v => negb (Nat.eqb v v1)) G.(lg_verts) in
    let new_edges := map (replace_in_edge v1 v2) G.(lg_edges) in
    (* Remove duplicate edges. *)
    let dedup_edges := nodup edge_eq_dec new_edges in
    mkLG new_verts dedup_edges (replace_vertex v1 v2 G.(lg_base)).

  (** Single fold step: if there's a fold pair, identify the two
      target vertices. *)
  Definition fold_step (G : LGraph r) : option (LGraph r) :=
    match find_fold_pair G with
    | None => None
    | Some (e1, e2) => Some (identify_vertices e1.(e_tgt) e2.(e_tgt) G)
    end.

End IdentifyVertex.

(* ================================================================== *)
(** * 3. Iterated folding (with fuel)                                   *)
(* ================================================================== *)

(** Apply [fold_step] up to [fuel] times. Since each fold strictly
    decreases vertex count, fuel = num_vertices is enough. *)

Fixpoint fold_iterate {r : nat} (fuel : nat) (G : LGraph r) : LGraph r :=
  match fuel with
  | 0 => G
  | S k =>
      match fold_step G with
      | None => G
      | Some G' => fold_iterate k G'
      end
  end.

(** The "Stallings core" graph: petal-graph + iterated folding. *)
Definition stallings_core {r : nat} (w : list (Letter r)) : LGraph r :=
  let G := petal_graph w in
  fold_iterate (num_vertices G) G.

(* ================================================================== *)
(** * 4. Termination and correctness                                    *)
(* ================================================================== *)

(** ** Helpers for fold-step termination. *)

(** A graph is "well-formed" if every edge target is in the vertex
    list. This is preserved by fold_step. *)
Definition wf_graph {r : nat} (G : LGraph r) : Prop :=
  forall e : Edge r,
    In e G.(lg_edges) ->
    In e.(e_src) G.(lg_verts) /\ In e.(e_tgt) G.(lg_verts).

(** is_fold_pair e1 e2 = true implies the targets differ. *)
Lemma is_fold_pair_diff_targets {r : nat} :
  forall e1 e2 : Edge r,
    is_fold_pair e1 e2 = true ->
    e1.(e_tgt) <> e2.(e_tgt).
Proof.
  intros e1 e2 H Heq.
  unfold is_fold_pair in H.
  destruct (Nat.eqb e1.(e_src) e2.(e_src)) eqn:Hs; [|discriminate].
  destruct (letter_eq_dec e1.(e_lbl) e2.(e_lbl)) as [Hl|Hl]; [|discriminate].
  destruct (Nat.eqb e1.(e_tgt) e2.(e_tgt)) eqn:Ht.
  - discriminate.
  - apply Nat.eqb_neq in Ht. apply Ht. exact Heq.
Qed.

(** Length of filter is at most length of list. *)
Lemma filter_length_le : forall {A : Type} (p : A -> bool) (l : list A),
    length (filter p l) <= length l.
Proof.
  induction l as [|x rest IH]; simpl; [reflexivity|].
  destruct (p x); simpl; lia.
Qed.

(** filter (negb ∘ eqb v1) preserves length minus 1 when v1 ∈ list. *)
Lemma filter_neq_length :
  forall (v1 : Vertex) (l : list Vertex),
    In v1 l ->
    length (filter (fun v => negb (Nat.eqb v v1)) l) < length l.
Proof.
  intros v1 l Hin.
  induction l as [|x rest IH]; [inversion Hin|].
  simpl in Hin. destruct Hin as [Heq | Hin'].
  - subst x. simpl. rewrite Nat.eqb_refl. simpl.
    pose proof (filter_length_le (fun v => negb (Nat.eqb v v1)) rest) as Hbnd.
    apply Nat.lt_succ_r. exact Hbnd.
  - simpl. specialize (IH Hin').
    destruct (Nat.eqb x v1); simpl; lia.
Qed.

(** Identifying two distinct vertices in a graph (when v1 is in the
    vertex set) strictly decreases the vertex count. *)
Lemma identify_vertices_decreases_strict {r : nat} :
  forall (v1 v2 : Vertex) (G : LGraph r),
    In v1 G.(lg_verts) ->
    v1 <> v2 ->
    num_vertices (identify_vertices v1 v2 G) < num_vertices G.
Proof.
  intros v1 v2 G Hin Hneq.
  unfold identify_vertices, num_vertices. simpl.
  apply filter_neq_length. exact Hin.
Qed.

(** ** Discharging fold_step_decreases. *)

(** find_fold_pair_aux returns edges that have is_fold_pair = true. *)
Lemma find_fold_pair_aux_correct {r : nat} :
  forall (edges other : list (Edge r)) (e1 e2 : Edge r),
    find_fold_pair_aux edges other = Some (e1, e2) ->
    is_fold_pair e1 e2 = true.
Proof.
  induction edges as [|e rest IH]; intros other a b Hf.
  - simpl in Hf. discriminate.
  - simpl in Hf.
    destruct (filter (fun e' => is_fold_pair e e') other)
      as [|c cs] eqn:Hc.
    + apply (IH _ _ _ Hf).
    + injection Hf as Hf1 Hf2.
      assert (Hin : In c (filter (fun e' => is_fold_pair e e') other)).
      { rewrite Hc. left. reflexivity. }
      apply filter_In in Hin. destruct Hin as [_ Hpair].
      subst. exact Hpair.
Qed.

Lemma find_fold_pair_correct {r : nat} :
  forall (G : LGraph r) (e1 e2 : Edge r),
    find_fold_pair G = Some (e1, e2) ->
    is_fold_pair e1 e2 = true.
Proof.
  intros G e1 e2 H. apply (find_fold_pair_aux_correct _ _ _ _ H).
Qed.

(** find_fold_pair_aux returns edges that are in [edges] ∪ [other]. *)
Lemma find_fold_pair_aux_in_lists {r : nat} :
  forall (edges other : list (Edge r)) (e1 e2 : Edge r),
    find_fold_pair_aux edges other = Some (e1, e2) ->
    In e1 edges /\ In e2 other.
Proof.
  induction edges as [|e rest IH]; intros other a b Hf.
  - simpl in Hf. discriminate.
  - simpl in Hf.
    destruct (filter (fun e' => is_fold_pair e e') other)
      as [|c cs] eqn:Hc.
    + (* recurse on rest with a filtered other *)
      apply IH in Hf. destruct Hf as [Hin_a Hin_b].
      split.
      * right. exact Hin_a.
      * (* Hin_b ∈ filter(...) other ⊆ other *)
        apply filter_In in Hin_b. apply Hin_b.
    + injection Hf as Hf1 Hf2.
      assert (Hin : In c (filter (fun e' => is_fold_pair e e') other)).
      { rewrite Hc. left. reflexivity. }
      apply filter_In in Hin. destruct Hin as [Hin_oth _].
      subst. split; [left; reflexivity | exact Hin_oth].
Qed.

Lemma find_fold_pair_in_graph {r : nat} :
  forall (G : LGraph r) (e1 e2 : Edge r),
    find_fold_pair G = Some (e1, e2) ->
    In e1 G.(lg_edges) /\ In e2 G.(lg_edges).
Proof.
  intros G e1 e2 H.
  apply (find_fold_pair_aux_in_lists G.(lg_edges) G.(lg_edges) e1 e2 H).
Qed.

(** Each fold step strictly decreases the number of vertices, provided
    the graph is well-formed (all edge targets are in the vertex set). *)
(** fold_step_decreases_wf: provable but the Coq-elaboration
    of `find_fold_pair_correct` gets confused under nested options
    pattern-matching. Left as a future-work item. *)

(** Direct proof using is_fold_pair_diff_targets without intermediate
    lemmas. The cleanest version of fold_step_decreases under wf
    + a "find_fold_pair returns first edge in graph" hypothesis. *)

Lemma fold_step_decreases_clean {r : nat} :
  forall (G : LGraph r) (e1 e2 : Edge r),
    fold_step G = Some (identify_vertices e1.(e_tgt) e2.(e_tgt) G) ->
    is_fold_pair e1 e2 = true ->
    In e1.(e_tgt) G.(lg_verts) ->
    num_vertices (identify_vertices e1.(e_tgt) e2.(e_tgt) G) < num_vertices G.
Proof.
  intros G e1 e2 _ Hpair Hin.
  apply identify_vertices_decreases_strict.
  - exact Hin.
  - apply (is_fold_pair_diff_targets _ _ Hpair).
Qed.

(** Final wf version: combining the helpers, under wf + an
    "in-graph" hypothesis on find_fold_pair, fold_step strictly
    decreases vertex count. *)

Lemma fold_step_decreases_wf {r : nat} :
  forall (G G' : LGraph r),
    wf_graph G ->
    (forall e1 e2,
       find_fold_pair G = Some (e1, e2) ->
       In e1 G.(lg_edges) /\ In e2 G.(lg_edges)) ->
    fold_step G = Some G' -> num_vertices G' < num_vertices G.
Proof.
  intros G G' Hwf Hffp Hfs.
  unfold fold_step in Hfs.
  case_eq (find_fold_pair G); [|intros Hnone; rewrite Hnone in Hfs; discriminate].
  intros [e1 e2] Hfp.
  rewrite Hfp in Hfs.
  injection Hfs as HG'. subst G'.
  pose proof (@find_fold_pair_correct r G e1 e2 Hfp) as Hpair.
  pose proof (Hffp e1 e2 Hfp) as [Hin1 _].
  pose proof (Hwf e1 Hin1) as [_ Htgt1].
  apply identify_vertices_decreases_strict.
  - exact Htgt1.
  - apply (is_fold_pair_diff_targets _ _ Hpair).
Qed.

(** Final clean fold_step termination: under wf, fold_step decreases.
    This combines all the helpers — fully axiom-free. *)

Theorem fold_step_decreases_under_wf {r : nat} :
  forall (G G' : LGraph r),
    wf_graph G ->
    fold_step G = Some G' -> num_vertices G' < num_vertices G.
Proof.
  intros G G' Hwf Hfs.
  apply (fold_step_decreases_wf G G' Hwf).
  - intros e1 e2 Hfp.
    apply (@find_fold_pair_in_graph r G e1 e2 Hfp).
  - exact Hfs.
Qed.

(** is_fold_pair is symmetric. *)
Lemma is_fold_pair_sym {r : nat} :
  forall e1 e2 : Edge r,
    is_fold_pair e1 e2 = is_fold_pair e2 e1.
Proof.
  intros e1 e2. unfold is_fold_pair.
  rewrite (Nat.eqb_sym e1.(e_src) e2.(e_src)).
  destruct (Nat.eqb e2.(e_src) e1.(e_src)); [|reflexivity].
  destruct (letter_eq_dec e1.(e_lbl) e2.(e_lbl)) as [Hl|Hl];
  destruct (letter_eq_dec e2.(e_lbl) e1.(e_lbl)) as [Hl'|Hl'];
    try (symmetry in Hl; contradiction);
    try (symmetry in Hl'; contradiction).
  - rewrite (Nat.eqb_sym e1.(e_tgt) e2.(e_tgt)). reflexivity.
  - reflexivity.
Qed.

(** If e2 has same src/lbl/tgt as e (i.e., is a "duplicate" copy of e),
    then is_fold_pair e1 e2 = is_fold_pair e1 e for any e1. *)
Lemma is_fold_pair_replace_dup {r : nat} :
  forall e1 e e2 : Edge r,
    e2.(e_src) = e.(e_src) ->
    e2.(e_lbl) = e.(e_lbl) ->
    e2.(e_tgt) = e.(e_tgt) ->
    is_fold_pair e1 e2 = is_fold_pair e1 e.
Proof.
  intros e1 e e2 Hs Hl Ht. unfold is_fold_pair.
  rewrite Hs, Ht. destruct (Nat.eqb e1.(e_src) e.(e_src)); [|reflexivity].
  destruct (letter_eq_dec e1.(e_lbl) e2.(e_lbl)) as [H1|H1];
  destruct (letter_eq_dec e1.(e_lbl) e.(e_lbl)) as [H2|H2];
    try (rewrite Hl in H1; contradiction);
    try (rewrite <- Hl in H2; contradiction);
    reflexivity.
Qed.

(** filter p l = [] iff every element of l fails p. *)
Lemma filter_nil_all_false {A : Type} (p : A -> bool) (l : list A) :
  filter p l = [] -> forall x, In x l -> p x = false.
Proof.
  intros Hnil x Hin.
  destruct (p x) eqn:Hpx; [|reflexivity].
  exfalso.
  assert (Hf : In x (filter p l)).
  { apply filter_In. split; assumption. }
  rewrite Hnil in Hf. inversion Hf.
Qed.

(** find_fold_pair_aux returns None iff no fold pair exists across (edges, other). *)

(** find_fold_pair_aux returning None implies no fold pair exists.
    Full proof requires careful handling of duplicate edges in the
    filtered `other`; left as a future-work item. The infrastructure
    helper lemmas (filter_nil_all_false, is_fold_pair_replace_dup,
    is_fold_pair_sym) are now in place for that proof. *)

(** Specialization to the no-duplicate case: if find_fold_pair_aux
    returns None and other has no duplicates, then no fold pair. *)

(** Contrapositive (complete version): if a fold pair exists with
    BOTH endpoints in `other`, the search finds something. We
    require the head's edge to be in `other` for the recursion. *)

Lemma find_fold_pair_aux_complete_first {r : nat} :
  forall (other : list (Edge r)) (e e2 : Edge r),
    In e2 other -> is_fold_pair e e2 = true ->
    filter (fun e' => is_fold_pair e e') other <> [].
Proof.
  intros other e e2 Hin Hpair.
  destruct (filter (fun e' => is_fold_pair e e') other) eqn:Hfilt;
    [|discriminate].
  exfalso.
  pose proof (filter_nil_all_false _ other Hfilt e2 Hin) as Hf.
  simpl in Hf. rewrite Hpair in Hf. discriminate.
Qed.

Lemma find_fold_pair_aux_finds_head {r : nat} :
  forall (rest other : list (Edge r)) (e e2 : Edge r),
    In e2 other -> is_fold_pair e e2 = true ->
    find_fold_pair_aux (e :: rest) other <> None.
Proof.
  intros rest other e e2 Hin Hpair Hnone.
  simpl in Hnone.
  pose proof (find_fold_pair_aux_complete_first other e e2 Hin Hpair) as Hnemp.
  destruct (filter (fun e' => is_fold_pair e e') other) as [|c cs] eqn:Hfilt;
    [contradiction|].
  discriminate.
Qed.

(** A list with two distinct elements has length ≥ 2. *)
Lemma length_two_from_distinct_in {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) :
  forall (x y : A) (l : list A),
    In x l -> In y l -> x <> y -> 2 <= length l.
Proof.
  intros x y l Hx Hy Hneq.
  destruct l as [|a [|b rest]]; [inversion Hx | | simpl; lia].
  exfalso. simpl in Hx, Hy.
  destruct Hx as [Hxe | []], Hy as [Hye | []]; subst; contradiction.
Qed.

(** Folded graph has no fold pair. *)
Lemma is_folded_no_fold_pair {r : nat} :
  forall (G : LGraph r) (e1 e2 : Edge r),
    is_folded G ->
    In e1 G.(lg_edges) -> In e2 G.(lg_edges) ->
    is_fold_pair e1 e2 = true ->
    False.
Proof.
  intros G e1 e2 Hfold Hin1 Hin2 Hpair.
  unfold is_folded in Hfold.
  pose proof (Hfold e1.(e_src) e1.(e_lbl)) as Hcnt.
  unfold out_count, out_edges in Hcnt.
  unfold is_fold_pair in Hpair.
  destruct (Nat.eqb e1.(e_src) e2.(e_src)) eqn:Hs; [|discriminate].
  destruct (letter_eq_dec e1.(e_lbl) e2.(e_lbl)) as [Hl|Hl]; [|discriminate].
  destruct (Nat.eqb e1.(e_tgt) e2.(e_tgt)) eqn:Ht; [discriminate|].
  apply Nat.eqb_eq in Hs.
  apply Nat.eqb_neq in Ht.
  (* Both e1 and e2 are in the filtered list. *)
  assert (Hf1 : In e1 (filter (fun e =>
      if Nat.eqb e.(e_src) e1.(e_src) then
        if letter_eq_dec e.(e_lbl) e1.(e_lbl) then true else false
      else false) G.(lg_edges))).
  { apply filter_In. split; [exact Hin1|].
    rewrite Nat.eqb_refl. destruct (letter_eq_dec e1.(e_lbl) e1.(e_lbl)); [reflexivity|contradiction]. }
  assert (Hf2 : In e2 (filter (fun e =>
      if Nat.eqb e.(e_src) e1.(e_src) then
        if letter_eq_dec e.(e_lbl) e1.(e_lbl) then true else false
      else false) G.(lg_edges))).
  { apply filter_In. split; [exact Hin2|].
    rewrite <- Hs, Nat.eqb_refl.
    destruct (letter_eq_dec e2.(e_lbl) e1.(e_lbl)) as [|Hne];
      [reflexivity | symmetry in Hl; contradiction]. }
  (* e1 ≠ e2 since their targets differ. *)
  assert (Hneq : e1 <> e2).
  { intro Heq. subst e2. apply Ht. reflexivity. }
  pose proof (length_two_from_distinct_in edge_eq_dec _ _ _ Hf1 Hf2 Hneq) as Hlen.
  lia.
Qed.

(** Corollary: if find_fold_pair returns Some, the graph isn't folded. *)
Lemma find_fold_pair_some_not_folded {r : nat} :
  forall (G : LGraph r) (e1 e2 : Edge r),
    find_fold_pair G = Some (e1, e2) ->
    ~ is_folded G.
Proof.
  intros G e1 e2 Hfp Hfolded.
  pose proof (@find_fold_pair_correct r G e1 e2 Hfp) as Hpair.
  pose proof (@find_fold_pair_in_graph r G e1 e2 Hfp) as [Hin1 Hin2].
  apply (@is_folded_no_fold_pair r G e1 e2 Hfolded Hin1 Hin2 Hpair).
Qed.

(** Contrapositive: if G is folded, find_fold_pair returns None. *)
Lemma is_folded_find_fold_pair_none {r : nat} :
  forall (G : LGraph r),
    is_folded G ->
    find_fold_pair G = None.
Proof.
  intros G Hfolded.
  destruct (find_fold_pair G) as [[e1 e2]|] eqn:Hfp; [|reflexivity].
  exfalso. apply (@find_fold_pair_some_not_folded r G e1 e2 Hfp Hfolded).
Qed.

(** Final: fold_step on a folded graph returns None (no progress). *)
Lemma is_folded_fold_step_none {r : nat} :
  forall (G : LGraph r),
    is_folded G ->
    fold_step G = None.
Proof.
  intros G Hfolded.
  unfold fold_step.
  rewrite (is_folded_find_fold_pair_none G Hfolded).
  reflexivity.
Qed.

(** fold_iterate on a folded graph is a no-op. *)
Lemma fold_iterate_folded_is_id {r : nat} :
  forall (fuel : nat) (G : LGraph r),
    is_folded G ->
    fold_iterate fuel G = G.
Proof.
  induction fuel as [|k IH]; intros G Hfolded; [reflexivity|].
  simpl. rewrite (is_folded_fold_step_none G Hfolded). reflexivity.
Qed.

(** If fold_step G = None, fold_iterate fuel G = G for any fuel. *)
Lemma fold_iterate_step_none {r : nat} :
  forall (fuel : nat) (G : LGraph r),
    fold_step G = None ->
    fold_iterate fuel G = G.
Proof.
  induction fuel as [|k IH]; intros G Hfs; [reflexivity|].
  simpl. rewrite Hfs. reflexivity.
Qed.

(** fold_iterate decomposes: (a+b) iterations = b after a. *)
Lemma fold_iterate_decompose {r : nat} :
  forall (a b : nat) (G : LGraph r),
    fold_iterate (a + b) G = fold_iterate b (fold_iterate a G).
Proof.
  induction a as [|k IH]; intros b G; [reflexivity|].
  simpl. destruct (fold_step G) as [G'|] eqn:Hfs.
  - apply IH.
  - symmetry. apply fold_iterate_step_none. exact Hfs.
Qed.

(** ** Preservation of well-formedness under fold operations. *)

(** Filtering vertices: v stays in filtered list iff v ∈ original AND v ≠ v1. *)
Lemma in_filter_neq {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) :
  forall (v1 v : A) (l : list A),
    In v (filter (fun x => negb (if eq_dec x v1 then true else false)) l) <->
    In v l /\ v <> v1.
Proof.
  intros v1 v l. split.
  - intro H. apply filter_In in H. destruct H as [Hin Hneg].
    split; [exact Hin|]. destruct (eq_dec v v1); [discriminate|]. assumption.
  - intros [Hin Hneq]. apply filter_In. split; [exact Hin|].
    destruct (eq_dec v v1); [contradiction|reflexivity].
Qed.

Lemma in_filter_neqb (v1 v : Vertex) (l : list Vertex) :
  In v (filter (fun x => negb (Nat.eqb x v1)) l) <-> In v l /\ v <> v1.
Proof.
  split.
  - intro H. apply filter_In in H. destruct H as [Hin Hneg].
    split; [exact Hin|].
    intro Heq. subst v. rewrite Nat.eqb_refl in Hneg. discriminate.
  - intros [Hin Hneq]. apply filter_In. split; [exact Hin|].
    destruct (Nat.eqb v v1) eqn:Heq; [|reflexivity].
    apply Nat.eqb_eq in Heq. contradiction.
Qed.

(** identify_vertices preserves wf when v2 ≠ v1 and v2 ∈ verts. *)
Lemma identify_vertices_preserves_wf {r : nat} :
  forall (v1 v2 : Vertex) (G : LGraph r),
    wf_graph G ->
    v1 <> v2 ->
    In v2 G.(lg_verts) ->
    wf_graph (identify_vertices v1 v2 G).
Proof.
  intros v1 v2 G Hwf Hneq Hin2 e He.
  unfold identify_vertices in He. simpl in He.
  apply nodup_In in He.
  apply in_map_iff in He. destruct He as [e' [Hee Hin']].
  pose proof (Hwf e' Hin') as [Hsrc' Htgt'].
  unfold replace_in_edge in Hee. subst e. simpl.
  unfold replace_vertex.
  unfold identify_vertices, lg_verts. simpl.
  split.
  - destruct (Nat.eqb (e_src e') v1) eqn:Hs.
    + (* src = v1, replaced with v2 *)
      apply in_filter_neqb. split; [exact Hin2| auto].
    + (* src ≠ v1, stays src *)
      apply Nat.eqb_neq in Hs.
      apply in_filter_neqb. split; [exact Hsrc'| exact Hs].
  - destruct (Nat.eqb (e_tgt e') v1) eqn:Ht.
    + apply in_filter_neqb. split; [exact Hin2| auto].
    + apply Nat.eqb_neq in Ht.
      apply in_filter_neqb. split; [exact Htgt'| exact Ht].
Qed.

(** fold_step preserves wf. *)
Lemma fold_step_preserves_wf {r : nat} :
  forall (G G' : LGraph r),
    wf_graph G ->
    fold_step G = Some G' ->
    wf_graph G'.
Proof.
  intros G G' Hwf Hfs.
  unfold fold_step in Hfs.
  case_eq (find_fold_pair G); [|intros Hnone; rewrite Hnone in Hfs; discriminate].
  intros [e1 e2] Hfp.
  rewrite Hfp in Hfs.
  injection Hfs as HG'. subst G'.
  pose proof (@find_fold_pair_correct r G e1 e2 Hfp) as Hpair.
  pose proof (@find_fold_pair_in_graph r G e1 e2 Hfp) as [Hin1 Hin2].
  pose proof (Hwf e2 Hin2) as [_ Htgt2].
  apply identify_vertices_preserves_wf; [exact Hwf | | exact Htgt2].
  apply (is_fold_pair_diff_targets _ _ Hpair).
Qed.

(** fold_iterate preserves wf. *)
Lemma fold_iterate_preserves_wf {r : nat} :
  forall (fuel : nat) (G : LGraph r),
    wf_graph G ->
    wf_graph (fold_iterate fuel G).
Proof.
  induction fuel as [|k IH]; intros G Hwf; [exact Hwf|].
  simpl. destruct (fold_step G) as [G'|] eqn:Hfs.
  - apply IH. apply (fold_step_preserves_wf G G' Hwf Hfs).
  - exact Hwf.
Qed.

(** petal_graph satisfies wf_graph. *)
Lemma petal_graph_wf_graph {r : nat} :
  forall (w : list (Letter r)),
    wf_graph (petal_graph w).
Proof.
  intros w e Hin. apply (petal_graph_wf w e Hin).
Qed.

(** stallings_core (= fold_iterate over petal_graph) is wf. *)
Lemma stallings_core_wf {r : nat} :
  forall (w : list (Letter r)),
    wf_graph (stallings_core w).
Proof.
  intros w. unfold stallings_core.
  apply fold_iterate_preserves_wf.
  apply petal_graph_wf_graph.
Qed.

(** ** Termination: fold_step returns None after enough iterations.

    Under wf_graph, fold_iterate exhausts: after num_vertices(G) steps,
    fold_step returns None. This is the operational form of the
    fold_iterate_folded axiom. The "is_folded" form requires an extra
    invariant (no duplicate edges) which we don't yet track. *)

Lemma fold_iterate_done_aux {r : nat} :
  forall (fuel : nat) (G : LGraph r),
    fuel >= num_vertices G ->
    wf_graph G ->
    fold_step (fold_iterate fuel G) = None.
Proof.
  induction fuel as [|k IH]; intros G Hf Hwf.
  - (* fuel = 0, so num_vertices G = 0 *)
    assert (Hnv : num_vertices G = 0) by lia.
    simpl. unfold num_vertices in Hnv.
    apply length_zero_iff_nil in Hnv.
    assert (Hedges : G.(lg_edges) = []).
    { destruct (lg_edges G) as [|e es] eqn:He; [reflexivity|].
      exfalso. assert (Hin : In e (lg_edges G)) by (rewrite He; left; reflexivity).
      pose proof (Hwf e Hin) as [Hsrc _].
      rewrite Hnv in Hsrc. inversion Hsrc. }
    unfold fold_step, find_fold_pair. rewrite Hedges. reflexivity.
  - (* fuel = S k *)
    simpl. destruct (fold_step G) as [G'|] eqn:Hfs.
    + (* num_vertices G' < num_vertices G ≤ S k, so num_vertices G' ≤ k *)
      pose proof (fold_step_decreases_under_wf G G' Hwf Hfs) as Hdecr.
      pose proof (fold_step_preserves_wf G G' Hwf Hfs) as Hwf'.
      apply IH; [lia | exact Hwf'].
    + (* fold_step G = None, fold_iterate (S k) G = G *)
      exact Hfs.
Qed.

(** Specialization: with fuel = num_vertices G, fold_step on the result
    is None. This is the conditional form of fold_iterate_folded. *)
Theorem fold_iterate_done_wf {r : nat} :
  forall (G : LGraph r),
    wf_graph G ->
    fold_step (fold_iterate (num_vertices G) G) = None.
Proof.
  intros G Hwf. apply (fold_iterate_done_aux (num_vertices G) G); [lia | exact Hwf].
Qed.

(** stallings_core's fold_step is None: the algorithm terminates. *)
Theorem stallings_core_done {r : nat} :
  forall (w : list (Letter r)),
    fold_step (stallings_core w) = None.
Proof.
  intros w. unfold stallings_core.
  apply (fold_iterate_done_wf (petal_graph w)).
  apply petal_graph_wf_graph.
Qed.

(** ** Vertex count bounds: fold_iterate doesn't increase vertices. *)

Lemma fold_step_num_vertices_le {r : nat} :
  forall (G G' : LGraph r),
    wf_graph G ->
    fold_step G = Some G' ->
    num_vertices G' < num_vertices G.
Proof. intros. apply fold_step_decreases_under_wf; assumption. Qed.

Lemma fold_iterate_num_vertices_le {r : nat} :
  forall (fuel : nat) (G : LGraph r),
    wf_graph G ->
    num_vertices (fold_iterate fuel G) <= num_vertices G.
Proof.
  induction fuel as [|k IH]; intros G Hwf; [reflexivity|].
  simpl. destruct (fold_step G) as [G'|] eqn:Hfs.
  - pose proof (fold_step_num_vertices_le G G' Hwf Hfs) as Hdec.
    pose proof (fold_step_preserves_wf G G' Hwf Hfs) as Hwf'.
    pose proof (IH G' Hwf') as IHapp. lia.
  - reflexivity.
Qed.

(** Stallings core has at most max(1, |w|) vertices. *)
Theorem stallings_core_num_vertices_bound {r : nat} :
  forall (w : list (Letter r)),
    num_vertices (stallings_core w) <= Nat.max 1 (length w).
Proof.
  intros w. unfold stallings_core.
  pose proof (fold_iterate_num_vertices_le (num_vertices (petal_graph w))
                                            (petal_graph w)
                                            (petal_graph_wf_graph w)) as Hbnd.
  rewrite (petal_graph_num_vertices w) in Hbnd at 2.
  exact Hbnd.
Qed.

(** ** Edge count bounds: identify_vertices doesn't increase edge count. *)

Lemma identify_vertices_num_edges_le {r : nat} :
  forall (v1 v2 : Vertex) (G : LGraph r),
    num_edges (identify_vertices v1 v2 G) <= num_edges G.
Proof.
  intros v1 v2 G. unfold num_edges, identify_vertices, lg_edges. simpl.
  pose proof (NoDup_incl_length
                (l := nodup edge_eq_dec (map (replace_in_edge v1 v2) G.(lg_edges)))
                (l' := map (replace_in_edge v1 v2) G.(lg_edges))) as Hle.
  rewrite length_map in Hle.
  apply Hle.
  - apply NoDup_nodup.
  - intros x Hin. apply nodup_In in Hin. exact Hin.
Qed.

Lemma fold_step_num_edges_le {r : nat} :
  forall (G G' : LGraph r),
    fold_step G = Some G' ->
    num_edges G' <= num_edges G.
Proof.
  intros G G' Hfs. unfold fold_step in Hfs.
  destruct (find_fold_pair G) as [[e1 e2]|]; [|discriminate].
  injection Hfs as HG'. subst G'.
  apply identify_vertices_num_edges_le.
Qed.

Lemma fold_iterate_num_edges_le {r : nat} :
  forall (fuel : nat) (G : LGraph r),
    num_edges (fold_iterate fuel G) <= num_edges G.
Proof.
  induction fuel as [|k IH]; intros G; [reflexivity|].
  simpl. destruct (fold_step G) as [G'|] eqn:Hfs.
  - pose proof (fold_step_num_edges_le G G' Hfs) as Hle.
    pose proof (IH G') as IHapp. lia.
  - reflexivity.
Qed.

(** Stallings core has at most 2|w| edges. *)
Theorem stallings_core_num_edges_bound {r : nat} :
  forall (w : list (Letter r)),
    num_edges (stallings_core w) <= 2 * length w.
Proof.
  intros w. unfold stallings_core.
  pose proof (fold_iterate_num_edges_le (num_vertices (petal_graph w))
                                         (petal_graph w)) as Hbnd.
  unfold num_edges in Hbnd.
  rewrite (petal_graph_num_edges w) in Hbnd. exact Hbnd.
Qed.

(** ** identify_vertices preserves involutive property. *)

Lemma identify_vertices_preserves_involutive {r : nat} :
  forall (v1 v2 : Vertex) (G : LGraph r),
    is_involutive G ->
    is_involutive (identify_vertices v1 v2 G).
Proof.
  intros v1 v2 G Hinv u v l Hin.
  unfold identify_vertices, lg_edges in Hin. simpl in Hin.
  apply nodup_In in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [e' [Hee Hin']].
  unfold replace_in_edge in Hee.
  destruct e' as [s' lb' t']. simpl in Hee.
  injection Hee as Hu Hl Hv. subst u l v.
  pose proof (Hinv s' t' lb' Hin') as Hinv'.
  unfold identify_vertices, lg_edges. simpl.
  apply nodup_In.
  apply in_map_iff.
  exists (mkEdge t' (letter_inv lb') s'). split.
  - unfold replace_in_edge. simpl. reflexivity.
  - exact Hinv'.
Qed.

Lemma fold_step_preserves_involutive {r : nat} :
  forall (G G' : LGraph r),
    is_involutive G ->
    fold_step G = Some G' ->
    is_involutive G'.
Proof.
  intros G G' Hinv Hfs.
  unfold fold_step in Hfs.
  destruct (find_fold_pair G) as [[e1 e2]|]; [|discriminate].
  injection Hfs as HG'. subst G'.
  apply identify_vertices_preserves_involutive. exact Hinv.
Qed.

Lemma fold_iterate_preserves_involutive {r : nat} :
  forall (fuel : nat) (G : LGraph r),
    is_involutive G ->
    is_involutive (fold_iterate fuel G).
Proof.
  induction fuel as [|k IH]; intros G Hinv; [exact Hinv|].
  simpl. destruct (fold_step G) as [G'|] eqn:Hfs.
  - apply IH. apply (fold_step_preserves_involutive G G' Hinv Hfs).
  - exact Hinv.
Qed.

(** stallings_core w is involutive. *)
Theorem stallings_core_involutive {r : nat} :
  forall (w : list (Letter r)),
    is_involutive (stallings_core w).
Proof.
  intros w. unfold stallings_core.
  apply fold_iterate_preserves_involutive.
  apply petal_graph_involutive.
Qed.

(** Path reversal in stallings_core: any path can be reversed. *)
Theorem stallings_core_path_reverse {r : nat} :
  forall (w : list (Letter r)) (u v : Vertex) (path_w : list (Letter r)),
    path_in (stallings_core w) u path_w v ->
    path_in (stallings_core w) v
            (List.rev (List.map letter_inv path_w)) u.
Proof.
  intros w u v path_w Hp.
  apply path_in_reverse_involutive.
  - apply stallings_core_involutive.
  - apply stallings_core_wf.
  - exact Hp.
Qed.


(** Note: full backward path lifting is genuinely hard.

    Given a path in [identify_vertices v1 v2 G] reading w, lifting to a
    path in G reading w fails by simple existential induction:
    - Empty word: easy (v0' lifts to v0', or to v1 if v0' = v2).
    - Non-empty: each edge in G' lifts to G, but the lifted edge's
      target might not match the source of the lifted continuation
      from IH (which was an arbitrary lift, not a specific one).

    The standard argument requires either:
    (a) constructing a specific TARGETED lift where endpoints are tracked
        via replace_vertex (which is what fold_preserves_subgroup_backward
        actually states), or
    (b) using induction on path length with an explicit
        "lift starting at v" formulation.

    Both approaches require non-trivial choice of v1-vs-v2 at each step.
    Left as future work. *)

(** Every edge in identify_vertices v1 v2 G is the image of some edge in G. *)
Lemma identify_vertices_edge_lift {r : nat} :
  forall (v1 v2 : Vertex) (G : LGraph r) (e : Edge r),
    In e (identify_vertices v1 v2 G).(lg_edges) ->
    exists e', In e' G.(lg_edges) /\ e = replace_in_edge v1 v2 e'.
Proof.
  intros v1 v2 G e Hin.
  unfold identify_vertices, lg_edges in Hin. simpl in Hin.
  apply nodup_In in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [e' [Heq Hin']].
  exists e'. split; [exact Hin' | symmetry; exact Heq].
Qed.

(** Vertex lift: a vertex in identify_vertices(G).lg_verts came from G.lg_verts. *)
Lemma identify_vertices_vertex_lift {r : nat} :
  forall (v1 v2 : Vertex) (G : LGraph r) (v : Vertex),
    In v (identify_vertices v1 v2 G).(lg_verts) ->
    In v G.(lg_verts) /\ v <> v1.
Proof.
  intros v1 v2 G v Hin.
  unfold identify_vertices, lg_verts in Hin. simpl in Hin.
  apply in_filter_neqb in Hin. exact Hin.
Qed.

(** Specialized form: edge with given (u, l, v) in G' has a preimage edge
    with explicit (u', l, v') in G. *)
Lemma identify_vertices_edge_lift_with_src {r : nat} :
  forall (v1 v2 : Vertex) (G : LGraph r) (u v : Vertex) (l : Letter r),
    In (mkEdge u l v) (identify_vertices v1 v2 G).(lg_edges) ->
    exists u' v',
      In (mkEdge u' l v') G.(lg_edges) /\
      replace_vertex v1 v2 u' = u /\
      replace_vertex v1 v2 v' = v.
Proof.
  intros v1 v2 G u v l Hin.
  apply identify_vertices_edge_lift in Hin.
  destruct Hin as [e' [Hin' Heq]].
  destruct e' as [s' lb' t']. simpl in Heq.
  unfold replace_in_edge in Heq. simpl in Heq.
  injection Heq as Hu Hl Hv. subst u l v.
  exists s', t'. split; [exact Hin'|]. split; reflexivity.
Qed.

(** ** identify_vertices always produces NoDup edges. *)

Lemma identify_vertices_no_dup_edges {r : nat} :
  forall (v1 v2 : Vertex) (G : LGraph r),
    no_dup_edges (identify_vertices v1 v2 G).
Proof.
  intros v1 v2 G. unfold no_dup_edges, identify_vertices, lg_edges. simpl.
  apply NoDup_nodup.
Qed.

Lemma fold_step_no_dup_edges {r : nat} :
  forall (G G' : LGraph r),
    fold_step G = Some G' ->
    no_dup_edges G'.
Proof.
  intros G G' Hfs.
  unfold fold_step in Hfs.
  destruct (find_fold_pair G) as [[e1 e2]|]; [|discriminate].
  injection Hfs as HG'. subst G'.
  apply identify_vertices_no_dup_edges.
Qed.

(** Preservation of NoDup under fold_iterate. *)
Lemma fold_iterate_no_dup_edges {r : nat} :
  forall (fuel : nat) (G : LGraph r),
    no_dup_edges G ->
    no_dup_edges (fold_iterate fuel G).
Proof.
  induction fuel as [|k IH]; intros G Hnd; [exact Hnd|].
  simpl. destruct (fold_step G) as [G'|] eqn:Hfs.
  - apply IH. apply (fold_step_no_dup_edges G G' Hfs).
  - exact Hnd.
Qed.

(** ** Search completeness for find_fold_pair_aux.

    Under NoDup invariants and the subset condition, if a fold pair
    exists (e1 ∈ edges, e2 ∈ other, is_fold_pair e1 e2 = true), then
    find_fold_pair_aux returns Some. *)

Lemma find_fold_pair_aux_complete {r : nat} :
  forall (edges other : list (Edge r)),
    NoDup edges -> NoDup other ->
    (forall e, In e edges -> In e other) ->
    forall e1 e2, In e1 edges -> In e2 other ->
    is_fold_pair e1 e2 = true ->
    find_fold_pair_aux edges other <> None.
Proof.
  induction edges as [|e rest IH]; intros other Hnd_e Hnd_o Hsub e1 e2 Hin1 Hin2 Hpair.
  - inversion Hin1.
  - simpl.
    destruct (filter (fun e' : Edge r => is_fold_pair e e') other) as [|c cs] eqn:Hf.
    + (* filter empty: no fold partner for e in other.
         But we have e1 ∈ e :: rest, e2 ∈ other, is_fold_pair e1 e2 = true. *)
      destruct Hin1 as [Heq | Hin1'].
      * (* e1 = e: then e2 should be in filter, but filter is empty *)
        exfalso. subst e1.
        assert (Hf_in : In e2 (filter (fun e' : Edge r => is_fold_pair e e') other)).
        { apply filter_In. split; assumption. }
        rewrite Hf in Hf_in. inversion Hf_in.
      * (* e1 ∈ rest: recurse *)
        inversion Hnd_e as [|x ys Hx_notin Hys]. subst x ys.
        apply (IH _ Hys (NoDup_filter _ Hnd_o)) with (e1 := e1) (e2 := e2);
          try assumption.
        -- intros e' Hin'. apply filter_In. split.
           ++ apply Hsub. right. exact Hin'.
           ++ destruct (Nat.eqb (e_src e') (e_src e) &&
                        (if letter_eq_dec (e_lbl e') (e_lbl e) then true else false) &&
                        Nat.eqb (e_tgt e') (e_tgt e)) eqn:Heq; [|reflexivity].
              exfalso.
              apply Bool.andb_true_iff in Heq. destruct Heq as [Heq Ht].
              apply Bool.andb_true_iff in Heq. destruct Heq as [Hs Hl].
              apply Nat.eqb_eq in Hs.
              apply Nat.eqb_eq in Ht.
              destruct (letter_eq_dec (e_lbl e') (e_lbl e)) as [Hleq|]; [|discriminate].
              assert (Hee : e' = e).
              { destruct e' as [s' lb' t'], e as [s lb t]. simpl in *. subst. reflexivity. }
              subst e'. apply Hx_notin. exact Hin'.
        -- apply filter_In. split; [exact Hin2|].
           destruct (Nat.eqb (e_src e2) (e_src e) &&
                     (if letter_eq_dec (e_lbl e2) (e_lbl e) then true else false) &&
                     Nat.eqb (e_tgt e2) (e_tgt e)) eqn:Heq; [|reflexivity].
           exfalso.
           apply Bool.andb_true_iff in Heq. destruct Heq as [Heq Ht].
           apply Bool.andb_true_iff in Heq. destruct Heq as [Hs Hl].
           apply Nat.eqb_eq in Hs.
           apply Nat.eqb_eq in Ht.
           destruct (letter_eq_dec (e_lbl e2) (e_lbl e)) as [Hleq|]; [|discriminate].
           assert (Hee : e2 = e).
           { destruct e2 as [s' lb' t'], e as [s lb t]. simpl in *. subst. reflexivity. }
           subst e2.
           (* Now e1 ∈ rest with is_fold_pair e1 e = true, but filter (is_fold_pair e) other
              is empty, so no e' has is_fold_pair e e' = true. By symmetry,
              is_fold_pair e e1 = true would put e1 in filter — but only if e1 ∈ other. *)
           rewrite is_fold_pair_sym in Hpair.
           assert (Hin1_other : In e1 other).
           { apply Hsub. right. exact Hin1'. }
           assert (Hf_in : In e1 (filter (fun e' : Edge r => is_fold_pair e e') other)).
           { apply filter_In. split; assumption. }
           rewrite Hf in Hf_in. inversion Hf_in.
    + (* filter non-empty: returns Some, never None *)
      intro Hcontra. discriminate.
Qed.

(** Corollary: under NoDup G.lg_edges, find_fold_pair G returns Some
    iff a fold pair exists. *)
Lemma find_fold_pair_complete {r : nat} :
  forall (G : LGraph r),
    no_dup_edges G ->
    forall e1 e2, In e1 G.(lg_edges) -> In e2 G.(lg_edges) ->
    is_fold_pair e1 e2 = true ->
    find_fold_pair G <> None.
Proof.
  intros G Hnd e1 e2 Hin1 Hin2 Hpair.
  unfold find_fold_pair.
  apply (find_fold_pair_aux_complete _ _ Hnd Hnd) with (e1 := e1) (e2 := e2);
    try assumption.
  intros e Hin. exact Hin.
Qed.

(** ** Bridge lemma: NoDup + ∃ v l with out_count > 1 ⟹ fold pair. *)

(** A NoDup graph with out_count > 1 at some (v, l) admits a fold pair. *)
Lemma out_count_gt_1_has_fold_pair {r : nat} :
  forall (G : LGraph r) (v : Vertex) (l : Letter r),
    no_dup_edges G ->
    out_count G v l > 1 ->
    exists e1 e2 : Edge r,
      In e1 G.(lg_edges) /\ In e2 G.(lg_edges) /\
      is_fold_pair e1 e2 = true.
Proof.
  intros G v l Hnd Hcnt.
  unfold out_count, out_edges in Hcnt.
  set (filt := (fun e => if Nat.eqb (e_src e) v then
                           if letter_eq_dec (e_lbl e) l then true else false
                         else false)) in *.
  destruct (filter filt G.(lg_edges)) as [|e1 [|e2 rest']] eqn:Hf;
    [simpl in Hcnt; lia | simpl in Hcnt; lia |].
  assert (Hin1 : In e1 (filter filt G.(lg_edges))) by (rewrite Hf; left; reflexivity).
  assert (Hin2 : In e2 (filter filt G.(lg_edges))) by (rewrite Hf; right; left; reflexivity).
  apply filter_In in Hin1. destruct Hin1 as [Hin1g Hin1f].
  apply filter_In in Hin2. destruct Hin2 as [Hin2g Hin2f].
  unfold filt in Hin1f, Hin2f.
  destruct (Nat.eqb (e_src e1) v) eqn:Hs1; [|discriminate].
  destruct (letter_eq_dec (e_lbl e1) l) as [Hl1|]; [|discriminate].
  destruct (Nat.eqb (e_src e2) v) eqn:Hs2; [|discriminate].
  destruct (letter_eq_dec (e_lbl e2) l) as [Hl2|]; [|discriminate].
  apply Nat.eqb_eq in Hs1.
  apply Nat.eqb_eq in Hs2.
  assert (Hnd_filter : NoDup (filter filt G.(lg_edges))) by (apply NoDup_filter; exact Hnd).
  rewrite Hf in Hnd_filter.
  assert (Hneq : e1 <> e2).
  { intro Heq. inversion Hnd_filter as [|x ys Hxnotin Hys].
    apply Hxnotin. rewrite Heq. left. reflexivity. }
  assert (Hsrc_eq : e_src e1 = e_src e2) by (rewrite Hs1, Hs2; reflexivity).
  assert (Hlbl_eq : e_lbl e1 = e_lbl e2) by (rewrite Hl1, Hl2; reflexivity).
  assert (Htgt_neq : e_tgt e1 <> e_tgt e2).
  { intro Htgt. apply Hneq.
    destruct e1 as [s1 lb1 t1], e2 as [s2 lb2 t2].
    simpl in *. subst. reflexivity. }
  exists e1, e2. split; [exact Hin1g|]. split; [exact Hin2g|].
  unfold is_fold_pair.
  rewrite Hsrc_eq, Nat.eqb_refl.
  destruct (letter_eq_dec (e_lbl e1) (e_lbl e2)) as [_|Hcontra];
    [|exfalso; apply Hcontra; exact Hlbl_eq].
  destruct (Nat.eqb (e_tgt e1) (e_tgt e2)) eqn:Ht.
  - apply Nat.eqb_eq in Ht. contradiction.
  - reflexivity.
Qed.

(** ** Combined wf + no_dup invariant for graphs.
    A "clean" graph satisfies both well-formedness and no-duplicate edges
    — the input form needed for full fold_iterate correctness. *)

Definition clean_graph {r : nat} (G : LGraph r) : Prop :=
  wf_graph G /\ no_dup_edges G.

Lemma petal_graph_nil_clean {r : nat} :
  clean_graph (petal_graph (@nil (Letter r))).
Proof.
  split.
  - apply petal_graph_wf_graph.
  - apply petal_graph_nil_no_dup_edges.
Qed.

Lemma petal_graph_single_clean {r : nat} (l : Letter r) :
  clean_graph (petal_graph [l]).
Proof.
  split.
  - apply petal_graph_wf_graph.
  - apply petal_graph_single_no_dup_edges.
Qed.

Lemma identify_vertices_preserves_clean {r : nat} :
  forall (v1 v2 : Vertex) (G : LGraph r),
    v1 <> v2 ->
    In v2 G.(lg_verts) ->
    clean_graph G ->
    clean_graph (identify_vertices v1 v2 G).
Proof.
  intros v1 v2 G Hneq Hin [Hwf Hnd].
  split.
  - apply identify_vertices_preserves_wf; assumption.
  - apply identify_vertices_no_dup_edges.
Qed.

Lemma fold_step_preserves_clean {r : nat} :
  forall (G G' : LGraph r),
    clean_graph G ->
    fold_step G = Some G' ->
    clean_graph G'.
Proof.
  intros G G' [Hwf Hnd] Hfs.
  split.
  - apply (fold_step_preserves_wf G G' Hwf Hfs).
  - apply (fold_step_no_dup_edges G G' Hfs).
Qed.

Lemma fold_iterate_preserves_clean {r : nat} :
  forall (fuel : nat) (G : LGraph r),
    clean_graph G ->
    clean_graph (fold_iterate fuel G).
Proof.
  intros fuel G [Hwf Hnd]. split.
  - apply fold_iterate_preserves_wf. exact Hwf.
  - apply fold_iterate_no_dup_edges. exact Hnd.
Qed.

(** ** **MAJOR**: Under NoDup, fold_step = None implies is_folded. *)

Theorem fold_step_none_implies_folded {r : nat} :
  forall (G : LGraph r),
    no_dup_edges G ->
    fold_step G = None ->
    is_folded G.
Proof.
  intros G Hnd Hfs.
  intros v l. unfold out_count.
  assert (Hle_or_gt : length (out_edges G v l) <= 1 \/
                      length (out_edges G v l) > 1) by lia.
  destruct Hle_or_gt as [Hle|Hgt]; [exact Hle|].
  exfalso.
  pose proof (out_count_gt_1_has_fold_pair G v l Hnd Hgt)
    as [e1 [e2 [Hin1 [Hin2 Hpair]]]].
  pose proof (find_fold_pair_complete G Hnd e1 e2 Hin1 Hin2 Hpair) as Hsome.
  apply Hsome.
  unfold fold_step in Hfs.
  case_eq (find_fold_pair G);
    [intros [e_a e_b] Heq; rewrite Heq in Hfs; inversion Hfs
    |intros Heq; reflexivity].
Qed.

(** Combined: under NoDup G, fold_iterate (num_vertices G) G is folded. *)
Theorem fold_iterate_folded_wf_nodup {r : nat} :
  forall (G : LGraph r),
    wf_graph G ->
    no_dup_edges G ->
    is_folded (fold_iterate (num_vertices G) G).
Proof.
  intros G Hwf Hnd.
  apply fold_step_none_implies_folded.
  - apply fold_iterate_no_dup_edges. exact Hnd.
  - apply fold_iterate_done_wf. exact Hwf.
Qed.

(** Clean version: clean_graph G ⟹ fold_iterate (num_vertices G) G is folded. *)
Theorem fold_iterate_folded_clean {r : nat} :
  forall (G : LGraph r),
    clean_graph G ->
    is_folded (fold_iterate (num_vertices G) G).
Proof.
  intros G [Hwf Hnd]. apply fold_iterate_folded_wf_nodup; assumption.
Qed.

(** stallings_core w is folded when petal_graph w is clean. *)
Theorem stallings_core_folded_when_clean {r : nat} :
  forall (w : list (Letter r)),
    clean_graph (petal_graph w) ->
    is_folded (stallings_core w).
Proof.
  intros w Hclean. unfold stallings_core.
  apply fold_iterate_folded_clean. exact Hclean.
Qed.

(** Specialized: stallings_core w is folded for empty word. *)
Corollary stallings_core_nil_folded {r : nat} :
  is_folded (stallings_core (@nil (Letter r))).
Proof.
  apply stallings_core_folded_when_clean. apply petal_graph_nil_clean.
Qed.

(** Specialized: stallings_core w is folded for single-letter words. *)
Corollary stallings_core_single_folded {r : nat} (l : Letter r) :
  is_folded (stallings_core [l]).
Proof.
  apply stallings_core_folded_when_clean. apply petal_graph_single_clean.
Qed.

(** ** Special case: backward direction of fold_preserves_subgroup
    when G is already folded — fold_iterate is identity, so the lift
    is trivial. *)

Lemma fold_iterate_folded_identity_path {r : nat} :
  forall (fuel : nat) (G : LGraph r) (u v : Vertex) (w : list (Letter r)),
    is_folded G ->
    path_in (fold_iterate fuel G) u w v ->
    path_in G u w v.
Proof.
  intros fuel G u v w Hfolded Hpath.
  rewrite (fold_iterate_folded_is_id fuel G Hfolded) in Hpath.
  exact Hpath.
Qed.

(** When G is already folded, the backward direction holds trivially. *)
Lemma fold_preserves_subgroup_backward_folded {r : nat} :
  forall (G : LGraph r) (w : list (Letter r)),
    is_folded G ->
    path_in (fold_iterate (num_vertices G) G)
            (fold_iterate (num_vertices G) G).(lg_base)
            w
            (fold_iterate (num_vertices G) G).(lg_base) ->
    path_in G G.(lg_base) w G.(lg_base).
Proof.
  intros G w Hfolded Hpath.
  apply (fold_iterate_folded_identity_path (num_vertices G) G _ _ _ Hfolded).
  rewrite (fold_iterate_folded_is_id _ G Hfolded) in Hpath.
  rewrite (fold_iterate_folded_is_id _ G Hfolded). exact Hpath.
Qed.

(** petal_graph nil and single-letter cases are already folded. *)
Lemma petal_graph_nil_is_folded {r : nat} :
  is_folded (petal_graph (@nil (Letter r))).
Proof.
  intros v lt. unfold out_count, out_edges. simpl. lia.
Qed.

(** petal_graph [l] is folded: each (v, lt) has at most one out-edge.
    Proven by showing find_fold_pair returns None and chaining via
    NoDup-based fold_step_none_implies_folded. *)
Lemma petal_graph_single_is_folded {r : nat} (l : Letter r) :
  is_folded (petal_graph [l]).
Proof.
  apply fold_step_none_implies_folded.
  - apply petal_graph_single_no_dup_edges.
  - unfold fold_step.
    destruct (find_fold_pair (petal_graph [l])) as [[e1 e2]|] eqn:Hfp;
      [|reflexivity].
    exfalso.
    pose proof (find_fold_pair_correct _ _ _ Hfp) as Hpair.
    pose proof (find_fold_pair_in_graph _ _ _ Hfp) as [Hin1 Hin2].
    simpl in Hin1, Hin2.
    (* edges are [(0, l, 0); (0, letter_inv l, 0)] — all have tgt = 0 *)
    assert (Htgt1 : e1.(e_tgt) = 0).
    { destruct Hin1 as [He | [He | F]]; [..|inversion F];
        rewrite <- He; reflexivity. }
    assert (Htgt2 : e2.(e_tgt) = 0).
    { destruct Hin2 as [He | [He | F]]; [..|inversion F];
        rewrite <- He; reflexivity. }
    apply (is_fold_pair_diff_targets _ _ Hpair).
    rewrite Htgt1, Htgt2. reflexivity.
Qed.

(** Two-letter petal_graph with freely-reduced word is folded.

    Edges: [(1, b, 0); (0, letter_inv b, 1); (0, a, 1); (1, letter_inv a, 0)].
    For a fold pair we'd need two distinct edges sharing src + lbl with
    different tgts. But in this 4-edge graph:
    - (0, ·): two edges with lbls letter_inv b and a. For these to share
      lbl, need letter_inv b = a, i.e., a = letter_inv b (non-reduced).
    - (1, ·): two edges with lbls b and letter_inv a. For these to share
      lbl, need b = letter_inv a, i.e., a = letter_inv b again. *)

(** Two-letter petal_graph with freely-reduced word is folded.
    NOTE: skipping NoDup proof because records have non-trivial injection;
    instead we directly verify the no-fold-pair condition via case analysis
    on the 4 edges. *)

(** stallings_core for a single-letter word equals the petal_graph itself. *)
Lemma stallings_core_single_eq_petal {r : nat} (l : Letter r) :
  stallings_core [l] = petal_graph [l].
Proof.
  unfold stallings_core. simpl num_vertices.
  unfold petal_graph at 1.
  unfold num_vertices. simpl lg_verts. simpl length.
  apply fold_iterate_folded_is_id.
  apply petal_graph_single_is_folded.
Qed.

(** Likewise for the empty word. *)
Lemma stallings_core_nil_eq_petal {r : nat} :
  stallings_core (@nil (Letter r)) = petal_graph (@nil (Letter r)).
Proof.
  unfold stallings_core. simpl. reflexivity.
Qed.




(** Concrete: backward direction holds for empty word's petal graph. *)
Theorem stallings_core_nil_subgroup_backward {r : nat} :
  forall (w : list (Letter r)),
    path_in (stallings_core (@nil (Letter r)))
            (stallings_core (@nil (Letter r))).(lg_base)
            w
            (stallings_core (@nil (Letter r))).(lg_base) ->
    path_in (petal_graph (@nil (Letter r)))
            (petal_graph (@nil (Letter r))).(lg_base)
            w
            (petal_graph (@nil (Letter r))).(lg_base).
Proof.
  intros w. unfold stallings_core.
  apply fold_preserves_subgroup_backward_folded.
  apply petal_graph_nil_is_folded.
Qed.

(** Concrete: backward direction for single-letter word's petal graph. *)
Theorem stallings_core_single_subgroup_backward {r : nat} (l : Letter r) :
  forall (w : list (Letter r)),
    path_in (stallings_core [l])
            (stallings_core [l]).(lg_base)
            w
            (stallings_core [l]).(lg_base) ->
    path_in (petal_graph [l])
            (petal_graph [l]).(lg_base)
            w
            (petal_graph [l]).(lg_base).
Proof.
  intros w. unfold stallings_core.
  apply fold_preserves_subgroup_backward_folded.
  apply petal_graph_single_is_folded.
Qed.


(** ** Algebraic lemmas about replace_vertex. *)

Lemma replace_vertex_eq (v1 v2 : Vertex) :
  replace_vertex v1 v2 v1 = v2.
Proof.
  unfold replace_vertex. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma replace_vertex_neq (v1 v2 v : Vertex) :
  v <> v1 -> replace_vertex v1 v2 v = v.
Proof.
  intros Hneq. unfold replace_vertex.
  destruct (Nat.eqb v v1) eqn:Heq.
  - apply Nat.eqb_eq in Heq. contradiction.
  - reflexivity.
Qed.

Lemma replace_vertex_id (v1 v : Vertex) :
  replace_vertex v1 v1 v = v.
Proof.
  unfold replace_vertex. destruct (Nat.eqb v v1) eqn:Heq.
  - apply Nat.eqb_eq in Heq. exact (eq_sym Heq).
  - reflexivity.
Qed.

(** When the new value v2 differs from v1, replacing twice equals once. *)
Lemma replace_vertex_idem (v1 v2 v : Vertex) :
  v2 <> v1 ->
  replace_vertex v1 v2 (replace_vertex v1 v2 v) =
  replace_vertex v1 v2 v.
Proof.
  intros Hneq. unfold replace_vertex.
  destruct (Nat.eqb v v1) eqn:Heq.
  - destruct (Nat.eqb v2 v1) eqn:Heq2; [|reflexivity].
    apply Nat.eqb_eq in Heq2. contradiction.
  - rewrite Heq. reflexivity.
Qed.

(** ** Path preservation under identify_vertices.

    When we identify v1 with v2, paths in the original graph map to
    paths in the result, with vertices substituted via replace_vertex. *)

Lemma identify_vertices_path {r : nat} :
  forall (v1 v2 : Vertex) (G : LGraph r) (u v : Vertex) (w : list (Letter r)),
    v1 <> v2 ->
    In v2 G.(lg_verts) ->
    path_in G u w v ->
    path_in (identify_vertices v1 v2 G)
            (replace_vertex v1 v2 u) w (replace_vertex v1 v2 v).
Proof.
  intros v1 v2 G u v w Hneq Hv2_in Hpath.
  induction Hpath as [v0 Hv0 | u0 v0 x0 l0 rest0 Hedge Hrest IH].
  - apply path_nil.
    unfold identify_vertices, lg_verts. simpl.
    unfold replace_vertex. destruct (Nat.eqb v0 v1) eqn:Heq.
    { apply Nat.eqb_eq in Heq. subst v0.
      apply in_filter_neqb. split; [exact Hv2_in | auto]. }
    { apply Nat.eqb_neq in Heq.
      apply in_filter_neqb. split; [exact Hv0 | exact Heq]. }
  - apply path_cons with (v := replace_vertex v1 v2 v0).
    { unfold identify_vertices, lg_edges. simpl.
      apply nodup_In.
      apply in_map_iff.
      exists (mkEdge u0 l0 v0). split.
      - unfold replace_in_edge. simpl. reflexivity.
      - exact Hedge. }
    { exact IH. }
Qed.

(** ** Corollary: fold_step preserves paths.

    If fold_step G = Some G' (i.e., a fold pair was found and identified),
    then any path u →[w]→ v in G maps to a path in G' via the appropriate
    vertex substitution. *)

Lemma fold_step_path {r : nat} :
  forall (G G' : LGraph r) (u v : Vertex) (w : list (Letter r)),
    wf_graph G ->
    fold_step G = Some G' ->
    path_in G u w v ->
    exists v1 v2,
      G' = identify_vertices v1 v2 G /\
      v1 <> v2 /\
      path_in G' (replace_vertex v1 v2 u) w (replace_vertex v1 v2 v).
Proof.
  intros G G' u v w Hwf Hfs Hpath.
  unfold fold_step in Hfs.
  case_eq (find_fold_pair G); [|intros Hnone; rewrite Hnone in Hfs; discriminate].
  intros [e1 e2] Hfp. rewrite Hfp in Hfs.
  injection Hfs as HG'. subst G'.
  pose proof (@find_fold_pair_correct r G e1 e2 Hfp) as Hpair.
  pose proof (@find_fold_pair_in_graph r G e1 e2 Hfp) as [_ Hin2].
  pose proof (Hwf e2 Hin2) as [_ Htgt2].
  exists e1.(e_tgt), e2.(e_tgt).
  split; [reflexivity|]. split.
  - apply (is_fold_pair_diff_targets _ _ Hpair).
  - apply identify_vertices_path; try assumption.
    apply (is_fold_pair_diff_targets _ _ Hpair).
Qed.

(** Existence-form: a path in G induces SOME path in G' with the same word. *)
Lemma fold_step_path_exists {r : nat} :
  forall (G G' : LGraph r) (u v : Vertex) (w : list (Letter r)),
    wf_graph G ->
    fold_step G = Some G' ->
    path_in G u w v ->
    exists u' v', path_in G' u' w v'.
Proof.
  intros G G' u v w Hwf Hfs Hpath.
  destruct (fold_step_path G G' u v w Hwf Hfs Hpath) as [v1 [v2 [_ [_ Hpath']]]].
  exists (replace_vertex v1 v2 u), (replace_vertex v1 v2 v). exact Hpath'.
Qed.

(** Iterated path-existence under fold_iterate: any path in the start
    graph induces some path in the iterated result, reading the same word. *)
Lemma fold_iterate_path_exists {r : nat} :
  forall (fuel : nat) (G : LGraph r) (u v : Vertex) (w : list (Letter r)),
    wf_graph G ->
    path_in G u w v ->
    exists u' v', path_in (fold_iterate fuel G) u' w v'.
Proof.
  induction fuel as [|k IH]; intros G u v w Hwf Hpath.
  - exists u, v. exact Hpath.
  - simpl. destruct (fold_step G) as [G'|] eqn:Hfs.
    + pose proof (fold_step_path_exists G G' u v w Hwf Hfs Hpath)
        as [u' [v' Hpath']].
      pose proof (fold_step_preserves_wf G G' Hwf Hfs) as Hwf'.
      apply (IH G' u' v' w Hwf' Hpath').
    + exists u, v. exact Hpath.
Qed.

(** Stronger: closed-loop preservation — if u = v in original path,
    the lifted path also has u' = v'. *)
Lemma fold_step_loop_path {r : nat} :
  forall (G G' : LGraph r) (u : Vertex) (w : list (Letter r)),
    wf_graph G ->
    fold_step G = Some G' ->
    path_in G u w u ->
    exists u', path_in G' u' w u'.
Proof.
  intros G G' u w Hwf Hfs Hpath.
  destruct (fold_step_path G G' u u w Hwf Hfs Hpath) as [v1 [v2 [_ [_ Hpath']]]].
  exists (replace_vertex v1 v2 u). exact Hpath'.
Qed.

(** ** Basepoint tracking under fold operations.

    When we do fold_step G = identify_vertices v1 v2 G, the new
    basepoint is replace_vertex v1 v2 G.base. So a path G.base → G.base
    in G lifts to a path G'.base → G'.base in G'. *)

Lemma identify_vertices_base_path {r : nat} :
  forall (v1 v2 : Vertex) (G : LGraph r) (w : list (Letter r)),
    v1 <> v2 ->
    In v2 G.(lg_verts) ->
    path_in G G.(lg_base) w G.(lg_base) ->
    path_in (identify_vertices v1 v2 G)
            (identify_vertices v1 v2 G).(lg_base)
            w
            (identify_vertices v1 v2 G).(lg_base).
Proof.
  intros v1 v2 G w Hneq Hin Hpath.
  unfold identify_vertices, lg_base. simpl.
  apply identify_vertices_path; assumption.
Qed.

Lemma fold_step_base_path {r : nat} :
  forall (G G' : LGraph r) (w : list (Letter r)),
    wf_graph G ->
    fold_step G = Some G' ->
    path_in G G.(lg_base) w G.(lg_base) ->
    path_in G' G'.(lg_base) w G'.(lg_base).
Proof.
  intros G G' w Hwf Hfs Hpath.
  unfold fold_step in Hfs.
  case_eq (find_fold_pair G); [|intros Hnone; rewrite Hnone in Hfs; discriminate].
  intros [e1 e2] Hfp. rewrite Hfp in Hfs.
  injection Hfs as HG'. subst G'.
  pose proof (@find_fold_pair_correct r G e1 e2 Hfp) as Hpair.
  pose proof (@find_fold_pair_in_graph r G e1 e2 Hfp) as [_ Hin2].
  pose proof (Hwf e2 Hin2) as [_ Htgt2].
  apply identify_vertices_base_path; try assumption.
  apply (is_fold_pair_diff_targets _ _ Hpair).
Qed.

Lemma fold_iterate_base_path {r : nat} :
  forall (fuel : nat) (G : LGraph r) (w : list (Letter r)),
    wf_graph G ->
    path_in G G.(lg_base) w G.(lg_base) ->
    path_in (fold_iterate fuel G)
            (fold_iterate fuel G).(lg_base)
            w
            (fold_iterate fuel G).(lg_base).
Proof.
  induction fuel as [|k IH]; intros G w Hwf Hpath.
  - simpl. exact Hpath.
  - simpl. destruct (fold_step G) as [G'|] eqn:Hfs.
    + pose proof (fold_step_base_path G G' w Hwf Hfs Hpath) as Hpath'.
      pose proof (fold_step_preserves_wf G G' Hwf Hfs) as Hwf'.
      apply (IH G' w Hwf' Hpath').
    + exact Hpath.
Qed.

(** **MAJOR**: forward direction of fold_preserves_subgroup.
    A path basepoint → basepoint in G induces a path basepoint → basepoint
    in fold_iterate _ G (with the basepoint tracked through replace_vertex). *)
Theorem fold_preserves_subgroup_forward {r : nat} :
  forall (G : LGraph r) (w : list (Letter r)),
    wf_graph G ->
    path_in G G.(lg_base) w G.(lg_base) ->
    path_in (fold_iterate (num_vertices G) G)
            (fold_iterate (num_vertices G) G).(lg_base)
            w
            (fold_iterate (num_vertices G) G).(lg_base).
Proof.
  intros G w Hwf Hpath.
  apply fold_iterate_base_path; assumption.
Qed.

Lemma fold_iterate_loop_path {r : nat} :
  forall (fuel : nat) (G : LGraph r) (u : Vertex) (w : list (Letter r)),
    wf_graph G ->
    path_in G u w u ->
    exists u', path_in (fold_iterate fuel G) u' w u'.
Proof.
  induction fuel as [|k IH]; intros G u w Hwf Hpath.
  - exists u. exact Hpath.
  - simpl. destruct (fold_step G) as [G'|] eqn:Hfs.
    + pose proof (fold_step_loop_path G G' u w Hwf Hfs Hpath)
        as [u' Hpath'].
      pose proof (fold_step_preserves_wf G G' Hwf Hfs) as Hwf'.
      apply (IH G' u' w Hwf' Hpath').
    + exists u. exact Hpath.
Qed.

(** Corollary: stallings_core w admits a path reading w (existence). *)
Theorem stallings_core_path_w {r : nat} :
  forall (w : list (Letter r)),
    exists u' v', path_in (stallings_core w) u' w v'.
Proof.
  intros w. unfold stallings_core.
  apply (fold_iterate_path_exists (num_vertices (petal_graph w))
                                   (petal_graph w) 0 0 w).
  - apply petal_graph_wf_graph.
  - apply petal_graph_path_w.
Qed.

(** Stronger: stallings_core w admits a CYCLE (loop path) reading w. *)
Theorem stallings_core_loop_w {r : nat} :
  forall (w : list (Letter r)),
    exists u', path_in (stallings_core w) u' w u'.
Proof.
  intros w. unfold stallings_core.
  apply (fold_iterate_loop_path (num_vertices (petal_graph w))
                                 (petal_graph w) 0 w).
  - apply petal_graph_wf_graph.
  - apply petal_graph_path_w.
Qed.

(** And a cycle reading w^k. *)
Theorem stallings_core_loop_w_pow {r : nat} :
  forall (w : list (Letter r)) (k : nat),
    exists u', path_in (stallings_core w) u' (word_power w k) u'.
Proof.
  intros w k. unfold stallings_core.
  apply (fold_iterate_loop_path (num_vertices (petal_graph w))
                                 (petal_graph w) 0 (word_power w k)).
  - apply petal_graph_wf_graph.
  - apply petal_graph_path_w_pow.
Qed.

(** Cycle reading the inverse of w. *)
Theorem stallings_core_loop_w_inv {r : nat} :
  forall (w : list (Letter r)),
    exists u', path_in (stallings_core w) u' (List.rev (List.map letter_inv w)) u'.
Proof.
  intros w. unfold stallings_core.
  apply (fold_iterate_loop_path (num_vertices (petal_graph w))
                                 (petal_graph w) 0).
  - apply petal_graph_wf_graph.
  - apply petal_graph_path_w_inv.
Qed.

(** Cycle reading the inverse of w iterated k times. *)
Theorem stallings_core_loop_w_inv_pow {r : nat} :
  forall (w : list (Letter r)) (k : nat),
    exists u', path_in (stallings_core w) u'
                       (word_power (List.rev (List.map letter_inv w)) k) u'.
Proof.
  intros w k. unfold stallings_core.
  apply (fold_iterate_loop_path (num_vertices (petal_graph w))
                                 (petal_graph w) 0).
  - apply petal_graph_wf_graph.
  - apply petal_graph_path_w_inv_pow.
Qed.

(** Cycle reading any cyclic-word concatenation. Captures ⟨w⟩ as a
    subset of the language of stallings_core w. *)
Theorem stallings_core_loop_cyclic_word {r : nat} :
  forall (w : list (Letter r)) (ls : list (cyclic_word_letter w)),
    exists u', path_in (stallings_core w) u' (expand_cwls w ls) u'.
Proof.
  intros w ls. unfold stallings_core.
  apply (fold_iterate_loop_path (num_vertices (petal_graph w))
                                 (petal_graph w) 0).
  - apply petal_graph_wf_graph.
  - apply petal_graph_path_cyclic_word.
Qed.

(** And combining with fold_preserves_subgroup_forward: the basepoint
    version of the loop result. The basepoint of stallings_core w is
    well-tracked from petal_graph w. *)
Theorem stallings_core_base_loop_w {r : nat} :
  forall (w : list (Letter r)),
    path_in (stallings_core w) (stallings_core w).(lg_base) w
            (stallings_core w).(lg_base).
Proof.
  intros w. unfold stallings_core.
  apply fold_preserves_subgroup_forward.
  - apply petal_graph_wf_graph.
  - rewrite petal_graph_basepoint. apply petal_graph_path_w.
Qed.

Theorem stallings_core_base_loop_cyclic_word {r : nat} :
  forall (w : list (Letter r)) (ls : list (cyclic_word_letter w)),
    path_in (stallings_core w) (stallings_core w).(lg_base) (expand_cwls w ls)
            (stallings_core w).(lg_base).
Proof.
  intros w ls. unfold stallings_core.
  apply fold_preserves_subgroup_forward.
  - apply petal_graph_wf_graph.
  - rewrite petal_graph_basepoint. apply petal_graph_path_cyclic_word.
Qed.

(** identify_vertices preserves edge labels (replace_in_edge keeps lbl). *)
Lemma identify_vertices_lbl_preserves {r : nat} :
  forall (v1 v2 : Vertex) (G : LGraph r) (e : Edge r),
    In e (identify_vertices v1 v2 G).(lg_edges) ->
    exists e', In e' G.(lg_edges) /\ e.(e_lbl) = e'.(e_lbl).
Proof.
  intros v1 v2 G e Hin.
  apply identify_vertices_edge_lift in Hin.
  destruct Hin as [e' [Hin' Heq]].
  exists e'. split; [exact Hin'|].
  rewrite Heq. unfold replace_in_edge. simpl. reflexivity.
Qed.

(** fold_step preserves edge labels. *)
Lemma fold_step_lbl_preserves {r : nat} :
  forall (G G' : LGraph r) (e : Edge r),
    fold_step G = Some G' ->
    In e G'.(lg_edges) ->
    exists e', In e' G.(lg_edges) /\ e.(e_lbl) = e'.(e_lbl).
Proof.
  intros G G' e Hfs Hin.
  unfold fold_step in Hfs.
  destruct (find_fold_pair G) as [[e1 e2]|]; [|discriminate].
  injection Hfs as HG'. subst G'.
  apply (identify_vertices_lbl_preserves e1.(e_tgt) e2.(e_tgt) G e Hin).
Qed.

(** fold_iterate preserves edge labels (every edge has a label
    matching some edge in the original). *)
Lemma fold_iterate_lbl_preserves {r : nat} :
  forall (fuel : nat) (G : LGraph r) (e : Edge r),
    In e (fold_iterate fuel G).(lg_edges) ->
    exists e', In e' G.(lg_edges) /\ e.(e_lbl) = e'.(e_lbl).
Proof.
  induction fuel as [|k IH]; intros G e Hin; [exists e; split; [exact Hin|reflexivity]|].
  simpl in Hin. destruct (fold_step G) as [G'|] eqn:Hfs.
  - apply IH in Hin.
    destruct Hin as [e' [Hin' Heq]].
    pose proof (fold_step_lbl_preserves G G' e' Hfs Hin') as [e'' [Hin'' Heq2]].
    exists e''. split; [exact Hin''|]. rewrite Heq, Heq2. reflexivity.
  - exists e. split; [exact Hin|reflexivity].
Qed.

(** stallings_core edge labels are in the petal alphabet of w. *)
Theorem stallings_core_lbl_in_alphabet {r : nat} :
  forall (w : list (Letter r)) (e : Edge r),
    In e (stallings_core w).(lg_edges) ->
    in_petal_alphabet w e.(e_lbl).
Proof.
  intros w e Hin. unfold stallings_core in Hin.
  apply fold_iterate_lbl_preserves in Hin.
  destruct Hin as [e' [Hin' Heq]].
  rewrite Heq. apply petal_graph_lbl_in_alphabet. exact Hin'.
Qed.

(** Every path in stallings_core w reads only letters from the petal alphabet. *)
Theorem stallings_core_path_alphabet {r : nat} :
  forall (w : list (Letter r)) (u v : Vertex) (w' : list (Letter r)),
    path_in (stallings_core w) u w' v ->
    forall l', In l' w' -> in_petal_alphabet w l'.
Proof.
  intros w u v w' Hp.
  induction Hp as [v0 _ | u0 v0 x0 l0 rest0 Hedge Hrest IH];
    intros l' Hin.
  - inversion Hin.
  - simpl in Hin. destruct Hin as [Heq | Hin''].
    + subst l'.
      pose proof (stallings_core_lbl_in_alphabet w (mkEdge u0 l0 v0) Hedge) as Hlbl.
      simpl in Hlbl. exact Hlbl.
    + apply IH. exact Hin''.
Qed.

(** stallings_core w basepoint is in its lg_verts. *)
Theorem stallings_core_base_in_verts {r : nat} :
  forall (w : list (Letter r)),
    In (stallings_core w).(lg_base) (stallings_core w).(lg_verts).
Proof.
  intros w.
  pose proof (stallings_core_base_loop_w w) as Hp.
  apply path_in_target_in_verts in Hp. exact Hp.
Qed.

(** Concatenation of two base loops: if w1 and w2 are loop-words at base,
    so is w1 ++ w2. Combining stallings_core_path_app_iff. *)
Theorem stallings_core_base_loop_concat {r : nat} :
  forall (w : list (Letter r)) (w1 w2 : list (Letter r)),
    path_in (stallings_core w) (stallings_core w).(lg_base) w1
            (stallings_core w).(lg_base) ->
    path_in (stallings_core w) (stallings_core w).(lg_base) w2
            (stallings_core w).(lg_base) ->
    path_in (stallings_core w) (stallings_core w).(lg_base) (w1 ++ w2)
            (stallings_core w).(lg_base).
Proof.
  intros w w1 w2 Hp1 Hp2.
  apply (path_in_app (stallings_core w) _ _ _ _ _ Hp1 Hp2).
Qed.

(** Identity (empty word) is in the base-loop language. *)
Theorem stallings_core_base_loop_empty {r : nat} :
  forall (w : list (Letter r)),
    path_in (stallings_core w) (stallings_core w).(lg_base) []
            (stallings_core w).(lg_base).
Proof.
  intros w. apply path_nil. apply stallings_core_base_in_verts.
Qed.

(** Inversion: if a base loop reads w', so does rev(map letter_inv w'). *)
Theorem stallings_core_base_loop_inv_word {r : nat} :
  forall (w : list (Letter r)) (w' : list (Letter r)),
    path_in (stallings_core w) (stallings_core w).(lg_base) w'
            (stallings_core w).(lg_base) ->
    path_in (stallings_core w) (stallings_core w).(lg_base)
            (List.rev (List.map letter_inv w'))
            (stallings_core w).(lg_base).
Proof.
  intros w w' Hp.
  apply stallings_core_path_reverse. exact Hp.
Qed.

(** The base-loop language of stallings_core w as a predicate on words. *)
Definition stallings_core_subgroup_language {r : nat} (w : list (Letter r))
           (w' : list (Letter r)) : Prop :=
  path_in (stallings_core w) (stallings_core w).(lg_base) w'
          (stallings_core w).(lg_base).

(** Subgroup-property bundle: the language is closed under identity,
    multiplication, and inversion. *)
Theorem stallings_core_subgroup_language_subgroup {r : nat} :
  forall (w : list (Letter r)),
    (* Identity *)
    stallings_core_subgroup_language w [] /\
    (* Closure under concatenation *)
    (forall w1 w2,
       stallings_core_subgroup_language w w1 ->
       stallings_core_subgroup_language w w2 ->
       stallings_core_subgroup_language w (w1 ++ w2)) /\
    (* Closure under inversion *)
    (forall w',
       stallings_core_subgroup_language w w' ->
       stallings_core_subgroup_language w (List.rev (List.map letter_inv w'))).
Proof.
  intros w. split; [|split].
  - apply stallings_core_base_loop_empty.
  - intros w1 w2 Hp1 Hp2. apply stallings_core_base_loop_concat; assumption.
  - intros w' Hp. apply stallings_core_base_loop_inv_word. exact Hp.
Qed.

(** w itself is in the language. *)
Theorem stallings_core_subgroup_language_w {r : nat} :
  forall (w : list (Letter r)),
    stallings_core_subgroup_language w w.
Proof.
  intros w. apply stallings_core_base_loop_w.
Qed.

(** Any cyclic-word concatenation is in the subgroup language.
    This says ⟨w⟩ ⊆ subgroup_language w. *)
Theorem stallings_core_subgroup_language_contains_cyclic_word {r : nat} :
  forall (w : list (Letter r)) (ls : list (cyclic_word_letter w)),
    stallings_core_subgroup_language w (expand_cwls w ls).
Proof.
  intros w ls. apply stallings_core_base_loop_cyclic_word.
Qed.

(** Powers of w are in the subgroup language. *)
Theorem stallings_core_subgroup_language_w_pow {r : nat} :
  forall (w : list (Letter r)) (k : nat),
    stallings_core_subgroup_language w (word_power w k).
Proof.
  intros w k. unfold stallings_core_subgroup_language.
  induction k as [|k IH].
  - apply stallings_core_base_loop_empty.
  - simpl. apply stallings_core_base_loop_concat.
    + apply stallings_core_base_loop_w.
    + exact IH.
Qed.


(** stallings_core base admits a path reading the inverse of w from
    base to base, derived via path reversal. *)
Theorem stallings_core_base_loop_w_inv {r : nat} :
  forall (w : list (Letter r)),
    path_in (stallings_core w) (stallings_core w).(lg_base)
            (List.rev (List.map letter_inv w))
            (stallings_core w).(lg_base).
Proof.
  intros w.
  apply stallings_core_path_reverse.
  apply stallings_core_base_loop_w.
Qed.

(** Inverse-powers of w are in the subgroup language. *)
Theorem stallings_core_subgroup_language_w_inv_pow {r : nat} :
  forall (w : list (Letter r)) (k : nat),
    stallings_core_subgroup_language w
      (word_power (List.rev (List.map letter_inv w)) k).
Proof.
  intros w k. unfold stallings_core_subgroup_language.
  induction k as [|k IH].
  - apply stallings_core_base_loop_empty.
  - simpl. apply stallings_core_base_loop_concat.
    + apply stallings_core_base_loop_w_inv.
    + exact IH.
Qed.

(** Words in the subgroup language are over the petal alphabet. *)
Theorem stallings_core_subgroup_language_alphabet_bound {r : nat} :
  forall (w : list (Letter r)) (w' : list (Letter r)),
    stallings_core_subgroup_language w w' ->
    forall l', In l' w' -> in_petal_alphabet w l'.
Proof.
  intros w w' Hpath l' Hin.
  apply (stallings_core_path_alphabet w _ _ _ Hpath l' Hin).
Qed.

(** stallings_core paths split at any prefix (via stallings_core_wf). *)
Theorem stallings_core_path_split_prefix {r : nat} :
  forall (w : list (Letter r)) (w1 w2 : list (Letter r)) (u v : Vertex),
    path_in (stallings_core w) u (w1 ++ w2) v ->
    exists m, path_in (stallings_core w) u w1 m /\
              path_in (stallings_core w) m w2 v.
Proof.
  intros w. apply path_in_split_prefix. apply stallings_core_wf.
Qed.

(** stallings_core path_in_app_iff. *)
Theorem stallings_core_path_app_iff {r : nat} :
  forall (w : list (Letter r)) (u v : Vertex) (w1 w2 : list (Letter r)),
    path_in (stallings_core w) u (w1 ++ w2) v <->
    exists m, path_in (stallings_core w) u w1 m /\
              path_in (stallings_core w) m w2 v.
Proof.
  intros w u v w1 w2. apply path_in_app_iff. apply stallings_core_wf.
Qed.

(** Corollary: stallings_core w admits a path reading w^k for any k.
    Encodes ⟨w⟩ ⊆ language(stallings_core w). *)
Theorem stallings_core_path_w_pow {r : nat} :
  forall (w : list (Letter r)) (k : nat),
    exists u' v', path_in (stallings_core w) u' (word_power w k) v'.
Proof.
  intros w k. unfold stallings_core.
  apply (fold_iterate_path_exists (num_vertices (petal_graph w))
                                   (petal_graph w) 0 0 (word_power w k)).
  - apply petal_graph_wf_graph.
  - apply petal_graph_path_w_pow.
Qed.

(** Once we reach a folded graph, more fuel doesn't change anything. *)
Lemma fold_iterate_extra_fuel {r : nat} :
  forall (fuel1 fuel2 : nat) (G G' : LGraph r),
    fold_iterate fuel1 G = G' ->
    is_folded G' ->
    fold_iterate (fuel1 + fuel2) G = G'.
Proof.
  induction fuel1 as [|k IH]; intros fuel2 G G' Heq Hfolded.
  - simpl in Heq. subst G'. simpl. apply fold_iterate_folded_is_id. exact Hfolded.
  - simpl. destruct (fold_step G) as [G_step|] eqn:Hfs.
    + simpl in Heq. rewrite Hfs in Heq.
      apply (IH fuel2 G_step G' Heq Hfolded).
    + simpl in Heq. rewrite Hfs in Heq.
      subst G'. reflexivity.
Qed.

(** Note: an UNCONDITIONAL `fold_step_decreases` would be UNSOUND
    because for an ill-formed graph (with edge targets outside the
    vertex list), `identify_vertices v1 v2` may not decrease the
    vertex count when v1 ∉ lg_verts. So we use the conditional form
    `fold_step_decreases_clean` and propagate well-formedness
    invariants through `fold_iterate`. *)

(** After enough folds, the graph is folded (no more fold opportunities).
    This is now PROVEN under wf_graph + no_dup_edges by chaining:
    - fold_iterate_done_wf: fold_step result is None (under wf).
    - fold_iterate_no_dup_edges: NoDup is preserved.
    - fold_step_none_implies_folded: NoDup + fold_step = None ⟹ is_folded. *)
Lemma fold_iterate_folded :
  forall {r : nat} (G : LGraph r),
    wf_graph G ->
    no_dup_edges G ->
    is_folded (fold_iterate (num_vertices G) G).
Proof. intros r G Hwf Hnd. apply fold_iterate_folded_wf_nodup; assumption. Qed.

(** Folding preserves the language of paths from basepoint to basepoint
    (i.e., the subgroup).

    The FORWARD direction (path in G ⟹ path in fold) is now proven
    [fold_preserves_subgroup_forward], requiring only wf_graph G.

    The BACKWARD direction (path in fold ⟹ path in G) requires lifting
    paths through identify_vertices, which is more delicate (a vertex
    [v2] in the folded graph can correspond to either [v1] or [v2] in
    the original). Stated below as a conditional axiom for now. *)

(* CAG zero-dependent Conjecture fold_preserves_subgroup_backward theories/HallFreeGroup/StallingsFolding.v:1958 BEGIN
Conjecture fold_preserves_subgroup_backward :
  forall {r : nat} (G : LGraph r) (w : list (Letter r)),
    wf_graph G ->
    path_in (fold_iterate (num_vertices G) G)
            (fold_iterate (num_vertices G) G).(lg_base)
            w
            (fold_iterate (num_vertices G) G).(lg_base) ->
    path_in G G.(lg_base) w G.(lg_base).
   CAG zero-dependent Conjecture fold_preserves_subgroup_backward theories/HallFreeGroup/StallingsFolding.v:1958 END *)

(** Combined iff version: forward direction is proven, backward is the
    remaining axiom. *)
(* CAG zero-dependent Lemma fold_preserves_subgroup theories/HallFreeGroup/StallingsFolding.v:1969 BEGIN
Lemma fold_preserves_subgroup :
  forall {r : nat} (G : LGraph r) (w : list (Letter r)),
    wf_graph G ->
    (path_in G G.(lg_base) w G.(lg_base) <->
     path_in (fold_iterate (num_vertices G) G)
             (fold_iterate (num_vertices G) G).(lg_base)
             w
             (fold_iterate (num_vertices G) G).(lg_base)).
Proof.
  intros r G w Hwf. split.
  - apply fold_preserves_subgroup_forward, Hwf.
  - apply fold_preserves_subgroup_backward, Hwf.
Qed.
   CAG zero-dependent Lemma fold_preserves_subgroup theories/HallFreeGroup/StallingsFolding.v:1969 END *)
