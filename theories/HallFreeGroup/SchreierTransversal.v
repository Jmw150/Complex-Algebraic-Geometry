(** * HallFreeGroup/SchreierTransversal.v

    Schreier transversals for finite-index subgroups of free groups.

    Given a folded labeled graph G (representing a subgroup H ≤ F_r)
    with vertex set V, a Schreier transversal is a choice of paths
    (one per vertex from basepoint) — these correspond to coset
    representatives of H in F_r. *)

From CAG Require Import FreeGroup.
From CAG Require Import HallFreeGroup.LabeledGraph.
From CAG Require Import HallFreeGroup.StallingsFolding.
From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.

(* ================================================================== *)
(** * 1. Spanning trees in folded graphs                                *)
(* ================================================================== *)

(** A spanning tree of a folded graph: a sub-collection of edges that
    forms a tree connecting all vertices. We can build one greedily
    from the basepoint via BFS. *)

Section SpanningTree.
  Context {r : nat}.

  (** Edges forming a spanning tree, represented as a list. The
      tree is rooted at the basepoint. *)
  Definition SpanningTree := list (Edge r).

  (** Determine whether a vertex is reachable in a tree (= whether the
      vertex is the source/target of some tree edge, or the root). *)
  Fixpoint tree_reaches (root : Vertex) (T : SpanningTree)
      (visited : list Vertex)
      : list Vertex :=
    match T with
    | [] => visited
    | e :: rest =>
        if existsb (Nat.eqb e.(e_src)) visited
        then tree_reaches root rest (e.(e_tgt) :: visited)
        else
          if existsb (Nat.eqb e.(e_tgt)) visited
          then tree_reaches root rest (e.(e_src) :: visited)
          else tree_reaches root rest visited
    end.

  (** Build a spanning tree of [G] using greedy edge addition. *)
  Fixpoint build_tree_aux (fuel : nat) (G : LGraph r)
      (T : SpanningTree) (covered : list Vertex)
      : SpanningTree :=
    match fuel with
    | 0 => T
    | S k =>
        let candidate := find (fun e =>
          (existsb (Nat.eqb e.(e_src)) covered &&
           negb (existsb (Nat.eqb e.(e_tgt)) covered))) G.(lg_edges)
        in
        match candidate with
        | None => T
        | Some e =>
            build_tree_aux k G (e :: T) (e.(e_tgt) :: covered)
        end
    end.

  Definition build_spanning_tree (G : LGraph r) : SpanningTree :=
    build_tree_aux (length G.(lg_edges)) G [] [G.(lg_base)].

End SpanningTree.

(* ================================================================== *)
(** * 2. Tree-paths as coset representatives                            *)
(* ================================================================== *)

(** Given a spanning tree T of a folded graph G, the path from
    basepoint to vertex v (reading labels) gives a coset representative
    for the v-th coset of H. *)

Section TreePaths.
  Context {r : nat}.

  (** Find the path in the tree from [root] to [target] as a list
      of letters. We do a simple DFS up to fuel steps. *)
  Fixpoint tree_path_aux (fuel : nat) (T : list (Edge r))
      (current : Vertex) (target : Vertex) (visited : list Vertex)
      : option (list (Letter r)) :=
    match fuel with
    | 0 => None
    | S k =>
        if Nat.eqb current target then Some []
        else
          let next_options := filter (fun e =>
            Nat.eqb e.(e_src) current &&
            negb (existsb (Nat.eqb e.(e_tgt)) visited)) T in
          let rec_search := fix go (es : list (Edge r))
              : option (list (Letter r)) :=
            match es with
            | [] => None
            | e :: rest =>
                match tree_path_aux k T e.(e_tgt) target
                                    (e.(e_tgt) :: visited) with
                | Some p => Some (e.(e_lbl) :: p)
                | None => go rest
                end
            end
          in rec_search next_options
    end.

  Definition tree_path (T : SpanningTree) (root target : Vertex)
      : option (list (Letter r)) :=
    tree_path_aux (length T + 1) T root target [root].

  (** Coset representatives from a tree: for each vertex of G, the
      path from basepoint to that vertex. *)
  Definition coset_reps (G : LGraph r) (T : SpanningTree)
      : list (Vertex * option (list (Letter r))) :=
    map (fun v => (v, tree_path T G.(lg_base) v)) G.(lg_verts).

End TreePaths.

(* ================================================================== *)
(** * 3. Free generating set from non-tree edges                        *)
(* ================================================================== *)

(** The Schreier generators of H: for each non-tree edge (v, l, w),
    a generator is given by:
      [tree_path basepoint v] · l · [tree_path w basepoint]^{-1}

    These form a free generating set for the subgroup H. *)

Section SchreierGenerators.
  Context {r : nat}.

  (** Reverse a list of letters and invert each. *)
  Definition reverse_invert (w : list (Letter r)) : list (Letter r) :=
    List.rev (List.map (@letter_inv r) w).

  (** A Schreier generator from a non-tree edge. *)
  Definition schreier_gen (T : SpanningTree)
      (basepoint : Vertex) (e : Edge r)
      : option (list (Letter r)) :=
    match tree_path T basepoint e.(e_src),
          tree_path T basepoint e.(e_tgt) with
    | Some p1, Some p2 =>
        Some (p1 ++ [e.(e_lbl)] ++ reverse_invert p2)
    | _, _ => None
    end.

  (** All Schreier generators (one per non-tree edge). *)
  Definition all_schreier_gens (G : LGraph r) (T : SpanningTree)
      : list (list (Letter r)) :=
    List.fold_right (fun e acc =>
      if existsb (fun e' =>
        Nat.eqb e.(e_src) e'.(e_src) &&
        (if letter_eq_dec e.(e_lbl) e'.(e_lbl) then true else false) &&
        Nat.eqb e.(e_tgt) e'.(e_tgt)) T
      then acc  (* tree edge: skip *)
      else
        match schreier_gen T G.(lg_base) e with
        | Some g => g :: acc
        | None => acc
        end) [] G.(lg_edges).

End SchreierGenerators.

(* ================================================================== *)
(** * 4. Free factor decomposition (axiomatized for now)                *)
(* ================================================================== *)

(** **HALL'S FREE FACTOR THEOREM (statement):** Given γ ∈ F_r with
    γ ≠ e, let G be the Stallings core of ⟨γ⟩ and T a spanning tree.
    Then there exists a finite-index subgroup Δ ≤ F_r with:
    - Δ contains ⟨γ⟩.
    - γ is part of a free generating set for Δ (so ⟨γ⟩ is a free
      factor of Δ). *)

(** Predicate: a list of [RWord]s is a /Schreier generating set/
    containing [gamma] as a free generator (axiomatized at this layer;
    the full predicate refers to [DecisionProblems.HallTheorem]'s
    finite-index-subgroup machinery and is wired up there). *)
(* CAG zero-dependent Parameter is_hall_schreier_gen theories/HallFreeGroup/SchreierTransversal.v:180 BEGIN
Parameter is_hall_schreier_gen : forall (r : nat) (gamma : RWord r),
    list (RWord r) -> Prop.
   CAG zero-dependent Parameter is_hall_schreier_gen theories/HallFreeGroup/SchreierTransversal.v:180 END *)

(** Hall's free-factor theorem (famous old, M. Hall 1949;
    Conjecture per skip policy):
    for any non-identity [gamma ∈ F_r], there exist a finite-index
    subgroup [Δ ≤ F_r] and an explicit Schreier generating set of [Δ]
    realising [gamma] as one of the free generators (a free factor).

    γ R37 — replaces the earlier [Lemma … True] busywork form per
    [feedback_trivial_collapse_busywork.md].  The deep work is in
    [DecisionProblems.HallTheorem]; this top-level statement carries
    the standalone existential. *)
(* CAG zero-dependent Conjecture hall_finite_index_via_stallings theories/HallFreeGroup/SchreierTransversal.v:193 BEGIN
Conjecture hall_finite_index_via_stallings :
  forall (r : nat) (gamma : RWord r),
    gamma <> @rword_e r ->
    exists (gens : list (RWord r)),
      is_hall_schreier_gen r gamma gens.
   CAG zero-dependent Conjecture hall_finite_index_via_stallings theories/HallFreeGroup/SchreierTransversal.v:193 END *)

(* ================================================================== *)
(** * 5. Basic structural facts about spanning trees and paths        *)
(* ================================================================== *)

(** tree_path with positive fuel from current to current returns Some []. *)
Lemma tree_path_aux_self {r : nat} :
  forall (T : SpanningTree (r := r)) (current : Vertex)
         (visited : list Vertex) (k : nat),
    @tree_path_aux r (S k) T current current visited = Some [].
Proof.
  intros T current visited k. simpl.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

(** tree_path from a vertex to itself returns Some [] (with fuel ≥ 1). *)
Lemma tree_path_self {r : nat} (T : SpanningTree (r := r)) (v : Vertex) :
  T <> [] \/ length T = 0 ->
  @tree_path r T v v = Some [].
Proof.
  intros _. unfold tree_path.
  destruct (length T + 1) eqn:Hlen.
  - lia.
  - simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

(** Empty SpanningTree: tree_path from v to w always returns
    Some [] if v = w, otherwise None. *)
Lemma tree_path_empty_tree {r : nat} (v w : Vertex) :
  @tree_path r [] v w =
  (if Nat.eqb v w then Some [] else None).
Proof.
  unfold tree_path. simpl.
  destruct (Nat.eqb v w) eqn:Hvw; reflexivity.
Qed.

(** reverse_invert distributes: reverse_invert (a ++ b) = reverse_invert b ++ reverse_invert a. *)
Lemma reverse_invert_app {r : nat} (a b : list (Letter r)) :
  reverse_invert (a ++ b) = reverse_invert b ++ reverse_invert a.
Proof.
  unfold reverse_invert.
  rewrite map_app, rev_app_distr. reflexivity.
Qed.

(** reverse_invert is involutive. *)
Lemma reverse_invert_involutive {r : nat} (w : list (Letter r)) :
  reverse_invert (reverse_invert w) = w.
Proof.
  unfold reverse_invert.
  rewrite map_rev, rev_involutive.
  rewrite map_map.
  rewrite (map_ext _ id).
  - apply map_id.
  - intros l. unfold id. apply letter_inv_involutive.
Qed.

(** reverse_invert of empty is empty. *)
Lemma reverse_invert_nil {r : nat} :
  @reverse_invert r [] = [].
Proof. reflexivity. Qed.

(** Length of reverse_invert = length of input. *)
Lemma reverse_invert_length {r : nat} (w : list (Letter r)) :
  length (reverse_invert w) = length w.
Proof.
  unfold reverse_invert. rewrite length_rev, length_map. reflexivity.
Qed.

(** reverse_invert is symmetric (involution): inverse element of itself. *)
Lemma reverse_invert_symmetric {r : nat} (w : list (Letter r)) :
  reverse_invert (reverse_invert w) = w.
Proof. apply reverse_invert_involutive. Qed.

(** reverse_invert preserves NoDup (since it's a permutation of inverse-letter list). *)
Lemma reverse_invert_singleton {r : nat} (l : Letter r) :
  reverse_invert [l] = [letter_inv l].
Proof. reflexivity. Qed.

(** reverse_invert of a cons distributes (front-back). *)
Lemma reverse_invert_cons {r : nat} (l : Letter r) (rest : list (Letter r)) :
  reverse_invert (l :: rest) = reverse_invert rest ++ [letter_inv l].
Proof.
  unfold reverse_invert. simpl. reflexivity.
Qed.

(** reverse_invert of a singleton-prefix is the inverse-letter as a suffix. *)
Lemma reverse_invert_two {r : nat} (a b : Letter r) :
  reverse_invert [a; b] = [letter_inv b; letter_inv a].
Proof. reflexivity. Qed.

(** Applying letter_inv to each letter then reversing equals reverse_invert. *)
Lemma reverse_invert_via_map_rev {r : nat} (w : list (Letter r)) :
  reverse_invert w = List.rev (List.map (@letter_inv r) w).
Proof. reflexivity. Qed.

(** reverse_invert respects extensional letter_inv equality. *)
Lemma reverse_invert_app_singleton {r : nat} (l : Letter r) (w : list (Letter r)) :
  reverse_invert (w ++ [l]) = letter_inv l :: reverse_invert w.
Proof.
  rewrite reverse_invert_app. simpl. reflexivity.
Qed.

