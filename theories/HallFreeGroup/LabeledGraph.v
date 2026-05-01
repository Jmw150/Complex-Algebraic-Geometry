(** * HallFreeGroup/LabeledGraph.v

    Finite directed graphs labeled by [Letter r] (generators and
    inverses of the free group F_r). Used as Stallings core graphs
    for finitely generated subgroups of F_r. *)

From CAG Require Import FreeGroup.
From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Vectors.Fin.
Import ListNotations.

(** A vertex is identified by a natural-number index. *)
Definition Vertex := nat.

(** A labeled edge: source v, label l, target w.
    We allow edges in both "positive" and "negative" directions: a
    positive edge [(v, l, w)] with l = (i, false) is "v —g_i→ w";
    a negative edge with l = (i, true) is "v —g_i^{-1}→ w". By
    convention, we ALSO require the reverse edge: if (v, l, w) is
    in the graph, so is (w, letter_inv l, v). This makes the graph
    "involutive". *)

Record Edge (r : nat) : Type := mkEdge
  { e_src : Vertex
  ; e_lbl : Letter r
  ; e_tgt : Vertex
  }.

Arguments mkEdge {r}.
Arguments e_src {r}.
Arguments e_lbl {r}.
Arguments e_tgt {r}.

(** A finite labeled directed graph: a list of vertices and a list of
    edges. We keep the basepoint as an explicit field. *)

Record LGraph (r : nat) : Type := mkLG
  { lg_verts    : list Vertex
  ; lg_edges    : list (Edge r)
  ; lg_base     : Vertex
  (* No additional invariants required at this level. *)
  }.

Arguments mkLG {r}.
Arguments lg_verts {r}.
Arguments lg_edges {r}.
Arguments lg_base {r}.

(** ** Edge equality (decidable). *)

Lemma edge_eq_dec {r : nat} (e1 e2 : Edge r) : {e1 = e2} + {e1 <> e2}.
Proof.
  destruct e1 as [s1 l1 t1], e2 as [s2 l2 t2].
  destruct (Nat.eq_dec s1 s2) as [Hs|Hs];
    [|right; intro H; injection H; intros; congruence].
  destruct (letter_eq_dec l1 l2) as [Hl|Hl];
    [|right; intro H; injection H; intros; congruence].
  destruct (Nat.eq_dec t1 t2) as [Ht|Ht];
    [|right; intro H; injection H; intros; congruence].
  subst. left. reflexivity.
Qed.

(** ** Edge predicates. *)

(** Outgoing edges from vertex [v] with label [l]. *)
Definition out_edges {r : nat} (G : LGraph r) (v : Vertex) (l : Letter r)
  : list (Edge r) :=
  filter (fun e =>
    if Nat.eqb e.(e_src) v then
      if letter_eq_dec e.(e_lbl) l then true else false
    else false) G.(lg_edges).

(** Number of outgoing edges with given source and label. *)
Definition out_count {r : nat} (G : LGraph r) (v : Vertex) (l : Letter r)
  : nat := length (out_edges G v l).

(** A graph is "folded" / "immersed" if at most one outgoing edge per
    (vertex, label) pair. *)
Definition is_folded {r : nat} (G : LGraph r) : Prop :=
  forall (v : Vertex) (l : Letter r),
    out_count G v l <= 1.

(** ** Path traversal in the graph. *)

(** A path from vertex u to vertex v reading word w is a sequence of
    edges following labels in w from u to v. *)

Inductive path_in {r : nat} (G : LGraph r) :
  Vertex -> list (Letter r) -> Vertex -> Prop :=
  | path_nil : forall v, In v G.(lg_verts) -> path_in G v [] v
  | path_cons : forall u v w l rest,
      In (mkEdge u l v) G.(lg_edges) ->
      path_in G v rest w ->
      path_in G u (l :: rest) w.

(** ** Adding edges (used in subgroup-graph construction). *)

(** Add an edge to the graph (and its inverse). *)
Definition add_edge {r : nat} (G : LGraph r)
    (u : Vertex) (l : Letter r) (v : Vertex) : LGraph r :=
  mkLG G.(lg_verts)
       (mkEdge u l v :: mkEdge v (letter_inv l) u :: G.(lg_edges))
       G.(lg_base).

(** Add a vertex. *)
Definition add_vertex {r : nat} (G : LGraph r) (v : Vertex) : LGraph r :=
  mkLG (v :: G.(lg_verts)) G.(lg_edges) G.(lg_base).

(** ** Core graph for a single word: a "petal" cycle. *)

(** Build the core graph for the cyclic subgroup ⟨w⟩, where w is given
    as a list of letters. The graph is a single cycle of length
    |w|, with vertex 0 as the basepoint, and the cycle labeled with
    the letters of w. *)

(** Build a path of edges spelling [w] from vertex [cur] toward
    successive new vertices starting at [next_v]. The final letter's
    target is [final], so a cyclic petal is built by setting
    final = basepoint.

    Implementation note: since the last letter's target depends on
    the position in the list, we build the chain incrementally, then
    rewire the last edge's target to [final] in a separate step. *)

(** Auxiliary: build a chain of fresh-vertex edges following [w]
    starting at [cur], using fresh vertices from [next_v] upward. *)
Fixpoint chain_edges {r : nat} (cur : Vertex) (next_v : Vertex)
    (w : list (Letter r))
  : list Vertex * list (Edge r) * Vertex :=
  match w with
  | [] => ([], [], cur)
  | l :: rest =>
      let '(vs, es, last_v) := chain_edges next_v (S next_v) rest in
      (next_v :: vs,
       mkEdge cur l next_v :: mkEdge next_v (letter_inv l) cur :: es,
       last_v)
  end.

(** Rewire the last edge (cur, l, next_v) to (cur, l, basepoint).
    Practical implementation: just construct the petal with the
    chain plus a closing edge. *)

Definition petal_graph {r : nat} (w : list (Letter r)) : LGraph r :=
  match w with
  | [] => mkLG [0] [] 0
  | l :: nil =>
      (* single letter: a self-loop labeled l *)
      mkLG [0] [mkEdge 0 l 0; mkEdge 0 (letter_inv l) 0] 0
  | l :: rest =>
      (* multi-letter: chain l1, ..., l_{n-1} on fresh vertices,
         then a closing edge l_n from the last fresh vertex back to 0. *)
      let '(vs, es, last_v) := chain_edges 0 1 (removelast (l :: rest)) in
      let last_letter := List.last (l :: rest) l in
      mkLG (0 :: vs)
           (mkEdge last_v last_letter 0
            :: mkEdge 0 (letter_inv last_letter) last_v
            :: es)
           0
  end.

(** ** Basic lemmas. *)

Lemma petal_graph_basepoint : forall {r : nat} (w : list (Letter r)),
    (petal_graph w).(lg_base) = 0.
Proof.
  intros r w. unfold petal_graph.
  destruct w as [|l rest]; [reflexivity|].
  destruct rest as [|l2 rest2]; [reflexivity|].
  destruct (chain_edges 0 1 (removelast (l :: l2 :: rest2))) as [[vs es] last_v].
  reflexivity.
Qed.

(** ** Number of edges in a finite list. *)

Definition num_edges {r : nat} (G : LGraph r) : nat :=
  length G.(lg_edges).

Definition num_vertices {r : nat} (G : LGraph r) : nat :=
  length G.(lg_verts).

(** ** Well-formedness of the petal graph for short words. *)

(** The petal graph for the empty word is well-formed: no edges. *)
Lemma petal_graph_nil_wf {r : nat} :
  forall e : Edge r,
    In e (lg_edges (petal_graph (@nil (Letter r)))) ->
    In e.(e_src) (lg_verts (petal_graph (@nil (Letter r)))) /\
    In e.(e_tgt) (lg_verts (petal_graph (@nil (Letter r)))).
Proof.
  intros e Hin. simpl in Hin. inversion Hin.
Qed.

(** The petal graph for a single letter [l] is well-formed: both edges
    are self-loops at the basepoint 0. *)
Lemma petal_graph_single_wf {r : nat} :
  forall (l : Letter r) (e : Edge r),
    In e (lg_edges (petal_graph [l])) ->
    In e.(e_src) (lg_verts (petal_graph [l])) /\
    In e.(e_tgt) (lg_verts (petal_graph [l])).
Proof.
  intros l e Hin. simpl in Hin. simpl.
  destruct Hin as [Heq | [Heq | Hbad]].
  - subst e. simpl. split; left; reflexivity.
  - subst e. simpl. split; left; reflexivity.
  - inversion Hbad.
Qed.

(** Structural invariant of chain_edges: all edges have endpoints in
    {cur} ∪ vs, and last_v ∈ {cur} ∪ vs. *)
Lemma chain_edges_invariant {r : nat} :
  forall (w : list (Letter r)) (cur next_v : Vertex) (vs : list Vertex)
         (es : list (Edge r)) (last_v : Vertex),
    chain_edges cur next_v w = (vs, es, last_v) ->
    In last_v (cur :: vs) /\
    (forall e, In e es -> In e.(e_src) (cur :: vs) /\
                          In e.(e_tgt) (cur :: vs)).
Proof.
  induction w as [|l rest IH]; intros cur next_v vs es last_v Hch.
  - simpl in Hch. injection Hch as Hvs Hes Hlv. subst.
    split; [left; reflexivity|]. intros e Hin. inversion Hin.
  - simpl in Hch.
    destruct (chain_edges next_v (S next_v) rest) as [[vs' es'] last_v'] eqn:Hrec.
    pose proof (IH next_v (S next_v) vs' es' last_v' Hrec) as [Hlv_in Hes_in].
    injection Hch as Hvs Hes Hlv. subst.
    split.
    + destruct Hlv_in as [Heq | Hin].
      * subst. right; left; reflexivity.
      * right. right. exact Hin.
    + intros e Hin. simpl in Hin.
      destruct Hin as [Heq | [Heq | Hin']].
      * subst e. simpl. split; [left; reflexivity | right; left; reflexivity].
      * subst e. simpl. split; [right; left; reflexivity | left; reflexivity].
      * pose proof (Hes_in e Hin') as [Hsrc Htgt].
        split.
        -- destruct Hsrc as [Heq | Hin'']; [right; left; assumption | right; right; assumption].
        -- destruct Htgt as [Heq | Hin'']; [right; left; assumption | right; right; assumption].
Qed.

(** General petal_graph well-formedness for words of length ≥ 2. *)
Lemma petal_graph_multi_wf {r : nat} :
  forall (l1 l2 : Letter r) (rest : list (Letter r)) (e : Edge r),
    In e (lg_edges (petal_graph (l1 :: l2 :: rest))) ->
    In e.(e_src) (lg_verts (petal_graph (l1 :: l2 :: rest))) /\
    In e.(e_tgt) (lg_verts (petal_graph (l1 :: l2 :: rest))).
Proof.
  intros l1 l2 rest e Hin.
  unfold petal_graph in *.
  destruct (chain_edges 0 1 (removelast (l1 :: l2 :: rest))) as [[vs es] last_v]
    eqn:Hch.
  pose proof (chain_edges_invariant _ 0 1 vs es last_v Hch) as [Hlv_in Hes_in].
  simpl in Hin.
  destruct Hin as [Heq | [Heq | Hin']].
  - subst e. simpl. split; [exact Hlv_in | left; reflexivity].
  - subst e. simpl. split; [left; reflexivity | exact Hlv_in].
  - pose proof (Hes_in e Hin') as [Hsrc Htgt]. split; assumption.
Qed.

(** Combined: petal_graph is well-formed for any word. *)
Lemma petal_graph_wf {r : nat} :
  forall (w : list (Letter r)),
    forall e : Edge r,
      In e (lg_edges (petal_graph w)) ->
      In e.(e_src) (lg_verts (petal_graph w)) /\
      In e.(e_tgt) (lg_verts (petal_graph w)).
Proof.
  intros w e Hin.
  destruct w as [|l1 [|l2 rest]].
  - apply (petal_graph_nil_wf _ Hin).
  - apply (petal_graph_single_wf _ _ Hin).
  - apply (petal_graph_multi_wf _ _ _ _ Hin).
Qed.

(** ** Path existence in the petal graph. *)

(** Every path in petal_graph [] reads the empty word, since the graph
    has no edges. *)
Lemma petal_graph_nil_path_only_empty {r : nat} :
  forall (u v : Vertex) (w' : list (Letter r)),
    path_in (petal_graph (@nil (Letter r))) u w' v ->
    w' = [] /\ u = 0 /\ v = 0.
Proof.
  intros u v w' Hp.
  induction Hp as [v0 Hv | u0 v0 x0 l0 rest0 Hedge Hrest IH].
  - simpl in Hv. destruct Hv as [Hv | F]; [|inversion F].
    subst v0. split; [reflexivity | split; reflexivity].
  - simpl in Hedge. inversion Hedge.
Qed.

(** Empty word: trivial path from basepoint to basepoint in any
    petal_graph (since 0 ∈ verts always). *)
Lemma petal_graph_nil_path {r : nat} :
  forall (w : list (Letter r)),
    path_in (petal_graph w) 0 [] 0.
Proof.
  intros w. apply path_nil.
  unfold petal_graph.
  destruct w as [|l rest]; [left; reflexivity|].
  destruct rest as [|l2 rest2]; [left; reflexivity|].
  destruct (chain_edges 0 1 (removelast (l :: l2 :: rest2))) as [[vs es] last_v].
  simpl. left. reflexivity.
Qed.

(** Single-letter petal: reading l gives a path 0 → 0. *)
Lemma petal_graph_single_path_l {r : nat} :
  forall (l : Letter r),
    path_in (petal_graph [l]) 0 [l] 0.
Proof.
  intros l.
  apply path_cons with (v := 0).
  - simpl. left. reflexivity.
  - apply path_nil. simpl. left. reflexivity.
Qed.

(** Single-letter petal: reading l^{-1} also gives a path 0 → 0. *)
Lemma petal_graph_single_path_inv {r : nat} :
  forall (l : Letter r),
    path_in (petal_graph [l]) 0 [letter_inv l] 0.
Proof.
  intros l.
  apply path_cons with (v := 0).
  - simpl. right. left. reflexivity.
  - apply path_nil. simpl. left. reflexivity.
Qed.

(** Every path in petal_graph [l] starts and ends at 0. *)
Lemma petal_graph_single_path_endpoints {r : nat} :
  forall (l : Letter r) (u v : Vertex) (w' : list (Letter r)),
    path_in (petal_graph [l]) u w' v ->
    u = 0 /\ v = 0.
Proof.
  intros l u v w' Hp.
  induction Hp as [v0 Hv | u0 v0 x0 l0 rest0 Hedge Hrest IH].
  - simpl in Hv. destruct Hv as [Hv | F]; [|inversion F].
    subst v0. split; reflexivity.
  - simpl in Hedge. destruct Hedge as [He | [He | F]].
    + apply (f_equal e_src) in He as Hsrc. simpl in Hsrc.
      destruct IH as [_ Hv]. split; [exact (eq_sym Hsrc) | exact Hv].
    + apply (f_equal e_src) in He as Hsrc. simpl in Hsrc.
      destruct IH as [_ Hv]. split; [exact (eq_sym Hsrc) | exact Hv].
    + inversion F.
Qed.

(** A label l' is in the "petal alphabet" of w if l' or letter_inv l' is
    in w. (Equivalently, l' or its inverse appears as some letter of w.) *)
Definition in_petal_alphabet {r : nat} (w : list (Letter r)) (l : Letter r)
  : Prop :=
  In l w \/ In (letter_inv l) w.

Lemma in_petal_alphabet_letter_inv {r : nat} (w : list (Letter r)) (l : Letter r) :
  in_petal_alphabet w l <-> in_petal_alphabet w (letter_inv l).
Proof.
  unfold in_petal_alphabet. split.
  - intros [Hin | Hin].
    + right. rewrite letter_inv_involutive. exact Hin.
    + left. exact Hin.
  - intros [Hin | Hin].
    + right. exact Hin.
    + left. rewrite <- (letter_inv_involutive l). exact Hin.
Qed.

(** Every letter of w is in the petal alphabet. *)
Lemma in_petal_alphabet_letter {r : nat} (w : list (Letter r)) (l : Letter r) :
  In l w -> in_petal_alphabet w l.
Proof. intros Hin. left. exact Hin. Qed.

(** Helper: removelast result is a sublist of original. *)
Lemma in_removelast_in_orig {A : Type} :
  forall (l : list A) (x : A), In x (removelast l) -> In x l.
Proof.
  intros l x. revert x.
  induction l as [|y rest IH]; intros x Hin.
  - simpl in Hin. inversion Hin.
  - destruct rest as [|z rest']; [inversion Hin|].
    simpl removelast in Hin.
    simpl in Hin. destruct Hin as [Heq | Hin'].
    + subst y. left. reflexivity.
    + right. apply IH. exact Hin'.
Qed.

(** Helper: the last element is in the list. *)
Lemma last_in {A : Type} :
  forall (l : list A) (d : A), l <> [] -> In (List.last l d) l.
Proof.
  intros l d Hne. destruct l as [|x rest]; [contradiction|].
  clear Hne. revert x. induction rest as [|y rest IH]; intro x.
  - simpl. left. reflexivity.
  - simpl. right. apply IH.
Qed.

(** chain_edges' labels are letters of w (not inverses, by structure). *)
Lemma chain_edges_lbl_in_w {r : nat} :
  forall (w : list (Letter r)) (cur next_v : Vertex)
         (vs : list Vertex) (es : list (Edge r)) (last_v : Vertex),
    chain_edges cur next_v w = (vs, es, last_v) ->
    forall e, In e es ->
      In e.(e_lbl) w \/ In (letter_inv e.(e_lbl)) w.
Proof.
  induction w as [|l rest IH]; intros cur next_v vs es last_v Hch e Hin.
  - simpl in Hch. injection Hch as Hvs Hes Hlv. subst. inversion Hin.
  - simpl in Hch.
    destruct (chain_edges next_v (S next_v) rest) as [[vs' es'] last_v'] eqn:Hrec.
    pose proof (IH next_v (S next_v) vs' es' last_v' Hrec) as IHapp.
    injection Hch as Hvs Hes Hlv. subst.
    simpl in Hin. destruct Hin as [Heq | [Heq | Hin']].
    + (* (cur, l, next_v) *)
      subst e. simpl. left. left. reflexivity.
    + (* (next_v, letter_inv l, cur) *)
      subst e. simpl. right. rewrite letter_inv_involutive. left. reflexivity.
    + (* recursion *)
      destruct (IHapp e Hin') as [Hin_w | Hin_w].
      * left. right. exact Hin_w.
      * right. right. exact Hin_w.
Qed.

(** Every path in petal_graph [l] reads only letters from {l, l^{-1}}. *)
Lemma petal_graph_single_path_alphabet {r : nat} :
  forall (l : Letter r) (u v : Vertex) (w' : list (Letter r)),
    path_in (petal_graph [l]) u w' v ->
    forall l', In l' w' -> l' = l \/ l' = letter_inv l.
Proof.
  intros l u v w' Hp.
  induction Hp as [v0 _ | u0 v0 x0 l0 rest0 Hedge Hrest IH];
    intros l' Hin'.
  - inversion Hin'.
  - simpl in Hin'. destruct Hin' as [Heq | Hin''].
    + (* l' = l0; l0 is the label of an edge in petal_graph [l] *)
      subst l'.
      simpl in Hedge. destruct Hedge as [He | [He | F]].
      * apply (f_equal e_lbl) in He. simpl in He.
        left. symmetry. exact He.
      * apply (f_equal e_lbl) in He. simpl in He.
        right. symmetry. exact He.
      * inversion F.
    + apply IH. exact Hin''.
Qed.

(** Trivial: a path reading [] has the same source and target. *)
Lemma path_in_empty_word {r : nat} (G : LGraph r) :
  forall (u v : Vertex),
    path_in G u [] v -> u = v.
Proof.
  intros u v Hp. inversion Hp. reflexivity.
Qed.

(** ** Equivalence/iff lemmas for petal_graph short cases. *)

(** Empty petal_graph: full path characterization. *)
Lemma petal_graph_nil_path_iff {r : nat} :
  forall (u v : Vertex) (w' : list (Letter r)),
    path_in (petal_graph (@nil (Letter r))) u w' v <->
    (w' = [] /\ u = 0 /\ v = 0).
Proof.
  intros u v w'. split.
  - apply petal_graph_nil_path_only_empty.
  - intros [Hw [Hu Hv]]. subst.
    apply petal_graph_nil_path.
Qed.

(** Single-letter petal_graph: endpoint constraint as iff (one side). *)
Lemma petal_graph_single_path_iff_endpoints {r : nat} :
  forall (l : Letter r) (u v : Vertex) (w' : list (Letter r)),
    path_in (petal_graph [l]) u w' v ->
    u = 0 /\ v = 0.
Proof.
  intros l u v w' Hp.
  apply (petal_graph_single_path_endpoints l u v w' Hp).
Qed.

(** ** Path inversion lemmas: splitting a path on its first letter. *)

Lemma path_in_inv_cons {r : nat} (G : LGraph r) :
  forall (u v : Vertex) (l : Letter r) (rest : list (Letter r)),
    path_in G u (l :: rest) v ->
    exists w, In (mkEdge u l w) G.(lg_edges) /\ path_in G w rest v.
Proof.
  intros u v l rest Hp. inversion Hp; subst.
  exists v0. split; assumption.
Qed.

Lemma path_in_inv_nil {r : nat} (G : LGraph r) :
  forall (u v : Vertex),
    path_in G u [] v ->
    u = v /\ In v G.(lg_verts).
Proof.
  intros u v Hp. inversion Hp; subst.
  split; [reflexivity|assumption].
Qed.

(** Combining: given a path u →[w]→ v, split it at any prefix.
    Requires wf_graph for the source-in-verts membership. *)
Lemma path_in_split_prefix {r : nat} (G : LGraph r) :
  (forall e, In e G.(lg_edges) ->
             In e.(e_src) G.(lg_verts) /\ In e.(e_tgt) G.(lg_verts)) ->
  forall (w1 w2 : list (Letter r)) (u v : Vertex),
    path_in G u (w1 ++ w2) v ->
    exists m, path_in G u w1 m /\ path_in G m w2 v.
Proof.
  intros Hwf w1. induction w1 as [|l rest IH]; intros w2 u v Hp.
  - simpl in Hp. exists u. split; [|exact Hp].
    inversion Hp as [v0 Hv0 Heq1 Heq2 Heq3
                    | u0 v0 x0 l0 rest0 Hedge Hrest Heq1 Heq2 Heq3]; subst.
    + apply path_nil. assumption.
    + apply path_nil. apply Hwf in Hedge as [Hsrc _]. simpl in Hsrc. exact Hsrc.
  - simpl in Hp.
    apply path_in_inv_cons in Hp.
    destruct Hp as [w [Hedge Hrest]].
    apply IH in Hrest.
    destruct Hrest as [m [Hp1 Hp2]].
    exists m. split; [|exact Hp2].
    apply path_cons with (v := w); assumption.
Qed.

(** Specialization: path in petal_graph splits at any prefix (wf is automatic). *)
Lemma petal_graph_path_split_prefix {r : nat} :
  forall (w : list (Letter r)) (w1 w2 : list (Letter r)) (u v : Vertex),
    path_in (petal_graph w) u (w1 ++ w2) v ->
    exists m, path_in (petal_graph w) u w1 m /\
              path_in (petal_graph w) m w2 v.
Proof.
  intros w. apply path_in_split_prefix. apply petal_graph_wf.
Qed.


(** Two-letter petal: reading l1 :: l2 :: nil gives a path 0 → 0
    via the fresh vertex 1. *)
Lemma petal_graph_two_path {r : nat} :
  forall (l1 l2 : Letter r),
    path_in (petal_graph [l1; l2]) 0 [l1; l2] 0.
Proof.
  intros l1 l2.
  apply path_cons with (v := 1).
  - simpl. right. right. left. reflexivity.
  - apply path_cons with (v := 0).
    + simpl. left. reflexivity.
    + apply path_nil. simpl. left. reflexivity.
Qed.

(** Two-letter petal, inverse word: reading l2^{-1} :: l1^{-1} :: nil
    gives a path 0 → 0 via the fresh vertex 1. *)
Lemma petal_graph_two_path_inv {r : nat} :
  forall (l1 l2 : Letter r),
    path_in (petal_graph [l1; l2]) 0 [letter_inv l2; letter_inv l1] 0.
Proof.
  intros l1 l2.
  apply path_cons with (v := 1).
  - simpl. right. left. reflexivity.
  - apply path_cons with (v := 0).
    + simpl. right. right. right. left. reflexivity.
    + apply path_nil. simpl. left. reflexivity.
Qed.

(** Two-letter petal, cyclic shift: reading [l2; l1] gives a path 1 → 1
    (going around the cycle starting from vertex 1). *)
Lemma petal_graph_two_path_cyclic {r : nat} :
  forall (l1 l2 : Letter r),
    path_in (petal_graph [l1; l2]) 1 [l2; l1] 1.
Proof.
  intros l1 l2.
  apply path_cons with (v := 0).
  - simpl. left. reflexivity.
  - apply path_cons with (v := 1).
    + simpl. right. right. left. reflexivity.
    + apply path_nil. simpl. right. left. reflexivity.
Qed.

(** ** Edge count of petal_graph: 2 * length(w). *)

Lemma chain_edges_length {r : nat} :
  forall (w : list (Letter r)) (cur next_v : Vertex)
         (vs : list Vertex) (es : list (Edge r)) (last_v : Vertex),
    chain_edges cur next_v w = (vs, es, last_v) ->
    length es = 2 * length w.
Proof.
  induction w as [|l rest IH]; intros cur next_v vs es last_v Hch.
  - simpl in Hch. injection Hch as Hvs Hes Hlv. subst. reflexivity.
  - simpl in Hch.
    destruct (chain_edges next_v (S next_v) rest) as [[vs' es'] last_v'] eqn:Hrec.
    pose proof (IH next_v (S next_v) vs' es' last_v' Hrec) as IHapp.
    injection Hch as Hvs Hes Hlv. subst.
    simpl. rewrite IHapp. lia.
Qed.

Lemma length_removelast_cons {A : Type} :
  forall (l : list A), l <> [] -> length (removelast l) = length l - 1.
Proof.
  intros l Hne.
  destruct l as [|x l]; [contradiction|].
  clear Hne. revert x. induction l as [|y l IH]; intro x.
  - simpl. reflexivity.
  - simpl. f_equal. specialize (IH y).
    simpl in IH. lia.
Qed.

Lemma petal_graph_num_edges {r : nat} :
  forall (w : list (Letter r)),
    length (lg_edges (petal_graph w)) = 2 * length w.
Proof.
  intros w. unfold petal_graph.
  destruct w as [|l1 [|l2 rest]].
  - reflexivity.
  - reflexivity.
  - destruct (chain_edges 0 1 (removelast (l1 :: l2 :: rest)))
      as [[vs es] last_v] eqn:Hch.
    pose proof (chain_edges_length _ _ _ _ _ _ Hch) as Hlen.
    simpl. rewrite Hlen.
    rewrite length_removelast_cons; [|discriminate].
    simpl. lia.
Qed.

(** chain_edges produces |w| fresh vertices in vs. *)
Lemma chain_edges_vs_length {r : nat} :
  forall (w : list (Letter r)) (cur next_v : Vertex)
         (vs : list Vertex) (es : list (Edge r)) (last_v : Vertex),
    chain_edges cur next_v w = (vs, es, last_v) ->
    length vs = length w.
Proof.
  induction w as [|l rest IH]; intros cur next_v vs es last_v Hch.
  - simpl in Hch. injection Hch as Hvs Hes Hlv. subst. reflexivity.
  - simpl in Hch.
    destruct (chain_edges next_v (S next_v) rest) as [[vs' es'] last_v'] eqn:Hrec.
    pose proof (IH next_v (S next_v) vs' es' last_v' Hrec) as IHapp.
    injection Hch as Hvs Hes Hlv. subst.
    simpl. rewrite IHapp. reflexivity.
Qed.

(** Vertex count of petal_graph: max(1, length w). *)
Lemma petal_graph_num_vertices {r : nat} :
  forall (w : list (Letter r)),
    length (lg_verts (petal_graph w)) = Nat.max 1 (length w).
Proof.
  intros w. unfold petal_graph.
  destruct w as [|l1 [|l2 rest]].
  - reflexivity.
  - reflexivity.
  - destruct (chain_edges 0 1 (removelast (l1 :: l2 :: rest)))
      as [[vs es] last_v] eqn:Hch.
    pose proof (chain_edges_vs_length _ _ _ _ _ _ Hch) as Hlen.
    simpl. rewrite Hlen.
    rewrite length_removelast_cons; [|discriminate].
    simpl. lia.
Qed.

(** Path concatenation: combining paths u→v with w1 and v→x with w2
    gives a path u→x with w1 ++ w2. This is a structural property of
    [path_in] and useful for combining sub-paths. *)
Lemma path_in_app {r : nat} (G : LGraph r) :
  forall (u v x : Vertex) (w1 w2 : list (Letter r)),
    path_in G u w1 v ->
    path_in G v w2 x ->
    path_in G u (w1 ++ w2) x.
Proof.
  intros u v x w1 w2 H1.
  induction H1 as [v0 Hv0 | u0 v0 x0 l0 rest0 Hedge Hrest IH]; intros H2.
  - simpl. exact H2.
  - simpl. apply path_cons with (v := v0).
    + exact Hedge.
    + apply IH. exact H2.
Qed.

(** path_in respects iff under append, given wf_graph. *)
Lemma path_in_app_iff {r : nat} (G : LGraph r) :
  (forall e, In e G.(lg_edges) ->
             In e.(e_src) G.(lg_verts) /\ In e.(e_tgt) G.(lg_verts)) ->
  forall (u v : Vertex) (w1 w2 : list (Letter r)),
    path_in G u (w1 ++ w2) v <->
    exists m, path_in G u w1 m /\ path_in G m w2 v.
Proof.
  intros Hwf u v w1 w2. split.
  - apply path_in_split_prefix; assumption.
  - intros [m [H1 H2]]. apply (path_in_app G u m v w1 w2 H1 H2).
Qed.

(** Specialization: petal_graph path_in_app_iff. *)
Lemma petal_graph_path_app_iff {r : nat} :
  forall (w : list (Letter r)) (u v : Vertex) (w1 w2 : list (Letter r)),
    path_in (petal_graph w) u (w1 ++ w2) v <->
    exists m, path_in (petal_graph w) u w1 m /\
              path_in (petal_graph w) m w2 v.
Proof.
  intros w u v w1 w2. apply path_in_app_iff. apply petal_graph_wf.
Qed.

(** Monotonicity of path_in under graph extension via add_edge: every
    path in [G] is still a path in [add_edge G u' l' v']. *)
Lemma path_in_add_edge_mono {r : nat} (G : LGraph r) :
  forall (u v : Vertex) (w : list (Letter r)),
    path_in G u w v ->
    forall (u' v' : Vertex) (l' : Letter r),
      path_in (add_edge G u' l' v') u w v.
Proof.
  intros u v w Hpath u' v' l'.
  induction Hpath as [v0 Hv0 | u0 v0 x0 l0 rest0 Hedge Hrest IH].
  - apply path_nil. simpl. exact Hv0.
  - apply path_cons with (v := v0).
    + simpl. right. right. exact Hedge.
    + exact IH.
Qed.

(** Monotonicity of path_in under graph extension via add_vertex: every
    path in [G] is still a path in [add_vertex G v']. *)
Lemma path_in_add_vertex_mono {r : nat} (G : LGraph r) :
  forall (u v : Vertex) (w : list (Letter r)),
    path_in G u w v ->
    forall (v' : Vertex),
      path_in (add_vertex G v') u w v.
Proof.
  intros u v w Hpath v'.
  induction Hpath as [v0 Hv0 | u0 v0 x0 l0 rest0 Hedge Hrest IH].
  - apply path_nil. simpl. right. exact Hv0.
  - apply path_cons with (v := v0).
    + simpl. exact Hedge.
    + exact IH.
Qed.

(** ** Generalized graph monotonicity for path_in.

    A common pattern: if every edge of [G] is an edge of [G'] and every
    vertex of [G] is a vertex of [G'], then any path in [G] is a path
    in [G']. This subsumes [add_edge_mono] and [add_vertex_mono]. *)

Lemma path_in_subgraph_mono {r : nat} :
  forall (G G' : LGraph r),
    (forall v, In v G.(lg_verts) -> In v G'.(lg_verts)) ->
    (forall e, In e G.(lg_edges) -> In e G'.(lg_edges)) ->
    forall (u v : Vertex) (w : list (Letter r)),
      path_in G u w v -> path_in G' u w v.
Proof.
  intros G G' Hverts Hedges u v w Hpath.
  induction Hpath as [v0 Hv0 | u0 v0 x0 l0 rest0 Hedge Hrest IH].
  - apply path_nil. apply Hverts. exact Hv0.
  - apply path_cons with (v := v0).
    + apply Hedges. exact Hedge.
    + exact IH.
Qed.

(** ** Involutive graphs and path reversal.

    A graph is "involutive" if every edge (u, l, v) has a reverse edge
    (v, letter_inv l, u). The petal_graph and identify_vertices output
    are both involutive (by construction). In involutive graphs, paths
    reverse: a path u → v reading w corresponds to a path v → u reading
    rev(map letter_inv w). *)

Definition is_involutive {r : nat} (G : LGraph r) : Prop :=
  forall (u v : Vertex) (l : Letter r),
    In (mkEdge u l v) G.(lg_edges) ->
    In (mkEdge v (letter_inv l) u) G.(lg_edges).

(** A path that ends at v has v in the vertex set (when w is non-empty
    or path is path_nil). Useful to extract endpoint membership. *)
Lemma path_in_target_in_verts {r : nat} (G : LGraph r) :
  forall (u v : Vertex) (w : list (Letter r)),
    path_in G u w v -> In v G.(lg_verts).
Proof.
  intros u v w H.
  induction H as [v0 Hv0 | u0 v0 x0 l0 rest0 Hedge Hrest IH].
  - exact Hv0.
  - exact IH.
Qed.

(** In an involutive graph, paths reverse. The reversal of u →[w]→ v
    is v →[rev (map letter_inv w)]→ u. *)

Lemma path_in_reverse_involutive {r : nat} (G : LGraph r) :
  is_involutive G ->
  (forall e, In e G.(lg_edges) ->
             In e.(e_src) G.(lg_verts) /\ In e.(e_tgt) G.(lg_verts)) ->
  forall (u v : Vertex) (w : list (Letter r)),
    path_in G u w v ->
    path_in G v (List.rev (List.map letter_inv w)) u.
Proof.
  intros Hinv Hwf u v w H.
  induction H as [v0 Hv0 | u0 v0 x0 l0 rest0 Hedge Hrest IH].
  - simpl. apply path_nil. exact Hv0.
  - simpl.
    apply path_in_app with (v := v0); [exact IH|].
    apply path_cons with (v := u0).
    + apply Hinv. exact Hedge.
    + apply path_nil.
      pose proof (Hwf (mkEdge u0 l0 v0) Hedge) as [Hsrc _].
      simpl in Hsrc. exact Hsrc.
Qed.

(** ** petal_graph is involutive. *)

Lemma petal_graph_nil_involutive {r : nat} :
  is_involutive (petal_graph (@nil (Letter r))).
Proof.
  intros u v l Hin. simpl in Hin. inversion Hin.
Qed.

Lemma petal_graph_single_involutive {r : nat} (l : Letter r) :
  is_involutive (petal_graph [l]).
Proof.
  intros u v l0 Hin. simpl in Hin. simpl.
  destruct Hin as [Heq | [Heq | Hbad]].
  - injection Heq as Hu Hl Hv. subst.
    right. left. reflexivity.
  - injection Heq as Hu Hl Hv. subst. rewrite letter_inv_involutive.
    left. reflexivity.
  - inversion Hbad.
Qed.

(** ** chain_edges produces a forward path. *)

(** chain_edges builds a forward path from [cur] reading [w] to [last_v],
    where each edge of [es] is in any superset graph G that contains them.

    The vertex membership requirement is encoded as: cur ∈ G.verts and
    each new vertex (next_v, next_v + 1, ..., last_v - 1) is in G.verts. *)
Lemma chain_edges_forward_path {r : nat} :
  forall (w : list (Letter r)) (cur next_v : Vertex)
         (vs : list Vertex) (es : list (Edge r)) (last_v : Vertex),
    chain_edges cur next_v w = (vs, es, last_v) ->
    forall (G : LGraph r),
      In cur G.(lg_verts) ->
      (forall v, In v vs -> In v G.(lg_verts)) ->
      (forall e, In e es -> In e G.(lg_edges)) ->
      path_in G cur w last_v.
Proof.
  induction w as [|l rest IH]; intros cur next_v vs es last_v Hch G Hcur Hvs Hes.
  - simpl in Hch. injection Hch as Hvs0 Hes0 Hlv. subst.
    apply path_nil. exact Hcur.
  - simpl in Hch.
    destruct (chain_edges next_v (S next_v) rest) as [[vs' es'] last_v'] eqn:Hrec.
    injection Hch as Hvs0 Hes0 Hlv. subst.
    apply path_cons with (v := next_v).
    + apply Hes. simpl. left. reflexivity.
    + apply (IH next_v (S next_v) vs' es' last_v Hrec G).
      * apply Hvs. left. reflexivity.
      * intros v Hin. apply Hvs. right. exact Hin.
      * intros e Hin. apply Hes. simpl. right. right. exact Hin.
Qed.

(** ** General petal_graph forward path: reading w gives a path 0 → 0
    in petal_graph w. *)

(** chain_edges produces edges with strictly bounded src vertices. *)
Lemma chain_edges_src_bound {r : nat} :
  forall (w : list (Letter r)) (cur next_v : Vertex)
         (vs : list Vertex) (es : list (Edge r)) (last_v : Vertex),
    chain_edges cur next_v w = (vs, es, last_v) ->
    forall e, In e es ->
      In e.(e_src) (cur :: vs) /\ In e.(e_tgt) (cur :: vs).
Proof.
  intros. apply (chain_edges_invariant w cur next_v vs es last_v H).
  exact H0.
Qed.

(** Every edge label in petal_graph w is in the petal alphabet of w. *)
Lemma petal_graph_lbl_in_alphabet {r : nat} :
  forall (w : list (Letter r)) (e : Edge r),
    In e (lg_edges (petal_graph w)) ->
    in_petal_alphabet w e.(e_lbl).
Proof.
  intros w e Hin.
  destruct w as [|l1 [|l2 rest]].
  - simpl in Hin. inversion Hin.
  - simpl in Hin.
    destruct Hin as [Heq | [Heq | F]]; [..|inversion F].
    + subst e. simpl. left. left. reflexivity.
    + subst e. simpl. right. rewrite letter_inv_involutive. left. reflexivity.
  - unfold petal_graph in Hin.
    destruct (chain_edges 0 1 (removelast (l1 :: l2 :: rest)))
      as [[vs es] last_v] eqn:Hch.
    set (last_letter := List.last (l1 :: l2 :: rest) l1) in *.
    simpl in Hin.
    destruct Hin as [Heq | [Heq | Hin']].
    + subst e. simpl. left.
      apply (last_in (l1 :: l2 :: rest) l1). discriminate.
    + subst e. simpl. right. rewrite letter_inv_involutive.
      apply (last_in (l1 :: l2 :: rest) l1). discriminate.
    + pose proof (chain_edges_lbl_in_w _ _ _ _ _ _ Hch e Hin') as Hlbl.
      destruct Hlbl as [Hin_w | Hin_w].
      * left. apply in_removelast_in_orig with (l := l1 :: l2 :: rest).
        exact Hin_w.
      * right. apply in_removelast_in_orig with (l := l1 :: l2 :: rest).
        exact Hin_w.
Qed.

(** Every path in petal_graph w reads only letters from the petal alphabet. *)
Lemma petal_graph_path_alphabet {r : nat} :
  forall (w : list (Letter r)) (u v : Vertex) (w' : list (Letter r)),
    path_in (petal_graph w) u w' v ->
    forall l', In l' w' -> in_petal_alphabet w l'.
Proof.
  intros w u v w' Hp.
  induction Hp as [v0 _ | u0 v0 x0 l0 rest0 Hedge Hrest IH];
    intros l' Hin.
  - inversion Hin.
  - simpl in Hin. destruct Hin as [Heq | Hin''].
    + subst l'.
      pose proof (petal_graph_lbl_in_alphabet w (mkEdge u0 l0 v0) Hedge) as Hlbl.
      simpl in Hlbl. exact Hlbl.
    + apply IH. exact Hin''.
Qed.

(** Edges produced by chain_edges always come in inverse pairs. *)
Lemma chain_edges_involutive {r : nat} :
  forall (w : list (Letter r)) (cur next_v : Vertex)
         (vs : list Vertex) (es : list (Edge r)) (last_v : Vertex),
    chain_edges cur next_v w = (vs, es, last_v) ->
    forall (u v : Vertex) (l : Letter r),
      In (mkEdge u l v) es ->
      In (mkEdge v (letter_inv l) u) es.
Proof.
  induction w as [|l rest IH]; intros cur next_v vs es last_v Hch u v l0 Hin.
  - simpl in Hch. injection Hch as Hvs0 Hes0 Hlv. subst.
    inversion Hin.
  - simpl in Hch.
    destruct (chain_edges next_v (S next_v) rest) as [[vs' es'] last_v'] eqn:Hrec.
    injection Hch as Hvs0 Hes0 Hlv.
    rewrite <- Hes0 in *. clear Hes0 Hvs0 Hlv vs es last_v.
    simpl in Hin.
    destruct Hin as [Heq | [Heq | Hin']].
    + injection Heq as Hu Hl Hv. subst u l0 v.
      simpl. right. left. reflexivity.
    + injection Heq as Hu Hl Hv. subst u l0 v.
      rewrite letter_inv_involutive.
      simpl. left. reflexivity.
    + simpl. right. right.
      apply (IH next_v (S next_v) vs' es' last_v' Hrec u v l0 Hin').
Qed.

(** General petal_graph involutivity: every edge has its inverse twin. *)
Lemma petal_graph_multi_involutive {r : nat} (l1 l2 : Letter r) (rest : list (Letter r)) :
  is_involutive (petal_graph (l1 :: l2 :: rest)).
Proof.
  intros u v l0 Hin.
  unfold petal_graph in *.
  destruct (chain_edges 0 1 (removelast (l1 :: l2 :: rest)))
    as [[vs es] last_v] eqn:Hch.
  set (last_letter := List.last (l1 :: l2 :: rest) l1) in *.
  simpl in Hin.
  destruct Hin as [Heq | [Heq | Hin']].
  - injection Heq as Hu Hl Hv. subst u l0 v.
    simpl. right. left. reflexivity.
  - injection Heq as Hu Hl Hv. subst u l0 v.
    rewrite letter_inv_involutive.
    simpl. left. reflexivity.
  - simpl. right. right.
    apply (chain_edges_involutive _ 0 1 vs es last_v Hch u v l0 Hin').
Qed.

Lemma petal_graph_involutive {r : nat} (w : list (Letter r)) :
  is_involutive (petal_graph w).
Proof.
  destruct w as [|l1 [|l2 rest]].
  - apply petal_graph_nil_involutive.
  - apply petal_graph_single_involutive.
  - apply petal_graph_multi_involutive.
Qed.

Lemma petal_graph_path_w {r : nat} :
  forall (w : list (Letter r)),
    path_in (petal_graph w) 0 w 0.
Proof.
  intros w.
  destruct w as [|l1 [|l2 rest]].
  - apply petal_graph_nil_path.
  - apply petal_graph_single_path_l.
  - (* multi-letter: w = l1 :: l2 :: rest *)
    unfold petal_graph.
    destruct (chain_edges 0 1 (removelast (l1 :: l2 :: rest)))
      as [[vs es] last_v] eqn:Hch.
    set (last_letter := List.last (l1 :: l2 :: rest) l1).
    set (G := mkLG (0 :: vs)
                   (mkEdge last_v last_letter 0
                    :: mkEdge 0 (letter_inv last_letter) last_v
                    :: es)
                   0).
    (* Use the chain_edges path 0 → last_v reading removelast w,
       then extend with the last_letter edge to get 0 → 0 reading w. *)
    pose proof (chain_edges_forward_path
                  (removelast (l1 :: l2 :: rest))
                  0 1 vs es last_v Hch G) as Hpath_chain.
    assert (Happ : path_in G 0 (removelast (l1 :: l2 :: rest) ++ [last_letter]) 0).
    { apply path_in_app with (v := last_v).
      - apply Hpath_chain.
        + simpl. left. reflexivity.
        + intros v Hin. simpl. right. exact Hin.
        + intros e Hin. simpl. right. right. exact Hin.
      - apply path_cons with (v := 0).
        + simpl. left. reflexivity.
        + apply path_nil. simpl. left. reflexivity. }
    (* removelast (l1 :: l2 :: rest) ++ [last (l1::l2::rest) l1]
       = (l1 :: l2 :: rest) when the list is non-empty. *)
    assert (Heq : removelast (l1 :: l2 :: rest) ++ [last_letter] = l1 :: l2 :: rest).
    { unfold last_letter.
      symmetry. apply app_removelast_last. discriminate. }
    rewrite Heq in Happ.
    exact Happ.
Qed.

(** Corollary: petal_graph w admits a path 0 → 0 reading the inverse
    of w (rev (map letter_inv w)). This is the language closure under
    inversion in F_r. *)
Lemma petal_graph_path_w_inv {r : nat} :
  forall (w : list (Letter r)),
    path_in (petal_graph w) 0 (List.rev (List.map letter_inv w)) 0.
Proof.
  intros w.
  apply path_in_reverse_involutive.
  - apply petal_graph_involutive.
  - apply petal_graph_wf.
  - apply petal_graph_path_w.
Qed.

(** ** Power closure: petal_graph w admits paths reading w concatenated
    with itself k times. This realizes <w> ≤ language(petal_graph w). *)

Fixpoint word_power {A : Type} (w : list A) (k : nat) : list A :=
  match k with
  | 0 => []
  | S k' => w ++ word_power w k'
  end.

(** word_power distributes over addition. *)
Lemma word_power_add {A : Type} (w : list A) (a b : nat) :
  word_power w (a + b) = word_power w a ++ word_power w b.
Proof.
  induction a as [|a IH]; simpl.
  - reflexivity.
  - rewrite IH. rewrite app_assoc. reflexivity.
Qed.

(** word_power length: |w^k| = k * |w|. *)
Lemma word_power_length {A : Type} (w : list A) (k : nat) :
  length (word_power w k) = k * length w.
Proof.
  induction k as [|k IH]; simpl; [reflexivity|].
  rewrite length_app. lia.
Qed.

(** word_power w 1 = w. *)
Lemma word_power_one {A : Type} (w : list A) :
  word_power w 1 = w.
Proof.
  simpl. apply app_nil_r.
Qed.

(** word_power [] k = []. *)
Lemma word_power_nil {A : Type} (k : nat) :
  word_power (@nil A) k = [].
Proof.
  induction k; simpl; [reflexivity|].
  rewrite IHk. reflexivity.
Qed.

(** word_power w 0 = []. *)
Lemma word_power_zero {A : Type} (w : list A) :
  word_power w 0 = [].
Proof. reflexivity. Qed.

(** word_power w (S k) = w ++ word_power w k. *)
Lemma word_power_succ {A : Type} (w : list A) (k : nat) :
  word_power w (S k) = w ++ word_power w k.
Proof. reflexivity. Qed.

(** Multiplicative property: word_power w (a * b) = word_power (word_power w b) a. *)
Lemma word_power_mul {A : Type} (w : list A) (a b : nat) :
  word_power w (a * b) = word_power (word_power w b) a.
Proof.
  induction a as [|a IH]; simpl.
  - reflexivity.
  - rewrite word_power_add. rewrite IH. reflexivity.
Qed.

Lemma petal_graph_path_w_pow {r : nat} :
  forall (w : list (Letter r)) (k : nat),
    path_in (petal_graph w) 0 (word_power w k) 0.
Proof.
  intros w k. induction k as [|k IH].
  - apply petal_graph_nil_path.
  - simpl. apply path_in_app with (v := 0).
    + apply petal_graph_path_w.
    + exact IH.
Qed.

(** Inverse-power: also admits paths reading the inverse of w iterated k times. *)
Lemma petal_graph_path_w_inv_pow {r : nat} :
  forall (w : list (Letter r)) (k : nat),
    path_in (petal_graph w) 0 (word_power (List.rev (List.map letter_inv w)) k) 0.
Proof.
  intros w k. induction k as [|k IH].
  - apply petal_graph_nil_path.
  - simpl. apply path_in_app with (v := 0).
    + apply petal_graph_path_w_inv.
    + exact IH.
Qed.

(** Mixed words: petal_graph admits any concatenation of w and w^{-1}.
    More generally, the language is closed under FREE-MONOID
    operations on the "alphabet" {w, w^{-1}}. *)

Inductive cyclic_word_letter {r : nat} (w : list (Letter r)) : Type :=
  | cwl_w : cyclic_word_letter w
  | cwl_inv : cyclic_word_letter w.

Definition cwl_to_word {r : nat} (w : list (Letter r))
                       (l : cyclic_word_letter w) : list (Letter r) :=
  match l with
  | cwl_w _ => w
  | cwl_inv _ => List.rev (List.map letter_inv w)
  end.

Fixpoint expand_cwls {r : nat} (w : list (Letter r))
         (ls : list (cyclic_word_letter w)) : list (Letter r) :=
  match ls with
  | [] => []
  | l :: rest => cwl_to_word w l ++ expand_cwls w rest
  end.

(** expand_cwls distributes over append. *)
Lemma expand_cwls_app {r : nat} (w : list (Letter r))
      (a b : list (cyclic_word_letter w)) :
  expand_cwls w (a ++ b) = expand_cwls w a ++ expand_cwls w b.
Proof.
  induction a as [|x rest IH]; simpl; [reflexivity|].
  rewrite IH. rewrite app_assoc. reflexivity.
Qed.

(** expand_cwls of nil is nil. *)
Lemma expand_cwls_nil {r : nat} (w : list (Letter r)) :
  expand_cwls w [] = [].
Proof. reflexivity. Qed.

(** Length of expand_cwls is bounded by length(ls) * length(w). *)
Lemma expand_cwls_length {r : nat} (w : list (Letter r))
      (ls : list (cyclic_word_letter w)) :
  length (expand_cwls w ls) = length ls * length w.
Proof.
  induction ls as [|l rest IH].
  - reflexivity.
  - simpl. rewrite length_app, IH.
    destruct l; simpl.
    + reflexivity.
    + rewrite length_rev, length_map. reflexivity.
Qed.

Lemma petal_graph_path_cyclic_word {r : nat} :
  forall (w : list (Letter r)) (ls : list (cyclic_word_letter w)),
    path_in (petal_graph w) 0 (expand_cwls w ls) 0.
Proof.
  intros w ls. induction ls as [|l rest IH].
  - simpl. apply petal_graph_nil_path.
  - simpl. apply path_in_app with (v := 0).
    + destruct l; simpl.
      * apply petal_graph_path_w.
      * apply petal_graph_path_w_inv.
    + exact IH.
Qed.

(** ** No-duplicate-edges invariant for graphs.
    A graph is "edge-unique" if its edge list has no duplicates. This
    invariant + folded → is_folded together give the full Stallings
    correctness. *)

Definition no_dup_edges {r : nat} (G : LGraph r) : Prop :=
  NoDup G.(lg_edges).

(** Single-letter petal_graph is edge-unique: the two edges differ
    because letter_inv l ≠ l. *)
Lemma petal_graph_nil_no_dup_edges {r : nat} :
  no_dup_edges (petal_graph (@nil (Letter r))).
Proof.
  unfold no_dup_edges. simpl. constructor.
Qed.

Lemma petal_graph_single_no_dup_edges {r : nat} (l : Letter r) :
  no_dup_edges (petal_graph [l]).
Proof.
  unfold no_dup_edges. simpl.
  constructor.
  - intro Hin. simpl in Hin. destruct Hin as [Heq | Hbad].
    + (* mkEdge 0 (letter_inv l) 0 = mkEdge 0 l 0 *)
      assert (Hl : letter_inv l = l).
      { apply (f_equal e_lbl) in Heq. simpl in Heq. exact Heq. }
      apply (letter_inv_neq l). exact Hl.
    + inversion Hbad.
  - constructor.
    + intro Hbad. inversion Hbad.
    + constructor.
Qed.

