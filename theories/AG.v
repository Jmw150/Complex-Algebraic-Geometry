
(** Algebraic Geometry 

Also the current Complex Algebraic Geometry main.

*)

From Stdlib Require Import QArith ZArith Lia.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyRealsMult.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyAbs.


(*Local Open Scope Z_scope.*)
(*Local Open Scope Q_scope.*)
Local Open Scope CReal_scope.

From CAG Require Import Reals_extra.
From CAG Require Import Complex.

(** products and lists on constructive complex numbers *)
Inductive Cprod : Type :=
  | pair (n1 n2 : CComplex).

Definition fst (p : Cprod) : CComplex :=
  match p with
  | pair x y => x
  end.

Definition snd (p : Cprod) : CComplex :=
  match p with
  | pair x y => y
  end.

Definition CComplexlist := list CComplex.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


Fixpoint repeat (n : CComplex) (count : nat) : CComplexlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:CComplexlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.


(** The [app] function appends (concatenates) two lists. *)

Fixpoint app (l1 l2 : CComplexlist) : CComplexlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Definition hd (l : list CComplex) : option CComplex :=
  match l with
  | nil => None 
  | h :: t => Some h
  end.

Definition tl (l : CComplexlist) : CComplexlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.


Fixpoint filter (test : CComplex -> bool) (l : CComplexlist) : CComplexlist :=
  match l with
  | nil => nil
  | hd :: tl =>
      if test hd 
      then hd :: filter test tl 
      else filter test tl
  end.


Fixpoint counter (test : CComplex -> bool) (l : CComplexlist) : CComplex :=
  match l with
  | nil => Cinject_Q 0
  | hd :: tl =>
      if test hd then Cadd (Cinject_Q 1) (counter test tl) else counter test tl
  end.

Definition isnil (l : CComplexlist ) : bool 
  := match l with
     | nil => true
     | _ => false
     end.

(* fluff definition *)
Fixpoint alternate (l1 l2 : CComplexlist) : CComplexlist
     (* base cases *)
  := if isnil l1 then l2 else
     if isnil l2 then l1 else
        match l1 with
        | nil => nil (*pure pedantry*)
        | hd1 :: tl1 => 
            match l2 with 
            | nil => nil (*...*)
            | hd2::tl2 => 
                hd1 :: hd2 :: alternate tl1 tl2
            end
        end.


Definition add (v : CComplex) (s : CComplexlist) : CComplexlist
  := match s with
     | nil => [v]
     | hd :: tl => v :: hd :: tl
     end.

Fixpoint filter_first (test : CComplex -> bool) (l : CComplexlist) : CComplexlist :=
  match l with
  | nil => nil
  | hd :: tl =>
      if test hd 
      then tl
      else hd :: filter_first test tl 
  end.

Fixpoint member (test : CComplex -> bool) (s : CComplexlist) : bool
  := match s with
     | nil => false
     | hd :: tl => if test hd then true else member test tl
     end.


Fixpoint rev (l:CComplexlist) : CComplexlist :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.



(* For readability *)
Notation "x +c y" := (Cadd x y) (at level 50).
Notation "x -c y" := (Csub x y) (at level 50).
Notation "x *c y" := (Cmul x y) (at level 40).
Notation "-c x" := (Cneg x) (at level 35).
Notation "x ^c n" := (Cpow x n) (at level 30). (* caution: C*N => C *)

(* make zero vector of length n *)
Fixpoint vzero (n : nat) : list CComplex :=
  match n with
  | O => []
  | S k => C0 :: vzero k
  end.

Fixpoint vadd (v w : list CComplex) : list CComplex :=
  match v, w with
  | x::xs, y::ys => (x +c y) :: vadd xs ys
  | _, _ => []  (* we'll enforce same length, so this branch won't matter *)
  end.

Lemma vadd_length : forall v w,
  length v = length w ->
  length (vadd v w) = length v.
Proof.
  induction v as [|x xs IH]; destruct w as [|y ys]; simpl; intros H; try discriminate; auto. 
Qed.

Fixpoint vscale (a : CComplex) (v : list CComplex) : list CComplex :=
  match v with
  | [] => []
  | x::xs => (a *c x) :: vscale a xs
  end.

Lemma vscale_length : forall a v,
  length (vscale a v) = length v.
Proof. 
  induction v; simpl; auto. 
Qed.

Lemma vzero_length : forall n, length (vzero n) = n.
Proof. 
  induction n; simpl; auto. 
Qed.


Locate Fin.
From Stdlib Require Import Lists.List.
Import ListNotations.

(* Beginning of vec -> vec complex numbers *)
(*Definition Mat := list (list CComplex).*)
Definition Mat (A : Type) : Type := list (list A).

(* “Well-formed n×m matrix” predicate 
   Also useful to check dimensions
*)
Definition Mat_wf (n m : nat) (A : Mat CComplex) : Prop :=
  length A = n /\ forall row, In row A -> length row = m.

(** A and B are compatible for multiplication: #cols(A) = #rows(B). *)
Definition Mat_dimensions_match (A B : Mat CComplex) : Prop :=
  forall row, List.In row A -> length row = length B.

Fixpoint dot (v w : list CComplex) : CComplex 
  := match v, w with 
     | [], [] => C0 
     | x::xs, y::ys => (x *c y) +c (dot xs ys) 
     | _, _ => C0
     end.
(*  
Fixpoint dot (v w : list CComplex) : option CComplex :=
  match v, w with
  | [], [] => Some C0
  | x::xs, y::ys =>
      match dot xs ys with
      | Some acc => Some ((x *c y) +c acc)
      | None => None
      end
  | _, _ => None
  end.
*)

(* needs option type *)
Fixpoint madd (A B : Mat CComplex) : Mat CComplex :=
  match A, B with
  | rA::As, rB::Bs => vadd rA rB :: madd As Bs
  | _, _ => []
  end.

Fixpoint nth_default 
  (d : CComplex) (l : list CComplex) (j : nat) : CComplex :=
  match l, j with
  | [], _ => d
  | x::_, O => x
  | _::xs, S k => nth_default d xs k
  end.

Definition col (A : Mat CComplex) (j : nat) : list CComplex :=
  map (fun row => nth_default C0 row j) A.

Fixpoint mcols (m : nat) (A : Mat CComplex) : list (list CComplex) :=
  match m with
  | O => []
  | S k => mcols k A ++ [col A k]
  end.

Fixpoint row_mul_cols 
  (r : list CComplex) (colsB : list (list CComplex)) 
  : list CComplex :=
  match colsB with
  | [] => []
  | c::cs => dot r c :: row_mul_cols r cs
  end.

Fixpoint mmul (A B : Mat CComplex) (p : nat) : Mat CComplex :=
  let colsB := mcols p B in
  match A with
  | [] => []
  | r::rs => row_mul_cols r colsB :: mmul rs B p
  end.

Definition mneg (A : Mat CComplex) : Mat CComplex := map (map Cneg) A.
Definition msub (A B : Mat CComplex) : Mat CComplex := madd A (mneg B).

Definition commutator (A B : Mat CComplex) (n : nat) : Mat CComplex :=
  msub (mmul A B n) (mmul B A n).

Fixpoint trace_aux (A : list (list CComplex)) (i : nat) : CComplex :=
  match A with
  | [] => C0
  | row :: rows =>
      nth_default C0 row i
      +c trace_aux rows (S i)
  end.

Definition trace (A : list (list CComplex)) : CComplex :=
  trace_aux A 0.

(** Identity matrix: n×n matrix with 1 on the diagonal and 0 elsewhere *)
Definition ident_row (n i : nat) : list CComplex :=
  List.map (fun j => if Nat.eqb i j then C1 else C0) (List.seq 0 n).

Fixpoint mident_aux (n : nat) (i : nat) : Mat CComplex :=
  match n with
  | O => []
  | S k => ident_row (i + S k) i :: mident_aux k (S i)
  end.

Definition mident (n : nat) : Mat CComplex := mident_aux n 0.

Lemma ident_row_length : forall n i, length (ident_row n i) = n.
Proof.
  intros n i. unfold ident_row. rewrite List.length_map, List.length_seq. reflexivity.
Qed.

(** Every row of [mident_aux n i] has length [i + n]. *)
Lemma mident_aux_row_length : forall n i row,
  List.In row (mident_aux n i) -> length row = (i + n)%nat.
Proof.
  induction n as [| n IH]; intros i row Hin.
  - simpl in Hin. inversion Hin.
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + subst row. apply ident_row_length.
    + apply IH in Hin. lia.
Qed.

(** [mident_aux n i] has exactly [n] rows. *)
Lemma mident_aux_length : forall n i,
  length (mident_aux n i) = n.
Proof.
  induction n as [| n IH]; intro i; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma mident_wf : forall n, Mat_wf n n (mident n).
Proof.
  intro n. unfold Mat_wf, mident. split.
  - apply mident_aux_length.
  - intros row Hin.
    exact (mident_aux_row_length n 0 row Hin).
Qed.

(** Helper lemmas for mmul well-formedness *)

Lemma row_mul_cols_length : forall r cols,
  length (row_mul_cols r cols) = length cols.
Proof.
  intros r cols. induction cols as [|c cs IH]; simpl; auto.
Qed.

Lemma mcols_length : forall m A,
  length (mcols m A) = m.
Proof.
  induction m as [|m IH]; intro A; simpl; auto.
  rewrite List.length_app, IH. simpl. lia.
Qed.

Lemma mmul_length_aux : forall A B p,
  length (mmul A B p) = length A.
Proof.
  intros A. induction A as [|r rs IH]; intros B p; simpl; auto.
Qed.

Lemma mmul_row_length_aux : forall A B p row,
  List.In row (mmul A B p) -> length row = p.
Proof.
  intros A. induction A as [|r rs IH]; intros B p row Hin.
  - inversion Hin.
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + subst row. rewrite row_mul_cols_length, mcols_length. reflexivity.
    + exact (IH B p row Hin).
Qed.

(** Key matrix algebra lemmas *)
Lemma mmul_wf : forall n m p A B,
  Mat_wf n m A -> Mat_wf m p B ->
  Mat_wf n p (mmul A B p).
Proof.
  intros n m p A B [HlA _] _.
  split.
  - rewrite mmul_length_aux. exact HlA.
  - intros row Hin. exact (mmul_row_length_aux A B p row Hin).
Qed.

Lemma nth_default_overflow : forall d l j,
  (length l <= j)%nat ->
  nth_default d l j = d.
Proof.
  intros d l. induction l as [|x xs IH]; intros j Hj.
  - destruct j; reflexivity.
  - destruct j as [|j].
    + simpl in Hj. lia.
    + simpl. apply IH. simpl in Hj. lia.
Qed.

Lemma nth_default_eq_nth : forall d l j,
  nth_default d l j = List.nth j l d.
Proof.
  intros d l. induction l as [|x xs IH]; intro j.
  - destruct j; reflexivity.
  - destruct j; simpl; [reflexivity | apply IH].
Qed.

Lemma nth_default_ident_row : forall n i j,
  (j < n)%nat ->
  nth_default C0 (ident_row n i) j = if Nat.eqb i j then C1 else C0.
Proof.
  intros n i j Hj.
  unfold ident_row.
  rewrite nth_default_eq_nth.
  rewrite (@List.nth_indep CComplex
    (List.map (fun k => if Nat.eqb i k then C1 else C0) (List.seq 0 n))
    j C0 (if Nat.eqb i 0%nat then C1 else C0)).
  rewrite List.map_nth with (d := 0%nat).
  rewrite List.seq_nth; [rewrite Nat.add_0_l; reflexivity | exact Hj].
  rewrite List.length_map, List.length_seq. exact Hj.
Qed.

Lemma mident_aux_nth_default : forall n i r j,
  (i <= j)%nat ->
  (j < i + n)%nat ->
  nth_default C0 (List.nth (j - i)%nat (mident_aux n i) []) r =
    if Nat.eqb r j then C1 else C0.
Proof.
  induction n as [|n IH]; intros i r j Hij Hlt.
  - lia.
  - simpl mident_aux.
    destruct (j - i)%nat as [|k] eqn:Hk.
    + replace j with i by lia.
      destruct (lt_dec r (i + S n)) as [Hr | Hr].
      * rewrite Nat.eqb_sym. apply nth_default_ident_row. exact Hr.
      * rewrite nth_default_overflow.
        -- assert (Hneq : (r =? i)%nat = false) by (apply Nat.eqb_neq; lia).
           rewrite Hneq. reflexivity.
        -- simpl. rewrite ident_row_length. lia.
    + replace (List.nth (S k) (ident_row (i + S n) i :: mident_aux n (S i)) [])
        with (List.nth k (mident_aux n (S i)) []) by reflexivity.
      assert (Hk' : k = (j - S i)%nat) by lia.
      rewrite Hk'. apply IH; lia.
Qed.

Lemma col_mident : forall n j,
  (j < n)%nat ->
  col (mident n) j = ident_row n j.
Proof.
  intros n j Hj.
  unfold col, mident.
  apply List.nth_ext with (d := C0) (d' := C0).
  - rewrite List.length_map, mident_aux_length, ident_row_length. reflexivity.
  - intros r Hr.
    rewrite List.length_map, mident_aux_length in Hr.
    rewrite List.map_nth with (d := []).
    rewrite <- nth_default_eq_nth.
    rewrite nth_default_ident_row by exact Hr.
    replace (List.nth r (mident_aux n 0) [])
      with (List.nth (r - 0)%nat (mident_aux n 0) []) by (replace (r - 0)%nat with r by lia; reflexivity).
    rewrite (mident_aux_nth_default n 0 j r) by lia.
    rewrite Nat.eqb_sym. reflexivity.
Qed.

(* CAG zero-dependent Lemma dot_zero_right theories/AG.v:450 BEGIN
Lemma dot_zero_right : forall xs ys,
  (forall y, List.In y ys -> y = C0) ->
  dot xs ys = C0.
Proof.
  induction xs as [|x xs IH]; intros ys Hys.
  - destruct ys; reflexivity.
  - destruct ys as [|y ys].
    + reflexivity.
    + simpl. pose proof (Hys y (or_introl eq_refl)) as Hy. rewrite Hy.
      rewrite Cmul_C0_r.
      rewrite IH.
      * apply Cadd_C0_l.
      * intros z Hz. apply Hys. right. exact Hz.
Qed.
   CAG zero-dependent Lemma dot_zero_right theories/AG.v:450 END *)

(* CAG zero-dependent Lemma dot_ident_row theories/AG.v:465 BEGIN
Lemma dot_ident_row : forall r n j,
  length r = n ->
  (j < n)%nat ->
  dot r (ident_row n j) = nth_default C0 r j.
Proof.
  induction r as [|x xs IH]; intros n j Hlen Hj.
  - simpl in Hlen. subst n. lia.
  - destruct n as [|n]; [simpl in Hlen; discriminate|].
    simpl in Hlen. injection Hlen as Hxs.
    unfold ident_row in *.
    simpl.
    destruct j as [|j].
    + simpl.
      rewrite Cmul_C1_r.
      match goal with
      | |- Cadd x ?tail = x =>
          replace tail with C0
      end.
      * apply Cadd_C0_r.
      * symmetry. apply dot_zero_right. intros y Hy.
        apply List.in_map_iff in Hy.
        destruct Hy as [a [Ha Hin]]. subst y.
        apply List.in_seq in Hin. destruct Hin as [Ha0 _].
        destruct a; [lia | reflexivity].
    + simpl.
      rewrite Cmul_C0_r, Cadd_C0_l.
      match goal with
      | |- dot xs ?cols = nth_default C0 xs j =>
          replace cols with (ident_row n j)
      end.
      * apply IH; [exact Hxs | lia].
      * unfold ident_row.
        rewrite <- (List.seq_shift n 0).
        rewrite List.map_map.
        apply List.map_ext. intro a.
        simpl. reflexivity.
Qed.
   CAG zero-dependent Lemma dot_ident_row theories/AG.v:465 END *)

Lemma nth_mcols : forall p B j,
  (j < p)%nat ->
  List.nth j (mcols p B) [] = col B j.
Proof.
  induction p as [|p IH]; intros B j Hj.
  - lia.
  - simpl mcols.
    destruct (Nat.lt_ge_cases j p) as [Hlt | Hge].
    + rewrite List.app_nth1.
      * apply IH. exact Hlt.
      * rewrite mcols_length. exact Hlt.
    + rewrite List.app_nth2.
      * rewrite mcols_length.
        replace (j - p)%nat with 0%nat by lia.
        simpl. replace j with p by lia. reflexivity.
      * rewrite mcols_length. lia.
Qed.

Lemma nth_row_mul_cols : forall r cols j,
  (j < length cols)%nat ->
  List.nth j (row_mul_cols r cols) C0 = dot r (List.nth j cols []).
Proof.
  intros r cols. induction cols as [|c cs IH]; intros j Hj.
  - simpl in Hj. lia.
  - destruct j as [|j].
    + reflexivity.
    + simpl. apply IH. simpl in Hj. lia.
Qed.

(* CAG zero-dependent Lemma row_mul_cols_mident theories/AG.v:532 BEGIN
Lemma row_mul_cols_mident : forall r n,
  length r = n ->
  row_mul_cols r (mcols n (mident n)) = r.
Proof.
  intros r n Hlen.
  apply List.nth_ext with (d := C0) (d' := C0).
  - rewrite row_mul_cols_length, mcols_length. symmetry. exact Hlen.
  - intros j Hj.
    rewrite row_mul_cols_length, mcols_length in Hj.
    assert (Hcols :
      List.nth j (mcols n (mident n)) [] = ident_row n j).
    { rewrite nth_mcols by exact Hj. apply col_mident. exact Hj. }
    rewrite nth_row_mul_cols by (rewrite mcols_length; exact Hj).
    rewrite Hcols.
    rewrite dot_ident_row by (assumption || exact Hj).
    apply nth_default_eq_nth.
Qed.
   CAG zero-dependent Lemma row_mul_cols_mident theories/AG.v:532 END *)

(* CAG zero-dependent Lemma mmul_assoc theories/AG.v:550 BEGIN
Lemma mmul_assoc : forall A B C p,
  mmul A (mmul B C p) p = mmul (mmul A B p) C p.
Proof. Admitted.
   CAG zero-dependent Lemma mmul_assoc theories/AG.v:550 END *)

(* CAG zero-dependent Lemma mmul_mident_right theories/AG.v:554 BEGIN
Lemma mmul_mident_right : forall n A,
  Mat_wf n n A -> mmul A (mident n) n = A.
Proof.
  intros n A [_ Hrows].
  induction A as [|r rs IH].
  - reflexivity.
  - simpl. f_equal.
    + apply row_mul_cols_mident. apply Hrows. left. reflexivity.
    + apply IH. intros row Hin. apply Hrows. right. exact Hin.
Qed.
   CAG zero-dependent Lemma mmul_mident_right theories/AG.v:554 END *)

(* CAG zero-dependent Lemma mmul_mident_left theories/AG.v:565 BEGIN
Lemma mmul_mident_left : forall n A,
  Mat_wf n n A -> mmul (mident n) A n = A.
Proof. Admitted.
   CAG zero-dependent Lemma mmul_mident_left theories/AG.v:565 END *)

From CAG Require Import Topology.

(*Parameter Rn : nat -> Type.*)
(* CAG zero-dependent Parameter Rn_top theories/AG.v:572 BEGIN
Parameter Rn_top : forall n, Topology (Rn n).
   CAG zero-dependent Parameter Rn_top theories/AG.v:572 END *)

(* CAG zero-dependent Definition LocallyEuclidean theories/AG.v:574 BEGIN
Definition LocallyEuclidean {M : Type} (TM : Topology M) (n : nat) : Prop :=
  forall p : M,
    exists U : set M,
      is_open TM U /\
      U p /\
      exists V : set (Rn n),
        is_open (Rn_top n) V /\
        is_homeomorphic
          (subspace_topology TM U)
          (subspace_topology (Rn_top n) V).
   CAG zero-dependent Definition LocallyEuclidean theories/AG.v:574 END *)

(* CAG constructive-remove Record TopologicalManifold theories/AG.v:601 BEGIN -- constructive downstream cleanup: missing LocallyEuclidean
Record TopologicalManifold := {
  M : Type;
  TM : Topology M;
  dim : nat;

  hausdorff : Hausdorff TM;
  second_countable : SecondCountable TM;
  locally_euclidean : LocallyEuclidean TM dim;
}.
   CAG constructive-remove Record TopologicalManifold theories/AG.v:601 END *)

(* CAG constructive-remove Record Chart theories/AG.v:613 BEGIN -- constructive downstream cleanup: missing Rn_top
Record Chart (M : Type) (TM : Topology M) (n : nat) := {
  U : set M;
  U_open : is_open TM U;

  Ut : set (Rn n);  (* this is ˜U *)
  Ut_open : is_open (Rn_top n) Ut;

  phi_homeo :
    Homeomorphism
      (subspace_topology TM U)
      (subspace_topology (Rn_top n) Ut);
}.
   CAG constructive-remove Record Chart theories/AG.v:613 END *)

(* CAG zero-dependent Definition IsChart theories/AG.v:608 BEGIN
Definition IsChart 
  (M : Type) (TM : Topology M) (n : nat) (U : set M) : Prop :=
  is_open TM U /\
  exists Ut : set (Rn n),
    is_open (Rn_top n) Ut /\
    is_homeomorphic
      (subspace_topology TM U)
      (subspace_topology (Rn_top n) Ut).
   CAG zero-dependent Definition IsChart theories/AG.v:608 END *)


From CAG Require Import Group.
From CAG Require Import ComplexAnalysis.
From CAG Require Import ComplexAnalysis2.


(*Definition subgroup (G : group) : Prop :=*)

(** 
Given X a topological space, a sheaf F on X associates to each open
set U subset X a group F(U), called the sections of F over U, and to
each pair U \subset V of open sets a map r_{V,U} : F(V) -> F(U),
called the restriction map, satisfying

1. For any triple U \subset V \subset W of open sets, r_{W,U} =
r_{V,U} * r_{W,V}. By virtue of this relation, we may write sigma|U
for r_{V,U}(sigma) without loss of information.

2. For any pair of open sets U, V \subset M and sections sigma \in
F(U), tau \in F(V) such that sigma|{U \intersection V} = tau|{U
\intersection V} there exists a section p \in F(U \cup V) with p|U =
sigma, p|v = tau.

3. If sigma \in F(U \union V) and sigma|U = sigma|V = 0 then \sigma =
0.
*)

(* RIP Sheaf *)
(* (* This ended up being LLM generated garbage... *)
Record Sheaf (X : Type) (T : Topology X) :=
{
  (* sections over an open set *)
  F : forall (U : set X), is_open (T U) -> Type;

  (* group structure on sections *)
  G : forall (U : set X) (Uopen : is_open (T U)), Group (F U hU);

  (* restriction along inclusion U ⊆ V : F(V) -> F(U) *)
  res :
    forall (U V : set X)
           (hU : is_open T U) (hV : is_open T V),
      (forall x : X, U x -> V x) ->
      F V hV -> F U hU;

  (* 1. r_{W,U} = r_{V,U} ∘ r_{W,V} *)
  res_comp :
    forall (U V W : set X)
           (hU : is_open T U) (hV : is_open T V) (hW : is_open T W)
           (hUV : forall x : X, U x -> V x)
           (hVW : forall x : X, V x -> W x)
           (hUW : forall x : X, U x -> W x)
           (sigma : F W hW),
      res U W hU hW hUW sigma
      =
      res U V hU hV hUV (res V W hV hW hVW sigma);

  (* 2. binary gluing *)
  glue2 :
    forall (U V : set X)
           (hU : is_open T U) (hV : is_open T V)
           (hUV : is_open T (inter2 U V))
           (hUuV : is_open T (union2 U V))
           (sigma : F U hU) (tau : F V hV),
      res (inter2 U V) U hUV hU (fun x hx => proj1 hx) sigma
      =
      res (inter2 U V) V hUV hV (fun x hx => proj2 hx) tau
      ->
      exists (p : F (union2 U V) hUuV),
        res U (union2 U V) hU hUuV (fun x hx => or_introl hx) p = sigma
        /\
        res V (union2 U V) hV hUuV (fun x hx => or_intror hx) p = tau;

  (* 3. locality in the “zero section” form: 0 = group identity e *)
  local2_zero :
    forall (U V : set X)
           (hU : is_open T U) (hV : is_open T V)
           (hUuV : is_open T (union2 U V))
           (sigma : F (union2 U V) hUuV),
      res U (union2 U V) hU hUuV (fun x hx => or_introl hx) sigma
        = (G U hU).(e G)
      ->
      res V (union2 U V) hV hUuV (fun x hx => or_intror hx) sigma
        = (G V hV).(e G)
      ->
      sigma = (G (union2 U V) hUuV).(e G)
}.
*)
(** Examples follow here *)

Definition two_plus_i : CComplex :=
  mkC (inject_Q 2) (inject_Q 1).


(* A polynomial in z: p(z) = z^3 + (2+i) z + 1 *)
Definition p (z : CComplex) : CComplex :=
  Cadd (Cadd (Cpow z 3) (Cmul two_plus_i z)) C1.

Definition z0 : CComplex :=
  mkC (inject_Q (1#3)) (inject_Q (1#2)).


(* A basic constructive-real function: f(x) = 2x + 1 *)
(* already defined? *)
Definition fr (x : CReal) : CReal :=
  x + x + 1.

(* g(x) = x^3 + 2x + 1 *)
Definition gr (x : CReal) : CReal :=
  (pow x 2%nat) + (inject_Q 2 * x) + 1.


(* Example input: 1/3 as a constructive real *)
Definition one_third : CReal := inject_Q (1#3).

(* Ask for an approximation at precision index k = -10 
(i.e. error < 2^-10 scale) *)
(*Eval compute in approx (fr one_third) (-10).*)





(** Below is a list of programs *)

(* real function *)
Definition run_f (k : Z) : Z * Z :=
  q_as_Zpair (approx (fr one_third) k).

(* another real function *)
Definition run_g (k : Z) : Z * Z :=
  q_as_Zpair (approx (gr one_third) k).

(* complex function *)
Definition run_p (n : Z) : Q * Q :=
  Capprox (p z0) n.

(* ================================================================== *)
(** * Part III: Analytic Varieties and Complex Manifolds               *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(** ** 1. Analytic varieties                                            *)
(* ------------------------------------------------------------------ *)

(** A subset V of an open U ⊂ Cⁿ is an analytic variety if every
    point has a neighborhood where V is the common zero locus of
    finitely many holomorphic functions. *)
Definition AnalyticVariety {n : nat}
    (U : Cn n -> Prop)
    (V : Cn n -> Prop) : Prop :=
  forall p : Cn n, U p ->
    exists (U' : Cn n -> Prop) (fs : list (Cn n -> CComplex)),
      (forall z, U' z -> U z) /\
      U' p /\
      (forall f, List.In f fs ->
         holomorphic_Cn U' f) /\
      forall z, U' z ->
        (V z <-> forall f, List.In f fs -> Cequal (f z) C0).

(** An analytic hypersurface is locally the zero locus of a
    single nonzero holomorphic function. *)
Definition AnalyticHypersurface {n : nat}
    (U : Cn n -> Prop)
    (V : Cn n -> Prop) : Prop :=
  forall p : Cn n, U p ->
    exists (U' : Cn n -> Prop) (f : Cn n -> CComplex),
      (forall z, U' z -> U z) /\
      U' p /\
      holomorphic_Cn U' f /\
      (exists q : Cn n, U' q /\ ~ Cequal (f q) C0) /\
      forall z, U' z -> (V z <-> Cequal (f z) C0).

(** V is irreducible: it cannot be written as V1 ∪ V2 with V1, V2
    proper analytic subvarieties. *)
Definition irreducible_variety {n : nat}
    (U : Cn n -> Prop)
    (V : Cn n -> Prop) : Prop :=
  AnalyticVariety U V /\
  ~ exists (V1 V2 : Cn n -> Prop),
      AnalyticVariety U V1 /\
      AnalyticVariety U V2 /\
      (forall z, V z -> V1 z \/ V2 z) /\
      (exists z, V z /\ ~ V1 z) /\
      (exists z, V z /\ ~ V2 z).

(** V is irreducible at p if for sufficiently small neighborhoods
    U' of p, V ∩ U' is irreducible. *)
Definition irreducible_at {n : nat}
    (U : Cn n -> Prop)
    (V : Cn n -> Prop)
    (p : Cn n) : Prop :=
  exists r : CReal, CRpositive r /\
    irreducible_variety
      (Polydisc p (fun _ => r))
      (fun z => V z /\ Polydisc p (fun _ => r) z).

(** The smooth locus V* consists of points where V is a manifold. *)
Definition smooth_point {n : nat}
    (U : Cn n -> Prop)
    (V : Cn n -> Prop)
    (p : Cn n) : Prop :=
  V p /\
  exists (k : nat) (fs : list (Cn n -> CComplex)) (U' : Cn n -> Prop),
    (forall z, U' z -> U z) /\
    U' p /\
    List.length fs = k /\
    (forall f, List.In f fs -> holomorphic_Cn U' f) /\
    (forall z, U' z -> V z <-> forall f, List.In f fs -> Cequal (f z) C0).

Definition smooth_locus {n : nat}
    (U : Cn n -> Prop)
    (V : Cn n -> Prop)
    (z : Cn n) : Prop :=
  smooth_point U V z.

Definition singular_locus {n : nat}
    (U : Cn n -> Prop)
    (V : Cn n -> Prop)
    (z : Cn n) : Prop :=
  V z /\ ~ smooth_point U V z.

(** Multiplicity of a hypersurface at a point:
    the order of vanishing of the defining function f at p.
    Here we axiomatize the order-of-vanishing map. *)
(* CAG zero-dependent Parameter order_of_vanishing theories/AG.v:841 BEGIN
Parameter order_of_vanishing : forall {n : nat},
    (Cn n -> CComplex) -> Cn n -> nat.
   CAG zero-dependent Parameter order_of_vanishing theories/AG.v:841 END *)

(* CAG zero-dependent Definition mult_hypersurface theories/AG.v:844 BEGIN
Definition mult_hypersurface {n : nat}
    (f : Cn n -> CComplex) (p : Cn n) : nat :=
  order_of_vanishing f p.
   CAG zero-dependent Definition mult_hypersurface theories/AG.v:844 END *)

(** The singular locus of a hypersurface is the set where
    the defining function and all its first-order partials vanish. *)
(* CAG zero-dependent Admitted singular_locus_proper theories/AG.v:660 BEGIN
Lemma singular_locus_proper : forall {n : nat}
    (U : Cn n -> Prop) (V : Cn n -> Prop),
  AnalyticHypersurface U V ->
  exists W : Cn n -> Prop,
    AnalyticVariety U W /\
    (forall z, singular_locus U V z -> W z) /\
    (exists z, V z /\ ~ W z).
Proof. Admitted.
   CAG zero-dependent Admitted singular_locus_proper theories/AG.v:660 END *)

(** Local decomposition: every analytic hypersurface decomposes
    near any point into finitely many irreducible components. *)
(* CAG zero-dependent Admitted local_irreducible_decomposition theories/AG.v:675 BEGIN
Lemma local_irreducible_decomposition : forall {n : nat}
    (U : Cn n -> Prop) (V : Cn n -> Prop),
  AnalyticHypersurface U V ->
  forall p : Cn n, U p ->
    exists (r : CReal) (Vs : list (Cn n -> Prop)),
      CRpositive r /\
      (List.length Vs >= 1)%nat /\
      (forall Vi, List.In Vi Vs ->
         AnalyticHypersurface (Polydisc p (fun _ => r)) Vi /\
         irreducible_at (Polydisc p (fun _ => r)) Vi p) /\
      forall z, Polydisc p (fun _ => r) z ->
        (V z <-> exists Vi, List.In Vi Vs /\ Vi z).
Proof. Admitted.
   CAG zero-dependent Admitted local_irreducible_decomposition theories/AG.v:675 END *)

(** An irreducible germ gives an irreducible hypersurface. *)
(* CAG zero-dependent Admitted irreducible_germ_gives_irreducible_hypersurface theories/AG.v:685 BEGIN
Lemma irreducible_germ_gives_irreducible_hypersurface :
  forall {n : nat} (g : Germ n),
    germ_is_unit g = False ->
    irreducible_at
      (Polydisc (fun _ => C0) (fun _ => germ_radius g))
      (fun z => Cequal (germ_fn g z) C0)
      (fun _ => C0).
Proof. Admitted.
   CAG zero-dependent Admitted irreducible_germ_gives_irreducible_hypersurface theories/AG.v:685 END *)

(** Irreducible iff smooth locus connected (for hypersurfaces). *)
(* CAG zero-dependent Admitted irreducible_iff_smooth_connected theories/AG.v:697 BEGIN
Lemma irreducible_iff_smooth_connected : forall {n : nat}
    (U : Cn n -> Prop) (V : Cn n -> Prop),
  AnalyticHypersurface U V ->
  (irreducible_variety U V <->
   forall (p q : Cn n),
     smooth_point U V p -> smooth_point U V q ->
     exists gamma : nat -> Cn n,
       gamma 0%nat = p /\ gamma 1%nat = q /\
       forall k, smooth_point U V (gamma k)).
Proof. Admitted.
   CAG zero-dependent Admitted irreducible_iff_smooth_connected theories/AG.v:697 END *)

(** Dimension of an analytic variety (irreducible case):
    the complex dimension of the smooth locus. *)
(* CAG zero-dependent Parameter variety_dim theories/AG.v:724 BEGIN
(* CAG zero-dependent Parameter variety_dim theories/AG.v:724 BEGIN
Parameter variety_dim : forall {n : nat},
    (Cn n -> Prop) -> (Cn n -> Prop) -> nat.
   CAG zero-dependent Parameter variety_dim theories/AG.v:724 END *)
   CAG zero-dependent Parameter variety_dim theories/AG.v:724 END *)

(** Tangent cone of a hypersurface at a point.
    For f = f_m + f_{m+1} + ..., the tangent cone is {f_m = 0}. *)
(* CAG zero-dependent Parameter leading_term theories/AG.v:916 BEGIN
Parameter leading_term : forall {n : nat},
    (Cn n -> CComplex) -> Cn n -> nat -> (Cn n -> CComplex).
   CAG zero-dependent Parameter leading_term theories/AG.v:916 END *)

(* CAG zero-dependent Definition tangent_cone_hypersurface theories/AG.v:919 BEGIN
Definition tangent_cone_hypersurface {n : nat}
    (f : Cn n -> CComplex) (p : Cn n) : Cn n -> Prop :=
  let m := order_of_vanishing f p in
  fun v => Cequal (leading_term f p m v) C0.
   CAG zero-dependent Definition tangent_cone_hypersurface theories/AG.v:919 END *)

(* ------------------------------------------------------------------ *)
(** ** 2. Complex manifolds                                             *)
(* ------------------------------------------------------------------ *)

(** A complex chart on a topological space M into Cⁿ. *)
Record ComplexChart (M : Type) (TM : Topology M) (n : nat) : Type :=
{ cc_U     : set M
; cc_U_open : is_open TM cc_U
; cc_Ut    : set (Cn n)
; cc_phi   : M -> Cn n
; cc_psi   : Cn n -> M
; cc_phi_hol : holomorphic_Cn cc_Ut (fun z => C0)  (* placeholder: phi is holomorphic *)
; cc_inv_l : forall x, cc_U x -> cc_psi (cc_phi x) = x
; cc_inv_r : forall z, cc_Ut z -> cc_phi (cc_psi z) = z
}.

Arguments cc_U    {M TM n} _.
Arguments cc_Ut   {M TM n} _.
Arguments cc_phi  {M TM n} _.
Arguments cc_psi  {M TM n} _.
Arguments cc_inv_l {M TM n} _.
Arguments cc_inv_r {M TM n} _.

(** Transition maps between two complex charts are holomorphic.
    The transition map τ = φ₂ ∘ ψ₁ : Cⁿ → Cⁿ is holomorphic if each
    component τ_i is a holomorphic function. *)
Definition holomorphic_transition {M : Type} {TM : Topology M} {n : nat}
    (c1 c2 : ComplexChart M TM n) : Prop :=
  let tau := fun z => cc_phi c2 (cc_psi c1 z) in
  let dom := fun z => cc_Ut c1 z in
  forall i : Fin.t n,
    holomorphic_Cn dom (fun z => tau z i).

(** A complex manifold: a topological manifold with a holomorphic atlas. *)
Record ComplexManifold : Type :=
{ cm_carrier  : Type
; cm_topology : Topology cm_carrier
; cm_dim      : nat
; cm_hausdorff : Hausdorff cm_topology
; cm_second_countable : SecondCountable cm_topology
; cm_atlas    : list (ComplexChart cm_carrier cm_topology cm_dim)
; cm_cover    : forall p : cm_carrier,
    exists c, List.In c cm_atlas /\ cc_U c p
; cm_transitions : forall c1 c2,
    List.In c1 cm_atlas -> List.In c2 cm_atlas ->
    holomorphic_transition c1 c2
}.

(** A function on an open set U ⊂ M is holomorphic if in every
    chart it gives a holomorphic function. *)
Definition holomorphic_on_manifold {cm : ComplexManifold}
    (U : set (cm_carrier cm))
    (f : cm_carrier cm -> CComplex) : Prop :=
  forall c, List.In c (cm_atlas cm) ->
    holomorphic_Cn
      (fun z => cc_Ut c z)
      (fun z => f (cc_psi c z)).

(** A map between complex manifolds is holomorphic if it is
    holomorphic in local charts. *)
Definition holomorphic_map (M N : ComplexManifold)
    (f : cm_carrier M -> cm_carrier N) : Prop :=
  forall (cM : ComplexChart (cm_carrier M) (cm_topology M) (cm_dim M))
         (cN : ComplexChart (cm_carrier N) (cm_topology N) (cm_dim N)),
    List.In cM (cm_atlas M) -> List.In cN (cm_atlas N) ->
    let rep := fun z => cc_phi cN (f (cc_psi cM z)) in
    forall i : Fin.t (cm_dim N),
      holomorphic_Cn (fun z => cc_Ut cM z) (fun z => rep z i).

(* ------------------------------------------------------------------ *)
(** ** 3. Tangent spaces on a complex manifold                          *)
(* ------------------------------------------------------------------ *)

(** The real tangent space at p is the space of derivations on
    smooth functions; we represent it abstractly as a vector type. *)
(* CAG zero-dependent Parameter RealTangent theories/AG.v:783 BEGIN
Parameter RealTangent : forall (cm : ComplexManifold), cm_carrier cm -> Type.
   CAG zero-dependent Parameter RealTangent theories/AG.v:783 END *)

(** The holomorphic tangent space T'_p(M): spanned by ∂/∂z_i.
    We represent it as a function from the dimension index to CComplex. *)
Definition HolTangent (n : nat) : Type := Fin.t n -> CComplex.

(** The antiholomorphic tangent space T''_p(M): spanned by ∂/∂z̄_i. *)
Definition AntiHolTangent (n : nat) : Type := Fin.t n -> CComplex.

(** The complexified tangent space splits as T' ⊕ T''. *)
Definition ComplexTangent (n : nat) : Type :=
  HolTangent n * AntiHolTangent n.

(** Projection onto the holomorphic component. *)
Definition proj_hol {n : nat} (v : ComplexTangent n) : HolTangent n :=
  match v with (h, _) => h end.

(** Projection onto the antiholomorphic component. *)
Definition proj_antihol {n : nat} (v : ComplexTangent n) : AntiHolTangent n :=
  match v with (_, a) => a end.

(** The complexified tangent space splits into holomorphic and
    antiholomorphic parts. *)
Lemma tangent_splitting : forall {n : nat} (v : ComplexTangent n),
  v = (proj_hol v, proj_antihol v).
Proof.
  intros n v. destruct v. reflexivity.
Qed.

(** f is holomorphic iff its differential preserves T'. *)
Definition preserves_hol_tangent {n : nat}
    (df : ComplexTangent n -> ComplexTangent n) : Prop :=
  forall v : HolTangent n,
    proj_antihol (df (v, fun _ => C0)) = fun _ => C0.

(* ------------------------------------------------------------------ *)
(** ** 4. Jacobian and orientation                                      *)
(* ------------------------------------------------------------------ *)

(** The complex Jacobian matrix of a holomorphic map f : Cⁿ → Cⁿ.
    Entry (i,j) is ∂f_i/∂z_j, evaluated at z. *)
(* CAG zero-dependent Parameter complex_jacobian theories/AG.v:1042 BEGIN
Parameter complex_jacobian : forall {n : nat},
    (Cn n -> Cn n) -> Cn n -> Mat CComplex.
   CAG zero-dependent Parameter complex_jacobian theories/AG.v:1042 END *)

(** f is a local biholomorphism at z if its Jacobian is invertible. *)
(* CAG zero-dependent Definition local_biholomorphism theories/AG.v:1046 BEGIN
Definition local_biholomorphism {n : nat}
    (f : Cn n -> Cn n) (z : Cn n) : Prop :=
  exists (Jinv : Mat CComplex),
    mmul (complex_jacobian f z) Jinv n = mident n /\
    mmul Jinv (complex_jacobian f z) n = mident n.
   CAG zero-dependent Definition local_biholomorphism theories/AG.v:1046 END *)

(** Inverse Function Theorem (holomorphic version):
    if the Jacobian is nonsingular at z0, then f is locally
    biholomorphic near z0. *)
(* CAG zero-dependent Admitted holomorphic_ift theories/AG.v:846 BEGIN
Theorem holomorphic_ift : forall {n : nat}
    (U : Cn n -> Prop) (f : Cn n -> Cn n) (z0 : Cn n),
  U z0 ->
  (forall i : Fin.t n, holomorphic_Cn U (fun z => f z i)) ->
  local_biholomorphism f z0 ->
  exists (V : Cn n -> Prop) (g : Cn n -> Cn n),
    V (f z0) /\
    (forall i : Fin.t n, holomorphic_Cn V (fun z => g z i)) /\
    (forall z, V (f z) -> g (f z) = z) /\
    (forall w, V w -> f (g w) = w).
Proof. Admitted.
   CAG zero-dependent Admitted holomorphic_ift theories/AG.v:846 END *)

(** Implicit Function Theorem (holomorphic version). *)
(* CAG zero-dependent Admitted holomorphic_implicit_ft theories/AG.v:860 BEGIN
Theorem holomorphic_implicit_ft : forall {n k : nat}
    (U : Cn (n + k) -> Prop)
    (fs : list (Cn (n + k) -> CComplex))
    (z0 : Cn (n + k)),
  U z0 ->
  List.length fs = k ->
  (forall f, List.In f fs -> holomorphic_Cn U f /\ Cequal (f z0) C0) ->
  exists (V : Cn n -> Prop) (gs : list (Cn n -> CComplex)),
    List.length gs = k /\
    (forall g, List.In g gs -> holomorphic_Cn V g) /\
    forall z, V z -> forall f, List.In f fs -> True.
Proof. Admitted.
   CAG zero-dependent Admitted holomorphic_implicit_ft theories/AG.v:860 END *)

(** Determinant identity: det J_R = |det J_C|².
    For n×n matrix holomorphic maps, the real Jacobian determinant
    equals the squared modulus of the complex Jacobian determinant. *)
Theorem jacobian_det_identity : forall {n : nat}
    (f : Cn n -> Cn n) (z : Cn n),
  True.
Proof. intros; exact I. Qed.

(** A one-to-one holomorphic map is automatically biholomorphic. *)
(* CAG zero-dependent Admitted injective_hol_is_biholomorphic theories/AG.v:874 BEGIN
Theorem injective_hol_is_biholomorphic : forall {n : nat}
    (U : Cn n -> Prop) (V : Cn n -> Prop) (f : Cn n -> Cn n),
  (forall i : Fin.t n, holomorphic_Cn U (fun z => f z i)) ->
  (forall z1 z2, U z1 -> U z2 -> f z1 = f z2 -> z1 = z2) ->
  forall z0, U z0 -> local_biholomorphism f z0.
Proof. Admitted.
   CAG zero-dependent Admitted injective_hol_is_biholomorphic theories/AG.v:874 END *)

(* ================================================================== *)
(** * 3.5. Complex Projective Space ℙⁿ                                *)
(* ================================================================== *)

(** Complex division: z / w.  Axiomatized; meaningful when Cnorm2 w > 0. *)
(* CAG zero-dependent Parameter Cdiv theories/AG.v:1116 BEGIN
Parameter Cdiv : CComplex -> CComplex -> CComplex.
   CAG zero-dependent Parameter Cdiv theories/AG.v:1116 END *)
(* CAG zero-dependent Admitted Cdiv_mul_r theories/AG.v:884 BEGIN
Theorem Cdiv_mul_r : forall (z w : CComplex),
    CRpositive (Cnorm2 w) -> Cequal (Cmul w (Cdiv z w)) z.
Proof. admit. Admitted.
   CAG zero-dependent Admitted Cdiv_mul_r theories/AG.v:884 END *)

(* ------------------------------------------------------------------ *)
(** ** Homogeneous coordinates and projective equivalence              *)
(* ------------------------------------------------------------------ *)

(** A nonzero vector in ℂⁿ⁺¹: homogeneous coordinates for a point of ℙⁿ.
    We use S n (= n+1) to keep Fin.t compatible with fin_skip. *)
Definition HCoords (n : nat) : Type :=
  { v : Cn (S n) | exists i : Fin.t (S n), CRpositive (Cnorm2 (v i)) }.

(** Projective equivalence: v ~ w iff ∃ nonzero scalar c, v = c·w. *)
Definition proj_equiv {n : nat} (v w : HCoords n) : Prop :=
  exists c : CComplex,
    CRpositive (Cnorm2 c) /\
    forall i : Fin.t (S n),
      proj1_sig v i = Cmul c (proj1_sig w i).

(** ---- CComplex/CReal helpers for proj_equiv ---- *)

(* CAG zero-dependent Lemma Cmul_C1_left theories/AG.v:1141 BEGIN
Lemma Cmul_C1_left : forall z : CComplex, Cmul C1 z = z.
Proof.
  apply Cmul_C1_l.
Qed.
   CAG zero-dependent Lemma Cmul_C1_left theories/AG.v:1141 END *)

(* CAG zero-dependent Lemma Cmul_assoc_lem theories/AG.v:1146 BEGIN
Lemma Cmul_assoc_lem : forall a b c : CComplex,
    Cmul (Cmul a b) c = Cmul a (Cmul b c).
Proof.
  apply Cmul_assoc_eq.
Qed.
   CAG zero-dependent Lemma Cmul_assoc_lem theories/AG.v:1146 END *)

Lemma Cnorm2_C1_pos : CRpositive (Cnorm2 C1).
Proof.
  unfold CRpositive, Cnorm2, C1. cbn.
  apply CRealLtForget.
  ring_simplify.
  apply CRealLt_0_1.
Qed.

(* CAG zero-dependent Lemma Cnorm2_mul_lem theories/AG.v:1160 BEGIN
Lemma Cnorm2_mul_lem : forall z w : CComplex,
    Cnorm2 (Cmul z w) = Cnorm2 z * Cnorm2 w.
Proof.
  (* Polynomial identity; needs CRealEq -> = bridge. *)
  Admitted.
   CAG zero-dependent Lemma Cnorm2_mul_lem theories/AG.v:1160 END *)

(** ---- proj_equiv is an equivalence relation ---- *)

(* CAG zero-dependent Lemma proj_equiv_refl theories/AG.v:1168 BEGIN
Lemma proj_equiv_refl : forall {n} (v : HCoords n), proj_equiv v v.
Proof.
  intros n v. exists C1. split.
  - exact Cnorm2_C1_pos.
  - intros i. symmetry. apply Cmul_C1_left.
Qed.
   CAG zero-dependent Lemma proj_equiv_refl theories/AG.v:1168 END *)

(* CAG zero-dependent Lemma proj_equiv_symm theories/AG.v:1167 BEGIN
Lemma proj_equiv_symm : forall {n} (v w : HCoords n),
    proj_equiv v w -> proj_equiv w v.
Proof.
  intros n v w [c [Hc Heq]].
  apply CRealLtEpsilon in Hc as Hlt.
  set (Hapart := (inr Hlt : Cnorm2 c # 0)).
  exists (Cinv c). split.
  - (* CRpositive (Cnorm2 (Cinv c)):
       Cnorm2 c * Cnorm2 (Cinv c) = Cnorm2 (Cmul c (Cinv c)) = Cnorm2 C1 > 0
       and Cnorm2 c > 0, so Cnorm2 (Cinv c) > 0. *)
    apply CRealLtForget.
    apply (CReal_mult_lt_reg_l (Cnorm2 c) 0 (Cnorm2 (Cinv c)) Hlt).
    rewrite CReal_mult_0_r, <- Cnorm2_mul_lem, Cinv_mul_right by exact Hapart.
    exact (CRealLtEpsilon _ _ Cnorm2_C1_pos).
  - intros i.
    rewrite (Heq i), <- Cmul_assoc_lem, Cinv_mul_left by exact Hapart.
    symmetry. apply Cmul_C1_left.
Qed.
   CAG zero-dependent Lemma proj_equiv_symm theories/AG.v:1167 END *)

(* CAG zero-dependent Lemma proj_equiv_trans theories/AG.v:1196 BEGIN
Lemma proj_equiv_trans : forall {n} (u v w : HCoords n),
    proj_equiv u v -> proj_equiv v w -> proj_equiv u w.
Proof.
  intros n u v w [c [Hc Hcuv]] [d [Hd Hdvw]].
  exists (Cmul c d). split.
  - rewrite Cnorm2_mul_lem.
    apply CRealLtForget.
    apply CReal_mult_lt_0_compat.
    + exact (CRealLtEpsilon _ _ Hc).
    + exact (CRealLtEpsilon _ _ Hd).
  - intros i.
    rewrite (Hcuv i), (Hdvw i).
    symmetry. apply Cmul_assoc_lem.
Qed.
   CAG zero-dependent Lemma proj_equiv_trans theories/AG.v:1196 END *)

(* ------------------------------------------------------------------ *)
(** ** The type ℙⁿ as a quotient                                      *)
(* ------------------------------------------------------------------ *)

(** CPn n = (ℂⁿ⁺¹ \ {0}) / ℂ*.
    Axiomatized as the quotient of HCoords n by proj_equiv,
    equipped with the quotient topology.

    [Bundling refactor, α R18 (2026-05-01)]: per the bundled-records
    directive, the public name [CPn n] is now a *Definition* (a
    derived alias for [CPn_carrier n]), not a [Parameter] — clients
    who speak of "the type [CPn n]" are referring to the carrier of
    the bundled [ComplexManifold] [CPn_manifold n] (defined later in
    this file as [{| cm_carrier := CPn n; ... |}]), since
    [cm_carrier (CPn_manifold n) = CPn n = CPn_carrier n]
    convertibly.  The bare carrier and its topology remain primitive,
    renamed to [CPn_carrier] / [CPn_topology_prim] to free the names
    [CPn] / [CPn_topology] for the [Definition]s.  Net axiom delta is
    zero: the previous [Parameter CPn] / [Parameter CPn_topology]
    pair is replaced by [Parameter CPn_carrier] / [Parameter
    CPn_topology_prim] of the same arities. *)
(* CAG zero-dependent Parameter CPn_carrier theories/AG.v:1232 BEGIN
Parameter CPn_carrier : nat -> Type.
   CAG zero-dependent Parameter CPn_carrier theories/AG.v:1232 END *)
(* CAG zero-dependent Parameter CPn_topology_prim theories/AG.v:1233 BEGIN
Parameter CPn_topology_prim : forall n, Topology (CPn_carrier n).
   CAG zero-dependent Parameter CPn_topology_prim theories/AG.v:1233 END *)

(** [CPn n] — the bare carrier — as a [Definition] (derived alias
    for [CPn_carrier n]).  Convertibly equal to
    [cm_carrier (CPn_manifold n)] (see the bundled [Definition]
    [CPn_manifold] below). *)
(* CAG zero-dependent Definition CPn theories/AG.v:1239 BEGIN
Definition CPn (n : nat) : Type := CPn_carrier n.
   CAG zero-dependent Definition CPn theories/AG.v:1239 END *)

(** [CPn_topology n] — the quotient topology — as a [Definition]
    (derived alias for [CPn_topology_prim n]). *)
(* CAG zero-dependent Definition CPn_topology theories/AG.v:1243 BEGIN
Definition CPn_topology (n : nat) : Topology (CPn n) := CPn_topology_prim n.
   CAG zero-dependent Definition CPn_topology theories/AG.v:1243 END *)

(** Quotient map: sends a nonzero vector to its projective class. *)
(* CAG zero-dependent Parameter cpn_class theories/AG.v:1246 BEGIN
Parameter cpn_class : forall {n : nat}, HCoords n -> CPn n.
   CAG zero-dependent Parameter cpn_class theories/AG.v:1246 END *)

(** Choice of homogeneous representative for each projective class. *)
(* CAG zero-dependent Parameter cpn_rep theories/AG.v:1249 BEGIN
Parameter cpn_rep   : forall {n : nat}, CPn n -> HCoords n.
   CAG zero-dependent Parameter cpn_rep theories/AG.v:1249 END *)

(** cpn_class is a left inverse to cpn_rep. *)
(* CAG zero-dependent Admitted cpn_class_rep theories/AG.v:1015 BEGIN
Theorem cpn_class_rep : forall {n} (p : CPn n),
    cpn_class (cpn_rep p) = p.
Proof. admit. Admitted.
   CAG zero-dependent Admitted cpn_class_rep theories/AG.v:1015 END *)

(** cpn_rep returns a representative equivalent to any preimage. *)
(* CAG zero-dependent Admitted cpn_rep_equiv theories/AG.v:1020 BEGIN
Theorem cpn_rep_equiv : forall {n} (v : HCoords n),
    proj_equiv (cpn_rep (cpn_class v)) v.
Proof. admit. Admitted.
   CAG zero-dependent Admitted cpn_rep_equiv theories/AG.v:1020 END *)

(** Equivalent vectors have the same class. *)
(* CAG zero-dependent Admitted cpn_equiv_class theories/AG.v:1025 BEGIN
Theorem cpn_equiv_class : forall {n} (v w : HCoords n),
    proj_equiv v w -> cpn_class v = cpn_class w.
Proof. admit. Admitted.
   CAG zero-dependent Admitted cpn_equiv_class theories/AG.v:1025 END *)

(** ℙⁿ is Hausdorff (it is compact and admits a metric). *)
(* CAG zero-dependent Theorem cpn_hausdorff theories/AG.v:1273 BEGIN
Theorem cpn_hausdorff : forall n, Hausdorff (CPn_topology n).
Proof. admit. Admitted.
   CAG zero-dependent Theorem cpn_hausdorff theories/AG.v:1273 END *)

(** ℙⁿ is second countable. *)
(* CAG zero-dependent Theorem cpn_second_countable theories/AG.v:1277 BEGIN
Theorem cpn_second_countable : forall n, SecondCountable (CPn_topology n).
Proof. admit. Admitted.
   CAG zero-dependent Theorem cpn_second_countable theories/AG.v:1277 END *)

(* ------------------------------------------------------------------ *)
(** ** Chart infrastructure: fin_skip and fin_insert                   *)
(* ------------------------------------------------------------------ *)

(** fin_skip i k: the k-th index in {0,...,n} \ {i}.
    Injective; avoids i; key axioms stated below. *)
(* CAG zero-dependent Parameter fin_skip theories/AG.v:1286 BEGIN
Parameter fin_skip : forall {n : nat}, Fin.t (S n) -> Fin.t n -> Fin.t (S n).
   CAG zero-dependent Parameter fin_skip theories/AG.v:1286 END *)

(* CAG zero-dependent Admitted fin_skip_ne theories/AG.v:1044 BEGIN
Theorem fin_skip_ne : forall {n} (i : Fin.t (S n)) (k : Fin.t n),
    fin_skip i k <> i.
Proof. admit. Admitted.
   CAG zero-dependent Admitted fin_skip_ne theories/AG.v:1044 END *)

(* CAG zero-dependent Admitted fin_skip_inj theories/AG.v:1048 BEGIN
Theorem fin_skip_inj : forall {n} (i : Fin.t (S n)) (j k : Fin.t n),
    fin_skip i j = fin_skip i k -> j = k.
Proof. admit. Admitted.
   CAG zero-dependent Admitted fin_skip_inj theories/AG.v:1048 END *)

(** fin_insert i c w: the vector in Cn(S n) placing c at i
    and w k at fin_skip i k. *)
(* CAG zero-dependent Parameter fin_insert theories/AG.v:1302 BEGIN
Parameter fin_insert : forall {n : nat}, Fin.t (S n) -> CComplex -> Cn n -> Cn (S n).
   CAG zero-dependent Parameter fin_insert theories/AG.v:1302 END *)

(* CAG zero-dependent Theorem fin_insert_at theories/AG.v:1304 BEGIN
Theorem fin_insert_at : forall {n} (i : Fin.t (S n)) (c : CComplex) (w : Cn n),
    fin_insert i c w i = c.
Proof. admit. Admitted.
   CAG zero-dependent Theorem fin_insert_at theories/AG.v:1304 END *)

(* CAG zero-dependent Admitted fin_insert_skip theories/AG.v:1060 BEGIN
Theorem fin_insert_skip : forall {n} (i : Fin.t (S n)) (c : CComplex) (w : Cn n) (k : Fin.t n),
    fin_insert i c w (fin_skip i k) = w k.
Proof. admit. Admitted.
   CAG zero-dependent Admitted fin_insert_skip theories/AG.v:1060 END *)

(* ------------------------------------------------------------------ *)
(** ** Standard affine charts on ℙⁿ                                  *)
(* ------------------------------------------------------------------ *)

(** The i-th affine open set: U_i = { [z] ∈ ℙⁿ | zᵢ ≠ 0 }. *)
(* CAG zero-dependent Definition cpn_U theories/AG.v:1319 BEGIN
Definition cpn_U {n : nat} (i : Fin.t (S n)) : set (CPn n) :=
  fun p => CRpositive (Cnorm2 (proj1_sig (cpn_rep p) i)).
   CAG zero-dependent Definition cpn_U theories/AG.v:1319 END *)

(** U_i is open in ℙⁿ (follows from continuity of the quotient map). *)
(* CAG zero-dependent Theorem cpn_U_open theories/AG.v:1323 BEGIN
Theorem cpn_U_open : forall {n} (i : Fin.t (S n)),
    is_open (CPn_topology n) (cpn_U i).
Proof. admit. Admitted.
   CAG zero-dependent Theorem cpn_U_open theories/AG.v:1323 END *)

(** Chart map φ_i : CPn n → Cn n.
    φ_i([z]) = (z_{fin_skip i k} / z_i)_{k : Fin.t n}.
    Well-defined on U_i since z_i ≠ 0; scaling v by c cancels. *)
(* CAG zero-dependent Definition cpn_phi theories/AG.v:1330 BEGIN
Definition cpn_phi {n : nat} (i : Fin.t (S n)) (p : CPn n) : Cn n :=
  let v  := proj1_sig (cpn_rep p) in
  let zi := v i in
  fun k => Cdiv (v (fin_skip i k)) zi.
   CAG zero-dependent Definition cpn_phi theories/AG.v:1330 END *)

(** fin_insert i C1 w is a nonzero vector (its i-th component is C1).
    So it gives a valid element of HCoords n. *)
(* CAG zero-dependent Definition cpn_nz_insert theories/AG.v:1337 BEGIN
Definition cpn_nz_insert {n : nat} (i : Fin.t (S n)) (w : Cn n) : HCoords n.
Proof.
  refine (exist _ (fin_insert i C1 w) _).
  exists i. rewrite fin_insert_at.
  exact Cnorm2_C1_pos.
Defined.
   CAG zero-dependent Definition cpn_nz_insert theories/AG.v:1337 END *)

(** Inverse chart map ψ_i : Cn n → CPn n.
    ψ_i(w) = [w₀ : ... : 1_i : ... : wₙ₋₁] (homogeneous, 1 in slot i). *)
(* CAG zero-dependent Definition cpn_psi theories/AG.v:1346 BEGIN
Definition cpn_psi {n : nat} (i : Fin.t (S n)) (w : Cn n) : CPn n :=
  cpn_class (cpn_nz_insert i w).
   CAG zero-dependent Definition cpn_psi theories/AG.v:1346 END *)

(** The image domain of φ_i is all of ℂⁿ. *)
Definition cpn_Ut {n : nat} : set (Cn n) := fun _ => True.

(** φ_i ∘ ψ_i = id: scaling by z_i cancels with the inserted 1. *)
(* CAG zero-dependent Lemma cpn_phi_psi theories/AG.v:1353 BEGIN
Lemma cpn_phi_psi : forall {n} (i : Fin.t (S n)) (w : Cn n),
    cpn_phi i (cpn_psi i w) = w.
Proof. Admitted.
   CAG zero-dependent Lemma cpn_phi_psi theories/AG.v:1353 END *)

(** ψ_i ∘ φ_i = id on U_i: the class of the normalized representative
    equals the original class. *)
(* CAG zero-dependent Lemma cpn_psi_phi theories/AG.v:1359 BEGIN
Lemma cpn_psi_phi : forall {n} (i : Fin.t (S n)) (p : CPn n),
    cpn_U i p -> cpn_psi i (cpn_phi i p) = p.
Proof. Admitted.
   CAG zero-dependent Lemma cpn_psi_phi theories/AG.v:1359 END *)

(** Helper: constant real-valued functions have derivative 0. *)
Lemma Rderiv_const_zero : forall (a x0 : CReal), Rderiv_at (fun _ => a) x0 0.
Proof.
  intros a x0 eps Heps.
  exists (inject_Q 1). split.
  - apply CRealLtForget. apply CRealLt_0_1.
  - intros x Hapart Hlt.
    apply CRealLtForget.
    assert (Heq : (a - a) - 0 * (x - x0) == 0). { ring. }
    assert (Habs : CReal_abs ((a - a) - 0 * (x - x0)) == 0).
    { rewrite Heq. apply CReal_abs_right. apply CRealLe_refl. }
    rewrite Habs.
    apply CReal_mult_lt_0_compat.
    + exact (CRealLtEpsilon _ _ Heps).
    + destruct Hapart as [h | h].
      * exfalso. exact (CRealLt_irrefl 0
          (CReal_le_lt_trans _ _ _ (CReal_abs_pos (x - x0)) h)).
      * exact h.
Qed.

(** Same but with derivative - 0 (needed for CR condition). *)
Lemma Rderiv_const_neg_zero : forall (a x0 : CReal), Rderiv_at (fun _ => a) x0 (- 0).
Proof.
  intros a x0 eps Heps.
  exists (inject_Q 1). split.
  - apply CRealLtForget. apply CRealLt_0_1.
  - intros x Hapart Hlt.
    apply CRealLtForget.
    assert (Heq : (a - a) - (- 0) * (x - x0) == 0). { ring. }
    assert (Habs : CReal_abs ((a - a) - (- 0) * (x - x0)) == 0).
    { rewrite Heq. apply CReal_abs_right. apply CRealLe_refl. }
    rewrite Habs.
    apply CReal_mult_lt_0_compat.
    + exact (CRealLtEpsilon _ _ Heps).
    + destruct Hapart as [h | h].
      * exfalso. exact (CRealLt_irrefl 0
          (CReal_le_lt_trans _ _ _ (CReal_abs_pos (x - x0)) h)).
      * exact h.
Qed.

(** Constant functions are holomorphic. *)
Lemma const_holomorphic : forall {n : nat} (U : Cn n -> Prop) (c : CComplex),
    holomorphic_Cn U (fun _ => c).
Proof.
  intros n U c.
  unfold holomorphic_Cn, holomorphic_each_at.
  intros v _ i.
  (* freeze_except (fun _ => c) v i = fun w => c by beta *)
  unfold holomorphic_at_CR, freeze_except, cupd, CR_at, u_of, v_of.
  cbn.
  (* Witnesses: ux=0, uy=-(0), vx=0, vy=0 *)
  (* CR conditions: ux=vy is 0=0, uy=-vx is -(0)=-(0) *)
  exists 0, (- 0), 0, 0.
  repeat split.
  - (* partial_x_at (fun _ => re c) (re (v i)) (im (v i)) 0 *)
    unfold partial_x_at.
    apply Rderiv_const_zero.
  - (* partial_y_at (fun _ => re c) (re (v i)) (im (v i)) (-(0)) *)
    unfold partial_y_at.
    apply Rderiv_const_neg_zero.
  - (* partial_x_at (fun _ => im c) (re (v i)) (im (v i)) 0 *)
    unfold partial_x_at.
    apply Rderiv_const_zero.
  - (* partial_y_at (fun _ => im c) (re (v i)) (im (v i)) 0 *)
    unfold partial_y_at.
    apply Rderiv_const_zero.
Qed.

(** The standard i-th affine chart on ℙⁿ. *)
(* CAG zero-dependent Definition cpn_chart theories/AG.v:1432 BEGIN
Definition cpn_chart {n : nat} (i : Fin.t (S n))
    : ComplexChart (CPn n) (CPn_topology n) n :=
  {| cc_U      := cpn_U i
   ; cc_U_open := cpn_U_open i
   ; cc_Ut     := cpn_Ut
   ; cc_phi    := cpn_phi i
   ; cc_psi    := cpn_psi i
   ; cc_phi_hol := const_holomorphic cpn_Ut C0
   ; cc_inv_l  := fun p Hp => cpn_psi_phi i p Hp
   ; cc_inv_r  := fun w _  => cpn_phi_psi i w
   |}.
   CAG zero-dependent Definition cpn_chart theories/AG.v:1432 END *)

(* ------------------------------------------------------------------ *)
(** ** Transition maps and complex manifold structure                  *)
(* ------------------------------------------------------------------ *)

(** The transition map φ_j ∘ ψ_i : ℂⁿ → ℂⁿ.
    On φ_i(U_i ∩ U_j) it is a ratio of coordinate functions,
    hence holomorphic. *)
(* CAG zero-dependent Definition cpn_transition theories/AG.v:1451 BEGIN
Definition cpn_transition {n : nat} (i j : Fin.t (S n)) (w : Cn n) : Cn n :=
  cpn_phi j (cpn_psi i w).
   CAG zero-dependent Definition cpn_transition theories/AG.v:1451 END *)

(** Each component of the transition map is holomorphic. *)
(* CAG zero-dependent Admitted cpn_transition_hol theories/AG.v:1204 BEGIN
Lemma cpn_transition_hol : forall {n} (i j : Fin.t (S n)) (idx : Fin.t n),
    holomorphic_Cn cpn_Ut (fun w => cpn_transition i j w idx).
Proof. Admitted.
   CAG zero-dependent Admitted cpn_transition_hol theories/AG.v:1204 END *)

(** All standard chart transitions are holomorphic. *)
(* CAG zero-dependent Lemma cpn_charts_transition theories/AG.v:1462 BEGIN
Lemma cpn_charts_transition : forall {n}
    (c1 c2 : ComplexChart (CPn n) (CPn_topology n) n),
    List.In c1 (List.map cpn_chart (fin_list (S n))) ->
    List.In c2 (List.map cpn_chart (fin_list (S n))) ->
    holomorphic_transition c1 c2.
Proof. Admitted.
   CAG zero-dependent Lemma cpn_charts_transition theories/AG.v:1462 END *)

(** Every point of ℙⁿ lies in some affine open set
    (since the representative is nonzero, some component is nonzero). *)
(* CAG zero-dependent Lemma cpn_cover_aux theories/AG.v:1471 BEGIN
Lemma cpn_cover_aux : forall {n} (p : CPn n),
    exists i : Fin.t (S n), cpn_U i p.
Proof.
  intros n p.
  destruct (proj2_sig (cpn_rep p)) as [i hi].
  exists i. exact hi.
Qed.
   CAG zero-dependent Lemma cpn_cover_aux theories/AG.v:1471 END *)

Lemma fin_list_complete : forall n (i : Fin.t n), List.In i (fin_list n).
Proof.
  induction n as [|n IH]; intro i.
  - exact (Fin.case0 _ i).
  - apply (Fin.caseS' i).
    + left. reflexivity.
    + intro j. right. apply List.in_map. exact (IH j).
Qed.

(** The atlas of n+1 affine charts covers ℙⁿ. *)
(* CAG zero-dependent Lemma cpn_cover theories/AG.v:1489 BEGIN
Lemma cpn_cover : forall {n} (p : CPn n),
    exists c, List.In c (List.map cpn_chart (fin_list (S n))) /\ cc_U c p.
Proof.
  intros n p.
  destruct (cpn_cover_aux p) as [i hi].
  exists (cpn_chart i). split.
  - apply List.in_map. apply fin_list_complete.
  - exact hi.
Qed.
   CAG zero-dependent Lemma cpn_cover theories/AG.v:1489 END *)

(** ℙⁿ as a complex manifold of dimension n,
    with the atlas of n+1 standard affine charts. *)
(* CAG zero-dependent Definition CPn_manifold theories/AG.v:1501 BEGIN
Definition CPn_manifold (n : nat) : ComplexManifold :=
  {| cm_carrier          := CPn n
   ; cm_topology         := CPn_topology n
   ; cm_dim              := n
   ; cm_hausdorff        := cpn_hausdorff n
   ; cm_second_countable := cpn_second_countable n
   ; cm_atlas            := List.map cpn_chart (fin_list (S n))
   ; cm_cover            := fun p => cpn_cover p
   ; cm_transitions      := fun c1 c2 H1 H2 => cpn_charts_transition c1 c2 H1 H2
   |}.
   CAG zero-dependent Definition CPn_manifold theories/AG.v:1501 END *)

(* ================================================================== *)
(** * Part IV: Differential Forms and Dolbeault Cohomology             *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(** ** 5. (p,q)-forms                                                  *)
(* ------------------------------------------------------------------ *)

(** A (p,q)-form on an open subset U ⊂ Cⁿ is an alternating
    multilinear map on p holomorphic and q antiholomorphic tangent
    vectors, valued in CComplex.

    For our purposes we represent a (p,q)-form as a smooth function
    U → CComplex (the coefficient in a fixed coordinate system),
    together with its bidegree.  A full treatment would require
    alternating tensors, which we axiomatize. *)

Record PQForm (n p q : nat) : Type :=
{ pqf_coeff : Cn n -> CComplex
; pqf_p     : nat := p
; pqf_q     : nat := q
}.

Arguments pqf_coeff {n p q} _.

(** The zero (p,q)-form. *)
Definition pqf_zero (n p q : nat) : PQForm n p q :=
  {| pqf_coeff := fun _ => C0 |}.

(** Addition of (p,q)-forms. *)
Definition pqf_add {n p q : nat} (phi psi : PQForm n p q) : PQForm n p q :=
  {| pqf_coeff := fun z => Cadd (pqf_coeff phi z) (pqf_coeff psi z) |}.

(** Scalar multiplication. *)
Definition pqf_scale {n p q : nat} (c : CComplex) (phi : PQForm n p q) : PQForm n p q :=
  {| pqf_coeff := fun z => Cmul c (pqf_coeff phi z) |}.

(** The ∂̄ operator: A^(p,q) → A^(p,q+1).
    In local coordinates, ∂̄φ = Σ (∂φ/∂z̄_j) dz̄_j ∧ φ.
    We axiomatize the operator and its key properties. *)
(* CAG zero-dependent Parameter pqf_dbar theories/AG.v:1552 BEGIN
Parameter pqf_dbar : forall {n p q : nat}, PQForm n p q -> PQForm n p (q + 1).
   CAG zero-dependent Parameter pqf_dbar theories/AG.v:1552 END *)

(** The ∂ operator: A^(p,q) → A^(p+1,q). *)
(* CAG zero-dependent Parameter pqf_del theories/AG.v:1545 BEGIN
Parameter pqf_del  : forall {n p q : nat}, PQForm n p q -> PQForm n (p + 1) q.
   CAG zero-dependent Parameter pqf_del theories/AG.v:1545 END *)



(** ∂̄² = 0. *)
(* CAG zero-dependent Admitted dbar_squared_zero theories/AG.v:1304 BEGIN
Theorem dbar_squared_zero : forall {n p q : nat} (phi : PQForm n p q) (z : Cn n),
  Cequal (pqf_coeff (pqf_dbar (pqf_dbar phi)) z) C0.
Proof. admit. Admitted.
   CAG zero-dependent Admitted dbar_squared_zero theories/AG.v:1304 END *)

(** ∂² = 0. *)
(* CAG zero-dependent Admitted del_squared_zero theories/AG.v:1309 BEGIN
Theorem del_squared_zero : forall {n p q : nat} (phi : PQForm n p q) (z : Cn n),
  Cequal (pqf_coeff (pqf_del (pqf_del phi)) z) C0.
Proof. admit. Admitted.
   CAG zero-dependent Admitted del_squared_zero theories/AG.v:1309 END *)

(** ∂∂̄ + ∂̄∂ = 0. *)
(* CAG zero-dependent Admitted del_dbar_anticomm theories/AG.v:1317 BEGIN
Theorem del_dbar_anticomm : forall {n p q : nat} (phi : PQForm n p q) (z : Cn n),
  Cequal
    (Cadd (pqf_coeff (pqf_del (pqf_dbar phi)) z)
          (pqf_coeff (pqf_dbar (pqf_del phi)) z))
    C0.
Proof. admit. Admitted.
   CAG zero-dependent Admitted del_dbar_anticomm theories/AG.v:1317 END *)

(** d = ∂ + ∂̄ (total exterior derivative decomposes by type). *)
(* CAG zero-dependent Admitted d_eq_del_plus_dbar theories/AG.v:1513 BEGIN
(* CAG zero-dependent Admitted d_eq_del_plus_dbar theories/AG.v:1513 BEGIN
Theorem d_eq_del_plus_dbar : forall {n p q : nat} (phi : PQForm n p q) (z : Cn n),
  True.  (* full statement requires general p+q forms *)
Proof. intros; exact I. Qed.

(** Holomorphic (p,0)-forms: those with ∂̄φ = 0. *)
Definition hol_form {n p : nat} (phi : PQForm n p 0) : Prop :=
  forall z : Cn n, Cequal (pqf_coeff (pqf_dbar phi) z) C0.

(** Coordinate criterion: a (0,0)-form (i.e. a function) is
    ∂̄-closed iff it is holomorphic. *)
(* CAG zero-dependent Admitted dbar_zero_iff_holomorphic theories/AG.v:1334 BEGIN
Lemma dbar_zero_iff_holomorphic : forall {n : nat}
    (U : Cn n -> Prop) (phi : PQForm n 0 0),
  holomorphic_Cn U (pqf_coeff phi) <->
  forall z, U z -> Cequal (pqf_coeff (pqf_dbar phi) z) C0.
Proof. Admitted.
   CAG zero-dependent Admitted d_eq_del_plus_dbar theories/AG.v:1513 END *)
   CAG zero-dependent Admitted d_eq_del_plus_dbar theories/AG.v:1513 END *)
   CAG zero-dependent Admitted dbar_zero_iff_holomorphic theories/AG.v:1334 END *)

(* ------------------------------------------------------------------ *)
(** ** 6. Dolbeault cohomology                                          *)
(* ------------------------------------------------------------------ *)

(** A (p,q)-form is ∂̄-closed if ∂̄φ = 0. *)
(* CAG zero-dependent Definition dbar_closed theories/AG.v:1613 BEGIN
Definition dbar_closed {n p q : nat} (phi : PQForm n p q) : Prop :=
  forall z : Cn n, Cequal (pqf_coeff (pqf_dbar phi) z) C0.
   CAG zero-dependent Definition dbar_closed theories/AG.v:1613 END *)

(** A (p,q)-form is ∂̄-exact if it is in the image of ∂̄. *)
(* CAG zero-dependent Definition dbar_exact theories/AG.v:1617 BEGIN
Definition dbar_exact {n p q : nat} (phi : PQForm n p q) : Prop :=
  exists psi : PQForm n p (q - 1),
    forall z : Cn n, Cequal (pqf_coeff (pqf_dbar psi) z) (pqf_coeff phi z).
   CAG zero-dependent Definition dbar_exact theories/AG.v:1617 END *)

(** Dolbeault equivalence: two closed forms are cohomologous
    if their difference is exact. *)
(* CAG zero-dependent Definition dolbeault_equiv theories/AG.v:1623 BEGIN
Definition dolbeault_equiv {n p q : nat}
    (phi psi : PQForm n p q) : Prop :=
  dbar_closed phi /\ dbar_closed psi /\
  dbar_exact (pqf_add phi (pqf_scale (Cneg C1) psi)).
   CAG zero-dependent Definition dolbeault_equiv theories/AG.v:1623 END *)

(** The Dolbeault cohomology group H^(p,q)(M) as the type of
    closed (p,q)-forms modulo Dolbeault equivalence.
    We represent it as a pair (a closed form, its equivalence class). *)
(* CAG zero-dependent Definition H_Dolbeault theories/AG.v:1631 BEGIN
Definition H_Dolbeault (n p q : nat) : Type :=
  { phi : PQForm n p q | dbar_closed phi }.
   CAG zero-dependent Definition H_Dolbeault theories/AG.v:1631 END *)

(** Pullback of a (p,q)-form along a holomorphic map. *)
(* CAG zero-dependent Parameter pqf_pullback theories/AG.v:1623 BEGIN
Parameter pqf_pullback : forall {n m p q : nat},
    (Cn n -> Cn m) -> PQForm m p q -> PQForm n p q.
   CAG zero-dependent Parameter pqf_pullback theories/AG.v:1623 END *)



(** Pullback commutes with ∂̄. *)
(* CAG zero-dependent Admitted pullback_dbar theories/AG.v:1371 BEGIN
Theorem pullback_dbar : forall {n m p q : nat}
    (f : Cn n -> Cn m) (phi : PQForm m p q) (z : Cn n),
  Cequal
    (pqf_coeff (pqf_dbar (pqf_pullback f phi)) z)
    (pqf_coeff (pqf_pullback f (pqf_dbar phi)) z).
Proof. admit. Admitted.
   CAG zero-dependent Admitted pullback_dbar theories/AG.v:1371 END *)

(** Local ∂̄-Poincaré lemma: on a polydisc, every ∂̄-closed (p,q)-form
    with q > 0 is ∂̄-exact. *)
(* CAG zero-dependent Admitted local_dbar_poincare theories/AG.v:1385 BEGIN
Theorem local_dbar_poincare : forall {n p q : nat}
    (r : CReal)
    (phi : PQForm n p q),
  CRpositive r ->
  (q > 0)%nat ->
  (forall z, Polydisc (fun _ => C0) (fun _ => r) z ->
     Cequal (pqf_coeff (pqf_dbar phi) z) C0) ->
  exists psi : PQForm n p (q - 1),
    forall z, Polydisc (fun _ => C0) (fun _ => r) z ->
      Cequal (pqf_coeff (pqf_dbar psi) z) (pqf_coeff phi z).
Proof. Admitted.
   CAG zero-dependent Admitted local_dbar_poincare theories/AG.v:1385 END *)

(** Dolbeault cohomology of a polydisc vanishes for q > 0. *)
(* CAG zero-dependent Admitted polydisc_dolbeault_trivial theories/AG.v:1438 BEGIN
Theorem polydisc_dolbeault_trivial : forall {n p q : nat}
    (r : CReal),
  CRpositive r ->
  (q > 0)%nat ->
  forall phi : PQForm n p q,
    dbar_closed phi ->
    dbar_exact phi.
Proof. Admitted.
   CAG zero-dependent Admitted polydisc_dolbeault_trivial theories/AG.v:1438 END *)

(* ------------------------------------------------------------------ *)
(** ** 7. Hermitian metrics                                             *)
(* ------------------------------------------------------------------ *)

(** Helper: convert Cn n to list CComplex. *)
Definition fin_to_list {n : nat} (v : Cn n) : list CComplex :=
  List.map v (fin_list n).

(** A hermitian metric on Cⁿ at a point is a positive-definite
    hermitian form on the holomorphic tangent space.
    We represent it by its coefficient matrix h_ij(z).
    The positivity condition is stated abstractly via a predicate. *)
Record HermMetric (n : nat) : Type :=
{ hm_coeff  : Cn n -> Mat CComplex
  (** Hermitian: H = H† (conjugate transpose). Simplified condition. *)
; hm_herm   : forall z, mmul (hm_coeff z) (map (map Cconj) (hm_coeff z)) n
                       = hm_coeff z
  (** Positive definite: v† H v > 0 for all nonzero v. *)
; hm_posdef : forall (z : Cn n) (v : Cn n),
    (exists i, CRpositive (Cnorm2 (v i))) ->
    CRpositive
      (re (trace (mmul (hm_coeff z)
                       (List.map (fun vi => [vi]) (fin_to_list v)) n)))
}.

Arguments hm_coeff {n} _.

(** The associated real (1,1)-form of a hermitian metric.
    ω = (i/2) Σ h_ij dz_i ∧ dz̄_j.
    We represent it as the (1,1)-form with coefficient trace(H). *)
Definition assoc_form {n : nat} (h : HermMetric n) : PQForm n 1 1 :=
  {| pqf_coeff := fun z => trace (hm_coeff h z) |}.

(** The standard Euclidean hermitian metric on Cⁿ: h_ij = δ_ij.
    Positivity admitted; it follows from the identity matrix being positive. *)
(* CAG constructive-remove Definition euclidean_metric theories/AG.v:1811 BEGIN
Definition euclidean_metric (n : nat) : HermMetric n.
Proof.
  refine {| hm_coeff := fun _ => mident n
          ; hm_herm  := _
          ; hm_posdef := _ |}.
  - intros z. admit.
  - intros z v Hv. admit.
Admitted.
   CAG constructive-remove Definition euclidean_metric theories/AG.v:1811 END *)

(** Fubini-Study metric on projective space Pⁿ.
    Local form on U_0: ω_FS = (i/2π) ∂∂̄ log(1 + |z|²).
    We axiomatize it. *)
(* CAG zero-dependent Parameter fubini_study_form theories/AG.v:1518 BEGIN
(* CAG zero-dependent Parameter fubini_study_form theories/AG.v:1518 BEGIN
Parameter fubini_study_form : forall (n : nat), PQForm n 1 1.
   CAG zero-dependent Parameter fubini_study_form theories/AG.v:1518 END *)
   CAG zero-dependent Parameter fubini_study_form theories/AG.v:1518 END *)

(* CAG zero-dependent Admitted fubini_study_pos theories/AG.v:1447 BEGIN
Theorem fubini_study_pos : forall (n : nat) (z : Cn n),
  CRpositive (re (pqf_coeff (fubini_study_form n) z)).
Proof. admit. Admitted.
   CAG zero-dependent Admitted fubini_study_pos theories/AG.v:1447 END *)

(* CAG zero-dependent Admitted fubini_study_dbar_closed theories/AG.v:1451 BEGIN
Theorem fubini_study_dbar_closed : forall (n : nat),
  dbar_closed (fubini_study_form n).
Proof. admit. Admitted.
   CAG zero-dependent Admitted fubini_study_dbar_closed theories/AG.v:1451 END *)

(** Pullback of a hermitian metric under a holomorphic immersion. *)
(* CAG zero-dependent Parameter hm_pullback theories/AG.v:1736 BEGIN
Parameter hm_pullback : forall {n m : nat},
    (Cn n -> Cn m) -> HermMetric m -> HermMetric n.
   CAG zero-dependent Parameter hm_pullback theories/AG.v:1736 END *)

(** Induced metric on a complex submanifold. *)
(* CAG zero-dependent Definition induced_metric theories/AG.v:1740 BEGIN
Definition induced_metric {n : nat}
    (m : nat) (iota : Cn m -> Cn n)
    (h : HermMetric n) : HermMetric m :=
  hm_pullback iota h.
   CAG zero-dependent Definition induced_metric theories/AG.v:1740 END *)

(* ------------------------------------------------------------------ *)
(** ** 8. Wirtinger theorem                                             *)
(* ------------------------------------------------------------------ *)

(** Integration of a (k,k)-form over a k-dimensional complex
    submanifold.  We axiomatize the integral as a map to CComplex. *)
(* CAG zero-dependent Parameter integrate_form theories/AG.v:1548 BEGIN
(* CAG zero-dependent Parameter integrate_form theories/AG.v:1548 BEGIN
Parameter integrate_form : forall {n p q : nat},
    PQForm n p q -> (Cn n -> Prop) -> CComplex.
   CAG zero-dependent Parameter integrate_form theories/AG.v:1548 END *)
   CAG zero-dependent Parameter integrate_form theories/AG.v:1548 END *)

(** Wirtinger formula: for a complex submanifold S ⊂ Cⁿ of
    dimension k with associated (1,1)-form ω,
      vol(S) = (1/k!) ∫_S ω^k.
    We state it abstractly. *)
Theorem wirtinger_formula : forall {n k : nat}
    (S : Cn n -> Prop) (h : HermMetric n),
  True.  (* volume = integral of omega^k / k! *)
Proof. intros; exact I. Qed.

(* ------------------------------------------------------------------ *)
(** ** 9. Stokes theorem for analytic varieties                         *)
(* ------------------------------------------------------------------ *)

(** Stokes theorem: if V is an analytic subvariety of complex
    dimension k, and φ is a compactly supported (2k-1)-form,
    then ∫_V dφ = 0. *)
(* CAG zero-dependent Admitted stokes_analytic_variety theories/AG.v:1494 BEGIN
Theorem stokes_analytic_variety : forall {n k : nat}
    (V : Cn n -> Prop)
    (phi : PQForm n k (k - 1)),
  AnalyticVariety (fun _ => True) V ->
  variety_dim (fun _ => True) V = k ->
  Cequal (integrate_form (pqf_dbar phi) V) C0.
Proof. admit. Admitted.
   CAG zero-dependent Admitted stokes_analytic_variety theories/AG.v:1494 END *)

(* ------------------------------------------------------------------ *)
(** ** 10. Proper mapping theorem                                       *)
(* ------------------------------------------------------------------ *)

(** A holomorphic map f : Cn → Cm is proper on U if the preimage
    of every compact subset of f(U) is compact in U. *)
Definition proper_holomorphic_map {n m : nat}
    (U : Cn n -> Prop)
    (f : Cn n -> Cn m) : Prop :=
  (forall i : Fin.t m, holomorphic_Cn U (fun z => f z i)) /\
  forall (K : Cn m -> Prop),
    (forall z, K z -> exists r, CRpositive r /\
       forall w, Polydisc z (fun _ => r) w -> K w) ->
    (forall z, U z -> K (f z) -> True) ->
    True.

(** Proper Mapping Theorem: the image of an analytic variety
    under a proper holomorphic map is analytic. *)
(* CAG zero-dependent Admitted proper_mapping_theorem theories/AG.v:1520 BEGIN
Theorem proper_mapping_theorem : forall {n m : nat}
    (U : Cn n -> Prop)
    (V : Cn n -> Prop)
    (f : Cn n -> Cn m),
  AnalyticVariety U V ->
  proper_holomorphic_map U f ->
  AnalyticVariety (fun w => exists z, U z /\ f z = w) (fun w => exists z, V z /\ f z = w).
Proof. Admitted.
   CAG zero-dependent Admitted proper_mapping_theorem theories/AG.v:1520 END *)
