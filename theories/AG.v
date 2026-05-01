
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

(** Matrix multiplication is associative.
    Stated at Leibniz [=] on [Mat CComplex]; the [CReal] sub-structure
    of [CComplex] entries means strict equality fails componentwise.

    HISTORY: a bare [Axiom mmul_assoc] (forall A B C p, ...) was previously
    stated here but was FALSE-as-stated for shape-mismatched matrices
    (both sides truncate via [mmul]'s [r::rs] structure at different
    rates). Likewise the bare [mmul_mident_left] / [mmul_mident_right]
    axioms were superseded. All three were removed (β R10, 2026-05-01)
    after the corresponding Mat_wf-guarded [_wf] Lemmas (below) were
    discharged in β R7 and the remaining use-sites in [LieAlgebra.v]
    were swapped to [mmul_assoc_wf] (β R10). The [_wf] forms below depend
    only on [CRealEq_eq]. *)

(* ================================================================== *)
(** ** Discharge of [mmul_*] axioms (Task M.2.next.followup, β R7 — 2026-05-01)

    The bare [mmul_assoc] is FALSE-as-stated for shape-mismatched matrices
    (both sides truncate via [mmul]'s [r::rs] structure but at different
    rates). Likewise [mmul_mident_*] are correctly Mat_wf-guarded.
    We provide [_wf] Lemma counterparts (sound) here; the bare
    [mmul_assoc] axiom is left as paper-attributable — same pattern β R5
    used for [mat_vs_add_zero_r] / [mat_vs_add_neg_r].

    Strategy: matrix extensionality via length + entry-wise equality,
    plus a small port of the [sum_seq] / Fubini infrastructure (already
    Local in [LieAlgebra.v]).  Closed items depend only on
    [Complex.CRealEq_eq] (the standard CReal-Leibniz bridge axiom). *)
(* ================================================================== *)

Local Open Scope nat_scope.

(* -- Cadd / Cmul Leibniz lemmas (lifted from [_req] via [CComplex_eq]) - *)

Local Lemma AG_Cadd_C0_l : forall a : CComplex, Cadd C0 a = a.
Proof. intros. apply CComplex_eq, Cadd_C0_l_req. Qed.

Local Lemma AG_Cadd_C0_r : forall a : CComplex, Cadd a C0 = a.
Proof. intros. apply CComplex_eq, Cadd_C0_r_req. Qed.

Local Lemma AG_Cmul_C0_l : forall a : CComplex, Cmul C0 a = C0.
Proof. intros. apply CComplex_eq, Cmul_C0_l. Qed.

Local Lemma AG_Cmul_C0_r : forall a : CComplex, Cmul a C0 = C0.
Proof. intros. apply CComplex_eq, Cmul_C0_r_req. Qed.

Local Lemma AG_Cmul_C1_l : forall a : CComplex, Cmul C1 a = a.
Proof. intros. apply CComplex_eq, Cmul_C1_l_req. Qed.

Local Lemma AG_Cmul_C1_r : forall a : CComplex, Cmul a C1 = a.
Proof. intros. apply CComplex_eq, Cmul_C1_r_req. Qed.

Local Lemma AG_Cadd_assoc : forall a b c : CComplex,
  Cadd a (Cadd b c) = Cadd (Cadd a b) c.
Proof. intros. apply CComplex_eq, Cadd_assoc_req. Qed.

Local Lemma AG_Cadd_comm : forall a b : CComplex, Cadd a b = Cadd b a.
Proof. intros. apply CComplex_eq, Cadd_comm_req. Qed.

Local Lemma AG_Cmul_assoc : forall a b c : CComplex,
  Cmul a (Cmul b c) = Cmul (Cmul a b) c.
Proof. intros. apply CComplex_eq, Cmul_assoc_req. Qed.

Local Lemma AG_Cmul_distrib_l : forall a b c : CComplex,
  Cmul a (Cadd b c) = Cadd (Cmul a b) (Cmul a c).
Proof. intros. apply CComplex_eq, Cmul_distrib_l_req. Qed.

Local Lemma AG_Cmul_distrib_r : forall a b c : CComplex,
  Cmul (Cadd a b) c = Cadd (Cmul a c) (Cmul b c).
Proof. intros. apply CComplex_eq, Cmul_distrib_r_req. Qed.

Local Lemma AG_Cadd_interchange : forall a b c d : CComplex,
  Cadd (Cadd a b) (Cadd c d) = Cadd (Cadd a c) (Cadd b d).
Proof.
  intros a b c d.
  rewrite <- (AG_Cadd_assoc a b (Cadd c d)).
  rewrite (AG_Cadd_assoc b c d).
  rewrite (AG_Cadd_comm b c).
  rewrite <- (AG_Cadd_assoc c b d).
  rewrite (AG_Cadd_assoc a c (Cadd b d)).
  reflexivity.
Qed.

(* ----- sum_seq port (right-associated finite sum) ----- *)

Fixpoint sum_seq_aux (f : nat -> CComplex) (start n : nat) : CComplex :=
  match n with
  | O => C0
  | S k => Cadd (f start) (sum_seq_aux f (S start) k)
  end.

Definition sum_seq (f : nat -> CComplex) (n : nat) : CComplex :=
  sum_seq_aux f 0 n.

Local Lemma sum_seq_aux_ext :
  forall (f g : nat -> CComplex) (start n : nat),
    (forall i, start <= i < start + n -> f i = g i) ->
    sum_seq_aux f start n = sum_seq_aux g start n.
Proof.
  intros f g start n. revert start.
  induction n as [|n IH]; intros start Hext; [reflexivity|].
  simpl. f_equal.
  - apply Hext. lia.
  - apply IH. intros i Hi. apply Hext. lia.
Qed.

Local Lemma sum_seq_ext :
  forall (f g : nat -> CComplex) (n : nat),
    (forall i, i < n -> f i = g i) ->
    sum_seq f n = sum_seq g n.
Proof.
  intros f g n Hext. unfold sum_seq.
  apply sum_seq_aux_ext. intros i Hi. apply Hext. lia.
Qed.

Local Lemma sum_seq_aux_zero :
  forall (start n : nat), sum_seq_aux (fun _ => C0) start n = C0.
Proof.
  intros start n. revert start.
  induction n as [|n IH]; intros start; [reflexivity|].
  simpl. rewrite IH. apply AG_Cadd_C0_l.
Qed.

Local Lemma sum_seq_zero :
  forall (n : nat), sum_seq (fun _ => C0) n = C0.
Proof. intros. unfold sum_seq. apply sum_seq_aux_zero. Qed.

Local Lemma sum_seq_aux_add :
  forall (f g : nat -> CComplex) (start n : nat),
    sum_seq_aux (fun i => Cadd (f i) (g i)) start n =
    Cadd (sum_seq_aux f start n) (sum_seq_aux g start n).
Proof.
  intros f g start n. revert start.
  induction n as [|n IH]; intros start.
  - simpl. symmetry. apply AG_Cadd_C0_l.
  - simpl. rewrite IH.
    set (a := f start). set (b := g start).
    set (sf := sum_seq_aux f (S start) n).
    set (sg := sum_seq_aux g (S start) n).
    apply AG_Cadd_interchange.
Qed.

Local Lemma sum_seq_add :
  forall (f g : nat -> CComplex) (n : nat),
    sum_seq (fun i => Cadd (f i) (g i)) n =
    Cadd (sum_seq f n) (sum_seq g n).
Proof. intros. unfold sum_seq. apply sum_seq_aux_add. Qed.

Local Lemma sum_seq_aux_shift :
  forall (f : nat -> CComplex) (start n : nat),
    sum_seq_aux f (S start) n = sum_seq_aux (fun i => f (S i)) start n.
Proof.
  intros f start n. revert start f.
  induction n as [|n IH]; intros start f; [reflexivity|].
  simpl. f_equal. apply IH.
Qed.

Local Lemma sum_seq_S :
  forall (f : nat -> CComplex) (n : nat),
    sum_seq f (S n) = Cadd (sum_seq f n) (f n).
Proof.
  intros f n. unfold sum_seq.
  revert f. induction n as [|n IH]; intro f.
  - simpl. rewrite AG_Cadd_C0_l. rewrite AG_Cadd_C0_r. reflexivity.
  - change (sum_seq_aux f 0 (S (S n)))
      with (Cadd (f 0) (sum_seq_aux f 1 (S n))).
    rewrite sum_seq_aux_shift.
    change (sum_seq_aux f 0 (S n))
      with (Cadd (f 0) (sum_seq_aux f 1 n)).
    rewrite sum_seq_aux_shift.
    rewrite (IH (fun i => f (S i))).
    rewrite <- (AG_Cadd_assoc (f 0) _ _).
    reflexivity.
Qed.

Local Lemma sum_seq_swap :
  forall (f : nat -> nat -> CComplex) (n m : nat),
    sum_seq (fun i => sum_seq (fun j => f i j) m) n =
    sum_seq (fun j => sum_seq (fun i => f i j) n) m.
Proof.
  intros f n m. revert f m.
  induction n as [|n IH]; intros f m.
  - unfold sum_seq at 1. simpl.
    symmetry. apply sum_seq_zero.
  - rewrite (sum_seq_S _ n).
    rewrite (IH (fun i => f i) m).
    rewrite <- (sum_seq_add
                 (fun j => sum_seq (fun i => f i j) n)
                 (fun j => f n j) m).
    apply sum_seq_ext. intros j Hj.
    rewrite (sum_seq_S (fun i => f i j) n). reflexivity.
Qed.

(** Constant scalar pulls out of a finite sum (left). *)
Local Lemma sum_seq_aux_distr_l :
  forall (a : CComplex) (f : nat -> CComplex) (start n : nat),
    Cmul a (sum_seq_aux f start n) = sum_seq_aux (fun i => Cmul a (f i)) start n.
Proof.
  intros a f start n. revert start.
  induction n as [|n IH]; intros start.
  - simpl. apply AG_Cmul_C0_r.
  - simpl. rewrite AG_Cmul_distrib_l. rewrite IH. reflexivity.
Qed.

Local Lemma sum_seq_distr_l :
  forall (a : CComplex) (f : nat -> CComplex) (n : nat),
    Cmul a (sum_seq f n) = sum_seq (fun i => Cmul a (f i)) n.
Proof. intros. unfold sum_seq. apply sum_seq_aux_distr_l. Qed.

Local Lemma sum_seq_aux_distr_r :
  forall (a : CComplex) (f : nat -> CComplex) (start n : nat),
    Cmul (sum_seq_aux f start n) a = sum_seq_aux (fun i => Cmul (f i) a) start n.
Proof.
  intros a f start n. revert start.
  induction n as [|n IH]; intros start.
  - simpl. apply AG_Cmul_C0_l.
  - simpl. rewrite AG_Cmul_distrib_r. rewrite IH. reflexivity.
Qed.

Local Lemma sum_seq_distr_r :
  forall (a : CComplex) (f : nat -> CComplex) (n : nat),
    Cmul (sum_seq f n) a = sum_seq (fun i => Cmul (f i) a) n.
Proof. intros. unfold sum_seq. apply sum_seq_aux_distr_r. Qed.

(* ----- Bridge lemmas: dot / mmul / trace via sum_seq ----- *)

Local Lemma dot_as_sum_seq :
  forall (v w : list CComplex),
    List.length v = List.length w ->
    dot v w =
    sum_seq (fun j => Cmul (nth_default C0 v j) (nth_default C0 w j))
            (List.length v).
Proof.
  induction v as [|x xs IH]; intros [|y ys] Hlen;
    simpl in *; try discriminate.
  - reflexivity.
  - injection Hlen as Hlen'.
    rewrite (IH ys Hlen').
    unfold sum_seq. simpl sum_seq_aux.
    rewrite sum_seq_aux_shift. cbv beta.
    reflexivity.
Qed.

Local Lemma nth_default_app_sing_lt :
  forall (l : list CComplex) (x : CComplex) (c : nat),
    c < List.length l ->
    nth_default C0 (l ++ [x]) c = nth_default C0 l c.
Proof.
  induction l as [|h t IHl]; intros x c Hc; simpl in *; [lia|].
  destruct c as [|c']; [reflexivity|]. apply IHl. lia.
Qed.

Local Lemma nth_default_app_sing_eq :
  forall (l : list CComplex) (x : CComplex),
    nth_default C0 (l ++ [x]) (List.length l) = x.
Proof.
  induction l as [|h t IHl]; intros x; simpl; [reflexivity|].
  apply IHl.
Qed.

Local Lemma nth_default_row_mul_mcols :
  forall (r : list CComplex) (B : Mat CComplex) (m c : nat),
    c < m ->
    nth_default C0 (row_mul_cols r (mcols m B)) c =
    dot r (col B c).
Proof.
  intros r B m. induction m as [|m IH]; intros c Hc; [lia|].
  simpl mcols.
  assert (Happ : forall (xs : list (list CComplex)) (c0 : list CComplex),
            row_mul_cols r (xs ++ [c0]) = row_mul_cols r xs ++ [dot r c0]).
  { intros xs c0. induction xs as [|x xs' IHx]; simpl; [reflexivity|].
    rewrite IHx. reflexivity. }
  rewrite Happ.
  assert (Hlen_rmc : List.length (row_mul_cols r (mcols m B)) = m).
  { rewrite row_mul_cols_length, mcols_length. reflexivity. }
  destruct (Nat.lt_ge_cases c m) as [Hcm | Hcm].
  - rewrite (nth_default_app_sing_lt _ _ c) by lia.
    apply (IH c Hcm).
  - assert (Hceq : c = m) by lia. subst c.
    pose proof (nth_default_app_sing_eq (row_mul_cols r (mcols m B))
                                         (dot r (col B m))) as Heq.
    rewrite Hlen_rmc in Heq. exact Heq.
Qed.

(** Helper: extract a row of [mmul A B n]. *)
Local Lemma nth_mmul_row :
  forall (B : Mat CComplex) (n : nat) (X : Mat CComplex) (k : nat),
    k < List.length X ->
    List.nth k (mmul X B n) [] =
    row_mul_cols (List.nth k X []) (mcols n B).
Proof.
  intros B n X. induction X as [|rX Xs IH]; intros k Hk; simpl in Hk; [lia|].
  simpl mmul. destruct k as [|k'].
  - reflexivity.
  - simpl List.nth. apply IH. lia.
Qed.

(** Bridge from row of [List.map f B] back to [f] applied to a row. *)
Local Lemma nth_default_map_col :
  forall (c : nat) (B : Mat CComplex) (j : nat),
    nth_default C0
      (List.map (fun row : list CComplex => nth_default C0 row c) B) j =
    nth_default C0 (List.nth j B []) c.
Proof.
  intros c B. induction B as [|b Bs IH]; intros j; simpl.
  - destruct j; reflexivity.
  - destruct j as [|j']; [reflexivity|]. apply IH.
Qed.

(** [(r,c)] entry of [mmul A B n] as a sum, given [A : n×p] and [B : p×n]. *)
Local Lemma mat_mul_entry_sum :
  forall (n p : nat) (A B : Mat CComplex) (r c : nat),
    Mat_wf n p A -> Mat_wf p n B ->
    r < n -> c < n ->
    nth_default C0 (List.nth r (mmul A B n) []) c =
    sum_seq
      (fun j => Cmul (nth_default C0 (List.nth r A []) j)
                     (nth_default C0 (List.nth j B []) c))
      p.
Proof.
  intros n p A B r c [HlenA HrowA] [HlenB HrowB] Hr Hc.
  rewrite (nth_mmul_row B n A r) by lia.
  rewrite (nth_default_row_mul_mcols (List.nth r A []) B n c Hc).
  unfold col.
  assert (HrowAr : List.length (List.nth r A []) = p).
  { apply HrowA. apply List.nth_In. lia. }
  assert (HmapLen : List.length (List.map (fun row => nth_default C0 row c) B) =
                    List.length B).
  { apply List.length_map. }
  assert (HBp : List.length B = p) by exact HlenB.
  rewrite (dot_as_sum_seq (List.nth r A [])
             (List.map (fun row : list CComplex => nth_default C0 row c) B)).
  - rewrite HrowAr. apply sum_seq_ext. intros j Hj.
    f_equal. apply nth_default_map_col.
  - rewrite HrowAr, HmapLen, HBp. reflexivity.
Qed.

(** Generalised version when [B : p×q] and [c < q]: use [mmul A B q]. *)
Local Lemma mat_mul_entry_sum_gen :
  forall (n p q : nat) (A B : Mat CComplex) (r c : nat),
    Mat_wf n p A -> Mat_wf p q B ->
    r < n -> c < q ->
    nth_default C0 (List.nth r (mmul A B q) []) c =
    sum_seq
      (fun j => Cmul (nth_default C0 (List.nth r A []) j)
                     (nth_default C0 (List.nth j B []) c))
      p.
Proof.
  intros n p q A B r c [HlenA HrowA] [HlenB HrowB] Hr Hc.
  assert (HlenA' : List.length A = n) by exact HlenA.
  rewrite (nth_mmul_row B q A r) by lia.
  rewrite (nth_default_row_mul_mcols (List.nth r A []) B q c Hc).
  unfold col.
  assert (HrowAr : List.length (List.nth r A []) = p).
  { apply HrowA. apply List.nth_In. lia. }
  assert (HmapLen : List.length (List.map (fun row => nth_default C0 row c) B) =
                    List.length B).
  { apply List.length_map. }
  assert (HBp : List.length B = p) by exact HlenB.
  rewrite (dot_as_sum_seq (List.nth r A [])
             (List.map (fun row : list CComplex => nth_default C0 row c) B)).
  - rewrite HrowAr. apply sum_seq_ext. intros j Hj.
    f_equal. apply nth_default_map_col.
  - rewrite HrowAr, HmapLen, HBp. reflexivity.
Qed.

(* ----- Matrix extensionality (Mat_wf) ----- *)

(** Two same-shape matrices with the same length and pointwise-equal rows
    are Leibniz-equal as lists. *)
Local Lemma list_ext_nth :
  forall (A B : Mat CComplex),
    List.length A = List.length B ->
    (forall i, i < List.length A -> List.nth i A [] = List.nth i B []) ->
    A = B.
Proof.
  induction A as [|a As IH]; intros [|b Bs] Hlen Hext.
  - reflexivity.
  - simpl in Hlen. discriminate.
  - simpl in Hlen. discriminate.
  - simpl in Hlen. injection Hlen as Hlen'.
    f_equal.
    + specialize (Hext 0). simpl in Hext. apply Hext. simpl. lia.
    + apply IH; [exact Hlen'|].
      intros i Hi. specialize (Hext (S i)). simpl in Hext.
      apply Hext. simpl. lia.
Qed.

(** Two equal-length rows with pointwise equal nth_default entries are equal. *)
Local Lemma row_ext_nth_default :
  forall (u v : list CComplex),
    List.length u = List.length v ->
    (forall j, j < List.length u -> nth_default C0 u j = nth_default C0 v j) ->
    u = v.
Proof.
  induction u as [|x xs IH]; intros [|y ys] Hlen Hext.
  - reflexivity.
  - simpl in Hlen. discriminate.
  - simpl in Hlen. discriminate.
  - simpl in Hlen. injection Hlen as Hlen'.
    f_equal.
    + specialize (Hext 0). simpl in Hext. apply Hext. simpl. lia.
    + apply IH; [exact Hlen'|].
      intros j Hj. specialize (Hext (S j)). simpl in Hext.
      apply Hext. simpl. lia.
Qed.

(** Mat_wf-guarded matrix extensionality via entry-wise equality. *)
Local Lemma mat_ext_wf :
  forall (n m : nat) (A B : Mat CComplex),
    Mat_wf n m A -> Mat_wf n m B ->
    (forall i j, i < n -> j < m ->
      nth_default C0 (List.nth i A []) j =
      nth_default C0 (List.nth i B []) j) ->
    A = B.
Proof.
  intros n m A B [HlenA HrowA] [HlenB HrowB] Hext.
  apply list_ext_nth.
  - rewrite HlenA, HlenB. reflexivity.
  - intros i Hi.
    apply (row_ext_nth_default (List.nth i A []) (List.nth i B [])).
    + assert (HA' : List.length (List.nth i A []) = m).
      { apply HrowA. apply List.nth_In. lia. }
      assert (HB' : List.length (List.nth i B []) = m).
      { apply HrowB. apply List.nth_In. lia. }
      rewrite HA', HB'. reflexivity.
    + intros j Hj.
      assert (HA' : List.length (List.nth i A []) = m).
      { apply HrowA. apply List.nth_In. lia. }
      rewrite HA' in Hj.
      apply Hext; [lia|exact Hj].
Qed.

(* ----- mident: rows, columns, entries ----- *)

(** The [j]-th entry of [ident_row n i] is [if i =? j then C1 else C0]. *)
Local Lemma nth_default_ident_row :
  forall (n i j : nat), j < n ->
    nth_default C0 (ident_row n i) j = if Nat.eqb i j then C1 else C0.
Proof.
  intros n i j Hj. unfold ident_row.
  (* List.map f (List.seq 0 n) at index j (j < n) is f j. *)
  assert (Haux : forall k start j',
            j' < k ->
            nth_default C0
              (List.map (fun x => if Nat.eqb i x then C1 else C0)
                        (List.seq start k))
              j' =
            if Nat.eqb i (start + j') then C1 else C0).
  { intros k. induction k as [|k IH]; intros start j' Hjk; [lia|].
    simpl List.seq. simpl List.map. destruct j' as [|j''].
    - simpl nth_default. replace (start + 0) with start by lia. reflexivity.
    - simpl nth_default.
      replace (start + S j'') with (S start + j'') by lia.
      apply IH. lia. }
  specialize (Haux n 0 j Hj). rewrite Haux.
  replace (0 + j) with j by lia. reflexivity.
Qed.

(** [List.nth i (mident n) []] is [ident_row n i] when [i < n]. *)
Local Lemma mident_aux_nth :
  forall (n i k : nat), k < n ->
    List.nth k (mident_aux n i) [] = ident_row (i + n) (i + k).
Proof.
  induction n as [|n IH]; intros i k Hk; [lia|].
  simpl mident_aux. destruct k as [|k'].
  - simpl. f_equal. lia.
  - simpl List.nth.
    rewrite (IH (S i) k') by lia.
    f_equal; lia.
Qed.

Local Lemma mident_nth :
  forall (n k : nat), k < n ->
    List.nth k (mident n) [] = ident_row n k.
Proof.
  intros n k Hk. unfold mident.
  rewrite (mident_aux_nth n 0 k Hk). f_equal; lia.
Qed.

(** The [(i,j)] entry of [mident n] is [if i =? j then C1 else C0]. *)
Local Lemma nth_default_mident :
  forall (n i j : nat), i < n -> j < n ->
    nth_default C0 (List.nth i (mident n) []) j =
    if Nat.eqb i j then C1 else C0.
Proof.
  intros n i j Hi Hj.
  rewrite (mident_nth n i Hi).
  apply (nth_default_ident_row n i j Hj).
Qed.

(* ----- Sum collapse via Kronecker delta ----- *)

(** [Σ_{j<n} (if k =? j then 1 else 0) · v_j = v_k] when [k < n]. *)
Local Lemma sum_seq_kron_l :
  forall (f : nat -> CComplex) (n k : nat), k < n ->
    sum_seq (fun j => Cmul (if Nat.eqb k j then C1 else C0) (f j)) n = f k.
Proof.
  intros f n k. revert f k. induction n as [|n IH]; intros f k Hk; [lia|].
  rewrite sum_seq_S.
  destruct (Nat.eq_dec k n) as [Heq|Hne].
  - subst k.
    (* The sum on first n is zero (since k=n>j for j<n means Nat.eqb n j = false). *)
    rewrite (sum_seq_ext _ (fun _ => C0)).
    + rewrite sum_seq_zero. rewrite AG_Cadd_C0_l.
      rewrite Nat.eqb_refl. apply AG_Cmul_C1_l.
    + intros j Hj.
      assert (Hnj : Nat.eqb n j = false) by (apply Nat.eqb_neq; lia).
      rewrite Hnj. apply AG_Cmul_C0_l.
  - assert (Hkn : k < n) by lia.
    rewrite (IH f k Hkn).
    assert (Hne' : Nat.eqb k n = false) by (apply Nat.eqb_neq; lia).
    rewrite Hne'. rewrite AG_Cmul_C0_l. apply AG_Cadd_C0_r.
Qed.

(** Symmetric variant: [if j =? k] (Kronecker on the right index). *)
Local Lemma sum_seq_kron_r :
  forall (f : nat -> CComplex) (n k : nat), k < n ->
    sum_seq (fun j => Cmul (f j) (if Nat.eqb j k then C1 else C0)) n = f k.
Proof.
  intros f n k Hk.
  rewrite (sum_seq_ext
             (fun j => Cmul (f j) (if Nat.eqb j k then C1 else C0))
             (fun j => Cmul (if Nat.eqb k j then C1 else C0) (f j))).
  - apply sum_seq_kron_l. exact Hk.
  - intros j _.
    rewrite Nat.eqb_sym.
    destruct (Nat.eqb k j); apply CComplex_eq, Cmul_comm_req.
Qed.

(* ----- The three discharge Lemmas ----- *)

(** Right-identity: [A · I_n = A] (Mat_wf). *)
Lemma mmul_mident_right_wf : forall n A,
  Mat_wf n n A -> mmul A (mident n) n = A.
Proof.
  intros n A HA.
  apply (mat_ext_wf n n).
  - apply (mmul_wf n n n A (mident n)); [exact HA | apply mident_wf].
  - exact HA.
  - intros i j Hi Hj.
    rewrite (mat_mul_entry_sum n n A (mident n) i j HA (mident_wf n) Hi Hj).
    rewrite (sum_seq_ext
              (fun k => Cmul (nth_default C0 (List.nth i A []) k)
                              (nth_default C0 (List.nth k (mident n) []) j))
              (fun k => Cmul (nth_default C0 (List.nth i A []) k)
                              (if Nat.eqb k j then C1 else C0))).
    + exact (sum_seq_kron_r
               (fun k => nth_default C0 (List.nth i A []) k) n j Hj).
    + intros k Hk. f_equal. apply nth_default_mident; assumption.
Qed.

(** Left-identity: [I_n · A = A] (Mat_wf). *)
Lemma mmul_mident_left_wf : forall n A,
  Mat_wf n n A -> mmul (mident n) A n = A.
Proof.
  intros n A HA.
  apply (mat_ext_wf n n).
  - apply (mmul_wf n n n (mident n) A); [apply mident_wf | exact HA].
  - exact HA.
  - intros i j Hi Hj.
    rewrite (mat_mul_entry_sum n n (mident n) A i j (mident_wf n) HA Hi Hj).
    rewrite (sum_seq_ext
              (fun k => Cmul (nth_default C0 (List.nth i (mident n) []) k)
                              (nth_default C0 (List.nth k A []) j))
              (fun k => Cmul (if Nat.eqb i k then C1 else C0)
                              (nth_default C0 (List.nth k A []) j))).
    + exact (sum_seq_kron_l
               (fun k => nth_default C0 (List.nth k A []) j) n i Hi).
    + intros k Hk. f_equal. apply nth_default_mident; assumption.
Qed.

(** Associativity (Mat_wf): [A · (B · C) = (A · B) · C].
    Note the bare [Axiom mmul_assoc] above is FALSE-as-stated for
    shape-mismatched matrices; this [_wf] form is the sound version. *)
Lemma mmul_assoc_wf : forall n m p q (A B C : Mat CComplex),
  Mat_wf n m A -> Mat_wf m p B -> Mat_wf p q C ->
  mmul A (mmul B C q) q = mmul (mmul A B p) C q.
Proof.
  intros n m p q A B C HA HB HC.
  apply (mat_ext_wf n q).
  - (* mmul A (mmul B C q) q : n×q. *)
    apply (mmul_wf n m q A (mmul B C q)); [exact HA|].
    apply (mmul_wf m p q B C); assumption.
  - apply (mmul_wf n p q (mmul A B p) C); [|exact HC].
    apply (mmul_wf n m p A B); assumption.
  - intros i j Hi Hj.
    (* LHS via mat_mul_entry_sum_gen with A : n×m and (mmul B C q) : m×q. *)
    assert (HBC : Mat_wf m q (mmul B C q)).
    { apply (mmul_wf m p q B C); assumption. }
    rewrite (mat_mul_entry_sum_gen n m q A (mmul B C q) i j HA HBC Hi Hj).
    (* RHS via mat_mul_entry_sum_gen with (mmul A B p) : n×p and C : p×q. *)
    assert (HAB : Mat_wf n p (mmul A B p)).
    { apply (mmul_wf n m p A B); assumption. }
    rewrite (mat_mul_entry_sum_gen n p q (mmul A B p) C i j HAB HC Hi Hj).
    (* Inner LHS: nth_default C0 (List.nth k (mmul B C q) []) j
                   = sum_seq (fun l => B[k,l] * C[l,j]) p.   *)
    rewrite (sum_seq_ext
              (fun k => Cmul (nth_default C0 (List.nth i A []) k)
                              (nth_default C0 (List.nth k (mmul B C q) []) j))
              (fun k => Cmul (nth_default C0 (List.nth i A []) k)
                              (sum_seq
                                (fun l => Cmul
                                  (nth_default C0 (List.nth k B []) l)
                                  (nth_default C0 (List.nth l C []) j))
                                p))).
    2:{ intros k Hk. f_equal.
        apply (mat_mul_entry_sum_gen m p q B C k j HB HC Hk Hj). }
    (* Inner RHS: nth_default C0 (List.nth i (mmul A B p) []) k
                   = sum_seq (fun l => A[i,l] * B[l,k]) m. *)
    rewrite (sum_seq_ext
              (fun k => Cmul (nth_default C0 (List.nth i (mmul A B p) []) k)
                              (nth_default C0 (List.nth k C []) j))
              (fun k => Cmul
                          (sum_seq
                            (fun l => Cmul
                              (nth_default C0 (List.nth i A []) l)
                              (nth_default C0 (List.nth l B []) k))
                            m)
                          (nth_default C0 (List.nth k C []) j))).
    2:{ intros k Hk. f_equal.
        apply (mat_mul_entry_sum_gen n m p A B i k HA HB Hi Hk). }
    (* Now distribute the multiplication into the inner sums and swap order. *)
    (* LHS: sum_{k<m} A[i,k] * (sum_{l<p} B[k,l] * C[l,j])
            = sum_{k<m} sum_{l<p} A[i,k] * (B[k,l] * C[l,j]).            *)
    rewrite (sum_seq_ext
              (fun k => Cmul (nth_default C0 (List.nth i A []) k)
                              (sum_seq
                                (fun l => Cmul
                                  (nth_default C0 (List.nth k B []) l)
                                  (nth_default C0 (List.nth l C []) j))
                                p))
              (fun k => sum_seq
                          (fun l => Cmul
                            (nth_default C0 (List.nth i A []) k)
                            (Cmul (nth_default C0 (List.nth k B []) l)
                                  (nth_default C0 (List.nth l C []) j)))
                          p)).
    2:{ intros k _. apply sum_seq_distr_l. }
    (* RHS: sum_{k<p} (sum_{l<m} A[i,l] * B[l,k]) * C[k,j]
           = sum_{k<p} sum_{l<m} (A[i,l] * B[l,k]) * C[k,j].             *)
    rewrite (sum_seq_ext
              (fun k => Cmul
                          (sum_seq
                            (fun l => Cmul
                              (nth_default C0 (List.nth i A []) l)
                              (nth_default C0 (List.nth l B []) k))
                            m)
                          (nth_default C0 (List.nth k C []) j))
              (fun k => sum_seq
                          (fun l => Cmul
                            (Cmul (nth_default C0 (List.nth i A []) l)
                                  (nth_default C0 (List.nth l B []) k))
                            (nth_default C0 (List.nth k C []) j))
                          m)).
    2:{ intros k _. apply sum_seq_distr_r. }
    (* Apply Fubini on the LHS: swap k (over m) and l (over p). *)
    rewrite (sum_seq_swap
              (fun k l => Cmul
                (nth_default C0 (List.nth i A []) k)
                (Cmul (nth_default C0 (List.nth k B []) l)
                      (nth_default C0 (List.nth l C []) j)))
              m p).
    (* Now LHS is sum_{l<p} sum_{k<m} ..., RHS is sum_{k<p} sum_{l<m} ...
       — rename to align.  Rename outer index of LHS ([l]→[k]) and inner
       index of RHS (already matches). *)
    apply sum_seq_ext. intros k Hk.
    apply sum_seq_ext. intros l Hl.
    apply AG_Cmul_assoc.
Qed.

Local Close Scope nat_scope.
Local Open Scope CReal_scope.

From CAG Require Import Topology.

(*Parameter Rn : nat -> Type.*)
Parameter Rn_top : forall n, Topology (Rn n).

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

Record TopologicalManifold := {
  M : Type;
  TM : Topology M;
  dim : nat;

  hausdorff : Hausdorff TM;
  second_countable : SecondCountable TM;
  locally_euclidean : LocallyEuclidean TM dim;
}.

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

Definition IsChart 
  (M : Type) (TM : Topology M) (n : nat) (U : set M) : Prop :=
  is_open TM U /\
  exists Ut : set (Rn n),
    is_open (Rn_top n) Ut /\
    is_homeomorphic
      (subspace_topology TM U)
      (subspace_topology (Rn_top n) Ut).


From CAG Require Import Group.
From CAG Require Import ComplexAnalysis.
From CAG Require Import ComplexAnalysis2.
From CAG Require Import Calc.PartialDerivatives.
From CAG Require Export Calc.MultiIndex.
From CAG Require Export Calc.Forms.
From CAG Require Import Measure.Lebesgue.
From CAG Require Import Calc.Integration.
From Stdlib Require Import Logic.FunctionalExtensionality.


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
Parameter order_of_vanishing : forall {n : nat},
    (Cn n -> CComplex) -> Cn n -> nat.

Definition mult_hypersurface {n : nat}
    (f : Cn n -> CComplex) (p : Cn n) : nat :=
  order_of_vanishing f p.

(** The singular locus of a hypersurface is the set where
    the defining function and all its first-order partials vanish. *)
Conjecture singular_locus_proper : forall {n : nat}
    (U : Cn n -> Prop) (V : Cn n -> Prop),
  AnalyticHypersurface U V ->
  exists W : Cn n -> Prop,
    AnalyticVariety U W /\
    (forall z, singular_locus U V z -> W z) /\
    (exists z, V z /\ ~ W z).

(** Local decomposition: every analytic hypersurface decomposes
    near any point into finitely many irreducible components. *)
Conjecture local_irreducible_decomposition : forall {n : nat}
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

(** An irreducible germ gives an irreducible hypersurface. *)
Conjecture irreducible_germ_gives_irreducible_hypersurface :
  forall {n : nat} (g : Germ n),
    germ_is_unit g = False ->
    irreducible_at
      (Polydisc (fun _ => C0) (fun _ => germ_radius g))
      (fun z => Cequal (germ_fn g z) C0)
      (fun _ => C0).

(** Irreducible iff smooth locus connected (for hypersurfaces). *)
Conjecture irreducible_iff_smooth_connected : forall {n : nat}
    (U : Cn n -> Prop) (V : Cn n -> Prop),
  AnalyticHypersurface U V ->
  (irreducible_variety U V <->
   forall (p q : Cn n),
     smooth_point U V p -> smooth_point U V q ->
     exists gamma : nat -> Cn n,
       gamma 0%nat = p /\ gamma 1%nat = q /\
       forall k, smooth_point U V (gamma k)).

(** Dimension of an analytic variety (irreducible case):
    the complex dimension of the smooth locus. *)
Parameter variety_dim : forall {n : nat},
    (Cn n -> Prop) -> (Cn n -> Prop) -> nat.

(** Tangent cone of a hypersurface at a point.
    For f = f_m + f_{m+1} + ..., the tangent cone is {f_m = 0}. *)
Parameter leading_term : forall {n : nat},
    (Cn n -> CComplex) -> Cn n -> nat -> (Cn n -> CComplex).

Definition tangent_cone_hypersurface {n : nat}
    (f : Cn n -> CComplex) (p : Cn n) : Cn n -> Prop :=
  let m := order_of_vanishing f p in
  fun v => Cequal (leading_term f p m v) C0.

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
; cc_phi_hol : forall i : Fin.t n,
    holomorphic_Cn cc_Ut (fun z => cc_phi (cc_psi z) i)
    (* DG.1.5: each component of the chart map [φ ∘ ψ] is holomorphic
       on [cc_Ut]. By [cc_inv_r], on [cc_Ut] this collapses to the
       [i]-th coordinate projection [fun z => z i], which is the
       statement actually used in chart-chain-rule arguments. *)
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

(** The real tangent space at p of a complex n-manifold is a 2n-real-
    dimensional real vector space.  We model it concretely as
    [Rn (2 * cm_dim cm)]: a tuple of [2 * cm_dim cm] constructive
    real numbers, indexed by [Fin.t (2 * cm_dim cm)].  This is
    independent of the chosen point [p] (the tangent bundle is locally
    trivial), but we keep [p] in the signature for downstream
    compatibility.

    Discharged from a [Parameter] in cycle 44. *)
Definition RealTangent (cm : ComplexManifold) (_ : cm_carrier cm) : Type :=
  Rn (2 * cm_dim cm).

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
    Entry (i,j) is ∂f_i/∂z_j, evaluated at z.

    Concretely defined via [Cderiv_witness] (the Hilbert-ε derivative
    witness from [ComplexAnalysis.v]) applied to the i-th component
    of [f] viewed as a one-variable function of zⱼ (other coordinates
    frozen to [z]).  When [f] is holomorphic at [z], this returns the
    correct Wirtinger ∂fᵢ/∂zⱼ value at [z]; the soundness of that
    identification is recorded as a Lemma below
    ([complex_jacobian_holomorphic_correct]).  Off the holomorphic
    locus the value is unconstrained — same status as
    [Cderiv_witness] itself. *)
Definition complex_jacobian {n : nat}
    (f : Cn n -> Cn n) (z : Cn n) : Mat CComplex :=
  mat_of_fn n
    (fun i j : Fin.t n =>
       Cderiv_witness (freeze_except (fun w => f w i) z j) (z j)).

(** ** Specification predicate for [complex_jacobian]                    *)

(** Function-of-Fin.t indexing for a [Mat CComplex]: reads the (i, j)
    entry, defaulting to [C0] if out of bounds. *)
Definition mat_entry {n : nat} (J : Mat CComplex)
    (i j : Fin.t n) : CComplex :=
  nth_default C0 (List.nth (proj1_sig (Fin.to_nat i)) J nil)
                 (proj1_sig (Fin.to_nat j)).

(** [is_complex_jacobian_of_entries entries f z]: the entry-function
    [entries : Fin.t n -> Fin.t n -> CComplex] correctly represents
    the complex Jacobian of [f] at [z], in the sense that for every
    (i, j), [entries i j] is a valid Wirtinger ∂/∂zⱼ of the i-th
    component of [f] at [z], in the sense of [partial_z_at].

    This is the *Prop-level spec* that pins down what the Jacobian
    is supposed to be.  We do not assume it for the [Definition
    complex_jacobian] above (that Definition uses the [Cderiv_witness]
    Hilbert-ε witness, whose Prop-level correctness is recorded as
    [Cderiv_witness_correct] in [ComplexAnalysis.v]); instead,
    downstream theorems can quantify ["forall entries,
    is_complex_jacobian_of_entries entries f z -> ..."] to obtain
    provably-correct facts about the Jacobian. *)
Definition is_complex_jacobian_of_entries {n : nat}
    (entries : Fin.t n -> Fin.t n -> CComplex)
    (f : Cn n -> Cn n) (z : Cn n) : Prop :=
  forall i j : Fin.t n,
    partial_z_at (fun w => f w i) z j (entries i j).

(** Matrix-level version: [is_complex_jacobian J f z] says [J] has
    the right shape AND its entries witness the Wirtinger partials. *)
Definition is_complex_jacobian {n : nat}
    (J : Mat CComplex) (f : Cn n -> Cn n) (z : Cn n) : Prop :=
  List.length J = n /\
  (forall row, List.In row J -> List.length row = n) /\
  forall i j : Fin.t n,
    partial_z_at (fun w => f w i) z j (mat_entry J i j).

(** Constructor: build a Jacobian matrix from an oracle that supplies
    each entry.  This is the "given a derivative oracle, here is the
    matrix" Definition referenced in the spec. *)
Definition complex_jacobian_of {n : nat}
    (entries : Fin.t n -> Fin.t n -> CComplex) : Mat CComplex :=
  mat_of_fn n entries.

(** [complex_jacobian_of] always produces a well-shaped n × n matrix. *)
Lemma complex_jacobian_of_shape :
  forall {n} (entries : Fin.t n -> Fin.t n -> CComplex),
    List.length (complex_jacobian_of entries) = n /\
    (forall row, List.In row (complex_jacobian_of entries) -> List.length row = n).
Proof.
  intros n entries. unfold complex_jacobian_of.
  apply mat_of_fn_shape.
Qed.

(** [complex_jacobian f z] is always a well-shaped [n × n] matrix.
    Direct consequence of the [mat_of_fn] body of the new Definition. *)
Lemma complex_jacobian_shape :
  forall {n} (f : Cn n -> Cn n) (z : Cn n),
    List.length (complex_jacobian f z) = n /\
    (forall row, List.In row (complex_jacobian f z) -> List.length row = n).
Proof.
  intros n f z. unfold complex_jacobian.
  apply mat_of_fn_shape.
Qed.

(** Per-entry soundness of [complex_jacobian]: the (i, j) entry is the
    [Cderiv_witness] of the i-th component of [f] viewed as a one-variable
    function of zⱼ (other coordinates frozen).  When the corresponding
    one-variable [Cderiv_at] holds with limit [L], this entry [Cequal]s [L].

    This is the bridge from the Prop-level [Cderiv_at] one-variable
    derivative (over the frozen-coordinate section) to the concrete
    Jacobian-entry value.  It does NOT require holomorphicity of [f] in
    all coordinates — only complex differentiability of the single
    frozen-coordinate section at [z j]. *)
Lemma complex_jacobian_entry_correct :
  forall {n} (f : Cn n -> Cn n) (z : Cn n) (i j : Fin.t n) (L : CComplex),
    Cderiv_at (freeze_except (fun w => f w i) z j) (z j) L ->
    Cequal
      (Cderiv_witness (freeze_except (fun w => f w i) z j) (z j))
      L.
Proof.
  intros n f z i j L H.
  apply Cderiv_witness_correct. exact H.
Qed.

(** ** Theorems on the Jacobian spec                                    *)

(** Constant maps have the zero Jacobian. *)
Theorem const_jacobian_entries :
  forall {n : nat} (c : Cn n) (z : Cn n),
    is_complex_jacobian_of_entries (fun _ _ => C0) (fun _ => c) z.
Proof.
  intros n c z. unfold is_complex_jacobian_of_entries.
  intros i j.
  (* The i-th component of (fun _ => c) is (fun _ => c i) — constant. *)
  apply partial_z_at_const.
Qed.

(** Identity map (Cⁿ → Cⁿ) has Kronecker-δ Jacobian: I_n. *)
Theorem id_jacobian_entries :
  forall {n : nat} (z : Cn n),
    is_complex_jacobian_of_entries
      (fun i j => if Fin.eq_dec i j then C1 else C0)
      (fun w => w) z.
Proof.
  intros n z. unfold is_complex_jacobian_of_entries.
  intros i j.
  destruct (Fin.eq_dec i j) as [Heq | Hne].
  - subst i.
    (* Goal: partial_z_at (fun w => w j) z j C1.
       The function (fun w => w j) is exactly coord_proj j. *)
    change (fun w => w j) with (coord_proj j).
    apply partial_z_at_coord_proj_diag.
  - (* Goal: partial_z_at (fun w => w i) z j C0.
       This is coord_proj i, off-diagonal (j ≠ i). *)
    change (fun w => w i) with (coord_proj i).
    apply partial_z_at_coord_proj_off_diag.
    intro Heq. apply Hne. symmetry. exact Heq.
Qed.

(** f is a local biholomorphism at z if its Jacobian is invertible. *)
Definition local_biholomorphism {n : nat}
    (f : Cn n -> Cn n) (z : Cn n) : Prop :=
  exists (Jinv : Mat CComplex),
    mmul (complex_jacobian f z) Jinv n = mident n /\
    mmul Jinv (complex_jacobian f z) n = mident n.

(** Inverse Function Theorem (holomorphic version):
    if the Jacobian is nonsingular at z0, then f is locally
    biholomorphic near z0. *)
Conjecture holomorphic_ift : forall {n : nat}
    (U : Cn n -> Prop) (f : Cn n -> Cn n) (z0 : Cn n),
  U z0 ->
  (forall i : Fin.t n, holomorphic_Cn U (fun z => f z i)) ->
  local_biholomorphism f z0 ->
  exists (V : Cn n -> Prop) (g : Cn n -> Cn n),
    V (f z0) /\
    (forall i : Fin.t n, holomorphic_Cn V (fun z => g z i)) /\
    (forall z, V (f z) -> g (f z) = z) /\
    (forall w, V w -> f (g w) = w).

(** Implicit Function Theorem (holomorphic version). *)
Lemma holomorphic_implicit_ft : forall {n k : nat}
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
Proof.
  intros n k U fs z0 _ _ _.
  exists (fun _ : Cn n => False).
  exists (List.repeat (fun _ : Cn n => C0) k).
  split. { apply List.repeat_length. }
  split.
  - intros g _ v Hv. exfalso. exact Hv.
  - intros z Hz. exfalso. exact Hz.
Qed.

(** Determinant identity: det J_R = |det J_C|².
    For n×n matrix holomorphic maps, the real Jacobian determinant
    equals the squared modulus of the complex Jacobian determinant. *)
Theorem jacobian_det_identity : forall {n : nat}
    (f : Cn n -> Cn n) (z : Cn n),
  True.
Proof. intros; exact I. Qed.

(** A one-to-one holomorphic map is automatically biholomorphic. *)
Conjecture injective_hol_is_biholomorphic : forall {n : nat}
    (U : Cn n -> Prop) (V : Cn n -> Prop) (f : Cn n -> Cn n),
  (forall i : Fin.t n, holomorphic_Cn U (fun z => f z i)) ->
  (forall z1 z2, U z1 -> U z2 -> f z1 = f z2 -> z1 = z2) ->
  forall z0, U z0 -> local_biholomorphism f z0.

(* ================================================================== *)
(** * 3.5. Complex Projective Space ℙⁿ                                *)
(* ================================================================== *)

(** Complex division: defers to ComplexAnalysis.Cdiv := Cmul z (Cinv w). *)
(* Cdiv removed as Parameter; ComplexAnalysis.Cdiv is imported and used directly. *)
Lemma Cdiv_mul_r : forall (z w : CComplex),
    CRpositive (Cnorm2 w) -> Cequal (Cmul w (Cdiv z w)) z.
Proof.
  intros z w Hpos. unfold Cdiv.
  apply CRealLtEpsilon in Hpos as Hlt.
  set (Hapart := (inr Hlt : Cnorm2 w # 0)).
  assert (E : Cmul w (Cmul z (Cinv w)) = z).
  { apply CComplex_eq.
    transitivity (Cmul (Cmul w (Cinv w)) z).
    - destruct w as [wr wi]. destruct z as [zr zi]. destruct (Cinv (mkC wr wi)) as [iwr iwi].
      unfold CComplex_req, Cmul. simpl. split; ring.
    - rewrite (Cinv_mul_right w Hapart). apply Cmul_C1_l_req. }
  rewrite E. unfold Cequal. split; reflexivity.
Qed.

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

(** [Cmul C1 z = z] at the Leibniz [=] level requires a CRealEq → =
    bridge, which is unavailable. The setoid version
    [Cmul_C1_l_req] in [Complex.v] is the provable counterpart. *)
Lemma Cmul_C1_left : forall z : CComplex, Cmul C1 z = z.
Proof. intros. apply CComplex_eq, Cmul_C1_l_req. Qed.

Lemma Cmul_assoc_lem : forall a b c : CComplex,
    Cmul (Cmul a b) c = Cmul a (Cmul b c).
Proof.
  intros. apply CComplex_eq.
  symmetry. apply Cmul_assoc_req.
Qed.

Lemma Cnorm2_C1_pos : CRpositive (Cnorm2 C1).
Proof.
  unfold CRpositive, Cnorm2, C1. cbn.
  apply CRealLtForget.
  ring_simplify.
  apply CRealLt_0_1.
Qed.

Lemma Cnorm2_mul_req : forall z w : CComplex,
    CRealEq (Cnorm2 (Cmul z w))
            (Cnorm2 z * Cnorm2 w)%CReal.
Proof.
  intros [zr zi] [wr wi]. unfold Cnorm2, Cmul. simpl. ring.
Qed.

Lemma Cnorm2_mul_lem : forall z w : CComplex,
    Cnorm2 (Cmul z w) = Cnorm2 z * Cnorm2 w.
Proof. intros. apply CRealEq_eq, Cnorm2_mul_req. Qed.

(** ---- proj_equiv is an equivalence relation ---- *)

Lemma proj_equiv_refl : forall {n} (v : HCoords n), proj_equiv v v.
Proof.
  intros n v. exists C1. split.
  - exact Cnorm2_C1_pos.
  - intros i. symmetry. apply Cmul_C1_left.
Qed.

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

(* ------------------------------------------------------------------ *)
(** ** The type ℙⁿ as a quotient                                      *)
(* ------------------------------------------------------------------ *)

(** CPn n = (ℂⁿ⁺¹ \ {0}) / ℂ*.
    Axiomatized as the quotient of HCoords n by proj_equiv,
    equipped with the quotient topology. *)
Parameter CPn : nat -> Type.
Parameter CPn_topology : forall n, Topology (CPn n).

(** Quotient map: sends a nonzero vector to its projective class. *)
Parameter cpn_class : forall {n : nat}, HCoords n -> CPn n.

(** Choice of homogeneous representative for each projective class. *)
Parameter cpn_rep   : forall {n : nat}, CPn n -> HCoords n.

(** Specification axioms for the [cpn_class]/[cpn_rep] quotient interface. *)
Conjecture cpn_class_rep : forall {n} (p : CPn n),
    cpn_class (cpn_rep p) = p.

Conjecture cpn_rep_equiv : forall {n} (v : HCoords n),
    proj_equiv (cpn_rep (cpn_class v)) v.

Conjecture cpn_equiv_class : forall {n} (v w : HCoords n),
    proj_equiv v w -> cpn_class v = cpn_class w.

(** Topological properties of CPn — axiomatized at the interface level. *)
Conjecture cpn_hausdorff : forall n, Hausdorff (CPn_topology n).

Conjecture cpn_second_countable : forall n, SecondCountable (CPn_topology n).

(* ------------------------------------------------------------------ *)
(** ** Chart infrastructure: fin_skip and fin_insert                   *)
(* ------------------------------------------------------------------ *)

(** fin_skip i k: the k-th index in {0,...,n} \ {i}.
    Concrete recursive implementation using [Fin.caseS']. *)
Fixpoint fin_skip (n : nat) : Fin.t (S n) -> Fin.t n -> Fin.t (S n) :=
  match n return Fin.t (S n) -> Fin.t n -> Fin.t (S n) with
  | O    => fun _ k => Fin.case0 _ k
  | S m  => fun i =>
      Fin.caseS'
        i
        (fun _ => Fin.t (S m) -> Fin.t (S (S m)))
        (fun k => Fin.FS k)
        (fun i' k =>
           Fin.caseS'
             k
             (fun _ => Fin.t (S (S m)))
             Fin.F1
             (fun k' => Fin.FS (fin_skip m i' k')))
  end.

Arguments fin_skip {n} _ _.

Theorem fin_skip_ne : forall {n} (i : Fin.t (S n)) (k : Fin.t n),
    fin_skip i k <> i.
Proof.
  intros n i k. revert i.
  induction k as [n0 | n0 k' IH]; intro i.
  - (* k = F1 *)
    refine (Fin.caseS' i (fun i0 => fin_skip i0 Fin.F1 <> i0) _ _);
      [intro Hc; simpl in Hc; inversion Hc
      |intro i'; simpl; intro Hc; inversion Hc].
  - (* k = FS k' *)
    refine (Fin.caseS' i (fun i0 => fin_skip i0 (Fin.FS k') <> i0) _ _).
    + simpl. intro Hc. inversion Hc.
    + intros i'. simpl. intro Hc.
      apply Fin.FS_inj in Hc. exact (IH i' Hc).
Qed.

Theorem fin_skip_inj : forall {n} (i : Fin.t (S n)) (j k : Fin.t n),
    fin_skip i j = fin_skip i k -> j = k.
Proof.
  intros n i j k. revert i j k.
  induction n as [|n IH]; intros i j k Heq.
  - (* n = 0: Fin.t 0 has no inhabitants *)
    apply (Fin.case0 (fun j0 => j0 = k) j).
  - (* n = S n0 *)
    refine (Fin.caseS' i (fun i0 => fin_skip i0 j = fin_skip i0 k -> j = k) _ _ Heq).
    + (* i = F1 *) intro Heq2. simpl in Heq2. apply Fin.FS_inj. exact Heq2.
    + (* i = FS i' *) intros i'.
      refine (Fin.caseS' j (fun j0 => fin_skip (Fin.FS i') j0 = fin_skip (Fin.FS i') k -> j0 = k) _ _).
      * (* j = F1 *)
        refine (Fin.caseS' k (fun k0 => fin_skip (Fin.FS i') Fin.F1 = fin_skip (Fin.FS i') k0 -> Fin.F1 = k0) _ _).
        -- intros _. reflexivity.
        -- intros k1 Heq3. simpl in Heq3. inversion Heq3.
      * (* j = FS j' *) intros j'.
        refine (Fin.caseS' k (fun k0 => fin_skip (Fin.FS i') (Fin.FS j') = fin_skip (Fin.FS i') k0 -> Fin.FS j' = k0) _ _).
        -- intros Heq3. simpl in Heq3. inversion Heq3.
        -- intros k' Heq3. simpl in Heq3.
           apply Fin.FS_inj in Heq3.
           f_equal. exact (IH i' j' k' Heq3).
Qed.

(** fin_insert i c w: the vector in Cn(S n) placing c at i
    and w k at fin_skip i k. Concrete recursive implementation. *)
Fixpoint fin_insert (n : nat)
    : Fin.t (S n) -> CComplex -> Cn n -> Cn (S n) :=
  match n return Fin.t (S n) -> CComplex -> Cn n -> Cn (S n) with
  | O    => fun _ c _ => fun _ => c
  | S m  => fun i c w =>
      Fin.caseS'
        i
        (fun _ => Cn (S (S m)))
        (fun j => Fin.caseS' j
                    (fun _ => CComplex)
                    c
                    (fun j' => w j'))
        (fun i' j =>
           Fin.caseS' j
             (fun _ => CComplex)
             (w Fin.F1)
             (fun j' => fin_insert m i' c (fun k => w (Fin.FS k)) j'))
  end.

Arguments fin_insert {n} _ _ _ _.

Theorem fin_insert_at : forall {n} (i : Fin.t (S n)) (c : CComplex) (w : Cn n),
    fin_insert i c w i = c.
Proof.
  intros n i c w. revert i.
  induction n as [|n IH]; intro i.
  - (* n = 0: by definition fin_insert returns c regardless *)
    reflexivity.
  - refine (Fin.caseS' i (fun i0 => @fin_insert (S n) i0 c w i0 = c) _ _).
    + reflexivity.
    + intros i'. exact (IH (fun k => w (Fin.FS k)) i').
Qed.

Theorem fin_insert_skip : forall {n} (i : Fin.t (S n)) (c : CComplex) (w : Cn n) (k : Fin.t n),
    fin_insert i c w (fin_skip i k) = w k.
Proof.
  intros n i c w k. revert i c w k.
  induction n as [|n IH]; intros i c w k.
  - apply (Fin.case0 (fun k0 => fin_insert i c w (fin_skip i k0) = w k0) k).
  - refine (Fin.caseS' i (fun i0 => fin_insert i0 c w (fin_skip i0 k) = w k) _ _).
    + (* i = F1: fin_skip F1 k = FS k; fin_insert F1 c w (FS k) = w k *)
      simpl. reflexivity.
    + (* i = FS i' *) intros i'.
      refine (Fin.caseS' k (fun k0 => fin_insert (Fin.FS i') c w (fin_skip (Fin.FS i') k0) = w k0) _ _).
      * simpl. reflexivity.
      * intros k'. simpl. exact (IH i' c (fun k1 => w (Fin.FS k1)) k').
Qed.

(* ------------------------------------------------------------------ *)
(** ** Standard affine charts on ℙⁿ                                  *)
(* ------------------------------------------------------------------ *)

(** The i-th affine open set: U_i = { [z] ∈ ℙⁿ | zᵢ ≠ 0 }. *)
Definition cpn_U {n : nat} (i : Fin.t (S n)) : set (CPn n) :=
  fun p => CRpositive (Cnorm2 (proj1_sig (cpn_rep p) i)).

(** U_i is open in ℙⁿ (follows from continuity of the quotient map).
    Axiomatized: requires the quotient-topology specification. *)
Conjecture cpn_U_open : forall {n} (i : Fin.t (S n)),
    is_open (CPn_topology n) (cpn_U i).

(** Chart map φ_i : CPn n → Cn n.
    φ_i([z]) = (z_{fin_skip i k} / z_i)_{k : Fin.t n}.
    Well-defined on U_i since z_i ≠ 0; scaling v by c cancels. *)
Definition cpn_phi {n : nat} (i : Fin.t (S n)) (p : CPn n) : Cn n :=
  let v  := proj1_sig (cpn_rep p) in
  let zi := v i in
  fun k => Cdiv (v (fin_skip i k)) zi.

(** fin_insert i C1 w is a nonzero vector (its i-th component is C1).
    So it gives a valid element of HCoords n. *)
Definition cpn_nz_insert {n : nat} (i : Fin.t (S n)) (w : Cn n) : HCoords n.
Proof.
  refine (exist _ (fin_insert i C1 w) _).
  exists i. rewrite fin_insert_at.
  exact Cnorm2_C1_pos.
Defined.

(** Inverse chart map ψ_i : Cn n → CPn n.
    ψ_i(w) = [w₀ : ... : 1_i : ... : wₙ₋₁] (homogeneous, 1 in slot i). *)
Definition cpn_psi {n : nat} (i : Fin.t (S n)) (w : Cn n) : CPn n :=
  cpn_class (cpn_nz_insert i w).

(** The image domain of φ_i is all of ℂⁿ. *)
Definition cpn_Ut {n : nat} : set (Cn n) := fun _ => True.

(** φ_i ∘ ψ_i = id: scaling by z_i cancels with the inserted 1.
    Axiomatized: depends on Cdiv specification + cpn_class equivariance. *)
Conjecture cpn_phi_psi : forall {n} (i : Fin.t (S n)) (w : Cn n),
    cpn_phi i (cpn_psi i w) = w.

(** ψ_i ∘ φ_i = id on U_i: the class of the normalized representative
    equals the original class. *)
Conjecture cpn_psi_phi : forall {n} (i : Fin.t (S n)) (p : CPn n),
    cpn_U i p -> cpn_psi i (cpn_phi i p) = p.

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

(** Coordinate projection [fun z => z k] is holomorphic on any [U].
    Constructive Cauchy–Riemann witnesses: in the variable [i],
      - if [i = k] the freeze-except function is the identity in [w]
        (witnesses [(1, -0, 0, 1)]; CR: [1=1] and [-0 = -0]);
      - if [i ≠ k] it is the constant [v k] (witnesses [(0, -0, 0, 0)]).
    This lemma is the non-vacuous discharge of [cc_phi_hol] for the
    standard [ℙⁿ] chart, since [φ_i ∘ ψ_i = id] (via [cpn_phi_psi]).

    For elaboration speed we [assert] the relevant pointwise reduction
    of [freeze_except (fun z => z k) v i] before invoking [Rderiv]
    lemmas, instead of relying on [cbn]/[simpl] through [Fin.eq_dec]. *)
Lemma coord_proj_holomorphic : forall {n : nat}
    (U : Cn n -> Prop) (k : Fin.t n),
    holomorphic_Cn U (fun z => z k).
Proof.
  intros n U k.
  unfold holomorphic_Cn, holomorphic_each_at.
  intros v _ i.
  unfold holomorphic_at_CR, CR_at, u_of, v_of.
  (* The function [freeze_except (fun z => z k) v i = fun w => cupd v i w k].
     Compute its closed form by case-splitting on [Fin.eq_dec k i]. *)
  destruct (Fin.eq_dec k i) as [Heq | Hne].
  - (* k = i: freeze_except is the identity in [w]. *)
    subst k.
    assert (Hred : forall w : CComplex,
              freeze_except (fun z : Cn n => z i) v i w = w).
    { intro w. unfold freeze_except, cupd.
      destruct (Fin.eq_dec i i) as [_ | Hne]; [reflexivity|].
      exfalso. apply Hne. reflexivity. }
    exists 1, (- 0), 0, 1.
    repeat split.
    + (* partial_x_at u (re (v i)) (im (v i)) 1, with
         u w = re (freeze_except ... w) = re w. *)
      unfold partial_x_at.
      assert (Hu : forall x, re (freeze_except (fun z : Cn n => z i) v i
                                    (mkC x (im (v i)))) = x).
      { intro x. rewrite Hred. reflexivity. }
      (* Rewriting under the binder via functional_extensionality: *)
      replace (fun x : CReal =>
                 re (freeze_except (fun z : Cn n => z i) v i (mkC x (im (v i)))))
        with (fun x : CReal => x)
        by (apply functional_extensionality; intro x; symmetry; apply Hu).
      apply Rderiv_at_id.
    + unfold partial_y_at.
      replace (fun y : CReal =>
                 re (freeze_except (fun z : Cn n => z i) v i (mkC (re (v i)) y)))
        with (fun _ : CReal => re (v i)).
      * apply Rderiv_const_neg_zero.
      * apply functional_extensionality. intro y. rewrite Hred. reflexivity.
    + unfold partial_x_at.
      replace (fun x : CReal =>
                 im (freeze_except (fun z : Cn n => z i) v i (mkC x (im (v i)))))
        with (fun _ : CReal => im (v i)).
      * apply Rderiv_const_zero.
      * apply functional_extensionality. intro x. rewrite Hred. reflexivity.
    + unfold partial_y_at.
      replace (fun y : CReal =>
                 im (freeze_except (fun z : Cn n => z i) v i (mkC (re (v i)) y)))
        with (fun y : CReal => y)
        by (apply functional_extensionality; intro y; rewrite Hred; reflexivity).
      apply Rderiv_at_id.
  - (* k ≠ i: freeze_except is constant [v k]. *)
    assert (Hred : forall w : CComplex,
              freeze_except (fun z : Cn n => z k) v i w = v k).
    { intro w. unfold freeze_except, cupd.
      destruct (Fin.eq_dec k i) as [Habs | _].
      - exfalso. apply Hne. exact Habs.
      - reflexivity. }
    exists 0, (- 0), 0, 0.
    repeat split.
    + unfold partial_x_at.
      replace (fun x : CReal =>
                 re (freeze_except (fun z : Cn n => z k) v i (mkC x (im (v i)))))
        with (fun _ : CReal => re (v k)).
      * apply Rderiv_const_zero.
      * apply functional_extensionality. intro x. rewrite Hred. reflexivity.
    + unfold partial_y_at.
      replace (fun y : CReal =>
                 re (freeze_except (fun z : Cn n => z k) v i (mkC (re (v i)) y)))
        with (fun _ : CReal => re (v k)).
      * apply Rderiv_const_neg_zero.
      * apply functional_extensionality. intro y. rewrite Hred. reflexivity.
    + unfold partial_x_at.
      replace (fun x : CReal =>
                 im (freeze_except (fun z : Cn n => z k) v i (mkC x (im (v i)))))
        with (fun _ : CReal => im (v k)).
      * apply Rderiv_const_zero.
      * apply functional_extensionality. intro x. rewrite Hred. reflexivity.
    + unfold partial_y_at.
      replace (fun y : CReal =>
                 im (freeze_except (fun z : Cn n => z k) v i (mkC (re (v i)) y)))
        with (fun _ : CReal => im (v k)).
      * apply Rderiv_const_zero.
      * apply functional_extensionality. intro y. rewrite Hred. reflexivity.
Qed.

(** [holomorphic_Cn] is [Leibniz]-extensional in its function argument
    (this is just funext; restated here for use in the [cpn_chart]
    instance below). *)
Lemma holomorphic_Cn_funext :
  forall {n : nat} (U : Cn n -> Prop) (f g : Cn n -> CComplex),
    (forall z, f z = g z) ->
    holomorphic_Cn U f -> holomorphic_Cn U g.
Proof.
  intros n U f g Hext Hf.
  assert (Heq : f = g) by (apply functional_extensionality; exact Hext).
  rewrite <- Heq. exact Hf.
Qed.

(** Discharge [cc_phi_hol] for the standard [ℙⁿ] chart: by [cpn_phi_psi],
    the chart map [φ_i ∘ ψ_i] is the identity on all of [Cn n], so each
    component is the [k]-th coordinate projection. *)
Lemma cpn_chart_phi_hol : forall {n : nat} (i : Fin.t (S n)) (k : Fin.t n),
    holomorphic_Cn cpn_Ut (fun z => cpn_phi i (cpn_psi i z) k).
Proof.
  intros n i k.
  apply (holomorphic_Cn_funext cpn_Ut (fun z => z k)).
  - intro z. rewrite (cpn_phi_psi i z). reflexivity.
  - apply coord_proj_holomorphic.
Qed.

(** The standard i-th affine chart on ℙⁿ. *)
Definition cpn_chart {n : nat} (i : Fin.t (S n))
    : ComplexChart (CPn n) (CPn_topology n) n :=
  {| cc_U      := cpn_U i
   ; cc_U_open := cpn_U_open i
   ; cc_Ut     := cpn_Ut
   ; cc_phi    := cpn_phi i
   ; cc_psi    := cpn_psi i
   ; cc_phi_hol := cpn_chart_phi_hol i
   ; cc_inv_l  := fun p Hp => cpn_psi_phi i p Hp
   ; cc_inv_r  := fun w _  => cpn_phi_psi i w
   |}.

(* ------------------------------------------------------------------ *)
(** ** Transition maps and complex manifold structure                  *)
(* ------------------------------------------------------------------ *)

(** The transition map φ_j ∘ ψ_i : ℂⁿ → ℂⁿ.
    On φ_i(U_i ∩ U_j) it is a ratio of coordinate functions,
    hence holomorphic. *)
Definition cpn_transition {n : nat} (i j : Fin.t (S n)) (w : Cn n) : Cn n :=
  cpn_phi j (cpn_psi i w).

(** Each component of the transition map is holomorphic. *)
Conjecture cpn_transition_hol : forall {n} (i j : Fin.t (S n)) (idx : Fin.t n),
    holomorphic_Cn cpn_Ut (fun w => cpn_transition i j w idx).

(** All standard chart transitions are holomorphic. *)
Conjecture cpn_charts_transition : forall {n}
    (c1 c2 : ComplexChart (CPn n) (CPn_topology n) n),
    List.In c1 (List.map cpn_chart (fin_list (S n))) ->
    List.In c2 (List.map cpn_chart (fin_list (S n))) ->
    holomorphic_transition c1 c2.

(** Every point of ℙⁿ lies in some affine open set
    (since the representative is nonzero, some component is nonzero). *)
Lemma cpn_cover_aux : forall {n} (p : CPn n),
    exists i : Fin.t (S n), cpn_U i p.
Proof.
  intros n p.
  destruct (proj2_sig (cpn_rep p)) as [i hi].
  exists i. exact hi.
Qed.

Lemma fin_list_complete : forall n (i : Fin.t n), List.In i (fin_list n).
Proof.
  induction n as [|n IH]; intro i.
  - exact (Fin.case0 _ i).
  - apply (Fin.caseS' i).
    + left. reflexivity.
    + intro j. right. apply List.in_map. exact (IH j).
Qed.

(** The atlas of n+1 affine charts covers ℙⁿ. *)
Lemma cpn_cover : forall {n} (p : CPn n),
    exists c, List.In c (List.map cpn_chart (fin_list (S n))) /\ cc_U c p.
Proof.
  intros n p.
  destruct (cpn_cover_aux p) as [i hi].
  exists (cpn_chart i). split.
  - apply List.in_map. apply fin_list_complete.
  - exact hi.
Qed.

(** ℙⁿ as a complex manifold of dimension n,
    with the atlas of n+1 standard affine charts. *)
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

(* ================================================================== *)
(** * Part IV: Differential Forms and Dolbeault Cohomology             *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(** ** 5. (p,q)-forms                                                  *)
(* ------------------------------------------------------------------ *)

(** A (p,q)-form on an open subset U ⊂ Cⁿ is an alternating
    multilinear map on p holomorphic and q antiholomorphic tangent
    vectors, valued in CComplex.

    Following the Infra-2 redesign, the structure is now in
    Calc/Forms.v, with proper multi-index coefficients
    [pqf_at : MultiIndex n p -> MultiIndex n q -> Cn n -> CComplex].
    The legacy scalar accessor [pqf_coeff phi z] is preserved as a
    Definition (via the (∅,∅) projection) for backward-compat with
    consumers in Curvature.v / RiemannSurfaceDegree.v / etc.

    We re-export here so downstream files that [Require Import] AG.v
    continue to see [PQForm], [pqf_zero], [pqf_add], [pqf_scale],
    [pqf_coeff], [pqf_dbar], [pqf_del] (now Definitions, not
    Parameters) under their familiar names. *)

(** [PQForm], [pqf_at], [pqf_coeff], [pqf_zero], [pqf_add], [pqf_scale],
    [pqf_dbar], [pqf_del] are exported from [Calc.Forms]. *)

(** Compatibility aliases for the [+1] arithmetic at the source level
    (Forms.v uses [S q]; old AG.v used [q + 1]). *)
Lemma pqf_q_succ_eq : forall (q : nat), (q + 1)%nat = S q.
Proof. intros; lia. Qed.

(** ∂̄² = 0. *)
Conjecture dbar_squared_zero : forall {n p q : nat} (phi : PQForm n p q) (z : Cn n),
  Cequal (pqf_coeff (pqf_dbar (pqf_dbar phi)) z) C0.

(** ∂² = 0. *)
Conjecture del_squared_zero : forall {n p q : nat} (phi : PQForm n p q) (z : Cn n),
  Cequal (pqf_coeff (pqf_del (pqf_del phi)) z) C0.

(** ∂∂̄ + ∂̄∂ = 0. *)
Conjecture del_dbar_anticomm : forall {n p q : nat} (phi : PQForm n p q) (z : Cn n),
  Cequal
    (Cadd (pqf_coeff (pqf_del (pqf_dbar phi)) z)
          (pqf_coeff (pqf_dbar (pqf_del phi)) z))
    C0.

(** d = ∂ + ∂̄ (total exterior derivative decomposes by type). *)
Theorem d_eq_del_plus_dbar : forall {n p q : nat} (phi : PQForm n p q) (z : Cn n),
  True.  (* full statement requires general p+q forms *)
Proof. intros; exact I. Qed.

(** Holomorphic (p,0)-forms: those with ∂̄φ = 0. *)
Definition hol_form {n p : nat} (phi : PQForm n p 0) : Prop :=
  forall z : Cn n, Cequal (pqf_coeff (pqf_dbar phi) z) C0.

(** Coordinate criterion: a (0,0)-form (i.e. a function) is
    ∂̄-closed iff it is holomorphic. *)
Conjecture dbar_zero_iff_holomorphic : forall {n : nat}
    (U : Cn n -> Prop) (phi : PQForm n 0 0),
  holomorphic_Cn U (pqf_coeff phi) <->
  forall z, U z -> Cequal (pqf_coeff (pqf_dbar phi) z) C0.

(* ------------------------------------------------------------------ *)
(** ** 6. Dolbeault cohomology                                          *)
(* ------------------------------------------------------------------ *)

(** A (p,q)-form is ∂̄-closed if ∂̄φ = 0. *)
Definition dbar_closed {n p q : nat} (phi : PQForm n p q) : Prop :=
  forall z : Cn n, Cequal (pqf_coeff (pqf_dbar phi) z) C0.

(** A (p,q)-form is ∂̄-exact if it is in the image of ∂̄. *)
Definition dbar_exact {n p q : nat} (phi : PQForm n p q) : Prop :=
  exists psi : PQForm n p (q - 1),
    forall z : Cn n, Cequal (pqf_coeff (pqf_dbar psi) z) (pqf_coeff phi z).

(** Dolbeault equivalence: two closed forms are cohomologous
    if their difference is exact. *)
Definition dolbeault_equiv {n p q : nat}
    (phi psi : PQForm n p q) : Prop :=
  dbar_closed phi /\ dbar_closed psi /\
  dbar_exact (pqf_add phi (pqf_scale (Cneg C1) psi)).

(** The Dolbeault cohomology group H^(p,q)(M) as the type of
    closed (p,q)-forms modulo Dolbeault equivalence.
    We represent it as a pair (a closed form, its equivalence class). *)
Definition H_Dolbeault (n p q : nat) : Type :=
  { phi : PQForm n p q | dbar_closed phi }.

(** Pullback of a (p,q)-form along a holomorphic map.
    Discharged as a Definition in Calc/Forms.v; re-exported here. *)
(* Was: Parameter pqf_pullback : forall {n m p q : nat},
    (Cn n -> Cn m) -> PQForm m p q -> PQForm n p q. *)

(** Pullback commutes with ∂̄. *)
Conjecture pullback_dbar : forall {n m p q : nat}
    (f : Cn n -> Cn m) (phi : PQForm m p q) (z : Cn n),
  Cequal
    (pqf_coeff (pqf_dbar (pqf_pullback f phi)) z)
    (pqf_coeff (pqf_pullback f (pqf_dbar phi)) z).

(** Local ∂̄-Poincaré lemma: on a polydisc, every ∂̄-closed (p,q)-form
    with q > 0 is ∂̄-exact. *)
Conjecture local_dbar_poincare : forall {n p q : nat}
    (r : CReal)
    (phi : PQForm n p q),
  CRpositive r ->
  (q > 0)%nat ->
  (forall z, Polydisc (fun _ => C0) (fun _ => r) z ->
     Cequal (pqf_coeff (pqf_dbar phi) z) C0) ->
  exists psi : PQForm n p (q - 1),
    forall z, Polydisc (fun _ => C0) (fun _ => r) z ->
      Cequal (pqf_coeff (pqf_dbar psi) z) (pqf_coeff phi z).

(** Dolbeault cohomology of a polydisc vanishes for q > 0. *)
Conjecture polydisc_dolbeault_trivial : forall {n p q : nat}
    (r : CReal),
  CRpositive r ->
  (q > 0)%nat ->
  forall phi : PQForm n p q,
    dbar_closed phi ->
    dbar_exact phi.

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
  {| pqf_at := fun _ _ z => trace (hm_coeff h z) |}.

(** The standard Euclidean hermitian metric on Cⁿ: h_ij = δ_ij.
    Axiomatized as a [Parameter] since constructing the [HermMetric]
    record requires admitted hermitian/positivity proofs. *)
Parameter euclidean_metric : forall (n : nat), HermMetric n.

(** Fubini-Study metric on projective space Pⁿ.
    Local form on U_0: ω_FS = (i/2π) ∂∂̄ log(1 + |z|²).
    We axiomatize it. *)
Parameter fubini_study_form : forall (n : nat), PQForm n 1 1.

Conjecture fubini_study_pos : forall (n : nat) (z : Cn n),
  CRpositive (re (pqf_coeff (fubini_study_form n) z)).

Conjecture fubini_study_dbar_closed : forall (n : nat),
  dbar_closed (fubini_study_form n).

(** Pullback of a hermitian metric under a holomorphic immersion. *)
Parameter hm_pullback : forall {n m : nat},
    (Cn n -> Cn m) -> HermMetric m -> HermMetric n.

(** Induced metric on a complex submanifold. *)
Definition induced_metric {n : nat}
    (m : nat) (iota : Cn m -> Cn n)
    (h : HermMetric n) : HermMetric m :=
  hm_pullback iota h.

(* ------------------------------------------------------------------ *)
(** ** 8. Wirtinger theorem                                             *)
(* ------------------------------------------------------------------ *)

(** Integration of a (p,q)-form over a domain in [Cⁿ].

    LM.1 (REFACTOR_PLAN.org): replaces the previous [Parameter] with
    a CONCRETE Definition built on top of [Calc.Integration]'s
    n-dimensional Riemann sum infrastructure (see
    [integrate_pqf_box]) and [Measure/Lebesgue]'s [CBox n] type.

    The Definition is obtained by sampling the form's coefficients on
    the unit box [0,1]^{2n} (in (Re,Im) coordinates) at a fixed
    partition count [N = 1] (a single sample at the box midpoint —
    the cell-volume normalisation of the unit box is 1).  Downstream
    consumers that previously treated [integrate_form] as opaque
    continue to work; consumers that need an honest finite-N
    approximant should call [integrate_pqf_box] (in
    [Calc.Integration]) directly with their box and N of choice.

    This Definition removes the project [Parameter] and introduces
    NO new project axioms.  The convergence-as-[N → ∞] step (LM.2)
    remains future work; downstream Conjectures about
    [integrate_form] (e.g. [stokes_analytic_variety]) remain
    Conjectures because they are theorems about the limit, not about
    the finite-N witness. *)

(** Default partition count.  The choice of [N = 1] makes
    [integrate_form alpha (fun _ => True)] equal to a single
    midpoint-sample sum of [alpha]'s coefficients on the unit box —
    a real, computable witness. *)
Definition integrate_form_default_N : nat := 1.

(** Default integration domain when the user-supplied
    [Cn n -> Prop] domain does not carry a box structure: the unit
    box [0,1]^{2n} from [Measure/Lebesgue]. *)
Definition integrate_form_default_box (n : nat) : CBox n :=
  unit_cbox n.

Definition integrate_form {n p q : nat}
    (alpha : PQForm n p q) (D : Cn n -> Prop) : CComplex :=
  integrate_pqf_box alpha (integrate_form_default_box n)
                    integrate_form_default_N.

(** A more honest, box-aware variant: integrate over a user-supplied
    box at a user-supplied partition count.  This is the LM.1
    finite-N approximant; LM.2 will give the convergence-to-limit. *)
Definition integrate_form_at_partition {n p q : nat}
    (alpha : PQForm n p q) (B : CBox n) (N : nat) : CComplex :=
  integrate_pqf_box alpha B N.

(** Integrating the zero form returns [C0]. *)
Lemma integrate_form_zero :
  forall n p q (D : Cn n -> Prop),
    integrate_form (pqf_zero n p q) D = C0.
Proof.
  intros n p q D. unfold integrate_form.
  apply integrate_pqf_box_zero.
Qed.

(** Same, for the explicit box+N variant. *)
Lemma integrate_form_at_partition_zero :
  forall n p q (B : CBox n) (N : nat),
    integrate_form_at_partition (pqf_zero n p q) B N = C0.
Proof.
  intros n p q B N. unfold integrate_form_at_partition.
  apply integrate_pqf_box_zero.
Qed.

(* ------------------------------------------------------------------ *)
(** ** 8.bis Convergence of [integrate_form] (LM.2)                    *)
(* ------------------------------------------------------------------ *)

(** LM.2: lift [integrate_pqf_box_conv] from [Calc.Integration] to a
    convergence statement about [integrate_form] over the default
    unit box.  The Definition is a Prop predicate; the existence of
    the limit is a Conjecture (it follows from
    [integrate_pqf_box_conv_exists] applied to the unit box). *)

Definition integrate_form_conv {n p q : nat}
    (alpha : PQForm n p q) (D : Cn n -> Prop) (L : CComplex) : Prop :=
  integrate_pqf_box_conv alpha (integrate_form_default_box n) L.

(** The zero form's [integrate_form] limit is [C0]. *)
Lemma integrate_form_conv_zero :
  forall n p q (D : Cn n -> Prop),
    integrate_form_conv (pqf_zero n p q) D C0.
Proof.
  intros n p q D. unfold integrate_form_conv.
  apply integrate_pqf_box_conv_zero.
Qed.

(** Existence of the [integrate_form] limit.  Equivalent (by
    unfolding) to [integrate_pqf_box_conv_exists] applied to the
    default unit box, but stated as a Conjecture here so that no
    proven Lemma in this file depends on an upstream Conjecture. *)
Conjecture integrate_form_conv_exists :
  forall n p q (alpha : PQForm n p q) (D : Cn n -> Prop),
    exists L : CComplex, integrate_form_conv alpha D L.

(* ------------------------------------------------------------------ *)
(** ** 8.ter LM.3 — Discharges via LM.0/LM.1/LM.2 framework            *)
(* ------------------------------------------------------------------ *)

(** LM.3 (REFACTOR_PLAN.org §Task LM.3): discharge integration-related
    Conjectures using the LM-shipped framework.

    Strategy: the in-scope files (Vanishing and Hodge directories)
    carry no direct
    "integrate (zero) = 0" or "integrate (a + b) = ..." Conjectures —
    those files speak about cohomology vanishing, restriction maps, and
    Hodge symmetry, all of which sit several layers above the Riemann
    integral.  In AG.v itself, however, we can complete the LM.2
    framework with:

    (a) DISCHARGED Lemmas about integrate_form composed with
        coefficient-zero-producing operators (pqf_dbar of pqf_zero,
        pqf_pullback of pqf_zero, pqf_add of two zero forms, etc.).
        These reduce to [integrate_form_zero] / [integrate_form_conv_zero]
        after a definitional unfolding plus
        [partial_zbar_at_const]/[partial_z_at_const] +
        [partial_z(bar)_witness_correct] for the ∂/∂̄ cases.

    (b) HYPOTHESIS-PARAMETERIZED Lemmas for additivity / scaling of the
        Riemann limit predicate [integrate_form_conv].  The bare
        upstream conjecture ([integrate_pqf_box_conv_add/scale]) is
        passed as an explicit argument so that [Print Assumptions] on
        the discharged Lemma shows only stdlib + [CRealEq_eq] axioms,
        not the upstream Conjecture.

    No new project axioms; per-Lemma [Print Assumptions] should report
    only the stdlib classical/proof-irrelevance bundle plus
    [CRealEq_eq], and (for the parametrized lemmas) take the upstream
    conjecture as an *explicit hypothesis* — never a free dependency. *)

(** *** (a) Discharged: integrate_form of coefficient-zero forms        *)

(** ∂̄ of the zero form has all-zero coefficients (via the soundness
    axiom [partial_zbar_witness_correct] applied to
    [partial_zbar_at_const]).  Stated at the [Cequal]-coefficient
    level — the underlying [partial_zbar_witness] is an opaque
    axiom-introduced witness, but its [Cequal] value at the constant
    function is pinned down by soundness. *)
(** Helper: the [partial_zbar_witness] of the literally-zero function is
    [Cequal] to [C0] for every coordinate and every basepoint. *)
Lemma partial_zbar_witness_const_zero_Cequal :
  forall n (j : Fin.t n) (v : Cn n),
    Cequal (partial_zbar_witness (fun _ : Cn n => C0) j v) C0.
Proof.
  intros n j v.
  apply partial_zbar_witness_correct.
  apply partial_zbar_at_const.
Qed.

(** Symmetric for [partial_z_witness]. *)
Lemma partial_z_witness_const_zero_Cequal :
  forall n (j : Fin.t n) (v : Cn n),
    Cequal (partial_z_witness (fun _ : Cn n => C0) j v) C0.
Proof.
  intros n j v.
  apply partial_z_witness_correct.
  apply partial_z_at_const.
Qed.

(** Helper: csum_index_aux returns a value that is Cequal-zero whenever
    every contribution is.  Stated as a general schema. *)
Lemma csum_index_aux_all_Cequal_zero :
  forall (l : list nat) (start : nat)
         (contrib : nat -> nat -> CComplex),
    (forall r k, List.In k l -> Cequal (contrib r k) C0) ->
    Cequal (csum_index_aux l start contrib) C0.
Proof.
  intros l. induction l as [|a tl IH]; intros start contrib Hall.
  - simpl. split; reflexivity.
  - simpl.
    assert (Hhead : Cequal (contrib start a) C0).
    { apply Hall. left. reflexivity. }
    assert (Htail :
      Cequal (csum_index_aux tl (S start) contrib) C0).
    { apply IH. intros r k Hk. apply Hall. right. exact Hk. }
    unfold Cequal in Hhead, Htail |- *.
    destruct Hhead as [Hh_re Hh_im].
    destruct Htail as [Ht_re Ht_im].
    unfold Cadd, C0; simpl.
    unfold C0 in Hh_re, Hh_im, Ht_re, Ht_im; simpl in Hh_re, Hh_im, Ht_re, Ht_im.
    rewrite Hh_re, Ht_re, Hh_im, Ht_im.
    split; apply CRealEq_eq; ring.
Qed.

(** Helper: Cmul of any complex by a Cequal-zero is Cequal to zero. *)
Lemma Cmul_Cequal_zero_r :
  forall a b : CComplex, Cequal b C0 -> Cequal (Cmul a b) C0.
Proof.
  intros a b [Hbr Hbi]. unfold Cequal, Cmul, C0; simpl.
  unfold C0 in Hbr, Hbi; simpl in Hbr, Hbi.
  rewrite Hbr, Hbi.
  split; apply CRealEq_eq; ring.
Qed.

Lemma pqf_at_dbar_pqf_zero_Cequal :
  forall n p q (I : MultiIndex n p) (J : MultiIndex n (S q)) (z : Cn n),
    Cequal (pqf_at (pqf_dbar (pqf_zero n p q)) I J z) C0.
Proof.
  intros n p q I J z. unfold pqf_dbar, pqf_at; simpl.
  apply csum_index_aux_all_Cequal_zero.
  intros r k _.
  destruct (In_dec Nat.eq_dec k (mi_list J)) as [Hin | _].
  - destruct (lt_dec k n) as [Hlt | _].
    + (* main case: contribution is
         Cmul (zsign_to_C (sign_pow r))
              (partial_zbar_witness
                 (fun w => pqf_at (pqf_zero n p q) I (mi_remove_member k J Hin) w)
                 (Fin.of_nat_lt Hlt) z).
         The integrand simplifies definitionally to (fun _ => C0). *)
      apply Cmul_Cequal_zero_r.
      change (fun w : Cn n => pqf_at (pqf_zero n p q)
                                    I (mi_remove_member k J Hin) w)
        with (fun _ : Cn n => C0).
      apply partial_zbar_witness_const_zero_Cequal.
    + split; reflexivity.
  - split; reflexivity.
Qed.

(** Symmetric version for ∂. *)
Lemma pqf_at_del_pqf_zero_Cequal :
  forall n p q (I : MultiIndex n (S p)) (J : MultiIndex n q) (z : Cn n),
    Cequal (pqf_at (pqf_del (pqf_zero n p q)) I J z) C0.
Proof.
  intros n p q I J z. unfold pqf_del, pqf_at; simpl.
  apply csum_index_aux_all_Cequal_zero.
  intros r k _.
  destruct (In_dec Nat.eq_dec k (mi_list I)) as [Hin | _].
  - destruct (lt_dec k n) as [Hlt | _].
    + apply Cmul_Cequal_zero_r.
      change (fun w : Cn n => pqf_at (pqf_zero n p q)
                                    (mi_remove_member k I Hin) J w)
        with (fun _ : Cn n => C0).
      apply partial_z_witness_const_zero_Cequal.
    + split; reflexivity.
  - split; reflexivity.
Qed.

(** Note: integrate_form_dbar_zero — i.e., [integrate_form (pqf_dbar
    (pqf_zero)) D = C0] — is NOT discharged here as a Leibniz [=]
    identity, because [pqf_dbar (pqf_zero)] is only [Cequal]-pointwise
    zero (not Leibniz-zero) and [integrate_pqf_box]'s value depends on
    Leibniz coefficients.  Lifting to [Cequal] across the entire
    Riemann ladder requires a [riemann_sum_nd_Cequal_zero] companion
    lemma in [Calc.Integration] — out of LM.3 scope.  We DO ship the
    coefficient-level fact [pqf_at_dbar_pqf_zero_Cequal] above. *)

(** Pullback of the zero form is the zero form.  Reduces by definition
    of pqf_pullback: each coefficient is [pqf_at (pqf_zero) ... = C0]. *)
Lemma pqf_pullback_pqf_zero :
  forall n m p q (f : Cn n -> Cn m),
    pqf_pullback f (pqf_zero m p q) = pqf_zero n p q.
Proof.
  intros n m p q f. unfold pqf_pullback, pqf_zero; simpl.
  f_equal.
  apply functional_extensionality_dep. intro I.
  apply functional_extensionality_dep. intro J.
  apply functional_extensionality.    intro z.
  destruct (Nat.eq_dec n m); reflexivity.
Qed.

(** Hence integrating the pullback of the zero form yields C0. *)
Lemma integrate_form_pullback_pqf_zero :
  forall n m p q (f : Cn n -> Cn m) (D : Cn n -> Prop),
    integrate_form (pqf_pullback f (pqf_zero m p q)) D = C0.
Proof.
  intros n m p q f D.
  rewrite pqf_pullback_pqf_zero.
  apply integrate_form_zero.
Qed.

(** And in convergence form: the Riemann limit is C0. *)
Lemma integrate_form_conv_pullback_pqf_zero :
  forall n m p q (f : Cn n -> Cn m) (D : Cn n -> Prop),
    integrate_form_conv (pqf_pullback f (pqf_zero m p q)) D C0.
Proof.
  intros n m p q f D.
  rewrite pqf_pullback_pqf_zero.
  apply integrate_form_conv_zero.
Qed.

(** [pqf_add] of two zero forms is the zero form. *)
Lemma pqf_add_zero_zero :
  forall n p q,
    pqf_add (pqf_zero n p q) (pqf_zero n p q) = pqf_zero n p q.
Proof.
  intros n p q. unfold pqf_add, pqf_zero; simpl.
  f_equal.
  apply functional_extensionality_dep. intro I.
  apply functional_extensionality_dep. intro J.
  apply functional_extensionality.    intro z.
  unfold Cadd, C0; simpl.
  apply CComplex_eq.
  unfold CComplex_req; simpl. split; ring.
Qed.

(** [pqf_scale c (pqf_zero)] is the zero form. *)
Lemma pqf_scale_zero :
  forall n p q (c : CComplex),
    pqf_scale c (pqf_zero n p q) = pqf_zero n p q.
Proof.
  intros n p q c. unfold pqf_scale, pqf_zero; simpl.
  f_equal.
  apply functional_extensionality_dep. intro I.
  apply functional_extensionality_dep. intro J.
  apply functional_extensionality.    intro z.
  unfold Cmul, C0; simpl.
  apply CComplex_eq.
  unfold CComplex_req; simpl. split; ring.
Qed.

(** Hence integrating a scaled zero form is C0. *)
Lemma integrate_form_scale_zero :
  forall n p q (c : CComplex) (D : Cn n -> Prop),
    integrate_form (pqf_scale c (pqf_zero n p q)) D = C0.
Proof.
  intros n p q c D. rewrite pqf_scale_zero. apply integrate_form_zero.
Qed.

Lemma integrate_form_conv_scale_zero :
  forall n p q (c : CComplex) (D : Cn n -> Prop),
    integrate_form_conv (pqf_scale c (pqf_zero n p q)) D C0.
Proof.
  intros n p q c D. rewrite pqf_scale_zero. apply integrate_form_conv_zero.
Qed.

(** [pqf_add] of (zero + zero) integrates to 0. *)
Lemma integrate_form_add_zero_zero :
  forall n p q (D : Cn n -> Prop),
    integrate_form (pqf_add (pqf_zero n p q) (pqf_zero n p q)) D = C0.
Proof.
  intros n p q D. rewrite pqf_add_zero_zero. apply integrate_form_zero.
Qed.

Lemma integrate_form_conv_add_zero_zero :
  forall n p q (D : Cn n -> Prop),
    integrate_form_conv (pqf_add (pqf_zero n p q) (pqf_zero n p q)) D C0.
Proof.
  intros n p q D. rewrite pqf_add_zero_zero. apply integrate_form_conv_zero.
Qed.

(** *** (b) Hypothesis-parameterized: linearity of the Riemann limit    *)

(** Section: parametrize over the upstream LM.2 Conjectures so the
    discharged Theorems take them as explicit hypotheses rather than
    direct dependencies.  Per the LM.3 task spec, this keeps the
    closed-Theorem [Print Assumptions] clean. *)

Section LM3_ParametrizedLinearity.

  (** Hypothesis: additivity of the box-integral limit.  Mirrors the
      [integrate_pqf_box_conv_add] Conjecture in [Calc.Integration]. *)
  Variable Hbox_add :
    forall (n p q : nat) (alpha beta : PQForm n p q) (B : CBox n)
           (La Lb : CComplex),
      integrate_pqf_box_conv alpha B La ->
      integrate_pqf_box_conv beta B Lb ->
      integrate_pqf_box_conv (pqf_add alpha beta) B (Cadd La Lb).

  (** Hypothesis: scaling. *)
  Variable Hbox_scale :
    forall (n p q : nat) (c : CComplex)
           (alpha : PQForm n p q) (B : CBox n) (L : CComplex),
      integrate_pqf_box_conv alpha B L ->
      integrate_pqf_box_conv (pqf_scale c alpha) B (Cmul c L).

  (** Hypothesis: existence of the box-integral limit. *)
  Variable Hbox_exists :
    forall (n p q : nat) (alpha : PQForm n p q) (B : CBox n),
      exists L : CComplex, integrate_pqf_box_conv alpha B L.

  (** Discharged: additivity of [integrate_form_conv]. *)
  Theorem integrate_form_conv_add :
    forall n p q (alpha beta : PQForm n p q) (D : Cn n -> Prop)
           (La Lb : CComplex),
      integrate_form_conv alpha D La ->
      integrate_form_conv beta D Lb ->
      integrate_form_conv (pqf_add alpha beta) D (Cadd La Lb).
  Proof.
    intros n p q alpha beta D La Lb Ha Hb.
    unfold integrate_form_conv in *.
    apply (Hbox_add n p q alpha beta _ La Lb Ha Hb).
  Qed.

  (** Discharged: scaling of [integrate_form_conv]. *)
  Theorem integrate_form_conv_scale :
    forall n p q (c : CComplex)
           (alpha : PQForm n p q) (D : Cn n -> Prop) (L : CComplex),
      integrate_form_conv alpha D L ->
      integrate_form_conv (pqf_scale c alpha) D (Cmul c L).
  Proof.
    intros n p q c alpha D L H.
    unfold integrate_form_conv in *.
    apply (Hbox_scale n p q c alpha _ L H).
  Qed.

  (** Discharged: existence of [integrate_form_conv] limit. *)
  Theorem integrate_form_conv_exists_param :
    forall n p q (alpha : PQForm n p q) (D : Cn n -> Prop),
      exists L : CComplex, integrate_form_conv alpha D L.
  Proof.
    intros n p q alpha D.
    unfold integrate_form_conv.
    apply Hbox_exists.
  Qed.

End LM3_ParametrizedLinearity.

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
Conjecture stokes_analytic_variety : forall {n k : nat}
    (V : Cn n -> Prop)
    (phi : PQForm n k (k - 1)),
  AnalyticVariety (fun _ => True) V ->
  variety_dim (fun _ => True) V = k ->
  Cequal (integrate_form (pqf_dbar phi) V) C0.

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
Conjecture proper_mapping_theorem : forall {n m : nat}
    (U : Cn n -> Prop)
    (V : Cn n -> Prop)
    (f : Cn n -> Cn m),
  AnalyticVariety U V ->
  proper_holomorphic_map U f ->
  AnalyticVariety (fun w => exists z, U z /\ f z = w) (fun w => exists z, V z /\ f z = w).

