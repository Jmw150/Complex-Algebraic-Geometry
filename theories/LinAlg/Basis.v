(** * LinAlg/Basis.v
    Finite-dimensional linear algebra: linear combinations, linear
    independence, span, basis, and dimension.

    This module builds finite-dim VS theory on top of the existing
    [VectorSpaceF] record from Lie/BasicDef.v. The key ideas:

    - [linear_combination vs coeffs vs_list] computes Σᵢ coeffsᵢ · vᵢ.
    - [LinIndependent vs L] : the only way Σ cᵢ vᵢ = 0 is all cᵢ = 0.
    - [Spans vs L] : every vector is a linear combination of L.
    - [IsBasis vs L] : L is linearly independent and spans.
    - [HasDim vs n] : there exists a basis of length n. *)

Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* ================================================================== *)
(** * 1. Linear combinations                                          *)
(* ================================================================== *)

Section LinearCombinations.

  Context {F : Type} {fld : Field F} {V : Type} (vs : VectorSpaceF fld V).

  (** Σᵢ cᵢ · vᵢ where [coeffs] and [vs_list] are zipped pairwise.
      If lengths differ, extras are ignored (combine truncates). *)
  Fixpoint linear_combination (coeffs : list F) (vs_list : list V) : V :=
    match coeffs, vs_list with
    | [], _ | _, [] => vsF_zero vs
    | c :: cs, v :: ws =>
        vsF_add vs (vsF_scale vs c v) (linear_combination cs ws)
    end.

  (** All-zero coefficients give zero. *)
  Lemma lc_all_zero : forall (vs_list : list V) (n : nat),
      n = List.length vs_list ->
      linear_combination (List.repeat (cr_zero fld) n) vs_list = vsF_zero vs.
  Proof.
    induction vs_list as [|v ws IH]; intros n Hn.
    - destruct n; reflexivity.
    - destruct n as [|n']; [simpl in Hn; discriminate|].
      simpl. rewrite (vsF_scale_zero vs v).
      rewrite IH; [|simpl in Hn; lia].
      apply vsF_add_zero_l.
  Qed.

  (** Linear combination over empty list is zero. *)
  Lemma lc_nil_l : forall (vs_list : list V),
      linear_combination [] vs_list = vsF_zero vs.
  Proof. destruct vs_list; reflexivity. Qed.

  Lemma lc_nil_r : forall (coeffs : list F),
      linear_combination coeffs [] = vsF_zero vs.
  Proof. destruct coeffs; reflexivity. Qed.

End LinearCombinations.

(* ================================================================== *)
(** * 2. Linear independence and spanning                              *)
(* ================================================================== *)

Section IndependenceSpan.

  Context {F : Type} {fld : Field F} {V : Type} (vs : VectorSpaceF fld V).

  (** A list of vectors is linearly independent if the only way to
      combine them to get zero is with all-zero coefficients.

      Equivalent (via List.length): [List.length coeffs = List.length vs_list]
      ensures we don't take any short tails as "trivial". *)
  Definition LinIndependent (vs_list : list V) : Prop :=
    forall (coeffs : list F),
      List.length coeffs = List.length vs_list ->
      linear_combination vs coeffs vs_list = vsF_zero vs ->
      forall i, i < List.length coeffs ->
                List.nth i coeffs (cr_zero fld) = cr_zero fld.

  (** A list of vectors spans V if every v is a linear combination of them. *)
  Definition Spans (vs_list : list V) : Prop :=
    forall v : V, exists coeffs : list F,
      List.length coeffs = List.length vs_list /\
      v = linear_combination vs coeffs vs_list.

  (** A basis is a linearly independent spanning list. *)
  Definition IsBasis (vs_list : list V) : Prop :=
    LinIndependent vs_list /\ Spans vs_list.

  (** V has dimension n if there exists a basis of length n. *)
  Definition HasDim (n : nat) : Prop :=
    exists vs_list : list V, List.length vs_list = n /\ IsBasis vs_list.

End IndependenceSpan.

(* ================================================================== *)
(** * 3. Trivial cases: dimension 0 and 1                              *)
(* ================================================================== *)

Section LowDim.

  Context {F : Type} {fld : Field F} {V : Type} (vs : VectorSpaceF fld V).

  (** The empty list is linearly independent (vacuously). *)
  Lemma empty_lin_independent : LinIndependent vs [].
  Proof.
    intros coeffs Hlen Hlc i Hi.
    simpl in Hlen. apply List.length_zero_iff_nil in Hlen.
    subst coeffs. simpl in Hi. lia.
  Qed.

  (** Linearly-independent property is preserved on prefix when there's
      no nonzero combination. *)
  Lemma lin_indep_zero_iff_empty :
      Spans vs [] -> forall v : V, v = vsF_zero vs.
  Proof.
    intros HSpans v.
    destruct (HSpans v) as [coeffs [Hlen Heq]].
    rewrite Heq. apply lc_nil_r.
  Qed.

End LowDim.

(* ================================================================== *)
(** * 4. Singleton basis = dimension 1                                 *)
(* ================================================================== *)

Section SingletonBasis.

  Context {F : Type} {fld : Field F} {V : Type} (vs : VectorSpaceF fld V).

  (** A singleton {v} spans iff every w = c·v for some c. *)
  Definition Singleton_Spans (v : V) : Prop :=
    forall w : V, exists c : F, w = vsF_scale vs c v.

  (** A singleton {v} is lin. independent iff v ≠ 0 (c·v = 0 → c = 0). *)
  Definition Singleton_LinIndep (v : V) : Prop :=
    forall c : F, vsF_scale vs c v = vsF_zero vs -> c = cr_zero fld.

  (** Helper: linear_combination [c] [v] = c·v + 0 = c·v after eliminating add_zero_r. *)
  Lemma lc_singleton : forall (c : F) (v : V),
      linear_combination vs [c] [v] = vsF_add vs (vsF_scale vs c v) (vsF_zero vs).
  Proof. intros. reflexivity. Qed.

End SingletonBasis.

(* ================================================================== *)
(** * 5. Basis-via-Fin: alternative formulation                       *)
(* ================================================================== *)

Section FinBasis.

  Context {F : Type} {fld : Field F} {V : Type} (vs : VectorSpaceF fld V).

  (** A basis as a function from Fin.t n to V (alternative to list-based). *)
  Record FinBasis (n : nat) : Type := {
    fb_vec : nat -> V;  (* indexed; for k ≥ n we use a default *)
    fb_in_bound : forall k, k < n -> True;  (* placeholder constraint *)
  }.

  (** Sum over Fin.t n of c(i) * fb(i). *)
  Fixpoint fin_sum (n : nat) (c : nat -> F) (b : nat -> V) : V :=
    match n with
    | 0 => vsF_zero vs
    | S k => vsF_add vs (vsF_scale vs (c k) (b k)) (fin_sum k c b)
    end.

End FinBasis.
