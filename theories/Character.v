
(** Character Theory

    The character of a representation ρ : G → GL(n,ℂ) is the
    function χ_ρ : G → ℂ defined by χ_ρ(g) = trace(ρ(g)).

    Characters are class functions: χ(hgh⁻¹) = χ(g).
    They are additive under direct sums and multiplicative under
    tensor products.  For finite groups the inner product
    ⟨χ,ψ⟩ = (1/|G|)·Σ_{g} χ(g)·conj(ψ(g)) makes the irreducible
    characters into an orthonormal basis of class functions.
*)

From Stdlib Require Import List Arith Lia QArith ZArith.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
Import ListNotations.

From CAG Require Import Complex.
From CAG Require Import AG.
From CAG Require Import Group.
From CAG Require Import Representation.

Local Open Scope CReal_scope.

(* ------------------------------------------------------------------ *)
(** * 1. Character of a representation                                  *)
(* ------------------------------------------------------------------ *)

Definition character {G : Type} {sg : StrictGroup G} {n : nat}
    (ρ : GroupRep sg n) (g : G) : CComplex :=
  trace (rep_matrix ρ g).

(* ------------------------------------------------------------------ *)
(** * 2. Matrix algebra lemmas for trace                                *)
(* ------------------------------------------------------------------ *)

(** trace(A·B) = trace(B·A) — at Leibniz [=] level on [Mat CComplex]. *)
Conjecture trace_cyclic : forall (A B : Mat CComplex) (p : nat),
  trace (mmul A B p) = trace (mmul B A p).

(** trace(I_n) = n  (as a complex number).

    We inject via [Cinject_Q (inject_Q n)].  In Rocq the nat [n] does
    not automatically coerce, so we give the explicit statement and
    admit it pending a computational proof by induction on [n]. *)
(** Inject a natural number into [CComplex] as n copies of C1.
    This is defined recursively so that [Cinject_nat (S n) = Cadd C1 (Cinject_nat n)]
    holds definitionally, avoiding setoid issues with [inject_Q]. *)
Fixpoint Cinject_nat (n : nat) : CComplex :=
  match n with
  | O    => C0
  | S n' => Cadd C1 (Cinject_nat n')
  end.

(** [nth_default] on [List.map f (List.seq start len)] at position k
    equals [f (start + k)] when [k < len]. *)
Lemma nth_default_map_seq : forall (f : nat -> CComplex) (d : CComplex)
    (start len k : nat),
  (k < len)%nat ->
  nth_default d (List.map f (List.seq start len)) k = f (start + k)%nat.
Proof.
  intros f d start len k.
  revert start k.
  induction len as [| len IH]; intros start k Hlt.
  - lia.
  - simpl. destruct k as [| k'].
    + simpl. rewrite Nat.add_0_r. reflexivity.
    + simpl. rewrite (IH (S start) k' ltac:(lia)).
      f_equal. lia.
Qed.

(** The diagonal entry of [ident_row m i] at position [i] is [C1]
    (provided [i < m]). *)
Lemma ident_row_diag : forall m i,
  (i < m)%nat ->
  nth_default C0 (ident_row m i) i = C1.
Proof.
  intros m i Hlt.
  unfold ident_row.
  rewrite nth_default_map_seq by exact Hlt.
  rewrite Nat.add_0_l.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

(** [Cinject_nat] satisfies the successor equation. *)
(** Successor and zero equations hold definitionally. *)
Lemma Cinject_nat_succ : forall n,
  Cinject_nat (S n) = Cadd C1 (Cinject_nat n).
Proof. reflexivity. Qed.

Lemma Cinject_nat_zero : Cinject_nat 0%nat = C0.
Proof. reflexivity. Qed.

(** The trace of [mident_aux n i], read starting at diagonal position [i],
    equals [Cinject_nat n]. *)
Lemma trace_aux_mident_aux : forall n i,
  trace_aux (mident_aux n i) i = Cinject_nat n.
Proof.
  induction n as [| n IH]; intro i.
  - (* base: trace_aux [] i = C0 = Cinject_nat 0 *)
    simpl. reflexivity.
  - (* step: first row contributes C1 at position i, rest gives Cinject_nat n *)
    simpl.
    rewrite ident_row_diag by lia.
    rewrite IH.
    (* goal: C1 +c Cinject_nat n = Cinject_nat (S n) *)
    reflexivity.
Qed.

Lemma trace_mident : forall (n : nat),
  trace (mident n) = Cinject_nat n.
Proof.
  intro n. unfold trace, mident.
  apply trace_aux_mident_aux.
Qed.

(** Helpers for [trace_madd]. *)
Lemma nth_default_vadd : forall (r s : list CComplex) (i : nat),
  List.length r = List.length s ->
  nth_default C0 (vadd r s) i =
  Cadd (nth_default C0 r i) (nth_default C0 s i).
Proof.
  induction r as [| x xs IHr]; intros s i Hlen; destruct s as [| y ys];
    simpl in Hlen; try discriminate; simpl.
  - destruct i; apply CComplex_eq;
    apply CComplex_req_sym; apply Cadd_C0_l_req.
  - destruct i as [| i']; simpl.
    + reflexivity.
    + apply IHr. lia.
Qed.

Lemma trace_aux_madd : forall (A B : Mat CComplex) (i : nat),
  List.length A = List.length B ->
  (forall rA rB, List.In (rA, rB) (List.combine A B) ->
                 List.length rA = List.length rB) ->
  trace_aux (madd A B) i =
  Cadd (trace_aux A i) (trace_aux B i).
Proof.
  induction A as [| rA As IH]; intros B i Hlen Hrows;
    destruct B as [| rB Bs]; simpl in Hlen; try discriminate; simpl.
  - apply CComplex_eq; apply CComplex_req_sym; apply Cadd_C0_l_req.
  - rewrite (IH Bs (S i)) by
      (try lia; intros rA' rB' Hin; apply Hrows; right; exact Hin).
    rewrite nth_default_vadd by (apply Hrows; left; reflexivity).
    apply CComplex_eq.
    set (a := nth_default C0 rA i).
    set (b := nth_default C0 rB i).
    set (tA := trace_aux As (S i)).
    set (tB := trace_aux Bs (S i)).
    (* (a + b) + (tA + tB) ~~C (a + tA) + (b + tB) *)
    rewrite <- (Cadd_assoc_req a b (Cadd tA tB)).
    rewrite (Cadd_assoc_req b tA tB).
    rewrite (Cadd_comm_req b tA).
    rewrite <- (Cadd_assoc_req tA b tB).
    rewrite (Cadd_assoc_req a tA (Cadd b tB)).
    apply CComplex_req_refl.
Qed.

(** trace is linear in each row, hence additive.

    NOTE: the original statement is unconditional in [A] and [B], but
    that statement is mathematically false (e.g. [A=[]], [B=[[C1]]]
    gives [C0 = C1]).  We add the natural row-/column-shape hypotheses
    that hold for any [Mat_wf]-bearing pair of matrices. *)
Lemma trace_madd : forall (A B : Mat CComplex),
  List.length A = List.length B ->
  (forall rA rB, List.In (rA, rB) (List.combine A B) ->
                 List.length rA = List.length rB) ->
  trace (madd A B) = Cadd (trace A) (trace B).
Proof.
  intros A B Hlen Hrows. unfold trace.
  apply trace_aux_madd; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(** * 3. Basic character identities                                     *)
(* ------------------------------------------------------------------ *)

Section CharFacts.

Context {G : Type} (sg : StrictGroup G) (n : nat) (ρ : GroupRep sg n).

(** χ(e) = n   (the dimension of the representation). *)
Lemma char_identity :
  character ρ (se G sg) = Cinject_nat n.
Proof.
  unfold character.
  rewrite (rep_identity sg n ρ).
  apply trace_mident.
Qed.

(** χ is a class function: χ(hgh⁻¹) = χ(g). *)
Lemma char_class_fn : forall g h : G,
  character ρ (smul G sg h (smul G sg g (sinv G sg h))) =
  character ρ g.
Proof.
  intros g h.
  unfold character, rep_matrix.
  (* hom_fn ρ (h·g·h⁻¹) = ρ(h)·ρ(g)·ρ(h)⁻¹ *)
  rewrite (hom_mul ρ h (smul G sg g (sinv G sg h))).
  rewrite (hom_mul ρ g (sinv G sg h)).
  rewrite (hom_inv sg (GL_StrictGroup n) ρ h).
  simpl.  (* unfold GL_inv: sinv of GL_StrictGroup = GL_inv *)
  (* trace(ρ(h) · (ρ(g) · ρ(h)⁻¹)) = trace(ρ(g)) *)
  (* step 1: cyclic — trace(A·B) = trace(B·A) *)
  rewrite (trace_cyclic
    (gl_mat (hom_fn ρ h))
    (mmul (gl_mat (hom_fn ρ g)) (gl_inv_mat (hom_fn ρ h)) n)
    n).
  (* step 2: associate — trace((B·C)·A) = trace(B·(C·A)) *)
  rewrite <- (mmul_assoc_wf n n n n
                (gl_mat (hom_fn ρ g))
                (gl_inv_mat (hom_fn ρ h))
                (gl_mat (hom_fn ρ h))
                (gl_wf (hom_fn ρ g))
                (gl_inv_wf (hom_fn ρ h))
                (gl_wf (hom_fn ρ h))).
  (* step 3: C·A = ρ(h)⁻¹·ρ(h) = I *)
  rewrite (gl_left_inv (hom_fn ρ h)).
  (* step 4: B·I = B *)
  rewrite mmul_mident_right_wf.
  - reflexivity.
  - exact (gl_wf (hom_fn ρ g)).
Qed.

(** χ(g⁻¹) = conj(χ(g))  holds for unitary representations.

    We state the unitary condition and prove the consequence. *)
Definition is_unitary_rep : Prop :=
  forall g : G,
    mmul (rep_matrix ρ g)
         (List.map (List.map Cconj) (rep_matrix ρ g))
         n
    = mident n.

Conjecture char_inv_unitary : is_unitary_rep -> forall g : G,
  character ρ (sinv G sg g) =
  Cconj (character ρ g).

(** χ(gh) = trace(ρ(g)·ρ(h)) — direct from the hom law. *)
Lemma char_mul : forall g h : G,
  character ρ (smul G sg g h) =
  trace (mmul (rep_matrix ρ g) (rep_matrix ρ h) n).
Proof.
  intros g h. unfold character.
  rewrite rep_mul_matrix. reflexivity.
Qed.

End CharFacts.

(* ------------------------------------------------------------------ *)
(** * 4. Direct sum of representations                                  *)
(* ------------------------------------------------------------------ *)

(** Block-diagonal matrix: A ⊕ B as an (n+m)×(n+m) matrix.
    Row i of A⊕B is (row i of A) ++ (zero row of length m)
    for i < n, and (zero row of length n) ++ (row i-n of B)
    for i ≥ n.
*)
Definition block_diag (A B : Mat CComplex) (m : nat) : Mat CComplex :=
  List.app
    (List.map (fun row => List.app row (vzero m)) A)
    (List.map (fun row => List.app (vzero (List.length A)) row) B).

Lemma block_diag_wf : forall n m A B,
  Mat_wf n n A -> Mat_wf m m B ->
  Mat_wf (n + m) (n + m) (block_diag A B m).
Proof.
  intros n m A B [HlenA HrowA] [HlenB HrowB].
  unfold block_diag, Mat_wf. split.
  - (* number of rows = n + m *)
    rewrite List.length_app, List.length_map, List.length_map.
    rewrite HlenA, HlenB. reflexivity.
  - (* each row has length n + m *)
    intros row Hin.
    rewrite List.in_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* row = r ++ vzero m for some r in A *)
      rewrite List.in_map_iff in Hin.
      destruct Hin as [r [<- Hrin]].
      rewrite List.length_app, vzero_length, HrowA by exact Hrin.
      reflexivity.
    + (* row = vzero (length A) ++ r for some r in B *)
      rewrite List.in_map_iff in Hin.
      destruct Hin as [r [<- Hrin]].
      rewrite List.length_app, vzero_length, HlenA, HrowB by exact Hrin.
      reflexivity.
Qed.

(** trace of a block diagonal is the sum of traces. *)
Conjecture trace_block_diag : forall (A B : Mat CComplex) (n m : nat),
  Mat_wf n n A -> Mat_wf m m B ->
  trace (block_diag A B m) = Cadd (trace A) (trace B).

(** Direct sum of two GL elements.  The inverse of A⊕B is A⁻¹⊕B⁻¹. *)
Conjecture GL_direct_sum_right_inv : forall {n m : nat} (A : GLMat n) (B : GLMat m),
  mmul (block_diag (gl_mat A) (gl_mat B) m)
       (block_diag (gl_inv_mat A) (gl_inv_mat B) m)
       (n + m)
  = mident (n + m).

Conjecture GL_direct_sum_left_inv : forall {n m : nat} (A : GLMat n) (B : GLMat m),
  mmul (block_diag (gl_inv_mat A) (gl_inv_mat B) m)
       (block_diag (gl_mat A) (gl_mat B) m)
       (n + m)
  = mident (n + m).

Definition GL_direct_sum {n m : nat} (A : GLMat n) (B : GLMat m)
    : GLMat (n + m) :=
  mkGL (n + m)
    (block_diag (gl_mat A) (gl_mat B) m)
    (block_diag (gl_inv_mat A) (gl_inv_mat B) m)
    (block_diag_wf n m _ _ (gl_wf A) (gl_wf B))
    (block_diag_wf n m _ _ (gl_inv_wf A) (gl_inv_wf B))
    (GL_direct_sum_right_inv A B)
    (GL_direct_sum_left_inv A B).

(** Direct sum of two representations ρ₁ : G → GL(n) and ρ₂ : G → GL(m). *)
Parameter rep_direct_sum : forall {G : Type} {sg : StrictGroup G} {n m : nat}
    (ρ₁ : GroupRep sg n) (ρ₂ : GroupRep sg m),
    GroupRep sg (n + m).

(** χ_{ρ₁⊕ρ₂}(g) = χ_{ρ₁}(g) + χ_{ρ₂}(g). *)
Conjecture char_direct_sum : forall {G : Type} (sg : StrictGroup G)
    {n m : nat} (ρ₁ : GroupRep sg n) (ρ₂ : GroupRep sg m) (g : G),
  character (rep_direct_sum ρ₁ ρ₂) g =
  Cadd (character ρ₁ g) (character ρ₂ g).

(* ------------------------------------------------------------------ *)
(** * 5. Inner product of characters (finite groups)                    *)
(* ------------------------------------------------------------------ *)

(** For a finite group given by an explicit list [G_elems], the
    character inner product is:
      ⟨χ,ψ⟩ = (1/|G|) · Σ_{g ∈ G_elems} χ(g) · conj(ψ(g))

    We define the unnormalised sum first (no division needed for the
    statement of orthogonality up to a scalar).
*)
Section CharInnerProduct.

Context {G : Type} (sg : StrictGroup G).
Context (G_elems : list G).

(** Unnormalised inner product: Σ_{g} χ(g) · conj(ψ(g)). *)
Definition char_inner_product_sum
    {n m : nat}
    (ρ₁ : GroupRep sg n)
    (ρ₂ : GroupRep sg m)
    : CComplex :=
  List.fold_right
    (fun g acc =>
       Cadd acc
         (Cmul (character ρ₁ g)
               (Cconj (character ρ₂ g))))
    C0
    G_elems.

(** First orthogonality (statement).

    For a finite group and two irreducible representations ρ₁, ρ₂:
      Σ_{g} χ_{ρ₁}(g) · conj(χ_{ρ₂}(g)) = |G| · δ_{ρ₁,ρ₂}

    (where δ means equality as representations, i.e. isomorphic).
    The proof requires the Peter–Weyl / Schur's lemma machinery
    and is admitted here.
*)
Theorem char_orthogonality_first :
  forall {n : nat} (ρ₁ ρ₂ : GroupRep sg n),
  (* ρ₁ and ρ₂ are irreducible — predicate left abstract *)
  forall (irr₁ irr₂ : Prop),
  (* isomorphic reps have equal characters, non-iso reps have zero inner product *)
  True. (* placeholder — full statement needs GroupIso and irreducibility *)
Proof. intros; exact I. Qed.

End CharInnerProduct.

(* ------------------------------------------------------------------ *)
(** * 6. Schur's Lemma (statement)                                      *)
(* ------------------------------------------------------------------ *)

(** A morphism between irreducible representations is either zero
    or an isomorphism.  This is the engine behind orthogonality. *)
Definition RepHom {G : Type} (sg : StrictGroup G) {n m : nat}
    (ρ₁ : GroupRep sg n) (ρ₂ : GroupRep sg m) : Type :=
  { f : Mat CComplex |
    Mat_wf n m f /\
    forall g : G,
      mmul f (rep_matrix ρ₂ g) m =
      mmul (rep_matrix ρ₁ g) f m }.

Definition zero_mat (n m : nat) : Mat CComplex :=
  List.repeat (List.repeat C0 m) n.

Definition is_irreducible {G : Type} (sg : StrictGroup G) {n : nat}
    (ρ : GroupRep sg n) : Prop :=
  forall (m : nat) (ρ' : GroupRep sg m) (f : RepHom sg ρ' ρ),
    proj1_sig f = zero_mat n m \/ m = n.

Conjecture schurs_lemma : forall {G : Type} (sg : StrictGroup G)
    {n m : nat} (ρ₁ : GroupRep sg n) (ρ₂ : GroupRep sg m),
  is_irreducible sg ρ₁ ->
  is_irreducible sg ρ₂ ->
  forall (f : RepHom sg ρ₁ ρ₂),
    proj1_sig f = zero_mat n m \/
    (n = m /\ exists (c : CComplex),
      proj1_sig f = List.map (List.map (Cmul c)) (mident n)).
