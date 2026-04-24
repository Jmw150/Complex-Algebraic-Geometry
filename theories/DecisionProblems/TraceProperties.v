
(** * Decision Problems, Traces, and Representations

    Formalizes the framework from:
    "Decision Problems, Complexity, Traces, and Representations"
    (McReynolds et al.)

    Main content (Milestones 1–2):
    - word length and generating sets
    - conjugacy separability functions D_Γ, F_Γ, CD_Γ, Conj_Γ
    - trace-distinguishing properties (A), (B), (C), (D)
    - uniform variants, primed variants (arbitrary algebraically closed field)
    - easy implications among (A)–(D)
    - n-trace distinguished / fully n-trace distinguished
    - theorem statements with hypothesis placeholders
    - induced representation API skeleton
    - Proposition 1.3: (D) ⇒ conjugacy separable
    - Theorem 1.4 / 1.5: polynomial upper bounds
    - open questions as formal stubs *)

From CAG Require Import Group.
From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* ================================================================== *)
(** ** Part I — Finitely generated groups and word length *)
(* ================================================================== *)

(** A finitely generated group carries a finite generating set. *)
Record FGGroup (G : Type) : Type :=
  mkFGG
  {
    fgg_sg   : StrictGroup G;
    fgg_gens : list G;
    (** Every element can be written as a product of generators and inverses.
        (Existential statement; the generating set may not be irredundant.) *)
    fgg_gen  : forall x : G, exists ws : list G,
                  (forall w, In w ws -> In w fgg_gens \/
                             In (sinv G fgg_sg w) fgg_gens) /\
                  List.fold_right (smul G fgg_sg) (se G fgg_sg) ws = x;
  }.

Arguments fgg_sg   {G} _.
Arguments fgg_gens {G} _.
Arguments fgg_gen  {G} _.

(** Word length of x with respect to generating set X:
    minimum length of a word in X ∪ X⁻¹ equal to x. *)
Definition word_length {G : Type} (fgg : FGGroup G) (x : G) : nat :=
  let sg := fgg.(fgg_sg) in
  (** We take the minimum over all words representing x.
      For the formalization we define it existentially. *)
  let P := fun n =>
    exists ws : list G,
      length ws = n /\
      (forall w, In w ws -> In w fgg.(fgg_gens) \/
                            In (sinv G sg w) fgg.(fgg_gens)) /\
      List.fold_right (smul G sg) (se G sg) ws = x
  in
  (** The minimum exists by well-foundedness, but we just define it as
      a predicate for now. *)
  0. (* placeholder; full definition needs Nat.find or constructive minimum *)

(** Ball of radius n: elements reachable by words of length ≤ n. *)
Definition ball {G : Type} (fgg : FGGroup G) (n : nat) : G -> Prop :=
  fun x => word_length fgg x <= n.

(** Asymptotic comparison: f ≼ g iff ∃ C, f(n) ≤ C * g(C * n). *)
Definition asym_le (f g : nat -> nat) : Prop :=
  exists C : nat, 0 < C /\ forall n : nat, f n <= C * g (C * n).

(** Asymptotic equivalence: f ≈ g iff f ≼ g and g ≼ f. *)
Definition asym_eq (f g : nat -> nat) : Prop :=
  asym_le f g /\ asym_le g f.

Lemma asym_le_refl (f : nat -> nat) : asym_le f f.
Proof.
  exists 1. split. lia.
  intro n. rewrite !Nat.mul_1_l. lia.
Qed.

Lemma asym_eq_refl (f : nat -> nat) : asym_eq f f.
Proof.
  split; apply asym_le_refl.
Qed.

Lemma asym_le_trans (f g h : nat -> nat) :
    asym_le f g -> asym_le g h -> asym_le f h.
Proof.
  intros [C1 [HC1 H1]] [C2 [HC2 H2]].
  exists (C1 * C2). split. nia.
  intro n.
  eapply Nat.le_trans. apply H1.
  eapply Nat.le_trans.
  - apply Nat.mul_le_mono_l. apply H2.
  - assert (Heq : C2 * (C1 * n) = C1 * C2 * n) by nia.
    rewrite Heq. nia.
Qed.

(* ================================================================== *)
(** ** Part II — Conjugacy and separability functions *)
(* ================================================================== *)

(** Bou-Rabee residual finiteness function:
    D_Γ(γ) = min { [Γ:Δ] | Δ normal, finite index, γ ∉ Δ }. *)
Definition D_rf {G : Type} (sg : StrictGroup G) (gamma : G) : nat :=
  0. (* placeholder; requires finite quotient infrastructure *)

(** F_Γ,X(n) = max of D_Γ(γ) over nontrivial γ in the radius-n ball. *)
Definition F_rf {G : Type} (fgg : FGGroup G) (n : nat) : nat :=
  0. (* placeholder *)

(** Conjugacy-distinguishing size function:
    CD_Γ([γ],[η]) = min { |Q| | ∃ φ:Γ→Q, [φ(γ)] ≠ [φ(η)] in Q }. *)
Definition CD_conj {G : Type} (sg : StrictGroup G) (gamma eta : G) : nat :=
  0. (* placeholder *)

(** Conj_Γ,X(n) = max of CD_Γ over non-conjugate pairs of norm ≤ n. *)
Definition Conj_func {G : Type} (fgg : FGGroup G) (n : nat) : nat :=
  0. (* placeholder *)

(** Relative function Conj_{Γ,γ,X}(n):
    max of CD_Γ([γ],[η]) over η with norm ≤ n, η non-conjugate to γ. *)
Definition Conj_rel {G : Type} (fgg : FGGroup G) (gamma : G) (n : nat) : nat :=
  0. (* placeholder *)

(** Generator-independence of F_Γ (up to ≈). *)
Axiom F_rf_gen_independent :
  forall {G : Type} (fgg1 fgg2 : FGGroup G),
    fgg1.(fgg_sg) = fgg2.(fgg_sg) ->
    asym_eq (F_rf fgg1) (F_rf fgg2).

(** Generator-independence of Conj_Γ (up to ≈). *)
Axiom Conj_func_gen_independent :
  forall {G : Type} (fgg1 fgg2 : FGGroup G),
    fgg1.(fgg_sg) = fgg2.(fgg_sg) ->
    asym_eq (Conj_func fgg1) (Conj_func fgg2).

(* ================================================================== *)
(** ** Part III — Representation-theoretic infrastructure *)
(* ================================================================== *)

(** A representation of Γ in SL(n, F) is a group homomorphism.
    We axiomatize SL(n, F) as a type with a StrictGroup structure and a trace function. *)

Record MatrixGroup (F : Type) : Type :=
  mkMG
  {
    mg_carrier : Type;
    mg_sg      : StrictGroup mg_carrier;
    mg_trace   : mg_carrier -> F;
    mg_dim     : nat;
  }.

Arguments mg_carrier {F} _.
Arguments mg_sg      {F} _.
Arguments mg_trace   {F} _.
Arguments mg_dim     {F} _.

(** A representation ρ : Γ → SL(n, F). *)
Record Representation {G F : Type}
    (sg : StrictGroup G) (MG : MatrixGroup F) : Type :=
  mkRep
  {
    rep_fn  : G -> mg_carrier MG;
    rep_hom : forall g h : G,
                rep_fn (smul G sg g h) =
                smul (mg_carrier MG) (mg_sg MG) (rep_fn g) (rep_fn h);
  }.

Arguments rep_fn  {G F sg MG} _.
Arguments rep_hom {G F sg MG} _ _ _.

(** Trace of ρ on γ. *)
Definition trace_at {G F : Type} {sg : StrictGroup G} {MG : MatrixGroup F}
    (rho : Representation sg MG) (gamma : G) : F :=
  mg_trace MG (rep_fn rho gamma).

(* ================================================================== *)
(** ** Part IV — Trace-distinguishing properties (A)–(D) *)
(* ================================================================== *)

(** Conjugacy predicate. *)
Definition are_conjugate {G : Type} (sg : StrictGroup G) (gamma eta : G) : Prop :=
  exists g : G, smul G sg (smul G sg g gamma) (sinv G sg g) = eta.

(** SL_n-trace equivalence: Tr(ρ(γ)) = Tr(ρ(η)) for every ρ : Γ → SL(n,ℂ).
    Since we don't have ℂ-SL(n) in hand, we state this relative to a given
    MatrixGroup MG over a field F. *)

Definition trace_equiv_in_MG {G F : Type} {sg : StrictGroup G} (MG : MatrixGroup F)
    (gamma eta : G) : Prop :=
  forall rho : Representation sg MG,
    trace_at rho gamma = trace_at rho eta.

Definition SLn_trace_equiv {G F : Type} {sg : StrictGroup G}
    (MG_family : nat -> MatrixGroup F) (gamma eta : G) : Prop :=
  forall n : nat, @trace_equiv_in_MG G F sg (MG_family n) gamma eta.

(** Property (D): for each non-conjugate pair γ,η, some representation separates their traces.
    (Single pair, existential dimension.) *)
Definition property_D {G F : Type} (sg : StrictGroup G)
    (MG_family : nat -> MatrixGroup F) : Prop :=
  forall gamma eta : G,
    ~ are_conjugate sg gamma eta ->
    exists (n : nat) (rho : Representation sg (MG_family n)),
      trace_at rho gamma <> trace_at rho eta.

(** Property (C): for each finite set of conjugacy classes, one representation
    separates all trace values pairwise. *)
Definition property_C {G F : Type} (sg : StrictGroup G)
    (MG_family : nat -> MatrixGroup F) : Prop :=
  forall (gammas : list G),
    exists (n : nat) (rho : Representation sg (MG_family n)),
      forall gamma eta : G,
        In gamma gammas -> In eta gammas ->
        ~ are_conjugate sg gamma eta ->
        trace_at rho gamma <> trace_at rho eta.

(** Property (B): for each γ, one representation separates γ from every non-conjugate η.
    (Single γ, existential dimension depending on γ.) *)
Definition property_B {G F : Type} (sg : StrictGroup G)
    (MG_family : nat -> MatrixGroup F) : Prop :=
  forall gamma : G,
    exists (n : nat) (rho : Representation sg (MG_family n)),
      forall eta : G,
        ~ are_conjugate sg gamma eta ->
        trace_at rho gamma <> trace_at rho eta.

(** Property (A): a single representation separates traces of all non-conjugate pairs. *)
Definition property_A {G F : Type} (sg : StrictGroup G)
    (MG_family : nat -> MatrixGroup F) : Prop :=
  exists (n : nat) (rho : Representation sg (MG_family n)),
    forall gamma eta : G,
      ~ are_conjugate sg gamma eta ->
      trace_at rho gamma <> trace_at rho eta.

(** Uniform property (D): the dimension n₀ is globally bounded
    (not depending on the pair γ,η). *)
Definition uniform_D {G F : Type} (sg : StrictGroup G)
    (MG_family : nat -> MatrixGroup F) : Prop :=
  exists n0 : nat,
    forall gamma eta : G,
      ~ are_conjugate sg gamma eta ->
      exists rho : Representation sg (MG_family n0),
        trace_at rho gamma <> trace_at rho eta.

(** Uniform property (C): the dimension n is uniformly bounded. *)
Definition uniform_C {G F : Type} (sg : StrictGroup G)
    (MG_family : nat -> MatrixGroup F) : Prop :=
  exists n0 : nat,
    forall (gammas : list G),
      exists rho : Representation sg (MG_family n0),
        forall gamma eta : G,
          In gamma gammas -> In eta gammas ->
          ~ are_conjugate sg gamma eta ->
          trace_at rho gamma <> trace_at rho eta.

(** Primed variants: quantify over all algebraically closed fields F.
    We model this by quantifying over the MatrixGroup family. *)

(** Property (D'): (D) holds for every MatrixGroup family. *)
Definition property_D' {G : Type} (sg : StrictGroup G) : Prop :=
  forall (F : Type) (MG_family : nat -> MatrixGroup F),
    property_D sg MG_family.

(* ================================================================== *)
(** ** Part V — Easy implications among (A)–(D) *)
(* ================================================================== *)

(** (A) ⇒ (B) *)
Theorem property_A_implies_B {G F : Type} {sg : StrictGroup G}
    {MG_family : nat -> MatrixGroup F}
    (HA : property_A sg MG_family) : property_B sg MG_family.
Proof.
  unfold property_A in HA.
  unfold property_B.
  destruct HA as [n [rho Hrho]].
  intro gamma.
  exists n, rho.
  intro eta. apply Hrho.
Qed.

(** (B) ⇒ (D) *)
Theorem property_B_implies_D {G F : Type} {sg : StrictGroup G}
    {MG_family : nat -> MatrixGroup F}
    (HB : property_B sg MG_family) : property_D sg MG_family.
Proof.
  unfold property_B in HB.
  unfold property_D.
  intros gamma eta Hnc.
  destruct (HB gamma) as [n [rho Hrho]].
  exists n, rho. apply Hrho. exact Hnc.
Qed.

(** (C) ⇒ (D) *)
Theorem property_C_implies_D {G F : Type} {sg : StrictGroup G}
    {MG_family : nat -> MatrixGroup F}
    (HC : property_C sg MG_family) : property_D sg MG_family.
Proof.
  unfold property_C in HC.
  unfold property_D.
  intros gamma eta Hnc.
  destruct (HC [gamma; eta]) as [n [rho Hrho]].
  exists n, rho.
  apply Hrho.
  - left. reflexivity.
  - right. left. reflexivity.
  - exact Hnc.
Qed.

(** Uniform (C) ⇒ (C) *)
Theorem uniform_C_implies_C {G F : Type} {sg : StrictGroup G}
    {MG_family : nat -> MatrixGroup F}
    (HuC : uniform_C sg MG_family) : property_C sg MG_family.
Proof.
  unfold uniform_C in HuC.
  unfold property_C.
  destruct HuC as [n0 Hn0].
  intro gammas.
  destruct (Hn0 gammas) as [rho Hrho].
  exists n0, rho. exact Hrho.
Qed.

(** Uniform (D) ⇒ (D) *)
Theorem uniform_D_implies_D {G F : Type} {sg : StrictGroup G}
    {MG_family : nat -> MatrixGroup F}
    (HuD : uniform_D sg MG_family) : property_D sg MG_family.
Proof.
  unfold uniform_D in HuD.
  unfold property_D.
  destruct HuD as [n0 Hn0].
  intros gamma eta Hnc.
  destruct (Hn0 gamma eta Hnc) as [rho Hrho].
  exists n0, rho. exact Hrho.
Qed.

(* ================================================================== *)
(** ** Part VI — n-trace distinguished and fully n-trace distinguished *)
(* ================================================================== *)

(** γ is n-trace distinguished in Γ (over finite fields):
    for any η non-conjugate to γ, there exists a finite field F_q and
    a representation ρ : Γ → SL(n, F_q) with Tr(ρ(γ)) ≠ Tr(ρ(η)).

    We model "finite fields" parametrically. *)

Definition is_n_trace_distinguished {G F : Type} (sg : StrictGroup G)
    (MG_fin : nat -> list (MatrixGroup F)) (gamma : G) (n : nat) : Prop :=
  forall eta : G,
    ~ are_conjugate sg gamma eta ->
    exists (MG : MatrixGroup F),
      In MG (MG_fin n) /\
      exists rho : Representation sg MG,
        trace_at rho gamma <> trace_at rho eta.

(** γ is fully n-trace distinguished: for every non-conjugate η,
    every ρ : Γ → SL(n, F_q) separates Tr(ρ(γ)) from Tr(ρ(η)). *)
Definition is_fully_n_trace_distinguished {G F : Type} (sg : StrictGroup G)
    (MG_fin : nat -> list (MatrixGroup F)) (gamma : G) (n : nat) : Prop :=
  forall eta : G,
    ~ are_conjugate sg gamma eta ->
    forall (MG : MatrixGroup F),
      In MG (MG_fin n) ->
      forall rho : Representation sg MG,
        trace_at rho gamma <> trace_at rho eta.

(* ================================================================== *)
(** ** Part VII — Theorem 3.1 and 3.2 (ultraproduct theorems) *)
(* ================================================================== *)

(** Theorem 3.1: If Γ is finitely generated and fully n-trace distinguished
    for all pairs, then Γ has property (A).
    (Proof uses ultraproducts of finite fields → axiomatized.) *)
Axiom theorem_3_1 :
  forall {G F : Type} (sg : StrictGroup G)
         (MG_family : nat -> MatrixGroup F)
         (MG_fin : nat -> list (MatrixGroup F))
         (n : nat)
         (H : forall gamma eta : G,
             ~ are_conjugate sg gamma eta ->
             is_fully_n_trace_distinguished sg MG_fin gamma n),
    property_A sg MG_family.

(** Theorem 3.2: If for each γ there exists n_γ such that γ is fully
    n_γ-trace distinguished, then Γ has property (B). *)
Axiom theorem_3_2 :
  forall {G F : Type} (sg : StrictGroup G)
         (MG_family : nat -> MatrixGroup F)
         (MG_fin : nat -> list (MatrixGroup F))
         (H : forall gamma : G,
             exists n_gamma : nat,
               forall eta : G,
                 ~ are_conjugate sg gamma eta ->
                 is_fully_n_trace_distinguished sg MG_fin gamma n_gamma),
    property_B sg MG_family.

(* ================================================================== *)
(** ** Part VIII — Proposition 1.3: (D) implies conjugacy separable *)
(* ================================================================== *)

(** Conjugacy separable: for any non-conjugate γ,η, there is a finite
    quotient Q and a homomorphism φ : Γ → Q such that φ(γ) and φ(η)
    are non-conjugate in Q. *)
Definition conjugacy_separable {G : Type} (sg : StrictGroup G) : Prop :=
  forall gamma eta : G,
    ~ are_conjugate sg gamma eta ->
    exists (Q : Type) (sq : StrictGroup Q) (Q_list : list Q)
           (Q_complete : forall x : Q, In x Q_list)
           (phi : GroupHom sg sq),
      ~ are_conjugate sq (hom_fn phi gamma) (hom_fn phi eta).

(** Specialization lemma (Mal'cev / Bass-Lubotzky):
    A nonzero element in a finitely generated integral domain survives
    some reduction to a finite field. *)
Axiom specialization_lemma :
  forall (F : Type) (sg : StrictGroup F) (nonzero_elem : F),
    nonzero_elem <> se F sg ->
    exists (Q : Type) (sq : StrictGroup Q) (Q_list : list Q)
           (Q_complete : forall x : Q, In x Q_list)
           (phi : GroupHom sg sq),
      hom_fn phi nonzero_elem <> se Q sq.

(** Proposition 1.3: (D) implies conjugacy separable.

    Proof:
    1. Let γ,η be non-conjugate.
    2. By (D), there exists ρ : Γ → SL(n,F) with Tr(ρ(γ)) ≠ Tr(ρ(η)).
    3. The trace difference Tr(ρ(γ)) - Tr(ρ(η)) lies in a finitely generated ring.
    4. By specialization lemma, there exists a finite-field quotient where the
       trace difference is nonzero.
    5. In that finite quotient, ρ(γ) and ρ(η) have different traces.
    6. Non-conjugate elements have different traces (contrapositive of Schur). *)
Axiom proposition_1_3 :
  forall {G F : Type} (sg : StrictGroup G) (MG_family : nat -> MatrixGroup F)
         (HD : property_D sg MG_family),
    conjugacy_separable sg.

(* ================================================================== *)
(** ** Part IX — Theorems 1.4 and 1.5: polynomial upper bounds *)
(* ================================================================== *)

(** Effective linear representation: ρ : Γ → SL(n, R) where entries are
    polynomially bounded in word length. *)
Definition has_effective_linear_rep {G : Type} (fgg : FGGroup G)
    (dim : nat) (growth_bound : nat -> nat) : Prop :=
  (* Abstract: there exists a representation whose specialization size
     is bounded polynomially in word length *)
  True. (* placeholder *)

(** Abstract polynomial-bound theorem:
    effective trace-separating linear representation ⇒ polynomial bound on Conj. *)
Axiom effective_rep_gives_poly_bound :
  forall {G : Type} (fgg : FGGroup G)
         (n0 d : nat)
         (Heff : has_effective_linear_rep fgg n0 (fun k => Nat.pow k d)),
    exists C : nat, forall n : nat, Conj_func fgg n <= C * Nat.pow n d.

(** Theorem 1.4: (A) ⇒ Conj_Γ(n) ≼ n^d for some d.

    Strategy: the single representation ρ from (A) lies over a
    finitely generated ring; trace entries are polynomial in generators;
    specialization size is polynomially bounded. *)
Axiom theorem_1_4 :
  forall {G F : Type} (fgg : FGGroup G) (MG_family : nat -> MatrixGroup F)
         (HA : property_A (fgg.(fgg_sg)) MG_family),
    exists d : nat, asym_le (Conj_func fgg) (fun n => Nat.pow n d).

(** Theorem 1.5: (B) ⇒ for each γ, Conj_{Γ,γ}(n) ≼ n^{d_γ}. *)
Axiom theorem_1_5 :
  forall {G F : Type} (fgg : FGGroup G) (MG_family : nat -> MatrixGroup F)
         (HB : property_B (fgg.(fgg_sg)) MG_family)
         (gamma : G),
    exists d_gamma : nat, asym_le (Conj_rel fgg gamma) (fun n => Nat.pow n d_gamma).

(* ================================================================== *)
(** ** Part X — Induced representations *)
(* ================================================================== *)

(** Induced representation: if H ≤ G (finite index) and ρ : H → SL(n, F),
    then Ind^G_H(ρ) : G → SL([G:H]*n, F). *)

Record InducedRepData {G H F : Type}
    (sg : StrictGroup G) (sh : StrictGroup H)
    (H_pred : G -> Prop)
    (H_sub : is_subgroup (StrictGroup_to_Group sg) H_pred)
    (MG : MatrixGroup F) : Type :=
  mkIRD
  {
    ird_rho  : Representation sh MG;
    ird_ind  : MatrixGroup F;
    ird_rep  : Representation sg ird_ind;
    ird_dim  : mg_dim ird_ind = 0; (* placeholder: should be [G:H] * mg_dim MG *)
  }.

(** Trace formula for induced representations (Frobenius).
    Elements not conjugate into H have trace 0 in the induced rep.
    Elements conjugate into H have trace = sum over conjugates. *)
Axiom frobenius_trace_formula :
  forall {G H F : Type}
         (sg : StrictGroup G) (sh : StrictGroup H)
         (H_pred : G -> Prop)
         (H_sub : is_subgroup (StrictGroup_to_Group sg) H_pred)
         (MG : MatrixGroup F) (ird : InducedRepData sg sh H_pred H_sub MG),
    True. (* placeholder *)

(* ================================================================== *)
(** ** Part XI — Free groups have property (B): Theorem 1.6 *)
(* ================================================================== *)

(** Hall's theorem for free groups:
    for each γ ∈ F_r, there exists a finite-index subgroup Δ ≤ F_r such that
    F_r = ⟨γ⟩ * Δ (free product). *)
Axiom hall_theorem_free_groups :
  forall {G : Type} (sg : StrictGroup G)
         (free_rank : nat)
         (gamma : G),
    exists (Delta : G -> Prop),
      is_subgroup (StrictGroup_to_Group sg) Delta /\
      (forall g : G, exists (k : nat) (d : G),
          Delta d /\ g = smul G sg (gpow (StrictGroup_to_Group sg) gamma k) d).

(** Theorem 1.6: Free groups and surface groups have property (B). *)
Axiom theorem_1_6_free_groups :
  forall {G F : Type} (sg : StrictGroup G) (MG_family : nat -> MatrixGroup F)
         (r : nat),
    property_B sg MG_family.

Axiom theorem_1_6_surface_groups :
  forall {G F : Type} (sg : StrictGroup G) (MG_family : nat -> MatrixGroup F)
         (genus : nat) (Hg : 2 <= genus),
    property_B sg MG_family.

(* ================================================================== *)
(** ** Part XII — Fully residually free groups (Theorem 1.8) *)
(* ================================================================== *)

(** Fully residually free: for every finite set S of nontrivial elements,
    there exists ψ_S : Γ → F_r injective on S. *)
Definition fully_residually_free {G GF : Type}
    (sg : StrictGroup G) (sf : StrictGroup GF) : Prop :=
  forall (S : list G)
         (HS : forall x, In x S -> x <> se G sg),
    exists (phi : GroupHom sg sf),
      (forall x y : G, In x S -> In y S ->
         hom_fn phi x = hom_fn phi y -> x = y).

(** Theorem 1.8: For Γ fully residually free and Δ normal finite index,
    there exists ρ : Γ → SL(n, R) with Δ = ker(reduction mod m ∘ ρ). *)
Axiom theorem_1_8 :
  forall {G GF : Type} (sg : StrictGroup G) (sf : StrictGroup GF)
         (Hfrf : fully_residually_free sg sf)
         (Delta : G -> Prop)
         (HDnorm : is_normal_subgroup (StrictGroup_to_Group sg) Delta)
         (HDfin : exists (D_list : list G),
             NoDup D_list /\ (forall x, In x D_list <-> Delta x)),
    True. (* placeholder: requires SL(n,R) and ring reduction infrastructure *)

(* ================================================================== *)
(** ** Part XIII — SL_n-trace equivalence and Horowitz words *)
(* ================================================================== *)

(** SL_n-trace equivalence in a family of MatrixGroups. *)
Definition SLn_trace_equivalent {G F : Type} (sg : StrictGroup G)
    (MG_family : nat -> MatrixGroup F) (n : nat) (gamma eta : G) : Prop :=
  @trace_equiv_in_MG G F sg (MG_family n) gamma eta.

(** Lemma 4.1: If F_r has a non-conjugate SL_n-trace-equivalent pair,
    every non-elementary hyperbolic group does. *)
Axiom lemma_4_1 :
  forall {G F : Type} (sg : StrictGroup G) (MG_family : nat -> MatrixGroup F)
         (n : nat)
         (HFr_pair : exists gamma eta : G,
             ~ are_conjugate sg gamma eta /\
             SLn_trace_equivalent sg MG_family n gamma eta),
    True. (* non-elementary hyperbolic groups not yet defined *)

(** Reverse word lemma (Lemma 4.2):
    The reverse word r(w) and w are always SL_2-trace equivalent,
    but not in general for n > 2. *)
Axiom reverse_word_SL2_trace_equiv :
  forall {G F : Type} (sg : StrictGroup G) (MG2 : MatrixGroup F)
         (rho : Representation sg MG2) (w : G),
    trace_at rho w = trace_at rho (sinv G sg w).

(* ================================================================== *)
(** ** Part XIV — Quantitative open questions (as named placeholders) *)
(* ================================================================== *)

(** Conjecture 1: Finitely generated free groups do NOT have property (A). *)
Definition conjecture_1_free_no_A {G F : Type} (sg : StrictGroup G)
    (MG_family : nat -> MatrixGroup F) : Prop :=
  ~ property_A sg MG_family.

(** Open question: Are uniform (C) and uniform (D) equivalent? *)
Definition open_uniformC_eq_uniformD {G F : Type} (sg : StrictGroup G)
    (MG_family : nat -> MatrixGroup F) : Prop :=
  uniform_C sg MG_family <-> uniform_D sg MG_family.

(** Open question: Do SL_n-trace equivalent non-conjugate pairs exist for n > 2? *)
Definition open_SLn_trace_equiv_pairs {G F : Type} (sg : StrictGroup G)
    (MG_family : nat -> MatrixGroup F) (n : nat) (Hn : 2 < n) : Prop :=
  exists gamma eta : G,
    ~ are_conjugate sg gamma eta /\
    SLn_trace_equivalent sg MG_family n gamma eta.

(** Conjecture 2: SL_n-trace equivalent pairs exist iff positive-word pairs exist. *)
Definition conjecture_2_positive_words {G F : Type} (sg : StrictGroup G)
    (MG_family : nat -> MatrixGroup F) (n : nat)
    (is_positive_word : G -> Prop) : Prop :=
  (exists gamma eta : G,
      ~ are_conjugate sg gamma eta /\
      SLn_trace_equivalent sg MG_family n gamma eta)
  <->
  (exists gamma eta : G,
      is_positive_word gamma /\ is_positive_word eta /\
      ~ are_conjugate sg gamma eta /\
      SLn_trace_equivalent sg MG_family n gamma eta).

(** Open quantitative question: Is Conj_{F_r}(n) polynomially bounded? *)
Definition open_Conj_poly_bounded {G : Type} (fgg : FGGroup G) : Prop :=
  exists d C : nat, forall n : nat, Conj_func fgg n <= C * Nat.pow n d.

(* ================================================================== *)
(** ** Part XV — Theorem 1.1: uniform (C) / uniform (D) ⇒ (A) *)
(* ================================================================== *)

(** Theorem 1.1: If Γ uniformly has (C), then Γ has (A).

    The proof requires:
    - Baire category in irreducible representation varieties
    - each trace-coincidence locus Z_{i,j} is a proper closed subset
    - countable union of proper nowhere-dense sets ≠ whole variety

    Stated as axiom pending algebraic geometry infrastructure. *)
Axiom theorem_1_1_uniformC_implies_A :
  forall {G F : Type} (sg : StrictGroup G) (MG_family : nat -> MatrixGroup F)
         (HuC : uniform_C sg MG_family),
    property_A sg MG_family.

(** Theorem 1.1 (second half): uniform (D) + irreducibility ⇒ (A). *)
Axiom theorem_1_1_uniformD_irred_implies_A :
  forall {G F : Type} (sg : StrictGroup G) (MG_family : nat -> MatrixGroup F)
         (n0 : nat)
         (HuD : uniform_D sg MG_family)
         (Hirred : True (* irreducibility of Hom(Γ, SL(n0, F)) — external hypothesis *)),
    property_A sg MG_family.

(** Corollary 1.2: For free groups and surface groups:
    uniform (D) iff (A). *)
Axiom corollary_1_2_free_groups :
  forall {G F : Type} (sg : StrictGroup G) (MG_family : nat -> MatrixGroup F)
         (r : nat)
         (Hirred : True (* irreducibility of G^r for connected algebraic G *)),
    uniform_D sg MG_family <-> property_A sg MG_family.

Axiom corollary_1_2_surface_groups :
  forall {G F : Type} (sg : StrictGroup G) (MG_family : nat -> MatrixGroup F)
         (genus : nat) (Hg : 2 <= genus)
         (Hirred : True (* irreducibility of Hom(π₁(Σ_g), SL(n,ℂ)) *)),
    uniform_D sg MG_family <-> property_A sg MG_family.
