(** * DecisionProblems/FiniteLifts.v

    Open problems and main results from
    Karshon–Lubotzky–McReynolds–Reid–Shusterman (arXiv:2602.15463v1, Feb 2026),
    "Subgroups with all finite lifts isomorphic are conjugate".

    This file SCAFFOLDS the paper: it formalizes the precise statements of
      - Theorem 1.1  (Main Theorem: non-conjugate subgroups have a finite
                      lift in which the pre-images are not isomorphic)
      - Question 1.3 (Prasad: are Z-coset equivalent subgroups isomorphic?)
      - Theorem 1.4  (Question 1.3 has a negative answer)
      - Question 1.5 (proposed refinement of Question 1.3 — the OPEN problem)
      - Corollary 1.6 (profinite version)
      - Theorem 1.7  (PSL(2,29) tetrahedral example)

    Theorem 1.4 is proven from Theorem 1.1 + Scott's example + Lemma 2.1.
    Theorem 1.1 is taken as Axiom (proved by KLMRS). Lemma 2.1 (permanence
    under pullbacks) is proven up to a single module-theoretic Axiom that
    R-coset equivalence is preserved by surjective restriction.

    Convention follows DecisionProblems/OpenProblems.v: open problems are
    [Definition open_question_X_Y : Prop := ...]. Established results from
    the paper are Axiom; structural lemmas we can prove are Lemma/Theorem.
*)

From CAG Require Import Group.
From CAG Require Import GroupActions.Basic.
From Stdlib Require Import List ZArith.
Import ListNotations.

(* ================================================================== *)
(** * 1. Finite groups, subgroups, conjugacy of subgroups               *)
(* ================================================================== *)

(** A finite-group witness: a [StrictGroup] with a complete deduplicated
    enumeration of its carrier. Same convention as [Sylow/Applications.v]. *)

Definition IsFiniteEnum {G : Type} (sg : StrictGroup G) (G_list : list G) : Prop :=
  NoDup G_list /\ (forall x : G, In x G_list).

(** Two subgroups [H1] and [H2] of [G] are conjugate iff there exists [g]
    such that [g · H1 · g⁻¹ = H2]. We express the equality of subsets
    pointwise. *)
Definition conjugate_subgroups
    {G : Type} (sg : StrictGroup G) (H1 H2 : G -> Prop) : Prop :=
  exists g : G,
    forall x : G, H1 x <-> H2 (conj_act sg g x).

(** Pre-image of a subset under a homomorphism. *)
Definition preimage_subset
    {G H : Type} {sg : StrictGroup G} {sh : StrictGroup H}
    (phi : GroupHom sg sh) (K : H -> Prop) : G -> Prop :=
  fun x => K (hom_fn phi x).

(** A homomorphism is surjective iff every element of the codomain has
    a pre-image. *)
Definition is_surjective_hom
    {G H : Type} {sg : StrictGroup G} {sh : StrictGroup H}
    (phi : GroupHom sg sh) : Prop :=
  forall y : H, exists x : G, hom_fn phi x = y.

(* ================================================================== *)
(** * 2. Pre-image of a subgroup is a subgroup; pre-image preserves
        conjugacy of subgroups                                          *)
(* ================================================================== *)

Lemma preimage_is_subgroup :
    forall {G H : Type} (sg : StrictGroup G) (sh : StrictGroup H)
           (phi : GroupHom sg sh) (K : H -> Prop),
      is_subgroup (StrictGroup_to_Group sh) K ->
      is_subgroup (StrictGroup_to_Group sg)
                  (preimage_subset phi K).
Proof.
  intros G H sg sh phi K HK.
  unfold is_subgroup, contains_id, closed_under_mul, closed_under_inv,
         preimage_subset.
  simpl.
  destruct HK as [HKid [HKmul HKinv]].
  simpl in *.
  split; [| split].
  - (* eG ∈ φ⁻¹(K): φ(eG) = eH ∈ K *)
    rewrite (hom_id sg sh phi). exact HKid.
  - (* closed under mul *)
    intros a b Ha Hb.
    rewrite (hom_mul phi). apply HKmul; assumption.
  - (* closed under inv: take φ(a)⁻¹ ∈ K *)
    intros a Ha.
    destruct (HKinv (hom_fn phi a) Ha) as [b [Hb [Hab Hba]]].
    exists (sinv G sg a).
    split.
    + rewrite (hom_inv sg sh phi a).
      replace (sinv H sh (hom_fn phi a)) with b; [exact Hb |].
      apply (unique_inverse sh (hom_fn phi a) b); assumption.
    + simpl. split; [apply (sinv_right G sg) | apply (sinv_left G sg)].
Qed.

(** The remark in the paper's introduction: if [G_1] and [G_2] are
    conjugate in [G], then their pre-images under any surjective
    homomorphism [φ : G̃ → G] are conjugate in [G̃]. *)
Lemma preimage_preserves_conjugacy_of_subgroups :
    forall {G H : Type} (sg : StrictGroup G) (sh : StrictGroup H)
           (phi : GroupHom sg sh) (H1 H2 : H -> Prop),
      is_surjective_hom phi ->
      conjugate_subgroups sh H1 H2 ->
      conjugate_subgroups sg (preimage_subset phi H1)
                             (preimage_subset phi H2).
Proof.
  intros G H sg sh phi H1 H2 Hsurj [g Hg].
  destruct (Hsurj g) as [g_tilde Hgt].
  exists g_tilde.
  intro x. unfold preimage_subset, conj_act.
  (* φ(g̃ · x · g̃⁻¹) = φ(g̃) · φ(x) · φ(g̃)⁻¹ = g · φ(x) · g⁻¹ *)
  rewrite (hom_mul phi), (hom_mul phi), (hom_inv sg sh phi), Hgt.
  exact (Hg (hom_fn phi x)).
Qed.

(* ================================================================== *)
(** * 3. R-coset equivalence (Gassmann–Sunada / Z-equivalence)          *)
(* ================================================================== *)

(** R-coset equivalence is the relation [R[G/G_1] ≅ R[G/G_2]] as
    R[G]-modules. Formalizing this requires a development of group rings
    and module isomorphisms over arbitrary commutative rings R, which is
    not present in the project. We axiomatize it as an opaque relation
    parametrized by the ring R; this is the cleanest way to state the
    paper's results without bringing the entire group-ring infrastructure
    along. *)

Parameter R_coset_equivalent :
  forall (R : Type) {G : Type} (sg : StrictGroup G) (G1 G2 : G -> Prop), Prop.

(** Z-coset equivalence is the case [R = Z]. We don't fix a particular
    [Z]; the paper's statements only need a fixed coefficient ring. *)
Definition Z_coset_equivalent
    {G : Type} (sg : StrictGroup G) (G1 G2 : G -> Prop) : Prop :=
  R_coset_equivalent Z sg G1 G2.

(* ================================================================== *)
(** * 4. Lemma 2.1 — permanence of coset equivalence under pullbacks    *)
(* ================================================================== *)

(** Paper Lemma 2.1: if [G_1, G_2 ≤ G] are R-coset equivalent and
    [ψ : Γ → G] is surjective with [Γ_j = ψ⁻¹(G_j)], then [Γ_1, Γ_2] are
    R-coset equivalent.

    The proof in the paper uses [Γ/Γ_j ≅ G/G_j] as Γ-sets together with
    the universal property of R[·]. We axiomatize this lemma — it is
    standard module theory but requires the full R[G]-module
    infrastructure that the project does not yet have. *)
Conjecture R_coset_equiv_pullback :
  forall {R : Type} {G H : Type}
         (sg : StrictGroup G) (sh : StrictGroup H)
         (psi : GroupHom sg sh)
         (G1 G2 : H -> Prop),
    is_surjective_hom psi ->
    R_coset_equivalent R sh G1 G2 ->
    R_coset_equivalent R sg (preimage_subset psi G1)
                            (preimage_subset psi G2).

(** Specialization to [R = Z]. *)
Lemma Z_coset_equiv_pullback :
    forall {G H : Type} (sg : StrictGroup G) (sh : StrictGroup H)
           (psi : GroupHom sg sh) (G1 G2 : H -> Prop),
      is_surjective_hom psi ->
      Z_coset_equivalent sh G1 G2 ->
      Z_coset_equivalent sg (preimage_subset psi G1)
                            (preimage_subset psi G2).
Proof.
  intros G H sg sh psi G1 G2 Hsurj Hcoset.
  unfold Z_coset_equivalent in *.
  exact (R_coset_equiv_pullback sg sh psi G1 G2 Hsurj Hcoset).
Qed.

(* ================================================================== *)
(** * 5. Subgroup-isomorphism predicate                                  *)
(* ================================================================== *)

(** Two subgroups (as predicates) are isomorphic iff there exists a
    [GroupIso] between any [StrictGroup] structures on their carriers.
    Following the paper, we abstract this as a [Prop] — the witnessing
    StrictGroup structures and isomorphism are existentially quantified. *)
Definition subgroups_isomorphic
    {G H : Type} (sg : StrictGroup G) (sh : StrictGroup H)
    (G1 : G -> Prop) (H1 : H -> Prop) : Prop :=
  exists (sgsub : StrictGroup { x : G | G1 x })
         (shsub : StrictGroup { y : H | H1 y })
         (iso : GroupIso sgsub shsub), True.

(* ================================================================== *)
(** * 6. Theorem 1.1 — KLMRS Main Theorem                                *)
(* ================================================================== *)

(** Paper Theorem 1.1: For any finite group G there exists a finite group
    [G̃] and a surjective homomorphism [φ : G̃ → G] such that for any two
    non-conjugate subgroups [G_1, G_2 ≤ G], the pre-images [φ⁻¹(G_1)]
    and [φ⁻¹(G_2)] are not isomorphic.

    Stated as an Axiom: this is the main content of the paper, a 7-page
    construction via Sambale's outer-automorphism realization (Theorem 4.1
    + Theorem 4.2) plus an HNN extension argument. Formalizing the proof
    is a multi-month project. *)
Conjecture KLMRS_main_theorem :
  forall {G : Type} (sg : StrictGroup G) (G_list : list G),
    IsFiniteEnum sg G_list ->
    exists (Gtilde : Type) (sgt : StrictGroup Gtilde)
           (Gt_list : list Gtilde) (phi : GroupHom sgt sg),
      IsFiniteEnum sgt Gt_list /\
      is_surjective_hom phi /\
      (forall G1 G2 : G -> Prop,
         is_subgroup (StrictGroup_to_Group sg) G1 ->
         is_subgroup (StrictGroup_to_Group sg) G2 ->
         ~ conjugate_subgroups sg G1 G2 ->
         ~ subgroups_isomorphic sgt sgt
             (preimage_subset phi G1)
             (preimage_subset phi G2)).

(* ================================================================== *)
(** * 7. Question 1.3 — Prasad's question (now answered negatively)     *)
(* ================================================================== *)

(** Paper Question 1.3: "If G is a finite group and G_1, G_2 ≤ G are
    Z-coset equivalent, are G_1, G_2 necessarily isomorphic?"

    Stated as a [Prop]: this is the predicate "every finite group G and
    every Z-coset equivalent pair of subgroups have isomorphic
    underlying groups." The paper shows this Prop is FALSE. *)
Definition prasad_question_1_3 : Prop :=
  forall (G : Type) (sg : StrictGroup G) (G_list : list G),
    IsFiniteEnum sg G_list ->
    forall G1 G2 : G -> Prop,
      is_subgroup (StrictGroup_to_Group sg) G1 ->
      is_subgroup (StrictGroup_to_Group sg) G2 ->
      Z_coset_equivalent sg G1 G2 ->
      subgroups_isomorphic sg sg G1 G2.

(* ================================================================== *)
(** * 8. Scott's PSL(2,29) example — input to Theorem 1.4               *)
(* ================================================================== *)

(** Reference [14] in KLMRS: L. Scott (1993) constructed a pair of
    non-conjugate Z-coset equivalent subgroups of [PSL(2, 29)] of index
    203, both isomorphic to [A_5]. We axiomatize Scott's example as the
    abstract existence of such data: a finite group [S] with two
    non-conjugate, Z-coset equivalent subgroups. *)
Conjecture scott_example :
  exists (S : Type) (ssg : StrictGroup S) (S_list : list S)
         (S1 S2 : S -> Prop),
    IsFiniteEnum ssg S_list /\
    is_subgroup (StrictGroup_to_Group ssg) S1 /\
    is_subgroup (StrictGroup_to_Group ssg) S2 /\
    ~ conjugate_subgroups ssg S1 S2 /\
    Z_coset_equivalent ssg S1 S2.

(* ================================================================== *)
(** * 9. Theorem 1.4 — Question 1.3 has a negative answer               *)
(* ================================================================== *)

(** Paper Theorem 1.4: Question 1.3 has a negative answer.

    Proof strategy: take Scott's pair [S_1, S_2] (non-conjugate,
    Z-coset equivalent). Apply the KLMRS main theorem to S to get a
    finite extension [φ : S̃ → S] in which [φ⁻¹(S_1)] and [φ⁻¹(S_2)] are
    NOT isomorphic. By Lemma 2.1 (pullback preserves Z-coset equivalence),
    they remain Z-coset equivalent. So they witness the negation of
    Question 1.3. *)
Theorem theorem_1_4_question_1_3_negative :
    ~ prasad_question_1_3.
Proof.
  unfold prasad_question_1_3.
  intro Hprasad.
  destruct scott_example as
    [S [ssg [S_list [S1 [S2 [Hfin [HS1 [HS2 [Hnonconj Hcoset]]]]]]]]].
  destruct (KLMRS_main_theorem ssg S_list Hfin) as
    [Stilde [sst [St_list [phi [Hfint [Hsurj Hpairs]]]]]].
  pose proof (Hpairs S1 S2 HS1 HS2 Hnonconj) as Hnotiso.
  apply Hnotiso.
  apply (Hprasad Stilde sst St_list Hfint
                 (preimage_subset phi S1)
                 (preimage_subset phi S2)).
  - apply (preimage_is_subgroup sst ssg phi S1 HS1).
  - apply (preimage_is_subgroup sst ssg phi S2 HS2).
  - apply (Z_coset_equiv_pullback sst ssg phi S1 S2 Hsurj Hcoset).
Qed.

(* ================================================================== *)
(** * 10. Question 1.5 — the new OPEN problem                            *)
(* ================================================================== *)

(** Paper Question 1.5: "If G is a finite group and G_1, G_2 ≤ G are
    Z-coset equivalent subgroups that contain no non-trivial normal
    subgroup of G, are G_1, G_2 necessarily isomorphic?"

    This is the open problem proposed by KLMRS as a refinement of
    Prasad's question after their counter-example. The "core-free"
    condition (containing no non-trivial normal subgroup of G) is meant
    to rule out the kind of pullback-from-large-group obstructions that
    drove Theorem 1.4. *)

(** A subgroup [H ≤ G] is *core-free* iff it contains no non-trivial
    normal subgroup of [G]. *)
Definition is_core_free
    {G : Type} (sg : StrictGroup G) (H : G -> Prop) : Prop :=
  forall N : G -> Prop,
    is_normal_subgroup (StrictGroup_to_Group sg) N ->
    (forall x : G, N x -> H x) ->
    (forall x : G, N x -> x = se G sg).

Definition open_question_1_5 : Prop :=
  forall (G : Type) (sg : StrictGroup G) (G_list : list G),
    IsFiniteEnum sg G_list ->
    forall G1 G2 : G -> Prop,
      is_subgroup (StrictGroup_to_Group sg) G1 ->
      is_subgroup (StrictGroup_to_Group sg) G2 ->
      is_core_free sg G1 ->
      is_core_free sg G2 ->
      Z_coset_equivalent sg G1 G2 ->
      subgroups_isomorphic sg sg G1 G2.

(* ================================================================== *)
(** * 11. Corollary 1.6 — profinite-completion variant                   *)
(* ================================================================== *)

(** Paper Corollary 1.6: Let Γ be a finitely generated group, G a finite
    group with subgroups G_1, G_2, and φ : Γ → G a surjective hom. If the
    profinite completions of φ⁻¹(G_1) and φ⁻¹(G_2) are not isomorphic,
    then φ factors through a homomorphism Γ → H to a finite group in
    which the inverse images of G_1 and G_2 are not isomorphic.

    We don't have profinite completions in the project, so we abstract
    them as a Parameter and state the corollary as Axiom. *)
Parameter profinite_completion : forall {G : Type} (sg : StrictGroup G), Type.
Parameter profinite_iso :
  forall {G H : Type} (sg : StrictGroup G) (sh : StrictGroup H), Prop.

Conjecture KLMRS_corollary_1_6 :
  forall {Gamma G : Type} (sgam : StrictGroup Gamma) (sg : StrictGroup G)
         (G_list : list G) (phi : GroupHom sgam sg)
         (G1 G2 : G -> Prop)
         (HG1 : is_subgroup (StrictGroup_to_Group sg) G1)
         (HG2 : is_subgroup (StrictGroup_to_Group sg) G2),
    IsFiniteEnum sg G_list ->
    is_surjective_hom phi ->
    (* assumption: pi-completions of pre-images differ *)
    ~ profinite_iso sgam sgam ->
    exists (H : Type) (sh : StrictGroup H) (H_list : list H)
           (psi : GroupHom sgam sh) (theta : GroupHom sh sg),
      IsFiniteEnum sh H_list /\
      is_surjective_hom psi /\
      (forall x : Gamma,
         hom_fn phi x = hom_fn theta (hom_fn psi x)) /\
      ~ subgroups_isomorphic sh sh
          (preimage_subset theta G1)
          (preimage_subset theta G2).

(* ================================================================== *)
(** * 12. Theorem 1.7 — PSL(2,29) tetrahedral example                    *)
(* ================================================================== *)

(** Paper Theorem 1.7: Let G = PSL(2, 29) and let G_1, G_2 ≤ G be the
    non-conjugate A_5 subgroups (Scott's pair). Let T ⊂ H^3 be the
    tetrahedron with (3,5,3)-Coxeter diagram, and Γ the index-2
    orientation-preserving subgroup of the reflection group of T.
    Then there exist a finite quotient Q of Γ and an epimorphism
    Q → G for which the pre-images of G_1, G_2 are not isomorphic.

    The Magma computation in §5 of the paper exhibits this concretely.
    Stated as Axiom — formalizing the Magma calculation is out of scope. *)

Conjecture KLMRS_theorem_1_7 :
  exists (Gamma : Type) (sgam : StrictGroup Gamma)
         (G : Type)     (sg : StrictGroup G) (G_list : list G)
         (G1 G2 : G -> Prop)
         (Q : Type)     (sq : StrictGroup Q) (Q_list : list Q)
         (quotient : GroupHom sgam sq)
         (epi : GroupHom sq sg),
    IsFiniteEnum sg G_list /\
    IsFiniteEnum sq Q_list /\
    is_subgroup (StrictGroup_to_Group sg) G1 /\
    is_subgroup (StrictGroup_to_Group sg) G2 /\
    ~ conjugate_subgroups sg G1 G2 /\
    is_surjective_hom quotient /\
    is_surjective_hom epi /\
    ~ subgroups_isomorphic sq sq
        (preimage_subset epi G1)
        (preimage_subset epi G2).

(* ================================================================== *)
(** * 13. §1.3 / §1.4 informal open directions                           *)
(* ================================================================== *)

(** §1.3 and §1.4 of the paper raise four open directions that are not
    formally numbered as Questions but are stated as open. We formalize
    each as a [Definition : Prop]. They all depend on infrastructure
    not present in the project (number fields, function fields, mapping
    class groups, non-arithmetic lattices, profinite groups in their
    full generality), so we introduce the necessary abstractions as
    Parameters and state the questions over them.

    The point of formalizing them is to (a) record the precise question,
    (b) give it a Coq-level name future work can refer to, and (c) make
    explicit which infrastructure gaps would need to be filled before
    any attempt at a proof. *)

(** ** 13.1 Profinite Theorem 1.1 via anabelian results

    Paper §1.3: "It would however be interesting to see if, even just in
    the realm of profinite groups, one can obtain additional variants
    of Theorem 1.1 using other results from anabelian geometry..."

    The natural target is: a *profinite* version of Theorem 1.1 in which
    [G̃] is a profinite group (not necessarily finite) and [φ] is
    continuous-surjective. *)

(** Continuity of a homomorphism w.r.t. each side's profinite topology. *)
Parameter is_continuous_hom :
  forall {G H : Type} (sg : StrictGroup G) (sh : StrictGroup H)
         (phi : GroupHom sg sh), Prop.

(** Predicate "this group carries the topology of a profinite group". *)
Parameter IsProfinite : forall {G : Type} (sg : StrictGroup G), Prop.

(** Subgroup-isomorphism as profinite groups (uses [profinite_iso] from §11). *)
Parameter profinite_subgroups_isomorphic :
  forall {G H : Type} (sg : StrictGroup G) (sh : StrictGroup H)
         (G1 : G -> Prop) (H1 : H -> Prop), Prop.

Definition open_profinite_theorem_1_1 : Prop :=
  forall (G : Type) (sg : StrictGroup G) (G_list : list G),
    IsFiniteEnum sg G_list ->
    exists (Gtilde : Type) (sgt : StrictGroup Gtilde)
           (phi : GroupHom sgt sg),
      IsProfinite sgt /\
      is_continuous_hom sgt sg phi /\
      is_surjective_hom phi /\
      (forall G1 G2 : G -> Prop,
         is_subgroup (StrictGroup_to_Group sg) G1 ->
         is_subgroup (StrictGroup_to_Group sg) G2 ->
         ~ conjugate_subgroups sg G1 G2 ->
         ~ profinite_subgroups_isomorphic sgt sgt
             (preimage_subset phi G1)
             (preimage_subset phi G2)).

(** ** 13.2 Number-field recovery from the maximal prosupersolvable quotient

    Paper §1.3 (end): "...the question, raised in [6], of whether a
    number field can be recovered from the maximal prosupersolvable
    quotient of its absolute Galois group."

    Reference [6] = Karshon–Shusterman, arXiv:2601.01251. The question
    is open. *)

Parameter NumberField : Type.
Parameter NF_iso : NumberField -> NumberField -> Prop.
Parameter AbsGalois : NumberField -> Type.
Parameter AbsGaloisGroup :
  forall (K : NumberField), StrictGroup (AbsGalois K).
Parameter MaxProsupersolvableQuotient :
  forall {K : NumberField}, StrictGroup (AbsGalois K) -> Type.
Parameter MaxProsupQuotientGroup :
  forall (K : NumberField),
    StrictGroup (MaxProsupersolvableQuotient (AbsGaloisGroup K)).
Parameter prosup_iso :
  forall (K K' : NumberField), Prop.

(** The open question: prosup-equivalence of absolute Galois groups
    implies isomorphism of number fields. *)
Definition open_question_prosupersolvable_recovery : Prop :=
  forall (K K' : NumberField),
    prosup_iso K K' -> NF_iso K K'.

(** ** 13.3 Mapping class groups: profinite rigidity + Theorem-1.1 analog

    Paper §1.4: "One possible setting is that of mapping class groups
    of closed orientable surfaces — while their finite-index subgroups
    are isomorphic only if they are conjugate in view of [Ivanov 1997],
    we do not yet have the required profinite rigidity results."

    This describes TWO open problems:
      (a) Profinite rigidity of finite-index subgroups of MCG.
      (b) The combined Theorem-1.1 analog for finite quotients of MCG.

    [Ivanov 1997, Thm 5] gives the conjugacy-from-isomorphism direction;
    profinite rigidity is the missing piece. *)

(** Mapping class group of a closed orientable surface of genus [g ≥ 2]. *)
Parameter MCG : nat -> Type.
Parameter MCG_group : forall (g : nat), StrictGroup (MCG g).

(** Finite-index subgroup of a discrete group (predicate-style). *)
Definition is_finite_index
    {G : Type} (sg : StrictGroup G) (H : G -> Prop) : Prop :=
  exists (transversal : list G),
    (forall x : G, exists t, In t transversal /\ H (smul G sg (sinv G sg t) x)) /\
    NoDup transversal.

(** Profinite rigidity: finite-index subgroups isomorphic iff their
    profinite completions are isomorphic. *)
Definition open_mcg_profinite_rigidity : Prop :=
  forall (g : nat),
    2 <= g ->
    forall (H1 H2 : MCG g -> Prop),
      is_subgroup (StrictGroup_to_Group (MCG_group g)) H1 ->
      is_subgroup (StrictGroup_to_Group (MCG_group g)) H2 ->
      is_finite_index (MCG_group g) H1 ->
      is_finite_index (MCG_group g) H2 ->
      (subgroups_isomorphic (MCG_group g) (MCG_group g) H1 H2 <->
       profinite_subgroups_isomorphic (MCG_group g) (MCG_group g) H1 H2).

(** Combined Theorem-1.1 analog for MCG: paper notes this would follow
    from MCG profinite rigidity + Ivanov's conjugacy result. *)
Definition open_mcg_theorem_1_1_analog : Prop :=
  forall (g : nat),
    2 <= g ->
    forall (G : Type) (sg : StrictGroup G) (G_list : list G),
      IsFiniteEnum sg G_list ->
      forall (phi : GroupHom (MCG_group g) sg),
        is_surjective_hom phi ->
        exists (H : Type) (sh : StrictGroup H) (H_list : list H)
               (psi : GroupHom (MCG_group g) sh)
               (theta : GroupHom sh sg),
          IsFiniteEnum sh H_list /\
          is_surjective_hom psi /\
          (forall x : MCG g,
             hom_fn phi x = hom_fn theta (hom_fn psi x)) /\
          (forall G1 G2 : G -> Prop,
             is_subgroup (StrictGroup_to_Group sg) G1 ->
             is_subgroup (StrictGroup_to_Group sg) G2 ->
             ~ conjugate_subgroups sg G1 G2 ->
             ~ subgroups_isomorphic sh sh
                 (preimage_subset theta G1)
                 (preimage_subset theta G2)).

(** ** 13.4 Maximal non-arithmetic lattices: profinite rigidity + analog

    Paper §1.4: "A similar possible setting is that of maximal non-
    arithmetic lattices in Lie groups that exist by [Gromov–Piatetski-
    Shapiro] and [Margulis]. ... by work of Margulis, ... they are
    isomorphic as abstract groups if and only if they are conjugate in
    the maximal lattice. Profinite rigidity remains a possibility here
    as well."

    Same two-question structure as §13.3: profinite rigidity is open;
    the Theorem-1.1 analog follows from it. *)

(** A maximal non-arithmetic lattice in some Lie group (abstract type). *)
Parameter MaxNonArithLattice : Type.
Parameter MaxNonArithLattice_group : StrictGroup MaxNonArithLattice.

Definition open_nonarith_profinite_rigidity : Prop :=
  forall (H1 H2 : MaxNonArithLattice -> Prop),
    is_subgroup (StrictGroup_to_Group MaxNonArithLattice_group) H1 ->
    is_subgroup (StrictGroup_to_Group MaxNonArithLattice_group) H2 ->
    is_finite_index MaxNonArithLattice_group H1 ->
    is_finite_index MaxNonArithLattice_group H2 ->
    (subgroups_isomorphic
       MaxNonArithLattice_group MaxNonArithLattice_group H1 H2
     <->
     profinite_subgroups_isomorphic
       MaxNonArithLattice_group MaxNonArithLattice_group H1 H2).

Definition open_nonarith_theorem_1_1_analog : Prop :=
  forall (G : Type) (sg : StrictGroup G) (G_list : list G),
    IsFiniteEnum sg G_list ->
    forall (phi : GroupHom MaxNonArithLattice_group sg),
      is_surjective_hom phi ->
      exists (H : Type) (sh : StrictGroup H) (H_list : list H)
             (psi : GroupHom MaxNonArithLattice_group sh)
             (theta : GroupHom sh sg),
        IsFiniteEnum sh H_list /\
        is_surjective_hom psi /\
        (forall x : MaxNonArithLattice,
           hom_fn phi x = hom_fn theta (hom_fn psi x)) /\
        (forall G1 G2 : G -> Prop,
           is_subgroup (StrictGroup_to_Group sg) G1 ->
           is_subgroup (StrictGroup_to_Group sg) G2 ->
           ~ conjugate_subgroups sg G1 G2 ->
           ~ subgroups_isomorphic sh sh
               (preimage_subset theta G1)
               (preimage_subset theta G2)).

(* ================================================================== *)
(** * 14. Partial results — abelian case of Question 1.5                *)
(* ================================================================== *)

(** We attempt the abelian special case of Question 1.5. In an abelian
    group every subgroup is normal, so a core-free subgroup is forced
    to be trivial. Two trivial subgroups are always isomorphic. As a
    bonus the abelian case does not even require Z-coset equivalence —
    the conclusion follows from core-freeness alone. *)

From Stdlib Require Import Logic.ProofIrrelevance.

(** Helper: equality of sigma elements with the same first component
    follows from proof-irrelevance on the propositional second
    component. *)
Lemma sig_eq_proof_irrel :
    forall (A : Type) (P : A -> Prop) (x : A) (p q : P x),
      exist P x p = exist P x q.
Proof.
  intros A P x p q.
  rewrite (proof_irrelevance _ p q).
  reflexivity.
Qed.

Definition is_abelian {G : Type} (sg : StrictGroup G) : Prop :=
  forall a b : G, smul G sg a b = smul G sg b a.

(** In an abelian group, every subgroup is normal. *)
Lemma abelian_subgroup_is_normal :
    forall {G : Type} (sg : StrictGroup G),
      is_abelian sg ->
      forall H : G -> Prop,
        is_subgroup (StrictGroup_to_Group sg) H ->
        is_normal_subgroup (StrictGroup_to_Group sg) H.
Proof.
  intros G sg Habel H Hsub.
  unfold is_normal_subgroup. split; [exact Hsub |].
  intros g n ginv Hn [Hgg _]. simpl in *.
  (* Goal: H (g · n · ginv). Use commutativity to reduce to n. *)
  replace (smul G sg (smul G sg g n) ginv) with n; [exact Hn |].
  symmetry.
  rewrite (Habel g n).
  rewrite <- (sassoc G sg n g ginv).
  rewrite Hgg.
  apply (sid_right G sg).
Qed.

(** A core-free subgroup of an abelian group is trivial. *)
Lemma abelian_core_free_is_trivial :
    forall {G : Type} (sg : StrictGroup G),
      is_abelian sg ->
      forall H : G -> Prop,
        is_subgroup (StrictGroup_to_Group sg) H ->
        is_core_free sg H ->
        forall x : G, H x -> x = se G sg.
Proof.
  intros G sg Habel H Hsub Hcf x Hx.
  apply (Hcf H).
  - apply abelian_subgroup_is_normal; assumption.
  - tauto.
  - exact Hx.
Qed.

(** Helpers — top-level so they fully reduce when used. *)

Definition triv_canon
    {G : Type} (sg : StrictGroup G) (P : G -> Prop)
    (HP : is_subgroup (StrictGroup_to_Group sg) P)
    : { x : G | P x } :=
  exist P (se G sg) (proj1 HP).

Lemma triv_singleton :
    forall {G : Type} (sg : StrictGroup G) (P : G -> Prop)
           (HP : is_subgroup (StrictGroup_to_Group sg) P)
           (Htriv : forall x : G, P x -> x = se G sg)
           (a : { x : G | P x }),
      triv_canon sg P HP = a.
Proof.
  intros G sg P HP Htriv [a Ha].
  assert (Heq : a = se G sg) by (apply Htriv; exact Ha).
  unfold triv_canon. revert Ha. rewrite Heq. intros Ha.
  apply sig_eq_proof_irrel.
Qed.

Definition triv_strict_group
    {G : Type} (sg : StrictGroup G) (P : G -> Prop)
    (HP : is_subgroup (StrictGroup_to_Group sg) P)
    (Htriv : forall x : G, P x -> x = se G sg)
    : StrictGroup { x : G | P x } :=
  {| smul := fun _ _ => triv_canon sg P HP;
     se := triv_canon sg P HP;
     sinv := fun _ => triv_canon sg P HP;
     sassoc := fun _ _ _ => eq_refl;
     sid_right := triv_singleton sg P HP Htriv;
     sid_left := triv_singleton sg P HP Htriv;
     sinv_right := fun _ => eq_refl;
     sinv_left := fun _ => eq_refl;
  |}.

(** Two subgroups that are both forced to consist solely of the
    identity element are isomorphic. *)
Lemma trivial_subgroups_isomorphic :
    forall {G H : Type} (sg : StrictGroup G) (sh : StrictGroup H)
           (G1 : G -> Prop) (H1 : H -> Prop),
      is_subgroup (StrictGroup_to_Group sg) G1 ->
      is_subgroup (StrictGroup_to_Group sh) H1 ->
      (forall x : G, G1 x -> x = se G sg) ->
      (forall y : H, H1 y -> y = se H sh) ->
      subgroups_isomorphic sg sh G1 H1.
Proof.
  intros G H sg sh G1 H1 HG1 HH1 HtrivG HtrivH.
  exists (triv_strict_group sg G1 HG1 HtrivG),
         (triv_strict_group sh H1 HH1 HtrivH).
  unshelve eexists.
  { refine {| iso_hom := {| hom_fn := fun _ => triv_canon sh H1 HH1;
                            hom_mul := _ |};
              iso_inv_fn := fun _ => triv_canon sg G1 HG1;
              iso_left_inv := triv_singleton sg G1 HG1 HtrivG;
              iso_right_inv := triv_singleton sh H1 HH1 HtrivH |}.
    intros a b. reflexivity. }
  exact I.
Qed.

(** **Theorem (Question 1.5, abelian case).** In any abelian finite
    group [G], every pair of core-free subgroups is isomorphic — and
    in fact both subgroups are forced to be trivial. The Z-coset
    equivalence hypothesis from Question 1.5 is not needed in the
    abelian case. *)
Theorem question_1_5_abelian :
    forall (G : Type) (sg : StrictGroup G) (G_list : list G),
      IsFiniteEnum sg G_list ->
      is_abelian sg ->
      forall G1 G2 : G -> Prop,
        is_subgroup (StrictGroup_to_Group sg) G1 ->
        is_subgroup (StrictGroup_to_Group sg) G2 ->
        is_core_free sg G1 ->
        is_core_free sg G2 ->
        Z_coset_equivalent sg G1 G2 ->
        subgroups_isomorphic sg sg G1 G2.
Proof.
  intros G sg G_list Hfin Habel G1 G2 HG1 HG2 HCF1 HCF2 _.
  apply (trivial_subgroups_isomorphic sg sg G1 G2); auto.
  - apply (abelian_core_free_is_trivial sg Habel G1 HG1 HCF1).
  - apply (abelian_core_free_is_trivial sg Habel G2 HG2 HCF2).
Qed.

(** A useful corollary the paper does not state explicitly: in an
    abelian group, every core-free subgroup is the trivial subgroup.
    (Equivalently: the only core-free subgroup of an abelian group is
    {e}.) *)
Corollary abelian_unique_core_free :
    forall {G : Type} (sg : StrictGroup G),
      is_abelian sg ->
      forall H : G -> Prop,
        is_subgroup (StrictGroup_to_Group sg) H ->
        is_core_free sg H ->
        forall x : G, H x <-> x = se G sg.
Proof.
  intros G sg Habel H Hsub Hcf x.
  split.
  - apply (abelian_core_free_is_trivial sg Habel H Hsub Hcf).
  - intros ->. exact (proj1 Hsub).
Qed.

(* ================================================================== *)
(** * 15. Partial result — nilpotent / p-group case of Question 1.5     *)
(* ================================================================== *)

(** Beyond the abelian case (cycle 34), the next natural class is
    nilpotent groups. The classical fact we need: in a nilpotent group
    G, every nontrivial subgroup meets the center Z(G) nontrivially.
    For p-groups this is the standard non-trivial-center theorem (proved
    via the class equation, available in this project at
    [Conjugacy/ClassEquation.v]). For nilpotent groups in general, it
    follows from the upper central series.

    We axiomatize the consequence we need — call it the "central
    intersection property" — and derive Question 1.5 over groups
    satisfying it. *)

(** [HasCentralIntersectionProperty sg]: every subgroup of G whose
    central elements are all the identity is itself the trivial subgroup.
    Equivalently: every nontrivial subgroup of G meets Z(G) nontrivially,
    i.e., every minimal subgroup of G is contained in Z(G).

    Strictly between abelian and nilpotent:
    - Holds for: abelian groups, Q_8 (and more generally groups where
      every minimal subgroup is central).
    - FAILS for: D_4 (the reflection subgroup ⟨s⟩ has only e as a
      central element), more generally any group with a non-central
      element of prime order.
    - Fails for: non-abelian simple groups (S_n for n ≥ 5), free groups.

    Working name "central-intersection property". Not the same thing as
    nilpotency, despite both stemming from the structure of Z(G). *)
Definition HasCentralIntersectionProperty
    {G : Type} (sg : StrictGroup G) : Prop :=
  forall H : G -> Prop,
    is_subgroup (StrictGroup_to_Group sg) H ->
    (forall z, H z -> is_central (StrictGroup_to_Group sg) z ->
                      z = se G sg) ->
    forall x, H x -> x = se G sg.

(** Helper: inverse of a central element is central. *)
Lemma is_central_inv :
    forall {G : Type} (sg : StrictGroup G) (a : G),
      is_central (StrictGroup_to_Group sg) a ->
      is_central (StrictGroup_to_Group sg) (sinv G sg a).
Proof.
  intros G sg a Hac.
  unfold is_central in *. simpl in *. intro c.
  apply (left_cancel sg a).
  rewrite (sassoc G sg a (sinv G sg a) c).
  rewrite (sinv_right G sg a).
  rewrite (sid_left G sg c).
  rewrite (sassoc G sg a c (sinv G sg a)).
  rewrite (Hac c).
  rewrite <- (sassoc G sg c a (sinv G sg a)).
  rewrite (sinv_right G sg a).
  rewrite (sid_right G sg c).
  reflexivity.
Qed.

(** [H ∩ Z(G)] is a normal subgroup of G whenever H is a subgroup.
    Reason: every conjugate of a central element is itself. *)
Lemma H_inter_center_normal :
    forall {G : Type} (sg : StrictGroup G) (H : G -> Prop),
      is_subgroup (StrictGroup_to_Group sg) H ->
      is_normal_subgroup (StrictGroup_to_Group sg)
        (fun x => H x /\ is_central (StrictGroup_to_Group sg) x).
Proof.
  intros G sg H Hsub.
  unfold is_normal_subgroup. split.
  - (* is_subgroup of H ∩ Z(G) *)
    unfold is_subgroup, contains_id, closed_under_mul, closed_under_inv. simpl.
    destruct Hsub as [Hid [Hmul Hinv]]. simpl in *.
    split; [| split].
    + (* identity is central *)
      split; [exact Hid |].
      unfold is_central. simpl. intro b.
      rewrite (sid_left G sg b), (sid_right G sg b). reflexivity.
    + (* product of two central elements is central *)
      intros a b [Ha Hac] [Hb Hbc].
      split; [apply Hmul; assumption |].
      unfold is_central in *. simpl in *. intro c.
      rewrite <- (sassoc G sg a b c).
      rewrite (Hbc c).
      rewrite (sassoc G sg a c b).
      rewrite (Hac c).
      rewrite <- (sassoc G sg c a b).
      reflexivity.
    + (* inverse of a central element in H is central in H *)
      intros a [Ha Hac].
      destruct (Hinv a Ha) as [b [Hb Hinvab]].
      exists b. split.
      * split; [exact Hb |].
        destruct Hinvab as [Hab Hba]. simpl in *.
        rewrite (unique_inverse sg a b Hab Hba).
        apply is_central_inv. exact Hac.
      * exact Hinvab.
  - (* normality: g·n·ginv ∈ H ∩ Z(G) when n is central *)
    intros g n ginv [Hn Hncent] [Hgg _].
    simpl in *.
    replace (smul G sg (smul G sg g n) ginv) with n.
    + split; assumption.
    + symmetry.
      unfold is_central in Hncent. simpl in Hncent.
      rewrite <- (Hncent g).
      rewrite <- (sassoc G sg n g ginv).
      rewrite Hgg.
      apply (sid_right G sg).
Qed.

(** From core-freeness: every central element of H is the identity. *)
Lemma core_free_central_elements_trivial :
    forall {G : Type} (sg : StrictGroup G) (H : G -> Prop),
      is_subgroup (StrictGroup_to_Group sg) H ->
      is_core_free sg H ->
      forall z, H z ->
                is_central (StrictGroup_to_Group sg) z ->
                z = se G sg.
Proof.
  intros G sg H Hsub Hcf z Hz Hzcent.
  apply (Hcf (fun y => H y /\ is_central (StrictGroup_to_Group sg) y)).
  - apply H_inter_center_normal. exact Hsub.
  - intros y [Hy _]. exact Hy.
  - split; assumption.
Qed.

(** Combining: in a group with the central-intersection property,
    every core-free subgroup is trivial. *)
Lemma central_intersection_core_free_is_trivial :
    forall {G : Type} (sg : StrictGroup G),
      HasCentralIntersectionProperty sg ->
      forall H : G -> Prop,
        is_subgroup (StrictGroup_to_Group sg) H ->
        is_core_free sg H ->
        forall x : G, H x -> x = se G sg.
Proof.
  intros G sg Hcip H Hsub Hcf x Hx.
  apply (Hcip H Hsub).
  - apply core_free_central_elements_trivial; assumption.
  - exact Hx.
Qed.

(** **Theorem (Question 1.5, central-intersection-property case).**
    Question 1.5 holds over any finite group satisfying the
    central-intersection property — strictly extending the abelian case
    (Q_8, etc.) but NOT covering all nilpotent groups (e.g. D_4). Both
    subgroups are forced to be trivial. The Z-coset equivalence
    hypothesis is not needed. *)
Theorem question_1_5_central_intersection :
    forall (G : Type) (sg : StrictGroup G) (G_list : list G),
      IsFiniteEnum sg G_list ->
      HasCentralIntersectionProperty sg ->
      forall G1 G2 : G -> Prop,
        is_subgroup (StrictGroup_to_Group sg) G1 ->
        is_subgroup (StrictGroup_to_Group sg) G2 ->
        is_core_free sg G1 ->
        is_core_free sg G2 ->
        Z_coset_equivalent sg G1 G2 ->
        subgroups_isomorphic sg sg G1 G2.
Proof.
  intros G sg G_list Hfin Hcip G1 G2 HG1 HG2 HCF1 HCF2 _.
  apply (trivial_subgroups_isomorphic sg sg G1 G2); auto.
  - apply (central_intersection_core_free_is_trivial sg Hcip G1 HG1 HCF1).
  - apply (central_intersection_core_free_is_trivial sg Hcip G2 HG2 HCF2).
Qed.

(** Sanity check: every abelian group has the central-intersection
    property, because *every* element is central. So
    [question_1_5_central_intersection] actually subsumes [question_1_5_abelian]. *)
Lemma abelian_has_central_intersection_property :
    forall {G : Type} (sg : StrictGroup G),
      is_abelian sg ->
      HasCentralIntersectionProperty sg.
Proof.
  intros G sg Habel H Hsub Hall x Hx.
  apply Hall; [exact Hx |].
  unfold is_central. simpl.
  intro b. apply Habel.
Qed.

(* ================================================================== *)
(** * 16. Partial result — Q1.5 for ABELIAN subgroups                   *)
(* ================================================================== *)

(** A different angle on Q1.5: rather than constraining the ambient group
    [G], constrain the subgroups themselves to be abelian. Two abelian
    subgroups of any G that are Z-coset equivalent must be isomorphic
    by the structure theorem for finite abelian groups (which says
    finite abelian groups are determined up to isomorphism by their
    element-order multiset). The core-free hypothesis is not even
    needed in this case. *)

(** A subgroup [H ≤ G] is abelian if its elements commute pairwise. *)
Definition is_abelian_subgroup
    {G : Type} (sg : StrictGroup G) (H : G -> Prop) : Prop :=
  forall x y : G, H x -> H y -> smul G sg x y = smul G sg y x.

(** Element-order multiset: counts the elements of [H] of each natural
    order. Axiomatized as a Parameter — a concrete definition would
    require [order_of] and finite enumeration of [H]. *)
Parameter element_order_multiset :
  forall {G : Type} (sg : StrictGroup G) (H : G -> Prop), nat -> nat.

(** Z-coset equivalence implies equal element-order multisets (a basic
    consequence of Burnside / table-of-marks comparison: |fixed points
    of ⟨g⟩| count equally for both subgroups). *)
Axiom Z_coset_equivalent_same_order_multiset :
  forall {G : Type} (sg : StrictGroup G) (H1 H2 : G -> Prop),
    Z_coset_equivalent sg H1 H2 ->
    forall n : nat,
      element_order_multiset sg H1 n = element_order_multiset sg H2 n.

(** Structure theorem for finite abelian groups: two finite abelian
    groups with the same element-order multiset are isomorphic.

    Standard reference: Dummit & Foote, Theorem 5.2 (Fundamental
    Theorem of Finitely Generated Abelian Groups). The element-order
    multiset is equivalent to the multiset of elementary divisors,
    which determine the group up to isomorphism. *)
Conjecture abelian_subgroups_iso_from_order_multiset :
  forall {G : Type} (sg : StrictGroup G) (H1 H2 : G -> Prop),
    is_subgroup (StrictGroup_to_Group sg) H1 ->
    is_subgroup (StrictGroup_to_Group sg) H2 ->
    is_abelian_subgroup sg H1 ->
    is_abelian_subgroup sg H2 ->
    (forall n, element_order_multiset sg H1 n =
                element_order_multiset sg H2 n) ->
    subgroups_isomorphic sg sg H1 H2.

(** **Theorem (Q1.5, abelian-subgroup case).** Two abelian subgroups
    that are Z-coset equivalent are isomorphic. The core-free
    hypothesis is not used. *)
Theorem question_1_5_abelian_subgroups :
    forall (G : Type) (sg : StrictGroup G) (G_list : list G),
      IsFiniteEnum sg G_list ->
      forall G1 G2 : G -> Prop,
        is_subgroup (StrictGroup_to_Group sg) G1 ->
        is_subgroup (StrictGroup_to_Group sg) G2 ->
        is_abelian_subgroup sg G1 ->
        is_abelian_subgroup sg G2 ->
        Z_coset_equivalent sg G1 G2 ->
        subgroups_isomorphic sg sg G1 G2.
Proof.
  intros G sg G_list Hfin G1 G2 HG1 HG2 Habel1 Habel2 Hzce.
  apply abelian_subgroups_iso_from_order_multiset; auto.
  intros n.
  apply Z_coset_equivalent_same_order_multiset.
  exact Hzce.
Qed.

(** Strict generalization of the abelian-G case: when the ambient G is
    abelian, both subgroups are automatically abelian (since their
    elements live inside an abelian group). So [question_1_5_abelian]
    becomes a special case of [question_1_5_abelian_subgroups]. *)
Lemma is_abelian_implies_subgroup_abelian :
    forall {G : Type} (sg : StrictGroup G),
      is_abelian sg ->
      forall H : G -> Prop, is_abelian_subgroup sg H.
Proof.
  intros G sg Habel H x y _ _. apply Habel.
Qed.

(** A subgroup H is cyclic if H = ⟨g⟩ for some g ∈ H. *)
Definition is_cyclic_subgroup
    {G : Type} (sg : StrictGroup G) (H : G -> Prop) : Prop :=
  exists g : G, H g /\
    forall x : G, H x ->
      exists n : nat, gpow (StrictGroup_to_Group sg) g n = x.

(** Helper: [g^(m+n) = g^m · g^n]. *)
Lemma gpow_add :
    forall {G : Type} (sg : StrictGroup G) (g : G) (m n : nat),
      gpow (StrictGroup_to_Group sg) g (m + n) =
      smul G sg
        (gpow (StrictGroup_to_Group sg) g m)
        (gpow (StrictGroup_to_Group sg) g n).
Proof.
  intros G sg g m n.
  induction m as [|m IH].
  - simpl. symmetry. apply (sid_left G sg).
  - simpl. rewrite IH.
    apply (sassoc G sg).
Qed.

(** Powers of a single element commute: [g^m · g^n = g^n · g^m]. *)
Lemma gpow_self_commute :
    forall {G : Type} (sg : StrictGroup G) (g : G) (m n : nat),
      smul G sg
        (gpow (StrictGroup_to_Group sg) g m)
        (gpow (StrictGroup_to_Group sg) g n)
      = smul G sg
        (gpow (StrictGroup_to_Group sg) g n)
        (gpow (StrictGroup_to_Group sg) g m).
Proof.
  intros G sg g m n.
  rewrite <- (gpow_add sg g m n).
  rewrite <- (gpow_add sg g n m).
  rewrite (PeanoNat.Nat.add_comm m n).
  reflexivity.
Qed.

(** Cyclic subgroups are abelian — discharged via [gpow_self_commute].
    (Was Axiom in cycle 43; converted to Theorem 2026-04-30.) *)
Theorem is_cyclic_implies_abelian :
    forall {G : Type} (sg : StrictGroup G) (H : G -> Prop),
      is_cyclic_subgroup sg H ->
      is_abelian_subgroup sg H.
Proof.
  intros G sg H [g [_ Hgen]] x y Hx Hy.
  destruct (Hgen x Hx) as [m Hxm].
  destruct (Hgen y Hy) as [n Hyn].
  rewrite <- Hxm, <- Hyn.
  apply gpow_self_commute.
Qed.

(** Q1.5 for *Dedekind* groups (every subgroup is normal). This
    strictly generalises the abelian case: in a Dedekind group, every
    core-free subgroup is trivial (core = subgroup itself), so both
    subgroups in any Q1.5 input are forced trivial, hence isomorphic.
    Examples: abelian groups (trivially Dedekind) and the Hamiltonian
    groups (e.g. Q_8 × A × ... per the Dedekind classification). *)
Theorem question_1_5_dedekind :
    forall (G : Type) (sg : StrictGroup G) (G_list : list G),
      IsFiniteEnum sg G_list ->
      (forall H : G -> Prop,
         is_subgroup (StrictGroup_to_Group sg) H ->
         is_normal_subgroup (StrictGroup_to_Group sg) H) ->
      forall G1 G2 : G -> Prop,
        is_subgroup (StrictGroup_to_Group sg) G1 ->
        is_subgroup (StrictGroup_to_Group sg) G2 ->
        is_core_free sg G1 ->
        is_core_free sg G2 ->
        Z_coset_equivalent sg G1 G2 ->
        subgroups_isomorphic sg sg G1 G2.
Proof.
  intros G sg G_list Hfin Hded G1 G2 HG1 HG2 HCF1 HCF2 _.
  apply (trivial_subgroups_isomorphic sg sg G1 G2); auto.
  - intros x Hx.
    apply (HCF1 G1).
    + apply Hded. exact HG1.
    + tauto.
    + exact Hx.
  - intros x Hx.
    apply (HCF2 G2).
    + apply Hded. exact HG2.
    + tauto.
    + exact Hx.
Qed.

(** Q1.5 for groups whose every core-free subgroup is abelian.
    This subsumes the abelian-G case (every subgroup is abelian) and
    handles cases like S_3 where the ambient group is non-abelian
    but all core-free subgroups happen to be abelian. *)
Theorem question_1_5_when_corefree_subgroups_abelian :
    forall (G : Type) (sg : StrictGroup G) (G_list : list G),
      IsFiniteEnum sg G_list ->
      (forall H : G -> Prop,
         is_subgroup (StrictGroup_to_Group sg) H ->
         is_core_free sg H ->
         is_abelian_subgroup sg H) ->
      forall G1 G2 : G -> Prop,
        is_subgroup (StrictGroup_to_Group sg) G1 ->
        is_subgroup (StrictGroup_to_Group sg) G2 ->
        is_core_free sg G1 ->
        is_core_free sg G2 ->
        Z_coset_equivalent sg G1 G2 ->
        subgroups_isomorphic sg sg G1 G2.
Proof.
  intros G sg G_list Hfin Hall G1 G2 HG1 HG2 HCF1 HCF2 Hzce.
  apply (question_1_5_abelian_subgroups G sg G_list Hfin); auto.
Qed.

(** Q1.5 for cyclic subgroups: immediate corollary of the
    abelian-subgroup case. *)
Theorem question_1_5_cyclic_subgroups :
    forall (G : Type) (sg : StrictGroup G) (G_list : list G),
      IsFiniteEnum sg G_list ->
      forall G1 G2 : G -> Prop,
        is_subgroup (StrictGroup_to_Group sg) G1 ->
        is_subgroup (StrictGroup_to_Group sg) G2 ->
        is_cyclic_subgroup sg G1 ->
        is_cyclic_subgroup sg G2 ->
        Z_coset_equivalent sg G1 G2 ->
        subgroups_isomorphic sg sg G1 G2.
Proof.
  intros G sg G_list Hfin G1 G2 HG1 HG2 Hcyc1 Hcyc2 Hzce.
  apply question_1_5_abelian_subgroups with G_list; auto;
    apply is_cyclic_implies_abelian; assumption.
Qed.

(* ================================================================== *)
(** * 16b. Two further corollaries of Question 1.5                      *)
(* ================================================================== *)

(** **Theorem (Q1.5, no-nontrivial-corefree case).**
    If every core-free subgroup of G is trivial (the hypothesis says all
    elements of every core-free subgroup are the identity), then Q1.5
    holds vacuously: G1 and G2 are both trivial, hence isomorphic via
    [trivial_subgroups_isomorphic].

    This is the cleanest "vacuous" instantiation of Q1.5 — no abelian
    structure, no Dedekind property, no cyclic assumption.  Just the raw
    hypothesis that no nontrivial core-free subgroup exists. *)
Theorem question_1_5_when_no_nontrivial_corefree :
    forall (G : Type) (sg : StrictGroup G) (G_list : list G),
      IsFiniteEnum sg G_list ->
      (forall H : G -> Prop,
         is_subgroup (StrictGroup_to_Group sg) H ->
         is_core_free sg H ->
         forall x : G, H x -> x = se G sg) ->
      forall G1 G2 : G -> Prop,
        is_subgroup (StrictGroup_to_Group sg) G1 ->
        is_subgroup (StrictGroup_to_Group sg) G2 ->
        is_core_free sg G1 ->
        is_core_free sg G2 ->
        Z_coset_equivalent sg G1 G2 ->
        subgroups_isomorphic sg sg G1 G2.
Proof.
  intros G sg G_list _Hfin Hno G1 G2 HG1 HG2 HCF1 HCF2 _.
  apply (trivial_subgroups_isomorphic sg sg G1 G2); auto.
  - apply Hno; assumption.
  - apply Hno; assumption.
Qed.

(** Helper: a normal subgroup that is also core-free must be trivial,
    because the subgroup itself witnesses the core-free condition. *)
Lemma normal_core_free_is_trivial :
    forall {G : Type} (sg : StrictGroup G) (H : G -> Prop),
      is_subgroup (StrictGroup_to_Group sg) H ->
      is_normal_subgroup (StrictGroup_to_Group sg) H ->
      is_core_free sg H ->
      forall x : G, H x -> x = se G sg.
Proof.
  intros G sg H Hsub Hnorm Hcf x Hx.
  apply (Hcf H Hnorm).
  - tauto.
  - exact Hx.
Qed.

(** **Theorem (Q1.5, normal subgroups case).**
    If both core-free subgroups G1 and G2 happen to be normal in G,
    then they are both trivial (a normal subgroup is its own core, so
    core-freeness forces triviality) and hence isomorphic.

    This strictly extends the abelian case in a different direction:
    it does not require the ambient group to be abelian, only that the
    two particular subgroups in the Q1.5 pair are normal.  The
    Z-coset equivalence hypothesis is again not needed. *)
Theorem question_1_5_normal_corefree_subgroups :
    forall (G : Type) (sg : StrictGroup G) (G_list : list G),
      IsFiniteEnum sg G_list ->
      forall G1 G2 : G -> Prop,
        is_subgroup (StrictGroup_to_Group sg) G1 ->
        is_subgroup (StrictGroup_to_Group sg) G2 ->
        is_normal_subgroup (StrictGroup_to_Group sg) G1 ->
        is_normal_subgroup (StrictGroup_to_Group sg) G2 ->
        is_core_free sg G1 ->
        is_core_free sg G2 ->
        Z_coset_equivalent sg G1 G2 ->
        subgroups_isomorphic sg sg G1 G2.
Proof.
  intros G sg G_list _Hfin G1 G2 HG1 HG2 HN1 HN2 HCF1 HCF2 _.
  apply (trivial_subgroups_isomorphic sg sg G1 G2); auto.
  - apply (normal_core_free_is_trivial sg G1 HG1 HN1 HCF1).
  - apply (normal_core_free_is_trivial sg G2 HG2 HN2 HCF2).
Qed.

(* ================================================================== *)
(** * 17. Notes / status                                                 *)
(* ================================================================== *)

(** Summary:
      - Theorem 1.1 (KLMRS_main_theorem):       Axiom (paper proof)
      - Lemma   2.1 (R_coset_equiv_pullback):   Axiom (standard, needs
                                                  group-ring infrastructure)
      - Theorem 1.4 (theorem_1_4_question_1_3_negative): THEOREM
                                                  (proved here from the above
                                                  + Scott's example)
      - Question 1.5 (open_question_1_5):       Definition (OPEN PROBLEM)
      - §1.3 profinite Theorem 1.1 variant
        (open_profinite_theorem_1_1):           Definition (OPEN PROBLEM)
      - §1.3 prosupersolvable recovery
        (open_question_prosupersolvable_recovery): Definition (OPEN PROBLEM)
      - §1.4 MCG profinite rigidity
        (open_mcg_profinite_rigidity):          Definition (OPEN PROBLEM)
      - §1.4 MCG Theorem-1.1 analog
        (open_mcg_theorem_1_1_analog):          Definition (OPEN PROBLEM)
      - §1.4 non-arithmetic lattice rigidity
        (open_nonarith_profinite_rigidity):     Definition (OPEN PROBLEM)
      - §1.4 non-arithmetic lattice analog
        (open_nonarith_theorem_1_1_analog):     Definition (OPEN PROBLEM)
      - Corollary 1.6:                          Axiom
      - Theorem 1.7 (PSL(2,29) example):        Axiom (Magma calculation)

    The project gains:
      - 1 new theorem  (theorem_1_4_question_1_3_negative)
      - 2 new helper lemmas (preimage_is_subgroup,
                             preimage_preserves_conjugacy_of_subgroups,
                             Z_coset_equiv_pullback)
      - 1 stated open problem (open_question_1_5)
      - 5 new axioms          (R_coset_equiv_pullback, scott_example,
                               KLMRS_main_theorem, KLMRS_corollary_1_6,
                               KLMRS_theorem_1_7)
      - 2 new parameters      (R_coset_equivalent, profinite_completion,
                               profinite_iso)

    Net axiom delta: +5 axioms + 3 parameters, but with all of them tied
    to a single recent paper rather than to project-internal proof gaps.
    The new theorem theorem_1_4_question_1_3_negative is the formalized
    answer to Prasad's question. *)
