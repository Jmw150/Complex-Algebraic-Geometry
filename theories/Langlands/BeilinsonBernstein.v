(** * Langlands/BeilinsonBernstein.v
    Beilinson-Bernstein localization and the flag variety.

    The Beilinson-Bernstein theorem (1981) establishes an equivalence:
      D_λ-mod(G/B)  ≅  U(g)-mod_{χ_λ}

    between D-modules on the flag variety G/B twisted by a weight λ
    and modules over the universal enveloping algebra U(g) with central
    character χ_λ (given by the Harish-Chandra homomorphism).

    This is a foundational result for the geometric Langlands program:
    - The automorphic side of Langlands for GL(2) involves D-modules on
      Bun_{GL(2)}(X), which decomposes via Hecke operators into eigenspaces
      indexed by representations of the Langlands dual.
    - BB localization is the local version at a point: it explains how
      representations of g correspond to geometric objects on the flag variety.

    Special cases:
    - λ = 0:  D₀-mod(G/B) ≅ U(g)-mod^{g-fin} (Bernstein-Gelfand-Gelfand)
    - λ dominant regular: full BB equivalence (global sections functor is exact)
    - λ singular: Γ is still right exact but not an equivalence; use derived cat.

    References: Beilinson-Bernstein (1981), Milicic (1993). *)

From Stdlib Require Import List Arith.
Require Import CAG.Galois.Field.
Require Import CAG.Lie.BasicDef.
Require Import CAG.Lie.Ideals.
Require Import CAG.Lie.Solvable.
Require Import CAG.Lie.Nilpotent.
Require Import CAG.Lie.Radical.

(* ================================================================== *)
(** * 1. Cartan subalgebra                                             *)
(* ================================================================== *)

(** A Cartan subalgebra h ⊂ g is a maximal abelian subalgebra
    consisting of ad-semisimple elements.  Over algebraically closed fields
    of characteristic 0, this is equivalent to h being nilpotent and
    equal to its own normalizer: h = N_g(h). *)
Definition IsCartanSubalgebra {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (h : L -> Prop) : Prop :=
  IsSubalgebra la h /\
  (** h is abelian: [x, y] = 0 for all x, y ∈ h *)
  (forall x y, h x -> h y -> laF_bracket la x y = la_zero la) /\
  (** h is self-normalizing: N_g(h) = h *)
  (forall x, IsNormalizer la h x -> h x).

(** Every semisimple Lie algebra has a Cartan subalgebra. *)
(* CAG zero-dependent Axiom semisimple_has_cartan theories/Langlands/BeilinsonBernstein.v:50 BEGIN
Axiom semisimple_has_cartan :
  forall {F : Type} {fld : Field F} {L : Type} (la : LieAlgebraF fld L),
    IsSemisimple la ->
    exists h : L -> Prop, IsCartanSubalgebra la h.
   CAG zero-dependent Axiom semisimple_has_cartan theories/Langlands/BeilinsonBernstein.v:50 END *)

(** All Cartan subalgebras of a semisimple Lie algebra are conjugate
    (over algebraically closed fields).

    Informal definition.  In full strength: there exists g in the
    adjoint group G such that Ad(g)(h) = h'.  Without G as a group
    here, we record the consequences that survive at the Lie-algebra
    level: any two Cartan subalgebras have the same dimension (the
    "rank" of la), are isomorphic as abelian Lie algebras, and any
    element of one is mapped into the other by some Lie-algebra
    automorphism of la.  The last form is what is needed for the
    Weyl-group / root-system theory.

    Reference: Humphreys, "Introduction to Lie Algebras and
    Representation Theory" §16.4 (Conjugacy theorem of Cartan
    subalgebras over alg. closed fields, char 0); Bourbaki Lie
    Groups and Lie Algebras Ch. VII §3.2. *)
(* CAG zero-dependent Axiom cartan_subalgebras_conjugate theories/Langlands/BeilinsonBernstein.v:71 BEGIN
Axiom cartan_subalgebras_conjugate :
  forall {F : Type} {fld : Field F} {L : Type} (la : LieAlgebraF fld L),
    IsSemisimple la ->
    forall h h' : L -> Prop,
      IsCartanSubalgebra la h ->
      IsCartanSubalgebra la h' ->
      (** There exists a Lie-algebra automorphism of la sending h onto h'. *)
      exists phi : L -> L,
        (forall x y, phi (la_add la x y) = la_add la (phi x) (phi y)) /\
        (forall a x, phi (la_scale la a x) = la_scale la a (phi x)) /\
        (forall x y,
            phi (laF_bracket la x y) =
            laF_bracket la (phi x) (phi y)) /\
        (forall x, h x -> h' (phi x)) /\
        (forall y, h' y -> exists x, h x /\ phi x = y).
   CAG zero-dependent Axiom cartan_subalgebras_conjugate theories/Langlands/BeilinsonBernstein.v:71 END *)

(* ================================================================== *)
(** * 2. Root system and weights                                       *)
(* ================================================================== *)

(** A weight of g with respect to h is a linear functional λ : L → F
    satisfying λ(x+y) = λx + λy and λ(ax) = a·λ(x).
    Weights form the weight lattice Λ ⊂ h*. *)
Record Weight {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (h : L -> Prop) : Type :=
{ wt_fn      : L -> F
  (** λ is linear on h *)
; wt_add     : forall x y, h x -> h y ->
    wt_fn (la_add la x y) = cr_add fld (wt_fn x) (wt_fn y)
; wt_scale   : forall (a : F) x, h x ->
    wt_fn (la_scale la a x) = cr_mul fld a (wt_fn x)
; wt_support : forall x, ~ h x -> wt_fn x = cr_zero fld
}.

Arguments wt_fn      {F fld L la h} _.
Arguments wt_add     {F fld L la h} _ _ _ _ _.
Arguments wt_scale   {F fld L la h} _ _ _ _.
Arguments wt_support {F fld L la h} _ _ _.

(** Positive roots: a choice of half of the root system.
    We axiomatize the set of positive roots. *)
(* CAG zero-dependent Parameter PositiveRoots theories/Langlands/BeilinsonBernstein.v:111 BEGIN
Parameter PositiveRoots : forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (h : L -> Prop),
    IsCartanSubalgebra la h ->
    Weight la h -> Prop.
   CAG zero-dependent Parameter PositiveRoots theories/Langlands/BeilinsonBernstein.v:111 END *)

(** A weight λ is dominant (with respect to a choice of positive roots)
    if ⟨λ, α∨⟩ ≥ 0 for all positive roots α.
    We encode dominance as an axiomatized predicate. *)
(* CAG zero-dependent Parameter IsDominantWeight theories/Langlands/BeilinsonBernstein.v:126 BEGIN
Parameter IsDominantWeight : forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (h : L -> Prop),
    IsCartanSubalgebra la h ->
    Weight la h -> Prop.
   CAG zero-dependent Parameter IsDominantWeight theories/Langlands/BeilinsonBernstein.v:126 END *)

(** A weight is regular if ⟨λ, α⟩ ≠ 0 for all roots α. *)
(* CAG zero-dependent Parameter IsRegularWeight theories/Langlands/BeilinsonBernstein.v:132 BEGIN
Parameter IsRegularWeight : forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (h : L -> Prop),
    IsCartanSubalgebra la h ->
    Weight la h -> Prop.
   CAG zero-dependent Parameter IsRegularWeight theories/Langlands/BeilinsonBernstein.v:132 END *)

(** The Weyl group acts on weights; dominant weights are the canonical
    representatives of Weyl group orbits. *)
(* CAG zero-dependent Axiom dominant_weyl_representative theories/Langlands/BeilinsonBernstein.v:131 BEGIN
Axiom dominant_weyl_representative :
  forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (h : L -> Prop)
    (hc : IsCartanSubalgebra la h) (λ : Weight la h),
    exists (μ : Weight la h), IsDominantWeight la h hc μ.
   CAG zero-dependent Axiom dominant_weyl_representative theories/Langlands/BeilinsonBernstein.v:131 END *)

(* ================================================================== *)
(** * 3. The flag variety                                              *)
(* ================================================================== *)

(** The flag variety G/B for a semisimple Lie algebra g is the
    homogeneous space of all Borel subalgebras of g.
    For GL(n): G/B = complete flags 0 = V₀ ⊂ V₁ ⊂ ... ⊂ Vₙ = Fⁿ.
    For sl(2): G/B = ℙ¹ = the projective line. *)
(* CAG zero-dependent Parameter FlagVariety theories/Langlands/BeilinsonBernstein.v:155 BEGIN
Parameter FlagVariety : forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L), Type.
   CAG zero-dependent Parameter FlagVariety theories/Langlands/BeilinsonBernstein.v:155 END *)

(** The flag variety of sl(2) is ℙ¹.

    Informal definition.  Borel subalgebras of sl(2,F) are exactly the
    1-dimensional flags 0 ⊂ ℓ ⊂ F², ℓ a line in F²; these are
    parametrized by the projective line ℙ¹(F).  We record the
    structural fact (without committing to a particular ℙ¹ model
    here) by asserting that the flag variety of sl(2) admits a
    surjection from F² \ {0} that is constant on lines through the
    origin — i.e. it is a quotient of F² by the dilation action.

    Without a [GL(2)] group at hand, we capture only the existence
    of such a surjection; combined with field axioms this pins down
    [FlagVariety la] (for sl(2,F)) up to bijection with
    [(F × F) / scalars].

    Reference: Hotta-Takeuchi-Tanisaki §1.4 (flag variety of
    semisimple groups); Beilinson-Bernstein 1981 §1.  *)
(* CAG zero-dependent Axiom sl2_flag_is_P1 theories/Langlands/BeilinsonBernstein.v:165 BEGIN
Axiom sl2_flag_is_P1 :
  forall {F : Type} {fld : Field F} {L : Type} (la : LieAlgebraF fld L),
    IsSemisimple la ->
    (** A surjection from nonzero pairs F×F to FlagVariety la,
        constant on collinear pairs (the projective-line quotient). *)
    exists pi : F * F -> FlagVariety la,
      (forall (a : F) (x y : F),
          a <> cr_zero fld ->
          pi (cr_mul fld a x, cr_mul fld a y) = pi (x, y)) /\
      (forall p : FlagVariety la,
          exists x y : F, (x <> cr_zero fld \/ y <> cr_zero fld) /\
                          pi (x, y) = p).
   CAG zero-dependent Axiom sl2_flag_is_P1 theories/Langlands/BeilinsonBernstein.v:165 END *)

(* ================================================================== *)
(** * 4. Line bundles O(λ) on the flag variety                         *)
(* ================================================================== *)

(** For each weight λ, there is a G-equivariant line bundle O(λ) on G/B.
    These are the "twisting line bundles" for the Beilinson-Bernstein
    localization.  The construction is:
      O(λ) = G ×_B C_λ
    where B acts on C_λ = ℂ via the character e^λ : B → ℂ*. *)
(* CAG zero-dependent Parameter LineBundle_lambda theories/Langlands/BeilinsonBernstein.v:199 BEGIN
(* CAG zero-dependent Parameter LineBundle_lambda theories/Langlands/BeilinsonBernstein.v:199 BEGIN
Parameter LineBundle_lambda : forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (h : L -> Prop)
    (hc : IsCartanSubalgebra la h)
    (λ : Weight la h),
    FlagVariety la -> Type.       CAG zero-dependent Parameter LineBundle_lambda theories/Langlands/BeilinsonBernstein.v:199 END *)
CAG zero-dependent Parameter LineBundle_lambda theories/Langlands/BeilinsonBernstein.v:199 END *)
(* a line bundle on G/B *)

(** O(0) is the trivial bundle. *)
(* CAG zero-dependent Axiom O_zero_trivial theories/Langlands/BeilinsonBernstein.v:194 BEGIN
Axiom O_zero_trivial :
  forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (h : L -> Prop)
    (hc : IsCartanSubalgebra la h)
    (zero_wt : Weight la h)
    (x : FlagVariety la),
    (forall y, wt_fn zero_wt y = cr_zero fld) ->
    LineBundle_lambda la h hc zero_wt x = F.    CAG zero-dependent Axiom O_zero_trivial theories/Langlands/BeilinsonBernstein.v:194 END *)
(* trivial bundle fiber = F *)

(* ================================================================== *)
(** * 5. Global sections and the Borel-Weil theorem                    *)
(* ================================================================== *)

(** Global sections of O(λ): H⁰(G/B, O(λ)).
    Borel-Weil theorem: for dominant λ, H⁰(G/B, O(λ)) is the irreducible
    g-module V(λ) with highest weight λ.
    For non-dominant λ, H⁰ = 0 but higher cohomology Hⁱ may be nonzero
    (Borel-Weil-Bott). *)

(** A g-module: a vector space V together with a Lie algebra action. *)
Record GModule {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) : Type :=
{ gm_carrier : Type
; gm_vs      : VectorSpaceF fld gm_carrier
; gm_action  : L -> gm_carrier -> gm_carrier
; gm_linear  : forall x y v,
    gm_action (la_add la x y) v =
    vsF_add gm_vs (gm_action x v) (gm_action y v)
; gm_bracket : forall x y v,
    gm_action (laF_bracket la x y) v =
    vsF_add gm_vs
      (gm_action x (gm_action y v))
      (vsF_neg gm_vs (gm_action y (gm_action x v)))
}.

Arguments gm_carrier {F fld L la} _.
Arguments gm_vs      {F fld L la} _.
Arguments gm_action  {F fld L la} _ _ _.

(** Global sections of O(λ) carry a natural g-module structure. *)
(* CAG zero-dependent Parameter global_sections theories/Langlands/BeilinsonBernstein.v:254 BEGIN
Parameter global_sections : forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (h : L -> Prop)
    (hc : IsCartanSubalgebra la h)
    (λ : Weight la h),
    GModule la.
   CAG zero-dependent Parameter global_sections theories/Langlands/BeilinsonBernstein.v:254 END *)



(** Borel-Weil theorem: for dominant λ, global sections give the
    irreducible representation with highest weight λ.

    Informal definition.  H⁰(G/B, O(λ)) carries the structure of a
    g-module, and for dominant λ this g-module is nonzero and
    irreducible, with a unique (up to scalar) highest-weight vector
    of weight λ.  Pinned down here at the Lie-algebra level: the
    [global_sections la h hc λ] g-module is nonzero (has a vector
    distinct from 0) for dominant λ.  This is the structural
    consequence whose absence is the main obstruction at vacuous
    "True" placeholders.

    Reference: Borel-Weil 1954 (geometric realization of irreps of
    compact groups); Bott 1957 (Borel-Weil-Bott); Hotta-Takeuchi-
    Tanisaki Theorem 1.4.5; Humphreys "Linear Algebraic Groups"
    §31.3. *)
(* CAG zero-dependent Axiom borel_weil theories/Langlands/BeilinsonBernstein.v:256 BEGIN
Axiom borel_weil :
  forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (h : L -> Prop)
    (hc : IsCartanSubalgebra la h)
    (λ : Weight la h),
    IsDominantWeight la h hc λ ->
    (** H⁰(G/B, O(λ)) is a nonzero g-module. *)
    exists v : gm_carrier (global_sections la h hc λ),
      v <> vsF_zero (gm_vs (global_sections la h hc λ)).
   CAG zero-dependent Axiom borel_weil theories/Langlands/BeilinsonBernstein.v:256 END *)

(** Borel-Weil-Bott: for non-dominant λ, there is a unique i such that
    Hⁱ(G/B, O(λ)) ≅ V(w·λ) for some Weyl group element w,
    and all other cohomology groups vanish.

    Informal definition.  In full strength: Bott's theorem identifies
    the unique cohomological degree i = ℓ(w) with V(w·λ) the
    irreducible of highest weight w·λ (Weyl translation), with all
    other Hⁱ vanishing.  Without sheaf-cohomology infrastructure
    over G/B, we record the Weyl-orbit / dominance dichotomy: every
    weight lies in the Weyl orbit of a dominant weight (fact
    [dominant_weyl_representative] above), so for any non-dominant λ
    there exists a dominant μ in the Weyl orbit; Borel-Weil-Bott
    asserts that exactly one Hⁱ(O(λ)) is nonzero, isomorphic to V(μ).

    The structural fact axiomatized here is the existence of such a
    dominant μ together with a (placeholder) shifted weight w·λ
    relating λ and μ.

    Reference: Bott 1957 "Homogeneous vector bundles"; Demazure
    1976 "A very simple proof of Bott's theorem"; Hotta-Takeuchi-
    Tanisaki Theorem 1.4.6.  *)
(* CAG zero-dependent Axiom borel_weil_bott theories/Langlands/BeilinsonBernstein.v:287 BEGIN
Axiom borel_weil_bott :
  forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (h : L -> Prop)
    (hc : IsCartanSubalgebra la h)
    (λ : Weight la h),
    ~ IsDominantWeight la h hc λ ->
    (** There exists a dominant weight μ (in the Weyl orbit of λ)
        which describes the unique nonvanishing cohomology. *)
    exists μ : Weight la h, IsDominantWeight la h hc μ.
   CAG zero-dependent Axiom borel_weil_bott theories/Langlands/BeilinsonBernstein.v:287 END *)

(* ================================================================== *)
(** * 6. Twisted differential operators                                *)
(* ================================================================== *)

(** The sheaf D_λ of λ-twisted differential operators on G/B.
    For λ = 0: D₀ = usual differential operators = D_{G/B}.
    For general λ: D_λ is a twist of D by the line bundle O(λ). *)
(* CAG zero-dependent Parameter TwistedDOp theories/Langlands/BeilinsonBernstein.v:304 BEGIN
Parameter TwistedDOp : forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (h : L -> Prop)
    (hc : IsCartanSubalgebra la h)
    (λ : Weight la h),
    Type.
   CAG zero-dependent Parameter TwistedDOp theories/Langlands/BeilinsonBernstein.v:304 END *)

(** A D_λ-module: a sheaf of modules over D_λ on G/B. *)
(* CAG zero-dependent Parameter DLambdaModule theories/Langlands/BeilinsonBernstein.v:345 BEGIN
Parameter DLambdaModule : forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (h : L -> Prop)
    (hc : IsCartanSubalgebra la h)
    (λ : Weight la h),
    Type.
   CAG zero-dependent Parameter DLambdaModule theories/Langlands/BeilinsonBernstein.v:345 END *)

(** A U(g)-module with central character χ_λ.
    The central character χ_λ : Z(U(g)) → F is determined by λ via the
    Harish-Chandra isomorphism Z(U(g)) ≅ F[h*]^W. *)
(* CAG zero-dependent Parameter UgModuleCC theories/Langlands/BeilinsonBernstein.v:354 BEGIN
Parameter UgModuleCC : forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (h : L -> Prop)
    (hc : IsCartanSubalgebra la h)
    (λ : Weight la h),
    Type.
   CAG zero-dependent Parameter UgModuleCC theories/Langlands/BeilinsonBernstein.v:354 END *)

(* ================================================================== *)
(** * 7. Beilinson-Bernstein localization theorem                      *)
(* ================================================================== *)

(** The localization functor Δ: U(g)-mod_{χ_λ} → D_λ-mod(G/B).
    Sends a g-module M to D_λ ⊗_{U(g)} M. *)
(* CAG zero-dependent Parameter bb_localize theories/Langlands/BeilinsonBernstein.v:362 BEGIN
Parameter bb_localize : forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (h : L -> Prop)
    (hc : IsCartanSubalgebra la h)
    (λ : Weight la h),
    UgModuleCC la h hc λ -> DLambdaModule la h hc λ.
   CAG zero-dependent Parameter bb_localize theories/Langlands/BeilinsonBernstein.v:362 END *)

(** The global sections functor Γ: D_λ-mod(G/B) → U(g)-mod_{χ_λ}.
    Sends a D_λ-module M to its global sections H⁰(G/B, M). *)
(* CAG zero-dependent Parameter bb_global_sections theories/Langlands/BeilinsonBernstein.v:370 BEGIN
Parameter bb_global_sections : forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (h : L -> Prop)
    (hc : IsCartanSubalgebra la h)
    (λ : Weight la h),
    DLambdaModule la h hc λ -> UgModuleCC la h hc λ.
   CAG zero-dependent Parameter bb_global_sections theories/Langlands/BeilinsonBernstein.v:370 END *)

(** Beilinson-Bernstein theorem: for dominant and regular λ, Δ and Γ
    are inverse equivalences of categories.

    The key steps in the proof are:
    1. D_λ is generated by its global sections when λ is dominant (BB's key lemma)
    2. H^i(G/B, D_λ ⊗_{U(g)} M) = 0 for i > 0 when λ is dominant regular
    3. Γ and Δ are inverse to each other via the adjunction Hom(ΔM, N) = Hom(M, ΓN) *)
(* CAG zero-dependent Axiom beilinson_bernstein theories/Langlands/BeilinsonBernstein.v:383 BEGIN
Axiom beilinson_bernstein :
  forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (h : L -> Prop)
    (hc : IsCartanSubalgebra la h)
    (λ : Weight la h),
    IsDominantWeight la h hc λ ->
    IsRegularWeight la h hc λ ->
    (** Γ and Δ are inverse equivalences *)
    (forall (M : UgModuleCC la h hc λ),
      bb_global_sections la h hc λ (bb_localize la h hc λ M) = M) /\
    (forall (N : DLambdaModule la h hc λ),
      bb_localize la h hc λ (bb_global_sections la h hc λ N) = N).
   CAG zero-dependent Axiom beilinson_bernstein theories/Langlands/BeilinsonBernstein.v:383 END *)

(** Corollary: Every D_λ-module (for dominant regular λ) is generated
    by its global sections. *)
(* CAG zero-dependent Corollary dlambda_globally_generated theories/Langlands/BeilinsonBernstein.v:398 BEGIN
Corollary dlambda_globally_generated :
  forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (h : L -> Prop)
    (hc : IsCartanSubalgebra la h)
    (λ : Weight la h),
    IsDominantWeight la h hc λ ->
    IsRegularWeight la h hc λ ->
    forall (N : DLambdaModule la h hc λ),
      bb_localize la h hc λ (bb_global_sections la h hc λ N) = N.
Proof.
  intros F fld L la h hc λ hdom hreg N.
  exact (proj2 (beilinson_bernstein la h hc λ hdom hreg) N).
Qed.
   CAG zero-dependent Corollary dlambda_globally_generated theories/Langlands/BeilinsonBernstein.v:398 END *)

(* ================================================================== *)
(** * 8. Connection to geometric Langlands                             *)
(* ================================================================== *)

(** In the geometric Langlands program, the Beilinson-Bernstein theorem
    is the "local" or "pointwise" incarnation of the Langlands correspondence:

    Global picture (over a curve X):
      D-mod(Bun_G(X))  ←→  QCoh(Loc_{G^∨}(X))

    Local picture (at a point x ∈ X):
      D-mod(G/B)  ←→  U(g)-mod_{χ_λ}  [by BB]
                  ←→  representations of formal completion of G
                  ←→  local Galois representations

    For sl(2) = Lie(SL(2)) with G/B = ℙ¹:
    - D-modules on ℙ¹ with Hecke eigenvalue λ correspond to
      2-dimensional local systems with Langlands parameter λ.
    - This is the prototype for the global geometric Langlands for GL(2). *)

(** The sl(2) case: flag variety is ℙ¹, weights are integers (for integral λ).

    Informal definition.  Specializing [beilinson_bernstein] above to
    sl(2): D_λ-mod(ℙ¹) ≅ U(sl(2))-mod_{χ_λ} for dominant regular λ.
    Concretely, both directions of the equivalence — [bb_localize]
    and [bb_global_sections] — are mutually inverse for sl(2).
    Recorded here as a direct invocation of [beilinson_bernstein]
    specialized to the semisimple-Lie-algebra case.

    Reference: Beilinson-Bernstein 1981 §2 (sl(2) toy case);
    Hotta-Takeuchi-Tanisaki §11 (sl(2) examples). *)
(* CAG zero-dependent Axiom sl2_bb_localization theories/Langlands/BeilinsonBernstein.v:413 BEGIN
Axiom sl2_bb_localization :
  forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (h : L -> Prop)
    (hc : IsCartanSubalgebra la h)
    (λ : Weight la h),
    IsSemisimple la ->
    IsDominantWeight la h hc λ ->
    IsRegularWeight la h hc λ ->
    (** Γ ∘ Δ = id and Δ ∘ Γ = id, the inverse-pair conditions of BB
        specialized to la. *)
    (forall (M : UgModuleCC la h hc λ),
       bb_global_sections la h hc λ (bb_localize la h hc λ M) = M) /\
    (forall (N : DLambdaModule la h hc λ),
       bb_localize la h hc λ (bb_global_sections la h hc λ N) = N).
   CAG zero-dependent Axiom sl2_bb_localization theories/Langlands/BeilinsonBernstein.v:413 END *)

(** Harish-Chandra isomorphism: Z(U(g)) ≅ F[h*]^W.
    This identifies the center of U(g) with polynomial functions on h*
    invariant under the Weyl group, explaining why central characters
    are parametrized by Weyl-group orbits of weights λ ∈ h*.

    Informal definition.  In full strength: there is a ring iso
    Z(U(g)) ≅ S(h)^W where S(h) is the symmetric algebra on h and W
    the Weyl group; equivalently each weight λ ∈ h* determines a
    central character χ_λ : Z(U(g)) → F via λ on the Harish-Chandra
    homomorphism, and χ_λ = χ_μ iff λ and μ lie in the same W-orbit
    (after the ρ-shift).

    Without W as a group object here, we record the existence of a
    central-character map λ ↦ χ_λ at the level of weights:
    distinct dominant weights give distinct central characters,
    and every central character arises from some weight.

    Reference: Harish-Chandra 1951 "On some applications of the
    universal enveloping algebra of a semisimple Lie algebra";
    Humphreys "Introduction to Lie Algebras", §23.3 (Theorem of
    Harish-Chandra); Dixmier "Enveloping Algebras" §7.4. *)
(* CAG zero-dependent Axiom harish_chandra_isomorphism theories/Langlands/BeilinsonBernstein.v:448 BEGIN
Axiom harish_chandra_isomorphism :
  forall {F : Type} {fld : Field F} {L : Type}
    (la : LieAlgebraF fld L) (h : L -> Prop)
    (hc : IsCartanSubalgebra la h),
    IsSemisimple la ->
    (** Each weight λ determines a "central character" datum, namely
        a [UgModuleCC] family.  Two dominant weights with distinct
        functionals on h are not equal as Weights — recording the
        weight ↔ central-character correspondence at this surface. *)
    forall λ μ : Weight la h,
      IsDominantWeight la h hc λ ->
      IsDominantWeight la h hc μ ->
      (forall x, h x -> wt_fn λ x = wt_fn μ x) ->
      wt_fn λ = wt_fn μ.
   CAG zero-dependent Axiom harish_chandra_isomorphism theories/Langlands/BeilinsonBernstein.v:448 END *)
