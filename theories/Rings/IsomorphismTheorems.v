(** * IsomorphismTheorems.v — Ring isomorphism theorems (axiomatic)

    The four standard isomorphism theorems for rings (a.k.a. the
    "Noether isomorphism theorems") are bookkeeping-level structural
    facts.  Their statements are stable; we record them here as
    paper-attributable Axioms because the project does not yet have
    a formal [RingIso] record nor a fully-developed quotient-ring
    universal property (only [QuotientRing] + [quot_proj] +
    [quotient_universal] are available from [Rings.Quotients]).

    History note: prior to β R26 (2026-05-01) each statement was a
    bare =Axiom = forall …, True= placeholder.  β R26 replaced each
    body with a concrete logical statement following the γ R34
    pattern (paper-attributable axiom + informal-definition comment),
    using the existing infrastructure ([RingHom], [kernel_ideal],
    [image_subring], [QuotientRing], [ideal_sum], [is_ideal]).

    References: Dummit-Foote ch. 7 §7.3 ("Ring Homomorphisms and
    Quotient Rings", Theorems 7, 8, 16, 17, 18); Hungerford
    "Algebra" ch. III §2 ("The Isomorphism Theorems"); Lang
    "Algebra" ch. II §1.  *)

From CAG Require Import Rings.Ring Rings.Ideals Rings.Quotients.

(* ================================================================== *)
(** ** First Isomorphism Theorem: R/ker(φ) ≅ im(φ) *)
(* ================================================================== *)

(** For a ring hom φ : R → S, the canonical surjection π : R → R/ker(φ)
    factors φ uniquely through an injective ring hom
    φ̄ : R/ker(φ) → S whose image is im(φ).  Concretely, there exists
    a ring hom from R/ker(φ) into S which (a) recovers φ via
    pre-composition with the projection, and (b) lands in the image
    subring [image_subring r s phi] (and surjects onto it).

    Informal definition.  φ̄([a]) := φ(a); well-defined because
    a ≡ b mod ker(φ) ⇒ φ(a) = φ(b); injective because φ̄([a]) = 0
    ⇒ φ(a) = 0 ⇒ a ∈ ker(φ) ⇒ [a] = 0; surjective onto im(φ) by
    construction.

    Reference: Dummit-Foote Theorem 7.3.16 (First Isomorphism
    Theorem for rings); Lang Algebra II.1. *)
(* CAG zero-dependent Axiom ring_first_iso theories/Rings/IsomorphismTheorems.v:43 BEGIN
Axiom ring_first_iso :
  forall {R S : Type} (r : Ring R) (s : Ring S)
         (phi : RingHom r s),
  let K  := kernel_ideal r s phi in
  let HK := kernel_is_ideal r s phi in
  exists phibar : RingHom (QuotientRing r K HK) s,
    (** φ̄ ∘ π = φ : factorization through the projection *)
    (forall a : R,
       rhom_fn phibar (rhom_fn (quot_proj r K HK) a) = rhom_fn phi a)
    /\
    (** φ̄ is injective: kernel of φ̄ is trivial *)
    (forall x : QuotientCarrier r K,
       rhom_fn phibar x = rzero S s ->
       x = rzero (QuotientCarrier r K) (QuotientRing r K HK))
    /\
    (** φ̄ surjects onto im(φ) *)
    (forall y : S, image_subring r s phi y ->
       exists x : QuotientCarrier r K, rhom_fn phibar x = y).
   CAG zero-dependent Axiom ring_first_iso theories/Rings/IsomorphismTheorems.v:43 END *)

(* ================================================================== *)
(** ** Second Isomorphism Theorem: (A+B)/B ≅ A/(A∩B) *)
(* ================================================================== *)

(** If A and B are ideals of R, then A+B is an ideal, A∩B is an
    ideal of A (regarded as a (non-unital) subring), and there is
    a canonical isomorphism (A+B)/B ≅ A/(A∩B).

    Informal definition.  The map A → (A+B)/B sending a ↦ a + B has
    kernel A∩B; its image is (A+B)/B (every coset (a+b)+B equals
    a+B since b ∈ B).  The First Isomorphism Theorem then gives the
    claimed isomorphism.

    The full categorical statement requires a [RingIso] record and a
    quotient construction for non-unital subrings; here we record
    the structural fact that A∩B is an ideal of R (the "inner"
    ingredient needed by the proof).

    Reference: Dummit-Foote Theorem 7.3.17 (Second / "Diamond"
    Isomorphism Theorem); Hungerford III.2.13. *)
(* CAG zero-dependent Axiom ring_second_iso theories/Rings/IsomorphismTheorems.v:82 BEGIN
Axiom ring_second_iso :
  forall {R : Type} (r : Ring R)
         (A B : R -> Prop)
         (HA : is_ideal r A) (HB : is_ideal r B),
    (** A∩B is an ideal of R *)
    is_ideal r (fun x => A x /\ B x)
    /\
    (** A+B is an ideal of R *)
    is_ideal r (ideal_sum r A B)
    /\
    (** A ⊆ A+B and B ⊆ A+B (containment of summands in the sum) *)
    (forall x, A x -> ideal_sum r A B x)
    /\
    (forall x, B x -> ideal_sum r A B x).
   CAG zero-dependent Axiom ring_second_iso theories/Rings/IsomorphismTheorems.v:82 END *)

(* ================================================================== *)
(** ** Third Isomorphism Theorem: (R/I)/(J/I) ≅ R/J when I ⊆ J *)
(* ================================================================== *)

(** If I ⊆ J are both ideals of R, then J/I is an ideal of R/I and
    there is a canonical ring isomorphism (R/I)/(J/I) ≅ R/J.

    Informal definition.  The composition R → R/I → (R/I)/(J/I) is
    a surjective ring hom with kernel J; the First Isomorphism
    Theorem gives R/J ≅ (R/I)/(J/I).

    We axiomatize the existence of a surjective ring homomorphism
    R/I → R/J under I ⊆ J (the "obvious" projection), which is the
    structural input needed; combined with [ring_first_iso] this
    yields the full Third Isomorphism Theorem once the kernel is
    identified with J/I.

    Reference: Dummit-Foote Theorem 7.3.18 (Third Isomorphism
    Theorem); Hungerford III.2.14. *)
(* CAG zero-dependent Axiom ring_third_iso theories/Rings/IsomorphismTheorems.v:116 BEGIN
Axiom ring_third_iso :
  forall {R : Type} (r : Ring R)
         (I J : R -> Prop)
         (HI : is_ideal r I) (HJ : is_ideal r J)
         (Hincl : forall x, I x -> J x),
  exists psi : RingHom (QuotientRing r I HI) (QuotientRing r J HJ),
    (** ψ commutes with the projections: ψ(π_I(a)) = π_J(a). *)
    (forall a : R,
       rhom_fn psi (rhom_fn (quot_proj r I HI) a) =
       rhom_fn (quot_proj r J HJ) a)
    /\
    (** ψ is surjective. *)
    (forall y : QuotientCarrier r J,
       exists x : QuotientCarrier r I, rhom_fn psi x = y).
   CAG zero-dependent Axiom ring_third_iso theories/Rings/IsomorphismTheorems.v:116 END *)

(* ================================================================== *)
(** ** Fourth Isomorphism Theorem: ideal correspondence *)
(*
   Lattice / "Correspondence Theorem": ideals of R/I are in
   inclusion-preserving bijection with ideals of R that contain I.
*)
(* ================================================================== *)

(** Informal definition.  Let π : R → R/I be the projection.  The
    map [J ↦ π(J)] is a bijection between ideals of R containing I
    and ideals of R/I, with inverse [Jbar ↦ π⁻¹(Jbar)].  Both maps
    preserve inclusion, sums, intersections, products, and primality.

    Here we record the structural surjectivity at the level of
    individual ideals: every ideal of R/I is the image (under π) of
    its preimage in R, which is an ideal of R that contains I.

    Reference: Dummit-Foote Theorem 7.3.19 ("Lattice Isomorphism
    Theorem" / Fourth Isomorphism Theorem); Hungerford III.2.15. *)
(* CAG zero-dependent Axiom ring_fourth_iso theories/Rings/IsomorphismTheorems.v:147 BEGIN
Axiom ring_fourth_iso :
  forall {R : Type} (r : Ring R)
         (I : R -> Prop)
         (HI : is_ideal r I),
    forall (Jbar : QuotientCarrier r I -> Prop),
      is_ideal (QuotientRing r I HI) Jbar ->
    exists J : R -> Prop,
      is_ideal r J
      /\ (forall x, I x -> J x)                                   (** I ⊆ J *)
      /\ (forall a, J a <-> Jbar (rhom_fn (quot_proj r I HI) a)).    CAG zero-dependent Axiom ring_fourth_iso theories/Rings/IsomorphismTheorems.v:147 END *)
(** J = π⁻¹(Jbar) *)
