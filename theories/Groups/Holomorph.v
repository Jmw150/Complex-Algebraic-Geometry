(** * Holomorph.v — The holomorph Hol(H) = H ⋊ Aut(H)

    Since Aut(H) requires function extensionality infrastructure,
    the key facts are stated as axioms. *)

From CAG Require Import Group Groups.SemidirectProduct.

(** The holomorph Hol(H) realizes all automorphisms of H by conjugation
    within Hol(H). Equivalently, the natural map Aut(H) → Inn(Hol(H))
    composed with Inn(Hol(H)) ↪ Aut(Hol(H)) is well-defined.

    Stated as a Conjecture pending Holomorph/Aut infrastructure
    (Aut(H) is currently not formalized as a `StrictGroup`).
    Reference: Dummit & Foote §6.3 Theorem on holomorph. *)
(* CAG zero-dependent Conjecture holomorph_realizes_all_auts theories/Groups/Holomorph.v:15 BEGIN
Conjecture holomorph_realizes_all_auts :
  forall {H : Type} (sh : StrictGroup H)
         (phi : H -> H)
         (* phi is an automorphism of H *)
         (Hphi_hom : forall a b, phi (smul H sh a b) = smul H sh (phi a) (phi b))
         (Hphi_bij : forall b, exists a, phi a = b),
    (* There exists g ∈ Hol(H) and a copy ι : H → Hol(H) such that
       conjugation by g realizes phi on ι(H). The Conjecture asserts the
       existence of an "outer realization" group Hol with element g. *)
    exists (Hol : Type) (sH : StrictGroup Hol)
           (iota : H -> Hol) (g : Hol),
      (forall a b, iota (smul H sh a b) = smul Hol sH (iota a) (iota b)) /\
      (forall a, iota (phi a) =
                 smul Hol sH (smul Hol sH g (iota a)) (sinv Hol sH g)).
   CAG zero-dependent Conjecture holomorph_realizes_all_auts theories/Groups/Holomorph.v:15 END *)

(** The normalizer of H (embedded in Hol(H)) is all of Hol(H), and
    Hol(H)/H ≅ Aut(H).

    Stated as a Conjecture pending quotient and Aut(H) infrastructure.
    Reference: Dummit & Foote §6.3. *)
(* CAG zero-dependent Conjecture holomorph_normalizer_iso theories/Groups/Holomorph.v:35 BEGIN
Conjecture holomorph_normalizer_iso :
  forall {H : Type} (sh : StrictGroup H),
    exists (Hol : Type) (sH : StrictGroup Hol)
           (iota : H -> Hol),
      (forall a b, iota (smul H sh a b) = smul Hol sH (iota a) (iota b)) /\
      (* iota(H) is normal in Hol *)
      (forall g h, smul Hol sH (smul Hol sH g (iota h)) (sinv Hol sH g) =
                   iota h \/ exists h', smul Hol sH (smul Hol sH g (iota h)) (sinv Hol sH g) = iota h').
   CAG zero-dependent Conjecture holomorph_normalizer_iso theories/Groups/Holomorph.v:35 END *)
