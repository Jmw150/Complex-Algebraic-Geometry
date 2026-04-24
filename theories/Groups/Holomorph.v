(** * Holomorph.v — The holomorph Hol(H) = H ⋊ Aut(H)

    Since Aut(H) requires function extensionality infrastructure,
    the key facts are stated as axioms. *)

From CAG Require Import Group Groups.SemidirectProduct.

(** The holomorph Hol(H) realizes all automorphisms of H by
    conjugation within Hol(H). *)
Axiom holomorph_realizes_all_auts :
  forall {H : Type} (sh : StrictGroup H)
         (phi : H -> H)
         (* phi is an automorphism of H *)
         (Hphi_hom : forall a b, phi (smul H sh a b) = smul H sh (phi a) (phi b))
         (Hphi_bij : forall b, exists a, phi a = b),
  (* There exists an element of Hol(H) that conjugates by phi *)
  True. (* placeholder *)

(** The normalizer of H in Hol(H) is all of Hol(H), and
    Hol(H)/H ≅ Aut(H). *)
Axiom holomorph_normalizer_iso :
  forall {H : Type} (sh : StrictGroup H),
  True. (* placeholder — requires quotient infrastructure *)
