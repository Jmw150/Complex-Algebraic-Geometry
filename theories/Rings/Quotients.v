(** * Quotients.v — Quotient rings (axiomatic) *)

From CAG Require Import Rings.Ring Rings.Ideals.
From Stdlib Require Import FunctionalExtensionality PropExtensionality.

(* ================================================================== *)
(** ** Congruence relation mod an ideal *)
(* ================================================================== *)

(** a ≡ b (mod I) iff ∃ d ∈ I, a + d = b *)
Definition quotient_rel {R : Type} (r : Ring R) (I : R -> Prop) (a b : R) : Prop :=
  exists d, I d /\ radd R r a d = b.

(* ================================================================== *)
(** ** Quotient ring (axiomatic) *)
(*
   Since Rocq's type theory does not have quotient types natively,
   we axiomatize the quotient ring construction.
*)
(* ================================================================== *)

(* CAG zero-dependent Axiom QuotientCarrier theories/Rings/Quotients.v:22 BEGIN
Axiom QuotientCarrier : forall {R : Type} (r : Ring R) (I : R -> Prop), Type.
   CAG zero-dependent Axiom QuotientCarrier theories/Rings/Quotients.v:22 END *)

(* CAG zero-dependent Axiom QuotientRing theories/Rings/Quotients.v:24 BEGIN
Axiom QuotientRing : forall {R : Type} (r : Ring R) (I : R -> Prop)
    (HI : is_ideal r I), Ring (QuotientCarrier r I).
   CAG zero-dependent Axiom QuotientRing theories/Rings/Quotients.v:24 END *)

(* CAG zero-dependent Axiom quot_proj theories/Rings/Quotients.v:27 BEGIN
(* CAG zero-dependent Axiom quot_proj theories/Rings/Quotients.v:27 BEGIN
Axiom quot_proj : forall {R : Type} (r : Ring R) (I : R -> Prop)
    (HI : is_ideal r I), RingHom r (QuotientRing r I HI).
   CAG zero-dependent Axiom quot_proj theories/Rings/Quotients.v:27 END *)
   CAG zero-dependent Axiom quot_proj theories/Rings/Quotients.v:27 END *)

(* CAG zero-dependent Axiom quot_proj_surj theories/Rings/Quotients.v:27 BEGIN
Axiom quot_proj_surj : forall {R : Type} (r : Ring R) (I : R -> Prop)
    (HI : is_ideal r I) (x : QuotientCarrier r I),
    exists a : R, rhom_fn (quot_proj r I HI) a = x.
   CAG zero-dependent Axiom quot_proj_surj theories/Rings/Quotients.v:27 END *)

(* CAG zero-dependent Axiom quot_proj_kernel theories/Rings/Quotients.v:31 BEGIN
Axiom quot_proj_kernel : forall {R : Type} (r : Ring R) (I : R -> Prop)
    (HI : is_ideal r I) (a : R),
    rhom_fn (quot_proj r I HI) a =
      rzero (QuotientCarrier r I) (QuotientRing r I HI) <-> I a.
   CAG zero-dependent Axiom quot_proj_kernel theories/Rings/Quotients.v:31 END *)

(* ================================================================== *)
(** ** Universal property of the quotient *)
(* ================================================================== *)

(* CAG zero-dependent Axiom quotient_universal theories/Rings/Quotients.v:40 BEGIN
Axiom quotient_universal :
  forall {R S : Type} (r : Ring R) (s : Ring S) (I : R -> Prop)
         (HI : is_ideal r I)
         (phi : RingHom r s)
         (Hker : forall a, I a -> rhom_fn phi a = rzero S s),
  exists! phibar : RingHom (QuotientRing r I HI) s,
    forall a : R,
      rhom_fn phibar (rhom_fn (quot_proj r I HI) a) = rhom_fn phi a.
   CAG zero-dependent Axiom quotient_universal theories/Rings/Quotients.v:40 END *)
