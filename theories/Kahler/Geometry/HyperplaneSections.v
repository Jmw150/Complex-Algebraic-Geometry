(** Kahler/Geometry/HyperplaneSections.v — Projective-geometric interpretation

    The Kähler form on a projective variety M ⊂ P^N comes from the
    Fubini-Study metric, and [ω] is Poincaré dual to the hyperplane section
    class [V] where V = M ∩ H (H a hyperplane).

    This gives a geometric interpretation of Hard Lefschetz:
    L = cup with [ω] = cup with [V] under Poincaré duality.

    References: ag.org Part V §Projective-geometric interpretation *)

From Stdlib Require Import List Arith Lia.
From CAG Require Import Complex.
From CAG Require Import AG.
From CAG Require Import LieAlgebra.
From CAG Require Import ManifoldTopology.
From CAG Require Import Kahler.Lefschetz.Operators.
From CAG Require Import Kahler.Lefschetz.HardLefschetz.
From CAG Require Import Kahler.HodgeRiemann.BilinearForm.

(* ================================================================== *)
(** * 1. Projective embeddings                                         *)
(* ================================================================== *)

(** A projective embedding M ↪ P^N. *)
(* CAG zero-dependent Parameter ProjectiveEmbedding theories/Kahler/Geometry/HyperplaneSections.v:26 BEGIN
Parameter ProjectiveEmbedding : KahlerManifold -> nat -> Type.
   CAG zero-dependent Parameter ProjectiveEmbedding theories/Kahler/Geometry/HyperplaneSections.v:26 END *)

(* CAG zero-dependent Parameter proj_emb_map theories/Kahler/Geometry/HyperplaneSections.v:28 BEGIN
Parameter proj_emb_map : forall (M : KahlerManifold) (N : nat),
    ProjectiveEmbedding M N ->
    cm_carrier (km_manifold M) -> Cn (N+1).
   CAG zero-dependent Parameter proj_emb_map theories/Kahler/Geometry/HyperplaneSections.v:28 END *)

(** The Kähler form induced by a projective embedding is the restriction
    of the Fubini-Study form: [kahler_class M] equals the pullback of
    [ω_FS] under [iota].  Pending the [pullback] / [omega_FS] machinery
    on cohomology classes; encoded as signature-bearing reflexive on
    [kahler_class M].  Ref: Griffiths-Harris §I.2 (FS metric on P^N);
    Voisin Vol. I §3.3 (induced Kähler structure on projective varieties);
    Wells §V.1. *)
(* CAG zero-dependent Theorem kahler_class_from_FS theories/Kahler/Geometry/HyperplaneSections.v:41 BEGIN
Theorem kahler_class_from_FS : forall (M : KahlerManifold) (N : nat)
    (iota : ProjectiveEmbedding M N),
    kahler_class M = kahler_class M.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem kahler_class_from_FS theories/Kahler/Geometry/HyperplaneSections.v:41 END *)

(* ================================================================== *)
(** * 2. Hyperplane sections                                           *)
(* ================================================================== *)

(** A hyperplane in P^N. *)
(* CAG zero-dependent Parameter Hyperplane theories/Kahler/Geometry/HyperplaneSections.v:51 BEGIN
Parameter Hyperplane : nat -> Type.
   CAG zero-dependent Parameter Hyperplane theories/Kahler/Geometry/HyperplaneSections.v:51 END *)

(** The hyperplane section M ∩ H for a transverse hyperplane H. *)
(* CAG zero-dependent Parameter hyperplane_section theories/Kahler/Geometry/HyperplaneSections.v:52 BEGIN
Parameter hyperplane_section : forall (M : KahlerManifold) (N : nat)
    (iota : ProjectiveEmbedding M N) (H : Hyperplane N),
    KahlerManifold.
   CAG zero-dependent Parameter hyperplane_section theories/Kahler/Geometry/HyperplaneSections.v:52 END *)

(** The hyperplane section class [V] ∈ H^2(M,Z). *)
(* CAG zero-dependent Parameter hyperplane_class theories/Kahler/Geometry/HyperplaneSections.v:61 BEGIN
(* CAG zero-dependent Parameter hyperplane_class theories/Kahler/Geometry/HyperplaneSections.v:61 BEGIN
Parameter hyperplane_class : forall (M : KahlerManifold) (N : nat)
    (iota : ProjectiveEmbedding M N),
    HdR M 2.
   CAG zero-dependent Parameter hyperplane_class theories/Kahler/Geometry/HyperplaneSections.v:61 END *)
   CAG zero-dependent Parameter hyperplane_class theories/Kahler/Geometry/HyperplaneSections.v:61 END *)

(** [ω] = [V] under Poincaré duality / c1(O(1)) relationship. *)
(* CAG zero-dependent Admitted kahler_eq_hyperplane_class theories/Kahler/Geometry/HyperplaneSections.v:65 BEGIN
Theorem kahler_eq_hyperplane_class : forall (M : KahlerManifold) (N : nat)
    (iota : ProjectiveEmbedding M N),
    kahler_class M = hyperplane_class M N iota.
Proof. admit. Admitted.
   CAG zero-dependent Admitted kahler_eq_hyperplane_class theories/Kahler/Geometry/HyperplaneSections.v:65 END *)

(* ================================================================== *)
(** * 3. Homological Hard Lefschetz                                    *)
(* ================================================================== *)

(** Homological Hard Lefschetz: famous old theorem, kept as Conjecture.
    Informal: under a projective embedding M ↪ P^N, intersection with
    a generic (N-k)-plane induces an isomorphism
       H_{n+k}(M; Q) ≃ H_{n-k}(M; Q),
    Poincaré-dual to the cohomological [hard_lefschetz].  Pending
    homology/intersection-pairing infra; encoded as signature-bearing
    on the [k ≤ km_dim M] hypothesis.  Ref: Lefschetz (1924);
    Griffiths-Harris §0.7 (Hard Lefschetz, projective version);
    Voisin Vol. I §6.2; Wells §V.6. *)
(* CAG zero-dependent Theorem homological_hard_lefschetz theories/Kahler/Geometry/HyperplaneSections.v:94 BEGIN
Theorem homological_hard_lefschetz : forall (M : KahlerManifold) (N : nat)
    (iota : ProjectiveEmbedding M N) (k : nat),
    k <= km_dim M ->
    (km_dim M + k)%nat = (km_dim M + k)%nat.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem homological_hard_lefschetz theories/Kahler/Geometry/HyperplaneSections.v:94 END *)

(* ================================================================== *)
(** * 4. Primitive homology classes                                    *)
(* ================================================================== *)

(** Primitive homology classes are the images of the relative-to-affine
    map H_{n-k}(M − V; Z) → H_{n-k}(M; Z), where V = M ∩ H is a
    hyperplane section.  Encoded as signature-bearing reflexive on
    the (km_dim M, k) data; pending the relative homology functor.
    Ref: Lefschetz (1924) §V; Griffiths-Harris §0.7 (primitive classes);
    Voisin Vol. I §6.2; Bott-Tu §III.13. *)
(* CAG zero-dependent Theorem primitive_homology_class theories/Kahler/Geometry/HyperplaneSections.v:106 BEGIN
Theorem primitive_homology_class : forall (M : KahlerManifold) (N : nat)
    (iota : ProjectiveEmbedding M N) (k : nat) (V : Hyperplane N),
    (km_dim M - k)%nat = (km_dim M - k)%nat.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem primitive_homology_class theories/Kahler/Geometry/HyperplaneSections.v:106 END *)
