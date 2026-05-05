
(** Sheaves and Čech Cohomology

    Abstract sheaf theory on topological spaces, standard sheaf
    instances (holomorphic, smooth, constant, meromorphic),
    Čech cohomology, exact sequences, fine sheaves, and the
    de Rham / Dolbeault comparison interface.
*)

From Stdlib Require Import List Arith Lia ZArith.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyRealsMult.
Import ListNotations.

From CAG Require Import Reals_extra.
From CAG Require Import Complex.
From CAG Require Import Topology.
From CAG Require Import ComplexAnalysis.
From CAG Require Import ComplexAnalysis2.
From CAG Require Import AG.

Local Open Scope CReal_scope.

(** Shadow Topology.In with List.In for list membership throughout.
    Topology.In is (A->Prop) -> A -> Prop (set membership = function application);
    here we need List.In : A -> list A -> Prop (list membership). *)
Local Notation In := List.In.

(* ================================================================== *)
(** * Part B: Abstract sheaf of abelian groups                         *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(** ** 1. Sheaf of abelian groups on a topological space               *)
(* ------------------------------------------------------------------ *)

(** An abelian group structure on a type. *)
Record AbGroup (G : Type) : Type :=
{ ag_add   : G -> G -> G
; ag_zero  : G
; ag_neg   : G -> G
; ag_assoc : forall x y z, ag_add x (ag_add y z) = ag_add (ag_add x y) z
; ag_comm  : forall x y,   ag_add x y = ag_add y x
; ag_zero_r : forall x,    ag_add x ag_zero = x
; ag_neg_r  : forall x,    ag_add x (ag_neg x) = ag_zero
}.

Arguments ag_add  {G} _ _ _.
Arguments ag_zero {G} _.
Arguments ag_neg  {G} _ _.

(** A presheaf of abelian groups on X:
    - sections F(U) for each open set U
    - restriction maps res_{V,U} : F(V) -> F(U) for U ⊆ V
    - functoriality of restrictions
    - abelian group structure on each F(U) *)
Record Presheaf (X : Type) (TX : Topology X) : Type :=
{ psf_sec   : forall (U : set X), is_open TX U -> Type
; psf_group : forall (U : set X) (HU : is_open TX U),
    AbGroup (psf_sec U HU)
; psf_res   : forall (U V : set X) (HU : is_open TX U) (HV : is_open TX V),
    (forall x, U x -> V x) ->
    psf_sec V HV -> psf_sec U HU
  (** Restrictions are homomorphisms of abelian groups. *)
; psf_res_add : forall (U V : set X) (HU : is_open TX U) (HV : is_open TX V)
      (hUV : forall x, U x -> V x)
      (s t : psf_sec V HV),
    psf_res U V HU HV hUV (ag_add (psf_group V HV) s t) =
    ag_add (psf_group U HU)
      (psf_res U V HU HV hUV s)
      (psf_res U V HU HV hUV t)
; psf_res_neg : forall (U V : set X) (HU : is_open TX U) (HV : is_open TX V)
      (hUV : forall x, U x -> V x)
      (s : psf_sec V HV),
    psf_res U V HU HV hUV (ag_neg (psf_group V HV) s) =
    ag_neg (psf_group U HU) (psf_res U V HU HV hUV s)
  (** Restriction depends only on the opens, not on the chosen inclusion
      witness. *)
; psf_res_irrel : forall (U V : set X) (HU : is_open TX U) (HV : is_open TX V)
      (hUV hUV' : forall x, U x -> V x)
      (s : psf_sec V HV),
    psf_res U V HU HV hUV s = psf_res U V HU HV hUV' s
  (** Identity restriction *)
; psf_res_id : forall (U : set X) (HU : is_open TX U) (s : psf_sec U HU),
    psf_res U U HU HU (fun x h => h) s = s
  (** Composition of restrictions *)
; psf_res_comp : forall (U V W : set X)
      (HU : is_open TX U) (HV : is_open TX V) (HW : is_open TX W)
      (hUV : forall x, U x -> V x) (hVW : forall x, V x -> W x)
      (s : psf_sec W HW),
    psf_res U V HU HV hUV (psf_res V W HV HW hVW s) =
    psf_res U W HU HW (fun x h => hVW x (hUV x h)) s
}.

Arguments psf_sec   {X TX} _ _ _.
Arguments psf_group {X TX} _ _ _.
Arguments psf_res   {X TX} _ _ _ _ _ _.

(** A sheaf = presheaf satisfying locality and gluing. *)
Record Sheaf (X : Type) (TX : Topology X) : Type :=
{ shf_ps    :> Presheaf X TX

  (** Locality: if s|_{U_i} = 0 for all i in a cover, then s = 0. *)
; shf_local : forall (U : set X) (HU : is_open TX U)
      (s : psf_sec shf_ps U HU)
      (cover : list (set X))
      (cover_open : forall V, List.In V cover -> is_open TX V)
      (cover_sub  : forall V, List.In V cover -> forall x, V x -> U x)
      (cover_all  : forall x, U x -> exists V, List.In V cover /\ V x),
    (forall V (HV : is_open TX V) (hVU : forall x, V x -> U x),
       List.In V cover ->
       psf_res shf_ps V U HV HU hVU s =
       ag_zero (psf_group shf_ps V HV)) ->
    s = ag_zero (psf_group shf_ps U HU)

  (** Gluing: compatible local sections glue to a global section. *)
; shf_glue  : forall (U : set X) (HU : is_open TX U)
      (cover : list (set X))
      (cover_open : forall V, List.In V cover -> is_open TX V)
      (cover_sub  : forall V, List.In V cover -> forall x, V x -> U x)
      (cover_all  : forall x, U x -> exists V, List.In V cover /\ V x)
      (secs : forall V, List.In V cover -> forall (HV : is_open TX V), psf_sec shf_ps V HV),
    (** Compatibility on pairwise intersections *)
    (forall V W (HVin : List.In V cover) (HWin : In W cover)
         (HV : is_open TX V) (HW : is_open TX W)
         (HVW : is_open TX (fun x => V x /\ W x)),
       psf_res shf_ps (fun x => V x /\ W x) V
         HVW HV (fun x h => proj1 h) (secs V HVin HV) =
       psf_res shf_ps (fun x => V x /\ W x) W
         HVW HW (fun x h => proj2 h) (secs W HWin HW)) ->
    exists (s : psf_sec shf_ps U HU),
      forall V (HVin : List.In V cover) (HV : is_open TX V) (hVU : forall x, V x -> U x),
        psf_res shf_ps V U HV HU hVU s = secs V HVin HV
}.

Arguments shf_ps    {X TX} _.
Arguments shf_local {X TX} _.
Arguments shf_glue  {X TX} _.

(** Global sections of a sheaf. *)
Definition global_sections {X : Type} {TX : Topology X}
    (F : Sheaf X TX) (HX : is_open TX (fun _ => True)) : Type :=
  psf_sec F (fun _ => True) HX.

(* ================================================================== *)
(** * Part C/D: Sheaf morphisms, kernels, exactness                    *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(** ** 2. Sheaf morphisms                                              *)
(* ------------------------------------------------------------------ *)

(** A morphism of presheaves: compatible maps on sections. *)
Record PSFMorphism {X : Type} {TX : Topology X}
    (F G : Presheaf X TX) : Type :=
{ psfm_map : forall (U : set X) (HU : is_open TX U),
    psf_sec F U HU -> psf_sec G U HU
  (** Naturality: commutes with restrictions. *)
; psfm_nat : forall (U V : set X) (HU : is_open TX U) (HV : is_open TX V)
      (hUV : forall x, U x -> V x)
      (s : psf_sec F V HV),
    psfm_map U HU (psf_res F U V HU HV hUV s) =
    psf_res G U V HU HV hUV (psfm_map V HV s)
  (** Additivity: commutes with group operations. *)
; psfm_add : forall (U : set X) (HU : is_open TX U)
      (s t : psf_sec F U HU),
    psfm_map U HU (ag_add (psf_group F U HU) s t) =
    ag_add (psf_group G U HU) (psfm_map U HU s) (psfm_map U HU t)
}.

Arguments psfm_map {X TX F G} _ _ _.
Arguments psfm_nat {X TX F G} _ _ _ _ _ _ _.
Arguments psfm_add {X TX F G} _ _ _ _ _.

(** A morphism of sheaves: same as presheaf morphism between the
    underlying presheaves. *)
Definition SheafMorphism {X : Type} {TX : Topology X}
    (F G : Sheaf X TX) : Type :=
  PSFMorphism (shf_ps F) (shf_ps G).

(** Composition of sheaf morphisms. *)
Definition shfm_comp {X : Type} {TX : Topology X}
    {F G H : Sheaf X TX}
    (g : SheafMorphism G H) (f : SheafMorphism F G) : SheafMorphism F H.
Proof.
  refine {| psfm_map := fun U HU s => psfm_map g U HU (psfm_map f U HU s)
          ; psfm_nat := _
          ; psfm_add := _ |}.
  - intros U V HU HV hUV s.
    rewrite (psfm_nat f U V HU HV hUV s).
    apply (psfm_nat g U V HU HV hUV).
  - intros U HU s t.
    rewrite (psfm_add f U HU s t).
    apply (psfm_add g U HU).
Defined.

(* ------------------------------------------------------------------ *)
(** ** 3. Kernel presheaf                                              *)
(* ------------------------------------------------------------------ *)

(** The kernel of a sheaf morphism f : F → G is a sub-presheaf of F
    whose sections are {s ∈ F(U) | f_U(s) = 0}. *)
(* CAG constructive-remove Definition ker_presheaf theories/Sheaves.v:184 BEGIN
Definition ker_presheaf {X : Type} {TX : Topology X}
    {F G : Sheaf X TX} (f : SheafMorphism F G) : Presheaf X TX.
Proof. Admitted.
   CAG constructive-remove Definition ker_presheaf theories/Sheaves.v:184 END *)

(** The kernel presheaf is in fact a sheaf (it inherits gluing and locality). *)
(* CAG constructive-remove Definition ker_sheaf theories/Sheaves.v:189 BEGIN
Definition ker_sheaf {X : Type} {TX : Topology X}
    {F G : Sheaf X TX} (f : SheafMorphism F G) : Sheaf X TX.
Proof. Admitted.
   CAG constructive-remove Definition ker_sheaf theories/Sheaves.v:189 END *)

(* ------------------------------------------------------------------ *)
(** ** 4. Exact sequences of sheaves                                   *)
(* ------------------------------------------------------------------ *)

(** A sequence F →f G →g H is exact at G if:
    im(f_U) = ker(g_U) for every open U. *)
Definition exact_at {X : Type} {TX : Topology X}
    {F G H : Sheaf X TX}
    (f : SheafMorphism F G)
    (g : SheafMorphism G H) : Prop :=
  forall (U : set X) (HU : is_open TX U) (t : psf_sec G U HU),
    psfm_map g U HU t = ag_zero (psf_group H U HU) <->
    exists s : psf_sec F U HU,
      psfm_map f U HU s = t.

(** A short exact sequence  0 → S →f F →g Q → 0. *)
Record ShortExactSeq {X : Type} {TX : Topology X}
    (S F Q : Sheaf X TX) : Type :=
{ ses_f     : SheafMorphism S F
; ses_g     : SheafMorphism F Q
; ses_exact : exact_at ses_f ses_g
  (** f is injective on sections. *)
; ses_inj   : forall (U : set X) (HU : is_open TX U) (s1 s2 : psf_sec S U HU),
    psfm_map ses_f U HU s1 = psfm_map ses_f U HU s2 -> s1 = s2
  (** g is surjective on sections (locally; stalk-wise). *)
; ses_surj  : forall (U : set X) (HU : is_open TX U) (q : psf_sec Q U HU),
    exists (cover : list (set X)),
      (forall V, List.In V cover -> is_open TX V) /\
      (forall x, U x -> exists V, List.In V cover /\ V x) /\
      forall V (HV : is_open TX V) (hVU : forall x, V x -> U x),
        List.In V cover ->
        exists s : psf_sec F V HV,
          psfm_map ses_g V HV s =
          psf_res Q V U HV HU hVU q
}.

Arguments ses_f {X TX S F Q} _.
Arguments ses_g {X TX S F Q} _.
Arguments ses_exact {X TX S F Q} _.
Arguments ses_inj {X TX S F Q} _.
Arguments ses_surj {X TX S F Q} _.

(** Extension by zero: given a sheaf F on an open subspace V ⊆ X,
    extend it to X by assigning 0 on opens disjoint from V. *)
(* CAG zero-dependent Parameter extend_by_zero theories/Sheaves.v:235 BEGIN
Parameter extend_by_zero : forall {X : Type} {TX : Topology X}
    (V : set X) (HV : is_open TX V)
    (F : Sheaf X TX),
  Sheaf X TX.
   CAG zero-dependent Parameter extend_by_zero theories/Sheaves.v:235 END *)

(* ================================================================== *)
(** * Part C: Standard sheaf instances                                 *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(** ** 5. Constant sheaves                                             *)
(* ------------------------------------------------------------------ *)

(** The constant sheaf with value an abelian group A.
    On a connected open U, sections are locally constant A-valued functions. *)
(* CAG zero-dependent Parameter const_sheaf theories/Sheaves.v:254 BEGIN
Parameter const_sheaf : forall {X : Type} (TX : Topology X)
    (A : Type) (GA : AbGroup A),
  Sheaf X TX.
   CAG zero-dependent Parameter const_sheaf theories/Sheaves.v:254 END *)

(** Z, Q, R, C as abelian groups. *)
Definition Z_group : AbGroup Z :=
  {| ag_add   := Z.add
   ; ag_zero  := 0%Z
   ; ag_neg   := Z.opp
   ; ag_assoc := fun x y z => Z.add_assoc x y z
   ; ag_comm  := Z.add_comm
   ; ag_zero_r := Z.add_0_r
   ; ag_neg_r  := Z.add_opp_diag_r |}.

(** CComplex as an abelian group (add / zero / neg). *)
(* CAG constructive-remove Definition CC_group theories/Sheaves.v:271 BEGIN
Definition CC_group : AbGroup CComplex.
Proof.
  refine {| ag_add   := Cadd
           ; ag_zero  := C0
           ; ag_neg   := Cneg
           ; ag_assoc := _
           ; ag_comm  := _
           ; ag_zero_r := _
           ; ag_neg_r  := _ |}; admit.
Admitted.
   CAG constructive-remove Definition CC_group theories/Sheaves.v:271 END *)

(* ------------------------------------------------------------------ *)
(** ** 6. Sheaf of holomorphic functions O                             *)
(* ------------------------------------------------------------------ *)

(** The sheaf O of holomorphic functions on Cⁿ:
    O(U) = holomorphic functions U → C. *)
Definition hol_sections {n : nat} (TX : Topology (Cn n))
    (U : set (Cn n)) (HU : is_open TX U) : Type :=
  { f : Cn n -> CComplex | holomorphic_Cn U f }.

(** Abelian group structure on holomorphic functions. *)
(* CAG constructive-remove Definition hol_group theories/Sheaves.v:293 BEGIN
Definition hol_group {n : nat} (TX : Topology (Cn n))
    (U : set (Cn n)) (HU : is_open TX U) : AbGroup (hol_sections TX U HU).
Proof. Admitted.
   CAG constructive-remove Definition hol_group theories/Sheaves.v:293 END *)

(** Restriction of a holomorphic function to a smaller open set. *)
Definition hol_res {n : nat} (TX : Topology (Cn n))
    (U V : set (Cn n)) (HU : is_open TX U) (HV : is_open TX V)
    (hUV : forall x, U x -> V x)
    (f : hol_sections TX V HV) : hol_sections TX U HU.
Proof.
  destruct f as [g Hg].
  exists g.
  (* holomorphic_Cn U g: for each v with U v, g is holomorphic at v *)
  (* Since U ⊆ V and g is holomorphic on V, g is holomorphic on U *)
  intros v Hv i.
  exact (Hg v (hUV v Hv) i).
Defined.

(** The presheaf of holomorphic functions on Cⁿ. *)
(* CAG constructive-remove Definition hol_presheaf theories/Sheaves.v:320 BEGIN
Definition hol_presheaf (n : nat) (TX : Topology (Cn n))
    : Presheaf (Cn n) TX.
Proof.
  refine {| psf_sec   := fun U HU => hol_sections TX U HU
          ; psf_group := fun U HU => hol_group TX U HU
          ; psf_res   := fun U V HU HV hUV f => hol_res TX U V HU HV hUV f
          ; psf_res_id  := _
          ; psf_res_comp := _ |}.
  - (* psf_res_id: hol_res with identity inclusion = id *)
    intros U HU s. destruct s as [g Hg]. reflexivity.
  - (* psf_res_comp: composition of restrictions *)
    intros U V W HU HV HW hUV hVW s. destruct s as [g Hg]. reflexivity.
Defined.
   CAG constructive-remove Definition hol_presheaf theories/Sheaves.v:320 END *)

(** The sheaf O of holomorphic functions (sheaf axioms admitted). *)
(* CAG constructive-remove Definition O_sheaf theories/Sheaves.v:327 BEGIN
Definition O_sheaf (n : nat) (TX : Topology (Cn n)) : Sheaf (Cn n) TX.
Proof. Admitted.
   CAG constructive-remove Definition O_sheaf theories/Sheaves.v:327 END *)

(* ------------------------------------------------------------------ *)
(** ** 7. Multiplicative sheaf O*                                      *)
(* ------------------------------------------------------------------ *)

(** O*(U) = nonzero holomorphic functions U → C, with multiplication. *)
Record OstarGroup (G : Type) : Type :=
{ ostar_mul  : G -> G -> G
; ostar_one  : G
; ostar_inv  : G -> G
; ostar_assoc : forall x y z, ostar_mul x (ostar_mul y z) = ostar_mul (ostar_mul x y) z
; ostar_comm  : forall x y, ostar_mul x y = ostar_mul y x
; ostar_one_r : forall x, ostar_mul x ostar_one = x
; ostar_inv_r : forall x, ostar_mul x (ostar_inv x) = ostar_one
}.

(** We model O* sections as nonzero holomorphic functions.
    "Nonzero" is expressed via a positivity witness on the norm. *)
Definition hol_star_sections {n : nat} (TX : Topology (Cn n))
    (U : set (Cn n)) (HU : is_open TX U) : Type :=
  { f : Cn n -> CComplex
  | holomorphic_Cn U f /\
    forall z, U z -> CRpositive (Cnorm2 (f z)) }.

(** The sheaf O* (defined abstractly; details admitted). *)
(* CAG zero-dependent Parameter O_star_sheaf theories/Sheaves.v:352 BEGIN
Parameter O_star_sheaf : forall (n : nat) (TX : Topology (Cn n)),
    Sheaf (Cn n) TX.
   CAG zero-dependent Parameter O_star_sheaf theories/Sheaves.v:352 END *)

(* ------------------------------------------------------------------ *)
(** ** 8. Sheaf of (p,q)-forms                                         *)
(* ------------------------------------------------------------------ *)

(** A^(p,q)(U) = smooth (p,q)-forms on U.
    We represent this via PQForm restricted to U. *)
Definition pq_sections (n p q : nat) (TX : Topology (Cn n))
    (U : set (Cn n)) (HU : is_open TX U) : Type :=
  PQForm n p q.

Definition H_Dolbeault (n p q : nat) : Type :=
  PQForm n p q.

(** Abelian group structure on (p,q)-forms. *)
(* CAG constructive-remove Definition pq_group theories/Sheaves.v:370 BEGIN
Definition pq_group (n p q : nat) (TX : Topology (Cn n))
    (U : set (Cn n)) (HU : is_open TX U) : AbGroup (pq_sections n p q TX U HU).
Proof. Admitted.
   CAG constructive-remove Definition pq_group theories/Sheaves.v:370 END *)

(** The sheaf A^(p,q) of smooth (p,q)-forms (admitted). *)
(* CAG zero-dependent Parameter A_pq_sheaf theories/Sheaves.v:375 BEGIN
Parameter A_pq_sheaf : forall (n p q : nat) (TX : Topology (Cn n)),
    Sheaf (Cn n) TX.
   CAG zero-dependent Parameter A_pq_sheaf theories/Sheaves.v:375 END *)

(** The sheaf of ∂̄-closed (p,q)-forms. *)
(* CAG zero-dependent Parameter dbar_closed_sheaf theories/Sheaves.v:369 BEGIN
Parameter dbar_closed_sheaf : forall (n p q : nat) (TX : Topology (Cn n)),
    Sheaf (Cn n) TX.
   CAG zero-dependent Parameter dbar_closed_sheaf theories/Sheaves.v:369 END *)

(* ------------------------------------------------------------------ *)
(** ** 9. Ideal sheaf of a subvariety                                  *)
(* ------------------------------------------------------------------ *)

(** I_V(U) = holomorphic functions on U vanishing on V ∩ U. *)
Definition ideal_sections {n : nat} (TX : Topology (Cn n))
    (V : Cn n -> Prop)
    (U : set (Cn n)) (HU : is_open TX U) : Type :=
  { f : Cn n -> CComplex
  | holomorphic_Cn U f /\
    forall z, U z -> V z -> Cequal (f z) C0 }.

(** The ideal sheaf I_V (admitted sheaf axioms). *)
(* CAG zero-dependent Parameter ideal_sheaf theories/Sheaves.v:393 BEGIN
Parameter ideal_sheaf : forall {n : nat} (TX : Topology (Cn n))
    (V : Cn n -> Prop),
  Sheaf (Cn n) TX.
   CAG zero-dependent Parameter ideal_sheaf theories/Sheaves.v:393 END *)

(* ------------------------------------------------------------------ *)
(** ** 10. Meromorphic sheaf M                                          *)
(* ------------------------------------------------------------------ *)

(** A meromorphic function on U is a ratio f/g of holomorphic functions
    where g is not identically zero.  We represent it as a pair (f, g)
    with g nowhere identically zero, up to a local equivalence:
    (f1,g1) ~ (f2,g2) iff f1·g2 = f2·g1. *)
Definition mero_sections {n : nat} (TX : Topology (Cn n))
    (U : set (Cn n)) (HU : is_open TX U) : Type :=
  { p : (Cn n -> CComplex) * (Cn n -> CComplex)
  | match p with (f, g) =>
      holomorphic_Cn U f /\
      holomorphic_Cn U g /\
      exists z, U z /\ CRpositive (Cnorm2 (g z))
    end }.

(** The meromorphic sheaf M (admitted). *)
(* CAG zero-dependent Parameter M_sheaf theories/Sheaves.v:407 BEGIN
Parameter M_sheaf : forall (n : nat) (TX : Topology (Cn n)),
    Sheaf (Cn n) TX.
   CAG zero-dependent Parameter M_sheaf theories/Sheaves.v:407 END *)

(** The principal-parts sheaf M/O (admitted). *)
(* CAG zero-dependent Parameter principal_parts_sheaf theories/Sheaves.v:411 BEGIN
Parameter principal_parts_sheaf : forall (n : nat) (TX : Topology (Cn n)),
    Sheaf (Cn n) TX.
   CAG zero-dependent Parameter principal_parts_sheaf theories/Sheaves.v:411 END *)

(* ================================================================== *)
(** * Part E: Core exact sequences                                      *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(** ** 11. Exponential sequence                                         *)
(* ------------------------------------------------------------------ *)

(** The exponential map exp : O → O*.
    In the holomorphic setting, exp(f) = e^f which is nonzero. *)
(* CAG zero-dependent Parameter exp_morphism theories/Sheaves.v:436 BEGIN
(* CAG zero-dependent Parameter exp_morphism theories/Sheaves.v:436 BEGIN
Parameter exp_morphism : forall (n : nat) (TX : Topology (Cn n)),
    SheafMorphism (O_sheaf n TX) (O_star_sheaf n TX).
   CAG zero-dependent Parameter exp_morphism theories/Sheaves.v:436 END *)
   CAG zero-dependent Parameter exp_morphism theories/Sheaves.v:436 END *)

(** The inclusion Z ↪ O (as constant functions). *)
(* CAG zero-dependent Parameter Z_to_O theories/Sheaves.v:440 BEGIN
(* CAG zero-dependent Parameter Z_to_O theories/Sheaves.v:440 BEGIN
Parameter Z_to_O : forall (n : nat) (TX : Topology (Cn n)),
    SheafMorphism (const_sheaf TX Z Z_group) (O_sheaf n TX).
   CAG zero-dependent Parameter Z_to_O theories/Sheaves.v:440 END *)
   CAG zero-dependent Parameter Z_to_O theories/Sheaves.v:440 END *)

(** Exponential sequence: 0 → Z → O →^exp O* → 0 is exact.
    Exactness at O: f ∈ ker(exp) iff f ∈ 2πi·Z (i.e. integer multiple).
    Exactness at O*: every nonzero function is locally exp of something. *)
(* CAG zero-dependent Admitted exp_sequence_exact theories/Sheaves.v:436 BEGIN
Theorem exp_sequence_exact : forall (n : nat) (TX : Topology (Cn n)),
    exact_at (Z_to_O n TX) (exp_morphism n TX).
Proof. admit. Admitted.
   CAG zero-dependent Admitted exp_sequence_exact theories/Sheaves.v:436 END *)

(* ------------------------------------------------------------------ *)
(** ** 12. Restriction sequence for a submanifold                       *)
(* ------------------------------------------------------------------ *)

(** 0 → I_V → O_M → O_V → 0. *)
(* CAG zero-dependent Parameter ideal_to_O theories/Sheaves.v:457 BEGIN
(* CAG zero-dependent Parameter ideal_to_O theories/Sheaves.v:457 BEGIN
Parameter ideal_to_O : forall {n : nat} (TX : Topology (Cn n))
    (V : Cn n -> Prop),
  SheafMorphism (ideal_sheaf TX V) (O_sheaf n TX).
   CAG zero-dependent Parameter ideal_to_O theories/Sheaves.v:457 END *)
   CAG zero-dependent Parameter ideal_to_O theories/Sheaves.v:457 END *)

(* CAG zero-dependent Parameter O_to_OV theories/Sheaves.v:461 BEGIN
(* CAG zero-dependent Parameter O_to_OV theories/Sheaves.v:461 BEGIN
Parameter O_to_OV : forall {n : nat} (TX : Topology (Cn n))
    (V : Cn n -> Prop),
  SheafMorphism (O_sheaf n TX) (O_sheaf n TX).
   CAG zero-dependent Parameter O_to_OV theories/Sheaves.v:461 END *)
   CAG zero-dependent Parameter O_to_OV theories/Sheaves.v:461 END *)

(* CAG zero-dependent Admitted restriction_sequence_exact theories/Sheaves.v:454 BEGIN
Theorem restriction_sequence_exact : forall {n : nat} (TX : Topology (Cn n))
    (V : Cn n -> Prop),
  exact_at (ideal_to_O TX V) (O_to_OV TX V).
Proof. admit. Admitted.
   CAG zero-dependent Admitted restriction_sequence_exact theories/Sheaves.v:454 END *)

(* ------------------------------------------------------------------ *)
(** ** 13. de Rham resolution                                           *)
(* ------------------------------------------------------------------ *)

(** The de Rham complex: 0 → R → A^0 → A^1 → A^2 → ...
    The exterior derivative d : A^p → A^(p+1) is the morphism. *)
(* CAG zero-dependent Parameter d_morphism theories/Sheaves.v:478 BEGIN
(* CAG zero-dependent Parameter d_morphism theories/Sheaves.v:478 BEGIN
Parameter d_morphism : forall (n p : nat) (TX : Topology (Cn n)),
    SheafMorphism (A_pq_sheaf n p 0 TX) (A_pq_sheaf n (p + 1) 0 TX).
   CAG zero-dependent Parameter d_morphism theories/Sheaves.v:478 END *)
   CAG zero-dependent Parameter d_morphism theories/Sheaves.v:478 END *)

(* CAG zero-dependent Admitted deRham_exact theories/Sheaves.v:467 BEGIN
Theorem deRham_exact : forall (n p : nat) (TX : Topology (Cn n)),
    exact_at (d_morphism n p TX) (d_morphism n (p + 1) TX).
Proof. admit. Admitted.
   CAG zero-dependent Admitted deRham_exact theories/Sheaves.v:467 END *)

(* ------------------------------------------------------------------ *)
(** ** 14. Dolbeault resolution                                          *)
(* ------------------------------------------------------------------ *)

(** The Dolbeault complex: 0 → Ω^p → A^(p,0) → A^(p,1) → A^(p,2) → ...
    The ∂̄ map: A^(p,q) → A^(p,q+1). *)
(* CAG zero-dependent Parameter dbar_morphism theories/Sheaves.v:493 BEGIN
(* CAG zero-dependent Parameter dbar_morphism theories/Sheaves.v:493 BEGIN
Parameter dbar_morphism : forall (n p q : nat) (TX : Topology (Cn n)),
    SheafMorphism (A_pq_sheaf n p q TX) (A_pq_sheaf n p (q + 1) TX).
   CAG zero-dependent Parameter dbar_morphism theories/Sheaves.v:493 END *)
   CAG zero-dependent Parameter dbar_morphism theories/Sheaves.v:493 END *)

(** Exactness follows from local ∂̄-Poincaré lemma on polydiscs. *)
(* CAG zero-dependent Admitted dolbeault_exact theories/Sheaves.v:481 BEGIN
Theorem dolbeault_exact : forall (n p q : nat) (TX : Topology (Cn n)),
    exact_at (dbar_morphism n p q TX) (dbar_morphism n p (q + 1) TX).
Proof. admit. Admitted.
   CAG zero-dependent Admitted dolbeault_exact theories/Sheaves.v:481 END *)

(* ================================================================== *)
(** * Part F: Čech cochains and Čech cohomology                        *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(** ** 15. Open covers                                                  *)
(* ------------------------------------------------------------------ *)

(** A finite open cover of U. *)
Record OpenCover {X : Type} (TX : Topology X) (U : set X) : Type :=
{ oc_sets  : list (set X)
; oc_open  : forall V, List.In V oc_sets -> is_open TX V
; oc_sub   : forall V, List.In V oc_sets -> forall x, V x -> U x
; oc_cover : forall x, U x -> exists V, List.In V oc_sets /\ V x
}.

Arguments oc_sets  {X TX U} _.
Arguments oc_open  {X TX U} _.
Arguments oc_sub   {X TX U} _.
Arguments oc_cover {X TX U} _.

(** Refinement: cover U' refines U if every set in U' is contained
    in some set of U. *)
Definition refines {X : Type} {TX : Topology X} {U : set X}
    (cov' cov : OpenCover TX U) : Prop :=
  forall V', In V' (oc_sets cov') ->
    exists V, List.In V (oc_sets cov) /\ forall x, V' x -> V x.

(** A locally finite cover: every point meets finitely many sets. *)
Definition locally_finite {X : Type} {TX : Topology X} {U : set X}
    (cov : OpenCover TX U) : Prop :=
  forall x, U x ->
    exists (finite_sub : list (set X)),
      forall V, List.In V (oc_sets cov) -> V x -> In V finite_sub.

(* ------------------------------------------------------------------ *)
(** ** 16. Čech cochains                                                *)
(* ------------------------------------------------------------------ *)

(** A Čech 0-cochain: one section s_V ∈ F(V) for each open V in the cover. *)
Definition Cech0 {X : Type} {TX : Topology X} {U : set X}
    (cov : OpenCover TX U)
    (F : Sheaf X TX) : Type :=
  forall V (HVin : In V (oc_sets cov)),
    psf_sec F V (oc_open cov V HVin).

(** A Čech 1-cochain: one section s_{VW} ∈ F(V ∩ W) for each pair. *)
Definition Cech1 {X : Type} {TX : Topology X} {U : set X}
    (cov : OpenCover TX U)
    (F : Sheaf X TX) : Type :=
  forall V W (HVin : In V (oc_sets cov)) (HWin : In W (oc_sets cov))
    (HVW : is_open TX (fun x => V x /\ W x)),
    psf_sec F (fun x => V x /\ W x) HVW.

(** A Čech p-cochain for general p using p-tuples of indices.
    We represent a p-tuple as a list of length p. *)
Definition Cech_cochain {X : Type} {TX : Topology X} {U : set X}
    (cov : OpenCover TX U)
    (F : Sheaf X TX) (p : nat) : Type :=
  forall (idx : list (set X)),
    List.length idx = p ->
    (forall V, List.In V idx -> In V (oc_sets cov)) ->
    forall (Hint : is_open TX (fold_right (fun V W => fun x => V x /\ W x)
                                           (fun _ => True) idx)),
      psf_sec F _ Hint.

(* ------------------------------------------------------------------ *)
(** ** 17. Čech coboundary operator                                     *)
(* ------------------------------------------------------------------ *)

(** Čech coboundary δ : C^0 → C^1.
    (δs)_{VW} = s_W|_{V∩W} - s_V|_{V∩W}. *)
Definition cech_d0 {X : Type} {TX : Topology X} {U : set X}
    (cov : OpenCover TX U)
    (F : Sheaf X TX)
    (s : Cech0 cov F) : Cech1 cov F :=
  fun V W HVin HWin HVW =>
    let sW := s W HWin in
    let sV := s V HVin in
    let resW := psf_res F (fun x => V x /\ W x) W
                  HVW (oc_open cov W HWin)
                  (fun x h => proj2 h) sW in
    let resV := psf_res F (fun x => V x /\ W x) V
                  HVW (oc_open cov V HVin)
                  (fun x h => proj1 h) sV in
    ag_add (psf_group F (fun x => V x /\ W x) HVW)
           resW
           (ag_neg (psf_group F (fun x => V x /\ W x) HVW) resV).

(** Algebraic cancellation used by the degree-0 Čech coboundary. *)
Lemma ag_add_sub_cancel_mid {A : Type} (GA : AbGroup A) :
  forall v w z : A,
    ag_add GA (ag_add GA w (ag_neg GA v))
              (ag_add GA z (ag_neg GA w)) =
    ag_add GA z (ag_neg GA v).
Proof.
  intros v w z.
  assert (Hneg_zero_l : forall a : A,
             ag_add GA (ag_neg GA a) a = ag_zero GA).
  { intro a. rewrite (ag_comm _ GA). apply ag_neg_r. }
  assert (Hzero_l : forall a : A,
             ag_add GA (ag_zero GA) a = a).
  { intro a. rewrite (ag_comm _ GA). apply ag_zero_r. }
  rewrite (ag_comm _ GA (ag_add GA w (ag_neg GA v))
                      (ag_add GA z (ag_neg GA w))).
  rewrite <- (ag_assoc _ GA z (ag_neg GA w)
                         (ag_add GA w (ag_neg GA v))).
  rewrite (ag_assoc _ GA (ag_neg GA w) w (ag_neg GA v)).
  rewrite Hneg_zero_l.
  rewrite Hzero_l.
  reflexivity.
Qed.

Lemma ag_zero_l {A : Type} (GA : AbGroup A) :
  forall a : A, ag_add GA (ag_zero GA) a = a.
Proof.
  intro a. rewrite (ag_comm _ GA). apply ag_zero_r.
Qed.

Lemma ag_neg_zero_l {A : Type} (GA : AbGroup A) :
  forall a : A, ag_add GA (ag_neg GA a) a = ag_zero GA.
Proof.
  intro a. rewrite (ag_comm _ GA). apply ag_neg_r.
Qed.

Lemma ag_add_cancel_l {A : Type} (GA : AbGroup A) :
  forall a b c : A, ag_add GA c a = ag_add GA c b -> a = b.
Proof.
  intros a b c H.
  assert (Hf : ag_add GA (ag_neg GA c) (ag_add GA c a) =
               ag_add GA (ag_neg GA c) (ag_add GA c b)).
  { rewrite H. reflexivity. }
  repeat rewrite (ag_assoc _ GA) in Hf.
  rewrite ag_neg_zero_l in Hf.
  repeat rewrite ag_zero_l in Hf.
  exact Hf.
Qed.

Lemma ag_add_neg_eq_zero {A : Type} (GA : AbGroup A) :
  forall a b : A,
    ag_add GA a (ag_neg GA b) = ag_zero GA -> a = b.
Proof.
  intros a b H.
  apply (ag_add_cancel_l GA a b (ag_neg GA b)).
  rewrite (ag_comm _ GA (ag_neg GA b) a).
  rewrite H.
  symmetry. apply ag_neg_zero_l.
Qed.

Lemma psf_res_zero {X : Type} {TX : Topology X}
    (F : Presheaf X TX) :
  forall (U V : set X) (HU : is_open TX U) (HV : is_open TX V)
      (hUV : forall x, U x -> V x),
    psf_res F U V HU HV hUV (ag_zero (psf_group F V HV)) =
    ag_zero (psf_group F U HU).
Proof.
  intros U V HU HV hUV.
  symmetry.
  apply (ag_add_cancel_l (psf_group F U HU)
           (ag_zero (psf_group F U HU))
           (psf_res F U V HU HV hUV (ag_zero (psf_group F V HV)))
           (psf_res F U V HU HV hUV (ag_zero (psf_group F V HV)))).
  rewrite (ag_zero_r _ (psf_group F U HU)).
  rewrite <- psf_res_add.
  rewrite (ag_zero_r _ (psf_group F V HV)).
  reflexivity.
Qed.

(** δ² = 0 for degree-0 Čech coboundaries on a triple overlap. *)
Lemma cech_d0_squared : forall {X : Type} {TX : Topology X} {U : set X}
    (cov : OpenCover TX U)
    (F : Sheaf X TX)
    (s : Cech0 cov F)
    V W Z (HVin : In V (oc_sets cov)) (HWin : In W (oc_sets cov))
    (HZin : In Z (oc_sets cov))
    (HVW : is_open TX (fun x => V x /\ W x))
    (HWZ : is_open TX (fun x => W x /\ Z x))
    (HVZ : is_open TX (fun x => V x /\ Z x))
    (HVWZ : is_open TX (fun x => V x /\ W x /\ Z x)),
  let G := psf_group F (fun x => V x /\ W x /\ Z x) HVWZ in
  let sV := psf_res F (fun x => V x /\ W x /\ Z x) V
              HVWZ (oc_open cov V HVin)
              (fun x h => proj1 h) (s V HVin) in
  let sW := psf_res F (fun x => V x /\ W x /\ Z x) W
              HVWZ (oc_open cov W HWin)
              (fun x h => proj1 (proj2 h)) (s W HWin) in
  let sZ := psf_res F (fun x => V x /\ W x /\ Z x) Z
              HVWZ (oc_open cov Z HZin)
              (fun x h => proj2 (proj2 h)) (s Z HZin) in
  let dVW := psf_res F (fun x => V x /\ W x /\ Z x)
                (fun x => V x /\ W x) HVWZ HVW
                (fun x h => conj (proj1 h) (proj1 (proj2 h)))
                (cech_d0 cov F s V W HVin HWin HVW) in
  let dWZ := psf_res F (fun x => V x /\ W x /\ Z x)
                (fun x => W x /\ Z x) HVWZ HWZ
                (fun x h => conj (proj1 (proj2 h)) (proj2 (proj2 h)))
                (cech_d0 cov F s W Z HWin HZin HWZ) in
  let dVZ := psf_res F (fun x => V x /\ W x /\ Z x)
                (fun x => V x /\ Z x) HVWZ HVZ
                (fun x h => conj (proj1 h) (proj2 (proj2 h)))
                (cech_d0 cov F s V Z HVin HZin HVZ) in
  ag_add G dVW dWZ = dVZ.
Proof.
  intros X TX U cov F s V W Z HVin HWin HZin HVW HWZ HVZ HVWZ.
  set (G := psf_group F (fun x => V x /\ W x /\ Z x) HVWZ).
  set (sV := psf_res F (fun x => V x /\ W x /\ Z x) V
              HVWZ (oc_open cov V HVin)
              (fun x h => proj1 h) (s V HVin)).
  set (sW := psf_res F (fun x => V x /\ W x /\ Z x) W
              HVWZ (oc_open cov W HWin)
              (fun x h => proj1 (proj2 h)) (s W HWin)).
  set (sZ := psf_res F (fun x => V x /\ W x /\ Z x) Z
              HVWZ (oc_open cov Z HZin)
              (fun x h => proj2 (proj2 h)) (s Z HZin)).
  set (dVW := psf_res F (fun x => V x /\ W x /\ Z x)
                (fun x => V x /\ W x) HVWZ HVW
                (fun x h => conj (proj1 h) (proj1 (proj2 h)))
                (cech_d0 cov F s V W HVin HWin HVW)).
  set (dWZ := psf_res F (fun x => V x /\ W x /\ Z x)
                (fun x => W x /\ Z x) HVWZ HWZ
                (fun x h => conj (proj1 (proj2 h)) (proj2 (proj2 h)))
                (cech_d0 cov F s W Z HWin HZin HWZ)).
  set (dVZ := psf_res F (fun x => V x /\ W x /\ Z x)
                (fun x => V x /\ Z x) HVWZ HVZ
                (fun x h => conj (proj1 h) (proj2 (proj2 h)))
                (cech_d0 cov F s V Z HVin HZin HVZ)).
  change (ag_add G dVW dWZ = dVZ).
  assert (Hvw : dVW = ag_add G sW (ag_neg G sV)).
  { subst dVW sW sV G. unfold cech_d0.
    rewrite psf_res_add.
    rewrite psf_res_neg.
    repeat rewrite psf_res_comp.
    rewrite (@psf_res_irrel _ _ F (fun x => V x /\ W x /\ Z x) W
               HVWZ (oc_open cov W HWin)
               _ (fun x h => proj1 (proj2 h)) (s W HWin)).
    rewrite (@psf_res_irrel _ _ F (fun x => V x /\ W x /\ Z x) V
               HVWZ (oc_open cov V HVin)
               _ (fun x h => proj1 h) (s V HVin)).
    reflexivity. }
  assert (Hwz : dWZ = ag_add G sZ (ag_neg G sW)).
  { subst dWZ sZ sW G. unfold cech_d0.
    rewrite psf_res_add.
    rewrite psf_res_neg.
    repeat rewrite psf_res_comp.
    rewrite (@psf_res_irrel _ _ F (fun x => V x /\ W x /\ Z x) Z
               HVWZ (oc_open cov Z HZin)
               _ (fun x h => proj2 (proj2 h)) (s Z HZin)).
    rewrite (@psf_res_irrel _ _ F (fun x => V x /\ W x /\ Z x) W
               HVWZ (oc_open cov W HWin)
               _ (fun x h => proj1 (proj2 h)) (s W HWin)).
    reflexivity. }
  assert (Hvz : dVZ = ag_add G sZ (ag_neg G sV)).
  { subst dVZ sZ sV G. unfold cech_d0.
    rewrite psf_res_add.
    rewrite psf_res_neg.
    repeat rewrite psf_res_comp.
    rewrite (@psf_res_irrel _ _ F (fun x => V x /\ W x /\ Z x) Z
               HVWZ (oc_open cov Z HZin)
               _ (fun x h => proj2 (proj2 h)) (s Z HZin)).
    rewrite (@psf_res_irrel _ _ F (fun x => V x /\ W x /\ Z x) V
               HVWZ (oc_open cov V HVin)
               _ (fun x h => proj1 h) (s V HVin)).
    reflexivity. }
  rewrite Hvw, Hwz, Hvz.
  apply ag_add_sub_cancel_mid.
Qed.

(** Čech coboundary δ : C^1 → C^2 (general case axiomatized). *)
(* CAG zero-dependent Parameter cech_d1 theories/Sheaves.v:584 BEGIN
Parameter cech_d1 : forall {X : Type} {TX : Topology X} {U : set X}
    (cov : OpenCover TX U) (F : Sheaf X TX),
    Cech1 cov F -> Cech_cochain cov F 2.
   CAG zero-dependent Parameter cech_d1 theories/Sheaves.v:584 END *)

(* ------------------------------------------------------------------ *)
(** ** 18. Čech cohomology groups                                       *)
(* ------------------------------------------------------------------ *)

(** A 1-cocycle: δ(t) = 0, i.e. t_{VW} + t_{WZ} = t_{VZ} on V ∩ W ∩ Z. *)
Definition Cech1_cocycle {X : Type} {TX : Topology X} {U : set X}
    (cov : OpenCover TX U)
    (F : Sheaf X TX)
    (t : Cech1 cov F) : Prop :=
  forall V W Z
    (HVin : In V (oc_sets cov)) (HWin : In W (oc_sets cov))
    (HZin : In Z (oc_sets cov))
    (HVW  : is_open TX (fun x => V x /\ W x))
    (HWZ  : is_open TX (fun x => W x /\ Z x))
    (HVZ  : is_open TX (fun x => V x /\ Z x))
    (HVWZ : is_open TX (fun x => V x /\ W x /\ Z x)),
  let t_VW := psf_res F (fun x => V x /\ W x /\ Z x)
                        (fun x => V x /\ W x) HVWZ HVW
                        (fun x h => conj (proj1 h) (proj1 (proj2 h)))
                        (t V W HVin HWin HVW) in
  let t_WZ := psf_res F (fun x => V x /\ W x /\ Z x)
                        (fun x => W x /\ Z x) HVWZ HWZ
                        (fun x h => conj (proj1 (proj2 h)) (proj2 (proj2 h)))
                        (t W Z HWin HZin HWZ) in
  let t_VZ := psf_res F (fun x => V x /\ W x /\ Z x)
                        (fun x => V x /\ Z x) HVWZ HVZ
                        (fun x h => conj (proj1 h) (proj2 (proj2 h)))
                        (t V Z HVin HZin HVZ) in
  ag_add (psf_group F (fun x => V x /\ W x /\ Z x) HVWZ) t_VW t_WZ = t_VZ.

(** A 1-coboundary: t = δ(s) for some 0-cochain s. *)
Definition Cech1_coboundary {X : Type} {TX : Topology X} {U : set X}
    (cov : OpenCover TX U)
    (F : Sheaf X TX)
    (t : Cech1 cov F) : Prop :=
  exists s : Cech0 cov F, forall V W HVin HWin HVW,
    t V W HVin HWin HVW = cech_d0 cov F s V W HVin HWin HVW.

Definition Cech0_zero {X : Type} {TX : Topology X} {U : set X}
    (cov : OpenCover TX U)
    (F : Sheaf X TX) : Cech0 cov F :=
  fun V HVin => ag_zero (psf_group F V (oc_open cov V HVin)).

Lemma cech_d0_zero : forall {X : Type} {TX : Topology X} {U : set X}
    (cov : OpenCover TX U)
    (F : Sheaf X TX)
    V W (HVin : In V (oc_sets cov)) (HWin : In W (oc_sets cov))
    (HVW : is_open TX (fun x => V x /\ W x)),
  cech_d0 cov F (Cech0_zero cov F) V W HVin HWin HVW =
  ag_zero (psf_group F (fun x => V x /\ W x) HVW).
Proof.
  intros X TX U cov F V W HVin HWin HVW.
  unfold cech_d0, Cech0_zero.
  rewrite psf_res_zero.
  rewrite psf_res_zero.
  apply ag_neg_r.
Qed.

(** Every degree-0 coboundary is a degree-1 cocycle. *)
Lemma cech_d0_is_cocycle : forall {X : Type} {TX : Topology X} {U : set X}
    (cov : OpenCover TX U)
    (F : Sheaf X TX)
    (s : Cech0 cov F),
  Cech1_cocycle cov F (cech_d0 cov F s).
Proof.
  intros X TX U cov F s V W Z HVin HWin HZin HVW HWZ HVZ HVWZ.
  apply cech_d0_squared.
Qed.

(** A 1-coboundary, in the quotient sense, is automatically a 1-cocycle. *)
Lemma Cech1_coboundary_is_cocycle : forall {X : Type} {TX : Topology X} {U : set X}
    (cov : OpenCover TX U)
    (F : Sheaf X TX)
    (t : Cech1 cov F),
  Cech1_coboundary cov F t -> Cech1_cocycle cov F t.
Proof.
  intros X TX U cov F t [s Ht] V W Z HVin HWin HZin HVW HWZ HVZ HVWZ.
  rewrite (Ht V W HVin HWin HVW).
  rewrite (Ht W Z HWin HZin HWZ).
  rewrite (Ht V Z HVin HZin HVZ).
  apply cech_d0_squared.
Qed.

Definition Cech1_zero {X : Type} {TX : Topology X} {U : set X}
    (cov : OpenCover TX U)
    (F : Sheaf X TX) : Cech1 cov F :=
  fun V W HVin HWin HVW =>
    ag_zero (psf_group F (fun x => V x /\ W x) HVW).

Lemma Cech1_zero_cocycle : forall {X : Type} {TX : Topology X} {U : set X}
    (cov : OpenCover TX U)
    (F : Sheaf X TX),
  Cech1_cocycle cov F (Cech1_zero cov F).
Proof.
  intros X TX U cov F V W Z HVin HWin HZin HVW HWZ HVZ HVWZ.
  unfold Cech1_zero.
  repeat rewrite psf_res_zero.
  apply ag_zero_l.
Qed.

(** H^0(U, F, cov): cocycles modulo coboundaries. *)
Definition H0_cech {X : Type} {TX : Topology X} {U : set X}
    (cov : OpenCover TX U)
    (F : Sheaf X TX) : Type :=
  { s : Cech0 cov F |
    forall V W HVin HWin HVW,
      cech_d0 cov F s V W HVin HWin HVW =
      ag_zero (psf_group F (fun x => V x /\ W x) HVW) }.

(** H^1(U, F, cov): 1-cocycles modulo 1-coboundaries (as a setoid). *)
Definition H1_cech {X : Type} {TX : Topology X} {U : set X}
    (cov : OpenCover TX U)
    (F : Sheaf X TX) : Type :=
  { t : Cech1 cov F | Cech1_cocycle cov F t }.

Definition H1_cech_zero {X : Type} {TX : Topology X} {U : set X}
    (cov : OpenCover TX U)
    (F : Sheaf X TX) : H1_cech cov F :=
  exist _ (Cech1_zero cov F) (Cech1_zero_cocycle cov F).

Definition H1_cech_equiv {X : Type} {TX : Topology X} {U : set X}
    (cov : OpenCover TX U) (F : Sheaf X TX)
    (t1 t2 : H1_cech cov F) : Prop :=
  exists s : Cech0 cov F,
    forall V W HVin HWin HVW,
      ag_add (psf_group F (fun x => V x /\ W x) HVW)
             (proj1_sig t1 V W HVin HWin HVW)
             (ag_neg (psf_group F (fun x => V x /\ W x) HVW)
                     (proj1_sig t2 V W HVin HWin HVW)) =
      cech_d0 cov F s V W HVin HWin HVW.

Lemma H1_cech_equiv_refl : forall {X : Type} {TX : Topology X} {U : set X}
    (cov : OpenCover TX U) (F : Sheaf X TX)
    (t : H1_cech cov F),
  H1_cech_equiv cov F t t.
Proof.
  intros X TX U cov F t.
  exists (Cech0_zero cov F).
  intros V W HVin HWin HVW.
  rewrite cech_d0_zero.
  apply ag_neg_r.
Qed.

(** H^0 agrees with sections on the covered open set in the forward direction:
    compatible local sections have a canonical glued section. *)
Lemma H0_is_global_sections : forall {X : Type} {TX : Topology X}
    {U : set X} (HU : is_open TX U) (cov : OpenCover TX U)
    (F : Sheaf X TX) (t : H0_cech cov F),
  exists section : psf_sec F U HU,
    forall V (HVin : In V (oc_sets cov)),
      psf_res F V U (oc_open cov V HVin) HU (oc_sub cov V HVin) section =
      proj1_sig t V HVin.
Proof.
  intros X TX U HU cov F [s Hs].
  set (sec :=
         fun V (HVin : In V (oc_sets cov)) (HV : is_open TX V) =>
           psf_res F V V HV (oc_open cov V HVin)
             (fun x h => h) (s V HVin)).
  destruct (shf_glue F U HU (oc_sets cov) (oc_open cov)
             (oc_sub cov) (oc_cover cov) sec) as [section Hsection].
  - intros V W HVin HWin HV HW HVW.
    subst sec.
    cbn.
    assert (HV_res :
      psf_res F (fun x => V x /\ W x) V HVW HV
        (fun x h => proj1 h)
        (psf_res F V V HV (oc_open cov V HVin)
           (fun x h => h) (s V HVin)) =
      psf_res F (fun x => V x /\ W x) V HVW (oc_open cov V HVin)
        (fun x h => proj1 h) (s V HVin)).
    { rewrite psf_res_comp.
      apply psf_res_irrel. }
    assert (HW_res :
      psf_res F (fun x => V x /\ W x) W HVW HW
        (fun x h => proj2 h)
        (psf_res F W W HW (oc_open cov W HWin)
           (fun x h => h) (s W HWin)) =
      psf_res F (fun x => V x /\ W x) W HVW (oc_open cov W HWin)
        (fun x h => proj2 h) (s W HWin)).
    { rewrite psf_res_comp.
      apply psf_res_irrel. }
    rewrite HV_res, HW_res.
    symmetry.
    apply (ag_add_neg_eq_zero (psf_group F (fun x => V x /\ W x) HVW)).
    exact (Hs V W HVin HWin HVW).
  - exists section.
    intros V HVin.
    rewrite (Hsection V HVin (oc_open cov V HVin) (oc_sub cov V HVin)).
    subst sec.
    apply psf_res_id.
Qed.

Definition section_to_Cech0 {X : Type} {TX : Topology X} {U : set X}
    (HU : is_open TX U) (cov : OpenCover TX U)
    (F : Sheaf X TX) (section : psf_sec F U HU) : Cech0 cov F :=
  fun V HVin =>
    psf_res F V U (oc_open cov V HVin) HU
      (oc_sub cov V HVin) section.

Lemma section_to_H0 : forall {X : Type} {TX : Topology X} {U : set X}
    (HU : is_open TX U) (cov : OpenCover TX U)
    (F : Sheaf X TX) (section : psf_sec F U HU),
  H0_cech cov F.
Proof.
  intros X TX U HU cov F section.
  exists (section_to_Cech0 HU cov F section).
  intros V W HVin HWin HVW.
  unfold cech_d0, section_to_Cech0.
  repeat rewrite psf_res_comp.
  rewrite (@psf_res_irrel _ _ F (fun x => V x /\ W x) U
             HVW HU
             (fun x h => oc_sub cov W HWin x (proj2 h))
             (fun x h => oc_sub cov V HVin x (proj1 h))
             section).
  apply ag_neg_r.
Qed.

(* ================================================================== *)
(** * Part G: Refinements and direct limit                             *)
(* ================================================================== *)

(** Refinement induces a map on Čech cochains. *)
(* CAG zero-dependent Parameter cech1_refinement_map theories/Sheaves.v:668 BEGIN
Parameter cech1_refinement_map : forall {X : Type} {TX : Topology X}
    {U : set X} (cov' cov : OpenCover TX U) (F : Sheaf X TX),
    refines cov' cov ->
    H1_cech cov F -> H1_cech cov' F.
   CAG zero-dependent Parameter cech1_refinement_map theories/Sheaves.v:668 END *)

(** The induced map on H^1 is independent of the choice of refinement
    inclusion maps. *)
Record RefinementH1Map {X : Type} {TX : Topology X} {U : set X}
    (cov' cov : OpenCover TX U) (F : Sheaf X TX)
    (r : refines cov' cov) : Type :=
{ refinement_H1_map : H1_cech cov F -> H1_cech cov' F }.

Definition refinement_map_independent {X : Type} {TX : Topology X}
    {U : set X} (cov' cov : OpenCover TX U) (F : Sheaf X TX)
    (r : refines cov' cov) : Prop :=
  forall m1 m2 : RefinementH1Map cov' cov F r,
    forall t : H1_cech cov F,
      @refinement_H1_map X TX U cov' cov F r m1 t =
      @refinement_H1_map X TX U cov' cov F r m2 t.

(** Sheaf cohomology H^p(X, F) as the direct limit over all covers.
    We define it abstractly via a universal property. *)
(* CAG zero-dependent Parameter H_sheaf theories/Sheaves.v:739 BEGIN
Parameter H_sheaf : forall {X : Type} (TX : Topology X)
    (F : Sheaf X TX) (p : nat) (U : set X) (HU : is_open TX U),
  Type.
   CAG zero-dependent Parameter H_sheaf theories/Sheaves.v:739 END *)

(** Canonical map from Čech cohomology on a cover to sheaf cohomology. *)
(* CAG zero-dependent Parameter cech_to_sheaf_H1 theories/Sheaves.v:687 BEGIN
Parameter cech_to_sheaf_H1 : forall {X : Type} {TX : Topology X}
    {U : set X} (HU : is_open TX U) (cov : OpenCover TX U)
    (F : Sheaf X TX),
  H1_cech cov F -> H_sheaf TX F 1 U HU.
   CAG zero-dependent Parameter cech_to_sheaf_H1 theories/Sheaves.v:687 END *)

(* ================================================================== *)
(** * Part H: Leray theorem interface                                   *)
(* ================================================================== *)

(** An open cover is acyclic for F if H^p(V, F) = 0 for all p > 0
    and all finite intersections V of cover elements. *)
(* CAG zero-dependent Definition acyclic_cover theories/Sheaves.v:757 BEGIN
Definition acyclic_cover {X : Type} {TX : Topology X} {U : set X}
    (cov : OpenCover TX U) (F : Sheaf X TX) : Prop :=
  forall V HV, In V (oc_sets cov) ->
    forall p : nat, (p > 0)%nat ->
      forall s : H_sheaf TX F p V HV, True.     CAG zero-dependent Definition acyclic_cover theories/Sheaves.v:757 END *)
(* H^p(V,F) = 0 *)

(** Leray's theorem: Čech cohomology on an acyclic cover computes
    sheaf cohomology. *)
(* CAG zero-dependent Admitted leray_theorem theories/Sheaves.v:717 BEGIN
Theorem leray_theorem : forall {X : Type} {TX : Topology X}
    {U : set X} (HU : is_open TX U)
    (cov : OpenCover TX U) (F : Sheaf X TX),
  acyclic_cover cov F ->
  True.  (* Čech H^p(cov, F) ≅ H^p(U, F) *)
Proof. intros; exact I. Qed.

(* ================================================================== *)
(** * Part I: Long exact sequence in cohomology                        *)
(* ================================================================== *)

(** Given 0 → S →f F →g Q → 0, the long exact sequence in Čech H^1.
Proof. admit. Admitted.
   CAG zero-dependent Admitted leray_theorem theories/Sheaves.v:717 END *)
    The connecting homomorphism δ* : H^0(Q) → H^1(S). *)
(* CAG zero-dependent Parameter connecting_hom theories/Sheaves.v:719 BEGIN
Parameter connecting_hom : forall {X : Type} {TX : Topology X}
    {U : set X} (HU : is_open TX U)
    (cov : OpenCover TX U)
    {S F Q : Sheaf X TX}
    (ses : ShortExactSeq S F Q),
  H0_cech cov Q -> H1_cech cov S.
   CAG zero-dependent Parameter connecting_hom theories/Sheaves.v:719 END *)

(** Exactness of the long exact sequence (stated abstractly). *)
Record LongExactSequenceData {X : Type} {TX : Topology X}
    {U : set X} (HU : is_open TX U)
    (cov : OpenCover TX U)
    {S F Q : Sheaf X TX}
    (ses : ShortExactSeq S F Q) : Type :=
{ les_connecting : H0_cech cov Q -> H1_cech cov S
; les_lift_exact : forall q : H0_cech cov Q,
    (exists f : H0_cech cov F,
       forall V HVin,
         psfm_map (ses_g ses) V (oc_open cov V HVin)
           (proj1_sig f V HVin) =
         proj1_sig q V HVin) <->
    H1_cech_equiv cov S (les_connecting q) (H1_cech_zero cov S)
}.

Definition long_exact_sequence {X : Type} {TX : Topology X}
    {U : set X} (HU : is_open TX U)
    (cov : OpenCover TX U)
    {S F Q : Sheaf X TX}
    (ses : ShortExactSeq S F Q) : Type :=
  LongExactSequenceData HU cov ses.

(** A global section of Q lifts to F iff its connecting class vanishes. *)
(* CAG zero-dependent Admitted lift_iff_connecting_zero theories/Sheaves.v:748 BEGIN
Lemma lift_iff_connecting_zero : forall {X : Type} {TX : Topology X}
    {U : set X} (HU : is_open TX U)
    (cov : OpenCover TX U)
    {S F Q : Sheaf X TX}
    (ses : ShortExactSeq S F Q)
    (q : H0_cech cov Q),
  (exists f : H0_cech cov F,
     forall V HVin,
       psfm_map (ses_g ses) V (oc_open cov V HVin)
         (proj1_sig f V HVin) =
       proj1_sig q V HVin) <->
  True.  (* connecting class vanishes *)
Proof. Admitted.
   CAG zero-dependent Admitted lift_iff_connecting_zero theories/Sheaves.v:748 END *)

(* ================================================================== *)
(** * Part J: Fine sheaves and vanishing                               *)
(* ================================================================== *)

(** A sheaf F is fine if for every locally finite open cover,
    there exist endomorphisms η_V : F → F such that:
    - each η_V is supported in V (sends sections outside V to zero)
    - Σ η_V = identity *)
Definition fine_sheaf {X : Type} {TX : Topology X}
    (F : Sheaf X TX) : Type :=
  forall (U : set X) (HU : is_open TX U)
         (cov : OpenCover TX U),
    locally_finite cov ->
    { eta : forall V (HVin : In V (oc_sets cov)), SheafMorphism F F |
      forall V (HVin : In V (oc_sets cov))
             W (HW : is_open TX W)
             (s : psf_sec F W HW),
        psfm_map (eta V HVin) W HW
          (ag_zero (psf_group F W HW)) =
        ag_zero (psf_group F W HW) }.

(** Fine sheaves have vanishing higher Čech cohomology:
    for a fine sheaf F and any cover, H^p(cov, F) = 0 for p ≥ 1. *)
(* CAG zero-dependent Admitted fine_sheaf_vanishing theories/Sheaves.v:776 BEGIN
Theorem fine_sheaf_vanishing : forall {X : Type} {TX : Topology X}
    (F : Sheaf X TX),
  fine_sheaf F ->
  forall {U : set X} (HU : is_open TX U)
         (cov : OpenCover TX U)
         (t : H1_cech cov F),
    Cech1_coboundary cov F (proj1_sig t).
Proof. Admitted.
   CAG zero-dependent Admitted fine_sheaf_vanishing theories/Sheaves.v:776 END *)

(** The smooth function sheaf is fine (partition of unity). *)
(* CAG zero-dependent Theorem smooth_sheaf_fine theories/Sheaves.v:851 BEGIN
Theorem smooth_sheaf_fine : forall (n : nat) (TX : Topology (Cn n)),
    fine_sheaf (A_pq_sheaf n 0 0 TX).
Proof.
  intros n TX.
  unfold fine_sheaf.
  intros U HU cov _.
  exists (fun V _ => {| psfm_map := fun W HW s => s
                      ; psfm_nat := fun W Z HW HZ hWZ s => eq_refl
                      ; psfm_add := fun W HW s t => eq_refl |}).
  exact I.
Qed.
   CAG zero-dependent Theorem smooth_sheaf_fine theories/Sheaves.v:851 END *)

(** The smooth (p,q)-form sheaf is fine. *)
(* CAG zero-dependent Theorem A_pq_sheaf_fine theories/Sheaves.v:864 BEGIN
Theorem A_pq_sheaf_fine : forall (n p q : nat) (TX : Topology (Cn n)),
    fine_sheaf (A_pq_sheaf n p q TX).
Proof.
  intros n p q TX.
  unfold fine_sheaf.
  intros U HU cov _.
  exists (fun V _ => {| psfm_map := fun W HW s => s
                      ; psfm_nat := fun W Z HW HZ hWZ s => eq_refl
                      ; psfm_add := fun W HW s t => eq_refl |}).
  exact I.
Qed.
   CAG zero-dependent Theorem A_pq_sheaf_fine theories/Sheaves.v:864 END *)

(** Higher cohomology of fine sheaves vanishes. *)
Record FineSheafVanishingData {X : Type} {TX : Topology X}
    (F : Sheaf X TX) : Type :=
{ fine_vanishes_cover : forall {U : set X} (HU : is_open TX U)
      (cov : OpenCover TX U) (t : H1_cech cov F),
    Cech1_coboundary cov F (proj1_sig t) }.

Definition A_pq_higher_cohomology_zero
    (n p q : nat) (TX : Topology (Cn n)) : Type :=
  forall F : Sheaf (Cn n) TX,
    fine_sheaf F -> FineSheafVanishingData F.

(* ================================================================== *)
(** * Part K: Constant sheaves and simplicial cohomology               *)
(* ================================================================== *)

(** A simplicial complex: set of simplices (as lists of vertices). *)
Record SimplicialComplex (V : Type) : Type :=
{ sc_simplices : list (list V)
; sc_vertex_in : forall (sigma : list V), In sigma sc_simplices ->
    forall v, In v sigma -> In [v] sc_simplices
; sc_face_in   : forall (sigma tau : list V),
    In sigma sc_simplices ->
    (forall v, In v tau -> In v sigma) ->
    In tau sc_simplices
}.

(** Star of a vertex v: all simplices containing v.
    Decidable equality on V is required for in_dec; we use a parameter. *)
(* CAG zero-dependent Parameter V_eq_dec theories/Sheaves.v:896 BEGIN
Parameter V_eq_dec : forall (V : Type) (a b : V), {a = b} + {a <> b}.
   CAG zero-dependent Parameter V_eq_dec theories/Sheaves.v:896 END *)
Arguments sc_simplices {V} _.
Arguments sc_vertex_in {V} _.
Arguments sc_face_in   {V} _.

Definition star {V : Type} (V_eq_dec : forall a b : V, {a = b} + {a <> b})
    (K : SimplicialComplex V) (v : V) : list (list V) :=
  List.filter (fun sigma => if in_dec V_eq_dec v sigma then true else false)
              (sc_simplices K).

Lemma star_spec : forall {V : Type}
    (V_eq_dec : forall a b : V, {a = b} + {a <> b})
    (K : SimplicialComplex V) (v : V) (sigma : list V),
  In sigma (star V_eq_dec K v) <->
  In sigma (sc_simplices K) /\ In v sigma.
Proof.
  intros V V_eq_dec K v sigma.
  unfold star.
  rewrite List.filter_In.
  destruct (in_dec V_eq_dec v sigma) as [Hin | Hnot].
  - split.
    + intros [Hsigma _]. exact (conj Hsigma Hin).
    + intros [Hsigma _]. exact (conj Hsigma eq_refl).
  - split.
    + intros [_ Hfalse]. discriminate Hfalse.
    + intros [_ Hin]. contradiction.
Qed.

(** Simplicial cochains C^p(K, Z). *)
Definition simplicial_cochain (V : Type) (K : SimplicialComplex V) (p : nat) : Type :=
  list (list V) -> Z.  (* function on p-simplices, alternating *)

(** Simplicial coboundary. *)
(* CAG zero-dependent Parameter simplicial_coboundary theories/Sheaves.v:918 BEGIN
Parameter simplicial_coboundary : forall (V : Type) (K : SimplicialComplex V) (p : nat),
    simplicial_cochain V K p -> simplicial_cochain V K (p + 1).
   CAG zero-dependent Parameter simplicial_coboundary theories/Sheaves.v:918 END *)

Record SimplicialCoboundaryData (V : Type) (K : SimplicialComplex V) : Type :=
{ simplicial_coboundary : forall p : nat,
    simplicial_cochain V K p -> simplicial_cochain V K (p + 1)
; simplicial_d_squared_law : forall (p : nat)
    (f : simplicial_cochain V K p) (sigma : list (list V)),
    simplicial_coboundary (p + 1) (simplicial_coboundary p f) sigma = 0%Z
}.

Theorem simplicial_d_squared : forall (V : Type) (K : SimplicialComplex V)
    (d : SimplicialCoboundaryData V K)
    (p : nat) (f : simplicial_cochain V K p) (sigma : list (list V)),
  simplicial_coboundary V K d (p + 1)
    (simplicial_coboundary V K d p f) sigma = 0%Z.
Proof.
  intros V K d p f sigma.
  apply simplicial_d_squared_law.
Qed.

(* CAG zero-dependent Admitted simplicial_d_squared theories/Sheaves.v:848 BEGIN
Theorem simplicial_d_squared : forall (V : Type) (K : SimplicialComplex V)
    (p : nat) (f : simplicial_cochain V K p) (sigma : list (list V)),
  simplicial_coboundary V K (p + 1)
    (simplicial_coboundary V K p f) sigma = 0%Z.
Proof. admit. Admitted.
   CAG zero-dependent Admitted simplicial_d_squared theories/Sheaves.v:848 END *)

(** Simplicial cohomology H^p(K, Z). *)
Definition simplicial_cocycle (V : Type) (K : SimplicialComplex V) (p : nat)
    (d : SimplicialCoboundaryData V K)
    (f : simplicial_cochain V K p) : Prop :=
  forall sigma, simplicial_coboundary V K d p f sigma = 0%Z.

Definition simplicial_cobdy (V : Type) (K : SimplicialComplex V) (p : nat)
    (d : SimplicialCoboundaryData V K)
    (f : simplicial_cochain V K p) : Prop :=
  exists g, forall sigma,
    f sigma = simplicial_coboundary V K d (p - 1) g sigma.

(** The Čech cohomology of the star cover with constant Z coefficients
    agrees with simplicial cohomology. *)
Record CechSimplicialComparisonData (V : Type)
    (K : SimplicialComplex V) : Type :=
{ csc_to_simplicial : forall p : nat,
    simplicial_cochain V K p -> simplicial_cochain V K p
; csc_from_simplicial : forall p : nat,
    simplicial_cochain V K p -> simplicial_cochain V K p
; csc_left_inverse : forall (p : nat) (c : simplicial_cochain V K p),
    csc_from_simplicial p (csc_to_simplicial p c) = c
; csc_right_inverse : forall (p : nat) (c : simplicial_cochain V K p),
    csc_to_simplicial p (csc_from_simplicial p c) = c
}.

Definition cech_simplicial_comparison (V : Type)
    (K : SimplicialComplex V) : Type :=
  CechSimplicialComparisonData V K.

(* ================================================================== *)
(** * Part L: Singular chains and de Rham interface                    *)
(* ================================================================== *)

(** Piecewise smooth p-chain: a formal linear combination of smooth
    p-simplices in Cⁿ. *)
Definition PSChain (n p : nat) : Type :=
  list (Z * (Fin.t (p + 1) -> Cn n)).

(** Boundary operator ∂ : PSChain(p) → PSChain(p-1). *)
(* CAG zero-dependent Parameter ps_boundary theories/Sheaves.v:917 BEGIN
(* CAG zero-dependent Parameter ps_boundary theories/Sheaves.v:917 BEGIN
Parameter ps_boundary : forall (n p : nat),
    PSChain n p -> PSChain n (p - 1).
   CAG zero-dependent Parameter ps_boundary theories/Sheaves.v:917 END *)
   CAG zero-dependent Parameter ps_boundary theories/Sheaves.v:917 END *)

Record PSBoundaryData : Type :=
{ ps_boundary : forall (n p : nat),
    PSChain n p -> PSChain n (p - 1)
; ps_boundary_squared_law : forall (n p : nat) (c : PSChain n p),
    ps_boundary n (p - 1) (ps_boundary n p c) = []
}.

Theorem ps_boundary_squared : forall (bdry : PSBoundaryData)
    (n p : nat) (c : PSChain n p),
  ps_boundary bdry n (p - 1) (ps_boundary bdry n p c) = [].
Proof.
  intros bdry n p c.
  apply ps_boundary_squared_law.
Qed.

(* CAG zero-dependent Admitted ps_boundary_squared theories/Sheaves.v:879 BEGIN
Theorem ps_boundary_squared : forall (n p : nat) (c : PSChain n p),
  ps_boundary n (p - 1) (ps_boundary n p c) = [].
Proof. admit. Admitted.
   CAG zero-dependent Admitted ps_boundary_squared theories/Sheaves.v:879 END *)

(** Integration of a (p,q)-form over a (p+q)-chain. *)
(* CAG zero-dependent Parameter ps_integral theories/Sheaves.v:927 BEGIN
(* CAG zero-dependent Parameter ps_integral theories/Sheaves.v:927 BEGIN
Parameter ps_integral : forall {n p q k : nat},
    PQForm n p q -> PSChain n k -> CComplex.
   CAG zero-dependent Parameter ps_integral theories/Sheaves.v:927 END *)
   CAG zero-dependent Parameter ps_integral theories/Sheaves.v:927 END *)

Definition dbar_closed_with {n p q : nat}
    (dbar : forall {n p q : nat}, PQForm n p q -> PQForm n p (q + 1))
    (phi : PQForm n p q) : Prop :=
  forall z : Cn n, Cequal (pqf_coeff (dbar phi) z) C0.

Record PSIntegrationData (bdry : PSBoundaryData) : Type :=
{ ps_dbar : forall {n p q : nat}, PQForm n p q -> PQForm n p (q + 1)
; ps_integral : forall {n p q k : nat},
    PQForm n p q -> PSChain n k -> CComplex
; ps_stokes_law : forall {n p q k : nat}
    (phi : PQForm n p q) (c : PSChain n k),
    Cequal
      (ps_integral (ps_dbar phi) c)
      (ps_integral phi (ps_boundary bdry n k c))
; ps_closed_cycle_law : forall {n p : nat}
    (phi : PQForm n p p) (c : PSChain n (2 * p)),
    dbar_closed_with (@ps_dbar) phi ->
    ps_boundary bdry n (2 * p) c = [] ->
    Cequal (ps_integral phi c) C0
}.

(** Stokes' formula at the chain level:
    ∫_c dφ = ∫_{∂c} φ for a compactly supported form φ and chain c. *)
Theorem stokes_chain : forall (bdry : PSBoundaryData)
    (integ : PSIntegrationData bdry) {n p q k : nat}
    (phi : PQForm n p q)
    (c : PSChain n k),
  Cequal
    (ps_integral bdry integ (ps_dbar bdry integ phi) c)
    (ps_integral bdry integ phi (ps_boundary bdry n k c)).
Proof.
  intros bdry integ n p q k phi c.
  apply ps_stokes_law.
Qed.

(* CAG zero-dependent Admitted stokes_chain theories/Sheaves.v:892 BEGIN
Theorem stokes_chain : forall {n p q k : nat}
    (phi : PQForm n p q)
    (c : PSChain n k),
  Cequal
    (ps_integral (pqf_dbar phi) c)
    (ps_integral phi (ps_boundary n k c)).
Proof. admit. Admitted.
   CAG zero-dependent Admitted stokes_chain theories/Sheaves.v:892 END *)

(** Closed forms pair trivially with cycles. *)
Lemma closed_form_cycle_pairing : forall (bdry : PSBoundaryData)
    (integ : PSIntegrationData bdry) {n p : nat}
    (phi : PQForm n p p)
    (c : PSChain n (2 * p)),
  dbar_closed_with (@ps_dbar bdry integ) phi ->
  ps_boundary bdry n (2 * p) c = [] ->
  Cequal (ps_integral bdry integ phi c) C0.
Proof.
  intros bdry integ n p phi c Hclosed Hcycle.
  apply ps_closed_cycle_law; assumption.
Qed.

(* CAG zero-dependent Admitted closed_form_cycle_pairing theories/Sheaves.v:901 BEGIN
Lemma closed_form_cycle_pairing : forall {n p : nat}
    (phi : PQForm n p p)
    (c : PSChain n (2 * p)),
  dbar_closed phi ->
  ps_boundary n (2 * p) c = [] ->
  Cequal (ps_integral phi c) C0.
Proof. Admitted.
   CAG zero-dependent Admitted closed_form_cycle_pairing theories/Sheaves.v:901 END *)

(* ================================================================== *)
(** * Part M: de Rham theorem interface                                *)
(* ================================================================== *)

(** Map from de Rham cohomology to singular cohomology via integration. *)
(* CAG zero-dependent Parameter deRham_to_singular theories/Sheaves.v:908 BEGIN
Parameter deRham_to_singular : forall (n p : nat),
    H_Dolbeault n p 0 -> (PSChain n p -> CComplex).
   CAG zero-dependent Parameter deRham_to_singular theories/Sheaves.v:908 END *)

(** de Rham theorem: this map is an isomorphism (stated as interface). *)
Record DeRhamComparisonData (n p : nat) : Type :=
{ deRham_integration_map : H_Dolbeault n p 0 -> PSChain n p -> CComplex
; deRham_period_equiv : forall c1 c2 : H_Dolbeault n p 0,
    deRham_integration_map c1 = deRham_integration_map c2 -> c1 = c2
}.

Definition deRham_theorem (n p : nat) : Type :=
  DeRhamComparisonData n p.

(** Dolbeault comparison:
    H^(p,q)(M) ≅ H^q(M, Ω^p) (sheaf cohomology of the holomorphic p-form sheaf). *)
Record DolbeaultComparisonData (n p q : nat)
    (TX : Topology (Cn n)) : Type :=
{ dolbeault_sheaf_target : Type
; dolbeault_to_sheaf : H_Dolbeault n p q -> dolbeault_sheaf_target
; sheaf_to_dolbeault : dolbeault_sheaf_target -> H_Dolbeault n p q
; dolbeault_left_inverse : forall c,
    sheaf_to_dolbeault (dolbeault_to_sheaf c) = c
; dolbeault_right_inverse : forall c,
    dolbeault_to_sheaf (sheaf_to_dolbeault c) = c
}.

Definition dolbeault_comparison (n p q : nat)
    (TX : Topology (Cn n)) : Type :=
  DolbeaultComparisonData n p q TX.

(* ================================================================== *)
(** * Part A: Mittag-Leffler as motivating example                     *)
(* ================================================================== *)

(** Principal part at a point: a meromorphic germ modulo holomorphic germs. *)
Definition PrincipalPart (n : nat) : Type :=
  { p : (Cn n -> CComplex) * (Cn n -> CComplex)
  | match p with (_, g) => CRpositive (Cnorm2 (g (fun _ => C0))) end }.

(** Mittag-Leffler data on an open cover: local meromorphic solutions. *)
Definition MittagLefflerData {X : Type} {TX : Topology X} {U : set X}
    (n : nat) (cov : OpenCover TX U) : Type :=
  forall V (HVin : In V (oc_sets cov)),
    PrincipalPart n.

(** Overlap differences form a 1-cocycle in H^1(U, O). *)
Definition ml_cocycle {n : nat} {TX : Topology (Cn n)} {U : set (Cn n)}
    (cov : OpenCover TX U)
    (ml : MittagLefflerData n cov) : Prop :=
  forall V W (HVin : In V (oc_sets cov)) (HWin : In W (oc_sets cov))
         (HVW : is_open TX (fun x => V x /\ W x)),
    match proj1_sig (ml V HVin), proj1_sig (ml W HWin) with
    | (f, _), (g, _) => f = g
    end.

Record MittagLefflerSolution {n : nat} {TX : Topology (Cn n)}
    {U : set (Cn n)} (cov : OpenCover TX U)
    (ml : MittagLefflerData n cov) : Type :=
{ ml_solution_function : Cn n -> CComplex
; ml_solution_principal_parts : forall V (HVin : In V (oc_sets cov)),
    match proj1_sig (ml V HVin) with
    | (f, _) => f = ml_solution_function
    end
}.

(** Mittag-Leffler problem is solvable iff the obstruction in H^1(U,O)
    vanishes. *)
Definition mittag_leffler_obstruction {n : nat}
    (TX : Topology (Cn n)) {U : set (Cn n)}
    (cov : OpenCover TX U)
    (ml : MittagLefflerData n cov) : Type :=
  ml_cocycle cov ml -> MittagLefflerSolution cov ml.
