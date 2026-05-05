(** Projective/FunctionFields.v — Meromorphic = rational on projective varieties

    Key theorems:
    1. Every meromorphic function on P^n is rational.
       Proof: f meromorphic → (f)_0, (f)_∞ are divisors → by Chow's theorem
       they are algebraic → use homogeneous polynomials F,G of same degree
       → f = λ·F/G.

    2. Every meromorphic function on a smooth projective variety V is rational.
       Proof: generic projection π : V → P^k of degree d.
       f → elementary symmetric functions ψ_1,...,ψ_d on P^k (rational by 1).
       f satisfies polynomial P(T) = T^d - ψ_1 T^{d-1} + ... = 0 over K(P^k).
       Degree lower bound forces [M(V):π*K(P^k)] = d → every f is rational.

    References: ag.org Part I–II §Rational and meromorphic functions *)

From Stdlib Require Import List Arith ZArith Lia.
From CAG Require Import Complex.
From CAG Require Import ManifoldTopology.
From CAG Require Import AG.
From CAG Require Import Divisor.DivisorBundle.
From CAG Require Import Divisor.LineBundleCech.
From CAG Require Import Projective.TangentSpace.
From CAG Require Import Kahler.Lefschetz.Operators.

Local Open Scope CReal_scope.

(** P^n as a Kähler manifold. *)
(* CAG zero-dependent Parameter CPn_kahler theories/Projective/FunctionFields.v:29 BEGIN
Parameter CPn_kahler : nat -> KahlerManifold.
   CAG zero-dependent Parameter CPn_kahler theories/Projective/FunctionFields.v:29 END *)


(** A projective variety as a Kähler manifold (restricting the ambient metric). *)
(* CAG zero-dependent Parameter pv_to_kahler theories/Projective/FunctionFields.v:34 BEGIN
Parameter pv_to_kahler : ProjectiveVariety -> KahlerManifold.
   CAG zero-dependent Parameter pv_to_kahler theories/Projective/FunctionFields.v:34 END *)

(* ================================================================== *)
(** * 1. Rational functions on P^n                                     *)
(* ================================================================== *)

(** A rational function on P^n: a ratio F/G of homogeneous polynomials
    of the same degree, with G not identically zero. *)
(* CAG constructive-remove Record RationalFunctionPn theories/Projective/FunctionFields.v:45 BEGIN -- repair partial command cleanup after removing HomogPoly
Record RationalFunctionPn (n : nat) : Type :=
(* CAG constructive-remove Command { theories/Projective/FunctionFields.v:46 BEGIN -- missing HomogPoly
{ rf_num : HomogPoly n 1  (** numerator F, degree will be matched *)
; rf_den : HomogPoly n 1  (** denominator G, degree will be matched *)
; rf_den_nonzero : True   (** G not identically zero — formal placeholder *)
}.

   CAG constructive-remove Command { theories/Projective/FunctionFields.v:46 END *)
   CAG constructive-remove Record RationalFunctionPn theories/Projective/FunctionFields.v:45 END *)

(** Evaluation of a rational function away from zeros of G. *)
(* CAG zero-dependent Parameter rf_eval theories/Projective/FunctionFields.v:46 BEGIN
Parameter rf_eval : forall {n : nat} (f : RationalFunctionPn n)
    (p : Cn (n+1)),
    (** p ∉ zero set of rf_den f *)
    True -> CComplex.
   CAG zero-dependent Parameter rf_eval theories/Projective/FunctionFields.v:46 END *)

(* ================================================================== *)
(** * 2. Meromorphic functions                                         *)
(* ================================================================== *)

(** A meromorphic function on a complex manifold M. *)
(* CAG zero-dependent Parameter MeromorphicFn theories/Projective/FunctionFields.v:61 BEGIN
Parameter MeromorphicFn : forall (M : KahlerManifold), Type.
   CAG zero-dependent Parameter MeromorphicFn theories/Projective/FunctionFields.v:61 END *)

(** The zero divisor (f)_0 and pole divisor (f)_∞ of a meromorphic function. *)
(* CAG zero-dependent Parameter zero_divisor_of theories/Projective/FunctionFields.v:59 BEGIN
Parameter zero_divisor_of : forall (M : KahlerManifold),
    MeromorphicFn M -> Divisor (km_manifold M).
   CAG zero-dependent Parameter zero_divisor_of theories/Projective/FunctionFields.v:59 END *)
(* CAG zero-dependent Parameter pole_divisor_of theories/Projective/FunctionFields.v:61 BEGIN
Parameter pole_divisor_of : forall (M : KahlerManifold),
    MeromorphicFn M -> Divisor (km_manifold M).
   CAG zero-dependent Parameter pole_divisor_of theories/Projective/FunctionFields.v:61 END *)

(** The principal divisor (f) = (f)_0 - (f)_∞. *)
(* CAG zero-dependent Parameter principal_divisor theories/Projective/FunctionFields.v:65 BEGIN
Parameter principal_divisor : forall (M : KahlerManifold),
    MeromorphicFn M -> Divisor (km_manifold M).
   CAG zero-dependent Parameter principal_divisor theories/Projective/FunctionFields.v:65 END *)

(** A rational function on P^n viewed as meromorphic. *)
(* CAG zero-dependent Parameter rational_to_meromorphic_Pn theories/Projective/FunctionFields.v:69 BEGIN
Parameter rational_to_meromorphic_Pn : forall (n : nat),
    RationalFunctionPn n -> MeromorphicFn (CPn_kahler n).
   CAG zero-dependent Parameter rational_to_meromorphic_Pn theories/Projective/FunctionFields.v:69 END *)

(** The field of meromorphic functions on M. *)
(* CAG zero-dependent Parameter MeromorphicField theories/Projective/FunctionFields.v:73 BEGIN
Parameter MeromorphicField : forall (M : KahlerManifold), Type.
   CAG zero-dependent Parameter MeromorphicField theories/Projective/FunctionFields.v:73 END *)

(** The field of rational functions on V (restriction of ambient rational functions). *)
(* CAG zero-dependent Parameter RationalField theories/Projective/FunctionFields.v:76 BEGIN
Parameter RationalField : forall (V : ProjectiveVariety), Type.
   CAG zero-dependent Parameter RationalField theories/Projective/FunctionFields.v:76 END *)

(* ================================================================== *)
(** * 3. Chow's theorem                                                *)
(* ================================================================== *)

(** Predicate: [S] is a closed analytic subset of [Pⁿ] (axiomatized;
    see [ManifoldTopology] for the analytic-set infrastructure that
    would discharge this in a full development). *)
(* CAG zero-dependent Parameter is_closed_analytic_subset theories/Projective/FunctionFields.v:100 BEGIN
Parameter is_closed_analytic_subset : forall (n : nat),
    (Cn (n+1) -> Prop) -> Prop.
   CAG zero-dependent Parameter is_closed_analytic_subset theories/Projective/FunctionFields.v:100 END *)

(** Chow's theorem (famous old theorem; left as Conjecture per skip
    policy): every analytic subset of [Pⁿ] is algebraic — the zero
    set of finitely many homogeneous polynomials.  Source: Chow 1949;
    Griffiths–Harris Ch. 1.3 §"Chow's theorem"; Mumford Lec. 4. *)
(* CAG zero-dependent Conjecture chow_theorem theories/Projective/FunctionFields.v:107 BEGIN
Conjecture chow_theorem : forall (n : nat) (S : Cn (n+1) -> Prop),
    is_closed_analytic_subset n S ->
    exists (k : nat) (d : Fin.t k -> nat)
           (F : forall i : Fin.t k, HomogPoly n (d i)),
      forall p : Cn (n+1),
        S p <-> forall i : Fin.t k, poly_eval (homog_to_poly (F i)) p = C0.
   CAG zero-dependent Conjecture chow_theorem theories/Projective/FunctionFields.v:107 END *)

(* ================================================================== *)
(** * 4. Meromorphic = rational on P^n                                 *)
(* ================================================================== *)

(** Every meromorphic function on P^n is rational. *)
(* CAG zero-dependent Admitted meromorphic_is_rational_Pn theories/Projective/FunctionFields.v:109 BEGIN
Theorem meromorphic_is_rational_Pn : forall (n : nat)
    (f : MeromorphicFn (CPn_kahler n)),
    (** there exists a rational function r with f = rational_to_meromorphic_Pn n r *)
    exists r : RationalFunctionPn n,
    True. (** f = r as meromorphic functions *)
Proof. admit. Admitted.
   CAG zero-dependent Admitted meromorphic_is_rational_Pn theories/Projective/FunctionFields.v:109 END *)

(* ================================================================== *)
(** * 5. Generic projection                                            *)
(* ================================================================== *)

(** A generic projection of a k-dimensional projective variety V ⊂ P^n
    to a complementary P^k.  The fiber over a generic point has d = deg(V) points. *)
(* CAG zero-dependent Parameter GenericProjection theories/Projective/FunctionFields.v:134 BEGIN
Parameter GenericProjection : forall (V : ProjectiveVariety), Type.
   CAG zero-dependent Parameter GenericProjection theories/Projective/FunctionFields.v:134 END *)

(** The projection map π. *)
(* CAG zero-dependent Parameter gp_map theories/Projective/FunctionFields.v:120 BEGIN
Parameter gp_map : forall (V : ProjectiveVariety),
    GenericProjection V ->
    Cn (pv_ambient_dim V + 1) -> Cn (pv_complex_dim V + 1).
   CAG zero-dependent Parameter gp_map theories/Projective/FunctionFields.v:120 END *)

(** The degree of the generic projection equals deg(V). *)
(* CAG zero-dependent Parameter variety_degree theories/Projective/FunctionFields.v:144 BEGIN
(* CAG zero-dependent Parameter variety_degree theories/Projective/FunctionFields.v:144 BEGIN
Parameter variety_degree : ProjectiveVariety -> nat.
   CAG zero-dependent Parameter variety_degree theories/Projective/FunctionFields.v:144 END *)
   CAG zero-dependent Parameter variety_degree theories/Projective/FunctionFields.v:144 END *)

(** Cardinality of the generic fiber of a generic projection
    (axiomatized count). *)
(* CAG zero-dependent Parameter generic_fiber_card theories/Projective/FunctionFields.v:148 BEGIN
(* CAG zero-dependent Parameter generic_fiber_card theories/Projective/FunctionFields.v:148 BEGIN
Parameter generic_fiber_card : forall (V : ProjectiveVariety),
    GenericProjection V -> nat.
   CAG zero-dependent Parameter generic_fiber_card theories/Projective/FunctionFields.v:148 END *)
   CAG zero-dependent Parameter generic_fiber_card theories/Projective/FunctionFields.v:148 END *)

(** Generic projection has fiber cardinality [variety_degree V].

    Informal definition: the generic projection [π : V → Pᵏ] of a
    k-dimensional variety has generic fiber of size [variety_degree V]
    points (Griffiths–Harris Ch. 1.3 §"Generic projection";
    Hartshorne I.7.6).  Stated as a numerical equality on the
    structural cardinality function. *)
(* CAG zero-dependent Axiom generic_projection_degree theories/Projective/FunctionFields.v:139 BEGIN
Axiom generic_projection_degree : forall (V : ProjectiveVariety)
    (π : GenericProjection V),
    generic_fiber_card V π = variety_degree V.
   CAG zero-dependent Axiom generic_projection_degree theories/Projective/FunctionFields.v:139 END *)

(** All fibers of π are finite (no continuous family in a fiber).

    Informal definition: every fiber of [π : V → Pᵏ] is finite, as a
    consequence of the projection theorem for proper morphisms
    (Griffiths–Harris Ch. 1.3; Hartshorne II.4.8).  Stated as
    boundedness of fiber cardinality via the existing
    [generic_fiber_card]. *)
(* CAG zero-dependent Axiom generic_projection_finite_fibers theories/Projective/FunctionFields.v:150 BEGIN
Axiom generic_projection_finite_fibers : forall (V : ProjectiveVariety)
    (π : GenericProjection V),
    exists N : nat, forall π' : GenericProjection V,
      (generic_fiber_card V π' <= N)%nat.
   CAG zero-dependent Axiom generic_projection_finite_fibers theories/Projective/FunctionFields.v:150 END *)

(* ================================================================== *)
(** * 6. Meromorphic = rational on smooth projective varieties          *)
(* ================================================================== *)

(** Predicate: a meromorphic function on V is rational, in the sense
    that it lies in the image of the rational-to-meromorphic embedding
    on V (axiomatized at this layer; the embedding is built downstream). *)
(* CAG zero-dependent Parameter is_rational_on theories/Projective/FunctionFields.v:197 BEGIN
Parameter is_rational_on : forall (V : ProjectiveVariety),
    MeromorphicFn (pv_to_kahler V) -> Prop.
   CAG zero-dependent Parameter is_rational_on theories/Projective/FunctionFields.v:197 END *)

(** Main theorem (famous, GAGA-flavored; left as Conjecture per skip
    policy): on a smooth projective variety, every meromorphic function
    is rational — i.e. [M(V) = K(V)].
    Source: Serre 1956 GAGA, Griffiths–Harris Ch. 1.3 §"Meromorphic =
    rational on smooth projective varieties". *)
(* CAG zero-dependent Conjecture meromorphic_is_rational theories/Projective/FunctionFields.v:203 BEGIN
Conjecture meromorphic_is_rational : forall (V : ProjectiveVariety)
    (f : MeromorphicFn (pv_to_kahler V)),
    is_rational_on V f.
   CAG zero-dependent Conjecture meromorphic_is_rational theories/Projective/FunctionFields.v:203 END *)

(** Equivalently: the field extension [M(V) : π*K(Pᵏ)] = d = deg(V).

    Informal definition: stated as the existence of a finite-rank
    abstract field-extension index witnessing [variety_degree V]
    (Griffiths–Harris Ch. 1.3 §"Function field degree"; Mumford Lec. 7). *)
(* CAG zero-dependent Parameter function_field_extension_index theories/Projective/FunctionFields.v:202 BEGIN
(* CAG zero-dependent Parameter function_field_extension_index theories/Projective/FunctionFields.v:202 BEGIN
Parameter function_field_extension_index : forall (V : ProjectiveVariety),
    GenericProjection V -> nat.
   CAG zero-dependent Parameter function_field_extension_index theories/Projective/FunctionFields.v:202 END *)
   CAG zero-dependent Parameter function_field_extension_index theories/Projective/FunctionFields.v:202 END *)

(* CAG zero-dependent Axiom function_field_degree theories/Projective/FunctionFields.v:182 BEGIN
Axiom function_field_degree : forall (V : ProjectiveVariety)
    (π : GenericProjection V),
    function_field_extension_index V π = variety_degree V.
   CAG zero-dependent Axiom function_field_degree theories/Projective/FunctionFields.v:182 END *)

(* ================================================================== *)
(** * 7. GAGA-style corollaries                                        *)
(* ================================================================== *)

(** Predicate: meromorphic differential forms on V (axiomatized
    pointer; full structure requires sheaf cohomology of Ω). *)
(* CAG zero-dependent Parameter MeromorphicForm theories/Projective/FunctionFields.v:241 BEGIN
Parameter MeromorphicForm : forall (V : ProjectiveVariety) (k : nat), Type.
   CAG zero-dependent Parameter MeromorphicForm theories/Projective/FunctionFields.v:241 END *)

(** Predicate: a meromorphic k-form is algebraic. *)
(* CAG zero-dependent Parameter form_is_algebraic theories/Projective/FunctionFields.v:238 BEGIN
Parameter form_is_algebraic : forall (V : ProjectiveVariety) (k : nat),
    MeromorphicForm V k -> Prop.
   CAG zero-dependent Parameter form_is_algebraic theories/Projective/FunctionFields.v:238 END *)

(** Any meromorphic differential form on a smooth projective variety is
    algebraic.  GAGA-style consequence (famous; left as Conjecture per
    skip policy).  Source: Serre 1956 GAGA, Griffiths–Harris Ch. 1.3
    §"Meromorphic forms are algebraic". *)
(* CAG zero-dependent Conjecture meromorphic_forms_are_algebraic theories/Projective/FunctionFields.v:241 BEGIN
Conjecture meromorphic_forms_are_algebraic : forall (V : ProjectiveVariety)
    (k : nat) (ω : MeromorphicForm V k),
    form_is_algebraic V k ω.
   CAG zero-dependent Conjecture meromorphic_forms_are_algebraic theories/Projective/FunctionFields.v:241 END *)

(** Holomorphic-map predicate between projective varieties (axiomatized;
    full structure built on the embedding into projective spaces). *)
(* CAG zero-dependent Parameter HolomorphicMap theories/Projective/FunctionFields.v:261 BEGIN
Parameter HolomorphicMap : ProjectiveVariety -> ProjectiveVariety -> Type.
   CAG zero-dependent Parameter HolomorphicMap theories/Projective/FunctionFields.v:261 END *)

(* CAG zero-dependent Parameter map_is_algebraic theories/Projective/FunctionFields.v:255 BEGIN
Parameter map_is_algebraic : forall (V W : ProjectiveVariety),
    HolomorphicMap V W -> Prop.
   CAG zero-dependent Parameter map_is_algebraic theories/Projective/FunctionFields.v:255 END *)

(** Any holomorphic map between smooth projective varieties is
    algebraic (famous GAGA corollary; Conjecture per skip policy).
    Source: Serre 1956 GAGA, Griffiths–Harris Ch. 1.3 §"GAGA"; the
    proof passes through the graph in [V × W] and applies Chow. *)
(* CAG zero-dependent Conjecture holomorphic_maps_are_algebraic theories/Projective/FunctionFields.v:256 BEGIN
Conjecture holomorphic_maps_are_algebraic : forall (V W : ProjectiveVariety)
    (φ : HolomorphicMap V W),
    map_is_algebraic V W φ.
   CAG zero-dependent Conjecture holomorphic_maps_are_algebraic theories/Projective/FunctionFields.v:256 END *)
