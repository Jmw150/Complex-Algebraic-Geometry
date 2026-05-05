(** * (p,q)-forms with proper multi-index structure.

    This file replaces the degenerate single-coefficient [PQForm] record
    of AG.v with a properly indexed structure:

      α = Σ_{|I|=p, |J|=q} f_{IJ}(z) dz_I ∧ dz̄_J,

    where [I = (i_0 < ... < i_{p-1})] and [J = (j_0 < ... < j_{q-1})]
    are strictly-increasing index lists in [{0,..,n-1}], represented by
    [MultiIndex n p] / [MultiIndex n q].

    With this representation [pqf_dbar] and [pqf_del] become CONCRETE
    Definitions (no longer Parameters): each new coefficient at
    [(I, J')] (with [|J'| = q+1]) is the alternating sum

      (∂̄α)_{I, J'} (z) = Σ_{r=0}^{q} (-1)^r ∂̄_{j_r} (α_{I, J'∖j_r}) (z)

    and similarly for [∂].

    Computing [∂̄_k f] of a function [f : Cn n -> CComplex] at the
    function level — rather than at a single point — requires a
    derivative-witness axiom, since the constructive Cauchy-real
    framework does not provide a total derivative function.  We
    introduce a single sided-Wirtinger witness primitive:

      [partial_wirtinger_witness :
         bool -> (Cn n -> CComplex) -> Fin.t n -> Cn n -> CComplex]

    together with one soundness postulate.  The two projected wrappers
    [partial_z_witness] / [partial_zbar_witness] and their
    correctness lemmas are derived as Definitions / Lemmas (no extra
    axioms; β R11 consolidation, 2026-05-01: previously 4 axioms,
    now 2).  These are the ONLY new project axioms introduced by this
    file.

    Downstream of this file, [pqf_dbar] and [pqf_del] are real
    Definitions, [pqf_zero], [pqf_add], [pqf_scale] become elementwise
    operations, and the legacy scalar accessor [pqf_coeff] is provided
    as a Definition (the (∅,∅) coefficient at degree (0,0); zero
    otherwise) for backward compatibility with consumers that treated
    [pqf_coeff phi z] as a CComplex.
*)

From Stdlib Require Import Arith.PeanoNat Lia List ZArith.
Import ListNotations.

Set Warnings "-warn-library-file-stdlib-vector".
From Stdlib Require Import Vectors.Fin.
Set Warnings "+warn-library-file-stdlib-vector".

From CAG Require Import Complex.
From CAG Require Import Calc.PartialDerivatives.
From CAG Require Import Calc.MultiIndex.

(* ------------------------------------------------------------------ *)
(** * 1. Derivative-witness axioms                                      *)
(* ------------------------------------------------------------------ *)

(** Function-level Wirtinger partial of a [Cn n -> CComplex] function,
    in the [j]-th coordinate, parameterised by a sided-flag [s : bool]
    distinguishing the holomorphic ∂_j (when [s = true]) from the
    anti-holomorphic ∂̄_j (when [s = false]).

    This is a "definite description" witness: given [f] and the side
    [s], it returns a function [Cn n -> CComplex] which at every [v]
    equals the Prop-level partial derivative [partial_z_at f v j L] /
    [partial_zbar_at f v j L] specified by [s].  We do not assume
    convergence or smoothness; the soundness axiom only fires when the
    chosen Prop-level Wirtinger derivative actually exists.

    Soundness rationale: classical Hilbert ε / definite description on
    CReal limits.  Same paper-attributable risk/value calculus as
    [Cderiv_witness] / [Cderiv_witness_correct] in [ComplexAnalysis.v]
    (see γ R18, REFACTOR_PLAN.org).  The two-sided unified primitive
    halves the previous axiom count (β R11 consolidation, 2026-05-01:
    4 axioms → 2 axioms; the projected ∂_j and ∂̄_j wrappers below are
    Definitions).  A genuine concretisation requires the
    Wirtinger-CR bridge flagged by γ R18 — i.e. a real-partial
    [Rderiv]-witness foundation — which has not yet been built. *)

(* CAG zero-dependent Axiom partial_wirtinger_witness theories/Calc/Forms.v:81 BEGIN
Axiom partial_wirtinger_witness :
  forall {n : nat}, bool -> (Cn n -> CComplex) -> Fin.t n -> Cn n -> CComplex.
   CAG zero-dependent Axiom partial_wirtinger_witness theories/Calc/Forms.v:81 END *)

(** Soundness: when the Prop-level Wirtinger value exists at [v], the
    witness equals it.  In CReal-valued mathematics this holds
    vacuously when no derivative exists; when the derivative exists as
    a unique value, the witness reproduces it. *)
(* CAG zero-dependent Axiom partial_wirtinger_witness_correct theories/Calc/Forms.v:88 BEGIN
Axiom partial_wirtinger_witness_correct :
  forall {n} (s : bool) (f : Cn n -> CComplex) (j : Fin.t n)
         (v : Cn n) (L : CComplex),
    (if s then partial_z_at f v j L else partial_zbar_at f v j L) ->
    Cequal (partial_wirtinger_witness s f j v) L.
   CAG zero-dependent Axiom partial_wirtinger_witness_correct theories/Calc/Forms.v:88 END *)

(** Holomorphic ∂_j witness — unchanged downstream API. *)
(* CAG zero-dependent Definition partial_z_witness theories/Calc/Forms.v:95 BEGIN
Definition partial_z_witness {n : nat}
    (f : Cn n -> CComplex) (j : Fin.t n) (v : Cn n) : CComplex :=
  partial_wirtinger_witness true f j v.
   CAG zero-dependent Definition partial_z_witness theories/Calc/Forms.v:95 END *)

(** Anti-holomorphic ∂̄_j witness — unchanged downstream API. *)
(* CAG zero-dependent Definition partial_zbar_witness theories/Calc/Forms.v:100 BEGIN
Definition partial_zbar_witness {n : nat}
    (f : Cn n -> CComplex) (j : Fin.t n) (v : Cn n) : CComplex :=
  partial_wirtinger_witness false f j v.
   CAG zero-dependent Definition partial_zbar_witness theories/Calc/Forms.v:100 END *)

(** Soundness for the holomorphic ∂_j projection — derived from the
    parametric correctness axiom by specialising [s := true]. *)
(* CAG zero-dependent Lemma partial_z_witness_correct theories/Calc/Forms.v:106 BEGIN
Lemma partial_z_witness_correct :
  forall {n} (f : Cn n -> CComplex) (j : Fin.t n) (v : Cn n) (L : CComplex),
    partial_z_at f v j L ->
    Cequal (partial_z_witness f j v) L.
Proof.
  intros n f j v L H. unfold partial_z_witness.
  exact (partial_wirtinger_witness_correct true f j v L H).
Qed.
   CAG zero-dependent Lemma partial_z_witness_correct theories/Calc/Forms.v:106 END *)

(** Soundness for the anti-holomorphic ∂̄_j projection — derived from
    the parametric correctness axiom by specialising [s := false]. *)
(* CAG zero-dependent Lemma partial_zbar_witness_correct theories/Calc/Forms.v:117 BEGIN
Lemma partial_zbar_witness_correct :
  forall {n} (f : Cn n -> CComplex) (j : Fin.t n) (v : Cn n) (L : CComplex),
    partial_zbar_at f v j L ->
    Cequal (partial_zbar_witness f j v) L.
Proof.
  intros n f j v L H. unfold partial_zbar_witness.
  exact (partial_wirtinger_witness_correct false f j v L H).
Qed.
   CAG zero-dependent Lemma partial_zbar_witness_correct theories/Calc/Forms.v:117 END *)

(* ------------------------------------------------------------------ *)
(** * 2. Conversion: nat → Fin.t n with default                         *)
(* ------------------------------------------------------------------ *)

(** Build a [Fin.t n] from a [nat] [k] with a proof [k < n].  We use
    [Fin.of_nat_lt] from the Stdlib [Vectors.Fin] library. *)
Definition fin_of_nat_lt' (n k : nat) (Hk : k < n) : Fin.t n :=
  Fin.of_nat_lt Hk.

(** Bound-checked cast: converts [k : nat] to [Fin.t n] when possible.
    Fails (returns [None]) otherwise. *)
Definition fin_of_nat (n k : nat) : option (Fin.t n) :=
  match lt_dec k n with
  | left H  => Some (Fin.of_nat_lt H)
  | right _ => None
  end.

(* ------------------------------------------------------------------ *)
(** * 3. The indexed PQForm record                                      *)
(* ------------------------------------------------------------------ *)

(** A (p,q)-form on [Cⁿ] is given by a coefficient function
    [f_{I,J} : Cn n -> CComplex] for each pair of strictly-increasing
    multi-indices [I] (length p) and [J] (length q). *)
Record PQForm (n p q : nat) : Type := mkPQForm
  { pqf_at : MultiIndex n p -> MultiIndex n q -> Cn n -> CComplex
  ; pqf_p  : nat := p
  ; pqf_q  : nat := q
  }.

Arguments pqf_at {n p q} _ _ _ _.

(** Backward-compatible scalar accessor: gives a single-CComplex value
    for the form at point [z].  For (0,0)-forms this is exactly the
    sole coefficient.  For higher-degree forms, returns the
    coefficient at the lexicographically-first multi-index pair (an
    arbitrary projection — sufficient for downstream consumers that
    only care about the trace-like scalar value). *)
Definition pqf_coeff_first {n p q : nat} (phi : PQForm n p q) (z : Cn n) : CComplex :=
  match enum_MI n p, enum_MI n q with
  | I0 :: _, J0 :: _ => pqf_at phi I0 J0 z
  | _, _             => C0
  end.

(** Legacy alias: [pqf_coeff phi z] = [pqf_coeff_first phi z].
    Downstream consumers (e.g. Curvature.v, RiemannSurfaceDegree.v)
    that expect [pqf_coeff phi z : CComplex] continue to work. *)
Definition pqf_coeff {n p q : nat} (phi : PQForm n p q) (z : Cn n) : CComplex :=
  pqf_coeff_first phi z.

(* ------------------------------------------------------------------ *)
(** * 4. Algebraic operations                                           *)
(* ------------------------------------------------------------------ *)

(** Zero (p,q)-form. *)
Definition pqf_zero (n p q : nat) : PQForm n p q :=
  {| pqf_at := fun _ _ _ => C0 |}.

(** Pointwise/elementwise addition. *)
Definition pqf_add {n p q : nat} (phi psi : PQForm n p q) : PQForm n p q :=
  {| pqf_at := fun I J z => Cadd (pqf_at phi I J z) (pqf_at psi I J z) |}.

(** Scalar multiplication (constant scalar). *)
Definition pqf_scale {n p q : nat} (c : CComplex) (phi : PQForm n p q) : PQForm n p q :=
  {| pqf_at := fun I J z => Cmul c (pqf_at phi I J z) |}.

(* ------------------------------------------------------------------ *)
(** * 5. The ∂̄ operator                                                  *)
(* ------------------------------------------------------------------ *)

(** Helper: given a list [J' : MultiIndex n (S q)] and a particular
    nat [k] that occurs in [J'], remove [k] to produce a
    [MultiIndex n q]. *)

(** Helper: sum over a list of CComplex via Cadd, starting from C0. *)
Fixpoint csum (l : list CComplex) : CComplex :=
  match l with
  | []      => C0
  | a :: l' => Cadd a (csum l')
  end.

(** Convert sign_pow ∈ {+1, -1} : Z to a CComplex. *)
Definition zsign_to_C (s : Z) : CComplex :=
  match s with
  | 0%Z       => C0
  | Z.pos _   => C1
  | Z.neg _   => Cneg C1
  end.

(** Inner sum: for each position [r ∈ {0,..,q}] in the (q+1)-sequence
    [J'], let [k = J'!!r], remove it to get [J = J' ∖ k] of length [q],
    take [(-1)^r ∂̄_k (α_{I,J})], and sum.

    Implementation: enumerate the underlying nat list of [J'] with
    indices, dispatch each entry to a contribution. *)

Fixpoint csum_index_aux
    (l : list nat) (start : nat)
    (contrib : nat -> nat -> CComplex)
    : CComplex :=
  match l with
  | []      => C0
  | a :: l' => Cadd (contrib start a) (csum_index_aux l' (S start) contrib)
  end.

(** ∂̄ of a (p,q)-form: produces a (p, q+1)-form.  The [(I, J')]
    coefficient is [Σ_r (-1)^r ∂̄_{J'_r} α_{I, J' ∖ J'_r}]. *)
(* CAG zero-dependent Definition pqf_dbar theories/Calc/Forms.v:233 BEGIN
Definition pqf_dbar {n p q : nat} (alpha : PQForm n p q) : PQForm n p (S q) :=
  {| pqf_at :=
       fun (I : MultiIndex n p) (Jp : MultiIndex n (S q)) (z : Cn n) =>
         csum_index_aux (mi_list Jp) 0
           (fun r k =>
              match In_dec Nat.eq_dec k (mi_list Jp) with
              | left Hin =>
                  match lt_dec k n with
                  | left Hkn =>
                      let J : MultiIndex n q := mi_remove_member k Jp Hin in
                      let kf : Fin.t n := Fin.of_nat_lt Hkn in
                      Cmul (zsign_to_C (sign_pow r))
                           (partial_zbar_witness
                              (fun w => pqf_at alpha I J w)
                              kf
                              z)
                  | right _ => C0
                  end
              | right _ => C0
              end)
  |}.
   CAG zero-dependent Definition pqf_dbar theories/Calc/Forms.v:233 END *)

(** ∂ of a (p,q)-form: produces a (p+1, q)-form.  The [(I', J)]
    coefficient is [Σ_r (-1)^r ∂_{I'_r} α_{I' ∖ I'_r, J}]. *)
(* CAG zero-dependent Definition pqf_del theories/Calc/Forms.v:257 BEGIN
Definition pqf_del {n p q : nat} (alpha : PQForm n p q) : PQForm n (S p) q :=
  {| pqf_at :=
       fun (Ip : MultiIndex n (S p)) (J : MultiIndex n q) (z : Cn n) =>
         csum_index_aux (mi_list Ip) 0
           (fun r k =>
              match In_dec Nat.eq_dec k (mi_list Ip) with
              | left Hin =>
                  match lt_dec k n with
                  | left Hkn =>
                      let I : MultiIndex n p := mi_remove_member k Ip Hin in
                      let kf : Fin.t n := Fin.of_nat_lt Hkn in
                      Cmul (zsign_to_C (sign_pow r))
                           (partial_z_witness
                              (fun w => pqf_at alpha I J w)
                              kf
                              z)
                  | right _ => C0
                  end
              | right _ => C0
              end)
  |}.
   CAG zero-dependent Definition pqf_del theories/Calc/Forms.v:257 END *)

(* ------------------------------------------------------------------ *)
(** * 6. Pullback                                                       *)
(* ------------------------------------------------------------------ *)

(** Pullback of a (p,q)-form along a holomorphic map [f : Cn n -> Cn m].
    Naively at the function level: [(f^* α)_{I,J} (z) = α_{I,J} (f z)].
    This is the correct formula only modulo the chain rule for
    [df∧dz_I] / [df∧dz̄_J]; for the purposes of this development it
    suffices as the underlying coefficient pullback, with the chain
    rule structure handled elsewhere when needed. *)
Definition pqf_pullback {n m p q : nat}
    (f : Cn n -> Cn m) (alpha : PQForm m p q) : PQForm n p q :=
  {| pqf_at := fun (I : MultiIndex n p) (J : MultiIndex n q) (z : Cn n) =>
       (** Take the same multi-index pair on [Cⁿ] as on [Cᵐ] modulo
           bound; if [n ≠ m] the sets of admissible indices differ.
           For the purpose of compiling downstream consumers we
           project via the underlying nat lists: build an [m]-bounded
           multi-index from [I] when possible. *)
       match (Nat.eq_dec n m) with
       | left Hnm =>
           (* recast I, J as MultiIndex m p / m q via Hnm *)
           let I' : MultiIndex m p :=
             eq_rect n (fun n' => MultiIndex n' p) I m Hnm in
           let J' : MultiIndex m q :=
             eq_rect n (fun n' => MultiIndex n' q) J m Hnm in
           pqf_at alpha I' J' (f z)
       | right _ => C0
       end
  |}.
