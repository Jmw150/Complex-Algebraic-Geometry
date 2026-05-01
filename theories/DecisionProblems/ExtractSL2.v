(** * DecisionProblems/ExtractSL2.v

    Coq → OCaml extraction of SL(2, Qc) operations.

    Addresses [E2] from the McReynolds-roadmap todos.

    Provides Mat2 and SL2 specialized to the canonical rationals Qc,
    extracted to OCaml so users can compute concrete SL(2, Q) matrix
    products and traces. *)

From CAG Require Import LinAlg.Matrix2 LinAlg.SL2 LinAlg.SL2Fricke
                       LinAlg.QField.
From Stdlib Require Import QArith Qcanon Extraction ExtrOcamlBasic
                          ExtrOcamlNatInt.

Definition mat2_Qc : Type := Mat2 Qc.

Definition mat2_mk_Qc (a b c d : Qc) : mat2_Qc := mat2_mk a b c d.
Definition mat2_id_Qc : mat2_Qc := mat2_id Qc_Field.
Definition mat2_zero_Qc : mat2_Qc := mat2_zero Qc_Field.
Definition mat2_mul_Qc : mat2_Qc -> mat2_Qc -> mat2_Qc := mat2_mul Qc_Field.
Definition mat2_add_Qc : mat2_Qc -> mat2_Qc -> mat2_Qc := mat2_add Qc_Field.
Definition mat2_neg_Qc : mat2_Qc -> mat2_Qc := mat2_neg Qc_Field.
Definition mat2_scale_Qc : Qc -> mat2_Qc -> mat2_Qc := mat2_scale Qc_Field.
Definition mat2_det_Qc : mat2_Qc -> Qc := mat2_det Qc_Field.
Definition mat2_trace_Qc : mat2_Qc -> Qc := mat2_trace Qc_Field.
Definition mat2_adj_Qc : mat2_Qc -> mat2_Qc := mat2_adj Qc_Field.

(** Power of a matrix. *)
Fixpoint mat2_pow_Qc (M : mat2_Qc) (n : nat) : mat2_Qc :=
  match n with
  | O => mat2_id_Qc
  | S k => mat2_mul_Qc M (mat2_pow_Qc M k)
  end.

(** SL(2, Qc) sigma type and ops, sidestepping proof_irrelevance for
    the OCaml side: we just expose the underlying Mat2 ops. The
    "is_in_SL2" check is just det = 1. *)
Definition is_in_SL2_Qc (M : mat2_Qc) : bool :=
  match Qc_eq_dec (mat2_det_Qc M) 1%Qc with
  | left _ => true
  | right _ => false
  end.

(** Inverse for SL2 (det=1) matrices: just the adjugate. *)
Definition SL2_inv_Qc (M : mat2_Qc) : mat2_Qc := mat2_adj_Qc M.

(** Trace of a power (Chebyshev): tr(M^{n+2}) = tr(M)·tr(M^{n+1}) - tr(M^n). *)
Fixpoint trace_pow_chebyshev (t : Qc) (n : nat) : Qc :=
  match n with
  | O => Qcplus 1%Qc 1%Qc     (* tr(I) = 2 *)
  | S O => t                  (* tr(M) *)
  | S (S k as k') =>
      Qcminus
        (Qcmult t (trace_pow_chebyshev t k'))
        (trace_pow_chebyshev t k)
  end.

Set Extraction Output Directory "lib".

Extraction "sl2_ml.ml"
  mat2_mk_Qc mat2_id_Qc mat2_zero_Qc
  mat2_mul_Qc mat2_add_Qc mat2_neg_Qc mat2_scale_Qc
  mat2_det_Qc mat2_trace_Qc mat2_adj_Qc
  mat2_pow_Qc
  is_in_SL2_Qc SL2_inv_Qc
  trace_pow_chebyshev.
