(** * LinAlg/QField.v
    The rationals Qc (canonical rationals from Stdlib.Qcanon) packaged
    as a [Field Qc] instance.

    Used by ExtractSL2 to specialize Mat2 / SL2 to a concrete numeric
    field for OCaml extraction. Qc has Leibniz equality (unlike Q),
    making it directly compatible with the project's [Field] record. *)

From CAG Require Import Galois.Field.
From Stdlib Require Import QArith Qcanon.

(** [Qc] commutative-ring instance. *)
Definition Qc_CommRing : CommRing Qc.
Proof.
  refine (Build_CommRing Qc 0%Qc 1%Qc Qcplus Qcmult Qcopp _ _ _ _ _ _ _ _).
  - intros. apply Qcplus_assoc.
  - intros. apply Qcplus_comm.
  - intros. apply Qcplus_0_r.
  - intros. apply Qcplus_opp_r.
  - intros. apply Qcmult_assoc.
  - intros. apply Qcmult_comm.
  - intros. apply Qcmult_1_r.
  - intros. apply Qcmult_plus_distr_r.
Defined.

(** [Qc] field instance. *)
Definition Qc_Field : Field Qc.
Proof.
  refine (Build_Field Qc Qc_CommRing _ Qcinv _).
  - (* 0 ≠ 1 *) discriminate.
  - (* a ≠ 0 → a · a^-1 = 1 *)
    intros a Ha. simpl. apply Qcmult_inv_r. exact Ha.
Defined.
