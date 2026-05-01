
val snd : ('a1 * 'a2) -> 'a2

type comparison =
| Eq
| Lt
| Gt

val add : int -> int -> int

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val mul : positive -> positive -> positive
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val sub : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val size_nat : positive -> int

  val ggcdn : int -> positive -> positive -> positive * (positive * positive)

  val ggcd : positive -> positive -> positive * (positive * positive)

  val eq_dec : positive -> positive -> bool
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val mul : z -> z -> z

  val to_pos : z -> positive

  val sgn : z -> z

  val abs : z -> z

  val ggcd : z -> z -> z * (z * z)

  val eq_dec : z -> z -> bool
 end

type 'r commRing = { cr_zero : 'r; cr_one : 'r; cr_add : ('r -> 'r -> 'r);
                     cr_mul : ('r -> 'r -> 'r); cr_neg : ('r -> 'r) }

val cr_sub : 'a1 commRing -> 'a1 -> 'a1 -> 'a1

type 'f field = { fld_ring : 'f commRing; fld_inv : ('f -> 'f) }

type 'f mat2 = (('f * 'f) * 'f) * 'f

val mat2_mk : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 mat2

val mat2_id : 'a1 field -> 'a1 mat2

val mat2_zero : 'a1 field -> 'a1 mat2

val mat2_mul : 'a1 field -> 'a1 mat2 -> 'a1 mat2 -> 'a1 mat2

val mat2_add : 'a1 field -> 'a1 mat2 -> 'a1 mat2 -> 'a1 mat2

val mat2_neg : 'a1 field -> 'a1 mat2 -> 'a1 mat2

val mat2_scale : 'a1 field -> 'a1 -> 'a1 mat2 -> 'a1 mat2

val mat2_det : 'a1 field -> 'a1 mat2 -> 'a1

val mat2_trace : 'a1 field -> 'a1 mat2 -> 'a1

val mat2_adj : 'a1 field -> 'a1 mat2 -> 'a1 mat2

type q = { qnum : z; qden : positive }

val qeq_dec : q -> q -> bool

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qinv : q -> q

val qred : q -> q

type qc = q
  (* singleton inductive, whose constructor was Qcmake *)

val q2Qc : q -> qc

val qc_eq_dec : qc -> qc -> bool

val qcplus : qc -> qc -> qc

val qcmult : qc -> qc -> qc

val qcopp : qc -> qc

val qcminus : qc -> qc -> qc

val qcinv : qc -> qc

val qc_CommRing : qc commRing

val qc_Field : qc field

type mat2_Qc = qc mat2

val mat2_mk_Qc : qc -> qc -> qc -> qc -> mat2_Qc

val mat2_id_Qc : mat2_Qc

val mat2_zero_Qc : mat2_Qc

val mat2_mul_Qc : mat2_Qc -> mat2_Qc -> mat2_Qc

val mat2_add_Qc : mat2_Qc -> mat2_Qc -> mat2_Qc

val mat2_neg_Qc : mat2_Qc -> mat2_Qc

val mat2_scale_Qc : qc -> mat2_Qc -> mat2_Qc

val mat2_det_Qc : mat2_Qc -> qc

val mat2_trace_Qc : mat2_Qc -> qc

val mat2_adj_Qc : mat2_Qc -> mat2_Qc

val mat2_pow_Qc : mat2_Qc -> int -> mat2_Qc

val is_in_SL2_Qc : mat2_Qc -> bool

val sL2_inv_Qc : mat2_Qc -> mat2_Qc

val trace_pow_chebyshev : qc -> int -> qc
