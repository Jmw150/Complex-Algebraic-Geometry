
type nat =
| O
| S of nat

val snd : ('a1 * 'a2) -> 'a2

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

val add : nat -> nat -> nat

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

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison
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

  val size_nat : positive -> nat

  val ggcdn : nat -> positive -> positive -> positive * (positive * positive)

  val ggcd : positive -> positive -> positive * (positive * positive)
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val max : z -> z -> z

  val to_pos : z -> positive

  val sgn : z -> z

  val abs : z -> z

  val ggcd : z -> z -> z * (z * z)
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

type q = { qnum : z; qden : positive }

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qred : q -> q

val qabs : q -> q

val pos_log2floor_plus1 : positive -> positive

val qbound_lt_ZExp2 : q -> z

val qbound_ltabs_ZExp2 : q -> z

type cReal = { seq : (z -> q); scale : z }

val inject_Q : q -> cReal

val cReal_plus_seq : cReal -> cReal -> z -> q

val cReal_plus_scale : cReal -> cReal -> z

val cReal_plus : cReal -> cReal -> cReal

val cReal_opp_seq : cReal -> z -> q

val cReal_opp_scale : cReal -> z

val cReal_opp : cReal -> cReal

val cReal_minus : cReal -> cReal -> cReal

val cReal_mult_seq : cReal -> cReal -> z -> q

val cReal_mult_scale : cReal -> cReal -> z

val cReal_mult : cReal -> cReal -> cReal

val pow : cReal -> nat -> cReal

val approx : cReal -> z -> q

val q_as_Zpair : q -> z * z

type cComplex = { re : cReal; im : cReal }

val c0 : cComplex

val c1 : cComplex

val cinject_Q : q -> cComplex

val cadd : cComplex -> cComplex -> cComplex

val cmul : cComplex -> cComplex -> cComplex

val cpow : cComplex -> nat -> cComplex

val capprox : cComplex -> z -> q * q

type cComplexlist = cComplex list

val repeat : cComplex -> nat -> cComplexlist

val length : cComplexlist -> nat

val app0 : cComplexlist -> cComplexlist -> cComplexlist

val filter : (cComplex -> bool) -> cComplexlist -> cComplexlist

val counter : (cComplex -> bool) -> cComplexlist -> cComplex

val add0 : cComplex -> cComplexlist -> cComplexlist

val rev : cComplexlist -> cComplexlist

val vzero : nat -> cComplex list

val vadd : cComplex list -> cComplex list -> cComplex list

val vscale : cComplex -> cComplex list -> cComplex list

type 'a mat = 'a list list

val dot : cComplex list -> cComplex list -> cComplex

val madd : cComplex mat -> cComplex mat -> cComplex mat

val nth_default : cComplex -> cComplex list -> nat -> cComplex

val col : cComplex mat -> nat -> cComplex list

val mcols : nat -> cComplex mat -> cComplex list list

val row_mul_cols : cComplex list -> cComplex list list -> cComplex list

val mmul : cComplex mat -> cComplex mat -> nat -> cComplex mat

val trace_aux : cComplex list list -> nat -> cComplex

val trace : cComplex list list -> cComplex

val two_plus_i : cComplex

val p : cComplex -> cComplex

val z0 : cComplex

val fr : cReal -> cReal

val gr : cReal -> cReal

val one_third : cReal

val run_f : z -> z * z

val run_g : z -> z * z

val run_p : z -> q * q
