
type nat =
| O
| S of nat

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

val sub : nat -> nat -> nat

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Nat :
 sig
  val sub : nat -> nat -> nat

  val divmod : nat -> nat -> nat -> nat -> nat * nat

  val modulo : nat -> nat -> nat
 end

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

  val of_nat : nat -> positive
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

val seq : nat -> nat -> nat list

val repeat : 'a1 -> nat -> 'a1 list

val nth : nat -> 'a1 list -> 'a1 -> 'a1

val firstn : nat -> 'a1 list -> 'a1 list

val combine : 'a1 list -> 'a2 list -> ('a1 * 'a2) list

type q = { qnum : z; qden : positive }

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qred : q -> q

val qabs : q -> q

val pos_log2floor_plus1 : positive -> positive

val qbound_lt_ZExp2 : q -> z

val qbound_ltabs_ZExp2 : q -> z

type cReal = { seq0 : (z -> q); scale : z }

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

val cReal_abs_seq : cReal -> z -> q

val cReal_abs_scale : cReal -> z

val cReal_abs : cReal -> cReal

val cReal_max : cReal -> cReal -> cReal

type cComplex = { re : cReal; im : cReal }

val c0 : cComplex

val c1 : cComplex

val cinject_Q : q -> cComplex

val cadd : cComplex -> cComplex -> cComplex

val cmul : cComplex -> cComplex -> cComplex

val cpow : cComplex -> nat -> cComplex

val exp_i : cReal -> cComplex

val pi_R : cReal

val omega : nat -> cComplex

val csum : nat -> (nat -> cComplex) -> cComplex

val nth_C : cComplex list -> nat -> cComplex

val dft_coeff : cComplex list -> nat -> cComplex

val dft : cComplex list -> cComplex list

val idft_coeff : cComplex list -> nat -> cComplex

val idft : cComplex list -> cComplex list

val cyclic_conv : cComplex list -> cComplex list -> cComplex list

val pointwise_mul : cComplex list -> cComplex list -> cComplex list

val truncate_modes : nat -> cComplex list -> cComplex list

val pad_to : nat -> cComplex list -> cComplex list

val low_pass : nat -> nat -> cComplex list -> cComplex list

val spectral_proj : nat -> cComplex list -> cComplex list

type nonlinearity = cComplex -> cComplex

val relu_C : nonlinearity

val apply_nonlin : nonlinearity -> cComplex list -> cComplex list

type fNOLayerParams = { fno_K_max : nat; fno_weights : cComplex list;
                        fno_skip : cComplex; fno_nonlin : nonlinearity }

val apply_weights : cComplex list -> cComplex list -> cComplex list

val spectral_conv : fNOLayerParams -> cComplex list -> cComplex list

val skip_connection : fNOLayerParams -> cComplex list -> cComplex list

val fno_layer : fNOLayerParams -> cComplex list -> cComplex list

type fNOParams = { fno_lift : cComplex; fno_proj : cComplex;
                   fno_layers : fNOLayerParams list }

val lift : cComplex -> cComplex list -> cComplex list

val apply_layers : fNOLayerParams list -> cComplex list -> cComplex list

val fno_forward : fNOParams -> cComplex list -> cComplex list

val circulant_op : cComplex list -> cComplex list -> cComplex list
