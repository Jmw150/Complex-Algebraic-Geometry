
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
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z
 end

type 'g group = { mul : ('g -> 'g -> 'g); e : 'g }

type 'g commutativeGroup =
  'g group
  (* singleton inductive, whose constructor was mkCG *)

module Playground :
 sig
  val coq_GZ_add : z group

  val coq_Z_abel : z commutativeGroup
 end
