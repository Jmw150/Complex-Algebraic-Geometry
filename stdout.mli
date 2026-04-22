
type nat =
| O
| S of nat

val snd : ('a1 * 'a2) -> 'a2



module Nat :
 sig
  val sub : nat -> nat -> nat

  val divmod : nat -> nat -> nat -> nat -> nat * nat

  val modulo : nat -> nat -> nat
 end

val seq : nat -> nat -> nat list

val nth : nat -> 'a1 list -> 'a1 -> 'a1

val firstn : nat -> 'a1 list -> 'a1 list

val combine : 'a1 list -> 'a2 list -> ('a1 * 'a2) list
