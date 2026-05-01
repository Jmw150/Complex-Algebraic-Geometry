
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



val eqb : int -> int -> bool

val iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1

val bool_dec : bool -> bool -> bool

val eqb0 : bool -> bool -> bool

module Nat :
 sig
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val removelast : 'a1 list -> 'a1 list

val rev : 'a1 list -> 'a1 list

val list_eq_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

val existsb : ('a1 -> bool) -> 'a1 list -> bool

type t =
| F1 of int
| FS of int * t

val to_nat : int -> t -> int

val eqb1 : int -> int -> t -> t -> bool

val eq_dec : int -> t -> t -> bool

type letter = t * bool

val letter_inv : int -> letter -> letter

val letter_eq_dec : int -> letter -> letter -> bool

type word = letter list

val cancel_step : int -> word -> word option

val reduce_aux : int -> int -> word -> word

val reduce : int -> word -> word

val free_mul : int -> word -> word -> word

val free_inv : int -> word -> word

val word_eq : int -> word -> word -> bool

val fin2_of_bool : bool -> t

val f2_a : letter

val f2_b : letter

val f2_A : letter

val f2_B : letter

val reduce_F2 : word -> word

val free_mul_F2 : word -> word -> word

val free_inv_F2 : word -> word

val word_eq_F2 : word -> word -> bool

val conjugate_F2 : word -> word -> word

val rotate_left : 'a1 list -> 'a1 list

val all_rotations_aux : int -> 'a1 list -> 'a1 list list

val all_rotations : 'a1 list -> 'a1 list list

val cyclic_reduce_step : word -> word option

val cyclic_reduce_aux : int -> word -> word

val cyclic_reduce_F2 : word -> word

val word_eq_list_F2 : word list -> word -> bool

val are_conjugate_F2_dec : word -> word -> bool

val gamma_pow_F2_word : word -> int -> word

val reduce_poly : int -> word -> word

val free_mul_poly : int -> word -> word -> word

val free_inv_poly : int -> word -> word

val word_eq_poly : int -> word -> word -> bool
