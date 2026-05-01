
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Stdlib.Int.succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



(** val eqb : int -> int -> bool **)

let rec eqb n m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun _ -> false)
      m)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> false)
      (fun m' -> eqb n' m')
      m)
    n

(** val iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec iter n f x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> x)
    (fun n0 -> f (iter n0 f x))
    n

(** val bool_dec : bool -> bool -> bool **)

let bool_dec b1 b2 =
  if b1 then if b2 then true else false else if b2 then false else true

(** val eqb0 : bool -> bool -> bool **)

let eqb0 b1 b2 =
  if b1 then b2 else if b2 then false else true

module Nat =
 struct
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: l0 -> (f a) :: (map f l0)

(** val removelast : 'a1 list -> 'a1 list **)

let rec removelast = function
| [] -> []
| a :: l' -> (match l' with
              | [] -> []
              | _ :: _ -> a :: (removelast l'))

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x :: l' -> app (rev l') (x :: [])

(** val list_eq_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec list_eq_dec eq_dec0 l l' =
  match l with
  | [] -> (match l' with
           | [] -> true
           | _ :: _ -> false)
  | y :: l0 ->
    (match l' with
     | [] -> false
     | a :: l1 -> if eq_dec0 y a then list_eq_dec eq_dec0 l0 l1 else false)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a :: l0 -> (||) (f a) (existsb f l0)

type t =
| F1 of int
| FS of int * t

(** val to_nat : int -> t -> int **)

let rec to_nat _ = function
| F1 _ -> 0
| FS (n0, p) -> Stdlib.Int.succ (to_nat n0 p)

(** val eqb1 : int -> int -> t -> t -> bool **)

let rec eqb1 _ _ p q =
  match p with
  | F1 m' -> (match q with
              | F1 n' -> (=) m' n'
              | FS (_, _) -> false)
  | FS (n0, p') ->
    (match q with
     | F1 _ -> false
     | FS (n1, q') -> eqb1 n0 n1 p' q')

(** val eq_dec : int -> t -> t -> bool **)

let eq_dec n x y =
  if eqb1 n n x y then true else false

type letter = t * bool

(** val letter_inv : int -> letter -> letter **)

let letter_inv _ l =
  ((fst l), (negb (snd l)))

(** val letter_eq_dec : int -> letter -> letter -> bool **)

let letter_eq_dec n x y =
  let (t0, b) = x in
  let (t1, b0) = y in
  let s = eq_dec n t0 t1 in if s then bool_dec b b0 else false

type word = letter list

(** val cancel_step : int -> word -> word option **)

let rec cancel_step n = function
| [] -> None
| x :: tail ->
  (match tail with
   | [] -> None
   | y :: rest ->
     if letter_eq_dec n y (letter_inv n x)
     then Some rest
     else (match cancel_step n tail with
           | Some w' -> Some (x :: w')
           | None -> None))

(** val reduce_aux : int -> int -> word -> word **)

let rec reduce_aux n fuel w =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> w)
    (fun k ->
    match cancel_step n w with
    | Some w' -> reduce_aux n k w'
    | None -> w)
    fuel

(** val reduce : int -> word -> word **)

let reduce n w =
  reduce_aux n (length w) w

(** val free_mul : int -> word -> word -> word **)

let free_mul n u v =
  reduce n (app u v)

(** val free_inv : int -> word -> word **)

let free_inv n w =
  map (letter_inv n) (rev w)

(** val word_eq : int -> word -> word -> bool **)

let word_eq n u v =
  if list_eq_dec (letter_eq_dec n) (reduce n u) (reduce n v)
  then true
  else false

(** val fin2_of_bool : bool -> t **)

let fin2_of_bool = function
| true -> F1 (Stdlib.Int.succ 0)
| false -> FS ((Stdlib.Int.succ 0), (F1 0))

(** val f2_a : letter **)

let f2_a =
  ((F1 (Stdlib.Int.succ 0)), false)

(** val f2_b : letter **)

let f2_b =
  ((FS ((Stdlib.Int.succ 0), (F1 0))), false)

(** val f2_A : letter **)

let f2_A =
  letter_inv (Stdlib.Int.succ (Stdlib.Int.succ 0)) f2_a

(** val f2_B : letter **)

let f2_B =
  letter_inv (Stdlib.Int.succ (Stdlib.Int.succ 0)) f2_b

(** val reduce_F2 : word -> word **)

let reduce_F2 =
  reduce (Stdlib.Int.succ (Stdlib.Int.succ 0))

(** val free_mul_F2 : word -> word -> word **)

let free_mul_F2 =
  free_mul (Stdlib.Int.succ (Stdlib.Int.succ 0))

(** val free_inv_F2 : word -> word **)

let free_inv_F2 =
  free_inv (Stdlib.Int.succ (Stdlib.Int.succ 0))

(** val word_eq_F2 : word -> word -> bool **)

let word_eq_F2 =
  word_eq (Stdlib.Int.succ (Stdlib.Int.succ 0))

(** val conjugate_F2 : word -> word -> word **)

let conjugate_F2 g w =
  free_mul_F2 (free_mul_F2 g w) (free_inv_F2 g)

(** val rotate_left : 'a1 list -> 'a1 list **)

let rec rotate_left = function
| [] -> []
| x :: rest -> app rest (x :: [])

(** val all_rotations_aux : int -> 'a1 list -> 'a1 list list **)

let rec all_rotations_aux k w =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun k' -> w :: (all_rotations_aux k' (rotate_left w)))
    k

(** val all_rotations : 'a1 list -> 'a1 list list **)

let all_rotations w =
  all_rotations_aux (length w) w

(** val cyclic_reduce_step : word -> word option **)

let cyclic_reduce_step = function
| [] -> None
| l :: rest ->
  (match rev rest with
   | [] -> None
   | l' :: _ ->
     if (&&)
          (eqb (to_nat (Stdlib.Int.succ (Stdlib.Int.succ 0)) (fst l))
            (to_nat (Stdlib.Int.succ (Stdlib.Int.succ 0)) (fst l')))
          (eqb0 (snd l) (negb (snd l')))
     then Some (removelast rest)
     else None)

(** val cyclic_reduce_aux : int -> word -> word **)

let rec cyclic_reduce_aux fuel w =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> w)
    (fun fuel' ->
    match cyclic_reduce_step w with
    | Some w' -> cyclic_reduce_aux fuel' w'
    | None -> w)
    fuel

(** val cyclic_reduce_F2 : word -> word **)

let cyclic_reduce_F2 w =
  cyclic_reduce_aux (length w) (reduce_F2 w)

(** val word_eq_list_F2 : word list -> word -> bool **)

let word_eq_list_F2 ws target =
  existsb (word_eq_F2 target) ws

(** val are_conjugate_F2_dec : word -> word -> bool **)

let are_conjugate_F2_dec u v =
  let cu = cyclic_reduce_F2 u in
  let cv = cyclic_reduce_F2 v in word_eq_list_F2 (all_rotations cu) cv

(** val gamma_pow_F2_word : word -> int -> word **)

let gamma_pow_F2_word gamma i =
  iter i (free_mul_F2 gamma) []

(** val reduce_poly : int -> word -> word **)

let reduce_poly =
  reduce

(** val free_mul_poly : int -> word -> word -> word **)

let free_mul_poly =
  free_mul

(** val free_inv_poly : int -> word -> word **)

let free_inv_poly =
  free_inv

(** val word_eq_poly : int -> word -> word -> bool **)

let word_eq_poly =
  word_eq
