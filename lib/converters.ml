

(** A file for converting common types from rocq 

if such types are not extracted as zarith, int, etc...    
*)
open Base
open Complexrocq
(*
type nat =
| O
| S of nat

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)

 let rec add n m =
   match n with
   | O -> m
   | S p0 -> S (add p0 m)
end
include Coq__1

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p0 -> XO (succ p0)
  | XO p0 -> XI p0
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p0 ->
      (match y with
       | XI q0 -> XO (add_carry p0 q0)
       | XO q0 -> XI (add p0 q0)
       | XH -> XO (succ p0))
    | XO p0 ->
      (match y with
       | XI q0 -> XI (add p0 q0)
       | XO q0 -> XO (add p0 q0)
       | XH -> XI p0)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p0 ->
      (match y with
       | XI q0 -> XI (add_carry p0 q0)
       | XO q0 -> XO (add_carry p0 q0)
       | XH -> XI (succ p0))
    | XO p0 ->
      (match y with
       | XI q0 -> XO (add_carry p0 q0)
       | XO q0 -> XI (add p0 q0)
       | XH -> XO (succ p0))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p0 -> XI (XO p0)
  | XO p0 -> XI (pred_double p0)
  | XH -> XH

  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p0 -> add y (XO (mul p0 y))
    | XO p0 -> XO (mul p0 y)
    | XH -> y

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p0 ->
      (match y with
       | XI q0 -> compare_cont r p0 q0
       | XO q0 -> compare_cont Gt p0 q0
       | XH -> Gt)
    | XO p0 ->
      (match y with
       | XI q0 -> compare_cont Lt p0 q0
       | XO q0 -> compare_cont r p0 q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p0 -> XO (succ p0)
  | XO p0 -> XI p0
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p0 ->
      (match y with
       | XI q0 -> XO (add_carry p0 q0)
       | XO q0 -> XI (add p0 q0)
       | XH -> XO (succ p0))
    | XO p0 ->
      (match y with
       | XI q0 -> XI (add p0 q0)
       | XO q0 -> XO (add p0 q0)
       | XH -> XI p0)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p0 ->
      (match y with
       | XI q0 -> XI (add_carry p0 q0)
       | XO q0 -> XO (add_carry p0 q0)
       | XH -> XI (succ p0))
    | XO p0 ->
      (match y with
       | XI q0 -> XO (add_carry p0 q0)
       | XO q0 -> XI (add p0 q0)
       | XH -> XO (succ p0))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p0 -> XI (XO p0)
  | XO p0 -> XI (pred_double p0)
  | XH -> XH

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p0 -> IsPos (XI p0)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p0 -> IsPos (XO p0)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p0 -> IsPos (XO (XO p0))
  | XO p0 -> IsPos (XO (pred_double p0))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p0 ->
      (match y with
       | XI q0 -> double_mask (sub_mask p0 q0)
       | XO q0 -> succ_double_mask (sub_mask p0 q0)
       | XH -> IsPos (XO p0))
    | XO p0 ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p0 q0)
       | XO q0 -> double_mask (sub_mask p0 q0)
       | XH -> IsPos (pred_double p0))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p0 ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p0 q0)
       | XO q0 -> double_mask (sub_mask p0 q0)
       | XH -> IsPos (pred_double p0))
    | XO p0 ->
      (match y with
       | XI q0 -> double_mask (sub_mask_carry p0 q0)
       | XO q0 -> succ_double_mask (sub_mask_carry p0 q0)
       | XH -> double_pred_mask p0)
    | XH -> IsNeg

  (** val sub : positive -> positive -> positive **)

  let sub x y =
    match sub_mask x y with
    | IsPos z1 -> z1
    | _ -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p0 -> add y (XO (mul p0 y))
    | XO p0 -> XO (mul p0 y)
    | XH -> y

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p0 ->
      (match y with
       | XI q0 -> compare_cont r p0 q0
       | XO q0 -> compare_cont Gt p0 q0
       | XH -> Gt)
    | XO p0 ->
      (match y with
       | XI q0 -> compare_cont Lt p0 q0
       | XO q0 -> compare_cont r p0 q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val size_nat : positive -> nat **)

  let rec size_nat = function
  | XI p1 -> S (size_nat p1)
  | XO p1 -> S (size_nat p1)
  | XH -> S O

  (** val ggcdn :
      nat -> positive -> positive -> positive * (positive * positive) **)

  let rec ggcdn n a b =
    match n with
    | O -> (XH, (a, b))
    | S n0 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | Eq -> (a, (XH, XH))
             | Lt ->
               let (g0, p0) = ggcdn n0 (sub b' a') a in
               let (ba, aa) = p0 in (g0, (aa, (add aa (XO ba))))
             | Gt ->
               let (g0, p0) = ggcdn n0 (sub a' b') b in
               let (ab, bb) = p0 in (g0, ((add bb (XO ab)), bb)))
          | XO b0 ->
            let (g0, p0) = ggcdn n0 a b0 in
            let (aa, bb) = p0 in (g0, (aa, (XO bb)))
          | XH -> (XH, (a, XH)))
       | XO a0 ->
         (match b with
          | XI _ ->
            let (g0, p0) = ggcdn n0 a0 b in
            let (aa, bb) = p0 in (g0, ((XO aa), bb))
          | XO b0 -> let (g0, p0) = ggcdn n0 a0 b0 in ((XO g0), p0)
          | XH -> (XH, (a, XH)))
       | XH -> (XH, (XH, b)))

  (** val ggcd : positive -> positive -> positive * (positive * positive) **)

  let ggcd a b =
    ggcdn (Coq__1.add (size_nat a) (size_nat b)) a b
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p0 -> Zpos (XO p0)
  | Zneg p0 -> Zneg (XO p0)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p0 -> Zpos (XI p0)
  | Zneg p0 -> Zneg (Pos.pred_double p0)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p0 -> Zpos (Pos.pred_double p0)
  | Zneg p0 -> Zneg (XI p0)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p0 ->
      (match y with
       | XI q0 -> double (pos_sub p0 q0)
       | XO q0 -> succ_double (pos_sub p0 q0)
       | XH -> Zpos (XO p0))
    | XO p0 ->
      (match y with
       | XI q0 -> pred_double (pos_sub p0 q0)
       | XO q0 -> double (pos_sub p0 q0)
       | XH -> Zpos (Pos.pred_double p0))
    | XH ->
      (match y with
       | XI q0 -> Zneg (XO q0)
       | XO q0 -> Zneg (Pos.pred_double q0)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m n =
    add m (opp n)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val max : z -> z -> z **)

  let max n m =
    match compare n m with
    | Lt -> m
    | _ -> n

  (** val to_pos : z -> positive **)

  let to_pos = function
  | Zpos p0 -> p0
  | _ -> XH

  (** val sgn : z -> z **)

  let sgn = function
  | Z0 -> Z0
  | Zpos _ -> Zpos XH
  | Zneg _ -> Zneg XH

  (** val abs : z -> z **)

  let abs = function
  | Zneg p0 -> Zpos p0
  | x -> x

  (** val ggcd : z -> z -> z * (z * z) **)

  let ggcd a b =
    match a with
    | Z0 -> ((abs b), (Z0, (sgn b)))
    | Zpos a0 ->
      (match b with
       | Z0 -> ((abs a), ((sgn a), Z0))
       | Zpos b0 ->
         let (g0, p0) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p0 in ((Zpos g0), ((Zpos aa), (Zpos bb)))
       | Zneg b0 ->
         let (g0, p0) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p0 in ((Zpos g0), ((Zpos aa), (Zneg bb))))
    | Zneg a0 ->
      (match b with
       | Z0 -> ((abs a), ((sgn a), Z0))
       | Zpos b0 ->
         let (g0, p0) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p0 in ((Zpos g0), ((Zneg aa), (Zpos bb)))
       | Zneg b0 ->
         let (g0, p0) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p0 in ((Zpos g0), ((Zneg aa), (Zneg bb))))
 end

type q = { qnum : z; qden : positive }

(** val qplus : q -> q -> q **)

let qplus x y =
  { qnum = (Z.add (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden)));
    qden = (Coq_Pos.mul x.qden y.qden) }

(** val qmult : q -> q -> q **)

let qmult x y =
  { qnum = (Z.mul x.qnum y.qnum); qden = (Coq_Pos.mul x.qden y.qden) }

(** val qopp : q -> q **)

let qopp x =
  { qnum = (Z.opp x.qnum); qden = x.qden }

(** val qred : q -> q **)

let qred q0 =
  let { qnum = q1; qden = q2 } = q0 in
  let (r1, r2) = snd (Z.ggcd q1 (Zpos q2)) in
  { qnum = r1; qden = (Z.to_pos r2) }

(** val qabs : q -> q **)

let qabs x =
  let { qnum = n; qden = d } = x in { qnum = (Z.abs n); qden = d }

(** val pos_log2floor_plus1 : positive -> positive **)

let rec pos_log2floor_plus1 = function
| XI p' -> Coq_Pos.succ (pos_log2floor_plus1 p')
| XO p' -> Coq_Pos.succ (pos_log2floor_plus1 p')
| XH -> XH

(** val qbound_lt_ZExp2 : q -> z **)

let qbound_lt_ZExp2 q0 =
  match q0.qnum with
  | Z0 -> Zneg (XO (XO (XO (XI (XO (XI (XI (XI (XI XH)))))))))
  | Zpos p0 ->
    Z.pos_sub (Coq_Pos.succ (pos_log2floor_plus1 p0))
      (pos_log2floor_plus1 q0.qden)
  | Zneg _ -> Z0

(** val qbound_ltabs_ZExp2 : q -> z **)

let qbound_ltabs_ZExp2 q0 =
  qbound_lt_ZExp2 (qabs q0)

*)
(** Want: converters to be of module types. *)

let rec nat_of_int n =
  if n <= 0 then O
   else S(nat_of_int (n - 1))

let rec int_of_nat = function
  | O -> 0
  | S n -> 1 + int_of_nat n

let rec pos_of_int n =
  if n <= 0 then invalid_arg "pos_of_int: n must be >= 1";
  if n = 1 then XH
  else let half = pos_of_int (n / 2) in 
    if (n land 1) = 0 then XO half
    else XI half

let rec int_of_pos = function
  | XH -> 1
  | XO p -> 2 * int_of_pos p
  | XI p -> 2 * int_of_pos p + 1

let z_of_int n =
  if n = 0 then Z0
  else if n > 0 then Zpos (pos_of_int n)
  else Zneg (pos_of_int (-n))

let int_of_z = function
  | Z0 -> 0
  | Zpos p -> int_of_pos p
  | Zneg p -> -(int_of_pos p)

(* too lazy to make this any int args *)
let q_of_ints a b = 
  if b <= 0 then invalid_arg "q_of_ints: denomiator must be >= 1";
  { qnum = z_of_int a; qden = pos_of_int b}

let ints_of_q q = 
  (int_of_z q.qnum, int_of_pos q.qden)

let c_of_ints a b = 
  { re = inject_Q (q_of_ints a 1) ; 
    im = inject_Q (q_of_ints b 1)}

let ints_of_c k z = 
  let z_ap = (capprox z (z_of_int k)) in
  let (r, i) = z_ap in
  let (num1, den1) = ints_of_q r in
  let (num2, den2) = ints_of_q i in 
  (num1, den1, num2, den2)


