
type nat =
| O
| S of nat

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> nat **)

let rec length = function
| [] -> O
| _ :: l' -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

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
   | S p -> S (add p m)
end
include Coq__1

(** val mul : nat -> nat -> nat **)

let rec mul n m =
  match n with
  | O -> O
  | S p -> add m (mul p m)

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Nat =
 struct
  (** val sub : nat -> nat -> nat **)

  let rec sub n m =
    match n with
    | O -> n
    | S k -> (match m with
              | O -> n
              | S l -> sub k l)

  (** val divmod : nat -> nat -> nat -> nat -> nat * nat **)

  let rec divmod x y q0 u =
    match x with
    | O -> (q0, u)
    | S x' ->
      (match u with
       | O -> divmod x' y (S q0) y
       | S u' -> divmod x' y q0 u')

  (** val modulo : nat -> nat -> nat **)

  let modulo x = function
  | O -> x
  | S y' -> sub y' (snd (divmod x y' O y'))
 end

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XI (add p q0)
       | XO q0 -> XO (add p q0)
       | XH -> XI p)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> compare_cont r p q0
       | XO q0 -> compare_cont Gt p q0
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q0 -> compare_cont Lt p q0
       | XO q0 -> compare_cont r p q0
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
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XI (add p q0)
       | XO q0 -> XO (add p q0)
       | XH -> XI p)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double_mask (sub_mask p q0)
       | XO q0 -> succ_double_mask (sub_mask p q0)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q0 -> double_mask (sub_mask_carry p q0)
       | XO q0 -> succ_double_mask (sub_mask_carry p q0)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val sub : positive -> positive -> positive **)

  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> compare_cont r p q0
       | XO q0 -> compare_cont Gt p q0
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q0 -> compare_cont Lt p q0
       | XO q0 -> compare_cont r p q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val size_nat : positive -> nat **)

  let rec size_nat = function
  | XI p0 -> S (size_nat p0)
  | XO p0 -> S (size_nat p0)
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
               let (g, p) = ggcdn n0 (sub b' a') a in
               let (ba, aa) = p in (g, (aa, (add aa (XO ba))))
             | Gt ->
               let (g, p) = ggcdn n0 (sub a' b') b in
               let (ab, bb) = p in (g, ((add bb (XO ab)), bb)))
          | XO b0 ->
            let (g, p) = ggcdn n0 a b0 in
            let (aa, bb) = p in (g, (aa, (XO bb)))
          | XH -> (XH, (a, XH)))
       | XO a0 ->
         (match b with
          | XI _ ->
            let (g, p) = ggcdn n0 a0 b in
            let (aa, bb) = p in (g, ((XO aa), bb))
          | XO b0 -> let (g, p) = ggcdn n0 a0 b0 in ((XO g), p)
          | XH -> (XH, (a, XH)))
       | XH -> (XH, (XH, b)))

  (** val ggcd : positive -> positive -> positive * (positive * positive) **)

  let ggcd a b =
    ggcdn (Coq__1.add (size_nat a) (size_nat b)) a b

  (** val of_nat : nat -> positive **)

  let rec of_nat = function
  | O -> XH
  | S x -> (match x with
            | O -> XH
            | S _ -> succ (of_nat x))
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double (pos_sub p q0)
       | XO q0 -> succ_double (pos_sub p q0)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> pred_double (pos_sub p q0)
       | XO q0 -> double (pos_sub p q0)
       | XH -> Zpos (Pos.pred_double p))
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
  | Zpos p -> p
  | _ -> XH

  (** val sgn : z -> z **)

  let sgn = function
  | Z0 -> Z0
  | Zpos _ -> Zpos XH
  | Zneg _ -> Zneg XH

  (** val abs : z -> z **)

  let abs = function
  | Zneg p -> Zpos p
  | x -> x

  (** val ggcd : z -> z -> z * (z * z) **)

  let ggcd a b =
    match a with
    | Z0 -> ((abs b), (Z0, (sgn b)))
    | Zpos a0 ->
      (match b with
       | Z0 -> ((abs a), ((sgn a), Z0))
       | Zpos b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zpos aa), (Zpos bb)))
       | Zneg b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zpos aa), (Zneg bb))))
    | Zneg a0 ->
      (match b with
       | Z0 -> ((abs a), ((sgn a), Z0))
       | Zpos b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zneg aa), (Zpos bb)))
       | Zneg b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zneg aa), (Zneg bb))))
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: l0 -> (f a) :: (map f l0)

(** val seq : nat -> nat -> nat list **)

let rec seq start = function
| O -> []
| S len0 -> start :: (seq (S start) len0)

(** val repeat : 'a1 -> nat -> 'a1 list **)

let rec repeat x = function
| O -> []
| S k -> x :: (repeat x k)

(** val nth : nat -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n l default =
  match n with
  | O -> (match l with
          | [] -> default
          | x :: _ -> x)
  | S m -> (match l with
            | [] -> default
            | _ :: l' -> nth m l' default)

(** val firstn : nat -> 'a1 list -> 'a1 list **)

let rec firstn n l =
  match n with
  | O -> []
  | S n0 -> (match l with
             | [] -> []
             | a :: l0 -> a :: (firstn n0 l0))

(** val combine : 'a1 list -> 'a2 list -> ('a1 * 'a2) list **)

let rec combine l l' =
  match l with
  | [] -> []
  | x :: tl ->
    (match l' with
     | [] -> []
     | y :: tl' -> (x, y) :: (combine tl tl'))

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
  | Zpos p ->
    Z.pos_sub (Coq_Pos.succ (pos_log2floor_plus1 p))
      (pos_log2floor_plus1 q0.qden)
  | Zneg _ -> Z0

(** val qbound_ltabs_ZExp2 : q -> z **)

let qbound_ltabs_ZExp2 q0 =
  qbound_lt_ZExp2 (qabs q0)

type cReal = { seq0 : (z -> q); scale : z }

(** val inject_Q : q -> cReal **)

let inject_Q q0 =
  { seq0 = (fun _ -> q0); scale = (qbound_ltabs_ZExp2 q0) }

(** val cReal_plus_seq : cReal -> cReal -> z -> q **)

let cReal_plus_seq x y n =
  qred (qplus (x.seq0 (Z.sub n (Zpos XH))) (y.seq0 (Z.sub n (Zpos XH))))

(** val cReal_plus_scale : cReal -> cReal -> z **)

let cReal_plus_scale x y =
  Z.add (Z.max x.scale y.scale) (Zpos XH)

(** val cReal_plus : cReal -> cReal -> cReal **)

let cReal_plus x y =
  { seq0 = (cReal_plus_seq x y); scale = (cReal_plus_scale x y) }

(** val cReal_opp_seq : cReal -> z -> q **)

let cReal_opp_seq x n =
  qopp (x.seq0 n)

(** val cReal_opp_scale : cReal -> z **)

let cReal_opp_scale x =
  x.scale

(** val cReal_opp : cReal -> cReal **)

let cReal_opp x =
  { seq0 = (cReal_opp_seq x); scale = (cReal_opp_scale x) }

(** val cReal_minus : cReal -> cReal -> cReal **)

let cReal_minus x y =
  cReal_plus x (cReal_opp y)

(** val cReal_mult_seq : cReal -> cReal -> z -> q **)

let cReal_mult_seq x y n =
  qmult (x.seq0 (Z.sub (Z.sub n y.scale) (Zpos XH)))
    (y.seq0 (Z.sub (Z.sub n x.scale) (Zpos XH)))

(** val cReal_mult_scale : cReal -> cReal -> z **)

let cReal_mult_scale x y =
  Z.add x.scale y.scale

(** val cReal_mult : cReal -> cReal -> cReal **)

let cReal_mult x y =
  { seq0 = (cReal_mult_seq x y); scale = (cReal_mult_scale x y) }

(** val cReal_abs_seq : cReal -> z -> q **)

let cReal_abs_seq x n =
  qabs (x.seq0 n)

(** val cReal_abs_scale : cReal -> z **)

let cReal_abs_scale x =
  x.scale

(** val cReal_abs : cReal -> cReal **)

let cReal_abs x =
  { seq0 = (cReal_abs_seq x); scale = (cReal_abs_scale x) }

(** val cReal_max : cReal -> cReal -> cReal **)

let cReal_max x y =
  cReal_mult (cReal_plus (cReal_plus x y) (cReal_abs (cReal_minus y x)))
    (inject_Q { qnum = (Zpos XH); qden = (XO XH) })

type cComplex = { re : cReal; im : cReal }

(** val c0 : cComplex **)

let c0 =
  { re = (inject_Q { qnum = Z0; qden = XH }); im =
    (inject_Q { qnum = Z0; qden = XH }) }

(** val c1 : cComplex **)

let c1 =
  { re = (inject_Q { qnum = (Zpos XH); qden = XH }); im =
    (inject_Q { qnum = Z0; qden = XH }) }

(** val cinject_Q : q -> cComplex **)

let cinject_Q q0 =
  { re = (inject_Q q0); im = (inject_Q { qnum = Z0; qden = XH }) }

(** val cadd : cComplex -> cComplex -> cComplex **)

let cadd z0 w =
  { re = (cReal_plus z0.re w.re); im = (cReal_plus z0.im w.im) }

(** val cmul : cComplex -> cComplex -> cComplex **)

let cmul z0 w =
  { re = (cReal_minus (cReal_mult z0.re w.re) (cReal_mult z0.im w.im)); im =
    (cReal_plus (cReal_mult z0.re w.im) (cReal_mult z0.im w.re)) }

(** val cpow : cComplex -> nat -> cComplex **)

let rec cpow z0 = function
| O -> c1
| S n' -> cmul z0 (cpow z0 n')

(** val exp_i : cReal -> cComplex **)

let exp_i = Fno_impl.exp_i_impl

(** val pi_R : cReal **)

let pi_R = Fno_impl.pi_r_impl

(** val omega : nat -> cComplex **)

let omega n =
  exp_i
    (cReal_opp
      (cReal_mult
        (cReal_mult (inject_Q { qnum = (Zpos (XO XH)); qden = XH }) pi_R)
        (inject_Q { qnum = (Zpos XH); qden = (Coq_Pos.of_nat n) })))

(** val csum : nat -> (nat -> cComplex) -> cComplex **)

let rec csum n f =
  match n with
  | O -> c0
  | S n0 -> cadd (csum n0 f) (f n0)

(** val nth_C : cComplex list -> nat -> cComplex **)

let nth_C xs n =
  nth n xs c0

(** val dft_coeff : cComplex list -> nat -> cComplex **)

let dft_coeff xs k =
  let n = length xs in
  csum n (fun n0 -> cmul (nth_C xs n0) (cpow (omega n) (mul n0 k)))

(** val dft : cComplex list -> cComplex list **)

let dft xs =
  map (dft_coeff xs) (seq O (length xs))

(** val idft_coeff : cComplex list -> nat -> cComplex **)

let idft_coeff xs n =
  let n0 = length xs in
  let inv_N = cinject_Q { qnum = (Zpos XH); qden = (Coq_Pos.of_nat n0) } in
  cmul inv_N
    (csum n0 (fun k ->
      cmul (nth_C xs k) (cpow (omega n0) (sub (mul n0 k) (mul n k)))))

(** val idft : cComplex list -> cComplex list **)

let idft xs =
  map (idft_coeff xs) (seq O (length xs))

(** val cyclic_conv : cComplex list -> cComplex list -> cComplex list **)

let cyclic_conv xs ys =
  let n = length xs in
  map (fun n0 ->
    csum n (fun m ->
      cmul (nth_C xs m)
        (nth_C ys (Nat.modulo (sub (add n0 n) (Nat.modulo m n)) n))))
    (seq O n)

(** val pointwise_mul : cComplex list -> cComplex list -> cComplex list **)

let pointwise_mul xs ys =
  map (fun pat -> let (x, y) = pat in cmul x y) (combine xs ys)

(** val truncate_modes : nat -> cComplex list -> cComplex list **)

let truncate_modes =
  firstn

(** val pad_to : nat -> cComplex list -> cComplex list **)

let pad_to n xs =
  app xs (repeat c0 (sub n (length xs)))

(** val low_pass : nat -> nat -> cComplex list -> cComplex list **)

let low_pass n k_max xs =
  pad_to n (truncate_modes k_max xs)

(** val spectral_proj : nat -> cComplex list -> cComplex list **)

let spectral_proj k_max xs =
  idft (low_pass (length xs) k_max (dft xs))

type nonlinearity = cComplex -> cComplex

(** val relu_C : nonlinearity **)

let relu_C z0 =
  { re = (cReal_max z0.re (inject_Q { qnum = Z0; qden = XH })); im = z0.im }

(** val apply_nonlin : nonlinearity -> cComplex list -> cComplex list **)

let apply_nonlin =
  map

type fNOLayerParams = { fno_K_max : nat; fno_weights : cComplex list;
                        fno_skip : cComplex; fno_nonlin : nonlinearity }

(** val apply_weights : cComplex list -> cComplex list -> cComplex list **)

let apply_weights =
  pointwise_mul

(** val spectral_conv : fNOLayerParams -> cComplex list -> cComplex list **)

let spectral_conv p v =
  let n = length v in
  let xfull = dft v in
  let xlow = truncate_modes p.fno_K_max xfull in
  let xweighted = apply_weights p.fno_weights xlow in
  let xpad = pad_to n xweighted in idft xpad

(** val skip_connection : fNOLayerParams -> cComplex list -> cComplex list **)

let skip_connection p v =
  map (fun x -> cmul p.fno_skip x) v

(** val fno_layer : fNOLayerParams -> cComplex list -> cComplex list **)

let fno_layer p v =
  let kv = spectral_conv p v in
  let wv = skip_connection p v in
  apply_nonlin p.fno_nonlin
    (map (fun pat -> let (k, w) = pat in cadd k w) (combine kv wv))

type fNOParams = { fno_lift : cComplex; fno_proj : cComplex;
                   fno_layers : fNOLayerParams list }

(** val lift : cComplex -> cComplex list -> cComplex list **)

let lift p v =
  map (cmul p) v

(** val apply_layers :
    fNOLayerParams list -> cComplex list -> cComplex list **)

let rec apply_layers layers v =
  match layers with
  | [] -> v
  | l :: ls -> apply_layers ls (fno_layer l v)

(** val fno_forward : fNOParams -> cComplex list -> cComplex list **)

let fno_forward p u =
  lift p.fno_proj (apply_layers p.fno_layers (lift p.fno_lift u))

(** val circulant_op : cComplex list -> cComplex list -> cComplex list **)

let circulant_op =
  cyclic_conv
