
type nat =
| O
| S of nat

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

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
               let (g, p0) = ggcdn n0 (sub b' a') a in
               let (ba, aa) = p0 in (g, (aa, (add aa (XO ba))))
             | Gt ->
               let (g, p0) = ggcdn n0 (sub a' b') b in
               let (ab, bb) = p0 in (g, ((add bb (XO ab)), bb)))
          | XO b0 ->
            let (g, p0) = ggcdn n0 a b0 in
            let (aa, bb) = p0 in (g, (aa, (XO bb)))
          | XH -> (XH, (a, XH)))
       | XO a0 ->
         (match b with
          | XI _ ->
            let (g, p0) = ggcdn n0 a0 b in
            let (aa, bb) = p0 in (g, ((XO aa), bb))
          | XO b0 -> let (g, p0) = ggcdn n0 a0 b0 in ((XO g), p0)
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
         let (g, p0) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p0 in ((Zpos g), ((Zpos aa), (Zpos bb)))
       | Zneg b0 ->
         let (g, p0) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p0 in ((Zpos g), ((Zpos aa), (Zneg bb))))
    | Zneg a0 ->
      (match b with
       | Z0 -> ((abs a), ((sgn a), Z0))
       | Zpos b0 ->
         let (g, p0) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p0 in ((Zpos g), ((Zneg aa), (Zpos bb)))
       | Zneg b0 ->
         let (g, p0) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p0 in ((Zpos g), ((Zneg aa), (Zneg bb))))
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: l0 -> (f a) :: (map f l0)

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

type cReal = { seq : (z -> q); scale : z }

(** val inject_Q : q -> cReal **)

let inject_Q q0 =
  { seq = (fun _ -> q0); scale = (qbound_ltabs_ZExp2 q0) }

(** val cReal_plus_seq : cReal -> cReal -> z -> q **)

let cReal_plus_seq x y n =
  qred (qplus (x.seq (Z.sub n (Zpos XH))) (y.seq (Z.sub n (Zpos XH))))

(** val cReal_plus_scale : cReal -> cReal -> z **)

let cReal_plus_scale x y =
  Z.add (Z.max x.scale y.scale) (Zpos XH)

(** val cReal_plus : cReal -> cReal -> cReal **)

let cReal_plus x y =
  { seq = (cReal_plus_seq x y); scale = (cReal_plus_scale x y) }

(** val cReal_opp_seq : cReal -> z -> q **)

let cReal_opp_seq x n =
  qopp (x.seq n)

(** val cReal_opp_scale : cReal -> z **)

let cReal_opp_scale x =
  x.scale

(** val cReal_opp : cReal -> cReal **)

let cReal_opp x =
  { seq = (cReal_opp_seq x); scale = (cReal_opp_scale x) }

(** val cReal_minus : cReal -> cReal -> cReal **)

let cReal_minus x y =
  cReal_plus x (cReal_opp y)

(** val cReal_mult_seq : cReal -> cReal -> z -> q **)

let cReal_mult_seq x y n =
  qmult (x.seq (Z.sub (Z.sub n y.scale) (Zpos XH)))
    (y.seq (Z.sub (Z.sub n x.scale) (Zpos XH)))

(** val cReal_mult_scale : cReal -> cReal -> z **)

let cReal_mult_scale x y =
  Z.add x.scale y.scale

(** val cReal_mult : cReal -> cReal -> cReal **)

let cReal_mult x y =
  { seq = (cReal_mult_seq x y); scale = (cReal_mult_scale x y) }

(** val pow : cReal -> nat -> cReal **)

let rec pow r = function
| O -> inject_Q { qnum = (Zpos XH); qden = XH }
| S n0 -> cReal_mult r (pow r n0)

(** val approx : cReal -> z -> q **)

let approx x k =
  x.seq k

(** val q_as_Zpair : q -> z * z **)

let q_as_Zpair q0 =
  (q0.qnum, (Zpos q0.qden))

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

let cadd z1 w =
  { re = (cReal_plus z1.re w.re); im = (cReal_plus z1.im w.im) }

(** val cmul : cComplex -> cComplex -> cComplex **)

let cmul z1 w =
  { re = (cReal_minus (cReal_mult z1.re w.re) (cReal_mult z1.im w.im)); im =
    (cReal_plus (cReal_mult z1.re w.im) (cReal_mult z1.im w.re)) }

(** val cpow : cComplex -> nat -> cComplex **)

let rec cpow z1 = function
| O -> c1
| S n' -> cmul z1 (cpow z1 n')

(** val capprox : cComplex -> z -> q * q **)

let capprox z1 n =
  ((z1.re.seq n), (z1.im.seq n))

type cComplexlist = cComplex list

(** val repeat : cComplex -> nat -> cComplexlist **)

let rec repeat n = function
| O -> []
| S count' -> n :: (repeat n count')

(** val length : cComplexlist -> nat **)

let rec length = function
| [] -> O
| _ :: t -> S (length t)

(** val app0 : cComplexlist -> cComplexlist -> cComplexlist **)

let rec app0 l1 l2 =
  match l1 with
  | [] -> l2
  | h :: t -> h :: (app0 t l2)

(** val filter : (cComplex -> bool) -> cComplexlist -> cComplexlist **)

let rec filter test = function
| [] -> []
| hd :: tl -> if test hd then hd :: (filter test tl) else filter test tl

(** val counter : (cComplex -> bool) -> cComplexlist -> cComplex **)

let rec counter test = function
| [] -> cinject_Q { qnum = Z0; qden = XH }
| hd :: tl ->
  if test hd
  then cadd (cinject_Q { qnum = (Zpos XH); qden = XH }) (counter test tl)
  else counter test tl

(** val add0 : cComplex -> cComplexlist -> cComplexlist **)

let add0 v s =
  v :: s

(** val rev : cComplexlist -> cComplexlist **)

let rec rev = function
| [] -> []
| h :: t -> app0 (rev t) (h :: [])

(** val vzero : nat -> cComplex list **)

let rec vzero = function
| O -> []
| S k -> c0 :: (vzero k)

(** val vadd : cComplex list -> cComplex list -> cComplex list **)

let rec vadd v w =
  match v with
  | [] -> []
  | x :: xs -> (match w with
                | [] -> []
                | y :: ys -> (cadd x y) :: (vadd xs ys))

(** val vscale : cComplex -> cComplex list -> cComplex list **)

let rec vscale a = function
| [] -> []
| x :: xs -> (cmul a x) :: (vscale a xs)

type 'a mat = 'a list list

(** val dot : cComplex list -> cComplex list -> cComplex **)

let rec dot v w =
  match v with
  | [] -> c0
  | x :: xs ->
    (match w with
     | [] -> c0
     | y :: ys -> cadd (cmul x y) (dot xs ys))

(** val madd : cComplex mat -> cComplex mat -> cComplex mat **)

let rec madd a b =
  match a with
  | [] -> []
  | rA :: as0 ->
    (match b with
     | [] -> []
     | rB :: bs -> (vadd rA rB) :: (madd as0 bs))

(** val nth_default : cComplex -> cComplex list -> nat -> cComplex **)

let rec nth_default d l j =
  match l with
  | [] -> d
  | x :: xs -> (match j with
                | O -> x
                | S k -> nth_default d xs k)

(** val col : cComplex mat -> nat -> cComplex list **)

let col a j =
  map (fun row -> nth_default c0 row j) a

(** val mcols : nat -> cComplex mat -> cComplex list list **)

let rec mcols m a =
  match m with
  | O -> []
  | S k -> app (mcols k a) ((col a k) :: [])

(** val row_mul_cols :
    cComplex list -> cComplex list list -> cComplex list **)

let rec row_mul_cols r = function
| [] -> []
| c :: cs -> (dot r c) :: (row_mul_cols r cs)

(** val mmul : cComplex mat -> cComplex mat -> nat -> cComplex mat **)

let rec mmul a b p0 =
  let colsB = mcols p0 b in
  (match a with
   | [] -> []
   | r :: rs -> (row_mul_cols r colsB) :: (mmul rs b p0))

(** val trace_aux : cComplex list list -> nat -> cComplex **)

let rec trace_aux a i =
  match a with
  | [] -> c0
  | row :: rows -> cadd (nth_default c0 row i) (trace_aux rows (S i))

(** val trace : cComplex list list -> cComplex **)

let trace a =
  trace_aux a O

(** val two_plus_i : cComplex **)

let two_plus_i =
  { re = (inject_Q { qnum = (Zpos (XO XH)); qden = XH }); im =
    (inject_Q { qnum = (Zpos XH); qden = XH }) }

(** val p : cComplex -> cComplex **)

let p z1 =
  cadd (cadd (cpow z1 (S (S (S O)))) (cmul two_plus_i z1)) c1

(** val z0 : cComplex **)

let z0 =
  { re = (inject_Q { qnum = (Zpos XH); qden = (XI XH) }); im =
    (inject_Q { qnum = (Zpos XH); qden = (XO XH) }) }

(** val fr : cReal -> cReal **)

let fr x =
  cReal_plus (cReal_plus x x) (inject_Q { qnum = (Zpos XH); qden = XH })

(** val gr : cReal -> cReal **)

let gr x =
  cReal_plus
    (cReal_plus (pow x (S (S O)))
      (cReal_mult (inject_Q { qnum = (Zpos (XO XH)); qden = XH }) x))
    (inject_Q { qnum = (Zpos XH); qden = XH })

(** val one_third : cReal **)

let one_third =
  inject_Q { qnum = (Zpos XH); qden = (XI XH) }

(** val run_f : z -> z * z **)

let run_f k =
  q_as_Zpair (approx (fr one_third) k)

(** val run_g : z -> z * z **)

let run_g k =
  q_as_Zpair (approx (gr one_third) k)

(** val run_p : z -> q * q **)

let run_p n =
  capprox (p z0) n
