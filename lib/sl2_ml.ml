
(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

type comparison =
| Eq
| Lt
| Gt

module Coq__1 = struct
 (** val add : int -> int -> int **)

 let rec add = (+)
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

  (** val size_nat : positive -> int **)

  let rec size_nat = function
  | XI p0 -> Stdlib.Int.succ (size_nat p0)
  | XO p0 -> Stdlib.Int.succ (size_nat p0)
  | XH -> Stdlib.Int.succ 0

  (** val ggcdn :
      int -> positive -> positive -> positive * (positive * positive) **)

  let rec ggcdn n a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (XH, (a, b)))
      (fun n0 ->
      match a with
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
      n

  (** val ggcd : positive -> positive -> positive * (positive * positive) **)

  let ggcd a b =
    ggcdn (Coq__1.add (size_nat a) (size_nat b)) a b

  (** val eq_dec : positive -> positive -> bool **)

  let rec eq_dec p x0 =
    match p with
    | XI p0 -> (match x0 with
                | XI p1 -> eq_dec p0 p1
                | _ -> false)
    | XO p0 -> (match x0 with
                | XO p1 -> eq_dec p0 p1
                | _ -> false)
    | XH -> (match x0 with
             | XH -> true
             | _ -> false)
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

  (** val eq_dec : z -> z -> bool **)

  let eq_dec x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> true
             | _ -> false)
    | Zpos p -> (match y with
                 | Zpos p0 -> Coq_Pos.eq_dec p p0
                 | _ -> false)
    | Zneg p -> (match y with
                 | Zneg p0 -> Coq_Pos.eq_dec p p0
                 | _ -> false)
 end

type 'r commRing = { cr_zero : 'r; cr_one : 'r; cr_add : ('r -> 'r -> 'r);
                     cr_mul : ('r -> 'r -> 'r); cr_neg : ('r -> 'r) }

(** val cr_sub : 'a1 commRing -> 'a1 -> 'a1 -> 'a1 **)

let cr_sub cr a b =
  cr.cr_add a (cr.cr_neg b)

type 'f field = { fld_ring : 'f commRing; fld_inv : ('f -> 'f) }

type 'f mat2 = (('f * 'f) * 'f) * 'f

(** val mat2_mk : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 mat2 **)

let mat2_mk a b c d =
  (((a, b), c), d)

(** val mat2_id : 'a1 field -> 'a1 mat2 **)

let mat2_id fld =
  mat2_mk fld.fld_ring.cr_one fld.fld_ring.cr_zero fld.fld_ring.cr_zero
    fld.fld_ring.cr_one

(** val mat2_zero : 'a1 field -> 'a1 mat2 **)

let mat2_zero fld =
  mat2_mk fld.fld_ring.cr_zero fld.fld_ring.cr_zero fld.fld_ring.cr_zero
    fld.fld_ring.cr_zero

(** val mat2_mul : 'a1 field -> 'a1 mat2 -> 'a1 mat2 -> 'a1 mat2 **)

let mat2_mul fld m n =
  let (p, d) = m in
  let (p0, c) = p in
  let (a, b) = p0 in
  let (p1, d') = n in
  let (p2, c') = p1 in
  let (a', b') = p2 in
  mat2_mk
    (fld.fld_ring.cr_add (fld.fld_ring.cr_mul a a')
      (fld.fld_ring.cr_mul b c'))
    (fld.fld_ring.cr_add (fld.fld_ring.cr_mul a b')
      (fld.fld_ring.cr_mul b d'))
    (fld.fld_ring.cr_add (fld.fld_ring.cr_mul c a')
      (fld.fld_ring.cr_mul d c'))
    (fld.fld_ring.cr_add (fld.fld_ring.cr_mul c b')
      (fld.fld_ring.cr_mul d d'))

(** val mat2_add : 'a1 field -> 'a1 mat2 -> 'a1 mat2 -> 'a1 mat2 **)

let mat2_add fld m n =
  let (p, d) = m in
  let (p0, c) = p in
  let (a, b) = p0 in
  let (p1, d') = n in
  let (p2, c') = p1 in
  let (a', b') = p2 in
  mat2_mk (fld.fld_ring.cr_add a a') (fld.fld_ring.cr_add b b')
    (fld.fld_ring.cr_add c c') (fld.fld_ring.cr_add d d')

(** val mat2_neg : 'a1 field -> 'a1 mat2 -> 'a1 mat2 **)

let mat2_neg fld = function
| (p, d) ->
  let (p0, c) = p in
  let (a, b) = p0 in
  mat2_mk (fld.fld_ring.cr_neg a) (fld.fld_ring.cr_neg b)
    (fld.fld_ring.cr_neg c) (fld.fld_ring.cr_neg d)

(** val mat2_scale : 'a1 field -> 'a1 -> 'a1 mat2 -> 'a1 mat2 **)

let mat2_scale fld k = function
| (p, d) ->
  let (p0, c) = p in
  let (a, b) = p0 in
  mat2_mk (fld.fld_ring.cr_mul k a) (fld.fld_ring.cr_mul k b)
    (fld.fld_ring.cr_mul k c) (fld.fld_ring.cr_mul k d)

(** val mat2_det : 'a1 field -> 'a1 mat2 -> 'a1 **)

let mat2_det fld = function
| (p, d) ->
  let (p0, c) = p in
  let (a, b) = p0 in
  cr_sub fld.fld_ring (fld.fld_ring.cr_mul a d) (fld.fld_ring.cr_mul b c)

(** val mat2_trace : 'a1 field -> 'a1 mat2 -> 'a1 **)

let mat2_trace fld = function
| (p, d) -> let (p0, _) = p in let (a, _) = p0 in fld.fld_ring.cr_add a d

(** val mat2_adj : 'a1 field -> 'a1 mat2 -> 'a1 mat2 **)

let mat2_adj fld = function
| (p, d) ->
  let (p0, c) = p in
  let (a, b) = p0 in
  mat2_mk d (fld.fld_ring.cr_neg b) (fld.fld_ring.cr_neg c) a

type q = { qnum : z; qden : positive }

(** val qeq_dec : q -> q -> bool **)

let qeq_dec x y =
  Z.eq_dec (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))

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

(** val qinv : q -> q **)

let qinv x =
  match x.qnum with
  | Z0 -> { qnum = Z0; qden = XH }
  | Zpos p -> { qnum = (Zpos x.qden); qden = p }
  | Zneg p -> { qnum = (Zneg x.qden); qden = p }

(** val qred : q -> q **)

let qred q0 =
  let { qnum = q1; qden = q2 } = q0 in
  let (r1, r2) = snd (Z.ggcd q1 (Zpos q2)) in
  { qnum = r1; qden = (Z.to_pos r2) }

type qc = q
  (* singleton inductive, whose constructor was Qcmake *)

(** val q2Qc : q -> qc **)

let q2Qc =
  qred

(** val qc_eq_dec : qc -> qc -> bool **)

let qc_eq_dec =
  qeq_dec

(** val qcplus : qc -> qc -> qc **)

let qcplus x y =
  q2Qc (qplus x y)

(** val qcmult : qc -> qc -> qc **)

let qcmult x y =
  q2Qc (qmult x y)

(** val qcopp : qc -> qc **)

let qcopp x =
  q2Qc (qopp x)

(** val qcminus : qc -> qc -> qc **)

let qcminus x y =
  qcplus x (qcopp y)

(** val qcinv : qc -> qc **)

let qcinv x =
  q2Qc (qinv x)

(** val qc_CommRing : qc commRing **)

let qc_CommRing =
  { cr_zero = (q2Qc { qnum = Z0; qden = XH }); cr_one =
    (q2Qc { qnum = (Zpos XH); qden = XH }); cr_add = qcplus; cr_mul = qcmult;
    cr_neg = qcopp }

(** val qc_Field : qc field **)

let qc_Field =
  { fld_ring = qc_CommRing; fld_inv = qcinv }

type mat2_Qc = qc mat2

(** val mat2_mk_Qc : qc -> qc -> qc -> qc -> mat2_Qc **)

let mat2_mk_Qc =
  mat2_mk

(** val mat2_id_Qc : mat2_Qc **)

let mat2_id_Qc =
  mat2_id qc_Field

(** val mat2_zero_Qc : mat2_Qc **)

let mat2_zero_Qc =
  mat2_zero qc_Field

(** val mat2_mul_Qc : mat2_Qc -> mat2_Qc -> mat2_Qc **)

let mat2_mul_Qc =
  mat2_mul qc_Field

(** val mat2_add_Qc : mat2_Qc -> mat2_Qc -> mat2_Qc **)

let mat2_add_Qc =
  mat2_add qc_Field

(** val mat2_neg_Qc : mat2_Qc -> mat2_Qc **)

let mat2_neg_Qc =
  mat2_neg qc_Field

(** val mat2_scale_Qc : qc -> mat2_Qc -> mat2_Qc **)

let mat2_scale_Qc =
  mat2_scale qc_Field

(** val mat2_det_Qc : mat2_Qc -> qc **)

let mat2_det_Qc =
  mat2_det qc_Field

(** val mat2_trace_Qc : mat2_Qc -> qc **)

let mat2_trace_Qc =
  mat2_trace qc_Field

(** val mat2_adj_Qc : mat2_Qc -> mat2_Qc **)

let mat2_adj_Qc =
  mat2_adj qc_Field

(** val mat2_pow_Qc : mat2_Qc -> int -> mat2_Qc **)

let rec mat2_pow_Qc m n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> mat2_id_Qc)
    (fun k -> mat2_mul_Qc m (mat2_pow_Qc m k))
    n

(** val is_in_SL2_Qc : mat2_Qc -> bool **)

let is_in_SL2_Qc m =
  if qc_eq_dec (mat2_det_Qc m) (q2Qc { qnum = (Zpos XH); qden = XH })
  then true
  else false

(** val sL2_inv_Qc : mat2_Qc -> mat2_Qc **)

let sL2_inv_Qc =
  mat2_adj_Qc

(** val trace_pow_chebyshev : qc -> int -> qc **)

let rec trace_pow_chebyshev t n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    qcplus (q2Qc { qnum = (Zpos XH); qden = XH })
      (q2Qc { qnum = (Zpos XH); qden = XH }))
    (fun k' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> t)
      (fun k ->
      qcminus (qcmult t (trace_pow_chebyshev t k')) (trace_pow_chebyshev t k))
      k')
    n
