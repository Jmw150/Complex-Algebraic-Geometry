(* matn.ml — generic n×n matrix arithmetic over Qc.
   Uses the qc/q types from the extracted sl2_ml.ml. *)

open Sl2_ml

(* Convenience builders. *)
let rec pos_of_int n =
  if n <= 1 then XH
  else if n mod 2 = 0 then XO (pos_of_int (n / 2))
  else XI (pos_of_int (n / 2))

let z_of_int n =
  if n = 0 then Z0
  else if n > 0 then Zpos (pos_of_int n)
  else Zneg (pos_of_int (-n))

let qc_of_int n : qc = q2Qc { qnum = z_of_int n; qden = XH }

let qc_zero = qc_of_int 0
let qc_one = qc_of_int 1

(* A matrix is an n×n array of qc. *)
type mat = qc array array

let make n : mat = Array.make_matrix n n qc_zero

let dim (m : mat) = Array.length m

let id n : mat =
  let r = make n in
  for i = 0 to n - 1 do r.(i).(i) <- qc_one done;
  r

(* Matrix from a flat row-major list. *)
let of_list n (xs : qc list) : mat =
  let m = make n in
  let xs = Array.of_list xs in
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      m.(i).(j) <- xs.(i * n + j)
    done
  done; m

(* Matrix multiplication. *)
let mul (a : mat) (b : mat) : mat =
  let n = dim a in
  let r = make n in
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      let s = ref qc_zero in
      for k = 0 to n - 1 do
        s := qcplus !s (qcmult a.(i).(k) b.(k).(j))
      done;
      r.(i).(j) <- !s
    done
  done; r

(* Trace = sum of diagonal entries. *)
let trace (a : mat) : qc =
  let n = dim a in
  let s = ref qc_zero in
  for i = 0 to n - 1 do s := qcplus !s a.(i).(i) done;
  !s

(* Drop row r and column c. *)
let minor (a : mat) (r : int) (c : int) : mat =
  let n = dim a in
  let m = Array.make_matrix (n - 1) (n - 1) qc_zero in
  let ii = ref 0 in
  for i = 0 to n - 1 do
    if i <> r then begin
      let jj = ref 0 in
      for j = 0 to n - 1 do
        if j <> c then begin
          m.(!ii).(!jj) <- a.(i).(j);
          incr jj
        end
      done;
      incr ii
    end
  done; m

(* Determinant by cofactor expansion along the first row. *)
let rec det (a : mat) : qc =
  let n = dim a in
  if n = 0 then qc_one
  else if n = 1 then a.(0).(0)
  else begin
    let s = ref qc_zero in
    let sign = ref qc_one in
    for j = 0 to n - 1 do
      let m = minor a 0 j in
      let term = qcmult a.(0).(j) (det m) in
      let signed = qcmult !sign term in
      s := qcplus !s signed;
      sign := qcopp !sign  (* alternate signs starting +,-,+,- *)
    done;
    !s
  end

(* Adjugate (transpose of cofactor matrix). For 1×1, adj = id. *)
let adjugate (a : mat) : mat =
  let n = dim a in
  if n = 1 then
    let r = make 1 in r.(0).(0) <- qc_one; r
  else begin
    let r = make n in
    for i = 0 to n - 1 do
      for j = 0 to n - 1 do
        let m = minor a i j in
        let cof = det m in
        let sign = if (i + j) mod 2 = 0 then qc_one else qcopp qc_one in
        r.(j).(i) <- qcmult sign cof  (* note: transpose ⇒ swap i,j *)
      done
    done; r
  end

(* Inverse for det = 1 matrices: just the adjugate. *)
let inv_det1 a = adjugate a

(* Power of a matrix. *)
let rec pow (a : mat) (k : int) : mat =
  if k = 0 then id (dim a)
  else if k = 1 then a
  else mul a (pow a (k - 1))

(* Equality. *)
let qc_eq = qc_eq_dec
let eq (a : mat) (b : mat) : bool =
  let n = dim a in
  let same = ref true in
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      if not (qc_eq a.(i).(j) b.(i).(j)) then same := false
    done
  done; !same

(* Pretty-print a 2D matrix. *)
let pp_z = function
  | Z0 -> "0"
  | Zpos p -> let rec ti = function XH->1 | XO p->2*ti p | XI p->2*ti p+1
              in string_of_int (ti p)
  | Zneg p -> let rec ti = function XH->1 | XO p->2*ti p | XI p->2*ti p+1
              in string_of_int (- (ti p))
let pp_pos p = let rec ti = function XH->1 | XO p->2*ti p | XI p->2*ti p+1
               in string_of_int (ti p)
let pp_qc (q : qc) = let n = pp_z q.qnum in let d = pp_pos q.qden in
                    if d = "1" then n else n^"/"^d

let pp (m : mat) =
  let n = dim m in
  let buf = Buffer.create 32 in
  for i = 0 to n - 1 do
    Buffer.add_char buf '[';
    for j = 0 to n - 1 do
      if j > 0 then Buffer.add_string buf ", ";
      Buffer.add_string buf (pp_qc m.(i).(j))
    done;
    Buffer.add_char buf ']';
    if i < n - 1 then Buffer.add_char buf ' '
  done;
  Buffer.contents buf
