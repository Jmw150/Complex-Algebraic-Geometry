(* Sanity tests for sl2_ml.ml.  We build SL(2, Q) matrices from
   ints and verify det/trace/multiplication. *)

open Sl2_ml

(* Build positive integers (positive type from extracted Coq). *)
let rec pos_of_int n =
  if n <= 1 then XH
  else if n mod 2 = 0 then XO (pos_of_int (n / 2))
  else XI (pos_of_int (n / 2))

(* int → z (signed integer). *)
let z_of_int n =
  if n = 0 then Z0
  else if n > 0 then Zpos (pos_of_int n)
  else Zneg (pos_of_int (-n))

(* int → q (rational p/1) → qc (canonical). *)
let qc_of_int n : qc =
  q2Qc { qnum = z_of_int n; qden = XH }

(* int * int → qc (rational num/den) *)
let qc_of_frac n d =
  if d <= 0 then failwith "denominator must be positive"
  else q2Qc { qnum = z_of_int n; qden = pos_of_int d }

(* Pretty-print a qc as num/den or num. *)
let pp_z = function
  | Z0 -> "0"
  | Zpos p ->
      let rec to_int = function
        | XH -> 1
        | XO p -> 2 * to_int p
        | XI p -> 2 * to_int p + 1
      in
      string_of_int (to_int p)
  | Zneg p ->
      let rec to_int = function
        | XH -> 1
        | XO p -> 2 * to_int p
        | XI p -> 2 * to_int p + 1
      in
      string_of_int (- (to_int p))

let pp_pos p =
  let rec to_int = function
    | XH -> 1
    | XO p -> 2 * to_int p
    | XI p -> 2 * to_int p + 1
  in string_of_int (to_int p)

let pp_q (q : q) =
  let n = pp_z q.qnum in
  let d = pp_pos q.qden in
  if d = "1" then n else n ^ "/" ^ d

let pp_qc (qc : qc) = pp_q qc

let pp_mat2 (m : mat2_Qc) =
  let (((a, b), c), d) = m in
  Printf.sprintf "[[%s, %s] [%s, %s]]" (pp_qc a) (pp_qc b) (pp_qc c) (pp_qc d)

let qc_eq a b = qc_eq_dec a b

(* Tests *)
let test_id () =
  let i = mat2_id_Qc in
  Printf.printf "I = %s\n" (pp_mat2 i);
  Printf.printf "tr(I) = %s\n" (pp_qc (mat2_trace_Qc i));
  Printf.printf "det(I) = %s\n" (pp_qc (mat2_det_Qc i));
  assert (qc_eq (mat2_det_Qc i) (qc_of_int 1));
  assert (qc_eq (mat2_trace_Qc i) (qc_of_int 2))

let test_simple_matrix () =
  (* A = [[2, 1], [1, 1]] — has det = 1, in SL(2, Z) *)
  let a =
    mat2_mk_Qc
      (qc_of_int 2) (qc_of_int 1)
      (qc_of_int 1) (qc_of_int 1)
  in
  Printf.printf "A = %s\n" (pp_mat2 a);
  Printf.printf "det(A) = %s (should be 1)\n" (pp_qc (mat2_det_Qc a));
  Printf.printf "tr(A) = %s (should be 3)\n" (pp_qc (mat2_trace_Qc a));
  assert (qc_eq (mat2_det_Qc a) (qc_of_int 1));
  assert (qc_eq (mat2_trace_Qc a) (qc_of_int 3));
  assert (is_in_SL2_Qc a)

let test_multiplication () =
  (* A = [[1, 1], [0, 1]], B = [[1, 0], [1, 1]] — both in SL(2, Z) *)
  let a = mat2_mk_Qc (qc_of_int 1) (qc_of_int 1) (qc_of_int 0) (qc_of_int 1) in
  let b = mat2_mk_Qc (qc_of_int 1) (qc_of_int 0) (qc_of_int 1) (qc_of_int 1) in
  let ab = mat2_mul_Qc a b in
  let ba = mat2_mul_Qc b a in
  Printf.printf "AB = %s\n" (pp_mat2 ab);
  Printf.printf "BA = %s\n" (pp_mat2 ba);
  Printf.printf "tr(AB) = %s\n" (pp_qc (mat2_trace_Qc ab));
  Printf.printf "tr(BA) = %s (should equal tr(AB) — cyclicity)\n" (pp_qc (mat2_trace_Qc ba));
  assert (qc_eq (mat2_trace_Qc ab) (mat2_trace_Qc ba));
  Printf.printf "det(AB) = %s (should be 1)\n" (pp_qc (mat2_det_Qc ab));
  assert (qc_eq (mat2_det_Qc ab) (qc_of_int 1))

let test_inverse () =
  let a = mat2_mk_Qc (qc_of_int 1) (qc_of_int 1) (qc_of_int 0) (qc_of_int 1) in
  let a_inv = sL2_inv_Qc a in
  Printf.printf "A^-1 = %s (should be [[1,-1],[0,1]])\n" (pp_mat2 a_inv);
  let prod = mat2_mul_Qc a a_inv in
  Printf.printf "A · A^-1 = %s (should be I)\n" (pp_mat2 prod);
  let (((p11, p12), p21), p22) = prod in
  assert (qc_eq p11 (qc_of_int 1));
  assert (qc_eq p12 (qc_of_int 0));
  assert (qc_eq p21 (qc_of_int 0));
  assert (qc_eq p22 (qc_of_int 1))

let test_fricke () =
  (* Fricke identity: tr(AB) + tr(AB^-1) = tr(A) · tr(B), for A, B in SL(2). *)
  let a = mat2_mk_Qc (qc_of_int 2) (qc_of_int 1) (qc_of_int 1) (qc_of_int 1) in
  let b = mat2_mk_Qc (qc_of_int 1) (qc_of_int 2) (qc_of_int 1) (qc_of_int 3) in
  assert (is_in_SL2_Qc a);
  assert (is_in_SL2_Qc b);
  let tr_a = mat2_trace_Qc a in
  let tr_b = mat2_trace_Qc b in
  let ab = mat2_mul_Qc a b in
  let ab_inv = mat2_mul_Qc a (sL2_inv_Qc b) in
  let lhs = qcplus (mat2_trace_Qc ab) (mat2_trace_Qc ab_inv) in
  let rhs = qcmult tr_a tr_b in
  Printf.printf "tr(AB) + tr(AB^-1) = %s\n" (pp_qc lhs);
  Printf.printf "tr(A) · tr(B)      = %s\n" (pp_qc rhs);
  assert (qc_eq lhs rhs);
  Printf.printf "Fricke identity verified.\n"

let test_chebyshev () =
  (* For A in SL(2): tr(A^n) follows the Chebyshev recursion in tr(A). *)
  let a = mat2_mk_Qc (qc_of_int 2) (qc_of_int 1) (qc_of_int 1) (qc_of_int 1) in
  let t = mat2_trace_Qc a in
  for n = 0 to 5 do
    let tr_pow = mat2_trace_Qc (mat2_pow_Qc a n) in
    let tr_cheb = trace_pow_chebyshev t n in
    Printf.printf "tr(A^%d) direct = %s,  Chebyshev = %s\n"
      n (pp_qc tr_pow) (pp_qc tr_cheb);
    assert (qc_eq tr_pow tr_cheb)
  done;
  Printf.printf "Chebyshev recursion verified for n = 0..5.\n"

let () =
  Printf.printf "=== SL(2, Qc) extraction tests ===\n";
  test_id (); test_simple_matrix (); test_multiplication ();
  test_inverse (); test_fricke (); test_chebyshev ();
  Printf.printf "All SL(2) tests passed.\n"
