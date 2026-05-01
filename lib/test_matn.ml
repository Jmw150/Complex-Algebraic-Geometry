(* Sanity tests for matn.ml. *)
open Matn

let pp_qc = pp_qc

let test_id_3 () =
  let i = id 3 in
  Printf.printf "I_3 = %s\n" (pp i);
  Printf.printf "tr(I_3) = %s (should be 3)\n" (pp_qc (trace i));
  Printf.printf "det(I_3) = %s (should be 1)\n" (pp_qc (det i));
  assert (qc_eq (trace i) (qc_of_int 3));
  assert (qc_eq (det i) (qc_of_int 1))

let test_3x3_det () =
  (* M = [[1,2,3],[4,5,6],[7,8,9]] — singular, det = 0 *)
  let m = of_list 3 [
    qc_of_int 1; qc_of_int 2; qc_of_int 3;
    qc_of_int 4; qc_of_int 5; qc_of_int 6;
    qc_of_int 7; qc_of_int 8; qc_of_int 9;
  ] in
  Printf.printf "M = %s\n" (pp m);
  Printf.printf "det(M) = %s (should be 0)\n" (pp_qc (det m));
  assert (qc_eq (det m) (qc_of_int 0))

let test_sl3_inv () =
  (* M = [[1,1,0],[0,1,1],[0,0,1]] — upper-triangular SL_3, det = 1 *)
  let m = of_list 3 [
    qc_of_int 1; qc_of_int 1; qc_of_int 0;
    qc_of_int 0; qc_of_int 1; qc_of_int 1;
    qc_of_int 0; qc_of_int 0; qc_of_int 1;
  ] in
  Printf.printf "M = %s\n" (pp m);
  Printf.printf "det(M) = %s (should be 1)\n" (pp_qc (det m));
  let m_inv = inv_det1 m in
  Printf.printf "M^-1 = %s\n" (pp m_inv);
  let prod = mul m m_inv in
  Printf.printf "M·M^-1 = %s (should be I_3)\n" (pp prod);
  assert (eq prod (id 3))

let test_4x4_det () =
  (* 4x4 case to test recursion. M = upper triangular with 1's, det = 1 *)
  let m = of_list 4 [
    qc_of_int 1; qc_of_int 1; qc_of_int 1; qc_of_int 1;
    qc_of_int 0; qc_of_int 1; qc_of_int 1; qc_of_int 1;
    qc_of_int 0; qc_of_int 0; qc_of_int 1; qc_of_int 1;
    qc_of_int 0; qc_of_int 0; qc_of_int 0; qc_of_int 1;
  ] in
  Printf.printf "4x4 M = %s\n" (pp m);
  Printf.printf "det(M) = %s (should be 1)\n" (pp_qc (det m));
  assert (qc_eq (det m) (qc_of_int 1));
  let m_inv = inv_det1 m in
  let prod = mul m m_inv in
  Printf.printf "M·M^-1 = %s (should be I_4)\n" (pp prod);
  assert (eq prod (id 4))

let test_trace_cyclic () =
  let m1 = of_list 3 [
    qc_of_int 1; qc_of_int 2; qc_of_int 3;
    qc_of_int 0; qc_of_int 1; qc_of_int 4;
    qc_of_int 5; qc_of_int 6; qc_of_int 0;
  ] in
  let m2 = of_list 3 [
    qc_of_int 7; qc_of_int 8; qc_of_int 9;
    qc_of_int 1; qc_of_int 0; qc_of_int 2;
    qc_of_int 3; qc_of_int 4; qc_of_int 5;
  ] in
  let t12 = trace (mul m1 m2) in
  let t21 = trace (mul m2 m1) in
  Printf.printf "tr(M1·M2) = %s\n" (pp_qc t12);
  Printf.printf "tr(M2·M1) = %s (should equal — cyclicity)\n" (pp_qc t21);
  assert (qc_eq t12 t21)

let () =
  Printf.printf "=== matn.ml tests ===\n";
  test_id_3 ();
  test_3x3_det ();
  test_sl3_inv ();
  test_4x4_det ();
  test_trace_cyclic ();
  Printf.printf "All matn.ml tests passed.\n"
