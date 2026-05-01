(* Sanity tests for the extracted free_group_ml.ml *)

open Free_group_ml

(* F_2 letters *)
let a = f2_a
let b = f2_b
let a_inv = f2_A
let b_inv = f2_B

(* Helpers to make words *)
let w xs = xs

let pp_letter (l : letter) =
  let i = match fst l with
    | F1 _ -> "0"
    | FS _ -> "1"  (* approximate; we only care about F_2 *)
  in
  let bit = if snd l then "+" else "-" in
  Printf.sprintf "(%s,%s)" i bit

let _ = pp_letter

let pp_word w =
  "[" ^ (String.concat "," (List.map pp_letter w)) ^ "]"

(* Test 1: aA reduces to e *)
let test1 () =
  let w = [a; a_inv] in
  let r = reduce_F2 w in
  Printf.printf "aA reduces to %s (should be [])\n" (pp_word r);
  assert (r = [])

(* Test 2: ab is reduced *)
let test2 () =
  let w = [a; b] in
  let r = reduce_F2 w in
  Printf.printf "ab reduces to %s (should be [a;b])\n" (pp_word r);
  assert (List.length r = 2)

(* Test 3: word equality *)
let test3 () =
  Printf.printf "ab = ab: %b\n" (word_eq_F2 [a; b] [a; b]);
  Printf.printf "ab = ba: %b\n" (word_eq_F2 [a; b] [b; a]);
  Printf.printf "aA = e:  %b\n" (word_eq_F2 [a; a_inv] []);
  assert (word_eq_F2 [a; b] [a; b]);
  assert (not (word_eq_F2 [a; b] [b; a]));
  assert (word_eq_F2 [a; a_inv] [])

(* Test 4: free product *)
let test4 () =
  let w1 = [a; b] in
  let w2 = [b_inv; a] in
  let prod = free_mul_F2 w1 w2 in
  Printf.printf "ab · b^-1 a = %s (should be aa)\n" (pp_word prod);
  assert (word_eq_F2 prod [a; a])

(* Test 5: conjugation in F_2 *)
let test5 () =
  let g = [a] in
  let x = [b] in
  let c = conjugate_F2 g x in
  Printf.printf "conj_a(b) = %s (should be aba^-1)\n" (pp_word c);
  assert (word_eq_F2 c [a; b; a_inv])

(* Test 6: cyclic reduction *)
let test6 () =
  let w = [a; b; a_inv] in
  let cr = cyclic_reduce_F2 w in
  Printf.printf "cyc_red(aba^-1) = %s (should be [b])\n" (pp_word cr);
  assert (word_eq_F2 cr [b])

(* Test 7: conjugacy decision *)
let test7 () =
  Printf.printf "aba^-1 ~ b: %b (should be true)\n" (are_conjugate_F2_dec [a; b; a_inv] [b]);
  Printf.printf "ab ~ ba:    %b (should be true — cyclic rotations)\n" (are_conjugate_F2_dec [a; b] [b; a]);
  Printf.printf "a ~ b:      %b (should be false)\n" (are_conjugate_F2_dec [a] [b]);
  Printf.printf "ab ~ a^2:   %b (should be false)\n" (are_conjugate_F2_dec [a; b] [a; a]);
  assert (are_conjugate_F2_dec [a; b; a_inv] [b]);
  assert (are_conjugate_F2_dec [a; b] [b; a]);
  assert (not (are_conjugate_F2_dec [a] [b]));
  assert (not (are_conjugate_F2_dec [a; b] [a; a]))

(* Test 8: powers *)
let test8 () =
  let g3 = gamma_pow_F2_word [a; b] 3 in
  Printf.printf "(ab)^3 = %s (length should be 6)\n" (pp_word g3);
  assert (List.length g3 = 6)

let () =
  Printf.printf "=== Free group F_2 extraction tests ===\n";
  test1 (); test2 (); test3 (); test4 ();
  test5 (); test6 (); test7 (); test8 ();
  Printf.printf "All tests passed.\n"
