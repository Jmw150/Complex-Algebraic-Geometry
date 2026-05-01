(* positive_search.ml — search F_2 for SL_n-trace-equivalent
   non-conjugate POSITIVE-word pairs.

   Conjecture 5.5 (Lawton-Louder-McReynolds): SL_n-trace-equivalent
   non-conj pairs exist iff such pairs exist among POSITIVE words.

   For n=2 we know non-positive trace-equivalent pairs exist (e.g.,
   BBABa, BABBa). The conjecture predicts positive analogues also exist.

   Args: max_len  dim_n  num_reps *)

open Free_group_ml
open Sl2_ml
open Matn

(* Positive words: only [a; b], no inverses. *)
let pos_letters = [f2_a; f2_b]

(* Enumerate all positive words of length L (no reduction needed since
   no cancellations possible). 2^L of them. *)
let rec enum_positive l : letter list list =
  if l = 0 then [[]]
  else List.concat_map (fun w -> List.map (fun ll -> ll :: w) pos_letters)
                       (enum_positive (l - 1))

let enum_positive_up_to len =
  let acc = ref [] in
  for l = 1 to len do acc := !acc @ enum_positive l done; !acc

(* Conjugacy partition (using are_conjugate_F2_dec). *)
let partition_by_conjugacy (words : letter list list) : letter list list list =
  let classes = ref [] in
  List.iter (fun w ->
    let added = ref false in
    classes := List.map (fun cls ->
      match cls with
      | [] -> cls
      | rep :: _ ->
        if not !added && are_conjugate_F2_dec rep w
        then (added := true; cls @ [w])
        else cls
    ) !classes;
    if not !added then classes := !classes @ [[w]]
  ) words; !classes

type rep_n = { ra : mat; rb : mat }

let eval_letter (r : rep_n) (l : letter) : mat =
  let m = match fst l with F1 _ -> r.ra | FS _ -> r.rb in
  if snd l then inv_det1 m else m

let eval_word (r : rep_n) (w : letter list) : mat =
  let n = dim r.ra in
  List.fold_left (fun acc l -> mul acc (eval_letter r l)) (id n) w

let trace_word r w = trace (eval_word r w)

let rand_sln_mat (n : int) ~num_shears : mat =
  let m = id n in
  for _ = 1 to num_shears do
    let i = Random.int n in
    let j = Random.int n in
    if i <> j then begin
      let k = (Random.int 5) - 2 in
      if k <> 0 then
        for c = 0 to n - 1 do
          m.(i).(c) <- qcplus m.(i).(c) (qcmult (qc_of_int k) m.(j).(c))
        done
    end
  done; m

let build_rep_bank ~n ~count =
  let rec go acc k =
    if k = 0 then acc
    else go ({ ra = rand_sln_mat n ~num_shears:8;
               rb = rand_sln_mat n ~num_shears:8 } :: acc) (k - 1)
  in go [] count

let pp_w w =
  String.concat ""
    (List.map (fun (l : letter) ->
      let i = match fst l with F1 _ -> "a" | FS _ -> "b" in
      if snd l then String.uppercase_ascii i else i) w)

let search ~max_len ~dim_n ~num_reps =
  let words = enum_positive_up_to max_len in
  Printf.printf "Enumerated %d positive F_2 words of length 1..%d\n"
    (List.length words) max_len;
  let classes = partition_by_conjugacy words in
  Printf.printf "Found %d positive conjugacy classes.\n" (List.length classes);
  let arr = Array.of_list (List.map List.hd classes) in
  let n_arr = Array.length arr in
  let test_reps = build_rep_bank ~n:dim_n ~count:num_reps in
  let test_arr = Array.of_list test_reps in
  Printf.printf "Built %d random SL(%d, Z) representations.\n"
    (List.length test_reps) dim_n;
  let trace_table = Array.make_matrix n_arr num_reps qc_zero in
  for ri = 0 to num_reps - 1 do
    for gi = 0 to n_arr - 1 do
      trace_table.(gi).(ri) <- trace_word test_arr.(ri) arr.(gi)
    done
  done;

  let same_trace_vec i j =
    let same = ref true in
    for ri = 0 to num_reps - 1 do
      if not (qc_eq trace_table.(i).(ri) trace_table.(j).(ri))
      then same := false
    done; !same
  in
  let strict_pairs = ref 0 in
  let trace_eq_pairs = ref 0 in
  let inversion_only = ref 0 in
  let trace_eq_genuine = ref 0 in
  let suspicious = ref [] in
  for i = 0 to n_arr - 1 do
    for j = i + 1 to n_arr - 1 do
      incr strict_pairs;
      if same_trace_vec i j then begin
        incr trace_eq_pairs;
        let h_inv = free_inv_F2 arr.(j) in
        if are_conjugate_F2_dec arr.(i) h_inv
        then incr inversion_only
        else begin
          incr trace_eq_genuine;
          suspicious := (arr.(i), arr.(j)) :: !suspicious
        end
      end
    done
  done;

  Printf.printf "\n=== Positive-word SL(%d) search ===\n" dim_n;
  Printf.printf "Positive class reps                : %d\n" n_arr;
  Printf.printf "Total non-conjugate positive pairs : %d\n" !strict_pairs;
  Printf.printf "Trace-equivalent positive pairs    : %d\n" !trace_eq_pairs;
  Printf.printf "  inversion-only                   : %d\n" !inversion_only;
  Printf.printf "  GENUINE                          : %d\n" !trace_eq_genuine;

  if !trace_eq_genuine > 0 then begin
    Printf.printf "\nGenuine positive-word trace-equivalent pairs (first 30):\n";
    let rec take n = function
      | [] -> [] | _ when n = 0 -> []
      | x :: xs -> x :: take (n - 1) xs
    in
    List.iter (fun (g, h) ->
      Printf.printf "  γ = %s, η = %s  (lengths %d, %d)\n"
        (pp_w g) (pp_w h) (List.length g) (List.length h)
    ) (take 30 !suspicious)
  end

let () =
  Random.self_init ();
  let max_len = if Array.length Sys.argv > 1
                then int_of_string Sys.argv.(1) else 8 in
  let dim_n = if Array.length Sys.argv > 2
              then int_of_string Sys.argv.(2) else 2 in
  let num_reps = if Array.length Sys.argv > 3
                 then int_of_string Sys.argv.(3) else 100 in
  Printf.printf "=== Positive-word search (Conjecture 5.5 probe) ===\n";
  Printf.printf "max_len = %d, dim_n = %d, num_reps = %d\n" max_len dim_n num_reps;
  search ~max_len ~dim_n ~num_reps
