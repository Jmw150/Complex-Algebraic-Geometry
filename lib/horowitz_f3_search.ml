(* horowitz_f3_search.ml — search F_3 (3 generators a, b, c) for
   SL_n-trace-equivalent non-conjugate POSITIVE-word pairs.

   Args: max_len  dim_n  num_reps *)

open Free_group_ml
open Sl2_ml
open Matn

(* F_3 letters. Use the polymorphic constructors directly. *)
let f3_a : letter = (F1 3, false)
let f3_b : letter = (FS (3, F1 2), false)
let f3_c : letter = (FS (3, FS (2, F1 1)), false)

let pos_letters_f3 = [f3_a; f3_b; f3_c]

(* Rank parameter for the polymorphic operations. *)
let n_rank = 3

(* Enumerate positive F_3 words of length L (no reductions needed). *)
let rec enum_positive_f3 l =
  if l = 0 then [[]]
  else List.concat_map (fun w -> List.map (fun ll -> ll :: w) pos_letters_f3)
                       (enum_positive_f3 (l - 1))

let enum_positive_up_to len =
  let acc = ref [] in
  for l = 1 to len do acc := !acc @ enum_positive_f3 l done; !acc

(* Conjugacy via cyclic reduction + rotation. We can use polymorphic
   reduce_poly + rotation via OCaml. *)
let rec rotate_left = function
  | [] -> []
  | x :: rest -> rest @ [x]

let all_rotations w =
  let n = List.length w in
  let acc = ref [w] in
  let cur = ref w in
  for _ = 1 to n - 1 do
    cur := rotate_left !cur;
    acc := !cur :: !acc
  done;
  !acc

let cyclic_reduce_f3 w =
  (* For positive words there's no cancellation, and they're always
     cyclically reduced (no inverse pairs at boundary since no
     inverses present). *)
  reduce_poly n_rank w

let are_conjugate_f3 u v =
  let cu = cyclic_reduce_f3 u in
  let cv = cyclic_reduce_f3 v in
  List.exists (word_eq_poly n_rank cv) (all_rotations cu)

(* Conjugacy partition. *)
let partition_by_conjugacy words =
  let classes = ref [] in
  List.iter (fun w ->
    let added = ref false in
    classes := List.map (fun cls ->
      match cls with
      | [] -> cls
      | rep :: _ ->
        if not !added && are_conjugate_f3 rep w
        then (added := true; cls @ [w])
        else cls
    ) !classes;
    if not !added then classes := !classes @ [[w]]
  ) words; !classes

(* Representation of F_3: three generator images (matrices). *)
type rep_F3 = { ra : mat; rb : mat; rc : mat }

let eval_letter (r : rep_F3) (l : letter) : mat =
  let m = match fst l with
    | F1 _ -> r.ra
    | FS (_, F1 _) -> r.rb
    | FS (_, FS _) -> r.rc
  in
  if snd l then inv_det1 m else m

let eval_word (r : rep_F3) w : mat =
  let n = dim r.ra in
  List.fold_left (fun acc l -> mul acc (eval_letter r l)) (id n) w

let trace_word r w = trace (eval_word r w)

(* Random SL(n, Z) by random shears. *)
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
               rb = rand_sln_mat n ~num_shears:8;
               rc = rand_sln_mat n ~num_shears:8 } :: acc) (k - 1)
  in go [] count

let pp_w w =
  String.concat ""
    (List.map (fun (l : letter) ->
      let i = match fst l with
        | F1 _ -> "a"
        | FS (_, F1 _) -> "b"
        | FS _ -> "c" in
      if snd l then String.uppercase_ascii i else i) w)

let search ~max_len ~dim_n ~num_reps =
  let words = enum_positive_up_to max_len in
  Printf.printf "Enumerated %d positive F_3 words of length 1..%d\n"
    (List.length words) max_len;
  let classes = partition_by_conjugacy words in
  Printf.printf "Found %d positive F_3 conjugacy classes.\n" (List.length classes);
  let arr = Array.of_list (List.map List.hd classes) in
  let n_arr = Array.length arr in
  let test_reps = build_rep_bank ~n:dim_n ~count:num_reps in
  let test_arr = Array.of_list test_reps in
  Printf.printf "Built %d random SL(%d, Z) F_3-representations.\n"
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
        let h_inv = free_inv_poly n_rank arr.(j) in
        if are_conjugate_f3 arr.(i) h_inv
        then incr inversion_only
        else begin
          incr trace_eq_genuine;
          suspicious := (arr.(i), arr.(j)) :: !suspicious
        end
      end
    done
  done;
  Printf.printf "\n=== F_3 positive-word SL(%d) search ===\n" dim_n;
  Printf.printf "Positive class reps                : %d\n" n_arr;
  Printf.printf "Total non-conjugate positive pairs : %d\n" !strict_pairs;
  Printf.printf "Trace-equivalent positive pairs    : %d\n" !trace_eq_pairs;
  Printf.printf "  inversion-only                   : %d\n" !inversion_only;
  Printf.printf "  GENUINE                          : %d\n" !trace_eq_genuine;
  if !trace_eq_genuine > 0 then begin
    Printf.printf "\nGenuine F_3 trace-equivalent pairs (first 30):\n";
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
                then int_of_string Sys.argv.(1) else 5 in
  let dim_n = if Array.length Sys.argv > 2
              then int_of_string Sys.argv.(2) else 2 in
  let num_reps = if Array.length Sys.argv > 3
                 then int_of_string Sys.argv.(3) else 80 in
  Printf.printf "=== F_3 positive-word search ===\n";
  Printf.printf "max_len = %d, dim_n = %d, num_reps = %d\n"
    max_len dim_n num_reps;
  search ~max_len ~dim_n ~num_reps
