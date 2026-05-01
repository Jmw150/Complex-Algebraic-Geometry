(* horowitz_n_search.ml — search F_2 for SL_n-trace-equivalent
   non-conjugate pairs, for general n.

   Inputs:  command-line arg = max word length
            second arg = matrix dim n (default 3)

   Output:
     - For length L and SL(n), report:
        * Total non-conjugate pairs.
        * Pairs trace-equivalent under all test reps.
        * Of those, how many are γ ~ η^-1.
        * GENUINE pairs (non-conj, non-inv-conj, trace-equivalent).

   For n = 2 we know there are 16 genuine pairs at length 5
   (computed earlier). For n = 3 the question is OPEN. *)

open Free_group_ml
open Sl2_ml
open Matn

(* ---------- Word enumeration (same as horowitz_search.ml) ---------- *)
let all_letters : letter list = [f2_a; f2_b; f2_A; f2_B]

let rec enum_reduced l : letter list list =
  if l = 0 then [[]]
  else
    let prevs = enum_reduced (l - 1) in
    List.concat_map (fun w ->
      List.filter_map (fun ll ->
        match w with
        | [] -> Some (ll :: w)
        | hd :: _ ->
          if letter_inv 2 hd = ll then None
          else Some (ll :: w)
      ) all_letters
    ) prevs

let enum_up_to len =
  let acc = ref [] in
  for l = 0 to len do acc := !acc @ enum_reduced l done; !acc

(* ---------- Conjugacy partition ---------- *)

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

(* ---------- Generic-n representation ---------- *)
type rep_n = { ra : mat; rb : mat }

let eval_letter (r : rep_n) (l : letter) : mat =
  let m = match fst l with F1 _ -> r.ra | FS _ -> r.rb in
  if snd l then inv_det1 m else m

let eval_word (r : rep_n) (w : letter list) : mat =
  let n = dim r.ra in
  List.fold_left (fun acc l -> mul acc (eval_letter r l)) (id n) w

let trace_word r w = trace (eval_word r w)

(* ---------- Bank of test reps for SL(n, Z) ---------- *)

(* Random SL(n, Z) matrix via row operations on identity, applying
   random shears. Each shear preserves det. *)
let rand_sln_mat (n : int) ~num_shears : mat =
  let m = id n in
  let do_shear () =
    let i = Random.int n in
    let j = Random.int n in
    if i <> j then begin
      (* Add k * row j to row i: preserves determinant. *)
      let k = (Random.int 5) - 2 in (* k ∈ {-2,-1,0,1,2} *)
      if k <> 0 then
        for c = 0 to n - 1 do
          m.(i).(c) <- qcplus m.(i).(c) (qcmult (qc_of_int k) m.(j).(c))
        done
    end
  in
  for _ = 1 to num_shears do do_shear () done;
  m

let build_rep_bank ~n ~count : rep_n list =
  let rec go acc k =
    if k = 0 then acc
    else go ({ ra = rand_sln_mat n ~num_shears:8;
               rb = rand_sln_mat n ~num_shears:8 } :: acc) (k - 1)
  in go [] count

(* ---------- Main search ---------- *)
let search ~max_len ~dim_n ~num_reps =
  let words = enum_up_to max_len in
  Printf.printf "Enumerated %d reduced F_2 words of length ≤ %d\n"
    (List.length words) max_len;
  let classes = partition_by_conjugacy words in
  Printf.printf "Found %d conjugacy classes.\n" (List.length classes);
  let arr = Array.of_list (List.map List.hd classes) in
  let n_arr = Array.length arr in
  let test_reps = build_rep_bank ~n:dim_n ~count:num_reps in
  Printf.printf "Built %d random SL(%d, Z) representations.\n"
    (List.length test_reps) dim_n;

  (* Pre-compute trace tables. *)
  let trace_table = Array.make_matrix n_arr num_reps qc_zero in
  let test_arr = Array.of_list test_reps in
  for ri = 0 to num_reps - 1 do
    for gi = 0 to n_arr - 1 do
      trace_table.(gi).(ri) <- trace_word test_arr.(ri) arr.(gi)
    done;
    if ri mod 50 = 0 then Printf.printf "  computed traces for rep %d/%d\r%!"
      ri num_reps
  done;
  Printf.printf "  computed traces for all reps.   \n";

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

  Printf.printf "\n=== SL(%d) search summary ===\n" dim_n;
  Printf.printf "Conjugacy class reps               : %d\n" n_arr;
  Printf.printf "Total non-conjugate pairs          : %d\n" !strict_pairs;
  Printf.printf "Trace-equivalent under all test reps: %d\n" !trace_eq_pairs;
  Printf.printf "  of which γ ~ η^-1 (inversion case): %d\n" !inversion_only;
  Printf.printf "  of which GENUINE                    : %d\n" !trace_eq_genuine;

  if !trace_eq_genuine > 0 then begin
    Printf.printf "\nFirst 20 genuine candidates (probably need MORE reps to confirm):\n";
    let pp_w w =
      String.concat ""
        (List.map (fun (l : letter) ->
          let i = match fst l with F1 _ -> "a" | FS _ -> "b" in
          if snd l then String.uppercase_ascii i else i) w) in
    let rec take n = function
      | [] -> [] | _ when n = 0 -> []
      | x :: xs -> x :: take (n - 1) xs
    in
    List.iter (fun (g, h) ->
      Printf.printf "  γ = %s, η = %s  (lengths %d, %d)\n"
        (pp_w g) (pp_w h) (List.length g) (List.length h)
    ) (take 20 !suspicious)
  end else
    Printf.printf "\n→ All non-conjugate pairs separate by SL(%d) trace OR are γ ~ η^-1.\n" dim_n

let () =
  Random.self_init ();
  let max_len = if Array.length Sys.argv > 1
                then int_of_string Sys.argv.(1) else 5 in
  let dim_n = if Array.length Sys.argv > 2
              then int_of_string Sys.argv.(2) else 3 in
  let num_reps = if Array.length Sys.argv > 3
                 then int_of_string Sys.argv.(3) else 100 in
  Printf.printf "=== SL(%d) Horowitz-extension search in F_2 ===\n" dim_n;
  Printf.printf "max_len = %d, dim_n = %d, num_reps = %d\n" max_len dim_n num_reps;
  search ~max_len ~dim_n ~num_reps
