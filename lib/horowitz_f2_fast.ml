(* horowitz_f2_fast.ml — fast F_2 search using canonical-form hashing.

   Generalizes the OG horowitz_search to n-dim SL(n) reps and uses the
   speedy partitioning. *)

open Free_group_ml
open Sl2_ml
open Matn

let f2_letters = [f2_a; f2_b; f2_A; f2_B]

let n_rank = 2

let enum_reduced l =
  let rec go acc steps =
    if steps = l then acc
    else
      let new_acc =
        List.concat_map (fun w ->
          List.filter_map (fun ll ->
            match w with
            | [] -> Some [ll]
            | hd :: _ ->
              if letter_inv n_rank hd = ll then None
              else Some (ll :: w)
          ) f2_letters
        ) acc
      in
      go new_acc (steps + 1)
  in
  if l = 0 then [[]] else go [[]] 0

let enum_up_to len =
  let acc = ref [] in
  for l = 0 to len do acc := !acc @ enum_reduced l done; !acc

(* Letter index including inversion bit (0..3 for F_2). *)
let letter_index (l : letter) : int =
  let base = match fst l with F1 _ -> 0 | FS _ -> 1 in
  if snd l then base + 2 else base

(* Cyclic-reduce a word (used for proper conjugacy partition). *)
let cyclic_reduce_word (w : letter list) : letter list =
  let rec strip_loop w =
    match w with
    | [] -> []
    | [_] -> w
    | first :: rest ->
      let n = List.length rest in
      let last = List.nth rest (n - 1) in
      if letter_inv n_rank first = last then
        strip_loop (List.filteri (fun i _ -> i < n - 1) rest)
      else w
  in
  strip_loop (reduce_poly n_rank w)

let canonical_cyclic (w : letter list) : int list =
  let cw = cyclic_reduce_word w in
  let n = List.length cw in
  if n = 0 then []
  else
    let arr = Array.of_list (List.map letter_index cw) in
    let best = ref (Array.to_list arr) in
    for shift = 1 to n - 1 do
      let rotated = Array.init n (fun i -> arr.((i + shift) mod n)) in
      let rl = Array.to_list rotated in
      if compare rl !best < 0 then best := rl
    done;
    !best

let partition_by_canonical words =
  let tbl = Hashtbl.create 1024 in
  List.iter (fun w ->
    let canon = canonical_cyclic w in
    let prev = try Hashtbl.find tbl canon with Not_found -> [] in
    Hashtbl.replace tbl canon (w :: prev)
  ) words;
  Hashtbl.fold (fun _ cls acc -> cls :: acc) tbl []

type rep_F2 = { ra : mat; rb : mat }

let eval_letter (r : rep_F2) (l : letter) : mat =
  let m = match fst l with F1 _ -> r.ra | FS _ -> r.rb in
  if snd l then inv_det1 m else m

let eval_word r w =
  let n = dim r.ra in
  List.fold_left (fun acc l -> mul acc (eval_letter r l)) (id n) w

let trace_word r w = trace (eval_word r w)

let rand_sln_mat (n : int) ~num_shears : mat =
  let m = id n in
  for _ = 1 to num_shears do
    let i = Random.int n in let j = Random.int n in
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
  let words = enum_up_to max_len in
  Printf.printf "Enumerated %d reduced F_2 words of length 0..%d\n"
    (List.length words) max_len;
  let classes = partition_by_canonical words in
  Printf.printf "Found %d F_2 conjugacy classes (via hashing).\n"
    (List.length classes);
  let arr = Array.of_list (List.map List.hd classes) in
  let n_arr = Array.length arr in
  let test_reps = build_rep_bank ~n:dim_n ~count:num_reps in
  let test_arr = Array.of_list test_reps in
  Printf.printf "Built %d random SL(%d, Z) F_2-representations.\n"
    (List.length test_reps) dim_n;
  let trace_table = Array.make_matrix n_arr num_reps qc_zero in
  for ri = 0 to num_reps - 1 do
    for gi = 0 to n_arr - 1 do
      trace_table.(gi).(ri) <- trace_word test_arr.(ri) arr.(gi)
    done
  done;
  Printf.printf "Bucketing by trace vector...\n";
  let trace_vec_table = Hashtbl.create 1024 in
  for i = 0 to n_arr - 1 do
    let key = trace_table.(i) in
    let prev = try Hashtbl.find trace_vec_table key with Not_found -> [] in
    Hashtbl.replace trace_vec_table key (i :: prev)
  done;
  let strict_pairs = ref 0 in
  let trace_eq_pairs = ref 0 in
  let inversion_only = ref 0 in
  let trace_eq_genuine = ref 0 in
  let suspicious = ref [] in
  Hashtbl.iter (fun _ idxs ->
    let l = List.length idxs in
    if l >= 2 then begin
      let a = Array.of_list idxs in
      for i = 0 to l - 1 do
        for j = i + 1 to l - 1 do
          incr strict_pairs;
          incr trace_eq_pairs;
          let g = arr.(a.(i)) and h = arr.(a.(j)) in
          let h_inv = free_inv_poly n_rank h in
          let canon_g = canonical_cyclic g in
          let canon_hi = canonical_cyclic h_inv in
          if compare canon_g canon_hi = 0
          then incr inversion_only
          else begin
            incr trace_eq_genuine;
            suspicious := (g, h) :: !suspicious
          end
        done
      done
    end
  ) trace_vec_table;
  let total_pairs = n_arr * (n_arr - 1) / 2 in
  Printf.printf "\n=== F_2 fast SL(%d) search ===\n" dim_n;
  Printf.printf "Conjugacy class reps               : %d\n" n_arr;
  Printf.printf "Total non-conjugate pairs          : %d\n" total_pairs;
  Printf.printf "Trace-equivalent pairs             : %d\n" !trace_eq_pairs;
  Printf.printf "  inversion-only                   : %d\n" !inversion_only;
  Printf.printf "  GENUINE                          : %d\n" !trace_eq_genuine;
  if !trace_eq_genuine > 0 then begin
    Printf.printf "\nGenuine trace-equivalent pairs (first 30):\n";
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
                then int_of_string Sys.argv.(1) else 7 in
  let dim_n = if Array.length Sys.argv > 2
              then int_of_string Sys.argv.(2) else 3 in
  let num_reps = if Array.length Sys.argv > 3
                 then int_of_string Sys.argv.(3) else 60 in
  Printf.printf "=== F_2 FAST search ===\n";
  Printf.printf "max_len = %d, dim_n = %d, num_reps = %d\n"
    max_len dim_n num_reps;
  search ~max_len ~dim_n ~num_reps
