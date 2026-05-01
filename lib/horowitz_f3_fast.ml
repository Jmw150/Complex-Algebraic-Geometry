(* horowitz_f3_fast.ml — fast version using canonical cyclic-form
   hashing instead of O(n^2) pairwise conjugacy.

   For positive words, two words are F_r-conjugate iff one is a cyclic
   rotation of the other. We canonicalize by picking the
   lex-smallest cyclic rotation, then hash. *)

open Free_group_ml
open Sl2_ml
open Matn

let f3_a : letter = (F1 3, false)
let f3_b : letter = (FS (3, F1 2), false)
let f3_c : letter = (FS (3, FS (2, F1 1)), false)

let pos_letters_f3 = [f3_a; f3_b; f3_c]

let n_rank = 3

let rec enum_positive_f3 l =
  if l = 0 then [[]]
  else List.concat_map (fun w -> List.map (fun ll -> ll :: w) pos_letters_f3)
                       (enum_positive_f3 (l - 1))

let enum_positive_up_to len =
  let acc = ref [] in
  for l = 1 to len do acc := !acc @ enum_positive_f3 l done; !acc

(* Map letter to a small int including inversion bit (0..5 for F_3). *)
let letter_index (l : letter) : int =
  let base = match fst l with
    | F1 _ -> 0
    | FS (_, F1 _) -> 1
    | FS _ -> 2
  in
  if snd l then base + 3 else base

(* Canonical form: lex-smallest cyclic rotation. *)
let canonical_cyclic (w : letter list) : int list =
  let n = List.length w in
  let arr = Array.of_list (List.map letter_index w) in
  let best = ref (Array.to_list arr) in
  for shift = 1 to n - 1 do
    let rotated = Array.init n (fun i -> arr.((i + shift) mod n)) in
    let rl = Array.to_list rotated in
    if compare rl !best < 0 then best := rl
  done;
  !best

(* Partition by canonical form using a hashtable. *)
let partition_by_canonical words =
  let tbl = Hashtbl.create 1024 in
  List.iter (fun w ->
    let canon = canonical_cyclic w in
    let prev = try Hashtbl.find tbl canon with Not_found -> [] in
    Hashtbl.replace tbl canon (w :: prev)
  ) words;
  Hashtbl.fold (fun _ cls acc -> cls :: acc) tbl []

type rep_F3 = { ra : mat; rb : mat; rc : mat }

let eval_letter (r : rep_F3) (l : letter) : mat =
  let m = match fst l with
    | F1 _ -> r.ra
    | FS (_, F1 _) -> r.rb
    | FS _ -> r.rc
  in
  if snd l then inv_det1 m else m

let eval_word (r : rep_F3) w : mat =
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

(* Check if w_inv is a cyclic rotation of w via canonical form. *)
let are_conj_via_inv (w : letter list) : letter list -> bool =
  (* We compute canonical cyclic form of w, then check candidate. *)
  let cw = canonical_cyclic w in
  fun v -> compare (canonical_cyclic v) cw = 0

let search ~max_len ~dim_n ~num_reps =
  let words = enum_positive_up_to max_len in
  Printf.printf "Enumerated %d positive F_3 words of length 1..%d\n"
    (List.length words) max_len;
  let classes = partition_by_canonical words in
  Printf.printf "Found %d positive F_3 conjugacy classes (via hashing).\n"
    (List.length classes);
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
    done;
    if ri mod 50 = 0 then Printf.printf "  reps %d/%d\r%!" ri num_reps
  done;
  Printf.printf "  reps done.        \n";

  (* Bucket by trace-vector for fast same-trace matching. *)
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
          if are_conj_via_inv g h_inv
          then incr inversion_only
          else begin
            incr trace_eq_genuine;
            suspicious := (g, h) :: !suspicious
          end
        done
      done
    end
  ) trace_vec_table;
  (* Total non-conjugate pairs is (n choose 2). *)
  let total_pairs = n_arr * (n_arr - 1) / 2 in

  Printf.printf "\n=== F_3 fast positive-word SL(%d) search ===\n" dim_n;
  Printf.printf "Positive class reps                : %d\n" n_arr;
  Printf.printf "Total non-conjugate positive pairs : %d\n" total_pairs;
  Printf.printf "Trace-equivalent positive pairs    : %d\n" !trace_eq_pairs;
  Printf.printf "  inversion-only                   : %d\n" !inversion_only;
  Printf.printf "  GENUINE                          : %d\n" !trace_eq_genuine;

  (* Check how many pairs are GENUINELY 3-generator (use all 3 letters
     in the union of γ and η). *)
  let uses_all_3 (g, h) =
    let used = Array.make 3 false in
    List.iter (fun l -> used.(letter_index l mod 3) <- true) g;
    List.iter (fun l -> used.(letter_index l mod 3) <- true) h;
    used.(0) && used.(1) && used.(2)
  in
  let three_gen = List.filter uses_all_3 !suspicious in
  Printf.printf "  of GENUINE pairs, using all 3 generators: %d\n"
    (List.length three_gen);

  if !trace_eq_genuine > 0 then begin
    Printf.printf "\nGenuine F_3 trace-equivalent pairs (first 30):\n";
    let rec take n = function
      | [] -> [] | _ when n = 0 -> []
      | x :: xs -> x :: take (n - 1) xs
    in
    List.iter (fun (g, h) ->
      Printf.printf "  γ = %s, η = %s  (lengths %d, %d)\n"
        (pp_w g) (pp_w h) (List.length g) (List.length h)
    ) (take 30 !suspicious);
    if three_gen <> [] then begin
      Printf.printf "\n*** GENUINELY 3-GENERATOR pairs ***\n";
      List.iter (fun (g, h) ->
        Printf.printf "  γ = %s, η = %s\n" (pp_w g) (pp_w h)
      ) three_gen
    end
  end

let () =
  Random.self_init ();
  let max_len = if Array.length Sys.argv > 1
                then int_of_string Sys.argv.(1) else 8 in
  let dim_n = if Array.length Sys.argv > 2
              then int_of_string Sys.argv.(2) else 2 in
  let num_reps = if Array.length Sys.argv > 3
                 then int_of_string Sys.argv.(3) else 80 in
  Printf.printf "=== F_3 FAST positive-word search ===\n";
  Printf.printf "max_len = %d, dim_n = %d, num_reps = %d\n"
    max_len dim_n num_reps;
  search ~max_len ~dim_n ~num_reps
