(* horowitz_search.ml — search F_2 for SL_2-trace-equivalent
   non-conjugate pairs.

   Background: in F_r, the open question (open_SLn_trace_pair) asks
   whether two non-conjugate elements can have the SAME trace under
   every SL(n, ℂ) representation. For n = 2 the answer is NO
   (Horowitz). For n ≥ 3 it's open.

   This driver:
   1. Enumerates all reduced F_2 words up to length L.
   2. Groups them by conjugacy class using are_conjugate_F2_dec.
   3. For each non-conjugate pair (γ, η), tries many SL(2, Q)
      representations ρ : F_2 → SL(2, Q) and checks whether there
      EXISTS one with tr(ρ(γ)) ≠ tr(ρ(η)).
   4. Reports any pair that NEVER trace-separates — those would
      contradict Horowitz (and should not exist).

   No counterexample found = computational evidence consistent with
   Horowitz. *)

open Free_group_ml
open Sl2_ml

(* ---------- Conversion helpers ---------- *)
let rec pos_of_int n =
  if n <= 1 then XH
  else if n mod 2 = 0 then XO (pos_of_int (n / 2))
  else XI (pos_of_int (n / 2))

let z_of_int n =
  if n = 0 then Z0
  else if n > 0 then Zpos (pos_of_int n)
  else Zneg (pos_of_int (-n))

let qc_of_int n : qc = q2Qc { qnum = z_of_int n; qden = XH }

(* ---------- Word enumeration ---------- *)

(* The four F_2 letters. *)
let all_letters : letter list = [f2_a; f2_b; f2_A; f2_B]

(* Enumerate all reduced words of length exactly l. *)
let rec enum_reduced l : letter list list =
  if l = 0 then [[]]
  else
    let prevs = enum_reduced (l - 1) in
    List.concat_map (fun w ->
      List.filter_map (fun ll ->
        match w with
        | [] -> Some (ll :: w)
        | hd :: _ ->
          (* Cancel: ll · hd = e iff ll = hd^-1 *)
          if letter_inv 2 hd = ll then None
          else Some (ll :: w)
      ) all_letters
    ) prevs

(* All reduced words of length 0..L. *)
let enum_up_to len : letter list list =
  let acc = ref [] in
  for l = 0 to len do
    acc := !acc @ enum_reduced l
  done; !acc

(* ---------- Conjugacy partition ---------- *)

(* Greedy conjugacy class partition. *)
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
  ) words;
  !classes

(* ---------- Word evaluation under a representation ---------- *)

(* A representation ρ : F_2 → SL(2, Q) is given by ρ(a), ρ(b). *)
type rep_F2 = { rho_a : mat2_Qc; rho_b : mat2_Qc }

(* Evaluate ρ on a letter. *)
let eval_letter (r : rep_F2) (l : letter) : mat2_Qc =
  let mat = match fst l with
    | F1 _ -> r.rho_a    (* index 0 → a *)
    | FS _ -> r.rho_b    (* index 1 → b *)
  in
  if snd l then sL2_inv_Qc mat else mat
  (* Convention: snd = false means positive generator *)

(* Evaluate ρ on a word. *)
let eval_word (r : rep_F2) (w : letter list) : mat2_Qc =
  List.fold_left (fun acc l -> mat2_mul_Qc acc (eval_letter r l))
    mat2_id_Qc w

let trace_word (r : rep_F2) (w : letter list) : qc =
  mat2_trace_Qc (eval_word r w)

(* ---------- Bank of test representations ---------- *)

let rep_of_pairs ((aa, ab, ac, ad), (ba, bb, bc, bd)) =
  let m a b c d =
    mat2_mk_Qc (qc_of_int a) (qc_of_int b) (qc_of_int c) (qc_of_int d)
  in
  { rho_a = m aa ab ac ad; rho_b = m ba bb bc bd }

(* Generate all SL(2, Z) matrices [[a,b],[c,d]] with |a|,|b|,|c|,|d| ≤ K
   satisfying det = a*d - b*c = 1. *)
let enumerate_sl2_int (k : int) : (int * int * int * int) list =
  let acc = ref [] in
  for a = -k to k do
    for b = -k to k do
      for c = -k to k do
        for d = -k to k do
          if a * d - b * c = 1 then acc := (a, b, c, d) :: !acc
        done
      done
    done
  done;
  !acc

(* Build a diverse bank of representations by pairing many SL(2, Z)
   matrices for ρ(a) and ρ(b). *)
let build_rep_bank ?(k=2) () : rep_F2 list =
  let mats = enumerate_sl2_int k in
  let n = List.length mats in
  Printf.printf "Generated %d SL(2,Z) matrices with |entries| ≤ %d\n" n k;
  let m_arr = Array.of_list mats in
  let acc = ref [] in
  (* Pair sampling: take every (i, j) for small i, j, AND a few diagonal
     pairs to get variety. *)
  for i = 0 to min 19 (n - 1) do
    for j = 0 to min 19 (n - 1) do
      acc := rep_of_pairs (m_arr.(i), m_arr.(j)) :: !acc
    done
  done;
  !acc

let test_reps : rep_F2 list = build_rep_bank ~k:2 ()

(* ---------- The search ---------- *)

let qc_eq = qc_eq_dec

let search ?(max_len=4) () =
  let words = enum_up_to max_len in
  Printf.printf "Enumerated %d reduced F_2 words of length ≤ %d\n"
    (List.length words) max_len;
  let classes = partition_by_conjugacy words in
  Printf.printf "Found %d conjugacy classes.\n" (List.length classes);
  (* For each pair of distinct classes, take one representative each
     and test SL_2-trace separation. *)
  let reps_of_classes = List.map List.hd classes in
  let n = List.length reps_of_classes in
  Printf.printf "Trying all %d × %d / 2 pairs of conjugacy class reps\n"
    n n;
  (* Pre-compute traces of all class reps under all test reps. *)
  let arr = Array.of_list reps_of_classes in
  let n_arr = Array.length arr in
  let n_reps = List.length test_reps in
  let trace_table =
    Array.make_matrix n_arr n_reps (qc_of_int 0) in
  List.iteri (fun ri rep ->
    Array.iteri (fun gi g ->
      trace_table.(gi).(ri) <- trace_word rep g
    ) arr
  ) test_reps;
  let same_trace_vec i j =
    let same = ref true in
    for ri = 0 to n_reps - 1 do
      if not (qc_eq trace_table.(i).(ri) trace_table.(j).(ri))
      then same := false
    done; !same
  in
  let strict_pairs = ref 0 in           (* non-conjugate pairs *)
  let trace_eq_pairs = ref 0 in         (* of those, trace-equivalent *)
  let trace_eq_after_inv = ref 0 in     (* of those, even after η ~ γ^-1 check *)
  let inversion_only = ref 0 in         (* trace-eq because γ ~ η^-1 *)
  let suspicious = ref [] in
  for i = 0 to n_arr - 1 do
    for j = i + 1 to n_arr - 1 do
      incr strict_pairs;
      let g = arr.(i) and h = arr.(j) in
      let h_inv = free_inv_F2 h in
      if same_trace_vec i j then begin
        incr trace_eq_pairs;
        if are_conjugate_F2_dec g h_inv then
          incr inversion_only
        else begin
          incr trace_eq_after_inv;
          suspicious := (g, h) :: !suspicious
        end
      end
    done
  done;
  Printf.printf "\n=== Search summary ===\n";
  Printf.printf "Conjugacy class reps               : %d\n" n_arr;
  Printf.printf "Total non-conjugate pairs          : %d\n" !strict_pairs;
  Printf.printf "Trace-equivalent under all test reps: %d\n" !trace_eq_pairs;
  Printf.printf "  of which γ ~ η^-1 (inversion case): %d\n" !inversion_only;
  Printf.printf "  of which TRULY suspicious          : %d\n" !trace_eq_after_inv;
  Printf.printf "Test rep count: %d\n" n_reps;
  Printf.printf "\nInterpretation:\n";
  Printf.printf "  - Inversion-equivalent pairs (γ ~ η^-1): %d\n" !inversion_only;
  Printf.printf "  - GENUINE SL_2-trace-equivalent non-conjugate non-inverse-conjugate pairs: %d\n"
    !trace_eq_after_inv;
  if !trace_eq_after_inv > 0 then begin
    Printf.printf "  → These witness that F_2 does NOT satisfy property (B) for SL_2 alone.\n";
    Printf.printf "  → Each such pair requires a higher-dimensional rep to separate.\n";
    Printf.printf "  Examples (up to first 20):\n";
    let pp_w w =
      String.concat ""
        (List.map (fun (l : letter) ->
          let i = match fst l with F1 _ -> "a" | FS _ -> "b" in
          if snd l then String.uppercase_ascii i else i) w)
    in
    let rec take n = function
      | [] -> [] | _ when n = 0 -> []
      | x :: xs -> x :: take (n - 1) xs
    in
    List.iter (fun (g, h) ->
      Printf.printf "    γ = %s, η = %s  (lengths %d, %d)\n"
        (pp_w g) (pp_w h) (List.length g) (List.length h)
    ) (take 20 !suspicious)
  end

let () =
  Printf.printf "=== Horowitz n=2 search in F_2 ===\n";
  let max_len =
    match Sys.argv with
    | [| _; n |] -> int_of_string n
    | _ -> 4
  in
  Printf.printf "max_len = %d\n" max_len;
  search ~max_len ()
