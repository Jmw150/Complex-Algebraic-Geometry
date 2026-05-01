(* Investigate the 3-generator pair (abcacabbc, acabcabbc) and its
   reductions via Cayley-Hamilton. *)
open Free_group_ml
open Sl2_ml
open Matn

let f3_a : letter = (F1 3, false)
let f3_b : letter = (FS (3, F1 2), false)
let f3_c : letter = (FS (3, FS (2, F1 1)), false)

let mk_letter c =
  match c with
  | 'a' -> f3_a | 'b' -> f3_b | 'c' -> f3_c
  | _ -> failwith "bad"

let parse_word s =
  List.init (String.length s) (fun i -> mk_letter s.[i])

let rec pos_of_int n =
  if n <= 1 then XH
  else if n mod 2 = 0 then XO (pos_of_int (n / 2))
  else XI (pos_of_int (n / 2))
let z_of_int n =
  if n = 0 then Z0
  else if n > 0 then Zpos (pos_of_int n)
  else Zneg (pos_of_int (-n))
let qc_of_int n : qc = q2Qc { qnum = z_of_int n; qden = XH }

let pp_z = function
  | Z0 -> "0"
  | Zpos p -> let rec ti = function XH -> 1 | XO p -> 2*ti p | XI p -> 2*ti p + 1
              in string_of_int (ti p)
  | Zneg p -> let rec ti = function XH -> 1 | XO p -> 2*ti p | XI p -> 2*ti p + 1
              in string_of_int (-(ti p))
let pp_pos p = let rec ti = function XH -> 1 | XO p -> 2*ti p | XI p -> 2*ti p + 1
               in string_of_int (ti p)
let pp_qc (q : qc) = let n = pp_z q.qnum in let d = pp_pos q.qden in
                    if d = "1" then n else n^"/"^d

type rep_F3 = { ra : mat; rb : mat; rc : mat }

let mk_rep aa ab ac ad ba bb bc bd ca cb cc cd =
  let m a b c d =
    of_list 2 [qc_of_int a; qc_of_int b; qc_of_int c; qc_of_int d]
  in { ra = m aa ab ac ad; rb = m ba bb bc bd; rc = m ca cb cc cd }

let eval_letter (r : rep_F3) (l : letter) : mat =
  let m = match fst l with
    | F1 _ -> r.ra
    | FS (_, F1 _) -> r.rb
    | FS _ -> r.rc
  in
  if snd l then inv_det1 m else m

let eval_word r w =
  List.fold_left (fun acc l -> mul acc (eval_letter r l)) (id 2) w

let trace_of r w = trace (eval_word r w)

(* Random SL(2, Z) bank. *)
let rand_sl2 () =
  let m = id 2 in
  for _ = 1 to 6 do
    let i = Random.int 2 in let j = Random.int 2 in
    if i <> j then begin
      let k = Random.int 5 - 2 in
      if k <> 0 then
        for c = 0 to 1 do
          m.(i).(c) <- qcplus m.(i).(c) (qcmult (qc_of_int k) m.(j).(c))
        done
    end
  done; m

let () =
  Random.self_init ();
  Printf.printf "Investigating 3-gen pairs...\n";
  let words = [
    "abcacabbc", "acabcabbc";  (* length 9 *)
    "abcacabc",  "acabcabc";   (* length 8 reduction (Cayley on b² in suffix) *)
    "abcacac",   "acabcac";    (* length 7 reduction *)
    "abcaca",    "acabca";     (* length 6 — the X', Y' from Cayley reduction *)
  ] in
  let reps = Array.init 50 (fun _ ->
    { ra = rand_sl2 (); rb = rand_sl2 (); rc = rand_sl2 () }) in
  List.iter (fun (gs, hs) ->
    let g = parse_word gs in
    let h = parse_word hs in
    let agree = ref 0 in
    Array.iter (fun r ->
      let tg = trace_of r g in
      let th = trace_of r h in
      if qc_eq_dec tg th then incr agree
    ) reps;
    Printf.printf "(%s, %s) [length %d]: %d/%d reps trace-agree\n"
      gs hs (String.length gs) !agree (Array.length reps)
  ) words
