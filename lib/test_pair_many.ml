(* Try 200 random SL(2, Z) reps for the suspicious pair. *)
open Free_group_ml
open Sl2_ml

let rec pos_of_int n =
  if n <= 1 then XH
  else if n mod 2 = 0 then XO (pos_of_int (n / 2))
  else XI (pos_of_int (n / 2))
let z_of_int n =
  if n = 0 then Z0
  else if n > 0 then Zpos (pos_of_int n)
  else Zneg (pos_of_int (-n))
let qc_of_int n : qc = q2Qc { qnum = z_of_int n; qden = XH }

let mk_letter c = match c with
  | 'a' -> f2_a | 'A' -> f2_A
  | 'b' -> f2_b | 'B' -> f2_B
  | _ -> failwith "bad"

let parse_word s =
  List.init (String.length s) (fun i -> mk_letter s.[i])

type rep = { ra : mat2_Qc; rb : mat2_Qc }

let mk_rep aa ab ac ad ba bb bc bd =
  let m a b c d =
    mat2_mk_Qc (qc_of_int a) (qc_of_int b) (qc_of_int c) (qc_of_int d)
  in { ra = m aa ab ac ad; rb = m ba bb bc bd }

let eval_letter r l =
  let mat = match fst l with F1 _ -> r.ra | FS _ -> r.rb in
  if snd l then sL2_inv_Qc mat else mat

let eval_word r w =
  List.fold_left (fun acc l -> mat2_mul_Qc acc (eval_letter r l)) mat2_id_Qc w

let trace_of_word r w = mat2_trace_Qc (eval_word r w)

let () = Random.self_init ()

(* Generate a "random" SL(2, Z) matrix by choosing a, b, c freely and then d
   such that det = 1, but only when this is possible. We sample by trial. *)
let rand_sl2_mat () =
  let rec try_one tries =
    if tries = 0 then (1, 0, 0, 1)
    else
      let a = Random.int 21 - 10 in
      let b = Random.int 21 - 10 in
      let c = Random.int 21 - 10 in
      (* Need a*d - b*c = 1 → d = (1 + b*c) / a, exists iff a | 1+bc. *)
      if a = 0 then begin
        (* a = 0 ⇒ -bc = 1 ⇒ b*c = -1 ⇒ either (b,c) = (1,-1) or (-1,1). *)
        let b' = if Random.bool () then 1 else -1 in
        let c' = -b' in
        let d = Random.int 21 - 10 in
        (0, b', c', d)
      end else begin
        let r = 1 + b * c in
        if r mod a = 0 then (a, b, c, r / a)
        else try_one (tries - 1)
      end
  in try_one 100

let pair_a = parse_word "BBABa"
let pair_b = parse_word "BABBa"

let () =
  Printf.printf "Testing γ = BBABa, η = BABBa under 200 random SL(2,Z) reps\n";
  let total = ref 0 in
  let agree = ref 0 in
  for _ = 1 to 200 do
    let (aa, ab, ac, ad) = rand_sl2_mat () in
    let (ba, bb, bc, bd) = rand_sl2_mat () in
    let r = mk_rep aa ab ac ad ba bb bc bd in
    let tg = trace_of_word r pair_a in
    let th = trace_of_word r pair_b in
    incr total;
    if qc_eq_dec tg th then incr agree
  done;
  Printf.printf "Out of %d reps, traces agreed in %d cases.\n" !total !agree;
  if !agree = !total then
    Printf.printf "→ Strong evidence the trace polynomials are identical.\n"
