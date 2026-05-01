(* Investigate the suspicious pair BBABa vs BABBa under several SL(2,Z) reps. *)
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

let pp_z = function
  | Z0 -> "0"
  | Zpos p -> let rec ti = function XH -> 1 | XO p -> 2*ti p | XI p -> 2*ti p + 1
              in string_of_int (ti p)
  | Zneg p -> let rec ti = function XH -> 1 | XO p -> 2*ti p | XI p -> 2*ti p + 1
              in string_of_int (-(ti p))
let pp_pos p = let rec ti = function XH->1 | XO p->2*ti p | XI p->2*ti p+1
               in string_of_int (ti p)
let pp_qc (q : qc) = let n = pp_z q.qnum in let d = pp_pos q.qden in
                    if d = "1" then n else n^"/"^d

(* Convention: (F1,false)=a, (F1,true)=a^-1, (FS F1,false)=b, (FS F1,true)=b^-1. *)
let mk_letter ch =
  match ch with
  | 'a' -> f2_a | 'A' -> f2_A
  | 'b' -> f2_b | 'B' -> f2_B
  | _ -> failwith "bad char"

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

(* Test the suspicious pair *)
let () =
  let g = parse_word "BBABa" in
  let h = parse_word "BABBa" in
  Printf.printf "γ = BBABa, η = BABBa\n";
  Printf.printf "γ ~_F2 η?  %b\n" (are_conjugate_F2_dec g h);
  let h_inv = free_inv_F2 h in
  Printf.printf "γ ~_F2 η^-1?  %b\n" (are_conjugate_F2_dec g h_inv);
  Printf.printf "η^-1 (reversed): "; List.iter (fun (l : letter) ->
    let i = match fst l with F1 _ -> "a" | FS _ -> "b" in
    print_string (if snd l then String.uppercase_ascii i else i)) h_inv;
  print_newline ();
  (* Try several reps, including non-symmetric ones *)
  let reps = [
    "rep1 a=[[2,1],[1,1]] b=[[1,1],[1,2]]", mk_rep 2 1 1 1  1 1 1 2;
    "rep2 a=[[1,1],[0,1]] b=[[1,0],[1,1]]", mk_rep 1 1 0 1  1 0 1 1;
    "rep3 a=[[2,1],[1,1]] b=[[3,2],[1,1]]", mk_rep 2 1 1 1  3 2 1 1;
    "rep4 a=[[3,2],[1,1]] b=[[1,0],[1,1]]", mk_rep 3 2 1 1  1 0 1 1;
    "rep5 a=[[2,3],[1,2]] b=[[1,1],[0,1]]", mk_rep 2 3 1 2  1 1 0 1;
    "rep6 a=[[1,2],[2,5]] b=[[3,1],[2,1]]", mk_rep 1 2 2 5  3 1 2 1;
    "rep7 a=[[2,1],[3,2]] b=[[1,2],[1,3]]", mk_rep 2 1 3 2  1 2 1 3;
    "rep8 a=[[5,4],[1,1]] b=[[1,2],[3,7]]", mk_rep 5 4 1 1  1 2 3 7;
    "rep9 a=[[7,3],[2,1]] b=[[2,5],[1,3]]", mk_rep 7 3 2 1  2 5 1 3;
    "repA a=[[3,5],[1,2]] b=[[8,3],[5,2]]", mk_rep 3 5 1 2  8 3 5 2;
    "repB a=[[10,7],[3,2]] b=[[5,2],[2,1]]", mk_rep 10 7 3 2  5 2 2 1;
    "repC a=[[1,1],[-1,0]] b=[[0,1],[-1,1]]", mk_rep 1 1 (-1) 0  0 1 (-1) 1;
  ] in
  Printf.printf "Traces under various reps:\n";
  List.iter (fun (name, r) ->
    let tg = trace_of_word r g in
    let th = trace_of_word r h in
    let eq = qc_eq_dec tg th in
    Printf.printf "  %-50s tr(γ)=%s tr(η)=%s  eq=%b\n"
      name (pp_qc tg) (pp_qc th) eq
  ) reps
