(* Capture zarith's Z before Complexrocq.Z shadows it *)
module ZarithZ = Z

open Complexrocq
open Converters

(* ------------------------------------------------------------------ *)
(* Existing complex number demo                                         *)
(* ------------------------------------------------------------------ *)

let string_of_c c =
  let (cnum1, cden1, cnum2, cden2) = ints_of_c (-5) c in
  Printf.sprintf "%d/%d+%d/%di" cnum1 cden1 cnum2 cden2

let demo_complex () =
  Printf.printf "\n=== Complex arithmetic ===\n";
  let za = ZarithZ.of_int in
  let z  = Complexocaml.C.of_qs
    (Q.make (za 1) (za 2))
    (Q.make (za 2) (za 2)) in
  let n  = nat_of_int 5 in
  let x  = inject_Q (q_of_ints 1 3) in
  let y  = fr x in
  let y_ap = approx y (z_of_int (-5)) in
  let (rum, ren) = ints_of_q y_ap in
  let z2 = cinject_Q (q_of_ints 1 2) in
  let (cnum1, cden1, cnum2, cden2) = ints_of_c (-5) z2 in
  Printf.printf "ocaml complex: %s\n" (Complexocaml.C.to_string z);
  Printf.printf "nat = %d\n" (int_of_nat n);
  Printf.printf "R = %d/%d\n" rum ren;
  Printf.printf "C = %d/%d + %d/%di\n" cnum1 cden1 cnum2 cden2;
  let zl1 = repeat (cinject_Q (q_of_ints 5 1)) (nat_of_int 3) in
  let zl2 = repeat (cinject_Q (q_of_ints 4 1)) (nat_of_int 3) in
  let zl3 = repeat (cinject_Q (q_of_ints 3 1)) (nat_of_int 3) in
  let m = [zl1; zl2; zl3] in
  let mm = madd m m in
  let mtr = trace m in
  let string_of_cmat mat =
    mat |> List.map (fun row -> row |> List.map string_of_c |> String.concat " ")
        |> String.concat "\n"
  in
  Printf.printf "M(C) = \n%s\n" (string_of_cmat m);
  Printf.printf "M(C)+M(C) = \n%s\n" (string_of_cmat mm);
  Printf.printf "M(C).trace = %s\n" (string_of_c mtr)

(* ------------------------------------------------------------------ *)
(* DFT round-trip demo                                                  *)
(* ------------------------------------------------------------------ *)

let demo_dft () =
  Printf.printf "\n=== DFT round-trip ===\n";
  let input = Fno.real_signal [1.0; 2.0; 3.0; 4.0] in
  Fno.print_signal "input       " input;
  let freq   = Fno.dft input in
  Fno.print_signal "DFT         " freq;
  let reconstructed = Fno.idft freq in
  Fno.print_signal "IDFT(DFT(x))" reconstructed

(* ------------------------------------------------------------------ *)
(* FNO single-layer demo                                                *)
(* ------------------------------------------------------------------ *)

let demo_fno () =
  Printf.printf "\n=== FNO single layer (N=4, K_max=2) ===\n";
  let n = 4 in
  let k_max = 2 in
  let weights = [(2.0, 0.0); (0.5, 0.0)] in
  let layer = Fno.make_layer ~k_max ~weights ~skip:(1.0, 0.0) ~nonlin:Fno.id_nonlin in
  let net   = Fno.make_fno ~lift:(1.0, 0.0) ~proj:(1.0, 0.0) ~layers:[layer] in
  let input = Fno.real_signal (List.init n (fun _ -> 1.0)) in
  Fno.print_signal "input " input;
  Fno.print_signal "output" (Fno.forward net input)

(* ------------------------------------------------------------------ *)
(* Convolution theorem check                                            *)
(* ------------------------------------------------------------------ *)

let demo_conv_theorem () =
  Printf.printf "\n=== Convolution theorem: DFT(x*y) = DFT(x)·DFT(y) ===\n";
  let xs = Fno.real_signal [1.0; 0.0; 0.0; 0.0] in
  let ys = Fno.real_signal [1.0; 2.0; 3.0; 4.0] in
  let lhs = Fno.dft (Fno.cyclic_conv xs ys) in
  let rhs = List.map2 (fun (xr, xi) (yr, yi) ->
    (xr *. yr -. xi *. yi, xr *. yi +. xi *. yr))
    (Fno.dft xs) (Fno.dft ys) in
  Fno.print_signal "DFT(x⊛y)     " lhs;
  Fno.print_signal "DFT(x)·DFT(y)" rhs;
  let max_err = List.fold_left2 (fun acc (r1,i1) (r2,i2) ->
    Float.max acc (Float.max (Float.abs (r1-.r2)) (Float.abs (i1-.i2))))
    0.0 lhs rhs in
  Printf.printf "max error: %.2e\n" max_err

(* ------------------------------------------------------------------ *)
(* Two-layer FNO with ReLU                                              *)
(* ------------------------------------------------------------------ *)

let demo_fno_deep () =
  Printf.printf "\n=== FNO two-layer, ReLU, N=8 K_max=3 ===\n";
  let n = 8 and k_max = 3 in
  let layer1 = Fno.make_layer ~k_max
    ~weights:(List.init k_max (fun _ -> (1.0, 0.0)))
    ~skip:(0.0, 0.0) ~nonlin:Fno.relu in
  let layer2 = Fno.make_layer ~k_max
    ~weights:(List.init k_max (fun _ -> (0.5, 0.0)))
    ~skip:(0.5, 0.0) ~nonlin:Fno.id_nonlin in
  let net = Fno.make_fno ~lift:(1.0,0.0) ~proj:(1.0,0.0) ~layers:[layer1;layer2] in
  let input = Fno.real_signal (List.init n (fun k ->
    sin (2.0 *. Float.pi *. float_of_int k /. float_of_int n))) in
  Fno.print_signal "input " input;
  Fno.print_signal "output" (Fno.forward net input)

let () =
  demo_complex ();
  demo_dft ();
  demo_fno ();
  demo_conv_theorem ();
  demo_fno_deep ()
